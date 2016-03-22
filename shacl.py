## An implementation of SHACL based on query generation.
##
## Uses the rdflib package and its SPARQL implementation.
##
## Implements my proposed syntax.
## The compatability functions capture almost all of the current syntax.
## Validation reports are generated as result sets
##   (except that severities may be handled differently)
## but not all the information in them may conform to the spec.

import string
import itertools
import rdflib
from rdflib import Namespace
from rdflib.term import BNode
from rdflib.term import URIRef
from rdflib.term import Literal
from rdflib.namespace import RDF
from rdflib.namespace import RDFS
from rdflib.namespace import XSD

import sys
sys.setrecursionlimit(10000) # SPARQL parsing goes deep into recursion

true = Literal("true",datatype=XSD.boolean)
SH = Namespace("http://www.w3.org/ns/shacl#")
Info = SH.Info
Warning = SH.Warning
Violation = SH.Violation

universalShape = "SELECT ?object WHERE { BIND ( true AS ?object ) FILTER ( true=false ) }"
emptyShape = "SELECT ?object WHERE { BIND ( true AS ?object ) FILTER ( true=true ) }"

## attempt to do something better when mixing severities
## not carried through throughout
severe = { Info : [Info.n3(),Warning.n3(),Violation.n3()],
           Warning : [Warning.n3(),Violation.n3()],
           Violation : [Violation.n3()] }
def moreSevere(context) : return ", ".join(severe[ context["severity"] ])

## a syntax and way to do substitution, other syntaxes and ways are possible
trsquare = { ord('['):u'{', ord(']'):u'}', ord('{'):u'[', ord('}'):u']' }
class Template(string.Formatter):
    def format_field(self,value,spec):
            if isinstance(value,rdflib.term.Literal) :
                if value.datatype == XSD.string : value = '"'+value+'"'
            if isinstance(value,rdflib.term.BNode) : value = '"'+value+'"' 
            if isinstance(value,rdflib.term.URIRef) : value = value.n3()
            if isinstance(value,basestring) :
                value = unicode(value).translate(trsquare)
            return value
def substitute(s,g,context,*args,**kwargs) :
    fkwargs = dict(context, **kwargs)
    sr = unicode(s).translate(trsquare)
    sf = Template().format(sr,*args,**fkwargs)
    return sf.translate(trsquare)

# use namespaces associated with the shapes graph to shorten names in reports
def curieS(g,node) : # for substitution into strings
    if isinstance(node,rdflib.term.URIRef) :
        return node.n3(g.namespace_manager)
    else: return unicode(node)

def curie(g,node) : # for a SPARQL term
    return node.n3(g.namespace_manager)

def pathS(path) : # for a SPARQL path
    if isinstance(path,rdflib.term.Literal) : return unicode(path)
    else : return path.n3()

def listElements(g,head) :
    elements = []
    while ( ( head is not None ) and ( head != RDF.nil ) ) :
        elements.append(g.value(head,RDF.first))
        head = g.value(head,RDF.rest)
    if ( head is None ) : print "MALFORMED LIST"
    return elements

def listTurtle(g,head) :
    return [ element.n3() for element in listElements(g,head) ]

## utility functions to create code

def fragmentPattern(g,code,message,context) :	# SubSelect <- GroupGraphPattern pieces
    body = """# FRAGMENT 
  SELECT [projection] ?this ?message ?severity (?this AS ?object)
  WHERE { [outer] [inner]
          [code] }
  VALUES (?message ?severity) { ( [message] [severity] ) }"""
    result = substitute(body,g,context, code=code, message='"'+message+'"')
    return result

def fragment(g,code,message,context) : 		# SubSelect <- PrimaryExpression
    filter = """FILTER ( ! %(code)s )""" % { "code":code }
    return fragmentPattern(g,filter,message,context)

def parttoSPARQL(g,part) :
    result =  ("^"+g.value(part,SH.inverse).n3()) \
              if (part,SH.inverse,None) in g else part.n3()
    return result

def pathtoSPARQL(g,value) :
    if value == RDF.nil :
        print "EMPTY PATH"
        return ""
    if (value,RDF.rest,None) in g :
        path = [ parttoSPARQL(g,part) for part in listElements(g,value) ]
        return Literal("/".join(path))
    elif (value,SH.inverse,None) in g :
        return Literal(parttoSPARQL(g,value))
    else : return value

### implementations of components

def inC(g,value,context) :			# fragment PrimaryExpression 
    frag = "EXISTS { VALUES ?this { %s } }" % " ".join(listTurtle(g,value))
    return fragment(g,frag, "Not any required value",context)

def classC(g,value,context) :			# fragment PrimaryExpression
    frag = "EXISTS { ?this rdf:type/rdfs:subClassOf* %s }" % value.n3()
    return fragment(g,frag, "Does not have required class %s" % curieS(g,value), context)

def classInC(g,value,context) :			# fragment PrimaryExpression
    frag = """EXISTS { VALUES ?class { %s } 
      ?this rdf:type/rdfs:subClassOf* ?class . }""" % " ".join(listTurtle(g,value))
    return fragment(g,frag, "Does not have any required class", context)

def datatypeC(g,value,context) :		# fragment PrimaryExpression
    frag = "(isLiteral(?this) && datatype(?this) = %s)" % value.n3()
    return fragment(g,frag,"Does not have required datatype %s"%curieS(g,value), context)

def datatypeInC(g,value,context) :  		# fragPat GroupGraphPattern piece
    frag = """BIND ( datatype(?this) AS ?dt ) 
              FILTER NOT EXISTS { VALUES ?dt { %s } }""" % " ".join(listTurtle(g,value))
    return fragmentPattern(g,frag, "Not any required value",context)

def directTypeC(g,value,context) : 		# fragment PrimaryExpression
    frag = "EXISTS { ?this rdf:type %s }" % value.n3()
    return fragment(g,frag, "Does not have required type %s" % curieS(g,value), context)

def minLengthC(g,value,context) :		# fragment PrimaryExpression
    frag = "(!isBlank(?this) && STRLEN(STR(?this)) >= %s)" % value
    return fragment(g,frag, "Length too short, must be at least %s" % value, context)

def maxLengthC(g,value,context) :		# fragment PrimaryExpression
    frag = "(!isBlank(?this) && STRLEN(STR(?this)) <= %s)" % value
    return fragment(g,frag, "Length too long, must be at most %s" % value, context)

def minInclusiveC(g,value,context) :		# fragment PrimaryExpression
    frag = "(isLiteral(?this) && ?this >= %s)" % value
    return fragment(g,frag, "Too small, must be at least %s" % value, context)

def minExclusiveC(g,value,context) :		# fragment PrimaryExpression
    frag = "(isLiteral(?this) && ?this > %s)" % value
    return fragment(g,frag, "Too small, must be greater than %s" % value, context)

def maxInclusiveC(g,value,context) :		# fragment PrimaryExpression
    frag = "(isLiteral(?this) && ?this <= %s)" % value
    return fragment(g,frag, "Too big, must be at most %s" % value, context)

def maxExclusiveC(g,value,context) :		# fragment PrimaryExpression
    frag = "(isLiteral(?this) && ?this < %s)" % value
    return fragment(g,frag, "Too big, must be less than %s" % value, context)

def nodeKindC(g,value,context) :		# fragment PrimaryExpression
    if value == SH.BlankNode :
        return fragment(g,"isBlank(?this)","Not blank", context)
    if value == SH.IRI :
        return fragment(g,"isIRI(?this)","Not IRI", context)
    if value == SH.Literal :
        return fragment(g,"isLiteral(?this)", "Not literal", context)
                    
def patternConstruct(g,pattern,flags,context) :	# fragment PrimaryExpression
    frag = """(!isBlank(?this) && REGEX(STR(?this),"%(pattern)s","%(flags)s"))""" % \
           {"pattern":pattern,"flags":flags}
    return fragment(g,frag,"Does not match regular expression", context)

def patternC(g,value,context) :			# fragment PrimaryExpression
    if isinstance(value,rdflib.term.Literal) :
        return patternConstruct(g,value,"",context)
    else :
        pattern = g.value(value,RDF.first)
        flags = g.value(g.value(value,RDF.rest),RDF.first)
        return patternConstruct(g,pattern,flags,context)

### these don't currently set predicate and object, should they??
def equalsC(g,value,context) :			# fragPat GroupGraphPattern
    path1 = pathtoSPARQL(g,g.value(value,RDF.first))
    path2 = pathtoSPARQL(g,g.value(g.value(value,RDF.rest),RDF.first))
    frag = """{ { ?this %(path1)s ?value . MINUS { ?this %(path2)s ?value . } } UNION 
         { ?this %(path2)s ?value . MINUS { ?this %(path1)s ?value.  } } }""" % \
        { "path1":pathS(path1), "path2":pathS(path2) }
    return fragmentPattern(g,frag,"Paths don't have equal values", context)

## this is the approved syntax but maybe sh:disjoint would be a better name
def notEqualsC(g,value,context) :		# fragpat GroupGraphPattern piece
    path1 = pathtoSPARQL(g,g.value(value,RDF.first))
    path2 = pathtoSPARQL(g,g.value(g.value(value,RDF.rest),RDF.first))
    frag = """?this %(path1)s ?value1 . ?this %(path2)s ?value1 .""" % \
        { "path1":pathS(path1), "path2":pathS(path2) }
    return fragmentPattern(g,frag,"Paths share a value", context)
                    
def lessThanC(g,value,context) :		# fragpat GroupGraphPattern pieces
    path1 = pathtoSPARQL(g,g.value(value,RDF.first))
    path2 = pathtoSPARQL(g,g.value(g.value(value,RDF.rest),RDF.first))
    frag = """?this %(path1)s ?value1 . ?this %(path2)s ?value2 .
		FILTER ( ! (?value1 < ?value2) )""" % \
            { "path1":pathS(path1), "path2":pathS(path2) }
    return fragmentPattern(g,frag,"Second path value too small", context)
                    
def lessThanOrEqualsC(g,value,context) :	# fragpat GroupGraphPattern pieces
    path1 = pathtoSPARQL(g,g.value(value,RDF.first))
    path2 = pathtoSPARQL(g,g.value(g.value(value,RDF.rest),RDF.first))
    frag = """?this %(path1)s ?value1 . ?this %(path2)s ?value2 .
		FILTER ( ! (?value1 <= ?value2) )""" % \
            { "path1":pathS(path1), "path2":pathS(path2) }
    return fragmentPattern(g,frag,"Second path value too small", context)

def listC(g,value,context) :			# SubSelect
    elementCheck = newContext(g,Literal("rdf:rest*/rdf:first"),
                              "For list element", value,context) 
    result = """# LIST
  SELECT [projection] ?this ?message ([severity] AS ?severity)
         ?subject ?predicate ?object
  WHERE { [outer] [inner]
          { FILTER NOT EXISTS { ?this rdf:rest* rdf:nil .}
            BIND ( "List does not terminate at rdf:nil" AS ?message )
            BIND ( ?this AS ?subject )
          } UNION {
            ?this rdf:rest* ?tail .
            FILTER ( ( EXISTS { ?tail rdf:rest ?tail1 . ?tail rdf:rest ?tail2 .
                                FILTER ( ! sameTerm(?tail1,?tail2) ) } ) ||
                     ( EXISTS { ?tail rdf:first ?elem1 . ?tail rdf:first ?elem2 .
                                FILTER ( ! sameTerm(?elem1,?elem2) ) } ) )
            BIND ( "List has multiple firsts or rests" AS ?message )
            BIND ( ?this AS ?subject )
            BIND ( ?tail AS ?object )
          } UNION {
            FILTER EXISTS { rdf:nil rdf:rest|rdf:first ?x }
            BIND ( "rdf:nil has rdf:first or rdf:rest" AS ?message )
            BIND ( ?this AS ?subject )
         } UNION { [elementCheck] } }""" 
    return substitute(result,g,context,elementCheck=elementCheck)

def hasValueC(g,value,context) :		# SubSelect
    body = """# hasValue
  SELECT [projection] ?message ?severity
  WHERE { [outer] 
          FILTER NOT EXISTS { [inner] FILTER sameTerm(?this,[value]) } }
  VALUES (?message ?severity) { ( [message] [severity] ) }""" 
    return substitute(body,g,context,value=value,
                      message='"Missing required value %s"' % curieS(g,value))

def uniqueLangC(g,value,context) :		# SubSelect
    if value == true :
        body = """# uniquelang
  SELECT [projection] ?message ?severity
  WHERE { [outer] [inner]
          BIND (lang(?this) AS ?lang)
          FILTER (isLiteral(?this) && bound(?lang) && ?lang != "") }
  [group] ?lang  HAVING ( COUNT(?this) > 1 )
  VALUES (?message ?severity) { ( [message] [severity] ) }"""
	return substitute(body,g,context,message='"Values share a language tag"')
    else : return universalShape

def minCountC(g,value,context) :		# SubSelect
    body = """# minCount
  SELECT [projection] ?message ?severity
  WHERE { [outer] OPTIONAL { [inner] } }
  [group] HAVING ( COUNT (DISTINCT ?this) < [value] )
  VALUES (?message ?severity) { ( [message] [severity] ) }"""
    return substitute(body,g,context,value=value,
                      message='"Too few values, need at least %s"' % value)

def maxCountC(g,value,context) :		# SubSelect
    body = """# maxCount
  SELECT [projection] ?message ?severity
  WHERE { [outer] OPTIONAL { [inner] } }
  [group] HAVING ( COUNT (DISTINCT ?this) > [value] )
  VALUES (?message ?severity) { ( [message] [severity] ) }"""
    return substitute(body,g,context,value=value,
                      message=u'"Too many values, want at most %s"' % value)

def shapeC(g,value,context) :			# SubSelect
    child = processShape(g,value,context)
    return """# COMPONENT shape\n%(child)s""" % { "child":child }

def notC(g,value,context) :			# SubSelect
    child = processShape(g,value,context)
    result = """  SELECT [projection] ?this ?message ?severity ?subject ?property ?object
  WHERE { [outer] [inner]
          BIND ( "Fails to validate against negated shape" AS ?message )
          BIND ( [severity] AS ?severity ) 
          MINUS { 
            SELECT [projection] ?this
            WHERE { { [child] } 
                    FILTER ( ?severity IN ( [severe] ) ) 
                  } } }"""
    return substitute(result,g,context,child=child, severe=moreSevere(context) )

def andC(g,value,context) :			# SubSelect
    children = [ processShape(g,child,context)
                 for child in listElements(g,value) ]
    childs = "{ " + "\n } UNION {\n".join(children) + "\n }" \
             if len(children)>0 else ""
    result = """# COMPONENT and
  SELECT [projection] ?this ?message ?severity ?subject ?property ?object
  WHERE { [childs] }"""
    return substitute(result,g,context,childs=childs)

def orC(g,value,context) :			# SubSelect
    children = [ processShape(g,child,context)
                 for child in listElements(g,value) ]
    if len(children) == 0 :
        result="""SELECT [projection] ?this ?subject ?predicate ?object ?message ?severity
    WHERE { VALUES ( ?this ?subject ?predicate ?object ?message ?severity )
               { ( UNDEF UNDEF UNDEF UNDEF "Empty or" [severity] ) } }""" 
        return substitute(result,g,context)
    elif len(children) == 1 :
        return children[0]
    else :
        childs = [ """{ SELECT %(projection)s ?this WHERE { %(child)s } }""" % \
                   { "projection":context["projection"], "child":child }
                   for child in itertools.islice(children,1,None) ]
        result="""SELECT [projection] ?this ?message ?severity ?subject ?predicate ?object
    WHERE { { [first] } [childs] }"""
        return substitute(result,g,context, first=children[0], childs=" ".join(childs))

def closedC(g,value,context) :			# fragment PrimaryExpression
    paths = [ parttoSPARQL(g,element)
                   for element in listElements(g,value) ]
    closed = "!(" + "|".join(paths) + ")"
    frag = """( ! EXISTS { ?this %(closed)s ?value } )""" % { "closed":closed }
    return fragment(g,frag,"Value found for disallowed property", context)

def partitionC(g,value,context) :		# SubSelect
    children =  listElements(g,value)
    bodies = []
    exclusions = []
    for child in children :
        body,filters = processShapeInternal(g,child,context,exclusions=exclusions)
        bodies.append(body)
        excl = "{ " + " } UNION { ".join(filters) + " } "
        excl = substitute("{ SELECT [projection] ?this # EXCLUSION\n  WHERE { [excl] } } ",
                               g,context,excl=excl)
        exclusions.append(excl)
    final = substitute(""" { SELECT [projection] ?this ?message # PARTITION FINAL
    WHERE { [outer] [inner] [exclusion] } 
    VALUES (?message) { ( [message] ) } } """,g,context,
                       exclusion=" ".join(exclusions),message='"Partition not exhaustive"')
    bodies.append(final)
    bodys = "{ " + "\n } UNION {\n".join(bodies) + "\n }"
    result = """ # PARTITION
  SELECT [projection] ?this ?message ?severity ?subject ?property ?object
  WHERE { [bodys] }   """
    return substitute(result,g,context,bodys=bodys)

def constructShape(g,shape,components,context) :	# SubSelect <- SubSelects
    if ( len(components) > 0 ) :
        body = "{ " + " } UNION { ".join(components) + " }"
        result = """# SHAPE start [shape]
  SELECT [projection] ?this ?message ?severity 
         ?subject ?predicate ?object ([shape] AS ?shape )
  WHERE # SHAPE body\n { [body]
        } # SHAPE end [shape]\n""" 
        return substitute(result,g,context, shape=shape, body=body)
    else: return universalShape

# set up a new context that is the values of a path from the current context
def newContext(g,path,message,childShape,context) : # SubSelect
    childouter = """{ SELECT (?parent AS ?grandparent) (?this AS ?parent) 
        WHERE { %(inner)s } }""" % { "inner":context["inner"] }
    childinner = """{ ?parent %(path)s ?this . }""" % { "path":pathS(path) }
    childcontext=dict(severity=context["severity"],outer=childouter,projection="?parent",
                      group="GROUP BY ?parent",inner=childinner)
    child = processShape(g,childShape,childcontext)
    result ="""# newContext
  SELECT [projection] ?this ?message ?severity ?subject ?predicate ?object
  WHERE { [inner] # subshape inner
   {SELECT (?childGrandparent AS ?parent) (?childParent AS ?this)
           ?message ?severity ?subject ?predicate ?object
     WHERE
     {{ SELECT (?grandparent AS ?childGrandparent) (?parent AS ?childParent)
               (?message AS ?childMessage) (?severity as ?childSeverity)
               (?subject AS ?childSubject) (?predicate AS ?childPredicate) ?object
        WHERE {     [child]
              } }
      BIND( (IF(BOUND(?childSubject), ?childSubject, ?childParent)) AS ?subject )
      BIND( (IF(BOUND(?childSubject), ?childPredicate, [path])) AS ?predicate )
      BIND( CONCAT([message],?childMessage) AS ?message )
      BIND( [severity] AS ?severity ) 
      } } }"""
    return substitute(result,g,context,message='"'+message+'"',child=child,
                      path=curie(g,path) )

def propValuesC(g,value,context) :		# SubSelect
    path = pathtoSPARQL(g,g.value(value,RDF.first))
    childShape = g.value(g.value(value,RDF.rest),RDF.first)
    return newContext(g,path,"In path %s "% curieS(g,path),childShape, context)

# compatability constructs - not tested 
def constraintC(g,value,me,context) :
    return shapeC(g,value,context)

def propertyC(g,value,me,context) :
    property = g.value(value,SH.predicate).n3()
    return newContext(g,property,"In path %s " % path.n3(),value, context)

def inversePropertyC(g,value,me,context) :
    property = "^" + g.value(value,SH.predicate).n3()
    return newContext(g,property,"In path %s " % path.n3(),value, context)

def qualifiedValueShapeC(g,value,me,context) :
    filter = processShape(g,shape,parentcontext) 
    inner = "{ " + inner + "\n } MINUS { # FILTER\n" + filter + "\n }"
    min = g.value(me,SH.qualifiedMinCount,None)
    minComponent = minCountC(g,min,context) \
                   if min is not None else None
    max = g.value(me,SH.qualifiedMaxCount,None)
    maxComponent = maxCountC(g,max,context) \
                   if max is not None else None
    component = ( " { " + minComponent + " } UNION { " + maxComponent + " } " \
                  if min is not None else maxComponent ) \
                     if max is not None \
                     else minComponent if min is not None else None
    if component is not None :
        return constructShape(g,shape,[component],projection)
    else: return universalShape

def patternCompatibilityC(g,value,me,context) :
    flags = g.value(me,SH.flags,"")
    return patternConstruct(g,pattern,flags,context)

def closedCompatabilityC(g,value,me,context) :
    ignored = listTurtle(g,g.value(me,SH.flags,""))
    properties = [ g.value(property,SH.predicate).n3()
                   for property in g.objects(me,SH.property) ]
    inverses = [ "^" + g.value(property,SH.predicate).n3()
                   for property in g.objects(me,SH.inverseProperty) ]
    properties = ignored + properties + inverses
    closed = "!(" + "|".join(ignored + properties + inverses) + ")"
    frag = """( ! EXISTS ( ?this %(closed) ?value ) )""" % { "closed":closed }
    return fragment(g,frag,"Value found for disallowed property", context)

## control of SPARQL query construction

# mapping from construct property name to function that processes it
constructs = { 'in':inC , 'class':classC, 'classIn':classInC, 'datatype':datatypeC,
               'datatypeIn':datatypeInC, 'directType':directTypeC,
               'minLength':minLengthC, 'maxLength':maxLengthC, 
               'minInclusive':minInclusiveC, 'minExclusive':minExclusiveC, 
               'maxInclusive':maxInclusiveC, 'maxExclusive':maxExclusiveC,
               'nodeKind':nodeKindC, 'pattern':patternC,
               'equals':equalsC, 'notEquals':notEqualsC,
               'lessThan':lessThanC, 'lessThanOrEquals':lessThanOrEqualsC,
               'propValues':propValuesC, 'list':listC,
               'hasValue':hasValueC, 'uniqueLang':uniqueLangC,
               'minCount':minCountC, 'maxCount':maxCountC,
               'shape':shapeC, 'not':notC, 'and':andC, 'or':orC,
               'closed':closedC , 'partition':partitionC }
compatabilityConstructs = { 'constraint':constraintC, 'property':propertyC,
                            'inverseProperty':inversePropertyC, 
                            'qualifiedValueShape':qualifiedValueShapeC,
                            'patternC':patternCompatibilityC,
                            'closedC':closedCompatabilityC }

# process a shape for shape invocation
def processShapeInvocation(g,shape) :
    # process scopes
    scopes = []
    severity = g.value(shape,SH.severity,default=Violation)
    for scopeValue in g.objects(shape,SH.scopeNode) :
        scopes.append("VALUES ?this { %s }" % scopeValue.n3())
    for scopeValue in g.objects(shape,SH.scopeClass) :
        scopes.append("?this rdf:type/rdfs:subClassOf* %s ." % scopeValue.n3())
    for scopeValue in g.objects(shape,SH.scopePropertyObject) :
        scopes.append("SELECT DISTINCT ?this WHERE { ?that %s ?this . }" % scopeValue.n3())
    for scopeValue in g.objects(shape,SH.scopePropertySubject) :
        scopes.append("SELECT DISTINCT ?this WHERE { ?this %s ?that . }" % scopeValue.n3())
    if (shape,SH.scopeAllObjects,true) in g :
        scopes.append("SELECT DISTINCT ?this WHERE { ?that ?property ?this . }")
    if (shape,SH.scopeAllSubjects,true) in g :
        scopes.append("SELECT DISTINCT ?this WHERE { ?this ?property ?that . }")
    for scopeValue in g.objects(shape,SH.scopeSPARQL) :
        scopes.append("SELECT DISTINCT ( ?scope AS ?this ) WHERE { %s }" % scopeValue.n3())
    if ( len(scopes) > 0 ) :
        scope = "{ { # SCOPE\n" + "\n} UNION # SCOPE\n { ".join(scopes) + " } }\n"
        body = processShape(g,shape,{"severity":severity,"outer":"","projection":"",
                                     "group":"","inner":scope})
        return """PREFIX sh: <http://www.w3.org/ns/shacl#>\n""" + body
    else :
#        print "No scopes for shape", shape
        return None

def processShape(g,shape,context,compatability=False) :
    shape,filters = processShapeInternal(g,shape,context,compatability=False)
    return shape

def processShapeInternal(g,shape,context,exclusions=[],compatability=False) :
    assert shape is not None
    severity = g.value(shape,SH.severity,default=context["severity"])
    context = dict(context,severity=severity)
    filters = [ processShape(g,filterValue,context)
                for filterValue in g.objects(shape,SH.filter) ]
    if ( len(filters) > 0 ) : # what about severity?
        filterBodies = [ """SELECT %(projection)s ?this WHERE { %(body)s }""" % \
                             { "projection":context["projection"], "body":body }
                         for body in filters ]
        context["inner"] = "{ " + context["inner"] + " ".join(exclusions) + \
                        "\n } MINUS { # FILTER\n" + \
                        "\n } MINUS { # FILTER\n".join(filterBodies) + \
                        "\n }"
    components = []
    if compatability : # iterate on compatability constructs
        for name,function in compatabilityConstructs.items() : 
            for comValue in g.objects(shape,SH[name]) :
                components.append(function(g,comValue,shape,context))
    for name,function in constructs.items() : # iterate on constructs
        for comValue in g.objects(shape,SH[name]) :
            components.append(function(g,comValue,context))
    return constructShape(g,shape,components,context),filters

def constructShape(g,shape,components,context) :
    if ( len(components) > 0 ) :
        body = "{ " + " } UNION { ".join(components) + " }"
        result = """# SHAPE start [shape]
  SELECT [projection] ?this ?message ?severity 
         ?subject ?predicate ?object ([shape] AS ?shape )
  WHERE { # SHAPE body\n  [body]
        } # SHAPE end [shape]\n""" 
        return substitute(result,g,context, shape=shape, body=body)
    else: return universalShape


## published interface

# process a single shape
def validateShape(dataGraph,shape,shapesGraph,printShapes=False) :
    if printShapes : print "SHAPE", curie(shapesGraph,shape)
    shape = processShapeInvocation(shapesGraph,shape)
    if shape is not None :
        if printShapes : print "SHAPE with scopes"
        return dataGraph.query(shape)
    else : return []

# process a shapes graph
def validate(dataGraph,shapesGraph,printShapes=False,printResults=False) :
    # process each shape in the graph
    shapesQuery = """SELECT DISTINCT ?shape 
                     WHERE { ?shape rdf:type/rdfs:subClassOf* %s }""" % SH.Shape.n3()
    results = []
    for row in shapesGraph.query(shapesQuery) :
        if isinstance(row[0],rdflib.term.URIRef) :
            for result in validateShape(dataGraph,row[0],shapesGraph,printShapes) :
                results.append(result)
                if printResults : print result
    return results

## execute for validation

def qname(node) :
  if isinstance(node,rdflib.term.URIRef) : return shapesGraph.qname(unicode(node))
  else : return node.n3(shapesGraph.namespace_manager)

def printResult(result) :
      try : print "SH",qname(result.shape),
      except AttributeError : None
      try : print "THIS",qname(result.this),
      except AttributeError : None
      try : print "S",qname(result.subject),
      except AttributeError : None
      try : print "P",qname(result.predicate),
      except AttributeError : None
      try : print "O",qname(result.object),
      except AttributeError : None
      try : print "MESSAGE",qname(result.message),
      except AttributeError : None
      try : print "SEV",qname(result.severity),
      except AttributeError : None
      print ""

if __name__ == "__main__" :
    shapesGraph = rdflib.Graph()
    shapesGraph.bind("xs",Namespace("http://www.w3.org/2001/XMLSchema#"))
    shapesGraph.bind("rdf",Namespace("http://www.w3.org/1999/02/22-rdf-syntax-ns#"))
    shapesGraph.bind("rdfs",Namespace("http://www.w3.org/2000/01/rdf-schema#"))
    shapesGraph.bind("sh",Namespace("http://www.w3.org/ns/shacl#"))
    dataGraph = rdflib.Graph()

    print "VALIDATING",sys.argv[1],"against shapes in",sys.argv[2]
    dataGraph = dataGraph.parse(sys.argv[1],format='turtle')
    shapesGraph = shapesGraph.parse(sys.argv[2],format='turtle')
    results = validate(dataGraph,shapesGraph,False,False)

    for result in results : printResult(result)
