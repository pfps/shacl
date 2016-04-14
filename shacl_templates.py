## An implementation of SHACL based on query generation.
##
## Uses the rdflib package and its SPARQL implementation.
##
## Implements my proposed syntax.
## Validation reports are generated as result sets
##   (except that severities may be handled differently)
## but not all the information in them may conform to the spec.
## All constructs are handled by substitution into templates,
## except partition, which uses an internal-only interface

## NOT HANDLED
## per-language messages

from __future__ import print_function
from __future__ import unicode_literals
from builtins import str
from past.builtins import basestring

import string
import itertools
import rdflib
from rdflib import Namespace
from rdflib.term import BNode
from rdflib.term import URIRef
from rdflib.term import Literal
from rdflib.namespace import RDF
from rdflib.namespace import XSD

import sys
sys.setrecursionlimit(10000) 

metamodel = None

true = Literal("true",datatype=XSD.integer)
SH = Namespace("http://www.w3.org/ns/shacl#")
Info = SH.Info
Warning = SH.Warning
Violation = SH.Violation

## better way to do substitution
## Substitute for an expression with operators
##  name - value of argument
##  "string" - string
##  l(e,"string") - value(s) of e joined by string
##  p(e) - path of e in graph
##  s(e) - shape of e in graph
##  c(p,e) - shape of e in graph, run on values of p

import pyparsing as pp
term         = pp.Forward()
identifier   = pp.Word(pp.alphas,pp.alphanums)
strng        = pp.Group(pp.quotedString)
lpar         = pp.Literal('(').suppress()
rpar         = pp.Literal(')').suppress()
list         = pp.Group ( 'l' + lpar + term + pp.Optional(strng) + rpar )
path         = pp.Group ( 'p' + lpar + identifier + rpar  )
shape        = pp.Group ( 's' + lpar + identifier + rpar )
context      = pp.Group ( 'c' + lpar + ( path ^ strng )  + identifier + rpar )
term         << ( list ^ path ^ shape ^ context ^ identifier ^ strng  )
substitution = pp.Literal('[').suppress() + term + pp.Literal(']').suppress() \
               ^ pp.Literal('[[') ^ pp.Literal(']]')
pp.quotedString.setParseAction(pp.removeQuotes)
substitution.parseWithTabs()

def toSPARQL(g,value) :
    if isinstance(value,rdflib.term.URIRef) : return value.n3()
    elif isinstance(value,rdflib.term.BNode) : return '"'+value+'"'
    elif isinstance(value,rdflib.term.Literal) :
        if value.datatype == XSD.integer : return str(value)
        if value.datatype == XSD.decimal : return str(value)
        if value.datatype == XSD.double : return str(value)
        else : return value.n3()
    else : return value

def fetch(g,identifier,context,listp=False) :
    if listp : return listElements(g,context[identifier])
    else : return [ context[identifier] ]

def process(g,parse,context,listp=False) :
    if isinstance(parse,basestring) : # identifier
        return fetch(g,parse,context,listp)
    elif len(parse) == 1 : # string
        return [ str(parse[0]) ]
    else :
        if parse[0] == 'l' :
            l = [toSPARQL(g,e) for e in process(g,parse[1],context,True)]
            if len(parse)==2 : j = " "
            else : j = substitut(parse[2][0],g,context)
            return [ j.join(l) ]
        elif parse[0] == 'p' :
            l = fetch(g,parse[1],context,listp)
            return [ pathtoSPARQL(g,e) for e in l ]
        elif parse[0] == 's' : 
            l = fetch(g,parse[1],context,listp)
            return [ processShape(g,e,context) for e in l ]
        elif parse[0] == 'c' :
            p = process(g,parse[1],context)[0]
            l = fetch(g,parse[2],context,listp)
#            print ("SUB",context)
            return [ newContext(g,p,'"In path %s "'%p,e,context) for e in l ]

def substitut(string,g,context,**kwargs) :
    result = ""
    last = 0
    context = dict(context,**kwargs) # new dictionary adding **kwargs
    for parse,start,end in substitution.scanString(string) :
        result = result + string[last:start]
        sub = process(g,parse.asList()[0],context)
        sub = [ toSPARQL(g,e) for e in sub ]
        result += " ".join(sub)
        last = end
    return result + string[last:]

def listElements(g,head) :
    elements = []
    while ( ( head is not None ) and ( head != RDF.nil ) ) :
        elements.append(g.value(head,RDF.first))
        head = g.value(head,RDF.rest)
    if ( head is None ) : print( "MALFORMED LIST")
    return elements

universalShape = "SELECT ?subject WHERE { BIND ( true AS ?subject ) FILTER ( true=false ) }"

def partitionC(g,value,context) :		# SubSelect
    children =  listElements(g,value)
    bodies = []
    exclusions = []
    for child in children :
        body,filters = processShapeInternal(g,child,context,exclusions=exclusions)
        bodies.append(body)
        excl = "{ " + " } UNION { ".join(filters) + " } "
        excl = substitut("{ SELECT [projection] ?this # EXCLUSION\n  WHERE { [excl] } } ",
                               g,context,excl=excl)
        exclusions.append(excl)
    final = substitut(""" { SELECT [projection] ?this ?message # PARTITION FINAL
    WHERE { [outer] [inner] [exclusion] } 
    VALUES (?message) { ( [message] ) } } """,g,context,
                       exclusion=" ".join(exclusions),message='"Partition not exhaustive"')
    bodies.append(final)
    bodys = "{ " + "\n } UNION {\n".join(bodies) + "\n }"
    result = """ # PARTITION
  SELECT [projection] ?this ?subject ?property ?object ?PS ?CS ?severity ([component] AS ?component) ?message
  WHERE { [bodys] }   """
    return substitut(result,g,context,component=SH['partition'],bodys=bodys)

def constructQuery(g,pattern,filter,having,context) :
    pattern = pattern if pattern is not None else ""
    filter = """FILTER ( ! %(filter)s )""" % { "filter":filter } \
             if filter is not None else ""
    having = """GROUP BY ?this HAVING ( %(having)s )\n""" % { "having":having } \
             if having is not None else ""
    body = """# FRAGMENT 
  SELECT [projection] ?this (?this AS ?subject) ([PS] AS ?PS) ?severity ([component] AS ?component) ?message
  WHERE { [outer] [inner] %(pattern)s %(filter)s }
  %(having)s VALUES (?message ?severity) { ( [message] [severity] ) }""" % \
      { "filter":filter, "pattern":pattern, "having":having }
    result = substitut(body,g,context)
    return result

def processShapeInternal(g,shape,context,exclusions=[]) :
    assert shape is not None
    severity = g.value(shape,SH.severity,default=context["severity"])
    context = dict(context,severity=severity)
    filters = [ processShape(g,filterValue,context)
                for filterValue in g.objects(shape,SH.filter) ]
    if ( len(filters) > 0 ) : # filters use severity Violation
        fBodies = [ """SELECT %(projection)s ?this WHERE { { %(body)s }
				FILTER ( sameTerm(?severity,%(violation)s) ) }""" % \
                    { "projection":context["projection"], "body":body,
                      "violation":Violation.n3() }
                         for body in filters ]
        context["inner"] = "{ " + context["inner"] + " ".join(exclusions) + \
                        "\n } MINUS { # FILTER\n" + \
                        "\n } MINUS { # FILTER\n".join(fBodies) + \
                        "\n }"
    components = []
    for name,function in constructs.items() : # iterate on constructs
        for comValue in g.objects(shape,SH[name]) :
            components.append(function(g,comValue,context))
    assert metamodel is  not None
    for template in metamodel.subjects(RDF.type,SH.ComponentTemplate) :
        for value in g.objects(shape,template) :
            components.append( constructTemplate(g,template,value,context) )
    result = constructShape(g,shape,components,context)
    return result, filters

def constructShape(g,shape,components,context) :
    if ( len(components) > 0 ) :
        body = "{ " + " } UNION { ".join(components) + " }"
        result = """# SHAPE start [shape]
  SELECT [projection] ?this ?subject ?predicate ?object ?PS ?CS 
	?component ([shape] AS ?shape) ?message ?severity
  WHERE { # SHAPE body\n  [body]
        } # SHAPE end [shape]\n""" 
        return substitut(result,g,context, shape=shape, body=body)
    else: return universalShape

def fragmentPattern(g,code,message,context) :
    body = """# FRAGMENT 
  SELECT [projection] ?this (?this AS ?subject) ([PS] AS ?PS) 
	([severity] AS ?severity) ([component] AS ?component) ([message] AS ?message)
  WHERE { [outer] [inner]
          [code] }"""
    result = substitut(body,g,context, code=code, message='"'+message+'"')
    return result

def fragment(g,code,message,context) :
    filter = """FILTER ( ! %(code)s )""" % { "code":code }
    return fragmentPattern(g,filter,message,context)

def parttoSPARQL(g,part) :
    return ( "^" + g.value(part,SH.inverse).n3() ) \
           if (part,SH.inverse,None) in g else part.n3()

def pathtoSPARQL(g,value) :
    if value == RDF.nil : print( "EMPTY PATH" ); return ""
    path = [ parttoSPARQL(g,part) for part in listElements(g,value) ] \
           if (value,RDF.rest,None) in g else [ parttoSPARQL(g,value) ]
    return "/".join(path)

# set up a new context that is the values of a path from the current context
def newContext(g,path,message,childShape,context) :
    print("NEWCONTEXT",path,context)
    childouter = """{ SELECT (?p AS ?parent) (?gp AS ?grandparent)
	WHERE { { SELECT (?this AS ?p) (?parent AS ?gp) WHERE { %(inner)s } }
	} }""" % { "inner":context["inner"] }
    childinner = """{ ?parent %(path)s ?this . }""" % { "path":path }
    childcontext=dict(severity=context["severity"],outer=childouter,projection="?parent",
                      group="GROUP BY ?parent",inner=childinner, PS=childShape)
    child = processShape(g,childShape,childcontext)
    result ="""# newContext
  SELECT [projection] ?this ?subject ?predicate ?object ?PS ?CS ?severity ?component ?message
  WHERE { { [child] } UNION
	  { SELECT [projection] ?this (?this AS ?subject) ("[path]" AS ?predicate) ?object
		([PS] as ?PS) ([CPS] as ?CS) ([severity] AS ?severity) ([component] AS ?component) ([message] AS ?message)
	    WHERE { 
	        { SELECT (?o AS ?object) (?p AS ?this) WHERE
		  { SELECT (?parent AS ?p) (?this AS ?o ) WHERE {
			{ [child] 
			  } FILTER ( sameTerm(?PS,[CPS]) ) 
		} } }
		[outer] [inner] 
	    }
	  }
    }"""
    return substitut(result,g,context,message=message,path=path,child=child,CPS=childShape)

# non-template SHACL constructs - property name, function that processes it
constructs = { 'partition':partitionC}

# process a shape for shape invocation
def processShapeInvocation(g,shape,printShapes=False) :
    scopes = []
    severity = g.value(shape,SH.severity,default=Violation)
    scope = processScopes(g,shape,printShapes)
    if scope is not None :
        body = processShape(g,shape,{"severity":severity,"outer":"","projection":"?parent",
		                     "group":"","inner":scope,"PS":shape})
        if body == "" and printShapes : print( "No bodies for shape", shape)
        return None if body == "" else \
            """PREFIX sh: <http://www.w3.org/ns/shacl#>\n""" + body
    else :
        if printShapes : print( "No scopes for shape", shape)
        return None

def processScopes(g,shape,printShapes=False) :
    assert shape is not None
    scopes = []
    severity = g.value(shape,SH.severity,default=Violation)
    assert metamodel is not None
    for template in metamodel.subjects(RDF.type,SH.ScopeTemplate) :
        for value in g.objects(shape,template) :
            scopes.append( constructScopeTemplate(g,template,value) )
    result = constructScope(g,shape,scopes,context)
    return result

def constructScopeTemplate(g,template,argument) :
    context = dict()
    context["argument"] = argument # add argument value to context
    for argComponent in metamodel.objects(template,SH.propValues) : # look for arguments
        argPath = pathtoSPARQL(metamodel,metamodel.value(argComponent,RDF.first))
        argShape = metamodel.value(metamodel.value(argComponent,RDF.rest),RDF.first)
        argName = metamodel.value(argShape,SH.argumentName)
        argDefault = metamodel.value(argShape,SH.defaultValue,
                                     default= Literal("",datatype=XSD.string))
        if argName is not None :
            argVQuery = "SELECT ?value WHERE { ?shape %s ?value }" % argPath
            argVs = [row[0] for row in g.query(argVQuery,initBindings={'shape':argument})]
            argV = argVs[0] if len(argVs) > 0 else argDefault
            context[str(argName)]= argV
    query = metamodel.value(template,SH.templateQuery)
    if query is not None :
        return substitut(query,g,context)
    print( "SCOPE HAS NO CODE",template)
    return ""

def constructScope(g,shape,scopes,context) :
    if ( len(scopes) > 0 ) :
        scope = "{ SELECT ( ?scope as ?this ) WHERE { { # SCOPE\n" + \
                "\n} UNION # SCOPE\n { ".join(scopes) + " } } }\n"
        return scope
    else : return None

# process a shape in a context
def processShape(g,shape,context) :
    assert shape is not None
    severity = g.value(shape,SH.severity,default=context["severity"])
    context = dict(context,severity=severity)
    filters = [ processShape(g,filterValue,context)
                for filterValue in g.objects(shape,SH.filter) ]
    if ( len(filters) > 0 ) : # what about severity?
        filterBodies = [ """SELECT %(projection)s ?this WHERE { %(body)s }""" % \
                             { "projection":context["projection"], "body":body }
                         for body in filters ]
        context["inner"] = "{ " + context["inner"] + "\n } MINUS { # FILTER\n" + \
                "\n} MINUS { # FILTER\n".join(filterBodies) + "\n }"
    components = []
    for name,function in constructs.items() : # iterate on constructs
        for comValue in g.objects(shape,SH[name]) :
            components.append(function(g,comValue,context))
    assert metamodel is not None
    for template in metamodel.subjects(RDF.type,SH.ComponentTemplate) :
        for value in g.objects(shape,template) :
#            print("SHAPE CONTEXT",context)
            components.append( constructTemplate(g,template,value,context) )
    return constructShape(g,shape,components,context)

def constructTemplate(g,template,argument,context) :
    context = dict(context) # copy the context to make changes to it
    context["argument"] = argument # add argument value to context
    context["component"] = template # add template as component
#    print("TEMPLATE",argument,template,context)
    for argComponent in metamodel.objects(template,SH.propValues) : # look for arguments
        argPath = pathtoSPARQL(metamodel,metamodel.value(argComponent,RDF.first))
        argShape = metamodel.value(metamodel.value(argComponent,RDF.rest),RDF.first)
        argName = metamodel.value(argShape,SH.argumentName)
        argDefault = metamodel.value(argShape,SH.defaultValue,
                                     default= Literal("",datatype=XSD.string))
        if argName is not None :
            argVQuery = "SELECT ?value WHERE { ?shape %s ?value }" % argPath
            argVs = [row[0] for row in g.query(argVQuery,initBindings={'shape':argument})]
            argV = argVs[0] if len(argVs) > 0 else argDefault
            context[str(argName)]= argV
    message = '"'+substitut(metamodel.value(template,SH.templateMessage),g,context)+'"'
    context["message"] = message # add message to context
    pattern = metamodel.value(template,SH.templatePattern)
    filter = metamodel.value(template,SH.templateFilter)
    having = metamodel.value(template,SH.templateHaving)
    if ( pattern is not None or filter is not None or having is not None ) :
        return constructQuery(g,pattern,filter,having,context)
    else :
        query = metamodel.value(template,SH.templateQuery)
        if query is not None :
#            print("TEMPLATE CONTEXT",context)
            return substitut(query,g,context)
    print( "TEMPLATE HAS NO CODE",template)
    return ""

def setupMetamodel(meta="./metamodel.ttl") :
    global metamodel
    metamodel = rdflib.Graph()
    metamodel = metamodel.parse(meta,format='turtle')

# process a single shape
def validateShape(dataGraph,shape,shapesGraph,printShapes=False) :
    if printShapes : print( "SHAPE NAME ", shape)
    shape = processShapeInvocation(shapesGraph,shape,printShapes)
#    if printShapes : print( "SHAPE SHAPE", shape)
    if shape is not None : return dataGraph.query(shape)
    else : return []

# process a shapes graph
def validate(dataGraph,shapesGraph,printShapes=False,validateShapes=False) :
    setupMetamodel(meta="./metamodel.ttl")
    # validate the shapes graph (but not the metamodel graph!)
    if validateShapes :
        print( "VALIDATING shapes graph against metamodel")
        validate(shapesGraph,metamodel)
        print( "VALIDATING shapes graph against metamodel END")
    # process each shape in the graph
    shapesQuery = """SELECT DISTINCT ?shape 
                     WHERE { ?shape rdf:type/rdfs:subClassOf* %s }""" % SH.Shape.n3()
    for row in shapesGraph.query(shapesQuery) :
        if isinstance(row[0],rdflib.term.URIRef) :
            for row in validateShape(dataGraph,row[0],shapesGraph,printShapes=printShapes) :
                printResult(row,shapesGraph)

def qname(node,graph) :
  if isinstance(node,rdflib.term.URIRef) : return graph.qname(str(node))
  else : return node.n3(graph.namespace_manager)

def printResult(result,graph) :
      try : print( "SH",qname(result.shape,graph), end=" ")
      except AttributeError : None
      try : print( "THIS",qname(result.this,graph), end=" ")
      except AttributeError : None
      try : print( "S",qname(result.subject,graph), end=" ")
      except AttributeError : None
      try : print( "P",qname(result.predicate,graph), end=" ")
      except AttributeError : None
      try : print( "O",qname(result.object,graph), end=" ")
      except AttributeError : None
      try : print( "MESSAGE",qname(result.message,graph), end=" ")
      except AttributeError : None
      try : print( "SEV",qname(result.severity,graph), end=" ")
      except AttributeError : None
      print ("")
