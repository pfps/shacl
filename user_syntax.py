# python3
# Parsing of user syntax
# Needs tweaking to handle recent changes

import pyparsing as pp

boolean  = pp.Literal('true')('boolean') ^ pp.Literal('false')('boolean')
nums     = pp.Word(pp.nums)
integer  = pp.Combine(pp.Optional(pp.Literal('-')^pp.Literal('+')) + nums)
exponent = pp.Combine((pp.Literal('e')^pp.Literal('E')) + integer)('exponent')
point    = pp.Literal('.')('point')
number   = ( integer('integer') + pp.Optional(point + pp.Optional(nums)('fraction')) + \
                 pp.Optional(exponent) ) ^ \
	     ( point + nums('fraction') + pp.Optional(exponent) )

prefixName         = pp.Word(pp.alphas,pp.alphanums)
name               = pp.Word(pp.alphas,pp.alphanums)
IRI                = pp.QuotedString('<',escChar='\\',endQuoteChar='>')('IRI')
qname              = pp.Group(prefixName + pp.Literal(':')('qname') + name)
name               = qname # | IRI # conflicts with <n

language           = pp.Word(pp.alphas,pp.alphanums+'-')
quotedString       = pp.QuotedString('"',escChar='\\',endQuoteChar='"')

literal = pp.Group ( quotedString('lexical') +
                     ( pp.Optional ( '@' + language('language') ) ^
                       pp.Optional ( '^^' + name('datatype') ) ) ^
                     number ^ boolean )

string             = pp.Group(pp.QuotedString('"','\\'))
nonnegativeInteger = pp.Word(pp.nums)
regex              = string

# just simple versions for now


property           = name
clss               = name
datatype           = name
value              = name ^ literal

pathpart  = property ^ pp.Group( property + pp.Literal('⁻¹').setResultsName('inverse') )
path      = pp.Group( pp.OneOrMore( pathpart ) )

atomic =  pp.Or( [
             ( pp.Literal('∈')('token') + clss.setResultsName('class',True) +
               pp.ZeroOrMore( '∪' + clss.setResultsName('class',True) ) ) , 
	     ( pp.Literal('^^')('token') +
               datatype.setResultsName('datatype',True).setResultsName('datatype',True) +
               pp.ZeroOrMore( '∪' + datatype.setResultsName('datatype',True) ) ) ,
 	     ( pp.Literal('∈')('token') +
               '{' + pp.ZeroOrMore(value.setResultsName('set',True)) + '}' ) ,
 	     ( pp.Literal('⋹')('token') + clss ) ,
 	     ( pp.Literal('ℓ')('token') + '≤' + nonnegativeInteger ) ,
 	     ( pp.Literal('ℓ')('token') + '≥' + nonnegativeInteger ) ,
             ( pp.Literal('>')('token') + literal ) ,
 	     ( pp.Literal('≥')('token') + literal ) ,
 	     ( pp.Literal('<')('token') + literal ) ,
 	     ( pp.Literal('≤')('token') + literal ) ,
 	     pp.Literal('IRI')('token') ,
 	     pp.Literal('Literal')('token') ,
 	     pp.Literal('BlankNode')('token') ,
 	     ( regex + pp.Literal('★')('token') + pp.Optional( string ) ) ,
 	     ( path + pp.Literal('=')('token') + path ) ,
 	     ( path + pp.Literal('∅')('token') + path ) ,
 	     ( path + pp.Literal('<')('token') + path ) ,
 	     ( path + pp.Literal('≤')('token') + path ) ,
 	     ( pp.Literal('⟦')('token') +
               pp.ZeroOrMore( pathpart.setResultsName('part',True) ) + '⟧' ) ,
 	     ( pp.Literal('∋')('token') + value ) ,
 	     ( pp.Literal('|')('token') + '≥' + nonnegativeInteger + '|' ) ,
 	     ( pp.Literal('|')('token') + '≤' + nonnegativeInteger + '|' ) ,
 	     ( pp.Literal('|')('token') + '=' + nonnegativeInteger + '|' ) ,
 	     ( pp.Literal('➀')('token') ) ,
 	     name ] )

disjunction = pp.Forward()

primary = pp.Forward()

primary <<   ( pp.Or ( [ atomic ,
                      ( pp.Literal('¬')('token') + pp.Group(primary)('component') ) ,
 	              ( path.setResultsName('path') + pp.Literal('∝')('token') +
                        pp.Group(primary)('component') ) ,
 	              ( pp.Literal('⦇')('token') + pp.Group(primary)('component') + '⦈' ) ,
                      ( pp.Literal('(').suppress() + disjunction +
                        pp.Literal(')').suppress() ) ] ) )

def partitionPP(toks) :
    if len(toks) == 1 : return toks[0]
    else : return None

partition = ( pp.Group(primary).setResultsName('component',True) +
              pp.Optional ( pp.Literal('∖')('token') +
                  pp.ZeroOrMore(pp.Group(primary).setResultsName('component',True)+'∖') )
            ).setParseAction(partitionPP)

def conjunctionPP(toks) :
    if len(toks) == 1 : return toks[0]
    else : return None

conjunction = ( pp.Group(partition).setResultsName('component',True) +
                pp.ZeroOrMore( pp.Literal('∧')('token') +
                   pp.Group(partition).setResultsName('component',True))
              ).setParseAction(conjunctionPP)

def shapePP(toks) :
    if toks.token == '→' :
        toks["filter"] = toks[0]
        toks["body"] = toks[2]
        return toks
    else :
        toks["body"] = toks[0]
        toks["token"] = '→'
        return toks

shape = ( pp.Group(conjunction) +
          pp.Optional ( pp.Literal('→')('token') +
                        pp.Group(conjunction) ) ).setParseAction(shapePP)

def reduce(shape) :
    if shape.get('filter') is None : return shape.get('body')
    else : return shape

def disjunctionPP(toks) :
    if len(toks) == 1 : return toks[0]
    else : return None

disjunction << ( pp.Group(shape.addParseAction(reduce)).setResultsName('component',True) +
                 pp.ZeroOrMore( pp.Literal('∨')('token') +
                  pp.Group(shape.addParseAction(reduce)).setResultsName('component',True) )
	       ).setParseAction(disjunctionPP)

scope     = pp.Group ( value ^ \
	               pp.Literal('∈').setResultsName('token') + clss ^ \
	               pp.Literal('¹').setResultsName('token') + property ^ \
	               property + pp.Literal('²').setResultsName('token') ^ \
	               pp.Literal('¹').setResultsName('token') + '?' ^ \
	               '?' + pp.Literal('²').setResultsName('token') )

scoping   = scope.setResultsName('scope',True) + \
                pp.ZeroOrMore( '∪' + scope.setResultsName('scope',True) ) + \
		pp.Literal('⊩')('token') + pp.Group(shape).setResultsName('shape')

definition = name('name') + '≡' + ( pp.Group(shape)('shape') ^ scoping )

prefix = pp.Keyword('@prefix')('token') + prefixName + ':' + IRI

shacl = pp.ZeroOrMore ( pp.Group( prefix ^ definition ^ scoping ) )

def parse(tag,production,string) :
    print( tag, string)
    dfns = production.parseString(string,True)
    print(tag,dfns.dump())
    print ("")

def parseSHACL(tag,string) :
    print( tag, string)
    dfns = shacl.parseString(string,True)
    for dfn in dfns :
        print(tag, "DFN START", dfn)
        print(tag, "DFN", "name", dfn.name)
        print(tag, "DFN", "components", dfn.components)
        print(tag, "DFN", "scope", dfn.scope)
        print(tag, "DFN", "token", dfn.shape.token)
        print(tag, "DFN", "filtr", dfn.shape.get('filter'))
        print(tag, "DFN", "body ", dfn.shape.get('body'))
        if dfn.shape.get('filter') is not None :
            print (tag + " DFN filtr dump", dfn.shape.filter.dump() )
        if dfn.shape.get('body') is not None :
            print (tag + " DFN body  dump", dfn.shape.body.dump() )
    print ("")


