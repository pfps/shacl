#!/usr/bin/python3
# Transform user syntax to an RDF graph

import pyparsing as pp
from user_syntax import shacl

import rdflib
from rdflib import Namespace
from rdflib.term import BNode
from rdflib.term import URIRef
from rdflib.term import Literal
from rdflib.namespace import RDF
from rdflib.namespace import RDFS
from rdflib.namespace import XSD

SH = Namespace("http://www.w3.org/ns/shacl#")

shapesGraph = None
nsm = None

def toLiteral(lit) : 
    if lit.get('lexical') is not None:
        if lit.get('datatype') is not None:
            return Literal(lit.lexical,datatype=toNode(lit.datatype))
        elif lit.get('language') is not None:
            return Literal(lit.lexical,lang=(lit.language))
        else: return Literal(lit.lexical)
    elif lit.get('boolean') is not None:
        return Literal(lit.boolean,datatype=XSD.boolean)
    else :
        number = ( str(lit.integer) if lit.get('integer') is not None else "" ) + \
                 ( str(lit.point) if lit.get('point') is not None else "" ) + \
                 ( str(lit.fraction) if lit.get('fraction') is not None else "" )
        if lit.get('exponent') is not None:
            return Literal(number+str(lit.exponent),datatype=XSD.double,normalize=False)
        elif lit.get('fraction') is not None:
            return Literal(number,datatype=XSD.decimal,normalize=False)
        else: return Literal(number,datatype=XSD.integer,normalize=False)

def toValue(what): # either a qname or a literal # doesn't handle IRIs
    if isinstance(what,pp.ParseResults) and what.qname == ':' :
        return toNode(what)
    else : return toLiteral(what)

def toNode(name) :  # only IRIs
    if isinstance(name,pp.ParseResults) and name.qname == ':' :
        for prefix,ns in nsm.namespaces() :
            if prefix == name[0] :
                return URIRef(ns + name[2])
        return URIRef("".join(name))
    else: return URIRef(name)

def makeList(node,link,elements) :
    here = node
    for e in elements :
        child = BNode()
        shapesGraph.add( (here,link,child) )
        shapesGraph.add( (child,RDF.first,e) )
        link = RDF.rest
        here = child
    shapesGraph.add( (here,link,RDF.nil) )

def transformList(node,link,components) :
    here = node
    for cmp in components :
        child = BNode()
        shapesGraph.add( (here,link,child) )
        this = transformComponent(cmp)
        shapesGraph.add( (child,RDF.first,this) )
        link = RDF.rest
        here = child
    shapesGraph.add( (here,link,RDF.nil) )

def transformPart(part) :
    if isinstance(part,pp.ParseResults) and part.inverse == "⁻¹" :
        node = BNode()
        shapesGraph.add( (node,SH.inverse,toNode(part[0])) )
        return node
    else : return toNode(part)

def transformPath(node,link,path) :
    if len(path) == 1 : shapesGraph.add( (node,link,transformPart(path[0])) )
    else : makeList(node,link,[transformPart(e) for e in path])
    return node

def transformScope(scopes,node) : 
    for scope in scopes :
        if scope.get('token') == "∈" :
            shapesGraph.add( (node,SH.scopeClass,toNode(scope[1])) )
        elif scope.get('token') == "¹" :
            if scope[1] == "?" : shapesGraph.add((node,SH.scopeAllSubjects,Literal(True)))
            else: shapesGraph.add( (node,SH.scopePropertySubject,toNode(scope[1])) )
        elif scope.get('token') == "²" :
            if scope[0] == "?" : shapesGraph.add((node,SH.scopeAllObjects,Literal(True)))
            else: shapesGraph.add( (node,SH.scopePropertyObject,toNode(scope[0])) )
        else:
            shapesGraph.add( (node,SH.scopeNode,toValue(scope[0])) )

def transformPathComponent(node,link,path1,path2) :
    node1 = BNode()
    node2 = BNode()
    shapesGraph.add( (node,link,node1) )
    shapesGraph.add( (node1,RDF.rest,node2) )
    shapesGraph.add( (node2,RDF.rest,RDF.nil) )
    transformPath( node1, RDF.first, path1 )
    transformPath( node2, RDF.first, path2 )

def transformComponent(component,node=None) :
    if component.get('token') is None : # named shape
        if node is None : return toNode(component[0])
        else:
            shapesGraph.add( (node,SH.shape,toNode(component[0])) )
            return node
    elif component.token == "→" :
        if node is None : 
            return transformShape(component)
        else :
            child = transformShape(component)
            shapesGraph.add( (node,SH['shape'],child) )
            return node
    if node is None :
        node = BNode()
        shapesGraph.add( (node,RDF.type,SH.Shape) )
    if component.token == "¬" :
        child = transformComponent(component.component)
        shapesGraph.add( (node,SH['not'],child) )
    elif component.token == "∧" :
        for cmp in component.component :
            transformComponent(cmp,node)
    elif component.token == "∨" :
        transformList(node,SH['or'],component.component)
    elif component.token == "∖" :
        transformList(node,SH['partition'],component.component)
    elif component.token == "∈" :
        if component.get('class') is not None :
            if len(component.get('class')) == 1 :
                shapesGraph.add( (node,SH['class'],toNode(component['class'][0])) )
            else : makeList(node,SH.classIn,[toNode(c) for c in component['class']])
        elif component.get('set') is not None :
            makeList(node,SH['in'],[toValue(c) for c in component['set']])
        else: print ( "ILLEGAL SYNTAX in ∈", component.dump() )
    elif component.token == "^^" :
        if len(component.get('datatype')) == 1 :
            shapesGraph.add( (node,SH['datatype'],toNode(component['datatype'][0])) )
        else : makeList(node,SH['datatypeIn'],[toNode(c) for c in component['datatype']])
    elif component.token == "⋹" :
        shapesGraph.add( (node,SH.directType,toNode(component[1])) )
    elif component.token == "ℓ" :
        if component[1] == '≤' :
            shapesGraph.add( (node,SH.maximumLength,
                              Literal(int(component[2]),datatype=XSD.integer)) )
        elif component[1] == '≥' :
            shapesGraph.add( (node,SH.minimumLength,
                              Literal(int(component[2]),datatype=XSD.integer)) )
        else: print ( "ILLEGAL SYNTAX in ℓ", component.dump() )
    elif component.token == ">" :
        shapesGraph.add( (node,SH.minExclusive,toLiteral(component[1])) )
    elif component.token == "≥" :
        shapesGraph.add( (node,SH.minInclusive,toLiteral(component[1])) )
    elif component.token == "<" :
        if len(component) == 2 :
            shapesGraph.add( (node,SH.maxExclusive,toLiteral(component[1])) )
        else : transformPathComponent(node,SH.lessThan,component[0],component[2])
    elif component.token == "≤" :
        if len(component) == 2 :
            shapesGraph.add( (node,SH.maxInclusive,toLiteral(component[1])) )
        else : transformPathComponent(node,SH.lessThanOrEquals,component[0],component[2])
    elif component.token == "IRI" :
        shapesGraph.add( (node,SH.nodeKind,SH.IRI) )
    elif component.token == "Literal" :
        shapesGraph.add( (node,SH.nodeKind,SH.Literal) )
    elif component.token == "BlankNode" :
        shapesGraph.add( (node,SH.nodeKind,SH.BlankNode) )
    elif component.token == "★" :
        if len(component) == 2 :
            shapesGraph.add( (node,SH.pattern, Literal(component[0][0])) )
        elif len(component) == 3 :
            makeList(node,SH.pattern,[Literal(component[0][0]),
                                      Literal(component[2][0])])
        else: print ( "ILLEGAL SYNTAX in ★", component.dump() )
    elif component.token == "=" :
        transformPathComponent(node,SH.equals,component[0],component[2])
    elif component.token == "∅" :
        transformPathComponent(node,SH.disjoint,component[0],component[2])
    elif component.token == "⟦" :
        makeList(node,SH.closed,[ transformPart(part) for part in component.part ])
    elif component.token == "∋" :
        shapesGraph.add( (node,SH.hasValue,toValue(component[1])) )
    elif component.token == "|" :
        if component[1] == '≤' :
            shapesGraph.add( (node,SH.maxCount,
                              Literal(int(component[2]),datatype=XSD.integer)) )
        elif component[1] == '≥' :
            shapesGraph.add( (node,SH.minCount,
                              Literal(int(component[2]),datatype=XSD.integer)) )
        elif component[1] == '=' :
            shapesGraph.add( (node,SH.minCount,
                              Literal(int(component[2]),datatype=XSD.integer)) )
            shapesGraph.add( (node,SH.maxCount,
                              Literal(int(component[2]),datatype=XSD.integer)) )
        else: print ( "ILLEGAL SYNTAX in |", component.dump() )
    elif component.token == "➀" :
        shapesGraph.add( (node,SH.uniqueLang,Literal("true",datatype=XSD.boolean)) )
    elif component.token == "⦇" :
        shape = transformComponent(component[1])
        shapesGraph.add( (node,SH.list,shape) )        
    elif component.token == "∝" :
        node1 = BNode()
        node2 = BNode()
        shapesGraph.add( (node,SH.propValues,node1) )
        shapesGraph.add( (node1,RDF.rest,node2) )
        shapesGraph.add( (node2,RDF.rest,RDF.nil) )
        transformPath( node1, RDF.first, component[0] )
        shape = transformComponent(component[2])
        shapesGraph.add( (node2,RDF.first,shape) )
    else : print( "ILLEGAL SYNTAX for component", component.dump() ) 
    return node

def transformFilter(filter,node) : 
    child = transformComponent(filter)
    shapesGraph.add((node,SH.filter,child))

def transformShape(shape,node = None) :
    if node is None : node = BNode()
    shapesGraph.add( (node, RDF.type, SH.Shape) )
    if shape.get('filter') is not None :
        transformFilter(shape.filter,node)
    if shape.get('body') is not None :
        transformComponent(shape.body,node)
    else:
        transformComponent(shape,node)
    return node

def transform(dfns) :
    for dfn in dfns :
#        print ("DEFINITION",dfn)
        if dfn.token == '@prefix' :
#            print ("Namespace",dfn[1],"is",dfn[3])
            nsm.bind(dfn[1],dfn[3],replace=True)
        else :
            n = BNode() if dfn.get('name') is None else toNode(dfn.get('name'))
            if dfn.get('scope') is not None : transformScope(dfn.get('scope'),n)
            transformShape(dfn.get('shape'),n)

def transformFile() :
    global shapesGraph
    shapesGraph = rdflib.Graph()
    global nsm
    nsm = shapesGraph.namespace_manager
    nsm.bind('sh',SH)
    print( "TRANSFORMING",sys.argv[1])
    dfns =  shacl.parseFile(sys.argv[1],True)
    transform(dfns)
    print ( bytes.decode(shapesGraph.serialize(format='turtle')) )

import sys
if __name__ == "__main__" : transformFile()

