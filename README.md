# shacl
Implementations and metamodels for SHACL variants

* Notes:		General notes on the implementation(s)
* syntax.text:	Description of my proposal for SHACL syntax
* metamodel.ttl:	Metamodel for this syntax, including shapes to validate shape graphs
* metamodel-alternative.ttl:	Alternative metamodel
* user_syntax.text:	User-friendly version of syntax
* shacl.py:	Implementation of the core of SHACL in this syntax
* shacl_template.py:	Implementation of template mechanism and core SHACL minus partition in templates
* user_syntax.py:	Parser for user syntax
* transform.py:		Transform user syntax to RDF graph