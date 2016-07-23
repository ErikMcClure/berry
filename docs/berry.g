ID ::= [^!"#$%&'()*+,\-./:;<=>?@[\\\]^`{|}~ \t\r\n\f]+
NUMBER ::= ([0-9]+(\.[0-9]+)?|0x[0-9A-Fa-f]+|0b[01]+|0o[0-7]+)([eE]-?[0-9]+)?[^!"#$%&'()*+,\-./:;<=>?@[\\\]^`{|}~ \t\r\n\f]+
OPERATOR ::= [^!"#$%&'()*+,\-./:;<=>?@[\\\]^`{|}~]+
STRING ::= '"' [^"]* '"' // Note that we allow multiline strings
CHARACTER ::= '\'' [^']+ '\''
MACRO ::= '`' [^`]+ '`'
	
berry : chunk+ ;
pubpriv : 'public' | 'private' ;
decl : attribute* pubpriv? ( template? ( class | funcvarbind ) | typedef | enum ) ;
chunk : decl | namespace | using | assume | ruleimport | impl | basicmacro | attributemacro ;
rawtype : 'i8' | 'i16' | 'i32' | 'i64' | 'u8' | 'u16' | 'u32' | 'u64' | 'float' | 'double' | 'string' | 'string16' | 'string32' | 'void' | 'bool' | 'char' | 'byte' | 'int' | 'uint' | 'f16' | 'f32' | 'f64' ;

dotid : ID ( '.' ID )* ;
attribute : '[' ID invocation? ']' ;
enum : 'enum' ID ( ':' rawtype ) ? '{' ID ( '=' expr )? ( ',' ID ( '=' expr )? )* '}' ;
using : 'using' dotid ;
namespace : 'namespace' dotid '{' chunk+ '}' ;
algebraic_type : '{' ( algebraic_inner ( ID ';' ( algebraic_inner ID ';' )* | ( '|' algebraic_inner )* ) )? '}' ;
algebraic_inner : type | ( ID algebraic_type ) ;
typedef : 'type' ID '=' ( type ';' | algebraic_type ) ;
assert : 'assert' '(' expr ')' ;
assume : 'assume' '(' expr ')' ;
ruleimport : 'import' STRING ; // some parsers really hate "import" as a rule
macro_embed : MACRO expr? (MACRO expr?)* ;
macro_body : '{' (statement | macro_embed ';')* '}' | macro_embed ;
basicmacro : 'macro' type? ID ( '(' ( basicdecl ( ',' basicdecl )* )? ')' )? macro_body? ';' ; // You can have MACROs as values in the macro block itself, or just have one macro made entirely out of a macro_embed
attributemacro : 'attribute' ID '(' ( vardecl ( ',' vardecl )* )? ')' macro_body? ';' ;

vartype : type | 'var' ;
vardecl : vartype ID ;
basicdecl : vartype? ID ;
lambdadecl : basicdecl | '_' ;
paramdecl : basicdecl ( '=' expr )? | '_';
strictdecl : type ID ( '=' expr )? ;
varbind : vardecl ( '=' expr )? ';' ;
funcvartype : vartype | '{' type ('|' type)+ '}' ;
vartypelambda : '[' ( type ('|' type)* | 'var' ) ']';

block : '{' statement* '}' ;
optblock : block | optstatement ;
template_param : type ( ID ( OPERATOR expr )? | ( ':' type ( '+' type )* )? ( '=' type )? );
template : 'template' '[' template_param ( ',' template_param )* ( ',' ID '...' )? ']' ;
impl : 'impl' dottype (':' dottype)? ('{' classdecl* '}' | ';') ;
funcmods : 'static' | 'pure' | 'virtual' | 'abstract' ;
funcbegin : funcmods* funcvartype (ID | 'op' OPERATOR ) ;
funcend : '(' ( paramdecl ( ',' paramdecl )* )? ')' ( block | ';' ) ;
//function : funcbegin funcend;
funcvarbind : funcbegin ( '=' expr ';' | ';' | funcend ) ;

classdecl : decl | 'public:' | 'private:' ;
class : ( 'class' | 'trait' ) ID ( ':' dottype ( ',' dottype)* )? '{' classdecl* '}' ;

slicesuffix : '[' ( expr ( ( ':' expr)+ | ( ',' expr )+ )? | ':' | ) ']' ;
dottype : (ID | rawtype) slicesuffix* ( '.' (ID | rawtype) slicesuffix* )* ;
ntype : ( 'const' 'unsafe'? | 'unsafe' 'const'?)? dottype ( '!' | ( 'const'? ( '@' | '$' ) )* );
functype : 'fn' ( '.' ( dotid | rawtype | '(' dottype ')' ) )? vartypelambda? '(' ( type ( ',' type)* )? ')' ;
type : ntype | functype;

trycatch : 'try' block ( 'catch' '(' strictdecl ')' block )* ( 'else' block )? ( 'finally' block )? ;
optstatement : ( termvardecl | lambda ) ';' | forloop | with | loop | switch | ifgroup | 'static' varbind | 'break' NUMBER? ';' | 'continue' NUMBER? ';' | 'return' expr? ';'  | assert | assume | ';' ;
statement : optstatement | trycatch | block ; // we must exclude trycatch and block from optblock statements

forloop : 'for' '(' ( ';' expr? ';' expr? | vardecl ( ('=' expr)? ';' expr? ';' expr? | 'in' expr ) ) ')' optblock ;
with : 'with' '(' expr ')' block ;
loop : 'loop' optblock ( 'while' '(' expr ')' ) ;
switch : 'switch' '(' expr ')' '{' ( 'case' factor ID? ':' statement* )* '}' ;
ifgroup : 'if' '(' expr ')' optblock ( options {greedy=true;} : 'else' 'if' '(' expr ')' optblock)* ( options {greedy=true;} : 'else' optblock)?;

termvardecl : OPERATOR* factor termaftervardecl ;
termaftervardecl : (OPERATOR+ ( factor termafter )? | rawtype | 'var') | ID ( '=' expr)? | ;
	
expr : ternary | lambda ;
ternary : term ( '?' expr ':' expr )? ;
term : OPERATOR* factor termafter;
termafter : OPERATOR+ ( factor termafter )? | ;
factor : value | '(' expr ')' ;
initlist : '{' ( ID '=' expr ( ',' ID '=' expr)* | expr ( ',' expr )* )?  '}' ;
value : NUMBER | STRING | CHARACTER | 'null' | 'true' | 'false' | '.'? ID valueafter* initlist? ;
valueafter : slicesuffix | invocation | '.' ID ;

invocation : '(' ( expr ( ',' expr )* )? ')' ;
lambda : 'fn' vartypelambda? '(' ( lambdadecl ( ',' lambdadecl)* )? ')' funcmods* ( ':' '@'? ID (',' '@'? ID)* )? ( block | '->' expr ) ;