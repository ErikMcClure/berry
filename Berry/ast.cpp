// Copyright ©2015 Black Sphere Studios

#include "ast.h"
#include "bss-util/cTrie.h"
#include <iostream>

void EmitError(Program& p, const char* s, TOKEN*& t)
{
  p.errors.Add(s);
  std::cout << s << std::endl;
  ++t;
}

Node* CreateNode(SYNTAX_PART s)
{
  Node* n = new Node(s);
  n->node.typeset<Node::NODES>();
  return n;
}

Node* CreateNodeID(SYNTAX_PART s, ID id)
{
  return new Node(s, id);
}

Node* CreateNodeStr(SYNTAX_PART s, cStr&& str)
{
  return new Node(s, std::move(str));
}

void DiscardToken(TOKEN*& t, Tokens target)
{
  if(t->token == target)
    ++t;
}

void ExpectToken(Program& p, TOKEN*& t, Tokens target)
{
  if(t->token == target)
    ++t;
  else
    EmitError(p, cStrF("Expected token %i. Continuing to parse as if it existed.", target), t);
}

#define CALLFAILURE(tok) if(t->token != tok) { EmitError(p, "FATAL ERROR: Called " __FUNCTION__ " without a " _STRINGIZE(tok) " token.", t); return 0; }

Node* ConsumeID(Program& p, TOKEN*& t)
{
  if(t->token != T_ID)
  {
    EmitError(p, cStrF("ConsumeID() called on non-ID token: %s", ReverseToken(t->token)), t);
    return 0;
  }

  Node* n = CreateNodeID(SYNTAX_VALUE_ID, t->len);
  ++t;
  return n;
}

Node* ConsumeOP(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_OP);

  Node* n = CreateNodeStr(SYNTAX_OP, cStr(t->s, t->len));
  ++t;
  return n;
}

ID ConsumeString(Program& p, TOKEN*& t)
{
  if(t->token != T_STRING && t->token != T_CHARACTER && t->token != T_ID)
  {
    EmitError(p, cStrF("ConsumeString() called on non-string token: %s", ReverseToken(t->token)), t);
    return (ID)-1;
  }
  return (t++)->len;
}

Node* ConsumeNumber(Program& p, TOKEN*& t)
{
  if(t->token != T_NUMBER)
  {
    EmitError(p, cStrF("ConsumeNumber() called on non-number token: %s", ReverseToken(t->token)), t);
    return 0;
  }

  Node* n = CreateNodeStr(SYNTAX_VALUE_NUMBER, cStr(t->s, t->len)); // we can't resolve numbers yet because we don't know what all possible suffixes are.
  ++t;
  return n;
}

bool is_value(Tokens t)
{
  switch(t)
  {
  case T_NUMBER:
  case T_STRING:
  case T_CHARACTER:
  case T_NULL:
  case T_TRUE:
  case T_FALSE:
  case T_ID:
    return true;
  }
  return false;
}

static cTrie<TOKENID> op_trie(20, "!", "$", "+", ",", "->", ".", "...", ":", ";", "=", "?",
  "@", "|", "(", ")", "[", "]", "{", "}");

Tokens conv_op(TOKEN* t)
{
  TOKENID id;
  if(t->token == T_OP && (id = op_trie.Get(t->s, t->len)) != (TOKENID)-1)
    return Tokens(id + T_PIN);
  return t->token;
}

bool check_op(TOKEN* t, Tokens op)
{
  return conv_op(t) == op;
}

Tokens prefix_op(TOKEN* t, size_t& c)
{
  c = 0;
  if(!t->len || t->token != T_OP)
    return t->token;

  if(t->len >= 2 &&
    t->s[0] == '-' &&
    t->s[1] == '>')
  {
    c = t->len - 2;
    return T_LAMBDAEXPR;
  }

  if(t->len >= 3 &&
    t->s[0] == '.' &&
    t->s[1] == '.' &&
    t->s[2] == '.')
  {
    c = t->len - 3;
    return T_ELLIPSES;
  }

  TOKENID id;
  if(t->token == T_OP && (id = op_trie.Get(t->s, 1)) != (TOKENID)-1)
  {
    c = t->len - 1;
    return Tokens(id + T_PIN);
  }
  return t->token;
}

bool extract_op(TOKEN*& t, Tokens op)
{
  if(t->token == T_OP)
  {
    size_t c = t->len;
    if(prefix_op(t, c) != op)
      return false;
    if(c > 0)
    {
      t->s += (t->len - c);
      t->len = c;
      return true;
    }
  }
  else if(t->token != op)
    return false;
  ++t;
  return true;
}

void ExpectExtractOp(Program& p, TOKEN*& t, Tokens target)
{
  if(!extract_op(t, target))
    EmitError(p, cStrF("Expected token %s. Continuing to parse as if it existed.", ReverseToken(target)), t);
}

Node* parse_expr(Program& p, TOKEN*& t);

Node* parse_initlist(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_INITLIST);
  ExpectToken(p, t, T_LBRACE);
  if(t->token == T_ID && t[1].token == T_ASSIGN)
  {
    do
    {
      DiscardToken(t, T_COMMA);
      n->AddNode(ConsumeID(p, t));
      ExpectToken(p, t, T_ASSIGN);
      n->AddNode(parse_expr(p, t));
    } while(t->token == T_COMMA);
  }
  else
  {
    n->s = SYNTAX_INITLISTRAW;
    do
    {
      DiscardToken(t, T_COMMA);
      n->AddNode(parse_expr(p, t));
    } while(t->token == T_COMMA);
  }

  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_invocation(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_INVOKE);
  ExpectToken(p, t, T_LPAREN);
  if(t->token != T_RPAREN)
  {
    do
    {
      DiscardToken(t, T_COMMA);
      n->AddNode(parse_expr(p, t));
    } while(t->token == T_COMMA);
  }
  ExpectToken(p, t, T_RPAREN);
  return n;
}

Node* parse_templatearray(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_TEMPLATEARRAY);
  ExpectToken(p, t, T_LBRACKET);
  switch(conv_op(t))
  {
  case T_RBRACKET: // dynamic array
    ++t;
    return n;
  case T_COLON: // slice
    n->s = SYNTAX_SLICE;
    ++t;
    ExpectToken(p, t, T_RBRACKET);
    return n;
  }

  n->AddNode(parse_expr(p, t));
  if(extract_op(t, T_COLON))
  {
    n->s = SYNTAX_SLICE;
    do
    {
      n->AddNode(parse_expr(p, t));
    } while(!extract_op(t, T_COLON));
  }
  else
  {
    switch(conv_op(t))
    {
    case T_COMMA:
      do
      {
        ExpectToken(p, t, T_COMMA);
        n->AddNode(parse_expr(p, t));
      } while(t->token == T_COMMA);
      break;
    case T_RBRACKET:
      break;
    default:
      EmitError(p, cStrF("Expected ':' ',' or ']', but found %s instead.", ReverseToken(t->token)), t);
      return n;
    }
  }
  ExpectToken(p, t, T_RBRACKET);
  return n;
}

Node* parse_value(Program& p, TOKEN*& t)
{
  Node* n;
  switch(t->token)
  {
  case T_NUMBER:
    return ConsumeNumber(p, t);
  case T_STRING:
    return CreateNodeID(SYNTAX_VALUE_STRING, ConsumeString(p, ++t));
  case T_CHARACTER:
    return CreateNodeID(SYNTAX_VALUE_CHARACTER, ConsumeString(p, ++t));
  case T_NULL:
    return CreateNode(SYNTAX_VALUE_NULL);
  case T_TRUE:
  case T_FALSE:
    n = CreateNode(SYNTAX_VALUE_CONSTANT);
    n->node = Value();
    n->node.get<Value>().type = TY_BOOL;
    n->node.get<Value>().v = (__int64)(t->token == T_TRUE);
  default:
    EmitError(p, cStrF("Expected value, found invalid token %s instead", ReverseToken(t->token)), t);
    return 0;
  case T_ID:
    break;
  }
  
  n = CreateNode(SYNTAX_VALUE);
  n->AddNode(ConsumeID(p, t));
  while(true)
  {
    switch(t->token)
    {
    case T_DOT:
      n->AddNode(ConsumeID(p, t));
      continue;
    case T_LPAREN:
      n->AddNode(parse_invocation(p, t));
      continue;
    case T_LBRACKET:
      n->AddNode(parse_templatearray(p, t));
      continue;
    default:
      break;
    }
    break;
  }
  if(t->token == T_LBRACE)
    n->AddNode(parse_initlist(p, t));
  return n;
}

Node* parse_factor(Program& p, TOKEN*& t)
{
  if(t->token == T_LPAREN)
    return parse_expr(p, t);
  return parse_value(p, t);
}

void parse_termafter(Program& p, TOKEN*& t, Node* n)
{
  if(t->token != T_OP)
  { 
    EmitError(p, "FATAL ERROR: Called parse_termafter without a T_OP token.", t);
    return;
  }

  while(t->token == T_OP)
    n->AddNode(ConsumeOP(p, t));

  if(!is_value(t->token) && t->token != T_LPAREN)
    return;
  n->AddNode(parse_factor(p, t));
  if(t->token == T_OP)
    parse_termafter(p, t, n);
}

Node* parse_lambda(Program& p, TOKEN*& t);

Node* parse_expr(Program& p, TOKEN*& t)
{
  if(t->token == T_FN)
    return parse_lambda(p, t);

  Node* n = CreateNode(SYNTAX_EXPR);

  while(t->token == T_OP)
    n->AddNode(ConsumeOP(p, t));
  n->AddNode(parse_factor(p, t));
  if(t->token == T_OP)
    parse_termafter(p, t, n);
  return n;
}

Node* parse_rawtype(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_TYPE);
  Node* n = CreateNodeID(SYNTAX_TYPEID, t->len);
  ++t;
  return n;
}

bool IsTypeID(Node* n)
{
  return n->s == SYNTAX_TYPE &&
    n->nodes().Length() == 1 &&
    n->nodes()[0]->s == SYNTAX_DOTTYPE &&
    n->nodes()[0]->nodes().Length() == 1 && 
    n->nodes()[0]->nodes()[0]->s == SYNTAX_VALUE_ID;
}

Node* parse_dottype(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_DOTTYPE);

  do
  {
    DiscardToken(t, T_DOT);

    if(t->token == T_TYPE)
      n->AddNode(parse_rawtype(p, t));
    else
      n->AddNode(ConsumeID(p, t));

    while(t->token == T_LBRACKET)
      n->AddNode(parse_templatearray(p, t));
  } while(t->token == T_DOT);

  return n;
}

Node* parse_pretypemod(Program& p, TOKEN*& t)
{
  if(t->token == T_CONST || t->token == T_UNSAFE)
  {
    Node* n = CreateNodeID(SYNTAX_TOKEN, t->token);
    return n;
  }
  return 0;
}
Node* parse_posttypemod(Program& p, TOKEN*& t)
{
  if(t->token == T_CONST)
    return CreateNodeID(SYNTAX_TOKEN, T_CONST);
  if(extract_op(t, T_REF))
    return CreateNodeID(SYNTAX_TOKEN, T_REF);
  if(extract_op(t, T_DEFREF))
    return CreateNodeID(SYNTAX_TOKEN, T_DEFREF);
  if(extract_op(t, T_PIN))
    return CreateNodeID(SYNTAX_TOKEN, T_PIN);
  return 0;
}

Node* parse_dotid(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_DOTID);
  n->AddNode(ConsumeID(p, t));
  while(t->token == T_DOT)
    n->AddNode(ConsumeID(p, ++t));
  return n;
}

Node* parse_type(Program& p, TOKEN*& t);

Node* parse_vartypelambda(Program& p, TOKEN*& t)
{
  ExpectToken(p, t, T_LBRACKET);
  Node* n = CreateNode(SYNTAX_VARTYPELAMBDA);
  if(t->token == T_VAR)
    n->AddNode(CreateNodeID(SYNTAX_TYPEID, TY_VAR));
  else
  {
    n->AddNode(parse_type(p, t));
    while(t->token == T_ALGEBRIAC)
      n->AddNode(parse_type(p, t));
  }

  ExpectToken(p, t, T_RBRACKET);
  return n;
}

Node* parse_type(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_TYPE);
  if(t->token == T_FN)
  {
    n->s = SYNTAX_TYPE_FN;
    ++t;
    if(t->token == T_DOT)
    {
      if(t->token == T_TYPE)
        n->AddNode(parse_rawtype(p, t)); // this is rawtype instead of dottype because of ambiguities with parsing a full type here.
      else if(t->token == T_LPAREN)
      {
        n->AddNode(parse_dottype(p, ++t));
        ExpectToken(p, t, T_RPAREN);
      }
      else if(t->token == T_ID)
        n->AddNode(parse_dotid(p, t));
      else
        EmitError(p, cStrF("Illegal token after T_FN T_DOT: ", t->token), t);
    }
    if(t->token == T_LBRACKET)
      n->AddNode(parse_vartypelambda(p, t));

    ExpectToken(p, t, T_LPAREN);
    n->AddNode(parse_type(p, t));
    while(t->token == T_COMMA)
      n->AddNode(parse_type(p, ++t));

    ExpectToken(p, t, T_RPAREN);
  }
  else
  {
    while(n->AddNode(parse_pretypemod(p, t)));
    n->AddNode(parse_dottype(p, t));
    while(n->AddNode(parse_posttypemod(p, t)));
  }

  return n;
}

Node* parse_vartype(Program& p, TOKEN*& t)
{
  if(t->token == T_VAR)
    return CreateNodeID(SYNTAX_TYPEID, TY_VAR);
  return parse_type(p, t);
}

Node* parse_algebriac_type(Program& p, TOKEN*& t);

void parse_algebriac_inner(Program& p, TOKEN*& t, Node* n)
{
  if(t->token == T_ID && t[1].token == T_LBRACE)
  {
    n->AddNode(ConsumeID(p, t));
    n->AddNode(parse_algebriac_type(p, t));
  }
  else
    n->AddNode(parse_type(p, t));
}

Node* parse_algebriac_type(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_TYPE_ALGEBRIAC);
  ExpectToken(p, t, T_LBRACE);
  if(t->token != T_RBRACE) // an empty algebriac type is legal
  {
    parse_algebriac_inner(p, t, n);
    if(t->token == T_ID)
    {
      n->AddNode(ConsumeID(p, t));
      ExpectToken(p, t, T_SEMICOLON);
      while(t->token != T_RBRACE && t->token != T_EOF)
      {
        parse_algebriac_inner(p, t, n);
        n->AddNode(ConsumeID(p, t));
        ExpectToken(p, t, T_SEMICOLON);
      }
    }
    else if(t->token == T_ALGEBRIAC)
    {
      do
        parse_algebriac_inner(p, ++t, n);
      while(t->token == T_ALGEBRIAC);
    }
    else
      EmitError(p, cStrF("Expected ID or '|' but found %s", ReverseToken(t->token)), t);
  }
  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_typedef(Program& p, TOKEN*& t, Node* n)
{
  CALLFAILURE(T_TYPEDEF);
  n->s = SYNTAX_TYPEDEF;
  n->AddNode(ConsumeID(p, ++t)); // increment token, then eat the ID
  ExpectExtractOp(p, t, T_ASSIGN);
  if(t->token == T_LBRACE)
    return parse_algebriac_type(p, t);

  n->AddNode(parse_type(p, t));
  ExpectToken(p, t, T_SEMICOLON);
  return n;
}

Node* parse_enum(Program& p, TOKEN*& t, Node* n)
{
  CALLFAILURE(T_ENUM);
  n->s = SYNTAX_ENUM;
  n->AddNode(ConsumeID(p, ++t)); // increment token, then eat the ID
  
  if(conv_op(t) == T_COLON)
    n->AddNode(parse_rawtype(p, ++t));

  if(t->token != T_LBRACE) // We don't use ExpectToken here because we increment t below.
    EmitError(p, cStrF("Expected token %i. Continuing to parse as if it existed.", T_LBRACE), t);

  do
  {
    if((++t)->token == T_RBRACE) // Ensure we allow trailing commas
      break;
    Node* s = n->AddNode(CreateNode(SYNTAX_SUBNODE));
    s->AddNode(ConsumeID(p, t));
    if(extract_op(t, T_ASSIGN))
      s->AddNode(parse_expr(p, t));
  } while(t->token == T_COMMA);

  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_decl(Program& p, TOKEN*& t, bool* ispub);

Node* parse_classdecl(Program& p, TOKEN*& t, bool& ispub)
{
  switch(t->token)
  {
  case T_PUBLICBLOCK: ispub = true; ++t; return 0;
  case T_PRIVATEBLOCK: ispub = false; ++t; return 0;
  }
  return parse_decl(p, t, &ispub);
}

Node* parse_class(Program& p, TOKEN*& t, Node* n)
{
  if(t->token != T_TRAIT && t->token != T_CLASS)
  {
    EmitError(p, "FATAL ERROR: Expected trait or class token.", t);
    return 0;
  }
  n->s = (t->token == T_TRAIT) ? SYNTAX_TRAIT : SYNTAX_CLASS;
  ++t;

  n->AddNode(ConsumeID(p, t));
  if(t->token == ':') // eat inheritance list
  {
    Node* s = n->AddNode(CreateNode(SYNTAX_SUBNODE));

    s->AddNode(parse_dottype(p, t));
    while(t->token != T_LBRACE && t->token != T_EOF)
    {
      ExpectToken(p, t, T_COMMA);
      s->AddNode(parse_dottype(p, t));
    }
  }
  ExpectToken(p, t, T_LBRACE);

  bool ispub = true; // Stuff is public by default
  while(parse_classdecl(p, t, ispub));
  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_macro(Program& p, TOKEN*& t)
{
  if(t->token != T_MACRO && t->token != T_ATTRIBUTE)
  {
    EmitError(p, "FATAL ERROR: Expected macro or attribute token.", t);
    return 0;
  }

  EmitError(p, "ERROR: parse_macro() not implemented.", t);
  return 0;
}

Node* parse_attribute(Program& p, TOKEN*& t)
{
  if(t->token != T_LPAREN)
    return 0;
  Node* n = CreateNode(SYNTAX_ATTRIBUTE);
  n->AddNode(ConsumeID(p, t));
  n->AddNode(parse_invocation(p, t));
  return n;
}

bool eat_pubpriv(Program& p, TOKEN*& t, bool* ispub)
{
  switch(t->token)
  {
  case T_PRIVATE:
    ++t;
    return false;
  case T_PUBLIC:
    ++t;
    return true;
  }
  return !ispub || *ispub;
}

Node* parse_template(Program& p, TOKEN*& t)
{
  if(t->token != T_TEMPLATE) return 0;
  ExpectToken(p, ++t, T_LBRACKET);
  Node* n = CreateNode(SYNTAX_TEMPLATE);

  do
  {
    DiscardToken(t, T_COMMA);
    n->AddNode(parse_type(p, t));
    if(extract_op(t, T_COLON))
    {
      n->AddNode(parse_type(p, t));
      while(conv_op(t) == T_TRAITCOMBINE)
        n->AddNode(parse_type(p, ++t));
    }
    if(extract_op(t, T_ASSIGN))
    {
      n->AddNode(CreateNode(SYNTAX_TEMPLATE_PARAM_DEFAULT))->AddNode(parse_type(p, t));
    }
    else if(t->token == T_ID)
    {
      n->AddNode(ConsumeID(p, t));
      if(extract_op(t, T_ASSIGN))
        n->AddNode(CreateNode(SYNTAX_TEMPLATE_PARAM_DEFAULT))->AddNode(parse_expr(p, t));
      else if(extract_op(t, T_COLON))
        n->AddNode(CreateNode(SYNTAX_TEMPLATE_PARAM_SPEC))->AddNode(parse_expr(p, t));
    }
    else if(t->token != T_COMMA)
      EmitError(p, cStrF("Illegal token in template parameter: %s", ReverseToken(t->token)), t);

  } while(t->token == T_COMMA);

  ExpectToken(p, t, T_RBRACKET);
  return n;
}

Node* parse_funcmod(Program& p, TOKEN*& t)
{
  if(t->token == T_STATIC || t->token == T_PURE || t->token == T_VIRTUAL || t->token == T_ABSTRACT)
    return CreateNodeID(SYNTAX_TOKEN, t->token);

  return 0;
}

Node* parse_funcbegin(Program& p, TOKEN*& t, Node* n)
{
  while(n->AddNode(parse_funcmod(p, t)));
  if(t->token == T_LBRACE)
  {
    Node* r = n->AddNode(CreateNode(SYNTAX_ALGEBRIAC));
    do
      r->AddNode(parse_type(p, ++t));
    while(t->token == T_ALGEBRIAC);
  }
  
  n->AddNode(parse_vartype(p, t));
  if(t->token == T_OPDEF)
    n->AddNode(ConsumeOP(p, ++t));
  else
    n->AddNode(ConsumeID(p, t));
  return n;
}

Node* parse_vardecl(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_VARDECL);
  n->AddNode(parse_vartype(p, t));
  n->AddNode(ConsumeID(p, t));
  return n;
}

Node* parse_basicdecl(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_BASICDECL);
  if(!n->AddNode(parse_vartype(p, t)))
    return n;
  // because the vartype can resolve to a single ID, simply not having another ID here is valid grammar. If the
  // vartype IS a type and there ISN'T an ID, this is illegal, but we can't check this until types are resolved.
  if(t->token == T_ID) 
    n->AddNode(ConsumeID(p, t));
  return n;
}

Node* parse_paramdecl(Program& p, TOKEN*& t)
{
  if(t->token == T_UNDERSCORE)
  {
    ++t;
    return CreateNodeID(SYNTAX_TOKEN, T_UNDERSCORE);
  }

  Node* n = parse_basicdecl(p, t);
  if(extract_op(t, T_ASSIGN))
    n->AddNode(parse_expr(p, t));
  return n;
}

Node* parse_block(Program& p, TOKEN*& t);
Node* parse_optstatement(Program& p, TOKEN*& t);

Node* parse_optblock(Program& p, TOKEN*& t)
{
  if(t->token == T_LBRACE)
    return parse_block(p, t);
  return parse_optstatement(p, t);
}

Node* parse_forloop(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_FOR);
  Node* n = CreateNode(SYNTAX_FORLOOP);

  ExpectToken(p, ++t, T_LPAREN);
  Node* first = parse_expr(p, t);
  n->nodes().Add(first); // Add this node even if it's null
  if(first != nullptr)
  {
    switch(t->token)
    {
    case T_RPAREN: // While loop variation
      ExpectToken(p, t, T_RPAREN);
      n->AddNode(parse_optblock(p, t));
      return n;
    case T_IN: // foreach loop variation
      ExpectToken(p, t, T_IN);
      n->AddNode(parse_expr(p, t));
      ExpectToken(p, t, T_RPAREN);
      n->AddNode(parse_optblock(p, t));
      return n;
    }
  } // Otherwise this is a standard for loop
  ExpectToken(p, t, T_SEMICOLON);
  n->nodes().Add(parse_expr(p, t));
  ExpectToken(p, t, T_SEMICOLON);
  n->nodes().Add(parse_expr(p, t));
  ExpectToken(p, t, T_RPAREN);
  n->AddNode(parse_optblock(p, t));
  return n;
}

Node* parse_with(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_WITH);
  Node* n = CreateNode(SYNTAX_WITH);
  ExpectToken(p, ++t, T_LPAREN);
  n->AddNode(parse_expr(p, t));
  ExpectToken(p, t, T_RPAREN);
  n->AddNode(parse_block(p, t));
  return n;
}

Node* parse_loop(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_LOOP);
  Node* n = CreateNode(SYNTAX_LOOP);
  n->AddNode(parse_optblock(p, t));
  if(t->token != T_WHILE)
    return n;
  ExpectToken(p, t, T_WHILE);
  ExpectToken(p, t, T_LPAREN);
  n->AddNode(parse_expr(p, t));
  ExpectToken(p, t, T_RPAREN);
  return n;
}

Node* parse_strictdecl(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_VARDECL);
  n->AddNode(parse_type(p, t));
  n->AddNode(ConsumeID(p, t));
  if(extract_op(t, T_ASSIGN))
    n->AddNode(parse_expr(p, t));
  return n;
}
Node* parse_trycatch(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_TRYCATCH);
  ExpectToken(p, t, T_TRY);
  n->AddNode(parse_block(p, t));
  while(t->token == T_CATCH)
  {
    ExpectToken(p, t, T_LPAREN);
    n->AddNode(parse_strictdecl(p, t));
    ExpectToken(p, t, T_RPAREN);
    n->AddNode(parse_block(p, t));
  }
  if(t->token == T_ELSE)
    n->AddNode(parse_block(p, ++t))->s = SYNTAX_TRYELSE;
  if(t->token == T_FINALLY)
    n->AddNode(parse_block(p, ++t))->s = SYNTAX_TRYFINALLY;
  return n;
}

Node* parse_statement(Program& p, TOKEN*& t)
{
  switch(t->token)
  {
  case T_LBRACE:
    return parse_block(p, t);
  case T_TRY:
    return parse_trycatch(p, t);
  }
  return parse_optstatement(p, t);
}

Node* parse_switch(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_SWITCH);
  Node* n = CreateNode(SYNTAX_SWITCH);
  ExpectToken(p, ++t, T_LPAREN);
  n->AddNode(parse_expr(p, t));
  ExpectToken(p, t, T_RPAREN);
  ExpectToken(p, t, T_LBRACE);
  
  while(t->token != T_RBRACE && t->token != T_EOF)
  {
    ExpectToken(p, t, T_CASE);
    n->AddNode(parse_factor(p, t));
    if(t->token == T_ID)
      n->AddNode(ConsumeID(p, t));
    ExpectExtractOp(p, t, T_COLON);

    while(t->token != T_CASE && t->token != T_RBRACE && t->token != T_EOF)
      n->AddNode(parse_statement(p, t));
  }

  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_if(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_IF);
  Node* n = CreateNode(SYNTAX_IF);
  ExpectToken(p, ++t, T_LPAREN);
  n->AddNode(parse_expr(p, t));
  ExpectToken(p, t, T_RPAREN);
  n->AddNode(parse_optblock(p, t));

  while(t->token == T_ELSE && t[1].token == T_IF)
  {
    ExpectToken(p, ++t, T_IF);
    ExpectToken(p, t, T_LPAREN);
    n->AddNode(parse_expr(p, t));
    ExpectToken(p, t, T_RPAREN);
    n->AddNode(parse_optblock(p, t));
  }

  if(t->token == T_ELSE)
    n->AddNode(parse_optblock(p, ++t));

  return n;
}

Node* parse_lambda(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_FN);
  Node* n = CreateNode(SYNTAX_LAMBDA);
  ++t;
  if(t->token == T_LBRACKET)
    n->AddNode(parse_vartypelambda(p, t));
  
  ExpectToken(p, t, T_LPAREN);
  do
  {
    DiscardToken(t, T_COMMA);
    if(t->token == T_UNDERSCORE)
      n->AddNode(CreateNodeID(SYNTAX_TOKEN, T_UNDERSCORE));
    else
      n->AddNode(parse_basicdecl(p, t));
  } while(t->token == T_COMMA);
  ExpectToken(p, t, T_RPAREN);

  while(n->AddNode(parse_funcmod(p, t)));
  if(conv_op(t) == T_COLON)
  {
    do
    {
      ++t;
      if(conv_op(t) == T_REF)
        n->AddNode(CreateNodeID(SYNTAX_TOKEN, T_REF));
      n->AddNode(ConsumeID(p, t));
    } while(t->token == T_COMMA);
  }

  if(t->token == T_LBRACE)
    n->AddNode(parse_block(p, t));
  else if(extract_op(t, T_LAMBDAEXPR))
    n->AddNode(parse_expr(p, t));
  else
    EmitError(p, cStrF("Expected '{' or '->' but found %s", ReverseToken(t->token)), t);

  return n;
}

Node* parse_assert(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_ASSERT);
  Node* n = CreateNode(SYNTAX_ASSERT);
  ExpectToken(p, ++t, T_LPAREN);
  n->AddNode(parse_expr(p, t));
  ExpectToken(p, t, T_RPAREN);
  DiscardToken(t, T_SEMICOLON);
  return n;
}

Node* parse_assume(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_ASSUME);
  Node* n = CreateNode(SYNTAX_ASSUME);
  ExpectToken(p, ++t, T_LPAREN);
  n->AddNode(parse_expr(p, t));
  ExpectToken(p, t, T_RPAREN);
  DiscardToken(t, T_SEMICOLON);
  return n;
}

Node* parse_optstatement(Program& p, TOKEN*& t)
{
  Node* n;
  switch(t->token)
  {
  case T_FOR:
    return parse_forloop(p, t);
  case T_WITH:
    return parse_with(p, t);
  case T_LOOP:
    return parse_loop(p, t);
  case T_SWITCH:
    return parse_switch(p, t);
  case T_IF:
    return parse_if(p, t);
  case T_STATIC:
    ++t;
    n = CreateNode(SYNTAX_VARDECL);
    n->AddNode(CreateNodeID(SYNTAX_TOKEN, T_STATIC));
    n->AddNode(parse_vartype(p, t));
    n->AddNode(ConsumeID(p, t));
    if(extract_op(t, T_ASSIGN))
      n->AddNode(parse_expr(p, t));
    return n;
  case T_VAR:
  case T_TYPE:
    n = CreateNode(SYNTAX_VARDECL);
    n->AddNode(parse_vartype(p, t));
    n->AddNode(ConsumeID(p, t));
    if(extract_op(t, T_ASSIGN))
      n->AddNode(parse_expr(p, t));
    return n;
  case T_BREAK:
    ++t;
    n = CreateNodeID(SYNTAX_BREAK, 0); // once the number is resolved to an integer the node will be removed and the count put in ID.
    if(t->token != T_SEMICOLON)
      n->AddNode(ConsumeNumber(p, t));
    ExpectToken(p, t, T_SEMICOLON);
    return n;
  case T_CONTINUE:
    ++t;
    n = CreateNodeID(SYNTAX_CONTINUE, 0);
    if(t->token != T_SEMICOLON)
      n->AddNode(ConsumeNumber(p, t));
    ExpectToken(p, t, T_SEMICOLON);
    return n;
  case T_RETURN:
    ++t;
    n = CreateNode(SYNTAX_RETURN);
    if(t->token != T_SEMICOLON)
      n->AddNode(parse_expr(p, t));
    ExpectToken(p, t, T_SEMICOLON);
    return n;
  case T_ASSERT:
    return parse_assert(p, t);
  case T_ASSUME:
    return parse_assume(p, t);
  case T_SEMICOLON:
    ++t;
    return 0;
  case T_FN:
    n = parse_lambda(p, t);
    ExpectToken(p, t, T_SEMICOLON);
    return n;
  }

  n = CreateNode(SYNTAX_EXPR);
  while(t->token == T_OP)
    n->AddNode(ConsumeOP(p, t));
  n->AddNode(parse_factor(p, t));
  if(t->token == T_ID)
  {
    n->s = SYNTAX_VARDECL;
    n->AddNode(ConsumeID(p, t));
    if(extract_op(t, T_ASSIGN))
      n->AddNode(parse_expr(p, t));
  }
  else if(t->token == T_OP)
  {
    while(t->token == T_OP)
      n->AddNode(ConsumeOP(p, t));
    if(t->token != T_SEMICOLON)
    {
      n->AddNode(parse_factor(p, t));
      if(t->token == T_OP)
        parse_termafter(p, t, n);
    }
  }

  ExpectToken(p, t, T_SEMICOLON);
  return n;
}

Node* parse_block(Program& p, TOKEN*& t)
{
  Node* n = CreateNode(SYNTAX_BLOCK);

  ExpectToken(p, t, T_LBRACE);
  while(t->token != T_EOF && t->token != T_RBRACE)
    n->AddNode(parse_statement(p, t));
  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_decl(Program& p, TOKEN*& t, bool* ispub)
{
  Node* n = CreateNode(NUM_SYNTAX);
  while(n->AddNode(parse_attribute(p, t)));
  bool pub = eat_pubpriv(p, t, ispub);
  n->AddNode(parse_template(p, t));
  
  switch(t->token)
  {
  case T_TRAIT:
  case T_CLASS:
    return parse_class(p, t, n);
  case T_ENUM:
    return parse_enum(p, t, n);
  case T_TYPEDEF:
    return parse_typedef(p, t, n);
  default:
    parse_funcbegin(p, t, n);
    switch(conv_op(t))
    {
    case T_ASSIGN:
      n->s = SYNTAX_VARDECL;
      n->AddNode(parse_expr(p, ++t));
      ExpectToken(p, t, T_SEMICOLON);
      break;
    case T_LPAREN:
      n->s = SYNTAX_FUNCTION;
      ++t;
      if(t->token != T_RPAREN)
      {
        n->AddNode(parse_paramdecl(p, t));
        while(t->token == T_COMMA)
          n->AddNode(parse_paramdecl(p, ++t));
      }
      ExpectToken(p, t, T_RPAREN);
      if(t->token == T_SEMICOLON)
        break;
      n->AddNode(parse_block(p, t));
      break;
    case T_SEMICOLON:
      n->s = SYNTAX_VARDECL;
      ++t;
      break;
    default:
      EmitError(p, "Syntax error <insert useful details here>", t);
      break;
    }
  }

  return n;
}
Node* parse_using(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_USING);
  Node* n = CreateNode(SYNTAX_USING);
  n->AddNode(parse_dotid(p, ++t));
  DiscardToken(t, T_SEMICOLON);
  return n;
}

Node* parse_import(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_IMPORT);
  Node* n = CreateNodeID(SYNTAX_IMPORT, ConsumeString(p, ++t));
  DiscardToken(t, T_SEMICOLON);
  return n;
}

Node* parse_impl(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_IMPL);
  Node* n = CreateNode(SYNTAX_IMPL);
  n->AddNode(parse_dottype(p, t));
  if(extract_op(t, T_COLON))
  {
    ExpectExtractOp(p, t, T_COLON);
    n->AddNode(CreateNode(SYNTAX_SUBNODE))->AddNode(parse_dottype(p, t));
  }
  if(t->token == T_SEMICOLON)
  {
    ++t;
    return n;
  }
  ExpectToken(p, t, T_LBRACE);
  bool ispub = true; // Stuff is public by default
  while(parse_classdecl(p, t, ispub));
  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_chunk(Program& p, TOKEN*& t);

Node* parse_namespace(Program& p, TOKEN*& t)
{
  CALLFAILURE(T_NAMESPACE);
  Node* n = CreateNode(SYNTAX_NAMESPACE);
  n->AddNode(parse_dotid(p, ++t));
  ExpectToken(p, t, T_LBRACE);
  while(t->token != T_EOF && t->token != T_RBRACE)
    n->AddNode(parse_chunk(p, t));
  ExpectToken(p, t, T_RBRACE);
  return n;
}

Node* parse_chunk(Program& p, TOKEN*& t)
{
  switch(t->token)
  {
  case T_NAMESPACE:
    return parse_namespace(p, t);
  case T_USING:
    return parse_using(p, t);
  case T_ASSUME:
    return parse_assume(p, t);
  case T_IMPORT:
    return parse_import(p, t);
  case T_IMPL:
    return parse_impl(p, t);
  case T_ATTRIBUTE:
  case T_MACRO:
    return parse_macro(p, t);
  default: // If it isn't any of those, attempt to parse it as a decl
    return parse_decl(p, t, 0);
  }
}

void BuildAST(Program& p)
{
  p.root = CreateNode(SYNTAX_ROOT);
  TOKEN* end = p.tokens.end();
  TOKEN* cur = p.tokens.begin();
  Node* file;

  while(cur != end)
  {
    file = CreateNode(SYNTAX_FILE);
    p.root->AddNode(file);

    while(cur != end && cur->token != T_EOF)
      file->AddNode(parse_chunk(p, cur));
    ++cur; //eat EOF token
  }
}

void TraverseAST(Program& p, Node* n, void(*f)(Program&, Node*))
{
  if(!n) return;
  f(p, n);

  if(n->node.is<Node::NODES>())
  {
    for(auto& t : n->nodes())
      TraverseAST(p, t, f);
  }
}

void TraverseAST(Program& p, void(*f)(Program&, Node*))
{
  TraverseAST(p, p.root, f);
}



void DumpASTNode(Program& p, Node* n, std::ostream& out, int level)
{
  static const char* reverse[] = { "ROOT","FILE","USING","NAMESPACE","ALGEBRIAC","ATTRIBUTE","IMPL","ASSERT","ASSUME",
    "TRAIT","CLASS","ENUM","FUNCTION","INVOKE","OP","DOTTYPE",  "BASICDECL","VARDECL","BLOCK","FORLOOP","WITH","LOOP",
    "SWITCH","IF","RETURN","BREAK","CONTINUE","TRYCATCH","TRYELSE","TRYFINALLY","TEMPLATE","TEMPLATE_PARAM_DEFAULT",
    "TEMPLATE_PARAM_SPEC","TYPE", "TYPE_FN","TYPE_ALGEBRIAC","TYPEID", "TYPEDEF", "VARTYPELAMBDA","LAMBDA","EXPR",
    "TEMPLATEARRAY","SLICE","INITLISTRAW","INITLIST","DOTID", "IMPORT","TOKEN", "VALUE", "VALUE_ID", "VALUE_NUMBER",
    "VALUE_CONSTANT", "VALUE_STRING","VALUE_CHARACTER","VALUE_NULL","VALUE_TYPE", "SUBNODE"
  };
  static_assert(sizeof(reverse) / sizeof(const char*) == NUM_SYNTAX, "ERROR: reverse does not cover all of SYNTAX!");

  for(int i = 0; i < level * 2; ++i) out.put(' ');
  out << '<' << reverse[n->s];
  if(n->node.is<Node::NODES>())
  {
    out << '>' << std::endl;
    for(auto& k : n->node.get<Node::NODES>())
      DumpASTNode(p, k, out, level + 1);
    for(int i = 0; i < level * 2; ++i) out.put(' ');
    out << "</" << reverse[n->s] << '>' << std::endl;
  }
  else if(n->node.is<cStr>())
    out << '>' << n->node.get<cStr>() << "</" << reverse[n->s] << '>' << std::endl;
  else if(n->node.is<ID>())
    out << '>' << n->node.get<ID>() << "</" << reverse[n->s] << '>' << std::endl;
  else if(n->node.is<Value>())
    out << ">Value</" << reverse[n->s] << '>' << std::endl;
  else
    out << ">ERROR</" << reverse[n->s] << '>' << std::endl;

}
void DumpAST(Program& p, std::ostream& out)
{
  DumpASTNode(p, p.root, out, 0);
}
