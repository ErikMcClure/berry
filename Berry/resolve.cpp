// Copyright ©2015 Black Sphere Studios

#include "ast.h"
#include <iostream>
#include "bss-util/cTrie.h"

using namespace bss_util;

int OperatorPriority(const char* op)
{
  static cTrie<TOKENID> op_trie(51, "++", "--", "(", "[", "**", "!", "~", "#", "*", "/", "%", "%%", "+", "-", "<<",
    "<<<", ">>", ">>>", "<|", "|>", "==", "!=", "<", ">", "<=", ">=", "&", "^", "|", "&&", "||", "<:", ":>", "=",
    "+=", "-=" "*=", "/=", "<<=", ">>=", "<<<=", ">>>=", "<|=", "|>=", "%=", "%%=", "^=", "&=", "**=", "|=", "->");

  switch(op_trie[op])
  {
  case 0: // ++
  case 1: // --
  case 2: // (
  case 3: // [
    return 20;
  case 4: // **
    return 19;
  case 5: // !
  case 6: // ~
  case 7: // #
    return 18;
  case 8: // *
  case 9: // /
  case 10: // %
  case 11: // %%
    return 17;
  case 12: // +
  case 13: // -
    return 16;
  case 14: // <<
  case 15: // <<<
  case 16: // >>
  case 17: // >>>
  case 18: // <|
  case 19: // |>
    return 15;
  case 20: // ==
  case 21: // !=
  case 22: // <
  case 23: // >
  case 24: // <=
  case 25: // >=
    return 14;
  case 26: // &
    return 13;
  case 27: // ^
    return 12;
  case 28: // |
    return 11;
  case 29: // &&
    return 10;
  case 30: // ||
    return 9;
  case 31: // <:
  case 32: // :>
    return 8;
  case 33: // =
  case 34: // +=
  case 35: // -=
  case 36: // *=
  case 37: // /=
  case 38: // <<=
  case 39: // >>=
  case 40: // <<<=
  case 41: // >>>=
  case 42: // <|=
  case 43: // |>=
  case 44: // %=
  case 45: // %%=
  case 46: // ^=
  case 47: // &=
  case 48: // **=
  case 49: // |=
    return 6;
  case 50: // ->
    return 5;
  default: // user-defined operator precedence
    return 7;
  }
}
char TypeRef::Comp(const TypeRef& l, const TypeRef& r)
{ // Two types are the same only if they are functionally identical.
  char ret = SGNCOMPARE(l.type, r.type);
  if(!ret) ret = SGNCOMPARE(l.mods&TYPEREFMOD_COMPARISON, r.mods&TYPEREFMOD_COMPARISON);
  if(!ret) ret = SGNCOMPARE(l.indirection, r.indirection);
  if(!ret) ret = SGNCOMPARE(l.params.Length(), r.params.Length());
  if(!ret) ret = SGNCOMPARE(l.dim.Length(), r.dim.Length());
  //for(size_t i = 0; i < l.dim.Length() && !ret; ++i)
  //  ret = SGNCOMPARE(l.dim[i], r.dim[i]);
  for(size_t i = 0; i < l.params.Length() && !ret; ++i)
    ret = Value::Comp(l.params[i], r.params[i]);

  return ret;
}

void ResolveError(Program& p, const char* s)
{
  p.errors.Add(s);
  std::cout << s << std::endl;
}

Node* getfirstsyntax(Node* n, SYNTAX_PART s)
{
  assert(n->node.is<Node::NODES>());
  for(auto& t : n->nodes())
    if(t->s == s)
      return t;
  return 0;
}

Node* r_invpicknode(Program& p, Node* n, Node**& nodes, SYNTAX_PART reject, const char* error)
{
  if(n->node.is<Node::NODES>() && n->nodes().Length() > 0 && nodes < n->nodes().end() && nodes[0]->s != reject)
    return *(nodes++);
  else if(error != 0)
    ResolveError(p, error);
  return 0;
}

Node* r_picknode(Program& p, Node* n, Node**& nodes, SYNTAX_PART match, const char* error)
{
  if(!nodes && n->node.is<Node::NODES>())
    nodes = n->nodes().begin();
  if(n->node.is<Node::NODES>() && n->nodes().Length() > 0 && nodes < n->nodes().end() && nodes[0]->s == match)
    return *(nodes++);
  else if(error != 0)
    ResolveError(p, error);
  return 0;
}

TypeID r_resolveid(Program& p, ID id, TypeID context)
{
  auto ty = p.IDs.GetNear(TypeTuple { context, id, 0 }, false);
  if(ty && ty->value.name == id && ty->value.parent == context)
  {
    if(ty->next != 0 && ty->next->value.name == id && ty->next->value.parent == context)
      ResolveError(p, "DOTID element is ambiguous");
    else
      context = ty->value.type;
  }
  return context;
}

void r_gathertypes(Program& p, Node* n, TypeID context)
{
  if(!n) return;

  RawTypes t = TY_NUMTYPES;
  switch(n->s)
  {
  case SYNTAX_TRAIT: t = TY_TRAIT; break;
  case SYNTAX_CLASS:
  case SYNTAX_ENUM: t = TY_ENUM; break;
  case SYNTAX_FUNCTION: t = TY_FUNC; break;
  case SYNTAX_TYPEDEF: t = TY_COMPLEX; break;
  case SYNTAX_NAMESPACE:
  {
    Node* id = getfirstsyntax(n, SYNTAX_DOTID);
    Node** pnodes = 0;
    Node* cur = r_picknode(p, id, pnodes, SYNTAX_VALUE_ID, 0);
    Node* next;
    while(next = r_picknode(p, id, pnodes, SYNTAX_VALUE_ID, 0))
    {
      TypeID ncontext = r_resolveid(p, cur->node.get<ID>(), context);
      if(ncontext == context) // If the context wasn't updated this namespace doesn't exist yet.
      {
        TypeTuple key = { context, cur->node.get<ID>(), 0 };
        context = p.types.AddConstruct(key.name, context);
        p.types[context].id = context;
        key.type = context;
        p.IDs.Insert(key);
      }
      else
        context = ncontext;
      cur = next;
    }
    if(cur != 0)
    {
      id->s = SYNTAX_VALUE_ID;
      id->node = cur->node.get<ID>();
    }
    t = TY_NAMESPACE;
  }
    break;
  }

  if(t != TY_NUMTYPES)
  {
    Node* id = getfirstsyntax(n, SYNTAX_VALUE_ID);
    if(id)
    {
      TypeTuple key = { context, id->node.get<ID>(), 0 };
      context = p.types.AddConstruct(key.name, context);
      p.types[context].id = context;
      p.types[context].node = n;
      key.type = context;
      p.IDs.Insert(key);
      id->s = SYNTAX_TYPEID;
      id->node = (ID)context;
      n->t = context;
    }
    else
      ResolveError(p, "No ID could be found.");
  }

  if(n->node.is<Node::NODES>())
  {
    for(auto& t : n->nodes())
      r_gathertypes(p, t, context);
  }
}

TypeID Program::GetParent(TypeID child)
{
  return types[child].scope;
}

TypeID r_resolvedotid(Program& p, Node* n, TypeID context)
{
  if(n->s == SYNTAX_DOTID && n->node.is<Node::NODES>())
  {
    TypeID old = context;
    // We have to find all possible matches for this type. If there are multiple possible matches, it's ambiguous.
    for(auto& t : n->nodes())
    {
      if(t->s == SYNTAX_VALUE_ID)
      {
        TypeID cur = context;
        for(;;) // go through our current context and all it's parent contexts
        {
          TypeID id = r_resolveid(p, t->node.get<ID>(), cur);
          if(id != cur)
          {
            if(context == old)
              context = id;
            else
              ResolveError(p, "ID in DOTID is ambiguous.");
            break;
          }
          if(!cur)
            break;
          cur = p.GetParent(cur);
        }
        while(n != 0 && n->s != SYNTAX_FILE) n = n->parent; // Find our file node

        // Go through all our usings
      }
      else
        ResolveError(p, "ID node wasn't SYNTAX_DOTID or SYNTAX_TYPEID");
    }

    if(old != context) // If we can properly resolve this to a TypeID, change this node to a typeID node.
    {
      n->s = SYNTAX_TYPEID;
      n->node = (ID)context;
    }
  }
  else if(n->s == SYNTAX_TYPEID)
    return n->node.get<ID>();
  else
    ResolveError(p, "ID node wasn't SYNTAX_DOTID or SYNTAX_TYPEID");
}

void r_resolveusings(Program& p, Node* n)
{
  Node** pnodes = 0;
  Node* usings = r_picknode(p, n, pnodes, SYNTAX_SUBNODE, "File had no subnode for usings");
  if(usings)
  {
    for(auto& t : usings->nodes())
    {
      if(t->s == SYNTAX_USING && t->node.is<Node::NODES>())
      {
        TypeID context = 0;
        Node* dot = getfirstsyntax(t, SYNTAX_DOTID);
        for(auto& t : dot->nodes())
        {
          if(t->s == SYNTAX_VALUE_ID)
          {
            TypeID ncontext = r_resolveid(p, t->node.get<ID>(), context);
            if(ncontext == context)
            {
              ResolveError(p, "Failed to find ID in using statement");
              break;
            }
            context = ncontext;
          }
          else
            ResolveError(p, "ID node wasn't SYNTAX_DOTID or SYNTAX_TYPEID");
        }
        if(context != 0)
          t->t = context;
      }
    }
  }
}

void GatherTypes(Program& p)
{
  r_gathertypes(p, p.root, 0); // First we find all the types

  if(p.root->node.is<Node::NODES>()) // Then we resolve all the using statements
  {
    for(auto& n : p.root->nodes())
      r_resolveusings(p, n);
  }
}

TypeID r_resolvescope(Program& p, Node* n, Node**& nodes, TypeID context)
{
  if(nodes != 0 && n->node.is<Node::NODES>() && n->nodes().Length() > 0 && nodes < n->nodes().end())
  {
    context = r_resolvedotid(p, nodes[0], context);
    ++nodes;
  }
  else
    ResolveError(p, "scope node has no nodes!");

  return context;
}

void ResolveTypes(Program& p)
{
  // r_resolvetypes(p, p.root, 0); // Only resolves the types, does not evaluate dependent type constraints
}

Monotype Program::AddTypeRef(const TypeRef& r)
{
  Monotype* id = typeregistry.GetRef(r);
  if(!id)
  {
    auto p = typeregistry.Insert(r, ntyperegistry);
    typeregistryhash.Insert(ntyperegistry, &p->_key.first);
    return ntyperegistry++;
  }
  return *id;
}

void r_resolvenode(Program& p, Node* n, TypeID context);

void r_resolvedefault(Program& p, Node* n, TypeID context)
{
  if(n->node.is<Node::NODES>())
  {
    for(auto& t : n->nodes())
      r_resolvenode(p, t, context);
  }
}

Node* r_getinner(Node* n, SYNTAX_PART s)
{
  if(n->s == s && n->node.is<Node::NODES>() && n->nodes().Length() > 0)
    return n->nodes()[0];
  return n;
}

Monotype r_getTypeRef(Program& p, Node* n)
{
  TypeRef r = { 0 };

  if(n->s == SYNTAX_TYPEID) // This lets us set the context to the resulting ID
    r.type = n->node.get<ID>();
  else if(n->s == SYNTAX_VALUE_TYPE && n->node.get<Value>().v.is<Monotype*>())
    return n->node.get<Value>().type;
  else // Try to resolve things anyway in an attempt to minimize cascading errors
    ResolveError(p, "identifier did not resolve to TypeID or a TypeRef");
  return p.AddTypeRef(r);
}

void r_resolverest(Program& p, Node* n, Node**& nodes, TypeID context)
{
  if(nodes != 0 && n->node.is<Node::NODES>() && n->nodes().Length() > 0)
  {
    while(nodes < n->nodes().end())
    {
      r_resolvenode(p, *nodes, context);
      ++nodes;
    }
  }
}

#define CHECKCYCLE(c, x) if(p.types[(c)].stage == (x)) { ResolveError(p, "dependency cycle!"); }

void r_resolvetemplate(Program& p, Node* n, TypeID context)
{
  if(!n || !n->node.is<Node::NODES>()) return;

  r_resolvenode(p, n, context);
  if(n->nodes().Length() > 0)
  {
    Node** ptnodes = n->nodes().begin();
    while(ptnodes < n->nodes().end())
    {
      Node* typeref = r_picknode(p, n, ptnodes, SYNTAX_VALUE_TYPE, "Invalid type expression in template");
      Node* id = r_picknode(p, n, ptnodes, SYNTAX_VALUE_ID, 0);
      Node* typespec = r_picknode(p, n, ptnodes, SYNTAX_TEMPLATE_PARAM_SPEC, 0);
      Node* typedefault = r_picknode(p, n, ptnodes, SYNTAX_TEMPLATE_PARAM_DEFAULT, 0);

      if(!typeref)
      {
        ++ptnodes;
        continue;
      }
      TemplateArg arg = { typeref->node.get<Value>().type };
      if(id != 0)
        arg.id = id->node.get<ID>();
      if(typespec != 0)
        arg.v = typespec->node.get<Value>();
      if(typedefault != 0)
        arg.d = typedefault->node.get<Value>();
      p.types[context].templateargs.Add(arg);
    }
  }
}

TypeID r_resolveprototype(Program& p, Node* n, Node**& pnodes, TypeID context)
{
  Node* hold;
  Node* ptemplate;

  switch(n->s)
  {
  case SYNTAX_IMPL:
    ptemplate = r_picknode(p, n, pnodes, SYNTAX_TEMPLATE, 0);
    context = r_resolvescope(p, n, pnodes, context);
    if(hold != 0)
    {
      p.types[context].stage = Type::RESOLVE_PARTIAL_TYPE;
      context = hold->node.get<ID>();
      hold = r_picknode(p, n, pnodes, SYNTAX_SUBNODE, 0);
      if(hold != 0 && hold->nodes().Length() == 1)
        p.types[context].traits.Insert(r_getTypeRef(p, hold->nodes()[0]));
      p.types[context].stage = Type::RESOLVE_TYPE;
    }
    p.types[context].stage = Type::RESOLVE_PARTIAL_BODY;
    r_resolverest(p, n, pnodes, context);
    p.types[context].stage = Type::RESOLVE_BODY;
    break;
  case SYNTAX_TRAIT:
  case SYNTAX_CLASS:
  {
    ptemplate = r_picknode(p, n, pnodes, SYNTAX_TEMPLATE, 0);
    context = r_resolvescope(p, n, pnodes, context);
    auto& type = p.types[context];
    CHECKCYCLE(context, Type::RESOLVE_PARTIAL_TYPE);
    if(p.types[context].stage < Type::RESOLVE_TYPE)
    {
      r_resolvetemplate(p, ptemplate, context);
      p.types[context].stage = Type::RESOLVE_TYPE;

      hold = r_picknode(p, n, pnodes, SYNTAX_SUBNODE, 0);
      if(hold != 0)
      {
        r_resolvenode(p, hold, context);
        for(auto& k : hold->nodes())
        {
          Node** pinherit = 0;
          Node* inherit = r_picknode(p, k, pinherit, SYNTAX_VALUE_TYPE, "Inherited type did not resolve to a TypeRef");
          if(inherit != 0)
          {
            auto& t = inherit->node.get<Value>().type;
            TypeRef* ty = p.typeregistryhash[t];
            if(ty->type == TY_TRAIT)
              type.traits.Add(t);
            else if(ty->type == TY_COMPLEX && n->s == SYNTAX_CLASS)
              type.subtypes.Add(t);
            else
              ResolveError(p, "Inherited type was not TY_TRAIT or TY_COMPLEX");
          }
        }
      }
    }
  }
  break;
  /*case SYNTAX_ENUM:
  context = r_resolvescope(p, n, pnodes, usings, lastusing, context, true);
  if(p.types[context].type == TY_ENUM)
  {
  auto& t = p.types[context];
  if(t.stage != Type::RESOLVE_BODY)
  {
  Monotype enumtype = TY_INT;
  hold = r_invpicknode(p, n, pnodes, SYNTAX_SUBNODE, 0);
  if(hold != 0)
  {
  if(hold->s == SYNTAX_TYPEID) // This lets us set the context to the resulting ID
  enumtype = n->node.get<ID>();
  else
  ResolveError(p, "Enum must inherit from a primitive type.");

  t.subtypes.Add(r_getTypeRef(p, hold));
  }

  Value last = { enumtype };
  while(pnodes < n->nodes().end())
  {
  hold = r_picknode(p, n, pnodes, SYNTAX_SUBNODE, "Invalid enum node");
  if(hold != 0)
  {
  Node** pinner = 0;
  Node* inner = r_picknode(p, hold, pinner, SYNTAX_VALUE_ID, "Enum ID did not resolve to identifier");
  if(inner != 0)
  {
  Node* expr = r_invpicknode(p, hold, pinner, NUM_SYNTAX, 0);
  if(expr != 0)
  {
  if(expr->node.is<Value>())
  t.templateargs.Add(TemplateArg { enumtype, inner->node.get<ID>(), last = expr->node.get<Value>() });
  else
  ResolveError(p, "Enum member assigned to expression that does not evaluate to a value.");
  }
  else
  {
  if(last.v.is<int64_t>())
  last.v = last.v.get<int64_t>() + 1;
  t.templateargs.Add(TemplateArg { enumtype, inner->node.get<ID>(), last });
  }
  }
  }
  else
  ++pnodes;
  }
  }
  t.stage = Type::RESOLVE_BODY;
  }
  else
  ResolveError(p, "Enum type isn't set to TY_ENUM!");
  break;
  case SYNTAX_FUNCTION:
  {
  Node* ptemplate = r_picknode(p, n, pnodes, SYNTAX_TEMPLATE, 0);
  Node* retval = r_picknode(p, n, pnodes, SYNTAX_TYPE, "Function has no return type");
  context = r_resolvescope(p, n, pnodes, context, fullresolve);
  auto& type = p.types[context];
  CHECKCYCLE(context, Type::RESOLVE_PARTIAL_TYPE);
  if(p.types[context].stage < Type::RESOLVE_TYPE)
  {
  r_resolvetemplate(p, ptemplate, context, fullresolve);
  if(retval != 0)
  {
  r_resolvenode(p, retval, context, true);
  type.returntype = r_getTypeRef(p, retval);
  }

  while(hold = r_picknode(p, n, pnodes, SYNTAX_BASICDECL, 0))
  {
  r_resolvenode(p, hold, context, true);
  Node** phold = 0;
  Node* thold = r_picknode(p, hold, phold, SYNTAX_VALUE_TYPE, "Parameter has no type.");
  Node* tid = r_picknode(p, hold, phold, SYNTAX_VALUE_ID, 0);
  if(thold != 0)
  {
  type.subtypes.Add(r_getTypeRef(p, thold));
  type.typenames.Add(!tid ? 0 : tid->node.get<ID>());
  }
  }
  p.types[context].stage = Type::RESOLVE_TYPE;
  }

  if(fullresolve)
  {
  CHECKCYCLE(context, Type::RESOLVE_PARTIAL_BODY);
  if(p.types[context].stage != Type::RESOLVE_BODY)
  {
  p.types[context].stage = Type::RESOLVE_PARTIAL_BODY;
  r_resolverest(p, n, pnodes,  context, true);
  p.types[context].stage = Type::RESOLVE_BODY;
  }
  }
  }
  break;
  case SYNTAX_INVOKE:
  r_resolverest(p, n, pnodes, context, true);
  pnodes = 0;

  break;
  case SYNTAX_OP:
  break;
  case SYNTAX_DOTTYPE:
  break;
  case SYNTAX_TYPEID:
  if(n->node.get<ID>() == TY_INT)
  {
  switch(p.architecture)
  {
  case Program::ARCH_X64: n->node = (ID)TY_I64;
  case Program::ARCH_X86: n->node = (ID)TY_I32;
  }
  }
  else if(n->node.get<ID>() == TY_UINT)
  {
  switch(p.architecture)
  {
  case Program::ARCH_X64: n->node = (ID)TY_U64;
  case Program::ARCH_X86: n->node = (ID)TY_U32;
  }
  }
  case SYNTAX_FILE:
  case SYNTAX_ATTRIBUTE:
  case SYNTAX_ALGEBRIAC:
  case SYNTAX_ASSERT:
  case SYNTAX_ASSUME:
  case SYNTAX_SUBNODE:
  default:
  r_resolvedefault(p, n, context);
  break;*/
  }
}

void r_resolvenode(Program& p, Node* n, TypeID context)
{
  Node* hold;
  Node** pnodes = 0;

  switch(n->s)
  {
  case SYNTAX_NAMESPACE:
    context = r_resolvescope(p, n, pnodes, context);
    r_resolverest(p, n, pnodes, context);
    break;
  case SYNTAX_TRAIT:
  case SYNTAX_CLASS:
  case SYNTAX_IMPL:
    context = r_resolveprototype(p, n, pnodes, context);
    CHECKCYCLE(context, Type::RESOLVE_PARTIAL_BODY);
    if(p.types[context].stage < Type::RESOLVE_PARTIAL_BODY)
    {
      p.types[context].stage = Type::RESOLVE_PARTIAL_BODY;
      while(pnodes < n->nodes().end())
      {
        if(pnodes[0]->s == SYNTAX_VARDECL)
        {

        }
        else if(pnodes[0]->s == SYNTAX_FUNCTION)
        {
          Node** temp;
          r_resolveprototype(p, pnodes[0], temp, context);
        }
      }
      p.types[context].stage = Type::RESOLVE_BODY;
    }
    break;
  case SYNTAX_ENUM:
    context = r_resolveprototype(p, n, pnodes, context);
    if(p.types[context].type == TY_ENUM)
    {
      auto& t = p.types[context];
      CHECKCYCLE(context, Type::RESOLVE_PARTIAL_BODY);
      if(t.stage < Type::RESOLVE_BODY)
      {
        t.stage = Type::RESOLVE_PARTIAL_BODY;
        Monotype enumtype = 0;
        Value last = { enumtype };
        while(pnodes < n->nodes().end())
        {
          hold = r_picknode(p, n, pnodes, SYNTAX_SUBNODE, "Invalid enum node");
          if(hold != 0)
          {
            Node** pinner = 0;
            Node* inner = r_picknode(p, hold, pinner, SYNTAX_VALUE_ID, "Enum ID did not resolve to identifier");
            if(inner != 0)
            {
              Node* expr = r_invpicknode(p, hold, pinner, NUM_SYNTAX, 0);
              if(expr != 0)
              {
                if(expr->node.is<Value>())
                  t.templateargs.Add(TemplateArg { enumtype, inner->node.get<ID>(), last = expr->node.get<Value>() });
                else
                  ResolveError(p, "Enum member assigned to expression that does not evaluate to a value.");
              }
              else
              {
                if(last.v.is<int64_t>())
                  last.v = last.v.get<int64_t>() + 1;
                t.templateargs.Add(TemplateArg { enumtype, inner->node.get<ID>(), last });
              }
            }
          }
          else
            ++pnodes;
        }
        t.stage = Type::RESOLVE_BODY;
      }
    }
    else
      ResolveError(p, "Enum type isn't set to TY_ENUM!");
    break;
  case SYNTAX_FUNCTION:
    context = r_resolveprototype(p, n, pnodes, context);
    
    CHECKCYCLE(context, Type::RESOLVE_PARTIAL_BODY);
    if(p.types[context].stage < Type::RESOLVE_BODY)
    {
      p.types[context].stage = Type::RESOLVE_PARTIAL_BODY;
      r_resolverest(p, n, pnodes, context);
      p.types[context].stage = Type::RESOLVE_BODY;
    }
  break;
  case SYNTAX_INVOKE:
    r_resolverest(p, n, pnodes, context);
    pnodes = 0;

    break;
  case SYNTAX_OP:
    break;
  case SYNTAX_DOTTYPE:
    break;
  case SYNTAX_TYPEID:
    if(n->node.get<ID>() == TY_INT)
    {
      switch(p.architecture)
      {
      case Program::ARCH_X64: n->node = (ID)TY_I64;
      case Program::ARCH_X86: n->node = (ID)TY_I32;
      }
    }
    else if(n->node.get<ID>() == TY_UINT)
    {
      switch(p.architecture)
      {
      case Program::ARCH_X64: n->node = (ID)TY_U64;
      case Program::ARCH_X86: n->node = (ID)TY_U32;
      }
    }
  case SYNTAX_FILE:
  case SYNTAX_ATTRIBUTE:
  case SYNTAX_ALGEBRIAC:
  case SYNTAX_ASSERT:
  case SYNTAX_ASSUME:
  case SYNTAX_SUBNODE:
  default:
    r_resolvedefault(p, n, context);
    break;
  }
}

void Resolve(Program& p)
{
  r_resolvenode(p, p.root, 0);
  
  // Ensure all types have been fully resolved
  for(auto& x : p.types)
  {
    //if(x.node != 0)
    //  r_resolvenode(p, x.node, 0) // Context is needed here
  }
}

TypeID InferType()
{

}

TypeID InferFunction()
{
  // Given this function name, find all functions that match the argument count, including any variadic ones.

  // Go through the initial typeID of each argument to find all possible potential matches for that argument

  // Sort each argument matching list, then find the intersection between all n arguments

  // Go through the resulting list and do a strict matching of the types, recursively through all template arguments. If a polytype matches, add the argument's type to a list of types the polytype must match simultaneously.

  // For each polytype, try to find an implicit type mapping for each of the types it needs to represent to try and generalize all of the types to a single monotype. If this isn't possible, reject it as a possibility.

  // Finally, each polytype is evaluated against the type constraints and rejected if they don't match.

  // Sort remaining function possibilities by type distance and pick the function with the smallest type distance. If there are multiple functions with the same smallest type distance, it is ambiguous.
}