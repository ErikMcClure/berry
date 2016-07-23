// Copyright ©2015 Black Sphere Studios

#include "ast.h"
#include <iostream>

void ResolveError(Program& p, const char* s)
{
  p.errors.Add(s);
  std::cout << s << std::endl;
}

ID getfirstID(Node* n)
{
  assert(n->node.is<Node::NODES>());
  for(auto& t : n->nodes())
    if(t->s == SYNTAX_VALUE_ID)
      return t->node.get<ID>();
  return 0;
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
  case SYNTAX_NAMESPACE: t = TY_NAMESPACE; break;
  }

  if(t != TY_NUMTYPES)
  {
    ID id = getfirstID(n);
    TypeTuple key = { context, id, 0 };
    context = p.types.AddConstruct(id, context);
    p.types[context].id = context;
    p.types[context].node = n;
    key.type = context;
    p.IDs.Insert(key);
  }

  if(n->node.is<Node::NODES>())
  {
    for(auto& t : n->nodes())
      r_gathertypes(p, t, context);
  }
}

void GatherTypes(Program& p)
{
  r_gathertypes(p, p.root, 0);
}

void ConstructTypes(Program& p)
{

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

UniqueID Program::AddTypeRef(const TypeRef& r)
{
  UniqueID* id = typeregistry.GetRef(r);
  if(!id)
  {
    auto p = typeregistry.Insert(r, ntyperegistry);
    typeregistryhash.Insert(ntyperegistry, &p->_key.first);
    return ntyperegistry++;
  }
  return *id;
}

void r_resolvenode(Program& p, Node* n, cStack<TypeID>& usings, size_t lastusing, TypeID context, bool fullresolve);

void r_resolvedefault(Program& p, Node* n, cStack<TypeID>& usings, size_t lastusing, TypeID context, bool fullresolve)
{
  if(n->node.is<Node::NODES>())
  {
    for(auto& t : n->nodes())
      r_resolvenode(p, t, usings, lastusing, context, fullresolve);
  }
}

Node* r_getinner(Node* n, SYNTAX_PART s)
{
  if(n->s == s && n->node.is<Node::NODES>() && n->nodes().Length() > 0)
    return n->nodes()[0];
  return n;
}

UniqueID r_getTypeRef(Program& p, Node* n)
{
  TypeRef r = { 0 };

  if(n->s == SYNTAX_TYPEID) // This lets us set the context to the resulting ID
    r.type = n->node.get<ID>();
  else if(n->s == SYNTAX_VALUE_TYPE && n->node.get<Value>().v.is<UniqueID*>())
    return n->node.get<Value>().type;
  else // Try to resolve things anyway in an attempt to minimize cascading errors
    ResolveError(p, "identifier did not resolve to TypeID or a TypeRef");
  return p.AddTypeRef(r);
}

void r_resolverest(Program& p, Node* n, Node**& nodes, cStack<TypeID>& usings, size_t lastusing, TypeID context, bool fullresolve)
{
  if(nodes != 0 && n->node.is<Node::NODES>() && n->nodes().Length() > 0)
  {
    while(nodes < n->nodes().end())
    {
      r_resolvenode(p, *nodes, usings, lastusing, context, fullresolve);
      ++nodes;
    }
  }
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

TypeID r_resolvescope(Program& p, Node* n, Node**& nodes, cStack<TypeID>& usings, size_t lastusing, TypeID context, bool fullresolve)
{
  if(nodes != 0 && n->node.is<Node::NODES>() && n->nodes().Length() > 0 && nodes < n->nodes().end())
  {
    r_resolvenode(p, *nodes, usings, lastusing, context, true);

    if(nodes[0]->s == SYNTAX_TYPEID) // This lets us set the context to the resulting ID
      context = nodes[0]->node.get<ID>();
    else
      ResolveError(p, "identifier did not resolve to TypeID or a TypeRef");

    ++nodes;
  }
  else
    ResolveError(p, "scope node has no nodes!");

  return context;
}

#define CHECKCYCLE(c, x) if(p.types[(c)].stage == (x)) { ResolveError(p, "dependency cycle!"); }

void r_resolvetemplate(Program& p, Node* n, cStack<TypeID>& usings, size_t lastusing, TypeID context, bool fullresolve)
{
  if(!n || !n->node.is<Node::NODES>()) return;

  r_resolvenode(p, n, usings, lastusing, context, true);
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

void r_resolvenode(Program& p, Node* n, cStack<TypeID>& usings, size_t lastusing, TypeID context, bool fullresolve)
{
  bool clearusings = false;
  Node* hold;
  Node** pnodes = 0;

  switch(n->s)
  {
  case SYNTAX_USING:
    r_resolvedefault(p, n, usings, lastusing, context, fullresolve);
    hold = r_picknode(p, n, pnodes, SYNTAX_TYPEID, "Using statement did not resolve to a single TYPEID node.");
    if(hold != 0)
      usings.Push(hold->node.get<ID>());
    break;
  case SYNTAX_NAMESPACE:
    lastusing = usings.Length();
    clearusings = true;
    context = r_resolvescope(p, n, pnodes, usings, lastusing, context, fullresolve);
    if(p.types[context].stage == Type::RESOLVE_PARTIAL_BODY)
    {
      if(fullresolve)
        ResolveError(p, "namespace dependency cycle!");
      break;
    }
    p.types[context].stage = Type::RESOLVE_PARTIAL_BODY;
    r_resolverest(p, n, pnodes, usings, lastusing, context, fullresolve);
    p.types[context].stage = Type::RESOLVE_BODY;
    break;
  case SYNTAX_IMPL:
    hold = r_picknode(p, n, pnodes, SYNTAX_TYPEID, "identifier did not resolve to TypeID.");
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
    r_resolverest(p, n, pnodes, usings, lastusing, context, fullresolve);
    p.types[context].stage = Type::RESOLVE_BODY;
    break;
  case SYNTAX_TRAIT:
  case SYNTAX_CLASS:
    lastusing = usings.Length();
    clearusings = true;
    {
      Node* ptemplate = r_picknode(p, n, pnodes, SYNTAX_TEMPLATE, 0);
      context = r_resolvescope(p, n, pnodes, usings, lastusing, context, fullresolve);
      auto& type = p.types[context];
      CHECKCYCLE(context, Type::RESOLVE_PARTIAL_TYPE);
      if(p.types[context].stage < Type::RESOLVE_TYPE)
      {
        r_resolvetemplate(p, ptemplate, usings, lastusing, context, fullresolve);
        p.types[context].stage = Type::RESOLVE_TYPE;

        hold = r_picknode(p, n, pnodes, SYNTAX_SUBNODE, 0);
        if(hold != 0)
        {
          r_resolvenode(p, hold, usings, lastusing, context, true);
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
      if(fullresolve)
      {
        if(p.types[context].stage != Type::RESOLVE_BODY)
        {
          CHECKCYCLE(context, Type::RESOLVE_PARTIAL_BODY);
          r_resolverest(p, n, pnodes, usings, lastusing, context, true);
        }
        p.types[context].stage = Type::RESOLVE_BODY;
      }
    }
    break;
  case SYNTAX_ENUM:
    context = r_resolvescope(p, n, pnodes, usings, lastusing, context, true);
    if(p.types[context].type == TY_ENUM)
    {
      auto& t = p.types[context];
      if(t.stage != Type::RESOLVE_BODY)
      {
        UniqueID enumtype = TY_INT;
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
    context = r_resolvescope(p, n, pnodes, usings, lastusing, context, fullresolve);
    auto& type = p.types[context];
    CHECKCYCLE(context, Type::RESOLVE_PARTIAL_TYPE);
    if(p.types[context].stage < Type::RESOLVE_TYPE)
    {
      r_resolvetemplate(p, ptemplate, usings, lastusing, context, fullresolve);
      if(retval != 0)
      {
        r_resolvenode(p, retval, usings, lastusing, context, true);
        type.returntype = r_getTypeRef(p, retval);
      }

      while(hold = r_picknode(p, n, pnodes, SYNTAX_BASICDECL, 0))
      {
        r_resolvenode(p, hold, usings, lastusing, context, true);
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
        r_resolverest(p, n, pnodes, usings, lastusing, context, true);
        p.types[context].stage = Type::RESOLVE_BODY;
      }
    }
  }
  break;
  case SYNTAX_INVOKE:
    r_resolverest(p, n, pnodes, usings, lastusing, context, true);
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
    clearusings = true;
  case SYNTAX_ATTRIBUTE:
  case SYNTAX_ALGEBRIAC:
  case SYNTAX_ASSERT:
  case SYNTAX_ASSUME:
  case SYNTAX_SUBNODE:
  default:
    r_resolvedefault(p, n, usings, lastusing, context, fullresolve);
    break;
  }

  if(clearusings)
    while(usings.Length() > lastusing)
      usings.Discard();
}

void Resolve(Program& p)
{
  cStack<TypeID> usings;
  r_resolvenode(p, p.root, usings, 0, 0, false); // Avoids instantiating any functions or types that aren't needed
  r_resolvenode(p, p.root, usings, 0, 0, true); // fully instantiates any remaining functions
}

