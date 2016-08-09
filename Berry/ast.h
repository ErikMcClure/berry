// Copyright ©2015 Black Sphere Studios

#ifndef __BERRY_AST_H__
#define __BERRY_AST_H__

#include "bss-util/cStr.h"
#include "bss-util/cDynArray.h"
#include "bss-util/LLBase.h"
#include "bss-util/cHash.h"
#include "bss-util/bss_stack.h"
#include "bss-util/variant.h"
#include "bss-util/cAVLtree.h"
#include "bss-util/cTRBtree.h"
#include "bss-util/cArraySort.h"
#include "process.h"

enum SYNTAX_PART : unsigned char {
  SYNTAX_ROOT = 0,
  SYNTAX_FILE,
  SYNTAX_USING,
  SYNTAX_NAMESPACE,
  SYNTAX_ALGEBRIAC,
  SYNTAX_ATTRIBUTE,
  SYNTAX_IMPL,
  SYNTAX_ASSERT,
  SYNTAX_ASSUME,
  SYNTAX_TRAIT,
  SYNTAX_CLASS,
  SYNTAX_ENUM,
  SYNTAX_FUNCTION,
  SYNTAX_CONSTRUCTOR,
  SYNTAX_DESTRUCTOR,
  SYNTAX_INVOKE,
  SYNTAX_OP,
  SYNTAX_DOTTYPE,  // This holds a non-resolved ID[0].ID[Arg].ID... chain
  SYNTAX_BASICDECL,
  SYNTAX_VARDECL,
  SYNTAX_BLOCK,
  SYNTAX_FORLOOP,
  SYNTAX_WITH,
  SYNTAX_LOOP,
  SYNTAX_SWITCH,
  SYNTAX_IF,
  SYNTAX_RETURN,
  SYNTAX_BREAK,
  SYNTAX_CONTINUE,
  SYNTAX_TRYCATCH,
  SYNTAX_TRYELSE,
  SYNTAX_TRYFINALLY,
  SYNTAX_TEMPLATE,
  SYNTAX_TEMPLATE_PARAM_DEFAULT,
  SYNTAX_TEMPLATE_PARAM_SPEC,
  SYNTAX_TYPE, // This is a type expression
  SYNTAX_TYPE_FN,
  SYNTAX_TYPE_ALGEBRIAC,
  SYNTAX_TYPEID, // This is an ID that was resolved to a TypeID.
  SYNTAX_TYPEDEF, // This is a "type =" type definition
  SYNTAX_VARTYPELAMBDA,
  SYNTAX_LAMBDA,
  SYNTAX_EXPR,
  SYNTAX_TEMPLATEARRAY,
  SYNTAX_SLICE,
  SYNTAX_INITLISTRAW,
  SYNTAX_INITLIST,
  SYNTAX_DOTID, // This holds a non-resolved ID.ID.ID... chain
  SYNTAX_IMPORT,
  SYNTAX_TOKEN, // This stores a token that has not been resolved yet
  SYNTAX_VALUE, // Unresolved value expression
  SYNTAX_VALUE_ID, // Holds an ID
  SYNTAX_VALUE_NUMBER, // any number that hasn't been resolved yet
  SYNTAX_VALUE_CONSTANT, // Any constant value that is simply its own type.
  SYNTAX_VALUE_STRING,
  SYNTAX_VALUE_CHARACTER,
  SYNTAX_VALUE_NULL,
  SYNTAX_VALUE_TYPE, // Points to a TypeRef resolved to a Monotype
  SYNTAX_SUBNODE,
  NUM_SYNTAX
};

enum TYPE_MODIFIERS : uint16_t {
  TYPEMOD_PRIVATE =   0b1, // The absence of this implies that the type is public. This only affects top-level type declarations
  TYPEMOD_MEMBER =    0b10, // function that's part of a class
  TYPEMOD_PURE =      0b100,
  TYPEMOD_VIRTUAL =   0b1000,
  TYPEMOD_ABSTRACT =  0b10000,
  TYPEMOD_OP =        0b100000, // Operator
  TYPEMOD_PREFIX =    0b1000000,
  TYPEMOD_POSTFIX =   0b10000000,
  TYPEMOD_PROPERTY =  0b100000000,
};

enum TYPEREF_MODIFIERS : char {
  TYPEREFMOD_CONST = 0b1,
  TYPEREFMOD_STATIC = 0b10, // used to signify that a variable is static
  TYPEREFMOD_UNSAFE = 0b100,
  TYPEREFMOD_PINNED = 0b1000,
  TYPEREFMOD_WEAK = 0b10000,
  TYPEREFMOD_SLICE = 0b100000,
  TYPEREFMOD_ARRAY = 0b1000000, // marks a dynamic or fixed size array. If dim is empty, it's a dynamic array.
  TYPEREFMOD_COMPARISON = TYPEREFMOD_CONST | TYPEREFMOD_UNSAFE | TYPEREFMOD_SLICE | TYPEREFMOD_WEAK | TYPEREFMOD_ARRAY,
};

struct Type;
struct Value;

struct TypeRef
{
  TypeID type;
  char mods; // TYPEREF_MODIFIERS
  char refs; // Number of indirections stored in the below integer.
  uint64_t indirection; // each two bits represents 4 possible states: mut ref, const ref, mut nonnullable, const nonnullable
  bss_util::cDynArray<Value> params; // If this is referring to a template overload, this contains the parameters.
  bss_util::cDynArray<__int64> dim; // If this is a fixed size array, contains the array dimensions.

  // This creates a partial ordering of types to allow the assignment of Monotypes for type resolution.
  static char Comp(const TypeRef& l, const TypeRef& r);
};

struct Value
{
  typedef bss_util::variant<double, __int64, cStr, bss_util::cDynArray<Value>, Monotype*, ID> V; // Monotype* holds no value, it simply means this is a literal type.
  Monotype type;
  V v;

  static char Comp(const Value& l, const Value& r) {
    char ret = SGNCOMPARE(l.type, r.type);
    if(!ret) ret = SGNCOMPARE(l.v.tag(), r.v.tag());
    if(ret) return ret;
    switch(l.v.tag())
    {
    case Value::V::Type<double>::value: return SGNCOMPARE(l.v.get<double>(), r.v.get<double>());
    case Value::V::Type<__int64>::value: return SGNCOMPARE(l.v.get<__int64>(), r.v.get<__int64>());
    case Value::V::Type<cStr>::value: return (char)strcmp(l.v.get<cStr>(), r.v.get<cStr>());
    case Value::V::Type<Monotype*>::value: return 0;
    case Value::V::Type<ID>::value: return SGNCOMPARE(l.v.get<ID>(), r.v.get<ID>());
    }
    assert(false);
    return 0;
  }
};

struct Node
{
  typedef bss_util::cDynArray<Node*> NODES;

  SYNTAX_PART s;
  Monotype t; // Can also be a TypeID for CLASS/TRAIT/IMPL etc. nodes
  bss_util::variant<NODES, Value, ID, cStr> node;
  Node* parent;
  Node(SYNTAX_PART part, Node* _parent) : s(part), parent(_parent) {}
  Node(SYNTAX_PART part, ID id, Node* _parent) : s(part), node(id), parent(_parent) {}
  Node(SYNTAX_PART part, cStr&& str, Node* _parent) : s(part), node(std::move(str)), parent(_parent) {}

  inline NODES& nodes() { return node.get<NODES>(); }
  inline Node* AddNode(Node* n) { if(n != 0) { n->parent = this; nodes().Add(n); } return n; }
  inline Node* AddNullNode(Node* n) { if(n != 0) { n->parent = this; nodes().Add(n); } else nodes().Add(0); return n; }
};

struct TemplateArg
{
  Monotype t; // If this is a type argument, this will point to a polytype that contains a list of the traits constraining it.
  ID id; // Otherwise, t points to a standard type, and this is the name of the value argument.
  Value v; // if applicable, this is the value of the value argument
  Value d; // This is the default argument, if it exists.
};

struct Type
{
  Type() {}
  Type(ID _name, TypeID _scope) : name(_name), scope(_scope), type(TY_UNKNOWN), mods(0), node(nullptr), stage(RESOLVE_NONE) {}
  ID name;
  TypeID scope; // Identifier of containing type (namespaces count as types for this purpose).
  TypeID id; 
  RawTypes type;
  uint16_t mods; // TYPE_MODIFIERS
  bss_util::cDynArray<Monotype> subtypes; // This lists inherited types if it's TY_COMPLEX, parameters if it's a function, traits if it's TY_POLYTYPE, or types if it's an algebriac type.
  bss_util::cDynArray<Monotype> members; // This lists members if it's TY_COMPLEX
  bss_util::cDynArray<ID> typenames; // Lists member names if TY_COMPLEX, or parameter names if it's a function.
  bss_util::cDynArray<TemplateArg> templateargs; // Either store the template arguments to this type, or stores enumeration pairs.
  bss_util::cDynArray<Monotype> traits; // stores the traits this type implements.
  Monotype returntype; // Stores return type of function
  Node* node; // Points to this type's definition in the AST
  enum { RESOLVE_NONE = 0, RESOLVE_PARTIAL_TYPE, RESOLVE_TYPE, RESOLVE_PARTIAL_BODY, RESOLVE_BODY } stage;
};

struct TypeTuple
{
  TypeID parent;
  ID name;
  TypeID type;

  static char Comp(const TypeTuple& l, const TypeTuple& r) {
    char ret = SGNCOMPARE(l.parent, r.parent);
    if(!ret) ret = SGNCOMPARE(l.name, r.name);
    return !ret ? SGNCOMPARE(l.type, r.type) : ret;
  }
};

struct TypeConstraint
{
  typedef bss_util::variant<TypeRef, Value> Constraint;
  TypeID type; // Type definition this corresponds to. The number of template arguments doesn't need to match up with this constraint if they have default values.
  bss_util::cDynArray<Constraint, size_t, CARRAY_SAFE> constraints; // Constraints that are active on this type. This can be empty if there are no constraints. Default values are removed and evaluated elsewhere.

  static char Comp(const TypeConstraint& l, const TypeConstraint& r) {
    char ret = SGNCOMPARE(l.type, r.type);
    if(!ret) ret = SGNCOMPARE(l.constraints.Length(), r.constraints.Length());
    for(size_t i = 0; i < l.constraints.Length() && !ret; ++i)
    {
      ret = SGNCOMPARE(l.constraints[i].tag(), r.constraints[i].tag());
      if(!ret)
        ret = l.constraints[i].is<TypeRef>() ? TypeRef::Comp(l.constraints[i].get<TypeRef>(), r.constraints[i].get<TypeRef>()) : Value::Comp(l.constraints[i].get<Value>(), r.constraints[i].get<Value>());
    }
    return ret;
  }
};

struct TypeFunction : TypeConstraint
{
  bss_util::cDynArray<TypeRef, size_t, CARRAY_SAFE> parameters;

  static char Comp(const TypeFunction& l, const TypeFunction& r) {
    char ret = TypeConstraint::Comp(l, r);
    if(!ret) ret = SGNCOMPARE(l.parameters.Length(), r.parameters.Length());
    for(size_t i = 0; i < l.parameters.Length() && !ret; ++i)
      ret = TypeRef::Comp(l.parameters[i], r.parameters[i]);
    return ret;
  }
};

struct TypeFunctionArgTuple
{
  size_t arg;
  ID name;
  TypeID context;
  TypeID parameter;
  TypeID implementation;

  static char Comp(const TypeFunctionArgTuple& l, const TypeFunctionArgTuple& r) {
    char ret = SGNCOMPARE(l.arg, r.arg);
    if(!ret) ret = SGNCOMPARE(l.context, r.context);
    if(!ret) ret = SGNCOMPARE(l.name, r.name);
    if(!ret) ret = SGNCOMPARE(l.parameter, r.parameter);
    if(!ret) ret = SGNCOMPARE(l.implementation, r.implementation);
    return ret;
  }
};

struct Program
{
  enum ARCH { ARCH_X86, ARCH_X64, ARCH_ARM, ARCH_WASM };
  Program(ARCH a) : root(0), architecture(a), ntyperegistry(0)
  {
    _addBaseType("", TY_UNKNOWN);
    _addBaseType("u8", TY_U8);
    _addBaseType("i8", TY_I8);
    _addBaseType("f64", TY_F64);
    _addBaseType("f32", TY_F32);
    _addBaseType("f16", TY_F16);
    _addBaseType("i16", TY_I16);
    _addBaseType("i32", TY_I32);
    _addBaseType("i64", TY_I64);
    _addBaseType("int", TY_INT);
    _addBaseType("u16", TY_U16);
    _addBaseType("u32", TY_U32);
    _addBaseType("u64", TY_U64);
    _addBaseType("uint", TY_UINT);
    _addBaseType("string", TY_STRING);
    _addBaseType("string16", TY_STRING16);
    _addBaseType("string32", TY_STRING32);
    _addBaseType("bool", TY_BOOL);
    _addBaseType("void", TY_VOID);
  }

  Node* root;
  cDynArray<TOKEN> tokens;
  cDynArray<cStr, ID, CARRAY_SAFE> strings; // Table of raw strings
  cDynArray<cStr, ID, CARRAY_SAFE> errors; // list of errors
  cDynArray<Type, TypeID, CARRAY_SAFE> types;
  bss_util::cTRBtree<TypeTuple, &TypeTuple::Comp> IDs;
  bss_util::cAVLtree<TypeRef, Monotype, &TypeRef::Comp> typeregistry;
  Monotype ntyperegistry;
  bss_util::cHash<Monotype, TypeRef*> typeregistryhash;
  bss_util::cHash<std::pair<Monotype, Monotype>, int> typemapping; //stores all a -> b type mappings and the resulting type distance
  bss_util::cAVLtree<TypeConstraint, void, &TypeConstraint::Comp> typeconstraints;
  bss_util::cAVLtree<TypeFunction, void, &TypeFunction::Comp> typefunctions;
  bss_util::cArraySort<TypeFunctionArgTuple, &TypeFunctionArgTuple::Comp> functionargs; // A sorted list of the function name, it's context, and it's nth argument, along with all the implementations of that function name that also satisfy that argument
  Processed processed;
  cStr LLVM; // LLVM IR output
  const ARCH architecture;

  Monotype AddTypeRef(const TypeRef& r);
  TypeID GetParent(TypeID child);

private:
  void _addBaseType(const char* name, RawTypes type)
  {
    TypeID t = types.AddConstruct(strings.Add(name), 0);
    assert(t == type);
    types.Back().id = t;
    types.Back().type = type;
    Monotype id = AddTypeRef(TypeRef { t });
    assert(id == type);
  }
};

extern void TraverseAST(Program& p, void(*f)(Program&, Node*));

// Builds an AST out of a sequence of tokens.
extern void BuildAST(Program& p);
extern void DumpAST(Program& p, std::ostream& out);
// Finds all types in the AST and builds a provisional table of them.
extern void GatherTypes(Program& p);
// Resolves all function signatures, type signatures, type mappings, and traits.
extern void ResolveTypes(Program& p);
// Resolves all types and collapses all expressions in the AST
extern void Resolve(Program& p);
// Processes the AST into a processed list of raw types and functions.
extern void Process(Program& p);
// Evaluates all static expressions to constant values when possible.
extern void EvaluateStatics(Program& p);
// Performs static analysis used to calculate optimizations
extern void Analyze(Program& p);
// Does all high level optimizations
extern void Optimize(Program& p);
// Outputs LLVM IR
extern void OutputLLVM(Program& p);
// Optimizes LLVM IR
extern void OptimizeLLVM(Program& p);
// Compiles LLVM IR
extern void CompileLLVM(Program& p);

#endif