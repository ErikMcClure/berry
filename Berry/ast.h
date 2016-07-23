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
  SYNTAX_VALUE_TYPE, // Points to a TypeRef resolved to a UniqueID
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
};

enum TYPEREF_MODIFIERS : char {
  TYPEREFMOD_CONST = 0b1,
  TYPEREFMOD_STATIC = 0b10, // used to signify that a variable is static
  TYPEREFMOD_UNSAFE = 0b100,
  TYPEREFMOD_PINNED = 0b1000,
  TYPEREFMOD_SLICE = 0b10000,
  TYPEREFMOD_ARRAY = 0b100000, // marks a dynamic or fixed size array. If dim is empty, it's a dynamic array.
  TYPEREFMOD_COMPARISON = TYPEREFMOD_CONST | TYPEREFMOD_UNSAFE | TYPEREFMOD_SLICE | TYPEREFMOD_ARRAY,
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

  // This creates a partial ordering of types to allow the assignment of UniqueIDs for type resolution.
  static char Comp(const TypeRef& l, const TypeRef& r);
};

struct Value
{
  typedef bss_util::variant<double, __int64, cStr, bss_util::cDynArray<Value>, UniqueID*, ID> V; // UniqueID* holds no value, it simply means this is a literal type.
  UniqueID type;
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
    case Value::V::Type<UniqueID*>::value: return 0;
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
  bss_util::variant<NODES, Value, ID, cStr> node;
  Node(SYNTAX_PART part) : s(part) {}
  Node(SYNTAX_PART part, ID id) : s(part), node(id) {}
  Node(SYNTAX_PART part, cStr&& str) : s(part), node(std::move(str)) {}

  inline NODES& nodes() { return node.get<NODES>(); }
  inline Node* AddNode(Node* n) { if(n != 0) nodes().Add(n); return n; }
};

struct TemplateArg
{
  UniqueID t; // If this is a type argument, this will point to a placeholder type that contains a list of the traits constraining it.
  ID id; // Otherwise, t points to a standard type, and this is the name of the value argument.
  Value v; // if applicable, this is the value of the value argument
  Value d; // This is the default argument, if it exists.
};

struct Type
{
  Type() {}
  Type(ID _name, TypeID _scope) : name(_name), scope(_scope), type(TY_UNKNOWN), mods(0), priority(0), node(nullptr), stage(RESOLVE_NONE) {}
  ID name;
  TypeID scope; // Identifier of containing type (namespaces count as types for this purpose).
  TypeID id; 
  RawTypes type;
  uint16_t mods; // TYPE_MODIFIERS
  int priority; // If this is an operator, store the priority.
  bss_util::cDynArray<UniqueID> subtypes; // This lists inherited types if it's TY_COMPLEX, parameters if it's a function, traits if it's TY_PLACEHOLDER, or types if it's an algebriac type.
  bss_util::cDynArray<UniqueID> members; // This lists members if it's TY_COMPLEX
  bss_util::cDynArray<ID> typenames; // Lists member names if TY_COMPLEX, or parameter names if it's a function.
  bss_util::cDynArray<TemplateArg> templateargs; // Either store the template arguments to this type, or stores enumeration pairs.
  bss_util::cDynArray<UniqueID> traits; // stores the traits this type implements.
  UniqueID returntype; // Stores return type of function
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
  bss_util::cAVLtree<TypeTuple, void, &TypeTuple::Comp> IDs;
  bss_util::cAVLtree<TypeRef, UniqueID, &TypeRef::Comp> typeregistry;
  bss_util::cHash<UniqueID, TypeRef*> typeregistryhash;
  bss_util::cHash<std::pair<UniqueID, UniqueID>, int> typemapping; //stores all a -> b type mappings and the resulting type distance
  UniqueID ntyperegistry;
  Processed processed;
  cStr LLVM; // LLVM IR output
  const ARCH architecture;

  UniqueID AddTypeRef(const TypeRef& r);

private:
  void _addBaseType(const char* name, RawTypes type)
  {
    TypeID t = types.AddConstruct(strings.Add(name), 0);
    assert(t == type);
    types.Back().id = t;
    types.Back().type = type;
    UniqueID id = AddTypeRef(TypeRef { t });
    assert(id == type);
  }
};

extern void TraverseAST(Program& p, void(*f)(Program&, Node*));

// Builds an AST out of a sequence of tokens.
extern void BuildAST(Program& p);
extern void DumpAST(Program& p, std::ostream& out);
// Finds all types in the AST and builds a provisional table of them.
extern void GatherTypes(Program& p);
// Construct basic type framework for user types
extern void ConstructTypes(Program& p);
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