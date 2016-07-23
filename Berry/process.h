// Copyright ©2016 Black Sphere Studios

#ifndef __BERRY_PROCESS_H__
#define __BERRY_PROCESS_H__

#include "bss-util/cDynArray.h"
#include "bss-util/cHash.h"
#include "bss-util/variant.h"
#include "lexer.h"

struct Processed
{
  struct FnCall;
  struct Assert;
  struct Control;
  struct Loop;
  struct If;
  struct Switch;
  struct Variable;

  typedef bss_util::variant<FnCall, Assert, Control, Loop, If, Switch, Variable> Instruction;
  typedef bss_util::cDynArray<Instruction, size_t, CARRAY_SAFE> Expression;

  struct Type
  {
    RawTypes type; // Specifies type. Can only be TY_COMPLEX, TY_FUNC, an integer, or a float.
    TypeID pointer; // If indirection is nonzero, _subtypes must be empty and this will contain the ID of the type being pointed to
    uint16_t align; // specifies alignment
    uint16_t indirection; // if nonzero, specifies that this is a pointer type with this many pointers.
    size_t count; // If not equal to 1, specifies an array of this type.
    bss_util::cDynArray<Type> _subtypes; // Specifies struct members if this is TY_COMPLEX, or the function return value followed by function arguments if this is TY_FUNC
  };

  struct FnCall
  {
    ID id;
    bss_util::cDynArray<Expression, size_t, CARRAY_SAFE> args;
    ID retval; // ID of the variable storing the return value.
    // preconditions derived from context
    // postconditions derived from code path based on preconditions
  };

  struct Assert
  {
    Expression expression;
  };

  struct Control
  {
    enum { RETURN, BREAK, CONTINUE } type;
    Expression arg;
  };

  struct Loop
  {
    Expression body;
  };

  struct If
  {
    Expression condition;
    Expression body;
    Expression otherwise; // holds instructions for "else" case.
  };

  // Represents an integral switch statement. Other switch statements must be resolved to something else before this.
  struct Switch
  {
    Expression condition;
    Expression default;
    bss_util::cDynArray<std::pair<ptrdiff_t, Expression>, size_t, CARRAY_SAFE> cases;
  };

  struct Variable
  {
    TypeID type;
    cStr name;
    ID id;
  };

  //struct Unsafe
  //{
  //  enum { POINTER_ADD, POINTER_SUB, POINTER_MUL, POINTER_ACCESS } type;
  //  Expression expression;
  //};

  struct Function
  {
    cStr name;
    ID id;
    Expression instructions;
    TypeID ret; // return value type
    cDynArray<TypeID> args; // type of each argument
    // baseline preconditions
    // postconditions satisfied on all code paths
  };

  bss_util::cDynArray<Function, size_t, CARRAY_SAFE> functions;
  bss_util::cHash<ID, Function*> fnhash;
  bss_util::cDynArray<Type, TypeID> types;
};

#endif