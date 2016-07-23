// Copyright ©2016 Black Sphere Studios

#ifndef __BERRY_LEXER_H__
#define __BERRY_LEXER_H__

#include "bss-util/cDynArray.h"
#include "bss-util/cStr.h"
#include "bss-util/cHash.h"

typedef unsigned short TOKENID;
typedef unsigned __int64 ID;
typedef unsigned __int64 TypeID;
typedef unsigned __int64 UniqueID;

enum Tokens : TOKENID {
  T_ID=0,
  T_TYPE, // Actual primitive type
  T_NUMBER, // Anything starting with 0-9 is a number
  T_OP, // any general unary or binary operator
  T_STRING, // "anything inside quotes"
  T_CHARACTER, // 'a'
  T_MACROEXPR, // `anything inside backticks`
  T_EMBED, // ^ after a macro block
  T_ABSTRACT,
  T_ASSERT,
  T_ASSUME,
  T_ATTRIBUTE,
  T_BREAK,
  T_CASE,
  T_CATCH,
  T_CLASS,
  T_CONST,
  T_CONTINUE,
  T_ELSE,
  T_ENUM,
  T_FALSE,
  T_FINALLY,
  T_FN,
  T_FOR,
  T_IF,
  T_IMPL,
  T_IMPORT,
  T_IN,
  T_LOOP,
  T_MACRO,
  T_NAMESPACE,
  T_NULL,
  T_OPDEF, // 'op' keyword
  T_PRIVATE,
  T_PUBLIC,
  T_PURE,
  T_RETURN,
  T_STATIC,
  T_SWITCH,
  T_TEMPLATE,
  T_TRAIT,
  T_TRUE,
  T_TRY,
  T_TYPEDEF, // 'type' keyword
  T_UNSAFE,
  T_USING,
  T_VAR,
  T_VIRTUAL,
  T_WHILE,
  T_WITH,
  T_UNDERSCORE, // _ (a solitary underscore is a reserved symbol)
  T_PRIVATEBLOCK, // private:
  T_PUBLICBLOCK, // public:
  T_PIN, // !
  T_DEFREF, // $
  T_TRAITCOMBINE, // + sign when used in traits
  T_COMMA, // ,
  T_LAMBDAEXPR, // -> for a lambda expression
  T_DOT, // .
  T_ELLIPSES, // ... for variadic templates
  T_COLON, // :
  T_SEMICOLON, // ;
  T_ASSIGN, // =
  T_TERNERY, // ?
  T_REF, // @
  T_ALGEBRIAC, // | (used inside algebriac types)
  T_LPAREN, // (
  T_RPAREN, // )
  T_LBRACKET, // [
  T_RBRACKET, // ]
  T_LBRACE, // {
  T_RBRACE, // }
  T_EOF, // signifies end of file, but there might be another file after this one.
  T_NUMTOKENS
};

enum RawTypes {
  TY_UNKNOWN,
  TY_U8,
  TY_I8,
  TY_F64,
  TY_F32,
  TY_F16,
  TY_I16,
  TY_I32,
  TY_I64,
  TY_INT,
  TY_U16,
  TY_U32,
  TY_U64,
  TY_UINT,
  TY_STRING,
  TY_STRING16,
  TY_STRING32,
  TY_BOOL,
  TY_VOID,
  TY_VAR,
  TY_COMPLEX,
  TY_TRAIT,
  TY_ENUM,
  TY_FUNC,
  TY_ALGEBRIAC,
  TY_NAMESPACE,
  TY_PLACEHOLDER, // Used for template placeholder types
  TY_NUMTYPES
};

struct TOKEN {
  TOKEN(Tokens token_,const char* s_,size_t len_) : token(token_), s(s_), len(len_) {}
  Tokens token;
  const char* s;
  size_t len;
};

using namespace bss_util;

// Parses an input stream into a series of tokens
extern void Parse(const char* s, cDynArray<TOKEN>& tokens, cDynArray<cStr, unsigned __int64, CARRAY_SAFE>& strings, cHash<const char*, unsigned int>& hash);
// Tries to get a word from the built-in type list
extern TOKENID GetType(const char* s, unsigned int len);
extern TOKENID GetType(const char* s);
extern void DumpTokens(cDynArray<TOKEN>& tokens, std::ostream& out);
extern const char* ReverseToken(TOKENID token);

#endif