// Copyright ©2015 Black Sphere Studios

#include "bss-util/cDynArray.h"
#include "bss-util/cStr.h"
#include "bss-util/cHash.h"

enum Tokens {
  T_ID=0,
  T_RETURN,
  T_IF,
  T_ELSE,
  T_FOR,
  T_WHILE,
  T_DO,
  T_SWITCH,
  T_CASE,
  T_BREAK,
  T_CONTINUE,
  T_PURE,
  T_CONST, 
  T_UNSAFE,
  T_FOREACH,
  T_FN,
  T_TEMPLATE,
  T_TYPEDEF, // 'type' keyword
  T_ASSERT,
  T_DEFAULT,
  T_VAR,
  T_USING,
  T_VIRTUAL,
  T_INLINE,
  T_STATIC,
  T_SIGNED,
  T_UNSIGNED,
  T_NAMESPACE,
  T_CLASS,
  T_ENUM,
  T_ABSTRACT,
  T_CONTRACT,
  T_NULL,
  T_PUBLIC,
  T_PROTECTED,
  T_PRIVATE,
  T_TRY,
  T_CATCH,
  T_FINALLY,
  T_IMPORT,
  T_NUMBER, // Anything starting with 0-9 is a number
  T_STRING, // "anything inside quotes"
  T_CHARACTER, // 'a'
  /*T_SEMICOLON, // ;
  T_COLON, // :
  T_COMMA, // ,
  T_DOT, // .
  T_ASSIGN, // =
  T_TERNERY, // ?
  T_EXCHANGE, // <>*/
  T_LPAREN, // (
  T_RPAREN, // )
  T_LBRACKET, // [
  T_RBRACKET, // ]
  T_LBRACE, // {
  T_RBRACE, // }
  T_OP, // any general unary or binary operator
  T_TYPEID,
  //T_REFOP, // @
  T_EOF, // signifies end of file, but there might be another file after this one.
  /*
  T_NEGATION, // - (any non-binary usage of - gets classified as a negation)
  T_POINTER, // * (any non-binary usage of * gets classified as either a pointer type signifier or a dereference operator)
  T_PLUS, // +
  T_MINUS, // -
  T_MULTIPLY, // *
  T_DIVIDE, // /
  T_XOR, // ^
  T_REMAINDER, // %
  T_BITAND, // &
  T_BITOR, // |
  T_FLIP, // ~ (prefix unary)
  T_NOT, // ! (prefix unary)
  T_LESSER, // <
  T_GREATER, // >
  T_LEQUAL, // <=
  T_GEQUAL, // >=
  T_EQUAL, // ==
  T_MODULO, // %%
  T_AND, // &&
  T_OR, // ||
  T_LBITROTATE, // <|
  T_RBITROTATE, // |>
  T_LBITSHIFT // <<
  T_RBITSHIFT // >>
  T_INC, // ++ (prefix unary)
  T_DEC, // -- (prefix unary)
  T_POSTINC, // ++ (postfix unary)
  T_POSTDEC, // -- (postfix unary)
  T_NOTEQUAL, // !=
  T_PLUSEQUAL, // +=
  T_MINUSEQUAL, // -=
  T_MULEQUAL, // *=
  T_DIVEQUAL, // /=
  T_XOREQUAL, // ^=
  T_BITANDEQUAL, // &=
  T_BITOREQUAL, // |=
  T_MODULOEQUAL, // %=
  T_LBITROTATEEQUAL, // <|=
  T_RBITROTATEEQUAL, // |>=
  T_LBITSHIFTEQUAL, // <<=
  T_RBITSHIFTEQUAL, // >>=
  T_ANDEQUAL, // &&=
  T_OREQUAL, // ||=
  T_REMAINDEREQUAL, // %%=*/
  T_NUMTOKENS
};

struct TOKEN {
  TOKEN(Tokens token_,const char* s_,size_t len_) : token(token_), s(s_), len(len_) {}
  Tokens token;
  const char* s;
  size_t len;
};

using namespace bss_util;

// Parses an input stream into a series of tokens
extern void Parse(const char* s, cDynArray<TOKEN>& tokens, cDynArray<cStr, unsigned int, CARRAY_SAFE>& strings, cHash<const char*, unsigned int>& hash);
// Tries to get a word from the built-in type list
extern unsigned char GetType(const char* s, unsigned int len);
extern unsigned char GetType(const char* s);
