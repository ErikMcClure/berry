// Copyright ©2015 Black Sphere Studios

#include <memory>
#include "trex.h"
#include "bss-util/cTrie.h"
#include "lexer.h"

using namespace bss_util;

// Punctuation characters without escaping:  !"#$%&'()*+,-./:;<=>?@[\]^{|}~
#define WHITESPACE " \\t\\r\\n\\v\\f"
#define PUNCTUATION "!\"#$%&'*+\\-./:<=>?@\\\\\\^|~"
#define RESERVED "`;,()\\[\\]{}"
static const char* trex_err;
TRex* regex_ID = trex_compile("^[^" PUNCTUATION WHITESPACE RESERVED "]+", &trex_err);
//TRex* regex_N = trex_compile("^([0-9]+(\.[0-9]+)?|0x[0-9A-Fa-f]+|0b[01]+|0o[0-7]+)([eE]-?[0-9]+)?[^" PUNCTUATION WHITESPACE RESERVED "]+", &trex_err);
TRex* regex_N = trex_compile("^[0-9]+(\\.[0-9]+)?([eE]-?[0-9]+)?[^" PUNCTUATION WHITESPACE RESERVED "]*", &trex_err);
TRex* regex_OP = trex_compile("^[" PUNCTUATION "]+", &trex_err);

TOKENID GetType(const char* s, unsigned int len)
{
  static cTrie<TOKENID> types(23, "u8", "i8", "f64", "f32", "f16", "i16", "i32", "i64", "int", "u16", "u32", "u64", "uint", "string", "string16", "string32",
    "bool", "var", "void", "byte", "char", "double", "float");
  TOKENID t = types.Get(s, (TOKENID)len);
  return (len > 64 || t == (TOKENID)-1) ? (TOKENID)-1 : ((t % TY_COMPLEX) + 1); // no built-in type is longer than 64 characters
}

TOKENID GetType(const char* s)
{
  return GetType(s, strlen(s));
}

inline unsigned int strinsert(const char* start, const char* end, cDynArray<cStr, unsigned __int64, CARRAY_SAFE>& strings, cHash<const char*, unsigned int>& hash)
{
  static cStr store;
  store.assign(start, end-start);

  if(hash.Exists(store)) {
    return hash[store];
  }

  unsigned int ret = strings.Add(store);
  hash.Insert(strings.Back(), ret);
  return ret;
}
TOKEN parse_inner(const char*& s, cDynArray<cStr, unsigned __int64, CARRAY_SAFE>& strings, cHash<const char*, unsigned int>& hash)
{
  static cTrie<TOKENID> t(41, "abstract", "assert", "assume", "attribute", "break", "case", "catch", "class", "const", "continue",
    "else", "enum", "false", "finally", "fn", "for", "if", "impl", "import", "in", "loop", "macro", "namespace",
    "null", "op", "private", "public", "pure", "return", "static", "switch", "template", "trait", "true", "try", "type",
    "unsafe", "using", "var", "virtual", "while", "with", "_");
  const char* begin;
  const char* end;
  TOKENID r;
  for(;;)
  {
    while(isspace(s[0])) s++; // skip spaces
    if(!s[0]) return TOKEN(T_EOF, 0, 0); // If we hit the end of the file return EOF
    if(s[0]=='/') // Check for a possible comment
    {
      if(s[1]=='/') // line comment
      {
        for(s+=2; s[0]!=0 && s[0]!='\n'; ++s);
        continue;
      } else if(s[1]=='*') // block comment
      {
        for(s+=2; s[0]!=0 && !(s[0]=='*' && s[1]=='/'); ++s);
        s+=2; //this pushes the pointer past the ending */
        continue;
      }
    }
    break;
  }
  if(s[0]>='0' && s[0]<='9') // Is it a number?
  {
    if(!trex_search(regex_N, s, &begin, &end)) // Try to match all possible numbers and find the end of it.
    {
      if(!trex_search(regex_ID, s, &begin, &end)) // if it failed, absorb it as an ID and discard it
        ++s; // if that somehow fails increment the string by one character
      s = end;
      return TOKEN(T_NUMTOKENS, "Malformed numerical constant.", -1); // If we failed, it was malformed.
    }
    s = end;
    return TOKEN(T_NUMBER, begin, end-begin);
  }
  if(s[0]=='"') // Is it a string?
  {
    for(begin=(++s); s[0]!=0 && s[0]!='"'; ++s)
    {
      if(s[0]=='\\' && s[1]=='"' && s[-1] != '\\') // make sure we haven't escaped the escape character
        s+=2; // this skips escaped quotes (we evaluate escaped characters later)
    }
    return TOKEN(T_STRING, 0, strinsert(begin, s++, strings, hash));
  }
  if(s[0]=='\'') // Is it a character?
  {
    for(begin=(++s); s[0]!=0 && s[0]!='\''; ++s)
    {
      if(s[0]=='\\' && s[1]=='\'' && s[-1] != '\\') // make sure we haven't escaped the escape character
        s+=2; // this skips escaped quotes (we evaluate escaped characters later)
    }
    return TOKEN(T_CHARACTER, 0, strinsert(begin, s++, strings, hash));
  }
  if(s[0] == '`') // Is it a macro expression?
  {
    for(begin = (++s); s[0] != 0 && s[0] != '`'; ++s); // macros cannot be escaped
    return TOKEN(T_MACROEXPR, 0, strinsert(begin, s++, strings, hash));
  }
  if(trex_search(regex_ID, s, &begin, &end)) // Is it an identifier or a keyword?
  {
    s=end;
    r=t.Get(begin, end-begin);
    if(r == (TOKENID)-1) // If this happens it isn't a reserved keyword, so check if it's a type
    {
      r = GetType(begin, end - begin);
      if(r == (TOKENID)-1) // It's not a type either so return it as an ordinary identifier
        return TOKEN(T_ID, 0, strinsert(begin, end, strings, hash));
      return TOKEN(T_TYPE, 0, r); // Otherwise it was a built-in type.
    }
    if(*end == ':')
    {
      switch(r + T_ABSTRACT)
      {
      case T_PUBLIC: r = T_PUBLICBLOCK; ++s; break;
      case T_PRIVATE: r = T_PRIVATEBLOCK; ++s; break;
      }
    }
    return TOKEN(Tokens(r + T_ABSTRACT), 0, 0); // Otherwise it was one of our reserved words
  }
  switch(s[0]) // If it wasn't an identifier it was some sort of operator character. Check for our special ones first.
  {
  case ';':
    return TOKEN(T_SEMICOLON, s++, 1);
  case ',':
    return TOKEN(T_COMMA, s++, 1);
  case '.':
    return TOKEN(T_DOT, s++, 1);/*
  case ':':
    return TOKEN(T_COLON, s++, 1);
  case '?':
    return TOKEN(T_TERNERY, s++, 1);*/
  case '(':
    return TOKEN(T_LPAREN, s++, 1);
  case ')':
    return TOKEN(T_RPAREN, s++, 1);
  case '[':
    return TOKEN(T_LBRACKET, s++, 1);
  case ']':
    return TOKEN(T_RBRACKET, s++, 1);
  case '{':
    return TOKEN(T_LBRACE, s++, 1);
  case '}':
    return TOKEN(T_RBRACE, s++, 1);
  default:
    if(trex_search(regex_OP, s, &begin, &end)) // Otherwise it must be an arbitrary operator
    {
      s = end;
      return TOKEN(T_OP, begin, end - begin);
    }
  }
  ++s;
  return TOKEN(T_NUMTOKENS, "Bad character in stream.", -1); // parse error
}

void Parse(const char* s, cDynArray<TOKEN>& tokens, cDynArray<cStr, unsigned __int64, CARRAY_SAFE>& strings, cHash<const char*, unsigned int>& hash)
{
  do { tokens.Add(parse_inner(s, strings, hash)); } while(tokens.Back().token != T_EOF);
}

const char* ReverseToken(TOKENID token)
{
  static const char* reverse[] = {
    "ID","TYPE", "NUMBER", "OP", "STRING", "CHARACTER", "MACROEXPR", "EMBED", "ABSTRACT","ASSERT","ASSUME","ATTRIBUTE",
    "BREAK","CASE","CATCH","CLASS","CONST","CONTINUE","ELSE","ENUM","FALSE","FINALLY","FN","FOR","IF","IMPL","IMPORT",
    "IN","LOOP","MACRO","NAMESPACE","NULL","OPDEF", "PRIVATE","PUBLIC","PURE","RETURN","STATIC","SWITCH","TEMPLATE",
    "TRAIT","TRUE","TRY","TYPEDEF", "UNSAFE","USING","VAR","VIRTUAL","WHILE","WITH","UNDERSCORE", "PRIVATEBLOCK",
    "PUBLICBLOCK", "PIN", "DEFREF", "TRAITCOMBINE", "COMMA", "LAMBDAEXPR", "DOT", "ELLIPSES", "COLON", "SEMICOLON",
    "ASSIGN", "TERNERY", "REF", "ALGEBRIAC", "LPAREN", "RPAREN", "LBRACKET", "RBRACKET", "LBRACE", "RBRACE", "EOF"
  };

  return reverse[token];
}

void DumpTokens(cDynArray<TOKEN>& tokens, std::ostream& out)
{
  for(auto& i : tokens)
  {
    out << "[" << ReverseToken(i.token) << "]";
  }

  out << std::endl;
}