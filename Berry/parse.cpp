// Copyright ©2015 Black Sphere Studios

#include <memory>
#include "trex.h"
#include "bss-util/cTrie.h"
#include "parse.h"

using namespace bss_util;

// Punctuation characters without escaping:  !"#$%&'()*+,-./:;<=>?@[\]^`{|}~
#define WHITESPACE " \t\r\n\v\f"
#define PUNCTUATION "!\"#$%&'()*+,\\-./:;<=>?@[\\\\\\]^`{|}~"
static const char* trex_err;
TRex* regex_ID = trex_compile("^[^" PUNCTUATION WHITESPACE "]+", &trex_err);
TRex* regex_N = trex_compile("^[0-9]+(\\.[0-9]+)?([eE]-?[0-9]+)?[^" PUNCTUATION WHITESPACE "]+", &trex_err);
TRex* regex_OP = trex_compile("^[" PUNCTUATION "]+", &trex_err);

extern unsigned char GetType(const char* s, unsigned int len)
{
  static cTrie<unsigned char> types(27, "int8", "int16", "int32", "int64", "uint8", "uint16", "uint32", "uint64", "half", "float", "double", "string", "string16", "string32", "void", "bool",
    "char", "short", "int", "long", "byte", "ushort", "uint", "ulong", "f16", "f32", "f64");
  return (len > 64) ? (unsigned char)-1 : types.Get(s, (unsigned char)len); // no built-in type is longer than 64 characters
}

extern unsigned char GetType(const char* s)
{
  return GetType(s, strlen(s));
}

inline unsigned int strinsert(const char* start, const char* end, cDynArray<cStr, unsigned int, CARRAY_SAFE>& strings, cHash<const char*, unsigned int>& hash)
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
TOKEN parse_inner(const char*& s, cDynArray<cStr, unsigned int, CARRAY_SAFE>& strings, cHash<const char*, unsigned int>& hash)
{
  static cTrie<unsigned char> t(29, "return", "if", "else", "for", "while", "do", "switch", "case", "break", "continue", "pure", "const", "unsafe",
    "foreach", "fn", "template", "type", "assert", "default", "var", "using", "virtual", "inline", "static", "signed", "unsigned", "namespace",
    "class", "enum", "abstract", "contract", "null", "public", "protected", "private", "try", "catch", "finally", "import");
  const char* begin;
  const char* end;
  unsigned char r;
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
      return TOKEN(T_NUMTOKENS, "Malformed numerical constant.", -1); // If we failed, it was malformed.
    s=end;
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
  if(trex_search(regex_ID, s, &begin, &end)) // Is it an identifier or a keyword?
  {
    s=end;
    r=t.Get(begin, end-begin);
    if(r==(unsigned char)-1) // If this happens it isn't a reserved keyword so it's an identifier
      return TOKEN(T_ID, 0, strinsert(begin, end, strings, hash));
    return TOKEN(Tokens(r+1), 0, 0); // Otherwise it was one of our reserved words
  }
  switch(s[0]) // If it wasn't an identifier it was some sort of operator character. Check for our special ones first.
  {
    /*case ';':
    return TOKEN(T_SEMICOLON, s, 1);
    case ':':
    return TOKEN(T_COLON, s, 1);
    case ',':
    return TOKEN(T_COMMA, s, 1);
    case '.':
    return TOKEN(T_DOT, s, 1);
    case '?':
    return TOKEN(T_TERNERY, s, 1);
    //case '@': // Only special when applied to types
    //  return TOKEN(T_FORCEREF, s, 1);
    case '=':
    return TOKEN(T_ASSIGN, s, 1);*/
  case '(':
    return TOKEN(T_LPAREN, s, 1);
  case ')':
    return TOKEN(T_RPAREN, s, 1);
  case '[':
    return TOKEN(T_LBRACKET, s, 1);
  case ']':
    return TOKEN(T_RBRACKET, s, 1);
  case '{':
    return TOKEN(T_LBRACE, s, 1);
  case '}':
    return TOKEN(T_RBRACE, s, 1);
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

extern void Parse(const char* s, cDynArray<TOKEN>& tokens, cDynArray<cStr, unsigned int, CARRAY_SAFE>& strings)
{
  cHash<const char*, unsigned int> hash;
  do { tokens.Add(parse_inner(s, strings, hash)); } while(tokens.Back().token != T_EOF);
}