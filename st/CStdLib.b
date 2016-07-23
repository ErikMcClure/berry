// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry.CStdLib {
  const byte[:] memchr(const byte[:] str, byte c) { return (unsafe byte[#str])memchr(str, c, #str) }
  int memcmp(const byte[:] l, const byte[:] r) { return memcmp(l, r, min(#l,#r)) }
  void memcpy(byte[:] l, const byte[:] r) { memcpy(l, r, min(#l, #r)) }
  void memmove(byte[:] l, const byte[:] r) { memmove(l, r, min(#l, #r)) }
  void memset(byte[:] l, byte c) { memset(l, c, #l) }
  byte[:] realloc(p_uint n, byte[:] p) { return (unsafe byte[n])realloc(n, p) }
  byte[:] malloc(p_uint n) { return (unsafe byte[n])malloc(n) }
  void free(byte[:] p) { free(p) }
  
  namespace Math {
    int abs(int x) { return abs(x) }
    int div(int x) { return div(x) }
    long abs(long x) { return labs(x) }
    long div(long x) { return ldiv(x) }
  }
  
  namespace String {
    double atof(const string str) { return atof(str) }
    int atoi(const string str) { return atoi(str) }
    long atol(const string str) { return atol(str) }
    int strcmp(const string l, const string r) { return strcmp(l, r) }
    int stricmp(const string l, const string r) { return stricmp(l, r) }
  }
}