// Copyright ©2016 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry.C {
  const byte[:] memchr(const byte[:] str, byte c)
  { 
    unsafe const void@ p = FFI.memchr((unsafe const void@)str, c, #str);
    return byte[:]((unsafe const byte@)p, ((unsafe const void@)str + #str) - p);
  }
  int memcmp(const byte[:] l, const byte[:] r) { return FFI.memcmp((unsafe const void@)l, (unsafe const void@)r, min(#l,#r)); }
  void memcpy(byte[:] l, const byte[:] r) { FFI.memcpy((unsafe const void@)l, (unsafe const void@)r, min(#l, #r)); }
  void memmove(byte[:] l, const byte[:] r) { FFI.memmove((unsafe const void@)l, (unsafe const void@)r, min(#l, #r)); }
  void memset(byte[:] l, byte c) { FFI.memset((unsafe const void@)l, c, #l); }
  void free(unsafe void@ p) { FFI.free(p); }
  
  template[T:__trivial_copy]
  void memcpynew(T[:] dest, T[:] src)
  {
    FFI.memcpy((unsafe const void@)dest, (unsafe const void@)dest, min(#dest, #src)); 
  }
  template[T]
  void memcpynew(T[:] dest, T[:] src)
  {
    for(uint i = 0; i < min(#dest, #src); ++i)
      dest[i].T(src[i])
  }
  
  template[T]
  T[:] malloc(uint n) { return T[:]((unsafe T@)FFI.malloc(n * #T), n); }
  template[T]
  T[:] realloc(T[:] cur, uint n)
  {
    if((unsafe T@)cur == null) // This CANNOT use Empty(), because we could get a valid slice with a length of zero we need to free.
      return n == 0 ? T[:](null, 0) : malloc[T](n);
    
    if(n == 0) // if n is zero this is equivilent to free, but we also have to call destructors if necessary
    {
      for(uint i = 0; i < #cur; ++i)
        cur[i].~T();
      free((unsafe void@)cur);
      return T[:](null, 0);
    }
    
    unsafe void@ p = __HEAP_REALLOC((unsafe void@)cur, n);
    
    if(p == (unsafe void@)cur) // If the block didn't change no memory moved so we're done.
      return T[:]((unsafe T@)p, n);
    
    // Otherwise a new block was allocated, so we need to construct it, then destruct and free the old one
    var new = T[:]((unsafe T@)p, n); 
    memcpynew[T](new, cur);
    
    for(uint i = 0; i < #cur; ++i)
      cur[i].~T()
    free((unsafe void@)cur);
    return new;
  }
  
  template[T:__byte_comparable] // If anything has a float in it or some other noncomparable object, this won't work (because NaN != NaN)
  bool _slicecmp(const T[:] l, const T[:] r) { return #l == #r ? !memcmp((unsafe const void@)l, (unsafe const void@)r) : false; }
  template[T]
  bool _slicecmp(const T[:] l, const T[:] r)
  {
    if(#l != #r)
      return false;
    for(uint i = 0; i < #l; ++i)
      if(l[i] != r[i])
        return false;
    return true;
  }
  
  namespace Math {
    i32 abs(i32 x) { return FFI.abs(x) }
    i32 div(i32 x) { return FFI.div(x) }
    i64 abs(i64 x) { return FFI.labs(x) }
    i64 div(i64 x) { return FFI.ldiv(x) }
  }
  
  namespace String {
    double atof(const string str) { return atof(str) }
    i32 atoi(const string str) { return atoi(str) }
    i64 atol(const string str) { return atol(str) }
    int strcmp(const string l, const string r) { return strcmp(l, r) }
    int stricmp(const string l, const string r) { return stricmp(l, r) }
  }
}