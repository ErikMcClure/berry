// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  type p_int = (#byte@ == #int) ? int : long
  type p_uint = (#byte@ == #uint) ? uint : ulong
  
  template[T]
  T min(T l, T r) { return l<r?l:r; }
  template[T]
  T max(T l, T r) { return l>r?l:r; }
  
  template[T]
  T FBNext(T x)
  {
    return x + 1 + (x>>1) + (x>>3) - (x>>7);
  }
  
  template[T = byte]
  void memcpy(T[:] l, const T[:] r)
  {
    if(__HasAssignment(T))
      for(p_uint i = 0; i < min(#l,#r); ++i)
        l[i] = r[i];
    else
      memcpy[byte]((unsafe byte[:])a, (unsafe byte[:])b);
  }
  void memcpy[byte](byte[:] l, const byte[:] r)
  {
    CStdLib.memcpy(l, r); //actual c call
  }
  template[T = byte]
  void memmove(T[:] l, const T[:] r)
  {
    if(__HasAssignment(T))
      for(p_uint i = 0; i < cnt; ++i)
        a[i] = b[i];
    else
      memmove[byte]((unsafe byte[:])a, (unsafe byte[:])b);
  }
  void memmove[byte](byte[:] l, const byte[:] r)
  {
    CStdLib.memmove(l, r);
  }
  template[T]
  T[:] __compiler_new(T[:] p)
  {
    if(__HasConstructor(T))
      for(p_uint i = 0; i < #p; ++i)
        p[i].T();
    return p;
  }
  template[T]
  void __compiler_delete(T[:] p)
  {
    if(__HasConstructor(T))
      for(p_uint i = 0; i < #p; ++i)
        p[i].~T();
  }
}