// Copyright ©2014 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Fixed-size array that owns its memory.
  template[T, A:StaticAllocator = DefaultAllocator]
  class Array : Slice[T]
  {
    Array(const Array r) : Array((T[:])r) {}
    Array(Array$ r) : Slice(r._p, r._n) { r._p=0; r._n=0; }
    Array(const T[:] r) : Array(#r) { memcpy[T](_p,r._p,_n); }
    Array(p_uint n=0) { this = A.Alloc(n); __compiler_new[T](_p, _n); }
    ~Array()
    { 
      if(_p)
        A.Dealloc(_p);
      __compiler_delete[T](_p, _n);
    }
    
    Array op=(const T[:] r) { ~Array(); Array(r); return this; }
    Array op=(Array$ r) { ~Array(); Array(r); return this; }
  }
}