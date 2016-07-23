// Copyright ©2016 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Defines the requirements for iterables and iterators
  template[T]
  trait Iterator
  {
    T@ Next()
  }
  
  template[T]
  trait Iterable
  {
    Iterator[T] Iter()
  }
  
  /*template[T, I]
  void foreach[Iterable[I],I](T src, void(I) f)
  {
    Iterator[i] iter = src.Iter()
    I item
    
    while((item = iter.Next()) != null)
      f(item)
  }

  template[T, I]
  void foreach[T[:], I](T[:] slice, void(I) f)
  {
    for(int i = 0; i < #slice; ++i)
      f(slice[i])
  }*/
  
  template[A, B]
  Iterable[B] map(const Iterable[A] s, fn[B](const A) f)
  {
    B[#s] b
    p_uint i = 0;
    for(A x in s)
      b[i++] = fn(x)
    return b
  }
  
  template[A, B]
  Iterable[A] mapmany(const Iterable[A] s, fn[Iterable[B]](const A) f)
  {
    B[] b
    for(A x in s)
      b += fn(x)
    return b
  })
  
  template[A]
  Iterable[A] filter(const Iterable[A] s, fn[bool](const A) f)
  {
    A[] l
    for(A item in s) 
      if(f(item))
        l += s
    return l
  }
  
  template[A]
  Iterable[A] concat(const Iterable[Iterable[A]] s)
  {
    var l = foldl(s, 0, fn[var](var x) { return #x })
    A[l] list;
    p_uint i = 0;
    for(var item in s)
      for(var subitem in s)
        list[i++] = subitem;
    return list;
  }
  
  template[A, T:Iterable[A]]
  bool any(const Iterable[A] s, fn[bool](const A)@ f = null)
  {
    if(f == null)
      return #s > 0
    for(A x in s)
      if(f(x))
        return true
    return false
  }
  
  template[A]
  bool all(const Iterable[A] s, fn[bool](const A) f)
  {
    for(A x in s)
      if(!f(x))
        return false
    return true
  }
  
  template[A]
  A fold(const Iterable[A] s, A init, fn[A](const A, const A)@ f)
  {
    for(A x in s)
      init = f(init, x);
    return init;
  }
}  
