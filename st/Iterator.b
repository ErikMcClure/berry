// Copyright ©2016 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE

namespace Berry {
  // Defines the requirements for iterables and iterators
  template[T]
  trait Iterator
  {
    T@ Next();
  }
  
  template[T]
  trait Iterable
  {
    Iterator[T] Iter();
  }
  
  template[A, B]
  B[#a] map(const Iterable[A] a, fn[B](const A) f) : b
  {
    uint i = 0;
    for(A x in a)
      b[i++] = fn(x);
    return b;
  }
  
  template[A, void]
  Iterable[A]@ map(Iterable[A]@ a, fn[void](A@) f)
  {
    for(A@ x in a)
      fn(x);
    return a;
  }
  
  template[A, B]
  B[] map(const Iterable[A] a, fn[Iterable[B]](const A) f) : b
  {
    for(A x in a)
      b += fn(x);
  }
  
  template[A]
  A@[] filter(const Iterable[A] a, fn[bool](const A) f) : v
  {
    for(A item in s) 
      if(f(item))
        v += @s;
    return l;
  }
  
  template[A!]
  A[] filter(const Iterable[A] a, fn[bool](const A) f) : v
  {
    for(A item in s) 
      if(f(item))
        v += s;
    return l;
  }
  
  //template[A] // This uses inferred template arguments
  //A[fold(a, 0, fn(n,x) -> n + #x)] reduce(const I a) : b
  template[A, I:Iterable[V], V:Iterable[A]] // This is with explicit template arguments
  A[fold[I, uint](a, 0, fn[uint](uint n, const V x) { return n + #x; })] reduce(const I a) : b
  {
    uint i = 0;
    for(var item in a)
      for(var subitem in item)
        b[i++] = subitem;
  }
  
  template[A]
  bool any(const Iterable[A] a, fn[bool](const A) f)
  {
    for(A x in a)
      if(f(x))
        return true;
    return false;
  }
  
  template[A]
  bool all(const Iterable[A] a, fn[bool](const A) f)
  {
    for(A x in a)
      if(!f(x))
        return false;
    return true;
  }
  
  template[A, B]
  B fold(const Iterable[A] a, B init, fn[B](const B, const A) f)
  {
    for(A x in a)
      init = f(init, x);
    return init;
  }
  
  template[A, B]
  B aggregate(B init, fn[B](const B, const A) f, A... args)
  {
    for(A x in args)
      init = f(init, x);
    return init;
  }
}  
