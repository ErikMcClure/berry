// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {  
  template[A:Comparable]
  pure A[] quicksort(const A[:] s)
  {
    var x = s[0];
    return quicksort(filter(s[1:], fn(y)-> y <= x)) + x + quicksort(filter(s, fn(y)-> y > x));
  }
  
  template[T:Comparable]
  T min(T l, T r) { return l<r?l:r; }
  template[T:Comparable]
  T max(T l, T r) { return l>r?l:r; }
  
  template[T:Integral]
  T FBNext(T x)
  {
    return x + 1 + (x>>1) + (x>>3) - (x>>7);
  }
}