// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  template[A]
  A[] filter(const A[:] s, const fn[bool](A) f) pure
  {
    A[] r;
    foreach(var x in s)
      if(f(x))
        r += x;
    return r;
  }
  
  template[A]
  A[] quicksort(const A[:] s) pure
  {
    var x = s[0];
    return quicksort(filter(s[1:], fn(y)-> y <= x)) + x + quicksort(filter(s, fn(y)-> y > x));
  }
}