// Copyright ©2016 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE

namespace Berry { 
  // Implements a generic algebriac type
  template[R, Args...]
  class Variant
  {
    Variant() : _tag(-1) {}
    Variant(const Variant copy) : _tag(copy._tag) {}
    Variant(Variant!! mov) : _tag(mov._tag) {}
    template[T]
    Variant(const T copy) {}
    template[T]
    Variant(T!! mov) {}
    
  private:
    int _tag;
    [Align(aggregate(0, op+, Args.Alignment...))]
    byte _store[aggregate(0, op+, #Args...];
  }
}