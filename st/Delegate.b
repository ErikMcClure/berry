// Copyright ©2014 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  template[R = void, Args...]
  class Delegate
  {
    Delegate() : _src(null), _f(null) { }
    Delegate(const Delegate copy) : _src(copy._src), _f(copy._f) { }
    R op()(Args args) const { return _f(_src, args) }
    bool IsEmpty() const { return _src==null || _f==null }
    
    template[D, fn.D[R](Args) FN]
    Delegate From(D@ src) { return Delegate((unsafe void@)src, _stub[D,FN]) }
    
  protected:
    template[D, fn.D[R](Args) FN]
    R _stub(unsafe void@ s, Args a) { return ((unsafe D@)s).$FN(a) }
    Delegate(unsafe void@ src, fn[R](unsafe void@, Args) f) : _src(src), _f(f) { }
    
    unsafe void@ _src
    fn[R](unsafe void@, Args) _f
  }
}