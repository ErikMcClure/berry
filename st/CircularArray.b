// Copyright ©2014 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Circular array implementation
  template[T]
  class CircularArray : Iterable[T]
  {
    CircularArray(const CircularArray r) : _a(r._a), _cur(r._cur), _len(r._len) {}
    CircularArray(CircularArray$ r) : _a(r._a), _cur(r._cur), _len(r._len) {}
    CircularArray(p_uint n) : _a(n), _cur(-1), _len(0) {}
    void Push(const T v) { _a[_cur=((_cur+1)%#_a)]=v; _len+=(_len<#_a); }
    T! PopFront() { assert(_len>0); --_len; var prev=_cur; _cur=(_cur-1)%%#_a; return _a[prev]; }
    T! Pop() { assert(_len>0); return _a[_modindex(--_len)]; }
    T$ Front() { return _a[_cur]; }
    const T Front() const { return _a[_cur]; }
    T$ Back() { return _a[_modindex(_len-1)]; }
    const T Back() const { return _a[_modindex(_len-1)]; }
    p_uint Capacity() const { return #_a; }
    p_uint Length() const { return _len; }
    void Resize(p_uint n) {
      p_int sz=#_a;
      _a.Resize(n);
      p_int c=_cur+1;
      if(sz<n)
        _a.MoveChunk(c,sz-c,#_a-sz);
    }
    T$ op[](p_int index) { return _a[_modindex(index)]; } // an index of 0 is the most recent item pushed into the circular array.
    const T op[](p_int index) const { return _a[_modindex(index)]; }
    CircularArray op=(const CircularArray r) { _a=r._a; _cur=r._cur; _len=r._len; return *this; }
    CircularArray op=(CircularArray$ r) { _a=r._a; _cur=r._cur; _len=r._len; r._len=0; r._cur=0; return *this; }
    p_uint op#() const { return _len; }
    __Iter Iter() { return __Iter(_a, _cur, _len) }
    
    class __Iter : Iterator[T]
    {
      __Iter(T[:] a, p_int cur, p_int len) : _a(a), _cur(cur), i(0)
      T@ Next() { return (i == #_a) ? null : _a[(_cur-i++)%%#_a] }
      
    private:
      T[:] _a;
      p_int _cur;
      p_int i;
    }
    
  protected:
    p_int _modindex(p_int index) { return (_cur-index)%%#_a; }
    
    T[] _a;
    p_int _cur;
    p_uint _len;
  };
}