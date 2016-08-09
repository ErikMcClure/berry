// Copyright ©2016 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Iterator for any standard array
  template[T]
  class SliceIterator : Iterator[T]
  {
    SliceIterator(unsafe T@! _p, unsafe T@! _end) : p(_p), end(_end) { }
    T@ Next() { return p==end ? null : p++ }
  
    private:
    unsafe T@! p;
    unsafe T@! end;
  }

  // Represents an Array Slice
  template[T]
  class Slice : Iterable[T]
  {    
    Slice(unsafe T@ p, uint n) : _p(p), _n(n) {}
    Slice(const Slice r) : _p(r._p), _s(r._n) {}
    Slice$ Reverse() { for(uint i = 0; i < (_n>>1); ++i) _p[i] <> _p[_n-1-i]; return this; }
    SliceIterator[T] Iter() { return SliceIterator[T](_p, _p+_n); }
    SliceIterator[const T] Iter() const { return SliceIterator[const T](_p, _p+_n); }
    property uint Length() const { return _n; }
    bool Empty() const { return _p == null || _n == 0; }
    
    Slice$ op=(const Slice r) { _p=r._p; _n=r._n; return this; }
    T@ op[](uint i) { assert(i < _n && i >= -_n); return _p[i<0 ? _n+i : i]; }
    const T op[](uint i) const { assert(i < _n && i >= -_n); return _p[i<0 ? _n+i : i]; }
    Slice op[:](uint i,uint n) const { return Slice(_p+i,n); }
    uint op#() const { return _n; }
    DynArray[T] op|>(uint i) const { return DynArray[T](this)|>=i; } // "rotate" right by i (or permute)
    DynArray[T] op<|(uint i) const { return DynArray[T](this)<|=i; } // rotate left by i
    Slice$ op|>=(uint k) {
      this[0:n].Reverse();
      this[0:k].Reverse();
      this[k:n].Reverse();
      return this;
    }
    Slice$ op<|=(uint i) { return this.op|>=(_n-i); }
    bool op==(const Slice r) const { return _slicecmp[T](this, r); }
    bool op!=(const Slice r) const { return !this.op==(r); }
    DynArray op+(Slice r) const { DynArray a(_n+r._n); memcpy[T](a._p,_p,_n); memcpy[T](a._p+_n,r._p,r._n); return a; }
    const unsafe T@! op() const { return _p; }
    unsafe T@! op() { return _p; }
    unsafe void@ op() { return (unsafe void@)_p; }
    
    static Slice[T] Empty = Slice[T](null, 0);
    
  private: 
    unsafe T@! _p;
    uint _n;
  }
}