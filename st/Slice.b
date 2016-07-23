// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {  
  // Represents an Array Slice
  template[T]
  class Slice : Iterable[T]
  {    
    Slice(unsafe T@ p, uint n) : _p(p), _n(n) {}
    Slice(Slice r) : _p(r._p), _s(r._n) {}
    
    Slice op=(const Slice$ r) { _p=r._p; _n=r._n; return this; }
    T@ op[](uint i) { return _p[i]; }
    const T op[](uint i) const { return _p[i]; }
    Slice op[:](uint i,uint n) const { return Slice(_p+i,n); }
    uint op#() const { return _n; }
    Array[T] op|>(uint i) const { return Array[T](this)|>=i; } // "rotate" right by i (or permute)
    Array[T] op<|(uint i) const { return Array[T](this)<|=i; } // rotate left by i
    Slice op|>=(uint k) {
      this[0:n].reverse();
      this[0:k].reverse();
      this[k:n].reverse();
      return this;
    }
    Slice op<|=(uint i) { return this.op|>=(_n-i); }
    bool op==(Slice r) const { return (_n != r._n) ? false : !memcmp[T](_p,r._p,_n); }
    bool op!=(Slice r) const { return !this.op==(r); }
    Slice reverse() { for(uint i = 0; i < (_n>>1); ++i) _p[i] <> _p[_n-1-i]; return this; }
    Array op+(Slice r) const { Array a(_n+r._n); memcpy[T](a._p,_p,_n); memcpy[T](a._p+_n,r._p,r._n); return a; }
    SliceIterator[T] Iter() { return SliceIterator[T](_p, _p+_n); }
    
    static Slice[T] Empty = Slice[T](null, 0);
    
  protected: 
    unsafe T@ _p;
    uint _n;
    
    template[T]
    class SliceIterator : Iterator[T]
    {
      SliceIterator(unsafe T@ _p, unsafe T@ _end) : p(_p), end(_end) { }
      T@ Next() { return p==end ? null : p++ }
    
      private:
      unsafe T@ p;
      unsafe T@ end;
    }
  }
}