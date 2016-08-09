// Copyright ©2016 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Implements a dynamic array
  template[T, Alloc:StaticAllocator = DefaultAllocator]
  class DynArray : Iterable[T] {
    DynArray(const DynArray copy) : DynArray((const T[:])copy) {}
    DynArray(DynArray!! mov) : _length(mov._length), _capacity(mov._capacity), _p(mov._p)
    { 
      mov._p = null;
      mov._capacity = 0;
      mov._length = 0;
    }
    DynArray(const T[:] copy) : _p(null), _length(0), _capacity(0)
    {
      Capacity(#copy);
      C.memcpynew[T](T[:](_p, _length), copy);
      _length = copy._length;
    }
    DynArray(uint n) : _p(null), _capacity(0), _length(0) { Capacity(n); }
    ~DynArray() { C.realloc[T](T[:](_p, _length), 0); }
    uint Add(const T t)
    {
      _checksize();
      _p[_length].T(t);
      return _length++;
    }
    void Remove(uint index)
    { 
      assert(index < _length);
      _remove[T](index);
    }
    void RemoveLast() { assert(_length > 0); _p[--_length].~T(); }
    void Insert(const T t, uint index=0)
    { 
      assert(index <= _length);
      _checksize();
      if(index < _length) // performing this check makes it impossible to insert something at index 0 when length is 0.
        _insert[T](t, index);
      else
        Add(t);
    }
    bool Empty() const { return _length == 0; }
    void Clear() { Length(0); }
    DynArray$ Reverse() { for(uint i = 0; i < (_length>>1); ++i) _p[i] <> _p[_length-1-i]; return this; }
    SliceIterator[T] Iter() { return SliceIterator[T](_p, _p + _length); }
    SliceIterator[const T] Iter() const { return SliceIterator[const T](_p, _p + _length); }
    property uint Length(uint length)
    {
      if(length < _length)
        for(uint i = length; i < _length; ++i)
          _p[i].~T();
      else if(length > _capacity)
        Capacity(length);
      return _length = length;
    }
    property uint Length() const { return _length; }
    property uint Capacity(uint capacity) const
    { 
      if(capacity > _capacity)
        _p = (unsafe T@)C.realloc[T](Slice[T](_p, _length), capacity);
      return _capacity = capacity;
    }
    property uint Capacity() const { return _capacity; }
    
    uint op#() const { return _length; }
    T@ op[](uint i) { assert(i < _length && i >= -_length); return _p[i<0 ? _length +i : i]; }
    const T op[](uint i) const { assert(i < _length && i >= -_length); return _p[i<0 ? _length+i : i]; }
    Slice[T] op[:](uint i,uint n) const { return Slice[T](_p+i,n); }
    DynArray op|>(uint i) const { return DynArray(this)|>=i; } // "rotate" right by i (or permute)
    DynArray op<|(uint i) const { return DynArray(this)<|=i; } // rotate left by i
    DynArray$ op|>=(uint k) {
      this[0:n].Reverse();
      this[0:k].Reverse();
      this[k:n].Reverse();
      return this;
    }
    DynArray$ op<|=(uint i) { return this.op|>=(_length-i); }
    T[:] op() { return Slice[T](_p, _length); }
    const T[:] op() const { return Slice[const T](_p, _length); 
    bool op==(const DynArray r) const { return _slicecmp[T](T[:](_p, _length), r); }
    bool op!=(const DynArray r) const { return !this.op==(r); }
    bool op==(const T[:] r) const { return _slicecmp[T](T[:](_p, _length), r); }
    bool op!=(const T[:] r) const { return !this.op==(r); }
    DynArray$ op=(const DynArray copy) { return op=((const T[:])copy); }
    DynArray$ op=(DynArray!! mov)
    {
      C.realloc[T](T[:](_p, _length), 0);
      _length = mov._length;
      _capacity = mov._capacity;
      _p = mov._p;
      mov._p = null;
      mov._capacity = 0;
      mov._length = 0;
      return this;
    }
    DynArray$ op=(const T[:] copy)
    {
      Length(0);
      if(#copy > _capacity)
        Capacity(#copy); // _length must be zero when this is called so realloc doesn't destroy anything
      _length = #copy; 
      C.memcpynew[T](T[:](_p, _length), copy);
      return this;
    }
    DynArray$ op +=(const T[:] add)
    {
      Capacity(_length + #add);
      C.memcpynew[T](T[:](_p + _length, #add), add);
      return this;
    }
    const DynArray op+(const T[:] add) const { DynArray r(this); return (r+=add); }

  private:
    template[U:__trivial_move]
    void _remove(uint index)
    {
      _p[index].~U();
      FFI.memmove(_p + index, _p + index + 1, #U*(_length - index - 1));
      --_length;
    }
    template[U]
    void _remove(uint index)
    {
      --_length;
      for(;index < _length; ++index)
        _p[index] = _p[index + 1];
      _p[_length].~U();
    }
    template[U:__trivial_move]
    void _insert(const U t, uint index)
    {
      assert(index >= 0 && _length >= index);
      FFI.memmove(_p + index + 1, _p + index, #U*(_length - index));
      _p[index].U(t);
      ++_length;
    }
    template[U]
    void _insert(const U t, uint index)
    {
      assert(_length > 0);
      _p[_length].U(_p[_length - 1]);
      for(uint i = _length - 1; i > index; ++i)
        _p[i] = _p[i - 1]
      _p[index] = t;
      ++_length;
    }
    void _checksize()
    {
      if(_length>=_capacity)
        Capacity(FBNext(_capacity));
      assert(_length<_capacity);
    }
    
    uint _length;
    uint _capacity;
    unsafe T@ _p;
  }
}  
