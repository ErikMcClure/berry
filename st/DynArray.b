// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Implements a dynamic array
  template[T, Alloc:StaticAllocator = DefaultAllocator]
  class DynArray : Slice[T] {
    DynArray(const T[:] copy) : Slice(copy) {}
    DynArray(const DynArray copy) : DynArray((T[:])copy) {}
    uint Add(const T t) { _checksize(); _array[_length]=t; return _length++; }
    void Remove(uint index) { AT_::RemoveInternal(index); --_length; }
    void RemoveLast() { --_length; }
    void Insert(const T t, uint index=0) { _checksize(); AT_::_pushback(index, (_length++)-index, t); }
    bool Empty() const { return !_length; }
    void Clear() { _length=0; }
    void SetLength(uint length) { if(length>_size) _array.Resize(length); _length=length; }
    uint Length() const { return _length; }
    uint Capacity() const { return _size; }
    T$ Front() { return _array[0]; }
    T$ Back() { return _array[_length-1]; }
    
    uint op#() const { return _len; }
    T[:] op() { return _array[0:_length]; }
    const T[:] op() const { return _array[0:_length]; }
    inline DynArray& operator=(const T[:] copy) { _array = copy; _length=#_array; return *this; }
    inline DynArray& operator=(const DynArray copy) { _array = copy; _length=#_array; return *this; } // included for generated move semantics
    inline DynArray& operator +=(const T[:] add) { _array.Resize(_length); _array += copy; _length+=#add; return *this; }
    inline const DynArray operator +(const T[:] add) const { DynArray r(this); return (r+=add); }

  protected:
    void _checksize()
    {
      if(_length>=_size) _array.Resize(FBNext(_size));
      assert(_length<_size);
    }
  }
}  
