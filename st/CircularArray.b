// Copyright ©2014 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Circular array implementation
  template[T]
  class CircularArray : Iterable[T]
  {
    CircularArray(const CircularArray copy) : CircularArray((const T[:])copy) {}
    CircularArray(CircularArray!! mov) : _length(mov._length), _capacity(mov._capacity), _p(mov._p), _cur(mov._cur)
    { 
      mov._p = null;
      mov._capacity = 0;
      mov._length = 0;
      mov._cur = 0;
    }
    CircularArray(const T[:] copy) : _p(null), _length(0), _capacity(0), _cur(copy._cur)
    {
      Capacity(#copy);
      C.memcpynew[T](T[:](_p, _length), copy);
      _length = copy._length;
    }
    CircularArray(uint n) : _p(null), _capacity(0), _length(0), _cur(-1) { Capacity(n); }
    ~CircularArray() { Clear(); free(_p); }
    
    void Push(const T v)
    {
      _cur = (_cur + 1) % _capacity;
      if(_length < _capacity)
      {
        _p[_cur].T(v);
        ++_length;
      }
      else
        _p[_cur] = v;
    }
    T Pop()
    {
      assert(_length > 0);
      --_length;
      T r = _p[_cur];
      _p[_cur].~T();
      _cur = (_cur - 1) % _capacity;
      return r;
    }
    T PopBack()
    { 
      assert(_length>0);
      uint l = _modindex(--_length);
      T r = _p[l];
      _array[l].~T();
      return r;
    }
    void Discard()
    {
      assert(_length > 0);
      --_length;
      _p[_cur].~T();
      _cur = (_cur - 1) % _capacity;
    }
    void DiscardBack()
    {
      assert(_length>0);
      uint l = _modindex(--_length);
      _array[l].~T();
    }
    property uint Capacity() const { return _capacity; }
    property uint Length() const { return _length; }
    property uint Capacity(uint capacity)
    {
      if(capacity < _capacity)
      {
        Clear(); // Getting the right destructors here is complicated and trying to preserve the array when it's shrinking is meaningless.
        C.realloc[T](T[:](_p, _length), capacity);
      }
      else if(capacity > _capacity)
      {
        T* n = AT_::_getalloc(capacity);
        if(_cur - _length >= -1) // If true the chunk is contiguous
          BASE::_copymove(n + _cur - _length + 1, _array + _cur - _length + 1, _length);
        else
        {
          CType i = _modindex(_length - 1);
          BASE::_copymove(n + bssmod<CType>(_cur - _length + 1, capacity), _array + i, _capacity - i);
          BASE::_copymove(n, _array, _cur + 1);
        }
        AT_::_free(_array);
        _array = n;
      }
      return _capacity = capacity;
    }
    void Clear()
    {
      if(_length == _capacity) // Dump the whole thing
        for(uint i = 0; i < _length; ++i)
          _p[i].~T();
      else if(_cur - _length >= -1) // The current used chunk is contiguous
        for(uint i = 1; i <= _length; ++i)
          _p[_cur - _length + i].~T();
      else // We have two seperate chunks that must be dealt with
      {
        uint i = _modindex(_length - 1);
        BASE::_setlength(_array + i, _capacity - i, 0);
        BASE::_setlength(_array, _cur + 1, 0); // We can only have two seperate chunks if it crosses over the 0 mark at some point, so this always starts at 0
      }

      _length=0;
      _cur=-1;
    }
    
    
    T$ op[](int index) { return _p[_modindex(index < 0 ? _length - index : index)]; } // an index of 0 is the most recent item pushed into the circular array.
    const T op[](int index) const { return _p[_modindex(index < 0 ? _length - index : index)]; }
    uint op#() const { return _length; }
    __Iter[T] Iter() { return __Iter(_a, _cur, _len) }
    __Iter[const T] Iter() const { return __Iter(_a, _cur, _len) }
    
    template[U]
    class __Iter : Iterator[U]
    {
      __Iter(unsafe U@ p, uint len, int cur, int len) : _p(p), _len(len), _cur(cur), i(0)
      U@ Next() { return (i >= _len) ? null : _p[(_cur-i++)%_len] }
      
    private:
      unsafe U@ _p;
      uint _len;
      int _cur;
      int i;
    }
    
  private:
    int _modindex(int index) { return (_cur-index)%_length; }
    
    unsafe T@ _p;
    uint _length;
    uint _capacity;
    int _cur;
  };
}