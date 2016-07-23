// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Implements an array-based Stack
  template[T]
  class Stack {
    Stack(const Stack r) : _a(r._a), _len(r._len) {}
    Stack(p_uint n=0) : _a(n), _len(0) {}
    void Push(const T v) { if(++_len>#_a) _a.Resize(FBNext(#_a)); assert(_len-1<#_a); _a[_len-1]=v; }
    T Peek() const { return _a[_len-1]; }
    T@ Peek() { return _a[_len-1]; }
    T Pop() { return _a[--_len]; }
    void Discard() { --_len; }
    p_uint Length() const { return _len; }
    p_uint Capacity() const { return #_a; }
    
    T[:] op() { return _a }
    const T[:] op() const { return _a }
    Stack@ op<<(const T v) { Push(v); return this; }
    Stack@ op>>(T@ v) { v=Pop(); return this; }
    T op$() const { return Peek(); }
    Stack@ op=(const Stack r) { Array.op=(r); _len=r._len; return this; }
    p_uint op#() const { return _len; }
    
  protected:
    p_uint _len;
    T[] _a; // gets turned into a resizable array.
  }
}  
