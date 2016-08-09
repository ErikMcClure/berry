// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Implements an array-based Stack
  template[T]
  class Stack
  {
    Stack(uint n=0) : _a(n) {}
    void Push(const T v) { _a.Add(v); }
    T Peek() const { return _a[-1]; }
    T@ Peek() { return _a[-1]; }
    T Pop() { T r = _a[-1]; _a.RemoveLast(); return r; }
    void Discard() { _a.RemoveLast(); }
    void Clear() { _a.Clear(); }
    property uint Length(uint length) { return _a.Length = length; }
    property uint Length() const { return _a.Length; }
    property uint Capacity(uint capacity) { return _a.Capacity = capacity; }
    property uint Capacity() const { return _a.Capacity; }
    
    uint op#() const { return #a; }
    T@ op[](uint i) { return a[i]; }
    const T op[](uint i) const { return _a[i] }
    Slice[T] op[:](uint i,uint n) const { return _a[i:n]; }
    T[:] op() { return (T[:])_a; }
    const T[:] op() const { return (const T[:])_a; }
    Stack$ op<:(const T v) { Push(v); return this; }
    Stack$ op:>(T@ v) { v = _a[-1]; _a.RemoveLast(); return this; }
    T op~() const { return Peek(); }
    
  private:
    T[] _a;
  }
}  
