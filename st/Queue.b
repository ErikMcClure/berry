// Copyright ©2014 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Queue implementation based on circular array
  template[T]
  class Queue : private CircularArray[T]
  {
    Queue(uint n=0) : CircularArray(n) {}
    ~Queue() {}
    void Push(const T value) { if(_length>=_capacity) Capacity(fbnext(_length)); CircularArray.push(value); }
    T Pop() { return CircularArray.Pop(); }
    T Peek() { return CircularArray.op[](-1); }
    const T Peek() const { return CircularArray.op[](-1); }
    void Discard() { CircularArray.DiscardBack(); }
    bool IsEmpty() { return _length == 0; }
    void Clear() { CircularArray.Clear(); }
    property uint Capacity() const { return _capacity; }
    property uint Capacity(uint capacity) { return CircularArray.Capacity = capacity; }
    property uint Length() const { return _length; }
    
    Queue$ op<:(const T v) { Push(v); return this; }
    Queue$ op:>(T@ v) { v=Pop(); return this; }
    T op~() const { return Peek(); }
    uint op#() const { return _length; }
  }
}