// Copyright ©2014 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Queue implementation based on circular array
  template[T]
  class Queue : protected CircularArray[T]
  {
    Queue(const Queue r) : CircularArray(r) {}
    Queue(Queue$ r) : CircularArray(r) {}
    Queue(p_uint init=0) : CircularArray(init) {}
    ~Queue() {}
    void Push(const T value) { if(_len>=#_a) resize(fbnext(_len)); CircularArray.push(value); }
    T Pop() { return CircularArray.Pop(); }
    T Peek() { return CircularArray.Back(); }
    const T Peek() const { return CircularArray.Back(); }
    void Discard() { --_len; }
    bool IsEmpty() { return !_len; }
    void Clear() { CircularArray.Clear(); }
    p_uint Capacity() const { return CircularArray.Capacity(); }
    p_uint Length() const { return _len; }

    Queue$ op<<(const T v) { push(v); return this; }
    Queue$ op>>(T@ v) { v=pop(); return this; }
    T op~() const { return peek(); }
    Queue$ op=(const Queue r) { CircularArray.op=(r); return this; }
    Queue$ op=(Queue$ r) { CircularArray.op=(r); return this; }
    p_uint op#() const { return _len; }
  }
}