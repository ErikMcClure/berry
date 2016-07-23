// Copyright ©2014 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  template[T]
  trait ChannelT
  {
    void Push(const T push);
    bool Pull(T$ value);
    
    uint op#() const;
    static bool op:>(const T push, ChannelT@ right); // a :> c
    static bool op<:(T$ pull, ChannelT@ right); // a <: c
    static bool op:>(ChannelT@ left, T$ pull); // c :> a
    static bool op<:(ChannelT@ left, const T push); // c <: a
    ChannelT op=(ChannelT@ move);
  }
  
  template[T]
  class Channel : CChannel[T] // Standard value
  {
    
  }
  template[T@]
  class Channel : CChannel[T@] // A reference value that has been allocated elsewhere
  {

  }
  template[T[:]]
  class Channel : CChannel[T[:]] // A dynamically sized slice channel (e.g. strings).
  {

  }
}