// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry.IO {
  enum SeekOrigin : byte
  {
    Begin = 0,
    Current = 1,
    End = 2,
  }
    
  template[T = byte]
  class Stream
  {
    abstract bool CanRead() const
    abstract bool CanWrite()
    abstract p_uint Read(T[:] buffer)
    abstract p_uint Write(const T[:] buffer)
    abstract p_uint WriteLine(const T[:] buffer)
    abstract void Flush()
    abstract long Seek(long offset, SeekOrigin origin)
    abstract long Position()
  }
  
  Stream StdOut = magic
  Stream StdIn = magic
  Stream StdErr = magic
}