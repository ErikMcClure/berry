// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

using Berry.CStdLib

namespace Berry {
  template[T]
  trait StaticAllocator
  {
    static T[:] Alloc(uint n, T[:] p)
    static void Dealloc(T[:] p)
  }
  
  template[T]
  trait Allocator
  {
    T[:] Alloc(uint n, T[:] p)
    void Dealloc(T[:] p)
  }
  
  template[T, A : StaticAllocator[T]]
  class UseAllocator
  {
    UseAllocator(A@ alloc) { }
    T[:] Alloc(uint n, T[:] p = T[:].Empty) { A.Alloc(n, p) }
    void Dealloc(T[:] p) { A.Dealloc(p) }
  }
  
  template[T, A : Allocator[T]]
  class UseAllocator
  {
    UseAllocator(A@ alloc) : _alloc((alloc == null) ? A() : alloc) { }
    T[:] Alloc(uint n, T[:] p = T[:].Empty) { _alloc.Alloc(n, p) }
    void Dealloc(T[:] p) { _alloc.Dealloc(p) }
  
  protected:
    A@ _alloc
  }
  
  template[T]
  class DefaultAllocator : StaticAllocator[T]
  {
    static T[:] Alloc(uint n, T[:] p = T[:].Empty) { return realloc(n*#T, (unsafe byte[:])p) }
    static void Dealloc(T[:] p) { free((unsafe byte[:])p) }
  }
  
  class __FixedAllocator
  {
    class Node
    {
      uint size
      Node@ next
    }
    
  public:
    __FixedAllocator(uint sz, uint init=8) : _freelist(null), _root(null), _sz(sz)
    {
      assert(sz >= #uint);
      _allocchunk(init * _sz);
    }
    ~__FixedAllocator()
    {
      Node@ hold=_root;
      while((_root=hold)!=null)
      {
        hold=_root.next;
        free(_root);
      }
    }
    byte[:] Alloc(uint num) 
    {
      assert(num==1);
      if(_freelist == null) _allocchunk(FBNext(_root.size/_sz)*_sz);
      assert(_freelist != null);

      byte[:] ret = (unsafe byte[_sz])_freelist;
      _freelist=$((unsafe byte@@)_freelist);
      return ret;
    }
    void Dealloc(byte[:] p)
    {
      p[0:#byte@] = (unsafe byte[:])@_freelist;
      _freelist=p[0];
    }
    void Clear()
    {
      uint nsize=0;
      Node@ hold=_root;
      while((_root=hold)!=null)
      {
        nsize+=hold.size;
        hold=_root.next;
        free((unsafe byte[_root.size])_root);
      }
      _freelist=null; // There's this funny story about a time where I forgot to put this in here and then wondered why everything blew up.
      _allocchunk(nsize); // Note that nsize is in bytes
    }

  protected:
    void _allocchunk(uint nsize)
    {
      Node@ retval=(unsafe Node@)malloc(#Node + nsize);
      retval.next=_root;
      retval.size=nsize;
      _initchunk(retval);
      _root=retval;
    }

    void _initchunk(Node$ chunk)
    {
      byte[:] mem = ((unsafe byte[chunk.size])chunk)[#Node:];
      for(uint i = 0; i < #mem; i+=_sz)
      {
        mem[i:i+#byte@] = (unsafe byte[:])@_freelist;
        _freelist=mem[i];
      }
    }

    Node@ _root;
    byte@ _freelist;
    const uint _sz;
  }
  
  template[T]
  class FixedAllocator : __FixedAllocator, Allocator[T]
  {
    FixedAllocator(uint init=8) : __FixedAllocator(#T, init) {}
    T[:] Alloc(uint n, T[:] p) { return (unsafe T[:])__FixedAllocator.Alloc(n*#T); }
    void Dealloc(T[:] p) { __FixedAllocator.Dealloc((unsafe byte[:])p); }
  }
}