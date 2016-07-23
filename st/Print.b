// Copyright ©2015 Black Sphere Studios
// For conditions of distribution and use, see copyright notice in LICENSE.txt

namespace Berry {
  // Represents anything that has a ToString() function
  trait Printable {
    string ToString()
  }
  
  template[T, Args:Printable...]
  void print(Stream s, Args... args)
  {
  
  }
  
  void print(Stream s) {}
}