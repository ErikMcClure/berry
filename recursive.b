
module std

const bool = data { True | False }
const e = enum : i32 { One, Two, Three } // not an actual type, just a namespaced collection of constants
const s = struct { i : i32, b : bool, union { a : f32, b : u32 } }

fn add(l : int, r : int) : int
  return l + r
end
 
// The : between argument name and argument type is actually optional
fn[a] app(self : Iterator(a), fn : {a} -> {}) : {}
  for x in self do
    fn(x)
  end
end
  
//fn test[a, e : Type] where a ~= e (ref : a) : e
fn[a, e : Type] where a ~= e test(ref : a) : e
  return struct {gen : ref}
end
  
end


Note: A subtyping system must be *explicit*. All types and subtypes must be declared, they are never automatically inherited by satisfying a set of constraints. The set of constraints can be associated with a subtype, but you have to opt-in or the type system doesn't work.

When you ask for something that is "integral" what you're really asking for is any type that implements all of the necessary operations that an integer does.

A "subtype" implies that a type is a "subset" of another type, meaning that you cast _backwards_. The parent of a subtype necessarily implements everything the subtype does, so you can cast from the subtype up to it's parent, not the other way around. This means that a 64-bit integer is a subtype of an infinite-precision integer, a 32-bit integer is a subtype of a 64-bit integer, an 8-bit unsigned integer is a subtype of a 16-bit integer, etc.

Given two structs that share several fields, you would build a synthetic type that consists of just those overlapping fields, then have both structs implement it. This allows all structs to satisfy arbitrary field requirements, and also consistently work across C bounderies because memory layouts will either be predictable, or a conflict will throw a type error because a synthetic type overlaps with an already existing C type.

When you are thinking about what the actual "type" of a type is, it's literally just a Type, or a Function, or another higher level construct. That higher level constructs type is then a LanguageElement type, or something appropriate. 

Level 0 types:
  N-bit integer
  N-bit unsigned integer
  N-bit float
  bool
  struct aggregate
  union aggregate
  N-element array
  N-element vector (can only be used on types that are meaningful for SSE operations)
  N-element tuple
  pointer
  constant
  algebriac type (if used in a Level 0 context, gets reduced to a tagged union)
  concrete function (a function that only operates on level 0 types and therefore actually exists as machine code. This is the only function that can have a pointer.)
  
all these types are used at the bottom level of code generation and strongly correspond to concepts in LLVM or Webassembly. Many of them have very strict requirements - for example, a pointer can ONLY point to another level 0 type, because you can't have a pointer to an abstract concept. "bool" is defined here mostly for convenience because it is a concept used in the compiler, but this is optional. An algebriac data type called "bool" could conceivably be optimized down as well.

Level 1 types:
  Type (any level 0 type)
  Module
  Function
  Expression
  Symbol
  Splice
  
Note: ALL functions must return exactly one value to make the type system evaluation work. Functions that return "multiple" values actually just return a tuple which is then automatically taken apart.
  
Level 2 types:
  Kind
  Witness Types
  


Algebriac subtyping:
Determining whether or not a constraint is a subset of another constraint is exactly the problem of determining if a type is a subset of another type. As a result, the same algorithm could be used if constraints form a distributive lattice.