// Berry syntax test file
/* Tests as many different syntactical cases as possible *&!@#*$&@(#/\\\\\*!*) */
/** These tests are duplicated in the testbed, but this
  * is still useful for simple parser/lexer fuzzing. ***/

using Berry;
using Berry.C; // comment
using Foo.Bar.Z.XY;
using /* ignore */ Berry.FixEverything;

import "stdio.h"

// boop

using Pone;

assert(true);

type intdef = int;
type algebriac = { i64 | float | Inner { i32 | Math.Vector.Rainbow } | RealType { i32 | float d; bool b; } };

enum Numbers
{
  ONE,
  TWO,
  THREE,
  FIVE = 2 + 3,
}

namespace Berry {
  type notanint = f16;
  namespace C.Math.Vector {
    assert(false);
    
    type lookbelow = Berry.C.Math.Vector.Rainbow;
    
    [Export("C", false)]
    [TailCall]
    [Serializable("JSON")]
    public class Rainbow : Abstract.Algebra.Monads.fake_trait[intdef, 5 + 3, "test"], f32, FooBar[Bar[i8, char, Rainbow], Rainbow, Rainbow, op+, fbar(5, _)] {
      public:
      [Serialize]
      static const var a = "234";
      int a;
      Berry.C.Math.Vector.Rainbow@@ const@$! r;
      static unsafe var@@ m = @a;
      
      template[U,X:fp_t = double, A...]
      class Double : Rainbow, U {
        
      }
      impl Double : Integral;
      
      Double[string, Abstract.Algebra.Monads.fake_trait[u16, 3].ID[T].Type] n;
      { algebraic.Inner | Rainbow }! m;
      
      pure virtual property Math.Vector.Rainbow.Double[u8, f16] Prop() const { return m + n; }
      
      enum Strings : string32 {
        ABC = "abc",
        DEF = "DEF" + "PIE",
        x = "X"
      }
      
    private:
      template[int A = 5]
      abstract var deferred() { var a = this.Prop; return this.op+(a, A); }
      Rainbow$$ op=(Vector.Rainbow!! d) { try { return @this; } catch { return Rainbow(); } }
      
      template[T:Integral]
      static { Math.Vector.Rainbow | u8 } StatFunc() { return T < 4 ? 2 : Vector.Rainbow(); }
    }
    
    namespace Abstract.Algebra {
      namespace Monads {
        template[T:Integral = u16, T B <= 8 + #S, string S = "d"]
        private trait fake_trait : string[:].Empty(3)[2], Bar[#S,T]
        {
        
        
        
        
          private:
          
        }
      }
      
      enum BORING : int {
        BORED = 3,
        BORED2,
        BORED3,
      }
    }
  }
}

namespace Foo.Bar {
  
}

assert(2 != 1);