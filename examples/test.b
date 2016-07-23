// Test berry file

enum TestEnum : uint
{
  BLAH = 0,
  FOOBAR,
  FOO = 4,
}

template[T, int a = 1]
T templatetest(T b, int c)
{
  return a + b + c;
}

int main(string[:] args)
{
  if(#args > 0)
    return 1;
  else
  {
    int i = 5;
    int a = 0;
    
    for(i > 0)
    {
      a++;
    }
    
    return a;
  }
}