// Copyright ©2015 Black Sphere Studios

#include <stdio.h>
#include <fstream>
#include <memory>
#include "trex.h"
#include "bss-util/cTrie.h"
#include "bss-util/cHash.h"
#include "bss-util/cStr.h"
#include "ast.h"

using namespace bss_util;

cStr readfile(const char* path)
{
  FILE* f;
  FOPEN(f, path, "rb");
  if(!f) return cStr();
  fseek(f, 0, SEEK_END);
  long len = ftell(f);
  fseek(f, 0, SEEK_SET);
  cStr buf(len+1);
  fread(buf.UnsafeString(), 1, len, f);
  buf.UnsafeString()[len]=0;
  fclose(f);

  return buf;
}

int app(int argc, char** argv)
{
  cDynArray<cStr, unsigned int, CARRAY_SAFE> files;
  const char* const* modules;
  cStr out;
  bool makeDLL = false;
  bool makeDebug = false;
  int oLevel = 0;

  ProcessCmdArgs(argc, argv, [&](const char* const* p, size_t n) {
    switch(p[0][1])
    {
    case 'i': // input source files
      for(size_t i = 1; i < n; ++i)
        files.Add(readfile(p[i]));
      break;
    case 'f': // output executable or dll
      out=p[1];
      break;
    case 'm': // modules to link against
      modules=p+1;
      break;
    case 'l': // Causes a DLL to be generated instead of an EXE
      makeDLL = true;
      break;
    case 'g': // Why the hell do people use g?!
    case 'd': // include debug information
      makeDebug = true;
      break;
    case 'o':
      oLevel = !p[0][2] ? 0 : p[0][2] - '0';
    } 
  });

  Program p(Program::ARCH_X64);
  cHash<const char*, unsigned int> hash;

  for(size_t i = 0; i < files.Length(); ++i)
    Parse(files[i], p.tokens, p.strings, hash);
  DumpTokens(p.tokens, std::fstream(out + ".tokens", std::ios_base::trunc | std::ios_base::out));

  BuildAST(p);
  DumpAST(p, std::fstream(out + ".ast.xml", std::ios_base::trunc | std::ios_base::out));
  GatherTypes(p);
  ResolveTypes(p);
  Resolve(p);
  DumpAST(p, std::fstream(out + ".resolved.xml", std::ios_base::trunc | std::ios_base::out));
  //ResolveAST(p);
  //ExpandOps(p);
  //StaticAnalysis(p);
  //OptimizeAST(p);
  //cStr ir = ConvertToIR(p);
  //ir = OptimizeIR(p);
  //cStr machine = CompileIR(p);

  std::fstream ferr(out + ".errors", std::ios_base::trunc | std::ios_base::out);
  for(auto& i : p.errors)
    ferr << i.c_str() << std::endl;
  ferr.close();

  return 0;
}

int main(int argc, char** argv)
{
  cStr cmdline = "-i \"../examples/test.b\" -f \"../examples/bin/test.exe\"";
  int nargc = ToArgV<char>(0, cmdline.UnsafeString());
  DYNARRAY(char*, nargv, nargc);
  ToArgV(nargv, cmdline.UnsafeString());
  argc = nargc;
  argv = nargv;
  
  app(argc, argv);
}

struct HINSTANCE__;

// WinMain function, simply a catcher that calls the main function
int __stdcall WinMain(HINSTANCE__* hInstance, HINSTANCE__* hPrevInstance, char* lpCmdLine, int nShowCmd)
{
  cStr cmdline = lpCmdLine;
  int argc = ToArgV<char>(0, cmdline.UnsafeString());
  DYNARRAY(char*, argv, argc);
  ToArgV(argv, cmdline.UnsafeString());
  app(argc, argv);
}