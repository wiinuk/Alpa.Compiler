.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly RuntimeTypeGenericArg
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module RuntimeTypeGenericArg.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi sealed beforefieldinit RuntimeTypeGenericArg.Program
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<string,string> 
          Main(string A_0,
               string A_1) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  newobj     instance void class [mscorlib]System.Tuple`2<string,string>::.ctor(!0,
                                                                                            !1)
    IL_0007:  ret
  }
}