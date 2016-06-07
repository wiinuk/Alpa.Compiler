.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly OverloadOps
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module OverloadOps.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi sealed Ops
       extends [mscorlib]System.Object
{
  .method public static int32  Add(int32 A_0,
                                   int32 A_1) cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  add
    IL_0003:  ret
  }
  .method public static float32  Add(float32 A_0,
                                     float32 A_1) cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  add
    IL_0003:  ret
  }
}
.class public abstract auto ansi sealed Main
       extends [mscorlib]System.Object
{
  .method public static float32  main() cil managed
  {
    .maxstack  2
    IL_0000:  ldc.i4.1
    IL_0001:  ldc.i4.3
    IL_0002:  call       int32 Ops::Add(int32,
                                        int32)
    IL_0007:  conv.r4
    IL_0008:  ldc.r4     7.1100001
    IL_000d:  call       float32 Ops::Add(float32,
                                          float32)
    IL_0012:  ret
  }
}