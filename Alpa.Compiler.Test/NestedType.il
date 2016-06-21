.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly NestedType
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module NestedType.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi sealed beforefieldinit NestedType.Types.T1
       extends [mscorlib]System.Object
{
  .class abstract auto ansi sealed nested public beforefieldinit T2
         extends [mscorlib]System.Object
  {
    .class abstract auto ansi sealed nested public beforefieldinit T3
           extends [mscorlib]System.Object
    {
      .method public static void  M3() cil managed
      {
        .maxstack  0
        IL_0000:  ret
      }
    }
    .method public static void  M2() cil managed
    {
      .maxstack  0
      IL_0000:  ret
    }
  }
  .method public static void  M1() cil managed
  {
    .maxstack  0
    IL_0000:  ret
  }
}
.class public abstract auto ansi sealed beforefieldinit NestedType.Program
       extends [mscorlib]System.Object
{
  .method public static void  main() cil managed
  {
    .maxstack  0
    IL_0000:  call       void NestedType.Types.T1::M1()
    IL_0005:  call       void NestedType.Types.T1/T2::M2()
    IL_000a:  call       void NestedType.Types.T1/T2/T3::M3()
  }
}