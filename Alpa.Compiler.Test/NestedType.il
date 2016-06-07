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
.class public abstract auto ansi sealed NestedType
       extends [mscorlib]System.Object
{
  .class auto ansi sealed nested public beforefieldinit Type1
         extends [mscorlib]System.Object
  {
    .method public static void  Method1() cil managed
    {
      .maxstack  0
      IL_0000:  ret
    }
    .method public specialname rtspecialname 
            instance void  .ctor() cil managed
    {
      .maxstack  2
      IL_0000:  ldarg.0
      IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
      IL_0006:  ret
    }
  }
  .class abstract auto ansi sealed nested public Module1
         extends [mscorlib]System.Object
  {
    .method public static void  Fun1() cil managed
    {
      .maxstack  0
      IL_0000:  ret
    }
  }
  .class abstract auto ansi sealed nested public Module2
         extends [mscorlib]System.Object
  {
    .method public static void  Fun1() cil managed
    {
      .maxstack  0
      IL_0000:  ret
    }
  }
}