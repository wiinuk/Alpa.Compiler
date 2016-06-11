.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly Inherits
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module Inherits.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit Inherits.Int32EqComp
       extends [mscorlib]System.Object
       implements class [mscorlib]System.IEquatable`1<int32>,
                  class [mscorlib]System.IComparable`1<int32>
{
  .method public hidebysig newslot virtual final 
          instance bool  Equals(int32 A_1) cil managed
  {
    .maxstack  1
    IL_0000:  ldc.i4.1
    IL_0001:  ret
  }
  .method public hidebysig newslot virtual final 
          instance int32  CompareTo(int32 A_1) cil managed
  {
    .maxstack  1
    IL_0000:  ldc.i4.1
    IL_0001:  ret
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