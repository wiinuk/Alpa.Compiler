﻿.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly AliasSuccess
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module AliasSuccess.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit MyTuple`2<t1,t2>
       extends [mscorlib]System.Object
{
  .method public hidebysig specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}
.class public abstract auto ansi sealed beforefieldinit Program
       extends [mscorlib]System.Object
{
  .method public static void  main(class [mscorlib]System.Collections.Generic.List`1<class MyTuple`2<int32,class [mscorlib]System.Collections.Generic.List`1<class MyTuple`2<int32,string>>>> A_0) cil managed
  {
    .maxstack  0
    IL_0000:  ret
  }
}