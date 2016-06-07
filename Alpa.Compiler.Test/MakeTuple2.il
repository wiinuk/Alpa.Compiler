.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly MakeTuple2
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module MakeTuple2.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit MakeTuple2.Make`1<T1>
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<!T1,!!T2> 
          Tuple<T2>(!T1 A_0,
                    !!T2 A_1) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  newobj     instance void class [mscorlib]System.Tuple`2<!T1,!!T2>::.ctor(!0,
                                                                                       !1)
    IL_0007:  ret
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
.class public abstract auto ansi sealed MakeTuple2.Main
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<int32,string> 
          main() cil managed
  {
    .maxstack  2
    IL_0000:  ldc.i4.1
    IL_0001:  ldstr      "2"
    IL_0006:  call       class [mscorlib]System.Tuple`2<!0,!!0> class MakeTuple2.Make`1<int32>::Tuple<string>(!0,
                                                                                                              !!0)
    IL_000b:  ret
  }
}