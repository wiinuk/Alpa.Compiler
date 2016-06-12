.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly MakeTupleOverload
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module MakeTupleOverload.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit MakeTupleOverload.Make`1<T1>
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
  .method public static class [mscorlib]System.Tuple`2<string,string> 
          Tuple(string A_0,
                string A_1) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  newobj     instance void class [mscorlib]System.Tuple`2<string,string>::.ctor(!0,
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
.class public abstract auto ansi sealed beforefieldinit MakeTupleOverload.Main
       extends [mscorlib]System.Object
{
  .method public static class [mscorlib]System.Tuple`2<class [mscorlib]System.Tuple`2<string,string>,class [mscorlib]System.Tuple`2<string,string>> 
          main(string A_0,
               string A_1,
               string A_2,
               string A_3) cil managed
  {
    .maxstack  3
    IL_0000:  ldarg.0
    IL_0001:  ldarg.1
    IL_0002:  call       class [mscorlib]System.Tuple`2<!0,!!0> class MakeTupleOverload.Make`1<string>::Tuple<string>(!0,
                                                                                                                      !!0)
    IL_0007:  ldarg.2
    IL_0008:  ldarg.3
    IL_0009:  call       class [mscorlib]System.Tuple`2<string,string> class MakeTupleOverload.Make`1<string>::Tuple(string,
                                                                                                                     string)
    IL_000e:  newobj     instance void class [mscorlib]System.Tuple`2<class [mscorlib]System.Tuple`2<string,string>,class [mscorlib]System.Tuple`2<string,string>>::.ctor(!0,
                                                                                                                                                                          !1)
    IL_0013:  ret
  }
}