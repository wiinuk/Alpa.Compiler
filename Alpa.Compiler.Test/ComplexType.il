.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly extern System.Numerics
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly Complex
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module Complex.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public abstract auto ansi beforefieldinit Fun`2<a,b>
       extends [mscorlib]System.Object
{
  .method public hidebysig newslot abstract virtual 
          instance !b  Apply(!a A_1) cil managed
  {
  }
  .method public hidebysig specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}
.class interface public abstract auto ansi beforefieldinit Num`1<a>
{
  .method public hidebysig newslot abstract virtual 
          instance !a  ofInteger(valuetype [System.Numerics]System.Numerics.BigInteger A_1) cil managed
  {
  }
  .method public hidebysig newslot abstract virtual 
          instance !a  '_+_'(!a A_1,
                             !a A_2) cil managed
  {
  }
}
.class public auto ansi sealed beforefieldinit 'Num`1(int32)'
       extends [mscorlib]System.Object
       implements class Num`1<int32>
{
  .method public hidebysig virtual final 
          instance int32  ofInteger(valuetype [System.Numerics]System.Numerics.BigInteger A_1) cil managed
  {
    .maxstack  1
    IL_0000:  ldarg.1
    IL_0001:  call       int32 [System.Numerics]System.Numerics.BigInteger::op_Explicit(valuetype [System.Numerics]System.Numerics.BigInteger)
    IL_0006:  ret
  }
  .method public hidebysig virtual final 
          instance int32  '_+_'(int32 A_1,
                                int32 A_2) cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.1
    IL_0001:  ldarg.2
    IL_0002:  add
    IL_0003:  ret
  }
  .method public hidebysig specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}
.class public auto ansi sealed beforefieldinit CloSucc2`1<a>
       extends class Fun`2<!a,!a>
{
  .field public initonly class Num`1<!a> item1
  .method public specialname rtspecialname 
          instance void  .ctor(class Num`1<!a> A_1) cil managed
  {
    .maxstack  4
    IL_0000:  ldarg.0
    IL_0001:  call       instance void class Fun`2<!a,!a>::.ctor()
    IL_0006:  ldarg.0
    IL_0007:  ldarg.1
    IL_0008:  stfld      class Num`1<!0> class CloSucc2`1<!a>::item1
    IL_000d:  ret
  }
  .method public hidebysig virtual final 
          instance !a  Apply(!a A_1) cil managed
  {
    .maxstack  4
    IL_0000:  ldarg.0
    IL_0001:  ldfld      class Num`1<!0> class CloSucc2`1<!a>::item1
    IL_0006:  ldarg.1
    IL_0007:  ldarg.0
    IL_0008:  ldfld      class Num`1<!0> class CloSucc2`1<!a>::item1
    IL_000d:  call       valuetype [System.Numerics]System.Numerics.BigInteger [System.Numerics]System.Numerics.BigInteger::get_One()
    IL_0012:  callvirt   instance !0 class Num`1<!a>::ofInteger(valuetype [System.Numerics]System.Numerics.BigInteger)
    IL_0017:  callvirt   instance !0 class Num`1<!a>::'_+_'(!0,
                                                            !0)
    IL_001c:  ret
  }
}
.class public auto ansi sealed beforefieldinit CloSucc`1<a>
       extends class Fun`2<class Num`1<!a>,class Fun`2<!a,!a>>
{
  .method public hidebysig virtual final 
          instance class Fun`2<!a,!a>  Apply(class Num`1<!a> A_1) cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.1
    IL_0001:  newobj     instance void class CloSucc2`1<!a>::.ctor(class Num`1<!0>)
    IL_0006:  ret
  }
  .method public hidebysig specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void class Fun`2<class Num`1<!a>,class Fun`2<!a,!a>>::.ctor()
    IL_0006:  ret
  }
}
.class public abstract auto ansi sealed beforefieldinit Program
       extends [mscorlib]System.Object
{
  .field public static initonly class Num`1<int32> 'Num`1(int32)'
  .field public static initonly int32 ten
  .method public static class Fun`2<class Num`1<!!a>,class Fun`2<!!a,!!a>> 
          succ<a>() cil managed
  {
    .maxstack  1
    IL_0000:  newobj     instance void class CloSucc`1<!!a>::.ctor()
    IL_0005:  ret
  }
  .method private specialname rtspecialname static 
          void  .cctor() cil managed
  {
    .maxstack  1
    IL_0000:  newobj     instance void 'Num`1(int32)'::.ctor()
    IL_0005:  stsfld     class Num`1<int32> Program::'Num`1(int32)'
    IL_000a:  ldc.i4     0xa
    IL_000f:  stsfld     int32 Program::ten
    IL_0014:  ret
  }
  .method public static int32  main() cil managed
  {
    .maxstack  2
    IL_0000:  call       class Fun`2<class Num`1<!!0>,class Fun`2<!!0,!!0>> Program::succ<int32>()
    IL_0005:  ldsfld     class Num`1<int32> Program::'Num`1(int32)'
    IL_000a:  callvirt   instance !1 class Fun`2<class Num`1<int32>,class Fun`2<int32,int32>>::Apply(!0)
    IL_000f:  ldsfld     int32 Program::ten
    IL_0014:  callvirt   instance !1 class Fun`2<int32,int32>::Apply(!0)
    IL_0019:  ret
  }
}