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
.class interface public abstract auto ansi beforefieldinit Inherits.IHasM
{
  .method public hidebysig newslot abstract virtual 
          instance string  M() cil managed
  {
  }
}
.class interface public abstract auto ansi beforefieldinit Inherits.IHasO
{
  .method public hidebysig newslot abstract virtual 
          instance string  O() cil managed
  {
  }
}
.class interface public abstract auto ansi beforefieldinit Inherits.IHasP
{
  .method public hidebysig newslot abstract virtual 
          instance string  P() cil managed
  {
  }
}
.class public abstract auto ansi beforefieldinit Inherits.GrandParent
       extends [mscorlib]System.Object
{
  .method public hidebysig newslot abstract virtual 
          instance string  M() cil managed
  {
  }
  .method public hidebysig newslot abstract virtual 
          instance string  N() cil managed
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
.class public auto ansi beforefieldinit Inherits.Parent
       extends Inherits.GrandParent
       implements Inherits.IHasM,
                  Inherits.IHasO,
                  Inherits.IHasP
{
  .method public hidebysig virtual instance string 
          M() cil managed
  {
    .maxstack  1
    IL_0000:  ldstr      "Parent.M()"
    IL_0005:  ret
  }
  .method public hidebysig virtual final 
          instance string  N() cil managed
  {
    .maxstack  1
    IL_0000:  ldstr      "Parent.N()"
    IL_0005:  ret
  }
  .method public hidebysig newslot virtual 
          instance string  O() cil managed
  {
    .maxstack  1
    IL_0000:  ldstr      "Parent.O()"
    IL_0005:  ret
  }
  .method public hidebysig newslot virtual 
          instance string  P() cil managed
  {
    .maxstack  1
    IL_0000:  ldstr      "Parent.P()"
    IL_0005:  ret
  }
  .method public hidebysig specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void Inherits.GrandParent::.ctor()
    IL_0006:  ret
  }
}
.class public auto ansi beforefieldinit Inherits.Child
       extends Inherits.Parent
       implements Inherits.IHasM
{
  .method public hidebysig virtual final 
          instance string  M() cil managed
  {
    .maxstack  1
    IL_0000:  ldstr      "Child.M()"
    IL_0005:  ret
  }
  .method public hidebysig newslot virtual 
          instance string  N() cil managed
  {
    .maxstack  1
    IL_0000:  ldstr      "Child.N()"
    IL_0005:  ret
  }
  .method public hidebysig final instance string 
          P() cil managed
  {
    .maxstack  1
    IL_0000:  ldstr      "Child.P()"
    IL_0005:  ret
  }
  .method private hidebysig newslot virtual final 
          instance string  IHasM.M() cil managed
  {
    .override Inherits.IHasM::M
    .maxstack  1
    IL_0000:  ldstr      "Child.(IHasM.M)()"
    IL_0005:  ret
  }
  .method public hidebysig specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void Inherits.Parent::.ctor()
    IL_0006:  ret
  }
}