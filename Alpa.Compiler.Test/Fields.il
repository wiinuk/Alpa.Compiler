.assembly extern mscorlib
{
  .publickeytoken = (B7 7A 5C 56 19 34 E0 89 )
  .ver 4:0:0:0
}
.assembly Fields
{
  .hash algorithm 0x00008004
  .ver 0:0:0:0
}
.module Fields.dll
.imagebase 0x00400000
.file alignment 0x00000200
.stackreserve 0x00100000
.subsystem 0x0003
.corflags 0x00000001
.class public auto ansi sealed beforefieldinit Fields
       extends [mscorlib]System.Object
{
  .field public initonly int32 I1
  .field public int32 IM1
  .field public static initonly int32 S1
  .field public static int32 SM1
  .field public static literal bool C1 = bool(true)
  .field public static literal char C2 = char(0x0061)
  .field public static literal string C3 = "test"
  .field public static literal object C4 = nullref
  .field public static literal string C5 = nullref
  .field public static literal int32 Int32C1 = int32(0x0000000B)
  .field public static literal int32 Int32C2 = int32(0xFFFFFFFF)
  .field public static literal int32 Int32C3 = int32(0x0000000B)
  .field public static literal int64 Int64C1 = int64(0x100000000)
  .field public static literal int64 Int64C2 = int64(0xB)
  .field public static literal int8 Int8C1 = int8(0x0B)
  .field public static literal float64 Float64C1 = float64(11.)
  .field public static literal float64 Float64C2 = float64(11.)
  .field public static literal float32 Float32C2 = float32(11.)
  .field public static literal valuetype [mscorlib]System.ConsoleColor EnumC1 = int32(0x00000000)
  .method public hidebysig specialname rtspecialname 
          instance void  .ctor() cil managed
  {
    .maxstack  2
    IL_0000:  ldarg.0
    IL_0001:  call       instance void [mscorlib]System.Object::.ctor()
    IL_0006:  ret
  }
}