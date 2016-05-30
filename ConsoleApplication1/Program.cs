using System;
using System.Reflection;
using System.Reflection.Emit;

public class Base<T>
{
    public Base(T x) { Console.Write("T"); }
    public Base(int x) { Console.Write("int"); }
}
public class Extend : Base<int>
{
    public Extend() : base(0) { }
}

public class Make<T1>
{
    public static Tuple<T1, T2> Tuple<T2>(T1 item1, T2 item2) =>
        new Tuple<T1, T2>(item1, item2);
}


public class Naming {
}
public class Program
{
    public static void Main(string[] args) =>
        Make<int>.Tuple<string>(1, "2");
}

class B<U> { }
class A<T> : B<A<A<T>>> { }

public static class Prog
{
    public static void SaveDll()
    {
        var name = "test1";
        var assembly = AppDomain.CurrentDomain.DefineDynamicAssembly(new AssemblyName(name), AssemblyBuilderAccess.Save);
        var module = assembly.DefineDynamicModule(name + ".dll");

        // public class Make<T1>
        // {
        var makeT = module.DefineType("Make", TypeAttributes.Public);
        var t1 = makeT.DefineGenericParameters("T1")[0];


        //     public static Tuple<T1, T2> Tuple<T2>(T1 item1, T2 item2) =>
        var tupleM = makeT.DefineMethod("Tuple", MethodAttributes.Public | MethodAttributes.Static);
        var t2 = tupleM.DefineGenericParameters("T2")[0];
        tupleM.SetReturnType(typeof(Tuple<,>).MakeGenericType(t1, t2));
        tupleM.SetParameters(t1, t2);
        tupleM.DefineParameter(1, ParameterAttributes.None, "item1");
        tupleM.DefineParameter(2, ParameterAttributes.None, "item2");

        //         new Tuple<T1, T2>(item1, item2);
        var g = tupleM.GetILGenerator();
        g.Emit(OpCodes.Ldarg_0);
        g.Emit(OpCodes.Ldarg_1);
        g.Emit(OpCodes.Newobj, typeof(Tuple<int, int>).GetGenericTypeDefinition().MakeGenericType(t1, t2).GetConstructor(new[] { t1, t2 }));
        g.Emit(OpCodes.Ret);

        // }
        makeT.CreateType();

        // public class Program
        // {
        var programT = module.DefineType("Program", TypeAttributes.Public);

        //     public static void Main(string[] args) =>
        var mainM = programT.DefineMethod("Main", MethodAttributes.Public | MethodAttributes.Static);
        mainM.SetReturnType(typeof(void));
        mainM.SetParameters(typeof(string[]));
        tupleM.DefineParameter(2, ParameterAttributes.None, "args");

        //         Make<int>.Tuple<string>(1, "2");
        g = mainM.GetILGenerator();
        g.Emit(OpCodes.Ldc_I4_1);
        g.Emit(OpCodes.Ldstr, "2");
        g.Emit(OpCodes.Call, tupleM.MakeGenericMethod(typeof(string)));
        g.Emit(OpCodes.Pop);
        g.Emit(OpCodes.Ret);

        // }
        programT.CreateType();

        assembly.Save(name + ".dll");
    }
}