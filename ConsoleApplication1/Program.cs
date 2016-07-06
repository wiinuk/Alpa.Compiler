using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Linq.Expressions;
using System.Numerics;
using System.Reflection;
using static System.Console;

public interface IFun<a, b>
{
    b Apply(a arg0);
}
public abstract class Fun<a, b>
{
    public Fun() { }
    public abstract b Apply(a arg0);
}
public sealed class Id<a> : Fun<a, a>, IFun<a, a>
{
    public Id() : base() { }
    public sealed override a Apply(a arg0) => arg0;
}

public interface IHasM
{
    string M();
}
public interface IHasO
{
    string O();
}
public interface IHasP
{
    string P();
}
public abstract class GrandParent
{
    public abstract string M();
    public abstract string N();
}
public class Parent : GrandParent, IHasM, IHasO, IHasP
{
    // overridable override GrandParent.M(), explicit implement IHasM.M
    public override string M() => "Parent.M()";
    // notOverridable override GrandParent.N()
    public override sealed string N() => "Parent.N()";
    // overridable, explicit implement IHasO.O
    public virtual string O() => "Parent.O()";
    // notOverridable, explicit implement IHasP.P
    public virtual string P() => "Parent.P()";
}

public class Child : Parent, IHasM
{
    // notOverridable override GrandParent.M()
    public override sealed string M() => "Child.M()";
    // shadows GrandParent.N()
    public virtual new string N() => "Child.N()";
    // shadows Parent.P()
    public new string P() => "Child.P()";

    string IHasM.M() => "Child.(IHasM.M)()";
}

public static class S
{
    public static void AssertEquals<T>(T left, T right)
    {
        if (Comparer<T>.Default.Compare(left, right) != 0)
        {
            throw new Exception($"AssertEquals actual: {left}, expected: {right}");
        }
    }

    public static void SMain()
    {
        Parent parent = new Parent();
        Child child = new Child();

        GrandParent parentAsGrandParent = parent;
        GrandParent childAsGrandParent = child;
        Parent childAsParent = child;
        IHasM parentAsIHasM = parent;
        IHasO parentAsIHasO = parent;
        IHasP parentAsIHasP = parent;
        IHasM childAsIHasM = child;
        IHasO childAsIHasO = child;
        IHasP childAsIHasP = child;
        
        AssertEquals(child.M(), "Child.M()");
        AssertEquals(child.N(), "Child.N()");
        AssertEquals(child.O(), "Parent.O()");
        AssertEquals(child.P(), "Child.P()");
        
        AssertEquals(childAsGrandParent.M(), "Child.M()");
        AssertEquals(childAsGrandParent.N(), "Parent.N()");

        AssertEquals(childAsParent.M(), "Child.M()");
        AssertEquals(childAsParent.N(), "Parent.N()");
        AssertEquals(childAsParent.O(), "Parent.O()");
        AssertEquals(childAsParent.P(), "Parent.P()");
        
        AssertEquals(childAsIHasM.M(), "Child.(IHasM.M)()");
        AssertEquals(childAsIHasO.O(), "Parent.O()");
        AssertEquals(childAsIHasP.P(), "Parent.P()");
    }
}

class MyList<T>
{
    public void Add(object x) => WriteLine("Add(object)");
    public void Add(T x) => WriteLine("Add(T)");
}

//class C
//{
//    public static T M<TSource, T>(TSource a) where TSource : IEnumerable<T> => a;
//    public static T M<TSource, T>(TSource a) where TSource : IEquatable<T> => a;
//}
static class Program
{
    static MethodBase ResolveMethodOfOpenType(Type closeType, MethodInfo methodOfOpenType, MethodInfo methodOfCloseType) =>
        methodOfCloseType.Module.ResolveMethod(
            methodOfCloseType.MetadataToken,
            methodOfCloseType.DeclaringType.GetGenericTypeDefinition().GetGenericArguments(),
            methodOfOpenType.GetGenericArguments());

    static MethodInfo GetMethod(Type closeType, MethodInfo methodOfOpenType) =>
        closeType
            .GetMethods()
            .Single(m =>
                m.Name == methodOfOpenType.Name &&
                ResolveMethodOfOpenType(closeType, methodOfOpenType, m) == methodOfOpenType);

    static MethodInfo GetMethod<T>(MyList<T> myList) => ((Action<object>)myList.Add).Method;
    static MethodInfo GetGenericMethod<T>(MyList<T> myList) => ((Action<T>)myList.Add).Method;
    static MethodInfo GetAddMethod<T>()
    {
        Expression<Action<MyList<T>>> lambda = x => x.Add(null);
        return ((MethodCallExpression)lambda.Body).Method;
    }
    static MethodInfo GetGemericAddMethod<T>()
    {
        Expression<Action<MyList<T>, T>> lambda = (x, v) => x.Add(v);
        return ((MethodCallExpression)lambda.Body).Method;
    }

    //static void Palette()
    //{
    //    var addString = GetMethod(typeof(MyList<object>), typeof(MyList<>).GetMethod("Add", new[] { typeof(object) }));
    //    var addT = GetMethod(typeof(MyList<object>), typeof(MyList<>).GetMethod("Add", new[] { typeof(MyList<>).GetGenericArguments()[0] }));

    //    var adds = typeof(MyList<object>).GetMethods().Where(m => m.Name == "Add").ToList();
    //    addString != addT &&
    //        adds.Count == 2 &&
    //        adds.Contains(addString) &&
    //        adds.Contains(addT)

    //    adds.Contains(GetAddMethod<object>())
    //        adds.Contains(GetGemericAddMethod<object>())
    //       // GetMethod (MyList<T> myList) => ((Action<object>)myList.Add(null))
    //       var myList = new MyList<object>();
    //    var b = GetMethod(myList) == GetGenericMethod(myList);
    //    MulticastDelegate.CreateDelegate()
    //    var listOfObject = new MyList<object>();
    //    listOfObject.Add(null);

    //    var listOfInt = new MyList<int>();
    //    listOfInt.Add(0);
    //    typeof(MyList<object>).GetMethod("Add", new[] { typeof(object) });
    //    typeof(MyList<object>).GetMethod("Add", new[] { typeof(MyList<>).GetGenericArguments()[0] });

    //    //var addObject = typeof(MyList<>).GetMethod("Add", new[] { typeof(object) });
    //    //typeof(MyList<object>)
    //    //    .GetMethods()
    //    //    .Where(m => m.Name == "Add" && m != addObject)
    //    //    .Count();
    //}
}

namespace ConsoleApplication1
{
    public interface InterfaceEq<T>
    {
        bool Eq(T left, T right);
    }

    public abstract class AbstractAdd<T>
    {
        public abstract T Add(T left, T right);
    }

    public abstract class ImplementAbstractEq_ClassAbstract<T> : InterfaceEq<T>
    {
        public abstract bool Eq(T left, T right);
    }

    public abstract class AbstractOverrideEqInt_ClasAbstract : ImplementAbstractEq_ClassAbstract<int>
    {
        public abstract override bool Eq(int l, int r);
    }

    public class OverrideEq : AbstractOverrideEqInt_ClasAbstract
    {
        public override bool Eq(int l, int r) => l == r;
    }

    public class VirtualShow
    {
        public virtual string Show() => "";
    }

    public class OverrideShow : VirtualShow
    {
        public override string Show() => "";
    }

    public class NewVirtualShow : VirtualShow
    {
        public new virtual string Show() => "";
    }

    public class OverrideNewVirtualShow : NewVirtualShow
    {
        public override string Show() => "";
    }

    public class SealedOverrideShow : VirtualShow
    {
        public sealed override string Show() => "";
    }

    public sealed class OverrideShow_ClassSealed : VirtualShow
    {
        public override string Show() => "";
    }

    public abstract class ExplicitEqBase : InterfaceEq<int>
    {
        bool InterfaceEq<int>.Eq(int left, int right) => left == right;
    }

    public class EqInt : InterfaceEq<int>
    {
        public bool Eq(int left, int right) => left == right;
    }

    public sealed class EqInt_ClassSealed : InterfaceEq<int>
    {
        public bool Eq(int left, int right) => left == right;
    }

    public class EqIntVirtual : InterfaceEq<int>
    {
        public virtual bool Eq(int left, int right) => left == right;
    }

    public class ExplicitEqInt : InterfaceEq<int>
    {
        bool InterfaceEq<int>.Eq(int left, int right) => left == right;
    }

    public sealed class ExplicitEqInt_ClassSealed : InterfaceEq<int>
    {
        bool InterfaceEq<int>.Eq(int left, int right) => left == right;
    }

    public class Any { public int Fun(int a) => a; }

    public sealed class Any_ClassSealed { public int Fun(int a) => a; }

    public class TypeParam<T, U>
    {
        public Y Fun<X, Y>(T t, U u, Y y) => default(Y);
    }

    public sealed class EqualsInt : IEquatable<int>
    {
        public bool Equals(int other) => true;
    }

    public class Outer<T1>
    {
        public class Nested1<T2>
        {
            public class Nested2<T3>
            {
                public Tuple<T1, T2, T3> F;
            }
        }
    }

    public struct StructBox<T>
    {
        public T Value;
        public long A;
        public long B;
        public long C;
        public long D;
    }

    public class ClassBox<T>
    {
        public T Value;
        public long A;
        public long B;
        public long C;
        public long D;
    }
    
    static class Program
    {
        public static bool RetBool() => true;
        public static int OfInteger(BigInteger i) => (int)i;
        public static BigInteger DefaultBigInt() => default(BigInteger);
        public static int DefaultInt() => default(int);
        public static string DefaultString() => default(string);
        public static List<T> DefaultList<T>() => default(List<T>);
        public static T DefaultClass<T>() where T : class => default(T);
        public static T DefaultStruct<T>() where T : struct => default(T);
        public static T Default<T>() => default(T);

        public static string Show<T>(T x) => x.ToString();

        public static unsafe void LoadRef()
        {
            var n = 10;
            var np = &n;
            *np = 20;
            var n2 = *np;
        }
        public unsafe static void SetRef(ref int r1, int* r2, IntPtr r3, UIntPtr r4)
        {
            r1 = 10;
            *r2 = 10;
            *(int*)r3 = 10;
            *(int*)r4 = 10;
        }
        public unsafe static void RefElemType(int* n)
        {
            var n0 = (IntPtr)10;
            var r0 = &n0;
            var v0 = *r0;

            var n1 = (UIntPtr)10;
            var r1 = &n1;
            var v1 = *r1;
            
            var n2 = n;
            var r2 = &n2;
            var v2 = *r2;
        }

        public static T ArrayElem<T>(T[] xs) => xs[0];

        public static void StructField()
        {
            var x = new StructBox<StructBox<int>>();
            x.Value.Value = 10;
            var n = x.Value.Value;
        }

        public static void Main(string[] args)
        {
            'c'.GetType();
            WriteLine('c');
            WriteLine(new BigInteger());
            WriteLine(true);
            WriteLine(false);
            var x = (sbyte)3;
            WriteLine((object)x);
            WriteLine(123u);
            WriteLine((string)null);
            WriteLine("");
            WriteLine(true.ToString());
            new BigInteger(10);
        }
    }
}