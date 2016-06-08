using System;
using System.Collections.Generic;
using System.Linq;
using System.Linq.Expressions;
using System.Numerics;
using System.Reflection;
using static System.Console;

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

    static class Program
    {
        public static bool RetBool() => true;
        public static int OfInteger(BigInteger i) => (int)i;
        public static void Main(string[] args)
        {
            new BigInteger(10);
        }
    }
}