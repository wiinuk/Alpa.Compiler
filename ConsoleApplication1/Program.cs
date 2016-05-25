﻿namespace ConsoleApplication1
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

    static class Program
    {
        public static int Main(string[] args)
        {
            return 0;
        }
    }
}