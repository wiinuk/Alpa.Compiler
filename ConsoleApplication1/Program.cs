using System;
using GenericOperators;
using static System.Console;

namespace GenericOperators
{
    public interface IAddable<T>
    {
        T Add(T l, T r);
    }

    public struct Addable<T>
    {
        public T Value { get; private set; }
        public IAddable<T> Add { get; private set; }
        public Addable(T value, IAddable<T> add) { Value = value; Add = add; }

        public static Addable<T> operator +(Addable<T> left, Addable<T> right) => new Addable<T>(left.Add.Add(left.Value, right.Value), left.Add);
    }

    public interface IIntegral<T> : IAddable<T>
    {
        T Sub(T l, T r);
        T Mul(T l, T r);
        T Div(T l, T r);
    }

    public struct Integral<T>
    {
        public T Value { get; private set; }
        public IIntegral<T> Int { get; private set; }
        public Integral(T value, IIntegral<T> ops) { Value = value; Int = ops; }

        public static Integral<T> operator +(Integral<T> left, Integral<T> right) => new Integral<T>(left.Int.Add(left.Value, right.Value), left.Int);
        public static Integral<T> operator -(Integral<T> left, Integral<T> right) => new Integral<T>(left.Int.Sub(left.Value, right.Value), left.Int);
        public static Integral<T> operator *(Integral<T> left, Integral<T> right) => new Integral<T>(left.Int.Mul(left.Value, right.Value), left.Int);
        public static Integral<T> operator /(Integral<T> left, Integral<T> right) => new Integral<T>(left.Int.Div(left.Value, right.Value), left.Int);
    }

    //public struct GenericInt32 : IIntegral<int>
    //{
    //    readonly int value;
    //    public GenericInt32(int value) { this.value = value; }

    //    public Addable<int> GetGenericAddable() => new Addable<int>();

    //    public Integral<int> GetGenericIntegral()
    //    {
    //        throw new NotImplementedException();
    //    }
    //}
    //public struct GenericDouble : IAddable<GenericDouble>
    //{
    //    readonly double value;
    //    public GenericDouble(double value) { this.value = value; }
    //    public GenericDouble Add(GenericDouble other) => new GenericDouble(value + other.value);
    //}

    //public static class Generic
    //{
    //    public static GenericInt32 Int32(int value) => new GenericInt32(value);
    //    public static GenericDouble Double(double value) => new GenericDouble(value);

    //    public static Addable<T> AllowOperator<T>(this T self) where T : IAddable<T> => new GenericAd<T>(self);
    //    public static T UsingOperator<T>(this T self, Func<Addable<T>, Addable<T>> use) where T : IAddable<T> => use(new GenericAd<T>(self)).Value;
    //}
}

namespace ConsoleApplication1
{
    static class Usecase
    {
        public static Addable<T> Triple<T>(Addable<T> value) => value + value + value;
    }

    class Program
    {
        static void Main(string[] args)
        {
            //var a = Generic.Int32(10);
            //WriteLine("Int32 triple = {0}", Usecase.Triple(a));

            //var c = Generic.Double(10.1);
            //var d = Usecase.Triple(c);
        }
    }
}
