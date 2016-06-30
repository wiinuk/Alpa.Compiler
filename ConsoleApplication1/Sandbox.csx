using System.Reflection;
using System.Reflection.Emit;
using System.Collections.Generic;
using System;
using System.Linq.Expressions;
using System.Linq;
using System.Collections.ObjectModel;
using static System.Linq.Expressions.ExpressionType;
using static System.Reflection.Emit.OperandType;
using static System.Reflection.ExceptionHandlingClauseOptions;
using static System.Console;
using System.Runtime.CompilerServices;

public sealed class MEnv
{
    public readonly Module Module;
    public readonly Module BaseModule;
    public readonly Type[] TypeArgs;
    public readonly Type[] MethodTypeArgs;
    public readonly IReadOnlyList<ExceptionHandlingClause> Handlers;
    public MEnv(Module Module, Module BaseModule, Type[] TypeArgs, Type[] MethodTypeArgs, ExceptionHandlingClause[] Handlers)
    {
        this.Module = Module;
        this.BaseModule = BaseModule;
        this.TypeArgs = TypeArgs;
        this.MethodTypeArgs = MethodTypeArgs;
        this.Handlers = Handlers;
    }
}

public sealed class Stream
{
    public int index { get; private set; }
    public readonly IReadOnlyList<byte> items;
    public Stream(int index, IReadOnlyList<byte> items)
    {
        this.index = index;
        this.items = items;
    }
    public bool canRead => index < items.Count;

    public byte readU1() => items[index++];
    public sbyte readI1() => (sbyte)readU1();
    public short readI2() => (short)(readU1() | (readU1() << 8));

    private int readU1Shift(int n) => readU1() << n;
    public int readI4() => readU1Shift(0) | readU1Shift(8) | readU1Shift(16) | readU1Shift(24);
    public long readI8()
    {
        var x1 = (long)readI4();
        var x2 = (long)readI4() << 32;
        return x1 | x2;
    }
    public double readF8() => BitConverter.Int64BitsToDouble(readI8());
    public float readF4() => BitConverter.ToSingle(BitConverter.GetBytes(readI4()), 0);
}

static IReadOnlyList<T> ToReadonlyList<T>(this IEnumerable<T> source) => Array.AsReadOnly(source.ToArray());
Stream makeStream(IEnumerable<byte> xs) => new Stream(0, xs.ToReadonlyList());

MEnv envOfMethodBase(MethodBase m)
{
    var t = m.DeclaringType;
    return new MEnv
    (
        Module: m.Module,
        BaseModule: t.BaseType.Module,
        TypeArgs: t.IsGenericType ? t.GetGenericArguments() : null,
        MethodTypeArgs: m.IsGenericMethod ? m.GetGenericArguments() : null,
        Handlers: m.GetMethodBody().ExceptionHandlingClauses.ToArray()
    );
}
var opMap =
    typeof(OpCodes)
        .GetFields()
        .Select(f => f.GetValue(null))
        .OfType<OpCode>()
        .ToDictionary(x => x.Value, x => x);

static void printTupleLike<T>(this IEnumerable<T> xs, Action<T> print)
{
    Write("(");
    using (var e = xs.GetEnumerator())
    {
        if (e.MoveNext())
        {
            print(e.Current);
            while (e.MoveNext())
            {
                Write(", ");
                print(e.Current);
            }
        }
    }
    Write(")");
}
void printString(char q, string s)
{
    Write(q);
    foreach (var x in s)
    {
        if (x == q)
        {
            Write("\\{0}", q);
        }
        else if (!char.IsControl(x) && (short)x <= 128)
        {
            Write(x);
        }
        else
        {
            Write("\\u{0:X4}", (short)x);
        }
    }
    Write(q);
}
bool isIdStartOrContinue(char c) => '_' == c || '`' == c || char.IsLetterOrDigit(c);
bool isIdStart(char c) => '_' == c || char.IsLetter(c);

void printId(string s)
{
    if (s == "") { Write("''"); }
    else if (isIdStart(s[0]) && s.All(isIdStartOrContinue)) { Write(s); }
    else { printString('\'', s); }
}
void printType(Type x)
{
    printId(x.Name);
    if (x.IsGenericType) { x.GetGenericArguments().printTupleLike(printType); }
}
void printMethod(MethodBase m)
{
    printType(m.DeclaringType);
    Write("::");
    printId(m.Name);
    if (m.IsGenericMethod) { m.GetGenericArguments().printTupleLike(printType); }
    m.GetParameters().printTupleLike(p => printType(p.ParameterType));
    Write(" : ");
    var mi = m as MethodInfo;
    var ret = mi != null ? mi.ReturnType : typeof(void);
    printType(ret);
}
void printField(FieldInfo x)
{
    printType(x.DeclaringType);
    Write("::");
    printId(x.Name);
    Write(" : ");
    printType(x.FieldType);
}
void printBr(int x) => Write("@x{0:X4}", x);

void printOperand(MEnv env, Stream s, OperandType t)
{
    switch (t)
    {
        case InlineBrTarget: printBr(s.readI4() + s.index); return;
        case InlineField: printField(env.Module.ResolveField(s.readI4(), env.TypeArgs, env.MethodTypeArgs)); return;
        case InlineI: Write(s.readI4()); return;
        case InlineI8: Write("{0}L", s.readI8()); return;
        case InlineMethod:
            var md = s.readI4();
            try
            {
                printMethod(env.Module.ResolveMethod(md, env.TypeArgs, env.MethodTypeArgs));
            }
            catch
            {
                printMethod(env.BaseModule.ResolveMethod(md, env.TypeArgs, env.MethodTypeArgs));
            }
            return;
        case InlineNone: return;
        case InlineR: Write(s.readF8()); return;
        case InlineSig: Write("signature ({0})", env.Module.ResolveSignature(s.readI4())); return;
        case InlineString: printString('"', env.Module.ResolveString(s.readI4())); return;
        case InlineSwitch:
            var count = s.readI4();
            var offset = s.index + count * 4;

            Enumerable
                .Range(0, count)
                .Select(_ => offset + s.readI4())
                .printTupleLike(printBr);
            return;

        case InlineTok:
            var tok = s.readI4();
            var m = env.Module.ResolveMember(tok, env.TypeArgs, env.MethodTypeArgs);
            var fi = m as FieldInfo;
            if (fi != null) { printField(fi); }
            else
            {
                var mb = m as MethodBase;
                if (mb != null) { printMethod(mb); }
                else
                {
                    var ty = m as Type;
                    if (ty != null) { printType(ty); }
                    else
                    {
                        Write("member({0:X6})", tok);
                    }
                }
            }
            return;

        case InlineType: printType(env.Module.ResolveType(s.readI4(), env.TypeArgs, env.MethodTypeArgs)); return;
        case InlineVar: Write(s.readI2()); return;
        case ShortInlineBrTarget: printBr(s.readI1() + s.index); return;
        case ShortInlineI: Write("{0}y", s.readI1()); return;
        case ShortInlineR: Write("{0}f", s.readF4()); return;
        case ShortInlineVar: Write(s.readU1()); return;
        default: throw new Exception("unknown opcode value.");
    }
}
short readOpValue(Stream s)
{
    var v = s.readU1();
    return (v == 0xFE) ? (short)((0xFE << 8) | s.readU1()) : v;
}
void printIndent(int indent)
{
    for (var i = 0; i < indent; i++) { Write("    "); }
}

int printBlockStart(int i, MEnv env, int offset)
{
    var h = env.Handlers
        .FirstOrDefault(x =>
            x.TryOffset == offset ||
            x.HandlerOffset == offset ||
            (x.Flags == Filter && x.FilterOffset == offset)
        );
    if (h == null) { return i; }
    else if (h.TryOffset == offset)
    {
        printIndent(i);
        WriteLine("try");
        return i + 1;
    }
    else if (h.HandlerOffset == offset)
    {

        printIndent(i);
        switch (h.Flags)
        {
            case Finally: WriteLine("finally"); break;
            case Fault: WriteLine("fault"); break;
            case Clause:
                Write("catch ");
                printType(h.CatchType);
                WriteLine();
                break;
            case Filter: WriteLine("then"); break;
            default: throw new Exception();
        }
        return i + 1;
    }
    else
    {
        printIndent(i);
        WriteLine("filter");
        return i + 1;
    }
}

int printBlockEnd(int i, MEnv env, int offset)
{
    var h = env.Handlers
        .FirstOrDefault(x =>
            x.TryOffset + x.TryLength == offset ||
            x.HandlerOffset + x.HandlerLength == offset ||
            (x.Flags == Filter && x.HandlerOffset == offset)
        );
    if (h == null)
    {
        return i;
    }
    else if (offset == h.HandlerOffset)
    {
        return i - 1;
    }
    else
    {
        WriteLine();
        printIndent(i - 1);
        Write(";");
        return i - 1;
    }
}
int printInstr(int i, MEnv env, Stream s)
{
    var offset = s.index;
    var op = opMap[readOpValue(s)];
    var i2 = printBlockStart(i, env, offset);
    printIndent(i2);
    printBr(offset);
    Write(" {0} ", op.Name);
    printOperand(env, s, op.OperandType);
    return printBlockEnd(i2, env, s.index);
}
void printIL(MEnv env, Stream s)
{
    if (s.canRead)
    {
        var i = printInstr(0, env, s);
        while (s.canRead)
        {
            WriteLine();
            i = printInstr(i, env, s);
        }
    }
}
void printLocals(MethodBody b)
{
    var vs = b.LocalVariables;
    if (vs != null && 1 <= vs.Count)
    {
        Write("let ");
        if (!b.InitLocals) { Write("noinit "); }
        vs.printTupleLike(v =>
        {
            if (v.IsPinned) { Write("pinned "); }
            printType(v.LocalType);
        });
        WriteLine();
    }
}
void printMethodBase(MethodBase m)
{
    var env = envOfMethodBase(m);
    var b = m.GetMethodBody();
    var xs = b.GetILAsByteArray();
    printLocals(b);
    printIL(env, makeStream(xs));
}

static StrongBox<TResult> tryPick<TSource, TResult>(this IEnumerable<TSource> source, Func<TSource, StrongBox<TResult>> picker)
{
    foreach (var value in source)
    {
        var result = picker(value);
        if (result != null) { return result; }
    }
    return null;
}

static IEnumerable<Expression> Expressions(MemberBinding m)
{
    switch (m.BindingType)
    {
        case MemberBindingType.Assignment:
            var ma = m as MemberAssignment;
            yield return ma.Expression;
            break;

        case MemberBindingType.MemberBinding:
            var mmb = m as MemberMemberBinding;
            foreach (var b in mmb.Bindings) { foreach (var c in Expressions(b)) { yield return c; } }
            break;

        case MemberBindingType.ListBinding:
            var lb = m as MemberListBinding;
            foreach (var i in lb.Initializers) { foreach (var a in i.Arguments) { yield return a; } }
            break;

        default:
            break;
    }
}

static IEnumerable<T> Append<T>(T value, IEnumerable<T> values)
{
    yield return value;
    foreach (var v in values) { yield return v; }
}
static IEnumerable<T> Append<T>(IEnumerable<T> values, T value)
{
    foreach (var v in values) { yield return v; }
    yield return value;
}

static StrongBox<T> tryPick<T>(this Expression expr, Func<Expression, StrongBox<T>> picker)
{
    if (expr == null) { return null; }

    var result = picker(expr);
    if (result != null) { return result; }

    switch (expr.NodeType)
    {
        case Add:
        case AddChecked:
        case And:
        case AndAlso:
        case ArrayIndex:
        case Coalesce:
        case Divide:
        case Equal:
        case ExclusiveOr:
        case GreaterThan:
        case GreaterThanOrEqual:
        case LeftShift:
        case LessThan:
        case LessThanOrEqual:
        case Modulo:
        case Multiply:
        case MultiplyChecked:
        case NotEqual:
        case Or:
        case OrElse:
        case Power:
        case RightShift:
        case Subtract:
        case SubtractChecked:
        case Assign:
        case AddAssign:
        case AndAssign:
        case DivideAssign:
        case ExclusiveOrAssign:
        case LeftShiftAssign:
        case ModuloAssign:
        case MultiplyAssign:
        case OrAssign:
        case PowerAssign:
        case RightShiftAssign:
        case SubtractAssign:
        case AddAssignChecked:
        case MultiplyAssignChecked:
        case SubtractAssignChecked:
            var be = expr as BinaryExpression;
            return new[] { be.Left, be.Right }.tryPick(x => x.tryPick(picker));

        case ArrayLength:
        case ExpressionType.Convert:
        case ConvertChecked:
        case Negate:
        case UnaryPlus:
        case NegateChecked:
        case Not:
        case Quote:
        case TypeAs:
        case Decrement:
        case Increment:
        case Throw:
        case Unbox:
        case PreIncrementAssign:
        case PreDecrementAssign:
        case PostIncrementAssign:
        case PostDecrementAssign:
        case OnesComplement:
        case IsTrue:
        case IsFalse:
            var ue = expr as UnaryExpression;
            return ue.Operand.tryPick(picker);

        case Call:
            var mce = expr as MethodCallExpression;
            return Append(mce.Object, mce.Arguments).tryPick(x => x.tryPick(picker));

        case Conditional:
            var ce = expr as ConditionalExpression;
            return new[] { ce.Test, ce.IfTrue, ce.IfFalse }.tryPick(x => x.tryPick(picker));

        case Constant:
        case Parameter:
        case DebugInfo:
        case Default:
        case Extension:
            return null;

        case Invoke:
            var ie = expr as InvocationExpression;
            return Append(ie.Expression, ie.Arguments).tryPick(x => x.tryPick(picker));

        case Lambda:
            var le = expr as LambdaExpression;
            return Append(le.Parameters, le.Body).tryPick(x => x.tryPick(picker));

        case ListInit:
            var lie = expr as ListInitExpression;
            return Append(lie.NewExpression, lie.Initializers.SelectMany(i => i.Arguments)).tryPick(x => x.tryPick(picker));

        case MemberAccess:
            var me = expr as MemberExpression;
            return me.Expression.tryPick(x => x.tryPick(picker));

        case MemberInit:
            var mie = expr as MemberInitExpression;
            return Append(mie.NewExpression, mie.Bindings.SelectMany(Expressions)).tryPick(x => x.tryPick(picker));

        case New:
            var ne = expr as NewExpression;
            return ne.Arguments.tryPick(x => x.tryPick(picker));

        case NewArrayInit:
        case NewArrayBounds:
            var nae = expr as NewArrayExpression;
            return nae.Expressions.tryPick(x => x.tryPick(picker));

        case TypeIs:
        case TypeEqual:
            var ibe = expr as TypeBinaryExpression;
            return ibe.Expression.tryPick(x => x.tryPick(picker));

        case Block:
            var ble = expr as BlockExpression;
            return Append(ble.Variables.Concat(ble.Expressions), ble.Result).tryPick(x => x.tryPick(picker));

        case Dynamic:
            var de = expr as DynamicExpression;
            return de.Arguments.tryPick(x => x.tryPick(picker));

        case Goto:
            var ge = expr as GotoExpression;
            return ge.Value.tryPick(picker);

        case Index:
            var ixe = expr as IndexExpression;
            return Append(ixe.Object, ixe.Arguments).tryPick(x => x.tryPick(picker));

        case ExpressionType.Label:
            var lbe = expr as LabelExpression;
            return lbe.DefaultValue.tryPick(picker);

        case RuntimeVariables:
            var rve = expr as RuntimeVariablesExpression;
            return rve.Variables.tryPick(x => x.tryPick(picker));

        case Loop:
            var loe = expr as LoopExpression;
            return loe.Body.tryPick(picker);

        case Switch:
            var se = expr as SwitchExpression;
            return Append(Append(se.SwitchValue, se.Cases.SelectMany(c => Append(c.TestValues, c.Body))), se.DefaultBody).tryPick(x => x.tryPick(picker));

        case Try:
            var te = expr as TryExpression;
            return Append(te.Body, Append(Append(te.Fault, te.Handlers.SelectMany(c => new[] { c.Variable, c.Filter, c.Body })), te.Finally)).tryPick(x => x.tryPick(picker));

        default:
            throw new Exception();
    }
}

StrongBox<T> Some<T>(T v) => new StrongBox<T>(v);
StrongBox<T> None<T>() => null;
static T UnwrapOrDefault<T>(this StrongBox<T> v) => v == null ? default(T) : v.Value;
static T Unwrap<T>(this StrongBox<T> v)
{
    if (v == null) { throw new Exception($"{nameof(StrongBox<T>)} is empty."); }
    return v.Value;
}
static T UnwrapOr<T>(this StrongBox<T> v, Func<T> ifNone) => (v == null) ? ifNone() : v.Value;

MethodBase getMethod<T>(Expression<Func<T>> expr) =>
    expr.tryPick(e =>
    {
        switch (e.NodeType)
        {
            case Call: return Some((MethodBase)(e as MethodCallExpression).Method);
            case New: return Some((MethodBase)(e as NewExpression).Constructor);
            default: return None<MethodBase>();
        }
    })
    .UnwrapOr(() => { throw new InvalidOperationException($"method not found. { nameof(expr) }: { expr }"); });

var m = getMethod(() => "abc" + "rc");

public static class T
{
    public static IEnumerable<int> F(IEnumerable<int> xs)
    {
        var x = 10;
        return xs.Select(i => x += i);
    }
}

printMethodBase(typeof(T).GetMethod("F"));

var p = Expression.Parameter(typeof(int));
var xs = new ReadOnlyCollection<ParameterExpression>(new[] { p });
IEnumerable<Expression> ixs = xs;

//let print e = getMethod e |> printMethodBase; printfn ""
//let x() = [| 20n; 30n |]
//let app f x = f x

//let tryf() = try 1 / 0 with:? DivideByZeroException-> 0

//// print <@ let mutable x = ResizeArray.Enumerator() in x.MoveNext() @>


//let y() = [| 1s; 2s |]
//print <@ y @>

//try print <@ tryf @>
//with e->printfn "%A" e