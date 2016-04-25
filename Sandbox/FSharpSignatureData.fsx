module internal A
open System.Reflection
open System.IO
open System

let loadAsembly load =
    try Seq.singleton <| load()
    with 
    | :? FileNotFoundException
    | :? FileLoadException
    | :? BadImageFormatException -> Seq.empty

let getAssemblies (a: Assembly) = seq {
    for n in a.GetReferencedAssemblies() do
        yield! loadAsembly <| fun _ -> Assembly.Load n

    let path = a.Location
    if File.Exists path then
        let parent = Path.GetDirectoryName path
        if Directory.Exists parent then
            for f in Directory.GetFiles parent do
                yield! loadAsembly <| fun _ -> Assembly.LoadFile f
}

let rec assemblies knownNames a =
    let (++) x xs = Seq.append [|x|] xs

    let names =
        getAssemblies a 
        |> Seq.filter (fun n -> not <| Set.contains n.FullName knownNames) 
        |> Seq.cache

    let knownNames =
        names
        |> Seq.fold (fun knownNames n -> Set.add n.FullName knownNames) knownNames

    a ++ Seq.collect (fun a -> a ++ assemblies knownNames a) names

module Parser =
    [<Struct>]
    type View<'a>(xs: array<'a>, i: int) =
        member __.Array = xs
        member __.Index = i

    type Reply<'a,'c> = Succ of 'a * View<'c> | Fail of string list
    
    let succ x = fun xs -> Succ(x, xs)
    let fail message = fun _ -> Fail [message]
    let (>>.) l r = fun xs ->
        match l xs with
        | Fail e -> Fail e
        | Succ(_, xs) -> r xs

    let (.>>.) l r = fun xs ->
        match l xs with
        | Fail e -> Fail e
        | Succ(l, xs) ->
            match r xs with
            | Fail e -> Fail e
            | Succ(r, xs) -> Succ((l, r), xs)

    let (>>=) p f = fun xs ->
        match p xs with
        | Fail e -> Fail e
        | Succ(r, xs) ->
            let p = f r
            p xs
            
    let (|>>) p f = fun xs ->
        match p xs with
        | Fail e -> Fail e
        | Succ(r, xs) -> Succ(f r, xs)

    let (<|>) l r = fun xs ->
        match l xs with
        | Fail e1 ->
            match r xs with
            | Fail e2 -> Fail(e1 @ e2)
            | r -> r
        | r -> r
        
    let pipe2 l r f = fun xs ->
        match l xs with
        | Fail e -> Fail e
        | Succ(l, xs) ->
            match r xs with
            | Fail e -> Fail e
            | Succ(r, xs) -> Succ(f l r, xs)

    let pipe3 p1 p2 p3 f = fun xs ->
        match p1 xs with
        | Fail e -> Fail e
        | Succ(r1, xs) -> pipe2 p2 p3 (fun r2 r3 -> f r1 r2 r3) xs

    let pipe4 p1 p2 p3 p4 f = fun xs ->
        match p1 xs with
        | Fail e -> Fail e
        | Succ(r1, xs) -> pipe3 p2 p3 p4 (fun r2 r3 r4 -> f r1 r2 r3 r4) xs
        
    let tuple3 p1 p2 p3 = pipe3 p1 p2 p3 <| fun r1 r2 r3 -> r1, r2, r3
    let tuple4 p1 p2 p3 p4 = pipe4 p1 p2 p3 p4 <| fun r1 r2 r3 r4 -> r1, r2, r3, r4

    type Tuple7<'T1,'T2,'T3,'T4,'T5,'T6,'T7> = {
        Item1: 'T1
        Item2: 'T2
        Item3: 'T3
        Item4: 'T4
        Item5: 'T5
        Item6: 'T6
        Item7: 'T7
    }
    let tuple7 (p1, p2, p3, p4, p5, p6, p7) = pipe4 p1 p2 p3 (tuple4 p4 p5 p6 p7) <| fun r1 r2 r3 (r4, r5, r6, r7) ->
        {
            Item1 = r1; Item2 = r2; Item3 = r3; Item4 = r4
            Item5 = r5; Item6 = r6; Item7 = r7
        }

    let count n p xs =
        let rec aux rs xs = function
            | 0 -> Succ(List.rev rs, xs)
            | n ->
                match p xs with
                | Fail e -> Fail e
                | Succ(r, xs) -> aux (r::rs) xs (n - 1)

        if n < 0 then Fail [sprintf "count %d ... ..." n]
        else aux [] xs n

    module Buffer =
        let newArray() = Array.zeroCreate 4
        let newSize() = 0

        let asArray (items: array<_>) size =
            if items.Length = size then items
            else items.[0..size-1]

        let add (items: array<_>) size v =            
            let extend (items: array<_>) size =
                let xs = Array.zeroCreate(min 2146435071 (items.Length * 2))
                System.Array.Copy(items, 0, xs, 0, size)
                xs

            let items = if items.Length = size then extend items size else items
            
            items.[size] <- v
            items
                
    let countArray n p xs =
        let rec aux items size xs = function
            | 0 -> Succ(Buffer.asArray items size, xs)
            | n ->
                match p xs with
                | Fail e -> Fail e
                | Succ(r, xs) ->
                    let items = Buffer.add items size r
                    aux items (size + 1) xs (n - 1)

        if n < 0 then Fail [sprintf "countArray %d ... ..." n]
        else aux (Buffer.newArray()) (Buffer.newSize()) xs n

    let utf8String n (xs': View<_>) =
        let i = xs'.Index
        if i + n <= xs'.Array.Length then
            let s = System.Text.Encoding.UTF8.GetString(xs'.Array, i, n)
            Succ(s, View(xs'.Array, xs'.Index + n))
        else Fail [sprintf "countCharsArray %d ..." n]

    let many p = fun xs ->
        let rec aux rs xs =
            match p xs with
            | Fail _ -> Succ(List.rev rs, xs)
            | Succ(r, xs) -> aux (r::rs) xs
        aux [] xs


    let anyChar (xs: View<_>) =
        if xs.Index < xs.Array.Length
        then Succ(xs.Array.[xs.Index], View(xs.Array, xs.Index+1))
        else Fail ["skip []"]

    let pchar c (xs: View<_>) =
        if xs.Index < xs.Array.Length then
            let x = xs.Array.[xs.Index]
            if x = c then Succ(x, View(xs.Array, xs.Index+1))
            else Fail [sprintf "pchar %A ..." c]
        else Fail [sprintf "pchar %A ..." c]

    let parse p xs = p <| View(Seq.toArray xs, 0)
    type Parser<'c,'a> = View<'c> -> Reply<'a,'c>
    type ByteParser<'a> = Parser<byte,'a>

open Parser

let u_byte : ByteParser<byte> = anyChar
let prim_u_int32 = pipe4 u_byte u_byte u_byte u_byte <| fun b0 b1 b2 b3 ->
    int b0 ||| (int b1 <<< 8) ||| (int b2 <<< 16) ||| (int b3 <<< 24)

let u_int32 = u_byte >>= fun b0 ->
    if b0 <= 0x7Fuy then succ <| int b0
    elif b0 <= 0xBFuy then
        let b0 = b0 &&& 0x7Fuy
        u_byte |>> fun b1 -> (int b0 <<< 8) ||| int b1
    else
        prim_u_int32
        
let u_bytes = u_int32 >>= fun n -> countArray n u_byte
let u_int = u_int32
let u_prim_string = u_int32 >>= utf8String
let u_array p = u_int >>= fun n -> countArray n p

let u_encoded_ccuref =
    u_byte >>= function 
    | 0uy -> u_prim_string
    | n -> fail <| sprintf "u_encoded_ccuref: found number 0x%02Xuy" n

let u_encoded_string = u_prim_string
let u_encoded_pubpath = u_array u_int
let u_encoded_nleref = u_int .>>. u_array u_int
let u_encoded_simpletyp = u_int

let start1 =
    tuple7(
        u_array u_encoded_ccuref,
        tuple3 u_int u_int u_int,
        u_array u_encoded_string,
        u_array u_encoded_pubpath,
        u_array u_encoded_nleref,
        u_array u_encoded_simpletyp,
        u_bytes
    )

type Ignore = unit
type range = Ignore
type TyparData = Ignore
type XmlDoc = Ignore
type CompiledTypeRepr = Ignore
type ILScopeRef = Ignore
type Val = Ignore
type ValRef = Ignore
type ModuleOrNamespaceKind = Ignore
type TyconRef = Ignore
type ILTypeRef = Ignore
type TyconRecdFields = Ignore
type ILMethodRef = Ignore
type ILType = Ignore
type UnionCaseRef = Ignore
type ILTypeDef = Ignore
type MeasureExpr = Ignore
type TyconObjModelData = Ignore
type TyconUnionData = Ignore
type expr = Ignore
type NameMultiMap<'a> = | NameMultiMap
type LazyWithContext<'a,'b> = | LazyWithContext
type cache<'a> = | Cache
type QueueList<'a> = | QueueList


type TyparKind =
    | KindType 
    | KindMeasure

type stamp = int64

[<Struct>]
type EntityFlags (flags: int64) =
    new (usesPrefixDisplay, isModuleOrNamespace, preEstablishedHasDefaultCtor, hasSelfReferentialCtor) = 
        EntityFlags(
            (if isModuleOrNamespace then 0b00000000001L else 0L) |||
            (if usesPrefixDisplay then 0b00000000010L else 0L) |||
            (if preEstablishedHasDefaultCtor then 0b00000000100L else 0L) |||
            (if hasSelfReferentialCtor then 0b00000001000L else 0L)
        ) 

    member x.IsModuleOrNamespace = (flags &&& 0b00000000001L) <> 0x0L
    member x.IsPrefixDisplay = (flags &&& 0b00000000010L) <> 0x0L
    
    // This bit is not pickled, only used while establishing a type constructor. It is needed because the type constructor
    // is known to satisfy the default constructor constraint even before any of its members have been established.
    member x.PreEstablishedHasDefaultConstructor = (flags &&& 0b00000000100L) <> 0x0L

    // This bit represents an F# specific condition where a type has at least one constructor that may access
    // the 'this' pointer prior to successful initialization of the partial contents of the object. In this
    // case sub-classes must protect themselves against early access to their contents.
    member x.HasSelfReferentialConstructor = (flags &&& 0b00000001000L) <> 0x0L

    /// Get the flags as included in the F# binary metadata
    member x.PickledBits = (flags &&&  ~~~0b00000000100L)

type Entity = { (* mutable *) Data: EntityData }
and [<NoEquality; NoComparison>] EntityData = {
    /// The declared type parameters of the type
    (* mutable *)
    entity_typars: LazyWithContext<Typars, range>
    (* mutable *)
    entity_kind : TyparKind
    (* mutable *)
    entity_flags : EntityFlags
      
    /// The unique stamp of the "tycon blob". Note the same tycon in signature and implementation get different stamps 
    entity_stamp: stamp

    /// The name of the type, possibly with `n mangling 
    entity_logical_name: string

    /// The name of the type, possibly with `n mangling 
    (* mutable *)
    entity_compiled_name: string option

    /// The declaration location for the type constructor 
    entity_range: range
      
    /// The declared accessibility of the representation, not taking signatures into account 
    entity_tycon_repr_accessibility: Accessibility
      
    /// The declared attributes for the type 
    (* mutable *)
    entity_attribs: Attribs
                
    /// The declared representation of the type, i.e. record, union, class etc. 
    (* mutable *)
    entity_tycon_repr: TyconRepresentation option

    /// If non-None, indicates the type is an abbreviation for another type. 
    (* mutable *)
    entity_tycon_abbrev: typ option
      
    /// The methods and properties of the type 
    (* mutable *)
    entity_tycon_tcaug: TyconAugmentation
      
    /// Field used when the 'tycon' is really an exception definition 
    (* mutable *)
    entity_exn_info: ExceptionInfo
      
    /// This field is used when the 'tycon' is really a module definition. It holds statically nested type definitions and nested modules 
    (* mutable *)
    entity_modul_contents: Lazy<ModuleOrNamespaceType>

    /// The declared documentation for the type or module 
    entity_xmldoc : XmlDoc;
      
    /// The XML document signature for this entity
    (* mutable *)
    entity_xmldocsig : string;

    /// The stable path to the type, e.g. Microsoft.FSharp.Core.FSharpFunc`2 
    entity_pubpath : PublicPath option; 

    (* mutable *)
    entity_accessiblity: Accessibility; (*   how visible is this? *) 
 
    /// The stable path to the type, e.g. Microsoft.FSharp.Core.FSharpFunc`2 
    entity_cpath : CompilationPath option

    /// Used during codegen to hold the ILX representation indicating how to access the type 
    entity_il_repr_cache : CompiledTypeRepr cache
}
and CompilationPath = CompPath of ILScopeRef * (string * ModuleOrNamespaceKind) list
and 
    [<NoEquality; NoComparison>]
    // [<StructuredFormatDisplay("{Name}")>]
    Typar = {
        (* mutable *)
        Data: TyparData
        (* mutable *)
        AsType: typ
    }
and Typars = Typar list
and [<Sealed>] ModuleOrNamespaceType
    (
        kind: ModuleOrNamespaceKind,
        vals: QueueList<Val>,
        entities: QueueList<Entity>
    ) = class end

and [<NoEquality; NoComparison>] TyconAugmentation = {
    /// This is the value implementing the auto-generated comparison 
    /// semantics if any. It is not present if the type defines its own implementation 
    /// of IComparable or if the type doesn't implement IComparable implicitly. 
    (* mutable *)
    tcaug_compare : (ValRef * ValRef) option;
      
    /// This is the value implementing the auto-generated comparison
    /// semantics if any. It is not present if the type defines its own implementation
    /// of IStructuralComparable or if the type doesn't implement IComparable implicitly.
    (* mutable *)
    tcaug_compare_withc : ValRef option;                      

    /// This is the value implementing the auto-generated equality 
    /// semantics if any. It is not present if the type defines its own implementation 
    /// of Object.Equals or if the type doesn't override Object.Equals implicitly. 
    (* mutable *)
    tcaug_equals : (ValRef * ValRef) option;

    /// This is the value implementing the auto-generated comparison
    /// semantics if any. It is not present if the type defines its own implementation
    /// of IStructuralEquatable or if the type doesn't implement IComparable implicitly.
    (* mutable *)
    tcaug_hash_and_equals_withc : (ValRef * ValRef * ValRef) option;                                    

    /// True if the type defined an Object.GetHashCode method. In this 
    /// case we give a warning if we auto-generate a hash method since the semantics may not match up
    (* mutable *)
    tcaug_hasObjectGetHashCode : bool;             
      
    /// Properties, methods etc. in declaration order
    tcaug_adhoc_list : ResizeArray<ValRef>;
      
    /// Properties, methods etc. as lookup table
    (* mutable *)
    tcaug_adhoc : NameMultiMap<ValRef>;
      
    /// Interface implementations - boolean indicates compiler-generated 
    (* mutable *)
    tcaug_interfaces     : (typ * bool * range) list;  
      
    /// Super type, if any 
    (* mutable *)
    tcaug_super          : typ option;                 
      
    /// Set to true at the end of the scope where proper augmentations are allowed 
    (* mutable *)
    tcaug_closed         : bool;                       

    /// Set to true if the type is determined to be abstract 
    (* mutable *)
    tcaug_abstract : bool;                       
}
and PublicPath = PubPath of string[]
and ExceptionInfo =
    /// Indicates that an exception is an abbreviation for the given exception 
    | TExnAbbrevRepr of TyconRef 
    /// Indicates that an exception is shorthand for the given .NET exception type 
    | TExnAsmRepr of ILTypeRef
    /// Indicates that an exception carries the given record of values 
    | TExnFresh of TyconRecdFields
    /// Indicates that an exception is abstract, i.e. is in a signature file, and we do not know the representation 
    | TExnNone

and tinst = typ list

/// The algebra of types
and [<NoEquality; NoComparison>] typ =
    /// Indicates the type is a universal type, only used for types of values, members and record fields 
    | TType_forall of Typars * typ
    /// Indicates the type is a type application 
    | TType_app of TyconRef * tinst
    /// Indicates the type is a tuple type 
    | TType_tuple of typ list
    /// Indicates the type is a function type 
    | TType_fun of  typ * typ
    /// Indicates the type is a non-F#-visible type representing a "proof" that a union value belongs to a particular union case
    /// These types are not user-visible and will never appear as an inferred type. They are the types given to
    /// the temporaries arising out of pattern matching on union values.
    | TType_ucase of  UnionCaseRef * tinst
    /// Indicates the type is a variable type, whether declared, generalized or an inference type parameter  
    | TType_var of Typar 
    | TType_measure of MeasureExpr

and [<NoEquality; NoComparison>] TyconRepresentation = 
    /// Indicates the type is a class, struct, enum, delegate or interface 
    | TFsObjModelRepr    of TyconObjModelData
    /// Indicates the type is a record 
    | TRecdRepr          of TyconRecdFields
    /// Indicates the type is a discriminated union 
    | TFiniteUnionRepr   of TyconUnionData 
    /// Indicates the type is a .NET type 
    | TILObjModelRepr    of 
          // scope: 
          ILScopeRef * 
          // nesting:   
          ILTypeDef list * 
          // definition: 
          ILTypeDef 
    /// Indicates the type is implemented as IL assembly code using the given closed Abstract IL type 
    | TAsmRepr           of ILType
    /// Indicates the type is parameterized on a measure (e.g. float<_>) but erases to some other type (e.g. float)
    | TMeasureableRepr   of typ

and Accessibility = 
    /// Indicates the construct can only be accessed from any code in the given type constructor, module or assembly. [] indicates global scope. 
    | TAccess of CompilationPath list

and AttribExpr = AttribExpr of source: expr * evaluated: expr
and AttribKind = 
  /// Indicates an attribute refers to a type defined in an imported .NET assembly 
  | ILAttrib of ILMethodRef 
  /// Indicates an attribute refers to a type defined in an imported F# assembly 
  | FSAttrib of ValRef

/// Attrib(kind,unnamedArgs,propVal,appliedToAGetterOrSetter,range)
and Attrib = 
  | Attrib of TyconRef * kind: AttribKind * unnamedArgs: AttribExpr list * propVal: AttribNamedArg list * appliedToAGetterOrSetter: bool * range: range
  
and Attribs = Attrib list 

/// AttribNamedArg(name,type,isField,value)
and AttribNamedArg = AttribNamedArg of name: string * ``type``: typ * isField: bool * value: AttribExpr

and PickledModuleInfo = {
    mspec: ModuleOrNamespace
    compileTimeWorkingDir: string
    usesQuotations : bool
}
and ModuleOrNamespace = Entity

//let unpickleModuleInfo =
//    tuple4 unpickle_modul_spec u_string u_bool (u_space 3)
//    |>> fun (a, b, c, _space) -> { mspec = a; compileTimeWorkingDir = b; usesQuotations = c }

//let start2 = unpickleModuleInfo

open System.IO
//let bytes = File.ReadAllBytes(Path.Combine(__SOURCE_DIRECTORY__, "FSharpSignatureData.Sandbox.bin"))
let bytes = File.ReadAllBytes(Path.Combine(__SOURCE_DIRECTORY__, "FSharpSignatureData.FSharp.Compiler.bin"))


let (|EmptyView|_|) (x: View<_>) = if x.Array.Length = x.Index then Some() else None
let (Succ(data, EmptyView)) = parse start1 bytes
let {
        Item1 = ccuNameTab
        Item2 = ntycons, ntypars, nvals
        Item3 = stringTab
        Item4 = pubpathTab
        Item5 = nlerefTab
        Item6 = simpletypTab
        Item7 = phase1bytes 
    } = data
//let (Succ(data2, EmptyView)) = parse start2 phase1bytes


let f _ =
    let asm1 = Assembly.LoadFile(@"C:\Users\pc-2\project\AlpaVsix\Alpa\bin\Debug\Alpa.dll")
    let asm2 = Assembly.LoadFile(@"C:\Users\pc-2\project\Sandbox\Sandbox\bin\Debug\Sandbox.exe")
    let asm3 = Assembly.GetEntryAssembly()

    assemblies Set.empty asm2
    |> Seq.choose (fun a ->
        a.GetManifestResourceNames()
        |> Seq.tryFind (fun n -> (n+"").StartsWith("FSharpSignatureData."))
        |> function
        | Some n -> Some(a, n, a.GetManifestResourceStream n)
        | None -> None
    )
    |> Seq.iter (fun (a, n, s) ->
        let path = Path.Combine(__SOURCE_DIRECTORY__, n + ".bin")
        printfn "start %s" path
        use s = s
        use f = File.OpenWrite path
        do s.CopyTo f
        printfn "write %s" path
    )