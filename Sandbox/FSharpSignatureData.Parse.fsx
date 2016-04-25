module internal FSharpSignatureData.Parse
#load "./FSharpSignatureData.Parser.fsx"
open Parser


[<NoEquality; NoComparison>]
type InputTable<'T> = {
    itbl_name: string
    itbl_rows: 'T array
}
[<NoEquality; NoComparison>]
type Map<'a,'b> = {
    Link: 'a -> 'b -> unit
    Items: array<'a>
    Name: string
}
let lookup_uniq tbl n = 
    let arr = tbl.itbl_rows
    if n < 0 || n >= Array.length arr
    then
        // ufailwith st ("lookup_uniq in table "+tbl.itbl_name+" out of range, n = "+string n+ ", sizeof(tab) = " + string (Array.length arr))
        failwithf "lookup_uniq in table %s out of range, n = %d, sizeof(tab) = %d" tbl.itbl_name n (Array.length arr)
    else
        arr.[n]
        
[<Struct; StructuredFormatDisplay("{StructuredFormatDisplay}")>]
type Quote(value: string) = member __.StructuredFormatDisplay = value
type Ignore = Quote
type ILScopeRef = Quote
type EntityData = Quote
type Tycon = Quote
type TyparData = Quote
type Typar = Quote
type ValData = Quote
type Val = Quote
type PublicPath = Quote
type NonLocalEntityRef = Quote

[<NoEquality; NoComparison>]
type State = {
    iilscope: ILScopeRef

    itycons: Map<EntityData, Tycon>
    itypars: Map<TyparData, Typar>
    ivals: Map<ValData, Val>
    
    istrings: InputTable<string>
    ipubpaths: InputTable<PublicPath>
    inlerefs: InputTable<NonLocalEntityRef>
}

let u_byte : ByteParser<_,_> = anyChar
let u_bool = u_byte |>> fun b -> b = 1uy

[<GeneralizableValue>]
let prim_u_int32<'s> : ByteParser<_,'s> = pipe4 u_byte u_byte u_byte u_byte <| fun b0 b1 b2 b3 ->
        int b0 ||| (int b1 <<< 8) ||| (int b2 <<< 16) ||| (int b3 <<< 24)

[<GeneralizableValue>]        
let u_int32<'s> : ByteParser<_,'s> = u_byte >>= fun b0 ->
    if b0 <= 0x7Fuy then succ <| int b0
    elif b0 <= 0xBFuy then
        let b0 = b0 &&& 0x7Fuy
        u_byte |>> fun b1 -> (int b0 <<< 8) ||| int b1
    else
        prim_u_int32

let u_int8 = u_int32 |>> sbyte
let u_uint8 = u_byte |>> byte
let u_int16 = u_int32 |>> int16
let u_uint32 = u_int32 |>> uint32
let u_int = u_int32
        
[<GeneralizableValue>] 
let u_uint16<'s> : ByteParser<_,'s> = u_int32 |>> uint16
        
[<GeneralizableValue>] 
let u_int64<'s> : ByteParser<_,'s> = pipe2 u_int32 u_int32 <| fun b1 b2 ->
    (int64 b1 &&& 0xFFFFFFFFL) ||| (int64 b2 <<< 32)

let u_uint64 = u_int64 |>> uint64
let float_of_bits x = System.BitConverter.Int64BitsToDouble x
let float32_of_bits x = System.BitConverter.ToSingle(System.BitConverter.GetBytes(x: int32),0)

let u_single = u_int32 |>> float32_of_bits
let u_char = u_uint16 |>> (int32 >> char)

[<GeneralizableValue>] 
let u_bytes<'s> : ByteParser<_,'s> = u_int32 >>= fun n -> countArray n u_byte
        
[<GeneralizableValue>] 
let u_prim_string<'s> : ByteParser<_,'s> = u_int >>= utf8String

[<GeneralizableValue>]
let unreachable<'a> : 'a = failwith "unreachable"
let tagged f = u_byte >>= (int >> f)
let q format = Printf.ksprintf Quote format

let u_option p = tagged <| function
    | 0 -> succ None
    | 1 -> p |>> Some
    | n -> failf "u_option: found number %d" n

let u_array p = u_int >>= fun n -> countArray n p
let u_array_revi p f = u_int >>= fun n -> countRevIndexArray n p f

let u_list p = u_array p |>> Array.toList
let u_list_revi p f = u_array_revi p f |>> Array.toList

let u_lazy p =
    tuple7(
        
        // Read the number of bytes in the record
        prim_u_int32,

        // These are the ranges of OSGN nodes defined within the lazily read portion of the graph
        prim_u_int32,
        prim_u_int32,
        prim_u_int32,
        prim_u_int32,
        prim_u_int32,
        prim_u_int32
    )
    // ignore (len, otyconsIdx1, otyconsIdx2, otyparsIdx1, otyparsIdx2, ovalsIdx1, ovalsIdx2)
    >>. p
    |>> Lazy.CreateFromValue

let u_encoded_ccuref() = tagged <| function 
    | 0 -> u_prim_string
    | n -> failf "u_encoded_ccuref: found number 0x%02Xuy" n

let u_encoded_string = u_prim_string
let u_encoded_pubpath() = u_array u_int
let u_encoded_nleref() = u_int .>>. u_array u_int
let u_nleref = mapWithState u_int (fun n s -> lookup_uniq s.inlerefs n)
let u_encoded_simpletyp = u_int
let u_pubpath = mapWithState u_int (fun n s -> lookup_uniq s.ipubpaths n)

type pos = { posLine: int; posCol: int } 
type range = { rangeFile: string; rangeBegin: pos; rangeEnd: pos }

[<Sealed>]
type ident (text: string, range: range) = 
     member x.idText = text
     member x.idRange = range
     override x.ToString() = text

let mk_pos line column = { posLine = line; posCol = column }
let mk_range file p1 p2 = { rangeFile = file; rangeBegin = p1; rangeEnd = p2 }
let range0 = mk_range "unknown" (mk_pos 1 0) (mk_pos 1 80)

let u_pos = pipe2 u_int u_int mk_pos
let u_string = mapWithState u_int <| fun n state -> lookup_uniq state.istrings n
let u_strings = u_list u_string
let u_range = pipe3 u_string u_pos u_pos mk_range
let u_ident = pipe2 u_string u_range <| q"ident(%A, %A)"
let u_xmldoc =  u_array u_string |>> q"XmlDoc(%A)"

let u_ILPublicKey = tagged <| function
    | 0 -> u_bytes |>> q"PublicKey(%A)"
    | 1 -> u_bytes |>> q"PublicKeyToken(%A)"
    | x -> failf "u_ILPublicKey %d" x

let u_ILVersion = tuple4 u_uint16 u_uint16 u_uint16 u_uint16

let u_ILModuleRef = pipe3 u_string u_bool (u_option u_bytes) <| q"ILModuleRef.Create(%A, %A, %A)"

let u_ILAssemblyRef = tagged <| function
    | 0 -> 
        tuple6(u_string, u_option u_bytes, u_option u_ILPublicKey, u_bool, u_option u_ILVersion, u_option u_string)
        |>> fun (a, b, c, d, e, f) -> q"ILAssemblyRef.Create(%A,%A,%A,%A,%A,%A)" a b c d e f

    | x -> failf "u_ILAssemblyRef %d" x
    
let u_ILBasicCallConv = u_byte |>> function
    | 0uy -> q"CC_default"
    | 1uy -> q"CC_cdecl"
    | 2uy -> q"CC_stdcall"
    | 3uy -> q"CC_thiscall"
    | 4uy -> q"CC_fastcall"
    | 5uy -> q"CC_vararg"
    | _ -> unreachable

let u_ILHasThis = u_byte |>> function
    | 0uy -> q"CC_instance"
    | 1uy -> q"CC_instance_explicit"
    | 2uy -> q"CC_static"
    | _ -> unreachable
    
let u_ILVolatility = u_int |>> function
    | 0 -> q"Volatile"
    | 1 -> q"Nonvolatile"
    | x -> failwithf "u_ILVolatility %d" x

let u_ILReadonly = u_int |>> function
    | 0 -> q"ReadonlyAddress"
    | 1 -> q"NormalAddress"
    | x -> failwithf "u_ILReadonly %d" x

let u_ILBasicType = u_int |>> function
    | 0 -> q"DT_R"
    | 1 -> q"DT_I1"
    | 2 -> q"DT_U1"
    | 3 -> q"DT_I2"
    | 4 -> q"DT_U2"
    | 5 -> q"DT_I4"
    | 6 -> q"DT_U4"
    | 7 -> q"DT_I8"
    | 8 -> q"DT_U8"
    | 9 -> q"DT_R4"
    | 10 -> q"DT_R8"
    | 11 -> q"DT_I"
    | 12 -> q"DT_U"
    | 13 -> q"DT_REF"
    | x -> failwithf "u_ILBasicType %d" x
    
let u_ILCallConv = pipe2 u_ILHasThis u_ILBasicCallConv <| q"Callconv(%A, %A)"
let u_ILScopeRef = 
    let readBody tag =
        match int tag with
        | 0 -> succ <| q"ScopeRef_local"
        | 1 -> u_ILModuleRef |>> q"ScopeRef_module(%A)"
        | 2 -> u_ILAssemblyRef |>> q"ScopeRef_assembly(%A)"
        | _ -> failf "u_ILScopeRef %d" tag
    mapWithState (tagged readBody) <| fun res state ->
        q"rescope_scoref %A %A" state.iilscope res

let u_ILTypeRef = pipe3 u_ILScopeRef u_strings u_string <| q"ILTypeRef(%A, %A, %A)"
let u_ILArrayShape = u_list (u_option u_int32 .>>. u_option u_int32) |>> q"ILArrayShape(%A)"

let rec u_ILType xs =
    tagged (function
        | 0 -> succ <| q"Type_void"
        | 1 -> pipe2 u_ILArrayShape u_ILType <| q"Type_array(%A, %A)"
        | 2 -> u_ILTypeSpec |>> q"Type_value(%A)"
        | 3 -> u_ILTypeSpec |>> q"Type_boxed(%A)"
        | 4 -> u_ILType |>> q"Type_ptr(%A)"
        | 5 -> u_ILType |>> q"Type_byref(%A)"
        | 6 -> u_ILCallSig |>> q"Type_fptr(%A)"
        | 7 -> u_uint16 |>> q"Type_tyvar(%A)"
        | 8 -> pipe3 u_bool u_ILTypeRef u_ILType <| q"Type_modified(%A, %A, %A)"
        | x -> failf "u_ILType %d" x
    ) xs
    
and u_ILTypes = u_list u_ILType
and u_ILTypeSpec = pipe2 u_ILTypeRef u_ILTypes <| q"ILTypeSpec.Create(%A, %A)"
and u_ILCallSig = pipe3 u_ILCallConv u_ILTypes u_ILType <| q"{ callsigCallconv = %A; callsigArgs = %A; callsigReturn = %A }"

let u_ILMethodRef = 
    tuple6(u_ILTypeRef, u_ILCallConv, u_int, u_string, u_ILTypes, u_ILType)
    |>> fun (x1, x2, x3, x4, x5, x6) -> q"ILMethodRef.Create(%A, %A, %d, %A, %A, %A)" x1 x2 x3 x4 x5 x6
    
let u_ILMethodSpec = pipe3 u_ILMethodRef u_ILType u_ILTypes <| q"ILMethodSpec.Create(%A, %A, %A)"

let u_ILFieldRef = pipe3 u_ILTypeRef u_string u_ILType <| q"{ frefParent = %A; frefName = %A; frefType = %A }"
let u_ILFieldSpec = pipe2 u_ILFieldRef u_ILType <| q"{ fspecFieldRef = %A; fspecEnclosingType = %A }"

type ITag =
    | Inop = 0 
    | Ildarg = 1
    | Ildnull = 2 
    | Iilzero = 3
    | Icall = 4 
    | Iadd = 5
    | Isub = 6 
    | Imul = 7
    | Idiv = 8 
    | Idiv_un = 9 
    | Irem = 10 
    | Irem_un = 11 
    | Iand = 12 
    | Ior = 13 
    | Ixor = 14 
    | Ishl = 15 
    | Ishr = 16 
    | Ishr_un = 17 
    | Ineg = 18 
    | Inot = 19 
    | Iconv = 20
    | Iconv_un = 21 
    | Iconv_ovf = 22
    | Iconv_ovf_un = 23
    | Icallvirt = 24 
    | Ildobj = 25 
    | Ildstr = 26 
    | Icastclass = 27 
    | Iisinst = 28 
    | Iunbox = 29 
    | Ithrow = 30 
    | Ildfld = 31 
    | Ildflda = 32 
    | Istfld = 33 
    | Ildsfld = 34 
    | Ildsflda = 35 
    | Istsfld = 36 
    | Istobj = 37 
    | Ibox = 38 
    | Inewarr = 39 
    | Ildlen = 40 
    | Ildelema = 41 
    | Ickfinite = 42 
    | Ildtoken = 43 
    | Iadd_ovf = 44 
    | Iadd_ovf_un = 45 
    | Imul_ovf = 46 
    | Imul_ovf_un = 47 
    | Isub_ovf = 48 
    | Isub_ovf_un = 49 
    | Iceq = 50
    | Icgt = 51
    | Icgt_un = 52
    | Iclt = 53
    | Iclt_un = 54
    | Ildvirtftn = 55 
    | Ilocalloc = 56 
    | Irethrow = 57 
    | Isizeof = 58
    | Ildelem_any = 59
    | Istelem_any = 60
    | Iunbox_any = 61
    | Ildlen_multi = 62

let decoders =
    [|
        ITag.Ildarg, u_uint16 |>> q"I_ldarg(%A)";
        ITag.Icall, u_ILMethodSpec |>> q"I_call(Normalcall, %A, None)";
        ITag.Icallvirt, u_ILMethodSpec |>> q"I_callvirt(Normalcall, %A, None)";
        ITag.Ildvirtftn, u_ILMethodSpec |>> q"I_ldvirtftn(%A)";
        ITag.Iconv, u_ILBasicType |>> q"I_arith(AI_conv(%A))";
        ITag.Iconv_ovf, u_ILBasicType |>> q"I_arith(AI_conv_ovf(%A))";
        ITag.Iconv_ovf_un, u_ILBasicType |>> q"I_arith(AI_conv_ovf_un(%A))";
        ITag.Ildfld, pipe2 u_ILVolatility u_ILFieldSpec <| q"I_ldfld(Aligned, %A, %A)";
        ITag.Ildflda, u_ILFieldSpec |>> q"I_ldflda(%A)";
        ITag.Ildsfld, pipe2 u_ILVolatility u_ILFieldSpec <| q"I_ldsfld(%A, %A)";
        ITag.Ildsflda, u_ILFieldSpec |>> q"I_ldsflda(%A)";
        ITag.Istfld, pipe2 u_ILVolatility u_ILFieldSpec <| q"I_stfld(Aligned, %A, %A)";
        ITag.Istsfld, pipe2 u_ILVolatility u_ILFieldSpec <| q"I_stsfld(%A, %A)";
        ITag.Ildtoken, u_ILType |>> q"I_ldtoken(Token_type(%A))";
        ITag.Ildstr, u_string |>> q"I_ldstr(%A)";
        ITag.Ibox, u_ILType |>> q"I_box(%A)";
        ITag.Iunbox, u_ILType |>> q"I_unbox(%A)";
        ITag.Iunbox_any, u_ILType |>> q"I_unbox_any(%A)";
        ITag.Inewarr, pipe2 u_ILArrayShape u_ILType <| q"I_newarr(%A, %A)";
        ITag.Istelem_any, pipe2 u_ILArrayShape u_ILType <| q"I_stelem_any(%A, %A)";
        ITag.Ildelem_any, pipe2 u_ILArrayShape u_ILType <| q"I_ldelem_any(%A, %A)";
        ITag.Ildelema, pipe3 u_ILReadonly u_ILArrayShape u_ILType <| q"I_ldelema(%A, %A, %A)";
        ITag.Icastclass, u_ILType |>> q"I_castclass(%A)";
        ITag.Iisinst, u_ILType |>> q"I_isinst(%A)";
        ITag.Ildobj, u_ILType |>> q"I_ldobj(Aligned, Nonvolatile, %A)";
        ITag.Istobj, u_ILType |>> q"I_stobj(Aligned, Nonvolatile, %A)";
        ITag.Isizeof, u_ILType |>> q"I_sizeof(%A)";
        ITag.Ildlen_multi, pipe2 u_int32 u_int32 <| q"EI_ldlen_multi(%A, %A)";
        ITag.Iilzero, u_ILType |>> q"EI_ilzero(%A)";
    |] 

let simple_instrs = 
    [|  
        ITag.Iadd, q"I_arith(AI_add)";
        ITag.Iadd_ovf, q"I_arith(AI_add_ovf)";
        ITag.Iadd_ovf_un, q"I_arith(AI_add_ovf_un)";
        ITag.Iand, q"I_arith(AI_and)";  
        ITag.Idiv, q"I_arith(AI_div)"; 
        ITag.Idiv_un, q"I_arith(AI_div_un)";
        ITag.Iceq, q"I_arith(AI_ceq)";  
        ITag.Icgt, q"I_arith(AI_cgt)" ;
        ITag.Icgt_un, q"I_arith(AI_cgt_un)";
        ITag.Iclt, q"I_arith(AI_clt)";
        ITag.Iclt_un, q"I_arith(AI_clt_un)";
        ITag.Imul, q"I_arith(AI_mul)"  ;
        ITag.Imul_ovf, q"I_arith(AI_mul_ovf)";
        ITag.Imul_ovf_un, q"I_arith(AI_mul_ovf_un)";
        ITag.Irem, q"I_arith(AI_rem)"  ;
        ITag.Irem_un, q"I_arith(AI_rem_un)" ; 
        ITag.Ishl, q"I_arith(AI_shl)" ; 
        ITag.Ishr, q"I_arith(AI_shr)" ; 
        ITag.Ishr_un, q"I_arith(AI_shr_un)";
        ITag.Isub, q"I_arith(AI_sub)"  ;
        ITag.Isub_ovf, q"I_arith(AI_sub_ovf)";
        ITag.Isub_ovf_un, q"I_arith(AI_sub_ovf_un)"; 
        ITag.Ixor, q"I_arith(AI_xor)";  
        ITag.Ior, q"I_arith(AI_or)";     
        ITag.Ineg, q"I_arith(AI_neg)";     
        ITag.Inot, q"I_arith(AI_not)";     
        ITag.Ildnull, q"I_arith(AI_ldnull)";   
        ITag.Ickfinite, q"I_arith(AI_ckfinite)";
        ITag.Inop, q"I_arith(AI_nop)";
        ITag.Ilocalloc, q"I_localloc";
        ITag.Ithrow, q"I_throw";
        ITag.Ildlen, q"I_ldlen";
        ITag.Irethrow, q"I_rethrow";
    |]

let decode_tab =
    let tab = Array.init 256 <| failf "no decoder for instruction %d"
    let add_instr (icode, f) = tab.[int icode] <- f
    Array.iter add_instr decoders;
    Array.iter (fun (icode,mk) -> add_instr (icode,(fun _ -> mk))) simple_instrs;
    tab

let u_ILInstr = u_byte >>= (int >> Array.get decode_tab)

let u_qlist uv = u_list uv |>> q"QueueList.ofList(%A)"

let u_member_kind = u_byte |>> function
    | 0uy -> q"MemberKindMember"
    | 1uy -> q"MemberKindPropertyGet"
    | 2uy -> q"MemberKindPropertySet"
    | 3uy -> q"MemberKindConstructor"
    | 4uy -> q"MemberKindClassConstructor"
    | _ -> unreachable

let u_MemberFlags = 
    tuple6(u_bool, u_bool, u_bool, u_bool, u_bool, u_member_kind) |>> fun (x2, _x3UnusedBoolInFormat, x4, x5, x6, x7) ->
        q"{ MemberIsInstance = %b; MemberIsDispatchSlot = %b; MemberIsOverrideOrExplicitImpl = %b; MemberIsFinal = %b; MemberKind = %A }" x2 x4 x5 x6 x7

let u_osgn_decl getMap u = pipe3 getState u_int u <| fun state idx data ->
    let map = getMap state
    let res = Array.get map.Items idx
    map.Link res data
    res
    
let u_osgn_ref { Items = arr; Name = nm } = u_int >>= fun n ->
    if n < 0 || n >= Array.length arr
    then fail  <| sprintf "u_osgn_ref: out of range, table = %s, n = %d" nm n
    else succ <| Array.get arr n

let u_local_item_ref tab = u_osgn_ref tab
let u_tcref = tagged <| function
    | 0 -> getState >>= fun s -> u_local_item_ref s.itycons |>> q"ERef_local(%A)"
    | 1 -> u_nleref |>> q"ERef_nonlocal(%A)"
    | x -> failf "u_item_ref %A" x

let u_ucref = pipe2 u_tcref u_string <| q"UCRef(%A, %A)"
let u_rfref = pipe2 u_tcref u_string <| q"RFRef(%A, %A)"
    
let u_kind = u_byte |>> fun x ->
    match int x with
    | 0 -> q"KindType"
    | 1 -> q"KindMeasure"
    | _ -> failwithf "u_kind %d" x

let _fill_u_attribs, u_attribs = hole()
let _fill_u_typ, u_typ = hole()
let _fill_u_entity_spec_data, u_entity_spec_data = hole()

let u_typs = u_list u_typ

let u_TopTyparInfo = pipe2 u_ident u_kind <| q"TopTyparInfo(%A, %A)"

let u_TopArgInfo = pipe2 u_attribs (u_option u_ident) <| fun a b ->
    match a, b with
    | [], None -> q"TopValInfo.unnamedTopArg1"
    | _ -> q"{ Attribs = %A; Name = %A }" a b

let u_ValTopReprInfo = 
    pipe3
        (u_list u_TopTyparInfo)
        (u_list (u_list u_TopArgInfo))
        u_TopArgInfo
        <| q"TopValInfo(%A, %A, %A)"

let u_istype = u_byte >>= function
    | 0uy -> succ <| q"FSharpModuleWithSuffix"
    | 1uy -> succ <| q"FSharpModule"
    | 2uy -> succ <| q"Namespace"
    | x -> failf "u_istype %d" x
    
let u_ranges = u_option (u_range .>>. u_range)
let u_cpath = pipe2 u_ILScopeRef (u_list (u_string .>>. u_istype)) <| q"CompPath(%A, %A)"

// expr
let u_const = tagged <| function
    | 0 -> u_bool |>> q"TConst_bool(%b)"
    | 1 -> u_int8 |>> q"TConst_sbyte(%dy)"
    | 2 -> u_uint8 |>> q"TConst_byte(%duy)"
    | 3 -> u_int16 |>> q"TConst_int16(%ds)"
    | 4 -> u_uint16 |>> q"TConst_uint16(%dus)"
    | 5 -> u_int32 |>> q"TConst_int32(%d)"
    | 6 -> u_uint32 |>> q"TConst_uint32(%du)"
    | 7 -> u_int64 |>> q"TConst_int64(%dL)"
    | 8 -> u_uint64 |>> q"TConst_uint64(%dUL)"
    | 9 -> u_int64 |>> q"TConst_nativeint(%dL)"
    | 10 -> u_uint64 |>> q"TConst_unativeint(%dUL)"
    | 11 -> u_single |>> q"TConst_float32(%ff)"
    | 12 -> u_int64 |>> (float_of_bits >> q"TConst_float(%f)")
    | 13 -> u_char |>> q"TConst_char(%A)"
    | 14 -> u_string |>> q"TConst_string(%A)"
    | 15 -> succ <| q"TConst_unit"
    | 16 -> succ <| q"TConst_zero"
    | 17 -> u_array u_int32 |>> (System.Decimal >> q"TConst_decimal(%A)")
    | x -> failf "u_const %d" x
    
let u_access = u_list u_cpath |>> function
    | [] -> q"taccessPublic" // save unnecessary allocations 
    | res -> q"TAccess(%A)" res

let u_recdfield_spec = 
    pipe5
        u_bool
        u_bool
        u_typ
        u_bool
        (
            tuple7(
                u_bool,
                u_option u_const,
                u_ident,
                u_attribs,
                u_attribs,
                u_string,
                u_access
            )
        )
    <| fun a b c1 c2 (c2b,c3,d,e1,e2,f,g) ->
        q"{
            rfield_mutable = %A;  
            rfield_volatile = %A;  
            rfield_type = %A;
            rfield_static = %A;
            rfield_secret = %A;
            rfield_const = %A;
            rfield_id = %A;
            rfield_pattribs = %A;
            rfield_fattribs = %A;
            rfield_xmldoc = emptyXmlDoc;
            rfield_xmldocsig = %A;
            rfield_access = %A;
        }" a b c1 c2 c2b c3 d e1 e2 f g

let u_rfield_table = u_list u_recdfield_spec |>> q"MakeRecdFieldsTable(%A)"
let u_exnc_repr = tagged <| function
    | 0 -> u_tcref |>> q"TExnAbbrevRepr(%A)"
    | 1 -> u_ILTypeRef |>> q"TExnAsmRepr(%A)"
    | 2 -> u_rfield_table |>> q"TExnFresh(%A)"
    | 3 -> succ <| q"TExnNone"
    | x -> failf "u_exnc_repr %d" x

let u_nonlocal_val_ref = 
    tuple6( 
        u_tcref,
        u_option u_string,
        u_bool,
        u_string,
        u_int,
        u_option u_typ
    )
    |>> fun (a, b1, b2, b3, c, d) ->
        q"{ EnclosingEntity = %A; ItemKey = ValLinkageFullKey({ MemberParentMangledName = %A; MemberIsOverride = %b; LogicalName = %A; TotalArgCount = %d }, %A) }"
            a b1 b2 b3 c d
  
let u_vref = tagged <| function
    | 0 -> getState >>= fun s -> u_local_item_ref s.ivals |>> q"VRef_local(%A)"
    | 1 -> u_nonlocal_val_ref |>> q"VRef_nonlocal(%A)"
    | x -> failf "u_item_ref %d" x

let u_vrefs = u_list u_vref 


let u_member_kind = u_byte |>> fun x ->
    match int x with
    | 0 -> q"MemberKindMember"
    | 1 -> q"MemberKindPropertyGet"
    | 2 -> q"MemberKindPropertySet"
    | 3 -> q"MemberKindConstructor"
    | 4 -> q"MemberKindClassConstructor"
    | _ -> failwithf "u_member_kind %d" x

let u_trait_sln = tagged <| function
    | 0 -> pipe4 u_typ (u_option u_ILTypeRef) u_ILMethodRef u_typs <| q"ILMethSln(%A, %A, %A, %A)"
    | 1 -> pipe3 u_typ u_vref u_typs <| q"FSMethSln(%A, %A, %A)"
    | 2 -> succ <| q"BuiltInSln"
    | x -> failf "u_trait_sln %d" x

let u_trait = 
    tuple6(u_typs, u_string, u_MemberFlags, u_typs, u_option u_typ, u_option u_trait_sln)
    |>> fun (a, b, c, d, e, f) -> q"TTrait(%A, %A, %A, %A, %A, %A)" a b c d e (ref f)

let u_typar_constraint = 
    let u = function
        | 0 -> u_typ |>> fun a _ -> q"TTyparCoercesToType(%A, %A)" a range0
        | 1 -> u_trait |>> fun a _ -> q"TTyparMayResolveMemberConstraint(%A, %A)" a range0
        | 2 -> u_typ |>> fun a ridx -> q"TTyparDefaultsToType(%A, %A, %A)" ridx a range0
        | 3 -> succ <| fun _ -> q"TTyparSupportsNull(%A)" range0
        | 4 -> succ <| fun _ -> q"TTyparIsNotNullableValueType(%A)" range0
        | 5 -> succ <| fun _ -> q"TTyparIsReferenceType(%A)" range0
        | 6 -> succ <| fun _ -> q"TTyparRequiresDefaultConstructor(%A)" range0
        | 7 -> u_typs |>> fun a _ -> q"TTyparSimpleChoice(%A, %A)" a range0
        | 8 -> u_typ |>> fun a _ -> q"TTyparIsEnum(%A, %A)" a range0
        | 9 -> u_typ .>>. u_typ |>> fun (a, b) _ -> q"TTyparIsDelegate(%A, %A, %A)" a b range0
        | 10 -> succ <| fun _ -> q"TTyparSupportsComparison(%A)" range0
        | 11 -> succ <| fun _ -> q"TTyparSupportsEquality(%A)" range0
        | 12 -> succ <| fun _ -> q"TTyparIsUnmanaged(%A)" range0
        | x -> failf "u_typar_constraint %d" x

    tagged u

let u_typar_constraints = u_list_revi u_typar_constraint (<|)
let u_typar_spec_data =
    pipe5 u_ident u_attribs u_int64 u_typar_constraints u_xmldoc
    <| q"{ typar_id = %A; typar_il_name = None; typar_stamp = newStamp(); typar_attribs = %A; typar_flags = TyparFlags(int32 %A); typar_constraints = %A; typar_solution = None; typar_xmldoc = %A }"

let u_typar_spec = u_osgn_decl (fun s -> s.itypars) u_typar_spec_data
let u_typar_specs = u_list u_typar_spec

let u_recdfield_spec = 
    pipe5
        u_bool
        u_bool
        u_typ
        u_bool
        (
            tuple7(
                u_bool, 
                u_option u_const,
                u_ident,
                u_attribs,
                u_attribs,
                u_string,
                u_access
            )
        ) 
    <| fun a b c1 c2 (c2b,c3,d,e1,e2,f,g) ->
        q"{
            rfield_mutable = %A;
            rfield_volatile = %A;
            rfield_type = %A;
            rfield_static = %A;
            rfield_secret = %A;
            rfield_const = %A;
            rfield_id = %A;
            rfield_pattribs = %A;
            rfield_fattribs = %A;
            rfield_xmldoc = emptyXmlDoc;
            rfield_xmldocsig = %A;
            rfield_access = %A;
        }" a b c1 c2 c2b c3 d e1 e2 f g

let u_rfield_table = u_list u_recdfield_spec |>> q"MakeRecdFieldsTable(%A)"

let u_unioncase_spec = 
    tuple7(u_rfield_table, u_typ, u_string, u_ident, u_attribs, u_string, u_access)
    |>> fun (a,b,c,d,e,f,i) ->
        q"{ ucase_rfields = %A; ucase_rty = %A; ucase_il_name = %A; ucase_id = %A; ucase_attribs = %A; ucase_xmldoc = emptyXmlDoc; ucase_xmldocsig = %A; ucase_access = %A }"
            a b c d e f i
         
let u_slotparam = 
    tuple6(u_option u_string, u_typ, u_bool, u_bool, u_bool, u_attribs)
    |>> fun (a,b,c,d,e,f) -> q"TSlotParam(%A, %A, %A, %A, %A, %A)" a b c d e f

let u_slotsig = 
    tuple6(u_string, u_typ, u_typar_specs, u_typar_specs, u_list (u_list u_slotparam), u_option u_typ)
    |>> fun (a,b,c,d,e,f) -> q"TSlotSig(%A, %A, %A, %A, %A, %A)" a b c d e f

let u_tycon_objmodel_kind = tagged <| function
    | 0 -> succ <| q"TTyconClass"
    | 1 -> succ <| q"TTyconInterface"
    | 2 -> succ <| q"TTyconStruct"
    | 3 -> u_slotsig |>> q"TTyconDelegate(%A)"
    | 4 -> succ <| q"TTyconEnum"
    | x -> failf "u_tycon_objmodel_kind %d" x

let u_tycon_objmodel_data = 
    pipe3 u_tycon_objmodel_kind u_vrefs u_rfield_table
    <| q"{ fsobjmodel_kind = %A; fsobjmodel_vslots = %A; fsobjmodel_rfields = %A }"
  
let u_tycon_repr = tagged <| function
    | 0 -> u_rfield_table |>> q"TRecdRepr(%A)"
    | 1 -> u_list u_unioncase_spec |>> q"MakeUnionRepr(%A)"
    | 2 -> u_ILType |>> q"TAsmRepr(%A)"
    | 3 -> u_tycon_objmodel_data |>> q"TFsObjModelRepr(%A)"
    | 4 -> u_typ |>> q"TMeasureableRepr(%A)"
    | x -> failf "u_tycon_repr %d" x
    
let u_dummy_range = succ range0
let u_space n = skipCount n anyChar
let u_tcaug =
    pipe5
        (u_option (u_vref .>>. u_vref))
        (u_option u_vref)
        (u_option (tuple3 u_vref u_vref u_vref))
        (u_option (u_vref .>>. u_vref))
        (
            tuple5
                (u_list (u_string .>>. u_vref))
                (u_list (tuple3 u_typ u_bool u_dummy_range))
                (u_option u_typ)
                u_bool 
                (u_space 1)
        )
    <| fun a1 a2 a3 b2 (c,d,e,g,_space) ->
        q"{
            tcaug_compare = %A;
            tcaug_compare_withc = %A;
            tcaug_hash_and_equals_withc = %A;
            tcaug_equals = %A;

            // only used for code generation and checking - hence don't care about the values when reading back in
            tcaug_hasObjectGetHashCode = false;
            tcaug_adhoc_list = new ResizeArray<_> (List.map snd %A);
            tcaug_adhoc = NameMultiMap.ofList %A;
            tcaug_interfaces = %A;
            tcaug_super = %A;
            // pickled type definitions are always closed (i.e. no more intrinsic members allowed)
            tcaug_closed = true;
            tcaug_abstract = %A;
        }" a1 a2 a3 b2 c c d e g



let u_member_info = 
    pipe4 u_tcref u_MemberFlags (u_list u_slotsig) u_bool
    <| q"{ ApparentParent = %A; MemberFlags = %A; ImplementedSlotSigs = %A; IsImplemented = %A; }"
        
let u_tycon_spec = u_osgn_decl (fun state -> state.itycons) u_entity_spec_data

let u_parentref = tagged <| function
    | 0 -> succ <| q"ParentNone"
    | 1 -> u_tcref |>> q"Parent(%A)"
    | x -> failf "u_attribkind %d" x

let u_ValData =
    tuple7(
        u_string,
        u_option u_string,
        u_ranges,
        u_typ,
        u_int64,
        u_option u_member_info,
        tuple7(
            u_attribs,
            u_option u_ValTopReprInfo,
            u_string,
            u_access,
            u_parentref,
            u_option u_const,
            u_space 1
        )
    )
    |>> fun (x1,x1z,x1a,x2,x4,x8,(x9,x10,x12,x13,x13b,x14,_space)) ->
        let x1aa = match x1a with None -> range0 | Some(a,_) -> a
        let x1ab = match x1a with None -> range0 | Some(_,b) -> b
        q"{
            val_logical_name = %A;
            val_compiled_name = %A;
            val_range = %A;
            val_defn_range = %A;
            val_type = %A;
            val_stamp = newStamp();
            val_flags = ValFlags(%A);
            val_defn = None;
            val_member_info = %A;
            val_attribs = %A;
            val_top_repr_info = %A;
            val_xmldoc = emptyXmlDoc;
            val_xmldocsig = %A;
            val_access = %A;
            val_actual_parent = %A;
            val_const = %A;
        }" x1 x1z x1aa x1ab x2 x4 x8 x9 x10 x12 x13 x13b x14

let u_Val = u_osgn_decl (fun s -> s.ivals) u_ValData
let u_Vals = u_list u_Val

let u_modul_typ =
    pipe3 u_istype (u_qlist u_Val) (u_qlist u_tycon_spec)
        <| q"ModuleOrNamespaceType(%A, %A, %A)"

    
let u_attribkind = tagged <| function
    | 0 -> u_ILMethodRef |>> q"ILAttrib(%A)"
    | 1 -> u_vref |>> q"FSAttrib(%A)"
    | x -> failf "u_attribkind %d" x
    
let u_vrefFlags = tagged <| function
    | 0 -> succ <| q"NormalValUse"
    | 1 -> succ <| q"CtorValUsedAsSuperInit"
    | 2 -> succ <| q"CtorValUsedAsSelfInit"
    | 3 -> u_typ |>> q"PossibleConstrainedCall(%A)"
    | 4 -> succ <| q"VSlotDirectCall"
    | x -> failf "u_vrefFlags %d" x
    
let u_lval_op_kind = u_byte |>> fun x ->
    match int x with
    | 0 -> q"LGetAddr"
    | 1 -> q"LByrefGet"
    | 2 -> q"LSet"
    | 3 -> q"LByrefSet"
    | _ -> failwithf "uval_op_kind %d" x

let u_op = tagged <| function
    | 0 -> u_ucref |>> q"TOp_ucase(%A)"
    | 1 -> u_tcref |>> q"TOp_exnconstr(%A)"
    | 2 -> succ <| q"TOp_tuple"
    | 3 -> u_tcref |>> q"TOp_recd(RecdExpr, %A)"
    | 4 -> u_rfref |>> q"TOp_rfield_set(%A)"
    | 5 -> u_rfref |>> q"TOp_rfield_get(%A)"
    | 6 -> u_tcref |>> q"TOp_ucase_tag_get(%A)"
    | 7 -> pipe2 u_ucref u_int <| q"TOp_ucase_field_get(%A, %A)"
    | 8 -> pipe2 u_ucref u_int <| q"TOp_ucase_field_set(%A, %A)"
    | 9 -> pipe2 u_tcref u_int <| q"TOp_exnconstr_field_get(%A, %A)"
    | 10 -> pipe2 u_tcref u_int <| q"TOp_exnconstr_field_set(%A, %A)"
    | 11 -> u_int |>> q"TOp_tuple_field_get(%A)"
    | 12 -> pipe2 (u_list u_ILInstr) u_typs <| q"TOp_asm(%A, %A)"
    | 13 -> succ <| q"TOp_get_ref_lval"
    | 14 -> u_ucref |>> q"TOp_ucase_proof(%A)"
    | 15 -> succ <| q"TOp_coerce"
    | 16 -> u_trait |>> q"TOp_trait_call(%A)"
    | 17 -> pipe2 u_lval_op_kind u_vref <| q"TOp_lval_op(%A, %A)"
    | 18 ->
        tuple7(u_bool, u_bool, u_bool, u_bool, u_vrefFlags, u_bool, tuple5 u_bool u_ILMethodRef u_typs u_typs u_typs)
        |>> fun (x1,x2,x3,x4,x5,x6,(x7,x8,x9,x10,x11)) ->
            q"TOp_ilcall(%A, %A, %A, %A, %A, %A, %A, %A, %A, %A, %A)" x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11

    | 19 -> succ <| q"TOp_array"
    | 20 -> succ <| q"TOp_while(NoSequencePointAtWhileLoop, NoSpecialWhileLoopMarker)"
    | 21 ->
        let toDir = function
            | 0 -> q"FSharpForLoopUp"
            | 1 -> q"CSharpForLoopUp"
            | 2 -> q"FSharpForLoopDown"
            | _ -> failwith "unknown for loop"

        u_int |>> (toDir >> q"TOp_for(NoSequencePointAtForLoop, %A)")

    | 22 -> u_bytes |>> q"TOp_bytes(%A)"
    | 23 -> succ <| q"TOp_try_catch(NoSequencePointAtTry, NoSequencePointAtWith)"
    | 24 -> succ <| q"TOp_try_finally(NoSequencePointAtTry, NoSequencePointAtFinally)"
    | 25 -> u_rfref |>> q"TOp_field_get_addr(%A)"
    | 26 -> u_array u_uint16 |>> q"TOp_uint16s(%A)"
    | 27 -> succ <| q"TOp_reraise"
    | x -> failf "u_op %d" x


let _fill_u_expr, u_expr = hole()
let u_Exprs = u_list u_expr

_fill_u_expr := tagged <| function
    | 0 -> pipe3 u_const u_dummy_range u_typ <| q"TExpr_const(%A, %A, %A)"
    | 1 -> pipe3 u_vref u_vrefFlags u_dummy_range <| q"TExpr_val(%A, %A, %A)"
    | 2 -> pipe4 u_op u_typs u_Exprs u_dummy_range <| q"TExpr_op(%A, %A, %A, %A)"
    | 3 ->
        let c = u_int >>= function
            | 0 -> succ <| q"NormalSeq"
            | 1 -> succ <| q"ThenDoSeq"
            | x -> failf "specialSeqFlag %d" x

        pipe4 u_expr u_expr c u_dummy_range <|
            q"TExpr_seq(%A, %A, %A, SuppressSequencePointOnExprOfSequential, %A)"

    | 4 ->
        tuple6(
            u_option u_Val,
            u_option u_Val,
            u_Vals,
            u_expr,
            u_dummy_range,
            u_typ
        )
        |>> fun (a0, b0, b1, c, d, e) ->
            q"TExpr_lambda(newUnique(), %A, %A, %A, %A, %A, %A, SkipFreeVarsCache())" a0 b0 b1 c d e

    | 5 ->
        pipe4 u_typar_specs u_expr u_dummy_range u_typ <|
            q"TExpr_tlambda(newUnique(), %A, %A, %A, %A, SkipFreeVarsCache())"

    | 6 -> pipe5 u_expr u_typ u_typs u_Exprs u_dummy_range <| q"TExpr_app(%A, %A, %A, %A, %A)"
    | 7 -> pipe3 u_binds u_expr u_dummy_range <| q"TExpr_letrec(%A, %A, %A, NewFreeVarsCache())"
//    | 8 ->  let a = u_bind st
//            let b = u_expr st
//            let c = u_dummy_range st
//            TExpr_let (a,b,c,NewFreeVarsCache()) 
//    | 9 ->  let a = u_dummy_range st
//            let b = u_dtree st
//            let c = u_targets st
//            let d = u_dummy_range st
//            let e = u_typ st
//            TExpr_match (NoSequencePointAtStickyBinding,a,b,c,d,e,SkipFreeVarsCache()) 
//    | 10 -> let b = u_typ st
//            let c = (u_option u_Val) st
//            let d = u_expr st
//            let e = u_methods st
//            let f = u_intfs st
//            let g = u_dummy_range st
//            TExpr_obj (newUnique(),b,c,d,e,f,g,SkipFreeVarsCache())
//    | 11 -> let a = u_constraints st
//            let b = u_expr st
//            let c = u_expr st
//            let d = u_dummy_range st
//            TExpr_static_optimization (a,b,c,d)
//    | 12 -> let a = u_typar_specs st
//            let b = u_expr st
//            let c = u_dummy_range st
//            TExpr_tchoose (a,b,c)
//    | 13 -> let b = u_expr st
//            let c = u_dummy_range st
//            let d = u_typ st
//            TExpr_quote (b,ref None,c,d)
//    | _ -> ufailwith st "u_expr" 

let u_attrib_expr = pipe2 u_expr u_expr <| q"AttribExpr(%A, %A)"
let u_attrib_arg = pipe4 u_string u_typ u_bool u_attrib_expr <| q"AttribNamedArg(%A, %A, %A, %A)"
let u_attrib = 
    tuple6(u_tcref, u_attribkind, u_list u_attrib_expr, u_list u_attrib_arg, u_bool, u_dummy_range)
    |>> fun (a,b,c,d,e,f) -> q"Attrib(%A, %A, %A, %A, %A, %A)" a b c d e f
do
    _fill_u_entity_spec_data :=  
        pipe5
            u_typar_specs
            u_string
            (u_option u_string)
            u_range
            (
                tuple7(
                    u_option u_pubpath,
                    u_access .>>. u_access,
                    u_attribs,
                    u_option u_tycon_repr,
                    u_option u_typ,
                    u_tcaug,
                    tuple7(
                        u_string, 
                        u_kind,
                        u_int64,
                        u_option u_cpath,
                        u_lazy u_modul_typ,
                        u_exnc_repr,
                        u_space 1
                    )
                )
            )
        <| fun x1 x2a x2b x2c (x3,(x4a,x4b),x6,x7,x8,x9,(x10,x10b,x11,x12,x13,x14,_space)) ->
            q"{
                entity_typars = LazyWithContext<_,_>.NotLazy %A
                entity_stamp = newStamp()
                entity_logical_name = %A
                entity_compiled_name = %A
                entity_range = %A
                entity_pubpath = %A
                entity_accessiblity = %A
                entity_tycon_repr_accessibility = %A
                entity_attribs = %A
                entity_tycon_repr = %A
                entity_tycon_abbrev = %A
                entity_tycon_tcaug = %A
                entity_xmldoc = emptyXmlDoc
                entity_xmldocsig = %A
                entity_kind = %A
                entity_flags = EntityFlags(%A)
                entity_cpath = %A
                entity_modul_contents = %A
                entity_exn_info = %A
                entity_il_repr_cache = newCache()
            }" x1 x2a x2b x2c x3 x4a x4b x6 x7 x8 x9 x10 x10b x11 x12 x13 x14

    _fill_u_attribs := u_list u_attrib
    
    let typWithTag = function
        | 0 -> u_typs |>> TType_tuple
        | 1 -> u_simpletyp
        | 2 -> pipe2 u_tcref u_typs <| fun tc tinst -> TType_app(tc, tinst)
        | 3 -> pipe2 u_typ u_typ <| fun d r -> TType_fun(d, r)
        | 4 -> u_tpref |>> fun r -> r.AsType
        | 5 -> pipe2 u_typar_specs u_typ <| fun tps r -> TType_forall(tps, r)
        | 6 -> u_measure_expr |>> TType_measure
        | 7 -> pipe2 u_ucref u_typs <| fun uc tinst -> TType_ucase(uc,tinst)
        | x -> failf "u_typ %d" x

    _fill_u_typ := tagged typWithTag

let unpickle_modul_spec = u_tycon_spec
let unpickleModuleInfo =
    pipe4 unpickle_modul_spec u_string u_bool (u_space 3) <| fun a b c _space ->
        { mspec = a; compileTimeWorkingDir = b; usesQuotations = c }

let start1 =
    tuple7(
        u_array <| u_encoded_ccuref(),
        tuple3 u_int u_int u_int,
        u_array u_encoded_string,
        u_array <| u_encoded_pubpath(),
        u_array <| u_encoded_nleref(),
        u_array u_encoded_simpletyp,
        u_bytes
    )

let start2 state = unpickleModuleInfo state

open System.IO
//let bytes = File.ReadAllBytes(Path.Combine(__SOURCE_DIRECTORY__, "FSharpSignatureData.Sandbox.bin"))
let bytes = File.ReadAllBytes(Path.Combine(__SOURCE_DIRECTORY__, "FSharpSignatureData.FSharp.Compiler.bin"))


let (|EmptyView|_|) (x: View<_,_>) = if x.IsEmpty then Some() else None
let (Succ(data, EmptyView)) = parse start1 bytes
let ccuNameTab, (ntycons, ntypars, nvals), stringTab, pubpathTab, nlerefTab, simpletypTab, phase1bytes = data

let (Succ(data2, EmptyView)) = parse (start2 state) phase1bytes