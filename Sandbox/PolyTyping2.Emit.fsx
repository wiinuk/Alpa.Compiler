module PolyTyping2_Emit
#load "PolyTyping2.fsx"

open PolyTyping2

let emit = function
    | Lit _ -> ()
    | Var(_) -> failwith "Not implemented yet"
    | Lam(_, _) -> failwith "Not implemented yet"
    | App(_, _) -> failwith "Not implemented yet"
    | Ext(_, _, _) -> failwith "Not implemented yet"
    | Let(_, _, _) -> failwith "Not implemented yet"
    | LetRec(_, _) -> failwith "Not implemented yet"
    | Mat(_, _, _) -> failwith "Not implemented yet"
    | TypeDef(name, _, _) -> failwith "Not implemented yet"
    | InstanceDef(name, typeArgs, methodImpls, cont) -> failwith "Not implemented yet"