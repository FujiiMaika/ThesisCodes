open Syntax
    
(* eval09 : defunctionalized interpreter *)

(* value *)
type v = VNum of int
       | VBool of bool
       | VFun of i * v list
       | VRec of i * v * v list
       | VContD of c * s * t * h
       | VContS of c * s * t
       | VEnv of v list
       | VC of c

(* instructions *)
and i = INum of int
      | IBool of bool
      | IAccess of int
      | IPush_closure of i
      | IReturn
      | IPush_env
      | IPop_env
      | ICall
      | IOperations of op
      | IThen_else of i * i
      | IPush_rec_closure of i * i
      | ITry_with of i * i
      | IMove_deep_handler
      | IMove_shallow_handler
      | ISeq of i * i

(* continuation *)
and c = i list

(* stack *)
and s = v list

and w = Hold of c * s
      | Append of w * w

(* trail *)
and t = TNil | Trail of w

(* meta continuation *)
and m = (c * s * t * h) list

(* handler's information *)
and h = i * v list


(* v_to_string : v -> string *)
let rec v_to_string v = match v with
    VNum n -> string_of_int n
  | VBool b -> if b then "true" else "false"
  | VFun _ -> "<VFun>"
  | VRec _ -> "<VRec>"
  | VContD _ -> "<VContD>"
  | VContS _ -> "<VContS>"
  | VEnv _ -> "<VEnv>"
  | VC _ -> "<VC>"

(* Value.print : v -> unit *)
let print v =
  let str = v_to_string v in
  print_string str
