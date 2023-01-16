open Syntax
    
(* eval01 : definitional interpreter *)

(* value *)
type v = VNum of int
       | VBool of bool
       | VFun of (v -> c -> t -> m -> v)

(* continuation *)
and c = v -> t -> m -> v

(* trail *)
and t = TNil | Trail of (v -> t -> m -> v)

(* meta continuation *)
and m = MNil
      | MCons of (c * t * h) * m

(* handler's information *)
and h = v -> v -> c -> t -> m -> v


(* v_to_string : v -> string *)
let rec v_to_string v = match v with
    VNum n -> string_of_int n
  | VBool b -> if b then "true" else "false"
  | VFun _ -> "<VFun>"

(* Value.print : v -> unit *)
let print v =
  let str = v_to_string v in
  print_string str
