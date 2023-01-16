open Syntax
    
(* eval04 : stack-based interpreter *)

(* value *)
type v = VNum of int
       | VBool of bool
       | VFun of (v -> c -> s -> t -> m -> v)
       | VEnv of v list

(* continuation *)
and c = f list

(* frame *)
and f = CApp0 of e * string list
      | CApp1
      | COp0 of e * op * string list
      | COp1 of op
      | CIf of e * e * string list
      | CCallD
      | CCallS

(* stack *)
and s = v list

(* trail *)
and t = TNil | Trail of (v -> t -> m -> v)

(* meta continuation *)
and m = MNil
      | MCons of (c * s * t * h) * m

(* handler's information *)
and h = v -> v -> c -> s -> t -> m -> v


(* v_to_string : v -> string *)
let rec v_to_string v = match v with
    VNum n -> string_of_int n
  | VBool b -> if b then "true" else "false"
  | VFun _ -> "<VFun>"
  | VEnv _ -> "<VEnv>"

(* Value.print : v -> unit *)
let print v =
  let str = v_to_string v in
  print_string str
