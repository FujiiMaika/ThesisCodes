open Syntax
open Value

(* eval08 : interpreter with functional instructions *)

(* initial continuation *)
let idc s t m = match s with
    v :: [] -> 
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t, h), m) -> c (v :: s) t m
        end
      | Trail (c) -> c v TNil m
    end
  | _ -> failwith "stack error" 

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons c t = match t with
    TNil -> Trail (c)
  | Trail (c') -> Trail (fun v t' m -> c v (cons c' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (c) -> cons c t1


(* instructions : c -> s -> t -> m -> v *)
let num n = fun c s t m -> match s with
    VEnv (vs) :: s -> c (VNum (n) :: s) t m
  | _ -> failwith "stack error"

let bool b = fun c s t m -> match s with
    VEnv (vs) :: s -> c (VBool (b) :: s) t m
  | _ -> failwith "stack error"

let access n = fun c s t m -> match s with
    VEnv (vs) :: s -> c ((List.nth vs n) :: s) t m
  | _ -> failwith "stack error"

let push_closure i = fun c s t m -> match s with
    VEnv (vs) :: s ->
    c (VFun (fun c' s' t' m' ->
        begin match s' with
            v :: s' -> i c' (VEnv (v :: vs) :: s') t' m'
          | _ -> failwith "stack error"
        end) :: s) t m
  | _ -> failwith "stack error"

let return = fun _ s t m -> match s with
    v :: VC (c) :: s -> c (v :: s) t m
  | _ -> failwith "stack error"

let push_env = fun c s t m -> match s with
    VEnv (vs) :: s -> c (VEnv (vs) :: VEnv (vs) :: s) t m
  | _ -> failwith "stack error"

let pop_env = fun c s t m -> match s with
    v :: VEnv (vs) :: s -> c (VEnv (vs) :: v :: s) t m
  | _ -> failwith "stack error"

let call = fun c s t m -> match s with
    v1 :: v0 :: s ->
    begin match v0 with
        VFun (f) -> f idc (v1 :: VC (c) :: s) t m
      | VCont (f) -> f c (v1 :: s) t m
      | _ -> failwith
               (v_to_string v0 ^ " is not a function; it can not be applied.")
    end
  | _ -> failwith "stack error"

let operations op = fun c s t m -> match s with
    v1 :: v0 :: s ->
    begin match (v0, v1) with
        (VNum n0, VNum n1) ->
        begin match op with
            Plus -> c (VNum (n0 + n1) :: s) t m
          | Minus -> c (VNum (n0 - n1) :: s) t m
          | Times -> c (VNum (n0 * n1) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else c (VNum (n0 / n1) :: s) t m
          | Equal -> c (VBool (n0 = n1) :: s) t m
          | Less -> c (VBool (n0 < n1) :: s) t m
        end
      | _ -> failwith (v_to_string v0 ^ " or " ^
                       v_to_string v1 ^ " are not numbers")
    end
  | _ -> failwith "stack error"

let then_else it ie = fun c s t m -> match s with
    v :: VEnv (vs) :: s ->
    begin match v with
        VBool (b) -> (if b then it else ie) c (VEnv (vs) :: s) t m 
      | _ -> failwith (v_to_string v ^
                       ": This expression was expected of type bool")
    end
  | _ -> failwith "stack error"

let push_rec_closure i0 i1 = fun c s t m -> match s with
    VEnv (vs) :: s ->
    let rec v0 = VFun (fun c' s' t' m' ->
        begin match s' with
            v :: s' -> i0 c' (VEnv (v :: v0 :: vs) :: s') t' m'
          | _ -> failwith "stack error"
        end) in
    i1 c (VEnv (v0 :: vs) :: s) t m
  | _ -> failwith "stack error"

let trywith i0 i1 = fun c s t m -> match s with
    VEnv (vs) :: s ->
    let h = fun c' s' t' m' ->
      begin match s' with
          vc :: v :: s' -> i1 c' (VEnv (vc :: v :: vs) :: s') t' m'
        | _ -> failwith "stack error"
      end in
    i0 idc (VEnv (vs) :: []) TNil (MCons ((c, s, t, h), m))
  | _ -> failwith "stack error"

let move_deep_handler = fun c s t m -> match s with
    v :: s ->
    begin match m with
        MCons ((c0, s0, t0, h), m0) ->
        let vc = VCont (fun c' s' t' m' ->
            begin match s' with
                v' :: s' -> c (v' :: s) t (MCons ((c', s', t', h), m'))
              | _ -> failwith "stack error"
            end) in
        h c0 (vc :: v :: s0) t0 m0
      | _ -> failwith "call_d is used without enclosing try_with"
    end
  | _ -> failwith "stack error"

let move_shallow_handler = fun c s t m -> match s with
    v :: s ->
    begin match m with
        MCons ((c0, s0, t0, h), m0) -> 
        let vc = VCont (fun c' s' t' m' ->
            begin match s' with
                v' :: s' -> c (v' :: s)
                              (apnd t (cons (fun v t m -> c' (v :: s') t m) t'))
                              m'
              | _ -> failwith "stack error"
            end) in
        h c0 (vc :: v :: s0) t0 m0
      | _ -> failwith "call_s is used without enclosing try_with"
    end
  | _ -> failwith "stack error"

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = fun c s t m -> i0 (fun s' t' m' -> i1 c s' t' m') s t m

(* f8 : e -> string list -> i *)
let rec f8 e xs = match e with
    Num n -> num n
  | Bool b -> bool b
  | Var x -> access (Env.offset x xs)
  | Fun (x, e) -> push_closure (f8 e (x :: xs) >> return)
  | App (e0, e1) -> push_env >> f8 e0 xs >> pop_env >> f8 e1 xs >> call
  | Op (e0, op, e1) ->
    push_env >> f8 e0 xs >> pop_env >> f8 e1 xs >> operations op
  | If (e0, e1, e2) -> push_env >> f8 e0 xs >> then_else (f8 e1 xs) (f8 e2 xs)
  | Rec (g, x, e0, e1) ->
    push_rec_closure (f8 e0 (x :: g :: xs) >> return) (f8 e1 (g :: xs))
  | TryWith (e0, x, k, e1) -> trywith (f8 e0 xs) (f8 e1 (k :: x :: xs))
  | CallD e -> f8 e xs >> move_deep_handler
  | CallS e -> f8 e xs >> move_shallow_handler
    
(* f : e -> v *)
let f e = f8 e [] idc (VEnv ([]) :: []) TNil MNil
