open Syntax
open Value

(* eval05 : interpreter with delinearized continuations *)

(* initial continuation *)
let idc = C0

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons c t = match t with
    TNil -> Trail (c)
  | Trail (c') -> Trail (fun v t' m -> c v (cons c' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (c) -> cons c t1

(* f5 : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f5 e xs vs c s t m = match e with
    Num n -> run_c5 c (VNum n) s t m
  | Bool b -> run_c5 c (VBool b) s t m
  | Var x -> run_c5 c (List.nth vs (Env.offset x xs)) s t m
  | Fun (x, e) ->
    run_c5 c
      (VFun (fun v c' s' t' m' -> f5 e (x :: xs) (v :: vs) c' s' t' m')) s t m
  | App (e0, e1) -> f5 e0 xs vs (CApp0 (e1, xs, c)) (VEnv (vs) :: s) t m
  | Op (e0, op, e1) -> f5 e0 xs vs (COp0 (e1, op, xs, c)) (VEnv (vs) :: s) t m
  | If (e0, e1, e2) -> f5 e0 xs vs (CIf (e1, e2, xs, c)) (VEnv (vs) :: s) t m
  | Rec (g, x, e0, e1) ->
    let rec v0 =
      VFun (fun v c s t m -> f5 e0 (x :: g :: xs) (v :: v0 :: vs) c s t m) in
    f5 e1 (g :: xs) (v0 :: vs) c s t m
  | TryWith (e0, x, k, e1) ->
    let h = fun v vc c' s' t' m' ->
      f5 e1 (k :: x :: xs) (vc :: v :: vs) c' s' t' m' in
    f5 e0 xs vs idc [] TNil (MCons ((c, s, t, h), m))
  | CallD e -> f5 e xs vs (CCallD (c)) s t m
  | CallS e -> f5 e xs vs (CCallS (c)) s t m

(* run_c5 : c -> v -> s -> t -> m -> v *)
and run_c5 c v s t m = match (c, s) with
    (C0, []) ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t, h), m) -> run_c5 c v s t m
        end
      | Trail (c) -> c v TNil m
    end
  | (CApp0 (e, xs, c), VEnv (vs) :: s) -> f5 e xs vs (CApp1 (c)) (v :: s) t m
  | (CApp1 (c), v0 :: s) ->
    begin match v0 with
        VFun (f) -> f v c s t m
      | _ -> failwith (v_to_string v0
                       ^ " is not a function; it can not be applied.")
    end
  | (COp0 (e, op, xs, c), VEnv (vs) :: s) ->
    f5 e xs vs (COp1 (op, c)) (v :: s) t m
  | (COp1 (op, c), v0 :: s) ->
    begin match (v0, v) with
        (VNum n0, VNum n1) ->
        begin match op with
            Plus -> run_c5 c (VNum (n0 + n1)) s t m
          | Minus -> run_c5 c (VNum (n0 - n1)) s t m
          | Times -> run_c5 c (VNum (n0 * n1)) s t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c5 c (VNum (n0 / n1)) s t m
          | Equal -> run_c5 c (VBool (n0 = n1)) s t m
          | Less -> run_c5 c (VBool (n0 < n1)) s t m
        end
      | _ -> failwith (v_to_string v0 ^ " or " ^ v_to_string v
                       ^ " are not numbers")
    end
  | (CIf (e1, e2, xs, c), VEnv (vs) :: s) ->
    begin match v with
        VBool (b) -> f5 (if b then e1 else e2) xs vs c s t m 
      | _ -> failwith (v_to_string v ^
                       ": This expression was expected of type bool")
    end
  | (CCallD (c), s) ->
    begin match m with
        MCons ((c0, s0, t0, h), m0) ->
        let vc = VFun (fun v c' s' t' m' ->
            run_c5 c v s t (MCons ((c', s', t', h), m'))) in
        h v vc c0 s0 t0 m0
      | _ -> failwith "call_d is used without enclosing try_with"
    end
  | (CCallS (c), s) ->
    begin match m with
        MCons ((c0, s0, t0, h), m0) -> 
        let vc = VFun (fun v c' s' t' m' ->
            run_c5 c v s
              (apnd t (cons (fun v t m -> run_c5 c' v s' t m) t')) m') in
        h v vc c0 s0 t0 m0
      | _ -> failwith "call_s is used without enclosing try_with"
    end
  | _ -> failwith "stack or cont error"
    
    

(* f : e -> v *)
let f e = f5 e [] [] idc [] TNil MNil
