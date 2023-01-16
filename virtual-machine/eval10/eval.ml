open Syntax
open Value

(* eval10 : interpreter with linear instructions *)

(* cons : w -> t -> t *)
let rec cons w t = match t with
    TNil -> Trail (w)
  | Trail (w') -> Trail (Append (w, w'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (w) -> cons w t1


(* run_c10 : c -> s -> t -> m -> v *)
let rec run_c10 c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        TNil ->
        begin match m with
            [] -> v
          | (c, s, t, h) :: m -> run_c10 c (v :: s) t m
        end
      | Trail (w) -> run_w10 w v TNil m
    end
  | (INum n :: c, VEnv (vs) :: s) -> run_c10 c (VNum (n) :: s) t m
  | (IBool b :: c, VEnv (vs) :: s) -> run_c10 c (VBool (b) :: s) t m
  | (IAccess n :: c, VEnv (vs) :: s) -> run_c10 c ((List.nth vs n) :: s) t m
  | (IPush_closure c' :: c, VEnv (vs) :: s) ->
    run_c10 c (VFun (c', vs) :: s) t m
  | (IReturn :: _, v :: VC (c) :: s) -> run_c10 c (v :: s) t m
  | (IPush_env :: c, VEnv (vs) :: s) ->
    run_c10 c (VEnv (vs) :: VEnv (vs) :: s) t m
  | (IPop_env :: c, v :: VEnv (vs) :: s) -> run_c10 c (VEnv (vs) :: v :: s) t m
  | (ICall :: c, v1 :: v0 :: s) ->
    begin match v0 with
        VFun (c', vs) -> run_c10 c' (VEnv (v1 :: vs) :: VC (c) :: s) t m
      | VRec (c', vr, vs) ->
        run_c10 c' (VEnv (v1 :: vr :: vs) :: VC (c) :: s) t m
      | VContD (c', s', t', h) -> run_c10 c' (v1 :: s') t' ((c, s, t, h) :: m)
      | VContS (c', s', t') ->
        run_c10 c' (v1 :: s') (apnd t' (cons (Hold (c, s)) t)) m
      | _ -> failwith
               (v_to_string v0 ^ " is not a function; it can not be applied.")
    end
  | (IOperations op :: c, v1 :: v0 :: s) ->
    begin match (v0, v1) with
        (VNum n0, VNum n1) ->
        begin match op with
            Plus -> run_c10 c (VNum (n0 + n1) :: s) t m
          | Minus -> run_c10 c (VNum (n0 - n1) :: s) t m
          | Times -> run_c10 c (VNum (n0 * n1) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c10 c (VNum (n0 / n1) :: s) t m
          | Equal -> run_c10 c (VBool (n0 = n1) :: s) t m
          | Less -> run_c10 c (VBool (n0 < n1) :: s) t m
        end
      | _ -> failwith (v_to_string v0 ^ " or " ^
                       v_to_string v1 ^ " are not numbers")
    end
  | (IThen_else (ct, ce) :: c, v :: VEnv (vs) :: s) ->
    begin match v with
        VBool (b) -> run_c10 ((if b then ct else ce) @ c) (VEnv (vs) :: s) t m 
      | _ -> failwith (v_to_string v ^
                       ": This expression was expected of type bool")
    end
  | (IPush_rec_closure (c0, c1) :: c, VEnv (vs) :: s) ->
    let rec vr = VRec (c0, vr, vs) in
    run_c10 (c1 @ c) (VEnv (vr :: vs) :: s) t m
  | (ITry_with (c0, c1) :: c, VEnv (vs) :: s) ->
    run_c10 c0 (VEnv (vs) :: []) TNil ((c, s, t, (c1, vs)) :: m)
  | (IMove_deep_handler :: c, v :: s) ->
    begin match m with
        (c0, s0, t0, (c', vs)) :: m0 ->
        run_c10 (c' @ c0)
          (VEnv (VContD (c, s, t, (c', vs)) :: v :: vs) :: s0) t0 m0
      | _ -> failwith "call_d is used without enclosing try_with"
    end
  | (IMove_shallow_handler :: c, v :: s) ->
    begin match m with
        (c0, s0, t0, (c', vs)) :: m0 -> 
        run_c10 (c' @ c0) (VEnv (VContS (c, s, t) :: v :: vs) :: s0) t0 m0
      | _ -> failwith "call_s is used without enclosing try_with"
    end
  | _ -> failwith "continuations or stacks error"

(* run_w10 : w -> v -> t -> m -> v *)
and run_w10 w v t m = match w with
    Hold (c, s) -> run_c10 c (v :: s) t m
  | Append (w, w') -> run_w10 w v (cons w' t) m


(* f10 : e -> string list -> c *)
let rec f10 e xs = match e with
    Num n -> [INum n]
  | Bool b -> [IBool b]
  | Var x -> [IAccess (Env.offset x xs)]
  | Fun (x, e) -> [IPush_closure (f10 e (x :: xs) @ [IReturn])]
  | App (e0, e1) -> [IPush_env] @ f10 e0 xs @ [IPop_env] @ f10 e1 xs @ [ICall]
  | Op (e0, op, e1) ->
    [IPush_env] @ f10 e0 xs @ [IPop_env] @ f10 e1 xs @ [IOperations op]
  | If (e0, e1, e2) ->
    [IPush_env] @ f10 e0 xs @ [IThen_else (f10 e1 xs, f10 e2 xs)]
  | Rec (g, x, e0, e1) ->
    [IPush_rec_closure (f10 e0 (x :: g :: xs) @ [IReturn], f10 e1 (g :: xs))]
  | TryWith (e0, x, k, e1) -> [ITry_with (f10 e0 xs, f10 e1 (k :: x :: xs))]
  | CallD e -> f10 e xs @ [IMove_deep_handler]
  | CallS e -> f10 e xs @ [IMove_shallow_handler]
    
(* f : e -> v *)
let f e = run_c10 (f10 e []) (VEnv ([]) :: []) TNil []
