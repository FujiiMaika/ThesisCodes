open Syntax
open Value

(* eval11 : interpreter with linearized trails *)

(* run_c11 : c -> s -> t -> m -> v *)
let rec run_c11 c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        [] ->
        begin match m with
            [] -> v
          | (c, s, t, h) :: m -> run_c11 c (v :: s) t m
        end
      | (c, s) :: t -> run_c11 c (v :: s) t m (* run_w10 w v TNil m *)
    end
  | (INum n :: c, VEnv (vs) :: s) -> run_c11 c (VNum (n) :: s) t m
  | (IBool b :: c, VEnv (vs) :: s) -> run_c11 c (VBool (b) :: s) t m
  | (IAccess n :: c, VEnv (vs) :: s) -> run_c11 c ((List.nth vs n) :: s) t m
  | (IPush_closure c' :: c, VEnv (vs) :: s) ->
    run_c11 c (VFun (c', vs) :: s) t m
  | (IReturn :: _, v :: VC (c) :: s) -> run_c11 c (v :: s) t m
  | (IPush_env :: c, VEnv (vs) :: s) ->
    run_c11 c (VEnv (vs) :: VEnv (vs) :: s) t m
  | (IPop_env :: c, v :: VEnv (vs) :: s) -> run_c11 c (VEnv (vs) :: v :: s) t m
  | (ICall :: c, v1 :: v0 :: s) ->
    begin match v0 with
        VFun (c', vs) -> run_c11 c' (VEnv (v1 :: vs) :: VC (c) :: s) t m
      | VRec (c', vr, vs) ->
        run_c11 c' (VEnv (v1 :: vr :: vs) :: VC (c) :: s) t m
      | VContD (c', s', t', h) -> run_c11 c' (v1 :: s') t' ((c, s, t, h) :: m)
      | VContS (c', s', t') -> run_c11 c' (v1 :: s') (t' @ (c, s) :: t) m
      | _ -> failwith
               (v_to_string v0 ^ " is not a function; it can not be applied.")
    end
  | (IOperations op :: c, v1 :: v0 :: s) ->
    begin match (v0, v1) with
        (VNum n0, VNum n1) ->
        begin match op with
            Plus -> run_c11 c (VNum (n0 + n1) :: s) t m
          | Minus -> run_c11 c (VNum (n0 - n1) :: s) t m
          | Times -> run_c11 c (VNum (n0 * n1) :: s) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c11 c (VNum (n0 / n1) :: s) t m
          | Equal -> run_c11 c (VBool (n0 = n1) :: s) t m
          | Less -> run_c11 c (VBool (n0 < n1) :: s) t m
        end
      | _ -> failwith (v_to_string v0 ^ " or " ^
                       v_to_string v1 ^ " are not numbers")
    end
  | (IThen_else (ct, ce) :: c, v :: VEnv (vs) :: s) ->
    begin match v with
        VBool (b) -> run_c11 ((if b then ct else ce) @ c) (VEnv (vs) :: s) t m 
      | _ -> failwith (v_to_string v ^
                       ": This expression was expected of type bool")
    end
  | (IPush_rec_closure (c0, c1) :: c, VEnv (vs) :: s) ->
    let rec vr = VRec (c0, vr, vs) in
    run_c11 (c1 @ c) (VEnv (vr :: vs) :: s) t m
  | (ITry_with (c0, c1) :: c, VEnv (vs) :: s) ->
    run_c11 c0 (VEnv (vs) :: []) [] ((c, s, t, (c1, vs)) :: m)
  | (IMove_deep_handler :: c, v :: s) ->
    begin match m with
        (c0, s0, t0, (c', vs)) :: m0 ->
        run_c11 (c' @ c0)
          (VEnv (VContD (c, s, t, (c', vs)) :: v :: vs) :: s0) t0 m0
      | _ -> failwith "call_d is used without enclosing try_with"
    end
  | (IMove_shallow_handler :: c, v :: s) ->
    begin match m with
        (c0, s0, t0, (c', vs)) :: m0 -> 
        run_c11 (c' @ c0) (VEnv (VContS (c, s, t) :: v :: vs) :: s0) t0 m0
      | _ -> failwith "call_s is used without enclosing try_with"
    end
  | _ -> failwith "continuations or stacks error"

(* f11 : e -> string list -> c *)
let rec f11 e xs = match e with
    Num n -> [INum n]
  | Bool b -> [IBool b]
  | Var x -> [IAccess (Env.offset x xs)]
  | Fun (x, e) -> [IPush_closure (f11 e (x :: xs) @ [IReturn])]
  | App (e0, e1) -> [IPush_env] @ f11 e0 xs @ [IPop_env] @ f11 e1 xs @ [ICall]
  | Op (e0, op, e1) ->
    [IPush_env] @ f11 e0 xs @ [IPop_env] @ f11 e1 xs @ [IOperations op]
  | If (e0, e1, e2) ->
    [IPush_env] @ f11 e0 xs @ [IThen_else (f11 e1 xs, f11 e2 xs)]
  | Rec (g, x, e0, e1) ->
    [IPush_rec_closure (f11 e0 (x :: g :: xs) @ [IReturn], f11 e1 (g :: xs))]
  | TryWith (e0, x, k, e1) -> [ITry_with (f11 e0 xs, f11 e1 (k :: x :: xs))]
  | CallD e -> f11 e xs @ [IMove_deep_handler]
  | CallS e -> f11 e xs @ [IMove_shallow_handler]
    
(* f : e -> v *)
let f e = run_c11 (f11 e []) (VEnv ([]) :: []) [] []
