open Syntax
open Value

(* eval09 : defunctionalized interpreter *)

(* initial continuation *)
let idc = []

(* cons : w -> t -> t *)
let rec cons w t = match t with
    TNil -> Trail (w)
  | Trail (w') -> Trail (Append (w, w'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (w) -> cons w t1


(* run_i9 : i -> c -> s -> t -> m -> v *)
let rec run_i9 i c s t m = match i with
    INum n ->
    begin match s with
        VEnv (vs) :: s -> run_c9 c (VNum (n) :: s) t m
      | _ -> failwith "stack error"
    end
  | IBool b ->
    begin match s with
        VEnv (vs) :: s -> run_c9 c (VBool (b) :: s) t m
      | _ -> failwith "stack error"
    end
  | IAccess n ->
    begin match s with
        VEnv (vs) :: s -> run_c9 c ((List.nth vs n) :: s) t m
      | _ -> failwith "stack error"
    end
  | IPush_closure i ->
    begin match s with
        VEnv (vs) :: s -> run_c9 c (VFun (i, vs) :: s) t m
      | _ -> failwith "stack error"
    end
  | IReturn ->
    begin match s with
        v :: VC (c) :: s -> run_c9 c (v :: s) t m
      | _ -> failwith "stack error"
    end
  | IPush_env ->
    begin match s with
        VEnv (vs) :: s -> run_c9 c (VEnv (vs) :: VEnv (vs) :: s) t m
      | _ -> failwith "stack error"
    end
  | IPop_env ->
    begin match s with
        v :: VEnv (vs) :: s -> run_c9 c (VEnv (vs) :: v :: s) t m
      | _ -> failwith "stack error"
    end
  | ICall ->
    begin match s with
        v1 :: v0 :: s ->
        begin match v0 with
            VFun (i, vs) -> run_i9 i idc (VEnv (v1 :: vs) :: VC (c) :: s) t m
          | VRec (i, vr, vs) ->
            run_i9 i idc (VEnv (v1 :: vr :: vs) :: VC (c) :: s) t m
          | VContD (c', s', t', h) ->
            run_c9 c' (v1 :: s') t' ((c, s, t, h) :: m)
          | VContS (c', s', t') ->
            run_c9 c' (v1 :: s') (apnd t' (cons (Hold (c, s)) t)) m
          | _ -> failwith
                   (v_to_string v0 ^
                    " is not a function; it can not be applied.")
        end
      | _ -> failwith "stack error"
    end
  | IOperations op ->
    begin match s with
        v1 :: v0 :: s ->
        begin match (v0, v1) with
            (VNum n0, VNum n1) ->
            begin match op with
                Plus -> run_c9 c (VNum (n0 + n1) :: s) t m
              | Minus -> run_c9 c (VNum (n0 - n1) :: s) t m
              | Times -> run_c9 c (VNum (n0 * n1) :: s) t m
              | Divide ->
                if n1 = 0 then failwith "Division by zero"
                else run_c9 c (VNum (n0 / n1) :: s) t m
              | Equal -> run_c9 c (VBool (n0 = n1) :: s) t m
              | Less -> run_c9 c (VBool (n0 < n1) :: s) t m
            end
          | _ -> failwith (v_to_string v0 ^ " or " ^
                           v_to_string v1 ^ " are not numbers")
        end
      | _ -> failwith "stack error"
    end
  | IThen_else (it, ie) ->
    begin match s with
        v :: VEnv (vs) :: s ->
        begin match v with
            VBool (b) -> run_i9 (if b then it else ie) c (VEnv (vs) :: s) t m 
          | _ -> failwith (v_to_string v ^
                           ": This expression was expected of type bool")
        end
      | _ -> failwith "stack error"
    end
  | IPush_rec_closure (i0, i1) ->
    begin match s with
        VEnv (vs) :: s ->
        let rec vr = VRec (i0, vr, vs) in
        run_i9 i1 c (VEnv (vr :: vs) :: s) t m
      | _ -> failwith "stack error"
    end
  | ITry_with (i0, i1) ->
    begin match s with
        VEnv (vs) :: s ->
        run_i9 i0 idc (VEnv (vs) :: []) TNil ((c, s, t, (i1, vs)) :: m)
      | _ -> failwith "stack error"
    end
  | IMove_deep_handler ->
    begin match s with
        v :: s ->
        begin match m with
            (c0, s0, t0, (i, vs)) :: m0 ->
            run_i9 i c0 (VEnv (VContD (c, s, t, (i, vs)) :: v :: vs) :: s0)
              t0 m0
          | _ -> failwith "call_d is used without enclosing try_with"
        end
      | _ -> failwith "stack error"
    end
  | IMove_shallow_handler ->
    begin match s with
        v :: s ->
        begin match m with
            (c0, s0, t0, (i, vs)) :: m0 -> 
            run_i9 i c0 (VEnv (VContS (c, s, t) :: v :: vs) :: s0) t0 m0
          | _ -> failwith "call_s is used without enclosing try_with"
        end
      | _ -> failwith "stack error"
    end
  | ISeq (i0, i1) -> run_i9 i0 (i1 :: c) s t m

(* run_c9 : c -> s -> t -> m -> v *)
and run_c9 c s t m = match c with
    [] ->
    begin match s with
        v :: [] -> 
        begin match t with
            TNil ->
            begin match m with
                [] -> v
              | (c, s, t, h) :: m -> run_c9 c (v :: s) t m
            end
          | Trail (w) -> run_w9 w v TNil m
        end
      | _ -> failwith "stack error"
    end
  | i :: c -> run_i9 i c s t m

(* run_w9 : w -> v -> t -> m -> v *)
and run_w9 w v t m = match w with
    Hold (c, s) -> run_c9 c (v :: s) t m
  | Append (w, w') -> run_w9 w v (cons w' t) m

(* (>>) : i -> i -> i *)
let (>>) i0 i1 = ISeq (i0, i1)

(* f9 : e -> string list -> i *)
let rec f9 e xs = match e with
    Num n -> INum n
  | Bool b -> IBool b
  | Var x -> IAccess (Env.offset x xs)
  | Fun (x, e) -> IPush_closure (f9 e (x :: xs) >> IReturn)
  | App (e0, e1) -> IPush_env >> f9 e0 xs >> IPop_env >> f9 e1 xs >> ICall
  | Op (e0, op, e1) ->
    IPush_env >> f9 e0 xs >> IPop_env >> f9 e1 xs >> IOperations op
  | If (e0, e1, e2) -> IPush_env >> f9 e0 xs >> IThen_else (f9 e1 xs, f9 e2 xs)
  | Rec (g, x, e0, e1) ->
    IPush_rec_closure (f9 e0 (x :: g :: xs) >> IReturn, f9 e1 (g :: xs))
  | TryWith (e0, x, k, e1) -> ITry_with (f9 e0 xs, f9 e1 (k :: x :: xs))
  | CallD e -> f9 e xs >> IMove_deep_handler
  | CallS e -> f9 e xs >> IMove_shallow_handler
    
(* f : e -> v *)
let f e = run_i9 (f9 e []) idc (VEnv ([]) :: []) TNil []
