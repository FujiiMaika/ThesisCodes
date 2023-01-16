open Syntax
open Value

(* eval02 : interpreter with defunctionalized continuation *)

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

(* f2 : e -> string list -> v list -> c -> t -> m -> v *)
let rec f2 e xs vs c t m = match e with
    Num n -> run_c2 c (VNum n) t m
  | Bool b -> run_c2 c (VBool b) t m
  | Var x -> run_c2 c (List.nth vs (Env.offset x xs)) t m
  | Fun (x, e) ->
    run_c2 c (VFun (fun v c' t' m' -> f2 e (x :: xs) (v :: vs) c' t' m')) t m
  | App (e0, e1) -> f2 e0 xs vs (CApp0 (e1, xs, vs, c)) t m
  | Op (e0, op, e1) -> f2 e0 xs vs (COp0 (e1, op, xs, vs, c)) t m
  | If (e0, e1, e2) -> f2 e0 xs vs (CIf (e1, e2, xs, vs, c)) t m
  | Rec (g, x, e0, e1) ->
    let rec v0 =
      VFun (fun v c t m -> f2 e0 (x :: g :: xs) (v :: v0 :: vs) c t m) in
    f2 e1 (g :: xs) (v0 :: vs) c t m
  | TryWith (e0, x, k, e1) ->
    let h = fun v vc c' t' m' -> f2 e1 (k :: x :: xs) (vc :: v :: vs) c' t' m'
    in f2 e0 xs vs idc TNil (MCons ((c, t, h), m))
  | CallD e -> f2 e xs vs (CCallD (c)) t m
  | CallS e -> f2 e xs vs (CCallS (c)) t m

(* run_c2 : c -> v -> t -> m -> v *)
and run_c2 c v t m = match c with
    C0 ->
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, t, h), m) -> run_c2 c v t m
        end
      | Trail (c) -> c v TNil m
    end
  | CApp0 (e, xs, vs, c) -> f2 e xs vs (CApp1 (v, c)) t m
  | CApp1 (v0, c) ->
    begin match v0 with
        VFun (f) -> f v c t m
      | _ -> failwith (v_to_string v0
                       ^ " is not a function; it can not be applied.")
    end
  | COp0 (e, op, xs, vs, c) -> f2 e xs vs (COp1 (op, v, c)) t m
  | COp1 (op, v0, c) ->
    begin match (v0, v) with
        (VNum n0, VNum n1) ->
        begin match op with
            Plus -> run_c2 c (VNum (n0 + n1)) t m
          | Minus -> run_c2 c (VNum (n0 - n1)) t m
          | Times -> run_c2 c (VNum (n0 * n1)) t m
          | Divide ->
            if n1 = 0 then failwith "Division by zero"
            else run_c2 c (VNum (n0 / n1)) t m
          | Equal -> run_c2 c (VBool (n0 = n1)) t m
          | Less -> run_c2 c (VBool (n0 < n1)) t m
        end
      | _ -> failwith (v_to_string v0 ^ " or " ^ v_to_string v
                       ^ " are not numbers")
    end
  | CIf (e1, e2, xs, vs, c) ->
    begin match v with
        VBool (b) -> f2 (if b then e1 else e2) xs vs c t m 
      | _ -> failwith (v_to_string v ^
                       ": This expression was expected of type bool")
    end
  | CCallD (c) ->
    begin match m with
        MCons ((c0, t0, h), m0) ->
        let vc = VFun (fun v c' t' m' -> run_c2 c v t (MCons ((c', t', h), m')))
        in h v vc c0 t0 m0
      | _ -> failwith "call_d is used without enclosing try_with"
    end
  | CCallS (c) ->
    begin match m with
        MCons ((c0, t0, h), m0) -> 
        let vc = VFun (fun v c' t' m' ->
            run_c2 c v (apnd t (cons (fun v t m -> run_c2 c' v t m) t')) m')
        in h v vc c0 t0 m0
      | _ -> failwith "call_s is used without enclosing try_with"
    end
    
    

(* f : e -> v *)
let f e = f2 e [] [] idc TNil MNil
