open Syntax
open Value

(* eval06 : refunctionalized interpreter *)

(* initial continuation *)
let idc v s t m = match s with
    [] -> 
    begin match t with
        TNil ->
        begin match m with
            MNil -> v
          | MCons ((c, s, t, h), m) -> c v s t m
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

(* f6 : e -> string list -> v list -> c -> s -> t -> m -> v *)
let rec f6 e xs vs c s t m = match e with
    Num n -> c (VNum n) s t m
  | Bool b -> c (VBool b) s t m
  | Var x -> c (List.nth vs (Env.offset x xs)) s t m
  | Fun (x, e) ->
    c (VFun (fun v c' s' t' m' -> f6 e (x :: xs) (v :: vs) c' s' t' m')) s t m
  | App (e0, e1) ->
    f6 e0 xs vs (fun v0 s0 t0 m0 ->
        begin match s0 with
            VEnv (vs) :: s0 ->
            f6 e1 xs vs (fun v1 s1 t1 m1 ->
                begin match s1 with
                    v0 :: s1 ->
                    begin match v0 with
                        VFun (f) -> f v1 c s1 t1 m1
                      | _ -> failwith (v_to_string v0 ^ " is not a function; it can not be applied.")
                    end
                  | _ -> failwith "stack error"
                end) (v0 :: s0) t0 m0
          | _ -> failwith "stack error"
        end) (VEnv (vs) :: s) t m
  | Op (e0, op, e1) ->
    f6 e0 xs vs (fun v0 s0 t0 m0 ->
        begin match s0 with
            VEnv (vs) :: s0 ->
            f6 e1 xs vs (fun v1 s1 t1 m1 ->
                begin match s1 with
                    v0 :: s1 ->
                    begin match (v0, v1) with
                        (VNum n0, VNum n1) ->
                        begin match op with
                            Plus -> c (VNum (n0 + n1)) s1 t1 m1
                          | Minus -> c (VNum (n0 - n1)) s1 t1 m1
                          | Times -> c (VNum (n0 * n1)) s1 t1 m1
                          | Divide ->
                            if n1 = 0 then failwith "Division by zero"
                            else c (VNum (n0 / n1)) s1 t1 m1
                          | Equal -> c (VBool (n0 = n1)) s1 t1 m1
                          | Less -> c (VBool (n0 < n1)) s1 t1 m1
                        end
                      | _ -> failwith (v_to_string v0 ^ " or " ^ v_to_string v1
                                       ^ " are not numbers")
                    end
                  | _ -> failwith "stack error"
                end) (v0 :: s0) t0 m0
          | _ -> failwith "stack error"
        end) (VEnv (vs) :: s) t m
  | If (e0, e1, e2) ->
    f6 e0 xs vs (fun v s t m ->
        begin match s with
            VEnv (vs) :: s ->
            begin match v with
                VBool (b) -> f6 (if b then e1 else e2) xs vs c s t m 
              | _ -> failwith (v_to_string v ^
                               ": This expression was expected of type bool")
            end
          | _ -> failwith "stack error"
        end) (VEnv (vs) :: s) t m
  | Rec (g, x, e0, e1) ->
    let rec v0 =
      VFun (fun v c s t m -> f6 e0 (x :: g :: xs) (v :: v0 :: vs) c s t m) in
    f6 e1 (g :: xs) (v0 :: vs) c s t m
  | TryWith (e0, x, k, e1) ->
    let h = fun v vc c' s' t' m' ->
      f6 e1 (k :: x :: xs) (vc :: v :: vs) c' s' t' m' in
    f6 e0 xs vs idc [] TNil (MCons ((c, s, t, h), m))
  | CallD e ->
    f6 e xs vs (fun v s t m ->
        begin match m with
            MCons ((c0, s0, t0, h), m0) ->
            let vc =
              VFun (fun v c' s' t' m' -> c v s t (MCons ((c', s', t', h), m')))
            in h v vc c0 s0 t0 m0
          | _ -> failwith "call_d is used without enclosing try_with"
        end) s t m
  | CallS e ->
    f6 e xs vs (fun v s t m ->
        begin match m with
            MCons ((c0, s0, t0, h), m0) -> 
            let vc = VFun (fun v c' s' t' m' ->
                c v s (apnd t (cons (fun v t m -> c' v s' t m) t')) m') in
            h v vc c0 s0 t0 m0
          | _ -> failwith "call_s is used without enclosing try_with"
        end) s t m
    
(* f : e -> v *)
let f e = f6 e [] [] idc [] TNil MNil
