open Syntax
open Value

(* eval02 : defuncarionalizing handler *)

(* initial continuation *)
let idc v t m = match t with
    TNil ->
    begin match m with
        MNil -> v
      | MCons ((c, t, h), m) -> c v t m
    end
  | Trail (c) -> c v TNil m

(* cons : (v -> t -> m -> v) -> t -> t *)
let rec cons c t = match t with
    TNil -> Trail (c)
  | Trail (c') -> Trail (fun v t' m -> c v (cons c' t') m)

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (c) -> cons c t1

(* f1 : e -> string list -> v list -> c -> t -> m -> v *)
let rec f1 e xs vs c t m = match e with
    Num n -> c (VNum n) t m
  | Bool b -> c (VBool b) t m
  | Var x -> c (List.nth vs (Env.offset x xs)) t m
  | Fun (x, e) ->
    c (VFun (fun v c' t' m' -> f1 e (x :: xs) (v :: vs) c' t' m')) t m
  | App (e0, e1) ->
    f1 e0 xs vs (fun v0 t0 m0 ->
        f1 e1 xs vs (fun v1 t1 m1 ->
            begin match v0 with
                VFun (f) -> f v1 c t1 m1
              | _ -> failwith (v_to_string v0
                               ^ " is not a function; it can not be applied.")
            end) t0 m0) t m
  | Op (e0, op, e1) ->
    f1 e0 xs vs (fun v0 t0 m0 ->
        f1 e1 xs vs (fun v1 t1 m1 ->
            begin match (v0, v1) with
                (VNum n0, VNum n1) ->
                begin match op with
                    Plus -> c (VNum (n0 + n1)) t1 m1
                  | Minus -> c (VNum (n0 - n1)) t1 m1
                  | Times -> c (VNum (n0 * n1)) t1 m1
                  | Divide ->
                    if n1 = 0 then failwith "Division by zero"
                    else c (VNum (n0 / n1)) t1 m1
                  | Equal -> c (VBool (n0 = n1)) t1 m1
                  | Less ->  c (VBool (n0 < n1)) t1 m1
                end
              | _ -> failwith (v_to_string v0 ^ " or " ^ v_to_string v1
                               ^ " are not numbers")
            end) t0 m0) t m
  | If (e0, e1, e2) ->
    f1 e0 xs vs (fun v0 t0 m0 ->
        begin match v0 with
            VBool (b) ->
            if b then f1 e1 xs vs c t0 m0 else f1 e2 xs vs c t0 m0
          | _ -> failwith (v_to_string v0 ^
                           ": This expression was expected of type bool")
        end) t m
  | Rec (g, x, e0, e1) ->
    let rec v0 =
      VFun (fun v c t m -> f1 e0 (x :: g :: xs) (v :: v0 :: vs) c t m) in
    f1 e1 (g :: xs) (v0 :: vs) c t m
  | TryWithD (e0, x, k, e1) ->
    f1 e0 xs vs idc TNil (MCons ((c, t, HD (x, k, e1, xs, vs)), m))
  | TryWithS (e0, x, k, e1) ->
    f1 e0 xs vs idc TNil (MCons ((c, t, HS (x, k, e1, xs, vs)), m))
  | Call e ->
    f1 e xs vs (fun v t' m' ->
        begin match m' with
            MCons ((c0, t0, h), m0) ->
            begin match h with
                HD (x, k, e0, xs0, vs0) ->
                let vc =
                  VFun (fun v2 c2 t2 m2 -> c v2 t' (MCons ((c2, t2, h), m2))) in
                f1 e0 (k :: x :: xs0) (vc :: v :: vs0) c0 t0 m0
              | HS (x, k, e0, xs0, vs0) ->
                let vc =
                  VFun (fun v2 c2 t2 m2 -> c v2 (apnd t' (cons c2 t2)) m2) in
                f1 e0 (k :: x :: xs0) (vc :: v :: vs0) c0 t0 m0
            end
          | _ -> failwith "call is used without enclosing handler"
        end) t m


(* f : e -> v *)
let f e = f1 e [] [] idc TNil MNil
