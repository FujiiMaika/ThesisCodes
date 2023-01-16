open Syntax
open Value

(* eval07 : interpreter with combined arguments *)

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

(* f7 : e -> string list -> c -> s -> t -> m -> v *)
let rec f7 e xs c s t m = match s with
    VEnv (vs) :: s -> 
    begin match e with
        Num n -> c (VNum (n) :: s) t m
      | Bool b -> c (VBool (b) :: s) t m
      | Var x -> c ((List.nth vs (Env.offset x xs)) :: s) t m
      | Fun (x, e) ->
        c (VFun (fun c' s' t' m' ->
            begin match s' with
                v :: s' -> f7 e (x :: xs) c' (VEnv (v :: vs) :: s') t' m'
              | _ -> failwith "stack error"
            end) :: s) t m
      | App (e0, e1) ->
        f7 e0 xs (fun s0 t0 m0 ->
            begin match s0 with
                v0 :: VEnv (vs) :: s0 ->
                f7 e1 xs (fun s1 t1 m1 ->
                    begin match s1 with
                        v1 :: v0 :: s1 -> 
                        begin match v0 with
                            VFun (f) -> f c (v1 :: s1) t1 m1
                          | _ -> failwith (v_to_string v0 ^ " is not a function; it can not be applied.")
                        end
                      | _ -> failwith "stack error"
                    end) (VEnv (vs) :: v0 :: s0) t0 m0
              | _ -> failwith "stack error"
            end) (VEnv (vs) :: VEnv (vs) :: s) t m
      | Op (e0, op, e1) ->
        f7 e0 xs (fun s0 t0 m0 ->
            begin match s0 with
                v0 :: VEnv (vs) :: s0 ->
                f7 e1 xs (fun s1 t1 m1 ->
                    begin match s1 with
                        v1 :: v0 :: s1 -> 
                        begin match (v0, v1) with
                            (VNum n0, VNum n1) ->
                            begin match op with
                                Plus -> c (VNum (n0 + n1) :: s1) t1 m1
                              | Minus -> c (VNum (n0 - n1) :: s1) t1 m1
                              | Times -> c (VNum (n0 * n1) :: s1) t1 m1
                              | Divide ->
                                if n1 = 0 then failwith "Division by zero"
                                else c (VNum (n0 / n1) :: s1) t1 m1
                              | Equal -> c (VBool (n0 = n1) :: s1) t1 m1
                              | Less -> c (VBool (n0 < n1) :: s1) t1 m1
                            end
                          | _ -> failwith (v_to_string v0 ^ " or " ^
                                           v_to_string v1 ^ " are not numbers")
                        end
                      | _ -> failwith "stack error"
                    end) (VEnv (vs) :: v0 :: s0) t0 m0
              | _ -> failwith "stack error"
            end) (VEnv (vs) :: VEnv (vs) :: s) t m
      | If (e0, e1, e2) ->
        f7 e0 xs (fun s t m ->
            begin match s with
                v :: VEnv (vs) :: s ->
                begin match v with
                    VBool (b) ->
                    f7 (if b then e1 else e2) xs c (VEnv (vs) :: s) t m 
                  | _ -> failwith
                           (v_to_string v ^
                            ": This expression was expected of type bool")
                end
              | _ -> failwith "stack error"
            end) (VEnv (vs) :: VEnv (vs) :: s) t m
      | Rec (g, x, e0, e1) ->
        let rec v0 =
          VFun (fun c s t m ->
              begin match s with
                  v :: s -> 
                  f7 e0 (x :: g :: xs) c (VEnv (v :: v0 :: vs) :: s) t m
                | _ -> failwith "stack error"
              end) in
        f7 e1 (g :: xs) c (VEnv (v0 :: vs) :: s) t m
      | TryWith (e0, x, k, e1) ->
        let h = fun c' s' t' m' ->
          begin match s' with
              vc :: v :: s' ->
              f7 e1 (k :: x :: xs) c' (VEnv (vc :: v :: vs) :: s') t' m'
            | _ -> failwith "stack error"
          end in
        f7 e0 xs idc (VEnv (vs) :: []) TNil (MCons ((c, s, t, h), m))
      | CallD e ->
        f7 e xs (fun s t m ->
            begin match s with
                v :: s -> 
                begin match m with
                    MCons ((c0, s0, t0, h), m0) ->
                    let vc = VFun (fun c' s' t' m' ->
                        begin match s' with
                            v' :: s' -> 
                            c (v' :: s) t (MCons ((c', s', t', h), m'))
                          | _ -> failwith "stack error"
                        end) in
                    h c0 (vc :: v :: s0) t0 m0
                  | _ -> failwith "call_d is used without enclosing try_with"
                end
              | _ -> failwith "stack error"
            end) (VEnv (vs) :: s) t m
      | CallS e ->
        f7 e xs (fun s t m ->
            begin match s with
                v :: s -> 
                begin match m with
                    MCons ((c0, s0, t0, h), m0) -> 
                    let vc = VFun (fun c' s' t' m' ->
                        begin match s' with
                            v' :: s' ->
                            c (v' :: s)
                              (apnd t (cons (fun v t m -> c' (v :: s') t m) t'))
                              m'
                          | _ -> failwith "stack error"
                        end) in
                    h c0 (vc :: v :: s0) t0 m0
                  | _ -> failwith "call_s is used without enclosing try_with"
                end
              | _ -> failwith "stack error"
            end) (VEnv (vs) :: s) t m
    end
  | _ -> failwith "stack error"
    
(* f : e -> v *)
let f e = f7 e [] idc (VEnv ([]) :: []) TNil MNil
