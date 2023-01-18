(* ----------------------------- *)
(* e : syntax *)
type e = Var of string
       | Fun of string * e
       | App of e * e
       | Shift of string * e
       | Control of string * e
       | Shift0 of string * e
       | Control0 of string * e
       | Reset of e
(* ----------------------------- *)

(* ------------------------------------------------------------- *)
(* env.ml *)
type 'a t = 'a list

let empty = []

(* exceptions *)
exception UnboundVariable

(* offset : string -> xs -> int *)
let offset x xs =
  let rec loop xs n = match xs with
      [] -> raise UnboundVariable
    | first :: rest -> if x = first then n else loop rest (n + 1)
  in
  loop xs 0
(* ------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* eval9 value *)
module M9 =
struct
  type v = VFun of i * v list
         | VContD of c * s * t * h
         | VContS of c * s * t
         | VEnv of v list
         | VC of c

  and i = IAccess of int
        | IPush_closure of i | IReturn | ICall
        | IPush_env | IPop_env
        | ITry_with of i * i | IMove_deep_handler | IMove_shallow_handler
        | ISeq of i * i

  and c = i list
      
  and s = v list
      
  and w = Hold of c * s | Append of w * w

  and t = TNil | Trail of w

  and h = i * v list
            
  and m = (c * s * t * h) list

(* Interpreter with defunctionalized continued, instructions : eval9 *)
(* initial continuation *)
let idc = []
  
(* cons : w -> t -> t *)
let cons w t = match t with
    TNil -> Trail (w)
  | Trail (w') -> Trail (Append (w, w'))

(* apnd : t -> t -> t *)
let apnd t0 t1 = match t0 with
    TNil -> t1
  | Trail (w) -> cons w t1

(* run_w9 : w -> v -> t -> m -> v *)
let rec run_h9 w v t m = match w with
    Hold (c, s) -> run_c9 c (v :: s) t m
  | Append (w, w') -> run_w9 w v (cons w' t) m

(* run_i9 : i -> c -> s -> t -> m -> v *)
let rec run_i9 i c s t m = match i with
    IAccess n ->
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
    Var x -> IAccess (Env.offset x xs)
  | Fun (x, e) -> IPush_closure (f9 e (x :: xs) >> IReturn)
  | App (e0, e1) -> IPush_env >> f9 e0 xs >> IPop_env >> f9 e1 xs >> ICall
  | TryWith (e0, x, k, e1) -> ITry_with (f9 e0 xs, f9 e1 (k :: x :: xs))
  | CallD e -> f9 e xs >> IMove_deep_handler
  | CallS e -> f9 e xs >> IMove_shallow_handler
           
(* f : e -> v *)
let f expr = run_i9 (f9 expr []) [] (VEnv ([]) :: []) TNil []
end
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* eval10 value *)
module M10 =
struct
  type v = VFun of c * v list
         | VContD of c * s * t * h
         | VContS of c * s * t
         | VEnv of v list
         | VC of c
             
  and i = IAccess of int
        | IPush_closure of c | IReturn | ICall
        | IPush_env | IPop_env
        | ITry_with of c * c | IMove_deep_handler | IMove_shallow_handler
          
  and c = i list
      
  and s = v list
      
  and w = Hold of c * s | Append of w * w

  and h = c * v list
                                    
  and t = TNil | Trail of w
            
  and m = (c * s * t * h) list

(* Interpreter with defunctionalized continued, instructions : eval10 *)
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
      | VContD (c', s', t', h) -> run_c10 c' (v1 :: s') t' ((c, s, t, h) :: m)
      | VContS (c', s', t') ->
        run_c10 c' (v1 :: s') (apnd t' (cons (Hold (c, s)) t)) m
      | _ -> failwith
               (v_to_string v0 ^ " is not a function; it can not be applied.")
    end
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
    Var x -> [IAccess (Env.offset x xs)]
  | Fun (x, e) -> [IPush_closure (f10 e (x :: xs) @ [IReturn])]
  | App (e0, e1) -> [IPush_env] @ f10 e0 xs @ [IPop_env] @ f10 e1 xs @ [ICall]
  | TryWith (e0, x, k, e1) -> [ITry_with (f10 e0 xs, f10 e1 (k :: x :: xs))]
  | CallD e -> f10 e xs @ [IMove_deep_handler]
  | CallS e -> f10 e xs @ [IMove_shallow_handler]
    
(* f : e -> v *)
let f expr = run_c10 (f10 expr []) (VEnv ([]) :: []) TNil []
end
(* -------------------------------------------------------------------------- *)



(* proof *)

(* ------------------------------------------------------------- *)
(* flat : M9.i -> M10.c *)
let rec flat i = begin match i with
    M9.IAccess (n) -> [M10.IAccess (n)]
  | M9.IPush_closure (i) -> [M10.IPush_closure (flat i)]
  | M9.IReturn -> [M10.IReturn]
  | M9.IPush_env -> [M10.IPush_env]
  | M9.IPop_env -> [M10.IPop_env]
  | M9.ICall -> [M10.ICall]
  | M9.ITry_with (i0, i1) [M10.ITry_with (flat i0, flat i1)]
  | M9.IMove_deep_handler -> [M10.IMove_deep_handler]
  | M9.IMove_shallow_handler -> [M10.IMove_shallow_handler]
  | M9.ISeq (i0, i1) -> (flat i0) @ (flat i1)
end
(* ------------------------------------------------------------- *)


(* -------------------------------- *)
(* flat (M9.f9 e xs) = M10.f10 e xs *)
(* -------------------------------- *)
  (* Var (x) *)
  flat (M9.f9 (Var (x)) xs)
= flat (M9.IAccess (offset x xs))
= [M10.IAccess (offset x xs)]
= M10.f10 Var (x) xs

  (* Fun (x, e) *)
  flat (M9.f9 (Fun (x, e)) xs)
= flat (M9.IPush_closure ((M9.f9 e (x :: xs)) >> M9.IReturn))
= [M10.IPush_closure (flat ((M9.f9 e (x :: xs)) >> M9.IReturn))]
= [M10.IPush_closure (flat (M9.ISeq (M9.f9 e (x :: xs), M9.IReturn)))]
= [M10.IPush_closure ((flat (M9.f9 e (x :: xs))) @ (flat  M9.IReturn))]
= [M10.IPush_closure ((M10.f10 e (x :: xs)) @ [M10.IReturn])]
= M10.f10 Fun (x, e) xs

  (* App (e0, e1) *)
  flat (M9.f9 (App (e0, e1)) xs)
= flat (M9.IPush_env >> (M9.f9 e0 xs)
                     >> M9.IPop_env >> (M9.f9 e1 xs) >> M9.ICall)
= flat (M9.ISeq (M9.IPush_env, M9.ISeq (M9.f9 e0 xs,
                M9.ISeq (M9.IPop_env, M9.ISeq (M9.f9 e1 xs, M9.ICall)))))
= (flat M9.IPush_env) @ (flat (M9.f9 e0 xs)) @ (flat M9.IPop_env)
      @ (flat (M9.f9 e1 xs)) @ (flat M9.ICall)
= [M10.IPush_env] @ (M10.f10 e0 xs) @ [M10.IPop_env]
      @ (M10.f10 e1 xs) @ [M10.ICall]
= M10.f10 App (e0, e1) xs

  (* TryWith (e0, x, k, e1) *)
  flat (M9.f9 (TryWith (e0, x, k, e1)) xs)
= flat (M9.ITry_with (M9.f9 e0 xs, M9.f9 e1 (k :: x :: xs)))
= [M10.ITry_with (flat (M9.f9 e0 xs), flat (M9.f9 e1 (k :: x :: xs)))]
= [M10.ITry_with (M10.f10 e0 xs, M10.f10 e1 (k :: x :: xs))]
= M10.f10 (TryWith (e0, x, k, e1)) xs

  (* CallD e *)
  flat (M9.f9 (CallD e) xs)
= flat (M9.f9 e xs >> M9.IMove_deep_handler)
= flat (M9.ISeq (M9.f9 e xs, M9.IMove_deep_handler))
= (flat M9.f9 e xs) @ (flat M9.IMove_deep_handler)
= (M10.f10 e xs) @ [M10.IMove_deep_handler]
= M10.f10 (CallD e) xs

  (* CallS e *)
  flat (M9.f9 (CallS e) xs)
= flat (M9.f9 e xs >> M9.IMove_shallow_handler)
= flat (M9.ISeq (M9.f9 e xs, M9.IMove_shallow_handler))
= (flat M9.f9 e xs) @ (flat M9.IMove_shallow_handler)
= (M10.f10 e xs) @ [M10.IMove_shallow_handler]
= M10.f10 (CallS e) xs
(* -------------------------------- *)


(* ----------------------------------- *)
(* flatC : M9.c -> M10.c *)
let rec flatC c = begin match c with
    [] -> []
  | i :: c -> (flat i) @ (flatC c)
end
(* ----------------------------------- *)

(* ---------------------------------------------------------------- *)
(* flatV : M9.v -> M10.v *)
let rec flatV v = begin match v with
    M9.VFun (i, vs) -> M10.VFun (flat i, List.map flatV vs)
  | M9.VContD (c, s, t, h) -> M10.VContD (flatC c, flatS s, flatT t, flatH h)
  | M9.VContS (c, s, t) -> M10.VContS (flatC c, flatS s, flatT t)
  | M9.VEnv (vs) -> M10.VEnv (List.map flatV vs)
  | M9.VC (c) -> M10.VC (flatC c)
end

(* flatS : M9.s -> M10.s *)
and flatS s = begin match s with
    [] -> []
  | v :: s -> (flatV v) :: (flatS s)
end

(* flatT : M9.t -> M10.t *)
and flatT t = begin match t with
    M9.TNil -> M10.TNil
  | M9.Trail (w) -> M10.Trail (flatW w)
end

(* flatW : M9.w -> M10.w *)
and flatW w = begin match w with
    M9.Hold (c, s) -> M10.Hold (flatC c, flatS s)
  | M9.Append (w, w') -> M10.Append (flatW w, flatW w')
end

(* flatH : M9.h -> M10.h *)
and flatH (i, vs) = (flat i, List.map flatV vs)

(* flatM : M9.m -> M10.m *)
let rec flatM m = begin match m with
    [] -> []
  | (c, s, t, h) :: m -> (flatC c, flatS s, flatT t, flatH h) :: (flatM m)
end
(* ---------------------------------------------------------------- *)


(* -------------------------------------------------- *)
(* flatT (M9.cons w t) = M10.cons (flatW w) (flatT t) *)
(* -------------------------------------------------- *)
  (* TNil *)
  flatT (M9.cons w M9.TNil)
= flatT (M9.Trail (w))
= M10.Trail (flatW w)
= M10.cons (flatW w) (M10.TNil)
= M10.cons (flatW w) (flatT M9.TNil)

  (* Trail (w') *)
  flatT (M9.cons w M9.Trail (w'))
= flatT (M9.Trail (M9.Append (w, w')))
= M10.Trail (M10.Append (flatW w, flatW w'))
= M10.cons (flatW w) (M10.Trail (flatW w'))
= M10.cons (flatW w) (flatT M9.Trail (w'))
(* -------------------------------------------------- *)


(* ------------------------------------------------------ *)
(* flatT (M9.apnd t0 t1) = M10.apnd (flatT t0) (flatT t1) *)
(* ------------------------------------------------------ *)
  (* TNil *)
  flatT (M9.apnd M9.TNil t1)
= flatT t1
= M10.apnd (M10.TNil) (flatT t1)
= M10.apnd (flatT M9.TNil) (flatT t1)

  (* Trail (w) *)
  flatT (M9.apnd (M9.Trail (w)) t1)
= flatT (M9.cons w t1)
= M10.cons (flatW w) (flatT t1)
= M10.apnd (M10.Trail (flatW w)) (flatT t1)
= M10.apnd (flatT (M9.Trail (w))) (flatT t1)
(* ------------------------------------------------------ *)


(* ---------------------------------------------------------------- *)
(* flatV (M9.run_i9 i c s t m) = 
   M10.run_c10 ((flat i) @ (flatC c)) (flatS s) (flatT t) (flatM m) *)
(* ---------------------------------------------------------------- *)
(* flatV (M9.run_c9 c s t m) = 
   M10.run_c10 (flatC c) (flatS s) (flatT t) (flatM m)              *)
(* ---------------------------------------------------------------- *)
(* flatV (M9.run_w9 h v t m) = 
   M10.run_w9 (flatW w) (flatV v) (flatT t) (flatM m)               *)
(* ---------------------------------------------------------------- *)
(* M9.run_w9 *)
   (* Hold (c, s) *)
   flatV (M9.run_w9 (M9.Hold (c, s)) v t m)
-> flatV (M9.run_c9 c (v :: s) t m)
ih M10.run_c10 (flatC c) (flatS (v :: s)) (flatT t) (flatM m)
=f M10.run_c10 (flatC c) ((flatV v) :: (flatS s)) (flatT t) (flatM m)
<- M10.run_w10 (M10.Hold (flatC c, flatS s)) (flatV v) (flatT t) (flatM m)
=f M10.run_w10 (flatW M9.Hold (c, s)) (flatV v) (flatT t) (flatM m)

  (* Append (w, w') *)
  flatV (M9.run_w9 (M9.Append (w, w')) v t m)
-> flatV (M9.run_w9 w v (M9.cons w' t) m)
ih M10.run_w10 (flatW w) (flatV v) (flatT (M9.cons w' t)) (flatM m)
=f M10.run_w10 (flatW w) (flatV v) (M10.cons (flatW w') (flatT t)) (flatM m)
<- M10.run_w10 (M10.Append (flatW w, flatW w')) (flatV v) (flatT t) (flatM m)
=f M10.run_w10 (flatW M9.Append (w, w')) (flatV v) (flatT t) (flatM m)


(* M9.run_c9 *)
   (* [] -- M9.TNil -- [] *)
   flatV (M9.run_c9 [] (v :: []) M9.TNil [])
-> flatV v
(* =f M10.v *)
<- M10.run_c10 [] ((flatV v) :: []) M10.TNil []
=f M10.run_c10 (flatC []) ((flatV v) :: (flatS [])) (flatT M9.TNil) (flatM [])
=f M10.run_c10 (flatC []) (flatS (v :: [])) (flatT M9.TNil) (flatM [])

   (* [] -- M9.TNil -- (c, s, t, h) :: m *)   (* flatH M9.h = M10.h ????? *)  
   flatV (M9.run_c9 [] (v :: []) M9.TNil ((c, s, t, h) :: m))
-> flatV (M9.run_c9 c (v :: s) t m)
ih M10.run_c10 (flatC c) (flatS (v :: s)) (flatT t) (flatM m)
=f M10.run_c10 (flatC c) ((flatV v) :: (flatS s)) (flatT t) (flatM m)
(* =f M10.run_c10 (flatC c) (M10.v :: (flatS s)) (flatT t) (flatM m) *)
<- M10.run_c10 [] ((flatV v) :: []) (M10.TNil)
               ((flatC c, flatS s, flatT t, flatH h) :: (flatM m))
=f M10.run_c10 (flatC []) (flatS (v :: [])) (flatT M9.TNil)
               (flatM ((c, s, t, h) :: m))

   (* [] -- Trail (w) *)
   flatV (M9.run_c9 [] (v :: []) (M9.Trail (w)) (flatM m))
-> flatV (M9.run_w9 w v M9.TNil m)
ih M10.run_w10 (flatW w) (flatV v) (flatT M9.TNil) (flatM m)
=f M10.run_w10 (flatW w) (flatV v) M10.TNil (flatM m)
<- M10.run_c10 [] ((flatV v) :: []) (M10.Trail (flatW w)) (flatM m)
=f M10.run_c10 (flatC []) (flatS (v :: [])) (flatT (M9.Trail (w))) (flatM m)

   (* i :: c *)
   flatV (M9.run_c9 (i :: c) s t m)
-> flatV (run_i9 i c s t m)
ih M10.run_c10 ((flat i) @ (flatC c)) (flatS s) (flatT t) (flatM m)
=f M10.run_c10 (flatC (i :: c)) (flatS s) (flatT t) (flatM m)


(* run_i9 *)
   (* IAccess *)
   flatV (M9.run_i9 (M9.IAccess (n)) c (M9.Env (vs) :: s) t m)
-> flatV (M9.run_c9 c ((List.nth M9.vs n) :: s) t m)
ih M10.run_c10 (flatC c) (flatS ((List.nth M9.vs n) :: s)) (flatT t) (flatM m)
=f M10.run_c10 (flatC c) ((List.nth M10.vs n) :: (flatS s)) (flatT t) (flatM m)
<- M10.run_c10 (M10.IAccess (n) :: (flatC c)) (M10.Env (vs) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.IAccess (n)] @ (flatC c)) (M10.Env (vs) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ((flat M9.IAccess (n)) @ (flatC c)) (flatS (M9.Env (vs) :: s))
               (flatT t) (flatM m)

   (* IPush_closure *)
   flatV (M9.run_i9 (M9.IPush_closure (i)) c (M9.Env (vs) :: s) t m)
-> flatV (M9.run_c9 c (M9.VFun (i, vs) :: s) t m)
ih M10.run_c10 (flatC c) (flatS (M9.VFun (i, vs) :: s)) (flatT t) (flatM m)
=f M10.run_c10 (flatC c) ((flatV (M9.VFun (i, vs))) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 (flatC c) ((M10.VFun (flat i, List.map flatV vs)) :: (flatS s))
               (flatT t) (flatM m)
<- M10.run_c10 ((M10.IPush_closure (flat i)) :: (flatC c))
               (M10.VEnv (List.map flatV vs) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.IPush_closure (flat i)] @ (flatC c))
               (flatS (M9.Env (vs) :: s))
               (flatT t) (flatM m)
=f M10.run_c10 ((flatI M9.IPush_closure (i)) @ (flatC c))
               (flatS (M9.Env (vs) :: s))
               (flatT t) (flatM m)

   (* IReturn *)
   flatV (M9.run_i9 M9.IReturn _ (v :: M9.VK (c') :: s) t m)
-> flatV (run_c9 c' (v :: s) t m)
ih M10.run_c10 (flatC c') (flatS (v :: s)) (flatT t) (flatM m)
=f M10.run_c10 (flatC c') ((flatV v) :: (flatS s)) (flatT t) (flatM m)
<- M10.run_c10 (M10.IReturn :: _) ((flatV v) :: M10.VK (flatC c') :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.IReturn] @ _) (flatS (v :: M9.VK (c') :: s))
               (flatT t) (flatM m)
=f M10.run_c10 ((flat M9.IReturn) @ _) (flatS (v :: M9.VK (c') :: s))
               (flatT t) (flatM m)

(* M10.vs = List.map flatV M9.vs *)

   (* IPush_env *)
   flatV (M9.run_i9 M9.IPush_env c (M9.Env (M9.vs) :: s) t m)
-> flatV (M9.run_c9 c (M9.VEnv (M9.vs) :: M9.VEnv (M9.vs) :: s) t m)
ih M10.run_c10 (flatC c) (flatS (M9.VEnv (M9.vs) :: M9.VEnv (M9.vs) :: s))
               (flatT t) (flatM m)
=f M10.run_c10 (flatC c)
               (M10.VEnv (M10.vs) :: M10.VEnv (M10.vs) :: (flatS s))
               (flatT t) (flatM m)
<- M10.run_c10 (M10.IPush_env :: (flatC c))
               (M10.VEnv (M10.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.IPush_env] @ (flatC c))
               (flatS (M9.Env (vs) :: s))
               (flatT t) (flatM m)
=f M10.run_c10 ((flat M9.IPush_env) @ (flatC c))
               (flatS (M9.Env (vs) :: s))
               (flatT t) (flatM m)

   (* IPop_env *)
   flatV (M9.run_i9 M9.IPop_env c (v :: M9.Env (M9.vs) :: s) t m)
-> flatV (M9.run_c9 c (M9.VEnv (M9.vs) :: v :: s) t m)
ih M10.run_c10 (flatC c) (flatS (M9.VEnv (M9.vs) :: v :: s)) 
               (flatT t) (flatM m)
=f M10.run_c10 (flatC c) (M10.VEnv (M10.vs) :: (flatV v) :: (flatS s)) 
               (flatT t) (flatM m)
<- M10.run_c10 (M10.IPop_env :: (flatC c))
               ((flatV v) :: M10.VEnv (M10.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.IPop_env] @ (flatC c))
               (flatS (v :: M9.Env (M9.vs) :: s)) (flatT t) (flatM m)
=f M10.run_c10 ((flat M9.IPop_env) @ (flatC c))
               (flatS (v :: M9.Env (M9.vs) :: s)) (flatT t) (flatM m)

   (* ICall -- VFun *)
   flatV (M9.run_i9 M9.ICall c (v :: M9.VFun (i, M9.vs) :: s) t m)
-> flatV (M9.run_i9 i [] (M9.VEnv (v :: M9.vs) :: M9.VK (c) :: s) t m)
ih M10.run_c10 ((flat i) @ [])
               (flatS (M9.VEnv (v :: M9.vs) :: M9.VK (c) :: s))
               (flatT t) (flatM m)
=f M10.run_c10 (flat i) 
               (M10.VEnv ((flatV v) :: M10.vs) :: M10.VK (flatC c) :: (flatS s))
               (flatT t) (flatM m)
<- M10.run_c10 (M10.ICall :: (flatC c))
               ((flatV v) :: M10.VFun (flat i, M10.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.ICall] @ (flatC c))
               (flatS (v :: M9.VFun (i, M9.vs) :: s)) (flatT t) (flatM m)
=f M10.run_c10 ((flat M9.ICall) @ (flatC c))
               (flatS (v :: M9.VFun (i, M9.vs) :: s)) (flatT t) (flatM m)

   (* ICall -- VContD *)
   flatV (M9.run_i9 M9.ICall c (v :: M9.VContS (c', s', t', h) :: s) t m)
-> flatV (M9.run_c9 c' (v :: s') t' ((c, s, t, h) :: m))
ih M10.run_c10 (flatC c') (flatS (v :: s')) (flatT t')
               (flatM ((c, s, t, h) :: m))
=f M10.run_c10 (flatC c') ((flatV v) :: (flatS s')) (flatT t')
               ((flatC c, flatS s, flatT t, faltH h) :: (flatM m))
<- M10.run_c10 (M10.ICall :: (flatC c))
               ((flatV v) :: M10.VContS (flatC c', flatS s', flatT t', flatH h)
                          :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.ICall] @ (flatC c))
               (flatS (v :: M9.VContS (c', s', t', h) :: s)) (flatT t) (flatM m)
=f M10.run_c10 ((flat M9.ICall) @ (flatC c))
               (flatS (v :: M9.VContS (c', s', t', h) :: s)) (flatT t) (flatM m)

   (* ICall -- VContS *)
   flatV (M9.run_i9 M9.ICall c (v :: M9.VContS (c', s', t') :: s) t m)
-> flatV (M9.run_c9 c' (v :: s')
                    (M9.apnd t' (M9.cons (M9.Hold (c, s)) t)) m)
ih M10.run_c10 (flatC c') (flatS (v :: s'))
               (flatT (M9.apnd t' (M9.cons (M9.Hold (c, s)) t))) (flatM m)
=f M10.run_c10 (flatC c') ((flatV v) :: (flatS s')) 
               (M10.apnd (flatT t')
                         (M10.cons (flatW (M9.Hold (c, s))) (flatT t)))
               (flatM m)
=f M10.run_c10 (flatC c') ((flatV v) :: (flatS s'))
               (M10.apnd (flatT t')
                         (M10.cons (M10.Hold (flatC c, flatS s)) (flatT t)))
               (flatM m)
<- M10.run_c10 (M10.ICall :: (flatC c))
               ((flatV v) :: M10.VContS (flatC c', flatS s', flatT t')
                          :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.ICall] @ (flatC c))
               (flatS (v :: M9.VContS (c', s', t') :: s)) (flatT t) (flatM m)
=f M10.run_c10 ((flat M9.ICall) @ (flatC c))
               (flatS (v :: M9.VContS (c', s', t') :: s)) (flatT t) (flatM m)

   (* ITry_with *)
   flatV (M9.run_i9 (M9.ITry_with (i0, i1)) c (M9.VEnv (M9.vs) :: s) t m)
-> flatV (M9.run_i9 i0 [] (M9.VEnv (M9.vs) :: []) M9.TNil 
                    ((c, s, t, (i1, M9.vs)) :: m))
ih M10.run_c10 ((flat i0) @ (flatC [])) (flatS (M9.VEnv (M9.vs) :: []))
               (flatT M9.TNil) (flatM ((c, s, t, (i1, M9.vs)) :: m))
=f M10.run_c10 (flat i0) ((flatV (M9.VEnv (M9.vs))) :: (flatS [])) M10.TNil 
               ((flatC c, flatS s, flatT t, flatH (i1, M9.vs)) :: (flatM m))
=f M10.run_c10 (flat i0) ((M10.VEnv (M10.vs)) :: []) M10.TNil 
               ((flatC c, flatS s, flatT t, (flat i1, M10.vs)) :: (flatM m))
<- M10.run_c10 (M10.ITry_with (flat i0, flati1) :: (flatC c)) 
               (M10.VEnv (M10.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M10.run_c10 ([M10.ITry_with (flat i0, flat i1)] @ (flatC c)) 
               (flatS (M9.VEnv (M9.vs) :: s))
               (flatT t) (flatM m)
=f M10.run_c10 ((flat (M9.ITry_with (i0, i1))) @ (flatC c)) 
               (flatS (M9.VEnv (M9.vs) :: s))
               (flatT t) (flatM m)

   (* IMove_deep_handler *)
   flatV (M9.run_i9 M9.IMove_deep_handler c (v :: s) t 
                    ((c0, s0, t0, (i, M9.vs)) :: m0))
-> flatV (M9.run_i9 i c0 (M9.VEnv 
                            (M9.VContD (c, s, t, (i, M9.vs)) :: v :: M9.vs)
                          :: s0) t0 m0)
ih M10.run_c10 ((flat i) @ (flatC c0))
               (flatS (M9.VEnv (M9.VContD (c, s, t, (i, M9.vs)) :: v :: M9.vs)
                          :: s0))
               (flatT t0) (flatM m0)
=f M10.run_c10 ((flat i) @ (flatC c0))
               (flatV (M9.VEnv (M9.VContD (c, s, t, (i, M9.vs)) :: v :: M9.vs))
                  :: (flatS s0))
               (flatT t0) (flatM m0)
=f M10.run_c10 ((flat i) @ (flatC c0))
               (M10.VEnv (M10.VContD (flatC c, flatS s, flatT t,
                                      flatH (i, M9.vs)) :: (flatV v) :: M10.vs)
                  :: (flatS s0))
               (flatT t0) (flatM m0)
=f M10.run_c10 ((flat i) @ (flatC c0))
               (M10.VEnv (M10.VContD (flatC c, flatS s, flatT t,
                                      (flat i, M10.vs)) :: (flatV v) :: M10.vs)
                  :: (flatS s0))
               (flatT t0) (flatM m0)
<- M10.run_c10 (M10.IMove_deep_handler :: (flatC c))
               ((flatV v) :: (flatS s)) (flatT t)
               ((flatC c0, flatS s0, flatT t0, (flat i, M10.vs)) :: (flatM m0))
=f M10.run_c10 ([M10.IMove_deep_handler] @ (flatC c))
               (flatS (v :: s)) (flatT t)
               (flatM ((c0, s0, t0, (i, M9.vs)) :: m0))
=f M10.run_c10 ((flat M9.IMove_deep_handler) @ (flatC c))
               (flatS (v :: s)) (flatT t)
               (flatM ((c0, s0, t0, (i, M9.vs)) :: m0))

   (* IMove_shallow_handler *)
   flatV (M9.run_i9 M9.IMove_shallow_handler c (v :: s) t 
                    ((c0, s0, t0, (i, M9.vs)) :: m0))
-> flatV (M9.run_i9 i c0 (M9.VEnv (M9.VContS (c, s, t) :: v :: M9.vs) :: s0)
                    t0 m0)
ih M10.run_c10 ((flat i) @ (flatC c0))
               (flatS (M9.VEnv (M9.VContS (c, s, t) :: v :: M9.vs) :: s0))
               (flatT t0) (flatM m0)
=f M10.run_c10 ((flat i) @ (flatC c0))
               (flatV (M9.VEnv (M9.VContS (c, s, t) :: v :: M9.vs))
                  :: (flatS s0))
               (flatT t0) (flatM m0)
=f M10.run_c10 ((flat i) @ (flatC c0))
               (M10.VEnv (M10.VContS (flatC c, flatS s, flatT t)
                            :: (flatV v) :: M10.vs)
                  :: (flatS s0))
               (flatT t0) (flatM m0)
<- M10.run_c10 (M10.IMove_shallow_handler :: (flatC c))
               ((flatV v) :: (flatS s)) (flatT t)
               ((flatC c0, flatS s0, flatT t0, (flat i, M10.vs)) :: (flatM m0))
=f M10.run_c10 ([M10.IMove_shallow_handler] @ (flatC c))
               (flatS (v :: s)) (flatT t)
               (flatM ((c0, s0, t0, (i, M9.vs)) :: m0))
=f M10.run_c10 ((flat M9.IMove_shallow_handler) @ (flatC c))
               (flatS (v :: s)) (flatT t)
               (flatM ((c0, s0, t0, (i, M9.vs)) :: m0))

   (* ISeq *)
  flatV (M9.run_c9 (M9.ISeq (i0, i1)) c s t m)
-> flatV (M9.run_i9 i0 (i1 :: c) s t m)
ih M10.run_c10 ((flat i0) @ (flatC (i1 :: c))) (flatS s) (flatT t) (flatM m)
=f M10.run_c10 ((flat i0) @ (flat i1) @ (flatC c)) (flatS s) (flatT t) (flatM m)
=f M10.run_c10 ((flat (M9.ISeq (i0, i1))) @ (flatC c))
               (flatS s) (flatT t) (flatM m)













