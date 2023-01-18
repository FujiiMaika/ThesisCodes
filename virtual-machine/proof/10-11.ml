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

(* ----------------------------------------------------------------- *)
(* instruction *)
type i = IAccess of int
       | IPush_closure of c | IReturn | ICall
       | IPush_env | IPop_env
       | ITry_with of c * c | IMove_deep_handler | IMove_shallow_handler

(* continuation *)
and c = i list
(* ----------------------------------------------------------------- *)

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
(* eval10 value *)
module M10 =
struct
  type v = VFun of c * v list
         | VContD of c * s * t * h
         | VContS of c * s * t
         | VEnv of v list
         | VC of c
      
  and s = v list
      
  and w = Hold of c * s | Append of w * w
                                    
  and t = TNil | Trail of w

  and h = c * v list
            
  and m = (c * s * t * h) list

(* Interpreter with linear instructions : eval10 *)
(* cons : w -> t -> t *)
let cons w t = match t with
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

(* -------------------------------------------------------------------------- *)
(* eval11 value *)
module M11 =
struct
  type v = VFun of c * v list
         | VContD of c * s * t * h
         | VContS of c * s * t
         | VEnv of v list
         | VC of c
      
  and s = v list
      
  and t = (c * s) list

  and h = c * v list
      
  and m = (c * s * t * h) list
  
(* Interpreter with linear trail : eval11 *)
(* run_c11 : c -> s -> t -> m -> v *)
let rec run_c11 c s t m = match (c, s) with
    ([], v :: []) ->
    begin match t with
        [] ->
        begin match m with
            [] -> v
          | (c, s, t, h) :: m -> run_c11 c (v :: s) t m
        end
      | (c, s) :: t -> run_c11 c (v :: s) t m
    end
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
      | VContD (c', s', t', h) -> run_c11 c' (v1 :: s') t' ((c, s, t, h) :: m)
      | VContS (c', s', t') -> run_c11 c' (v1 :: s') (t' @ (c, s) :: t) m
      | _ -> failwith
               (v_to_string v0 ^ " is not a function; it can not be applied.")
    end
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
    Var x -> [IAccess (Env.offset x xs)]
  | Fun (x, e) -> [IPush_closure (f11 e (x :: xs) @ [IReturn])]
  | App (e0, e1) -> [IPush_env] @ f11 e0 xs @ [IPop_env] @ f11 e1 xs @ [ICall]
  | TryWith (e0, x, k, e1) -> [ITry_with (f11 e0 xs, f11 e1 (k :: x :: xs))]
  | CallD e -> f11 e xs @ [IMove_deep_handler]
  | CallS e -> f11 e xs @ [IMove_shallow_handler]
           
(* f : e -> v *)
let f expr = run_c11 (f11 expr []) (VEnv ([]) :: []) [] []
end
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* flatV : M10.v -> M11.v *)
let rec flatV v = begin match v with
    M10.VFun (c, vs) -> M11.VFun (c, List.map flatV vs)
  | M10.VContD (c, s, t, h) -> M11.VContD (c, flatS s, flatT t, faltH h)
  | M10.VContC (c, s, t) -> M11.VContS (c, flatS s, flatT t)
  | M10.VEnv (vs) -> M11.VEnv (List.map flatV vs)
  | M10.VC (c) -> M11.VC (c)
end

(* flatS : M10.s -> M11.s *)
and flatS s = begin match s with
    [] -> []
  | v :: s -> (flatV v) :: (flatS s)
end

(* flatT : M10.t -> M11.t *)
and flatT t = begin match t with
    M10.TNil -> []
  | M10.Trail (w) -> flatW w
end

(* flatW : M10.w -> M11.t *)
and flatW w = begin match w with
    M10.Hold (c, s) -> (c, flatS s) :: []
  | M10.Append (w, w') -> (flatW w) @ (flatW w')
end

(* flatH : M10.h -> M11.h *)
and flatH (c, vs) = (c, List.map flatV vs)

(* flatM : M10.m -> M11.m *)
let rec flatM m = begin match m with
    [] -> []
  | (c, s, t, h) :: m -> (c, flatS s, flatT t, flatH h) :: (flatM m)
end
(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)
(* flatT (M10.cons w t) = (flatW w) @ (flatT t) *)
(* -------------------------------------------------------------------------- *)
  (* M10.TNil *)
  flatT (M10.cons w M10.TNil)
= faltT (Trail (w))
= flatW w
= (flatW w) @ []
= (flatW w) @ (flatT M10.TNil)

  (* M10.Trail (w') *)
  flatT (M10.cons w (M10.Trail (w')))
= flatT (Trail (M10.Append (w, w')))
= (flatW w) @ (flatW w')
= (flatW w) @ (flatT (M10.Trail (w')))
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* flatT (M10.apnd t0 t1) = (flatT t0) @ (flatT t1) *)
(* -------------------------------------------------------------------------- *)
  (* M10.TNil *)
  flatT (M10.apnd M10.TNil t1)
= flatT t1
= [] @ (flatT t1)
= (flatT M10.TNil) @ (flatT t1)

  (* M10.Trail (w) *)
  flatT (M10.apnd (M10.Trail (w)) t1)
= flatT (M10.cons w t1)
= (flatW w) @ (flatT t1)
= (flatT (M10.Trail (w))) @ (flatT t1)
(* -------------------------------------------------------------------------- *)


(* flatV (M10.run_h10 h v t m) = M11.run_c11 .... いらない??? *)



(* -------------------------------------------------------------------------- *)
(* flatV (M10.run_c10 c s t m) = M11.run_c11 c (flatS s) (flatT t) (flatM m) *)
(* -------------------------------------------------------------------------- *)
   (* [] -- TNil -- [] *)
   flatV (M10.run_c10 [] (v :: []) M10.TNil [])
-> flatV v
<- M11.run_c11 [] ((flatV v) :: []) [] []
=f M11.run_c11 [] (flatS (v :: [])) (flatT M10.TNil) (flatM [])

   (* [] -- TNil -- (c, s, t, h) :: m *)
   flatV (M10.run_c10 [] (v :: []) M10.TNil ((c, s, t, h) :: m))
-> flatV (M10.run_c10 c (v :: s) t m)
ih M11.run_c11 c (flatS (v :: s)) (flatT t) (flatM m)
=f M11.run_c11 c ((flatV v) :: (flatS s)) (flatT t) (flatM m)
<- M11.run_c11 [] ((flatV v) :: []) []
               ((c, flatS s, flatT t, flatH h) :: (flatM m))
=f M11.run_c11 [] (flatS (v :: [])) (flatT M10.TNil) (flatM ((c, s, t, h) :: m))

   (* Trail (Hold (c, s)) *)
   flatV (M10.run_c10 [] (v :: []) (M10.Trail (M10.Hold (c, s))) m)
-> flatV (M10.run_w10 (M10.Hold (c, s)) v M10.TNil m)
-> flatV (M10.run_c10 c (v :: s) M10.TNil m)
ih M11.run_c11 c (flatS (v :: s)) (flatT M10.TNil) (flatM m)
=f M11.run_c11 c ((flatV v) :: (flatS s)) [] (flatM m)
<- M11.run_c11 [] ((flatV v) :: []) ((c, flatS s) :: []) (flatM m)
=f M11.run_c11 [] (flatS (v :: [])) (flatW (M10.Hold (c, s))) (flatM m)
=f M11.run_c11 [] (flatS (v :: []))
               (flatT (M10.Trail (M10.Hold (c, s)))) (flatM m)

   (* Trail (Append (w, w')) *) (* w = M10.Hold (c, s) *)
   flatV (M10.run_c10 [] (v :: []) (M10.Trail (M10.Append (w, w'))) m)
-> flatV (M10.run_w10 (M10.Append (w, w')) v (M10.TNil) m)
-> flatV (M10.run_w10 w v (cons w' (M10.TNil)) m)
=  flatV (M10.run_w10 (M10.Hold (c, s)) v (cons w' (M10.TNil)) m)
-> flatV (M10.run_c10 c (v :: s) (cons w' (M10.TNil)) m)
ih M11.run_c11 c (flatS (v :: s)) (flatT (cons w' (M10.TNil))) (flatM m)
=f M11.run_c11 c ((flatV v) :: (flatS s)) ((flatW w') @ (flatT M10.TNil))
               (flatM m)
=f M11.run_c11 c ((flatV v) :: (flatS s)) (flatW w') (flatM m)
<- M11.run_c11 [] ((flatV v) :: []) ((c, flatS s) :: (flatW w')) (flatM m)
=f M11.run_c11 [] (flatS (v :: [])) ([(c, flatS s)] @ (flatW w')) (flatM m)
=f M11.run_c11 [] (flatS (v :: []))
               ((flatW M10.Hold (c, s)) @ (flatW w')) (flatM m)
=  M11.run_c11 [] (flatS (v :: [])) ((flatW w) @ (flatW w')) (flatM m)
=f M11.run_c11 [] (flatS (v :: [])) (flatW (M10.Append (w, w'))) (flatM m)
=f M11.run_c11 [] (flatS (v :: []))
               (flatT (M10.Trail (M10.Append (w, w')))) (flatM m)

   (* Trail (Append (w, w')) *) (* w = M10.Append (w0, w1) *)
   (* w0 = M10.Hold (c, s) *)
   flatV (M10.run_c10 [] (v :: []) (M10.Trail (M10.Append (w, w'))) m)
-> flatV (M10.run_w10 (M10.Append (w, w')) v M10.TNil m)
-> flatV (M10.run_w10 w v (cons w' M10.TNil) m)
=  flatV (M10.run_w10 (M10.Append (w0, w1)) v (cons w' M10.TNil) m)
-> flatV (M10.run_w10 w0 v (cons w1 (cons w' M10.TNil)) m)
=  flatV (M10.run_w10 (M10.Hold (c, s)) v (cons w1 (cons w' M10.TNil)) m) (*1*)
-> flatV (M10.run_c10 c (v :: s) (cons w1 (cons w' M10.TNil)) m)
ih M11.run_c11 c (flatS (v :: s)) (flatT (cons w1 (cons w' M10.TNil))) (flatM m)
=f M11.run_c11 c ((flatV v) :: (flatS s))
               ((flatW w1) @ (flatW w') @ (flatT M10.TNil)) (flatM m)
=f M11.run_c11 c ((flatV v) :: (flatS s))
               ((flatW w1) @ (flatW w') @ []) (flatM m)
=  M11.run_c11 c ((flatV v) :: (flatS s)) ((flatW w1) @ (flatW w')) (flatM m)
<- M11.run_c11 [] ((flatV v) :: [])
               ((c, flatS s) :: (flatW w1) @ (flatW w')) (flatM m)
=f M11.run_c11 [] ((flatV v) :: [])
               ([(c, flatS s)] @ (flatW w1) @ (flatW w')) (flatM m)
=f M11.run_c11 [] ((flatV v) :: [])
               ((flatW M10.Hold (c, s)) @ (flatW w1) @ (flatW w')) (flatM m)
=  M11.run_c11 [] ((flatV v) :: [])
               ((flatW w0) @ (flatW w1) @ (flatW w')) (flatM m)
=f M11.run_c11 [] ((flatV v) :: [])
               ((flatW M10.Append (w0, w1)) @ (flatW w')) (flatM m)
=  M11.run_c11 [] ((flatV v) :: []) ((flatW w) @ (flatW w')) (flatM m)
=f M11.run_c11 [] ((flatV v) :: []) (flatW M10.Append (w, w')) (flatM m)
=f M11.run_c11 [] ((flatV v) :: [])
               (flatT (M10.Trail (M10.Append (w, w')))) (flatM m)

   (* Trail (Append (w, w')) *) (* w = M10.Append (w0, w1) *)
   (* w0 = M10.Append (w01, w02) *)
   flatV (M10.run_c10 [] (v :: []) (M10.Trail (M10.Append (w, w'))) m)
-> flatV (M10.run_w10 (M10.Append (w, w')) v M10.TNil m)
-> flatV (M10.run_w10 w v (cons w' M10.TNil) m)
=  flatV (M10.run_w10 (M10.Append (w0, w1)) v (cons w' M10.TNil) m)
-> flatV (M10.run_w10 w0 v (cons w1 (cons w' M10.TNil)) m)
=  flatV (M10.run_w10 (M10.Append (w01, w02)) v (cons w1 (cons w' M10.TNil)) m)
   (*2*)
-> flatV (M10.run_w10 w01 v (cons w02 (cons w1 (cons w' M10.TNil))) m)
   (* w01 が M10.Hold (c, s) になるまで (*2*) を繰り返し、
      到達したら (*1*) のように展開していく *)
         ...
=  M11.run_c11 [] (flatS (v :: [])) (flatT (M10.Trail (M10.Append (w, w'))))
               (flatM M)

   (* IAcceess *)
   flatV (M10.run_c10 (IAccess (n) :: c) (M10.VEnv (M10.vs) :: s) t m)
-> flatV (M10.run_c10 c ((List.nth M10.vs n) :: s) t m)
ih M11.run_c11 c (flatS ((List.nth M10.vs n) :: s)) (flatT t) (flatM m)
=f M11.run_c11 c ((List.nth M11.vs n) :: (flatS s)) (flatT t) (flatM m)
<- M11.run_c11 (IAccess (n) :: c) (M11.VEnv (M11.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (IAccess (n) :: c) (flatS (M10.VEnv (M10.vs) :: s))
               (flatT t) (flatM m)

   (* IPush_closure *)
   flatV (M10.run_c10 (IPush_closure (c') :: c) (M10.VEnv (M10.vs) :: s) t m)
-> flatV (M10.run_c10 c (VFun (c', vs) :: s) t m)
ih M11.run_c11 c (flatS (VFun (c', vs) :: s)) (flatT t) (flatM m)
=f M11.run_c11 c (M11.VFun (c', M11.vs) :: (flatS s)) (flatT t) (flatM m)
<- M11.run_c11 (IPush_closure (c') :: c) (M11.VEnv (M11.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (IPush_closure (c') :: c) (flatS (M10.VEnv (M10.vs) :: s))
               (flatT t) (flatM m)

   (* IReturn *)
   flatV (M10.run_c10 (IReturn :: _) (v :: M10.VC (c) :: s) t m)
-> flatV (M11.run_c10 c (v :: s) t m)
ih M11.run_c11 c (flatS (v :: s)) (flatT t) (flatM m)
=f M11.run_c11 c ((flatV v) :: (flatS s)) (flatT t) (flatM m)
<- M11.run_c11 (IReturn :: _) ((flatV v) :: M11.VC (c) :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (IReturn :: _) (flatS (v :: M10.VC (c) :: s)) (flatT t) (flatM m)

   (* IPush_env *)
   flatV (M10.run_c10 (IPush_env :: c) (M10.VEnv (M10.vs) :: s) t m)
-> flatV (M10.run_c10 c (M10.VEnv (M10.vs) :: M10.VEnv (M10.vs) :: s) t m)
ih M11.run_c11 c (flatS (M10.VEnv (M10.vs) :: M10.VEnv (M10.vs) :: s))
               (flatT t) (flatM m)
=f M11.run_c11 c (M11.VEnv (M11.vs) :: M11.VEnv (M11.vs) :: (flatS s))
               (flatT t) (flatM m)
<- M11.run_c11 (IPush_env :: c) (M11.VEnv (M11.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (IPush_env :: c) (flatS (M10.VEnv (M10.vs) :: s))
               (flatT t) (flatM m)

   (* IPop_env *)
   flatV (M10.run_c10 (IPop_env :: c) (v :: M10.VEnv (M10.vs) :: s) t m)
-> flatV (M10.run_c10 c (M10.VEnv (M10.vs) :: v :: s) t m)
ih M11.run_c11 c (flatS (M10.VEnv (M10.vs) :: v :: s)) (flatT t) (flatM m)
=f M11.run_c11 c (M11.VEnv (M11.vs) :: (flatV v) :: (flatS s))
               (flatT t) (flatM m)
<- M11.run_c11 (IPop_env :: c) ((flatV v) :: M11.VEnv (M11.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (IPop_env :: c) (flatS (v :: M10.VEnv (M10.vs) :: s))
               (flatT t) (flatM m)

   (* ICall -- VFun *)
   flatV (M10.run_c10 (ICall :: c) (v :: M10.VFun (c', M10.vs) :: s) t m)
-> flatV (M10.run_c10 c' (M10.VEnv (v :: M10.vs) :: M10.VC (c) :: s) t m)
ih M11.run_c11 c' (flatS (M10.VEnv (v :: M10.vs) :: M10.VC (c) :: s))
               (flatT t) (flatM m)
=f M11.run_c11 c' (M11.VEnv ((flatV v) :: M11.vs) :: M11.VC (c) :: (flatS s))
               (flatT t) (flatM m)
<- M11.run_c11 (ICall :: c) ((flatV v) :: M11.VFun (c', M11.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (ICall :: c) (flatS (v :: M10.VFun (c', M10.vs) :: s))
               (flatT t) (flatM m)

   (* ICall -- VContD *)
   flatV (M10.run_c10 (ICall :: c) (v :: M10.VContD (c', s', t', h) :: s) t m)
-> flatV (M10.run_c10 c' (v :: s') t' ((c, s, t, h) :: m))
ih M11.run_c11 c' (flatS (v :: s')) (flatT t') (flatM ((c, s, t, h) :: m))
=f M11.run_c11 c' ((flatV v) :: (flatS s')) (flatT t')
               ((c, flatS s, flatT t, flatH h) :: (flatM m))
<- M11.run_c11 (ICall :: c)
               ((flatV v) :: M11.VContD (c', flatS s', flatT t', flatH h)
                          :: (flatS s)) (flatT t) (flatM m)
=f M11.run_c11 (ICall :: c) (flatS (v :: M10.VContD (c', s', t', h) :: s)) 
               (flatT t) (flatM m)

   (* ICall -- VContS *)
   flatV (M10.run_c10 (ICall :: c) (v :: M10.VContS (c', s', t') :: s) t m)
-> flatV (M10.run_c10 c' (v :: s')
                      (M10.apnd t' (M10.cons (M10.Hold (c, s)) t)) m)
ih M11.run_c11 c' (flatS (v :: s'))
               (flatT (M10.apnd t' (M10.cons (M10.Hold (c, s)) t))) (flatM m)
=f M11.run_c11 c' ((flatV v) :: (flatS s'))
               ((flatT t') @ (flatW M10.Hold (c, s)) @ (flatT t)) (flatM m)
=f M11.run_c11 c' ((flatV v) :: (flatS s'))
               ((flatT t') @ [(c, flatS s)] @ (flatT t)) (flatM m)
=  M11.run_c11 c' ((flatV v) :: (flatS s'))
               ((flatT t') @ ((c, flatS s) :: (flatT t))) (flatM m)
<- M11.run_c11 (ICall :: c)
               ((flatV v) :: M11.VContS (c', flatS s', flatT t') :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (ICall :: c) (flatS (v :: M10.VContS (c', s', t') :: s)) 
               (flatT t) (flatM m)

   (* ITry_with *)
   flatV (M10.run_c10 (ITry_with (c0, c1) :: c) (M10.VEnv (M10.vs) :: s) t m)
-> flatV (M10.run_c10 c0 (M10.VEnv (M10.vs) :: []) M10.TNil 
                      ((c, s, t, (c1, M10.vs)) :: m))
ih M11.run_c11 c0 (flatS (M10.VEnv (M10.vs) :: [])) (flatT M10.TNil)
               (flatM ((c, s, t, (c1, M10.vs)) :: m))
=f M11.run_c11 c0 (M11.VEnv (M11.vs) :: (flatS [])) []
               ((c, flatS s, flatT t, flatH (c1, M10.vs)) :: (flatM m))
=f M11.run_c11 c0 (M11.VEnv (M11.vs) :: []) []
               ((c, flatS s, flatT t, (c1, M11.vs)) :: (flatM m))
<- M11.run_c11 (ITry_with (c0, c1) :: c) (M11.VEnv (M11.vs) :: (flatS s))
               (flatT t) (flatM m)
=f M11.run_c11 (ITry_with (c0, c1) :: c) (flatS (M10.VEnv (M10.vs) :: s))
               (flatT t) (flatM m)

   (* IMove_deep_handler *)
   flatV (M10.run_c10 (IMove_deep_handler :: c) (v :: s) t 
                      ((c0, s0, t0, (c', M10.vs)) :: m0))
-> flatV (M10.run_c10 (c' @ c0) 
                      (M10.VEnv
                         (M10.VContD (c, s, t, (c', M10.vs)) :: v :: M10.vs)
                       :: s0) t0 m0)
ih M11.run_c11 (c' @ c0)
               (flatS (M10.VEnv
                         (M10.VContD (c, s, t, (c', M10.vs)) :: v :: M10.vs)
                       :: s0)) (flatT t0) (flatM m0)
=f M11.run_c11 (c' @ c0)
               (M11.VEnv (M11.VContD (c, flatS s, flatT t, (c', M11.vs))
                          :: (flatV v) :: M11.vs)
                :: (flatS s0)) (flatT t0) (flatM m0)
<- M11.run_c11 (IMove_deep_handler :: c) ((flatV v) :: (flatS s)) (flatT t)
               ((c0, flatS s0, flatT t0, (c', M11.vs)) :: (flatM m0))
=f M11.run_c11 (IMove_deep_handler :: c) (flatS (v :: s)) (flatT t)
               (flatM ((c0, s0, t0, (c', M10.vs)) :: m0))

   (* IMove_shallow_handler *)
   flatV (M10.run_c10 (IMove_shallow_handler :: c) (v :: s) t 
                      ((c0, s0, t0, (c', M10.vs)) :: m0))
-> flatV (M10.run_c10 (c' @ c0) 
                      (M10.VEnv (M10.VContS (c, s, t) :: v :: M10.vs) :: s0)
                      t0 m0)
ih M11.run_c11 (c' @ c0)
               (flatS (M10.VEnv (M10.VContS (c, s, t) :: v :: M10.vs) :: s0))
               (flatT t0) (flatM m0)
=f M11.run_c11 (c' @ c0)
               (M11.VEnv (M11.VContS (c, flatS s, flatT t) :: (flatV v)
                          :: M11.vs) :: (flatS s0))
               (flatT t0) (flatM m0)
<- M11.run_c11 (IMove_shallow_handler :: c) ((flatV v) :: (flatS s)) (flatT t)
               ((c0, flatS s0, flatT t0, (c', M11.vs)) :: (flatM m0))
=f M11.run_c11 (IMove_shallow_handler :: c) (flatS (v :: s)) (flatT t)
               (flatM ((c0, s0, t0, (c', M10.vs)) :: m0))





