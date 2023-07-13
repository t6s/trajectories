
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)
 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

type 't pred = 't -> bool

type 't rel = 't -> 't pred

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S n1 -> eq_dec n0 n1)
 end

module Pos =
 struct
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q0 =
    match p with
    | XI p0 -> (match q0 with
                | XI q1 -> eqb p0 q1
                | _ -> False)
    | XO p0 -> (match q0 with
                | XO q1 -> eqb p0 q1
                | _ -> False)
    | XH -> (match q0 with
             | XH -> True
             | _ -> False)

  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod) prod **)

  let rec ggcdn n a b =
    match n with
    | O -> Pair (XH, (Pair (a, b)))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n0 (sub b' a') a in
               let Pair (ba, aa) = p in Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n0 (sub a' b') b in
               let Pair (ab, bb) = p in Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n0 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI _ ->
            let Pair (g, p) = ggcdn n0 a0 b in
            let Pair (aa, bb) = p in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n0 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default
            | Cons (_, t0) -> nth m t0 default)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

(** val rev_append : 'a1 list -> 'a1 list -> 'a1 list **)

let rec rev_append l l' =
  match l with
  | Nil -> l'
  | Cons (a, l0) -> rev_append l0 (Cons (a, l'))

(** val concat : 'a1 list list -> 'a1 list **)

let rec concat = function
| Nil -> Nil
| Cons (x, l0) -> app x (concat l0)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t0) -> Cons ((f a), (map f t0))

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, t0) -> f b (fold_right f a0 t0)

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> False
| Cons (a, l0) -> (match f a with
                   | True -> True
                   | False -> existsb f l0)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f x with
   | True -> Cons (x, (filter f l0))
   | False -> filter f l0)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Nil -> None
| Cons (x, tl) -> (match f x with
                   | True -> Some x
                   | False -> find f tl)

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Coq_Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Coq_Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Coq_Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Coq_Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Coq_Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Coq_Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Coq_Pos.mul x' y')
       | Zneg y' -> Zneg (Coq_Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Coq_Pos.mul x' y')
       | Zneg y' -> Zpos (Coq_Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Coq_Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Coq_Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q0 -> Coq_Pos.eqb p q0
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q0 -> Coq_Pos.eqb p q0
                 | _ -> False)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos p -> (match y with
                 | Zpos p0 -> Coq_Pos.eq_dec p p0
                 | _ -> Right)
    | Zneg p -> (match y with
                 | Zneg p0 -> Coq_Pos.eq_dec p p0
                 | _ -> Right)
 end

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | Eq -> True
  | _ -> False

(** val head : 'a1 -> 'a1 list -> 'a1 **)

let head x0 = function
| Nil -> x0
| Cons (x, _) -> x

(** val behead : 'a1 list -> 'a1 list **)

let behead = function
| Nil -> Nil
| Cons (_, s') -> s'

(** val last : 'a1 -> 'a1 list -> 'a1 **)

let rec last x = function
| Nil -> x
| Cons (x', s') -> last x' s'

(** val belast : 'a1 -> 'a1 list -> 'a1 list **)

let rec belast x = function
| Nil -> Nil
| Cons (x', s') -> Cons (x, (belast x' s'))

(** val iota : nat -> nat -> nat list **)

let rec iota m = function
| O -> Nil
| S n' -> Cons (m, (iota (S m) n'))

(** val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

let rec merge leT s1 = match s1 with
| Nil -> (fun x -> x)
| Cons (x1, s1') ->
  let rec merge_s1 s2 = match s2 with
  | Nil -> s1
  | Cons (x2, s2') ->
    (match leT x1 x2 with
     | True -> Cons (x1, (merge leT s1' s2))
     | False -> Cons (x2, (merge_s1 s2')))
  in merge_s1

(** val merge_sort_push :
    'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec merge_sort_push leT s1 ss = match ss with
| Nil -> Cons (s1, ss)
| Cons (s2, ss') ->
  (match s2 with
   | Nil -> Cons (s1, ss')
   | Cons (_, _) -> Cons (Nil, (merge_sort_push leT (merge leT s2 s1) ss')))

(** val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list **)

let rec merge_sort_pop leT s1 = function
| Nil -> s1
| Cons (s2, ss') -> merge_sort_pop leT (merge leT s2 s1) ss'

(** val merge_sort_rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec merge_sort_rec leT ss s = match s with
| Nil -> merge_sort_pop leT s ss
| Cons (x1, l) ->
  (match l with
   | Nil -> merge_sort_pop leT s ss
   | Cons (x2, s') ->
     let s1 =
       match leT x1 x2 with
       | True -> Cons (x1, (Cons (x2, Nil)))
       | False -> Cons (x2, (Cons (x1, Nil)))
     in
     merge_sort_rec leT (merge_sort_push leT s1 ss) s')

(** val sort : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort leT =
  merge_sort_rec leT Nil

type q = { qnum : z; qden : positive }

(** val qeq_bool : q -> q -> bool **)

let qeq_bool x y =
  zeq_bool (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qle_bool : q -> q -> bool **)

let qle_bool x y =
  Z.leb (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let Pair (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x y =
    match O.compare x y with
    | LT -> Left
    | _ -> Right

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x y =
    match eq_dec x y with
    | Left -> True
    | Right -> False
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module Nat_as_OT =
 struct
  type t = nat

  (** val compare : nat -> nat -> nat compare0 **)

  let compare x y =
    match Nat.compare x y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : nat -> nat -> sumbool **)

  let eq_dec =
    Nat.eq_dec
 end

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t, 'elt) prod list

  (** val empty : 'a1 t **)

  let empty =
    Nil

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | Nil -> True
  | Cons (_, _) -> False

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | Nil -> False
  | Cons (p, l) ->
    let Pair (k', _) = p in
    (match X.compare k k' with
     | LT -> False
     | EQ -> True
     | GT -> mem k l)

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_mem_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * bool
     * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
      -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 f2 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l) -> f1 s k' _x l __ __ __
  | R_mem_3 (s, k', _x, l, _res, r0) ->
    f2 s k' _x l __ __ __ _res r0 (coq_R_mem_rec k f f0 f1 f2 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | Nil -> f3 __
     | Cons (a, l) ->
       let Pair (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ -> let hrec = mem_rect k f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_3 (y, y0, y1, y2, (mem k y2),
      (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | Nil -> None
  | Cons (p, s') ->
    let Pair (k', x) = p in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x
     | GT -> find k s')

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_find_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt option
     * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rect k f f0 f1 f2 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 f2 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s') -> f1 s k' x s' __ __ __
  | R_find_3 (s, k', x, s', _res, r0) ->
    f2 s k' x s' __ __ __ _res r0 (coq_R_find_rec k f f0 f1 f2 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | Nil -> f3 __
     | Cons (a, l) ->
       let Pair (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ -> let hrec = find_rect k f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_3 (y, y0, y1, y2, (find k y2),
      (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x s = match s with
  | Nil -> Cons ((Pair (k, x)), Nil)
  | Cons (p, l) ->
    let Pair (k', y) = p in
    (match X.compare k k' with
     | LT -> Cons ((Pair (k, x)), s)
     | EQ -> Cons ((Pair (k, x)), l)
     | GT -> Cons ((Pair (k', y)), (add k x l)))

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_add_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rect k x f f0 f1 f2 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
      -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 f2 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l) -> f1 s k' y l __ __ __
  | R_add_3 (s, k', y, l, _res, r0) ->
    f2 s k' y l __ __ __ _res r0 (coq_R_add_rec k x f f0 f1 f2 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | Nil -> f3 __
     | Cons (a, l) ->
       let Pair (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ ->
         let hrec = add_rect k x f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t, 'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y) (fun y y0 y1 y2 _ _ _ _ _ ->
      R_add_1 (y, y0, y1, y2)) (fun y y0 y1 y2 _ _ _ _ _ -> R_add_2 (y, y0,
      y1, y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_3 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | Nil -> Nil
  | Cons (p, l) ->
    let Pair (k', x) = p in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> Cons ((Pair (k', x)), (remove k l)))

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list
  | R_remove_3 of 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 'elt t
     * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rect k f f0 f1 f2 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 ->
      'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 f2 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l) -> f1 s k' x l __ __ __
  | R_remove_3 (s, k', x, l, _res, r0) ->
    f2 s k' x l __ __ __ _res r0 (coq_R_remove_rec k f f0 f1 f2 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f f0 f1 f2 s =
    let f3 = f s in
    let f4 = f0 s in
    let f5 = f1 s in
    let f6 = f2 s in
    (match s with
     | Nil -> f3 __
     | Cons (a, l) ->
       let Pair (a0, b) = a in
       let f7 = f6 a0 b l __ in
       let f8 = fun _ _ ->
         let hrec = remove_rect k f f0 f1 f2 l in f7 __ __ hrec
       in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match X.compare k a0 with
        | LT -> f10 __ __
        | EQ -> f9 __ __
        | GT -> f8 __ __))

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_2 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_3 (y, y0, y1, y2,
      (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | Nil -> acc
    | Cons (p, m') -> let Pair (k, e) = p in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t, 'elt) prod list * 'a
     * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0 (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> 'a3 -> 'a3) -> 'a1 t
      -> 'a2 -> 'a3 **)

  let rec fold_rect f f0 f1 m acc =
    let f2 = f0 m acc in
    let f3 = f1 m acc in
    (match m with
     | Nil -> f2 __
     | Cons (a, l) ->
       let Pair (a0, b) = a in
       let f4 = f3 a0 b l __ in
       let hrec = fold_rect f f0 f1 l (f a0 b acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
      'a2 -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> 'a3 -> 'a3) -> 'a1 t
      -> 'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
      coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2, y3,
      (fold f y3 (f y1 y2 y0)), (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res
      __

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | Nil -> (match m' with
              | Nil -> True
              | Cons (_, _) -> False)
    | Cons (p, l) ->
      let Pair (x, e) = p in
      (match m' with
       | Nil -> False
       | Cons (p0, l') ->
         let Pair (x', e') = p0 in
         (match X.compare x x' with
          | EQ -> (match cmp e e' with
                   | True -> equal cmp l l'
                   | False -> False)
          | _ -> False))

  type 'elt coq_R_equal =
  | R_equal_0 of 'elt t * 'elt t
  | R_equal_1 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * bool * 'elt coq_R_equal
  | R_equal_2 of 'elt t * 'elt t * X.t * 'elt * (X.t, 'elt) prod list * 
     X.t * 'elt * (X.t, 'elt) prod list * X.t compare0
  | R_equal_3 of 'elt t * 'elt t * 'elt t * 'elt t

  (** val coq_R_equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
      'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
      X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
      'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
      'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rect cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rect cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val coq_R_equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
      'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> bool -> 'a1 coq_R_equal -> 'a2 ->
      'a2) -> ('a1 t -> 'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ ->
      X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t compare0 -> __ -> __ ->
      'a2) -> ('a1 t -> 'a1 t -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) ->
      'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal -> 'a2 **)

  let rec coq_R_equal_rec cmp f f0 f1 f2 _ _ _ = function
  | R_equal_0 (m, m') -> f m m' __ __
  | R_equal_1 (m, m', x, e, l, x', e', l', _res, r0) ->
    f0 m m' x e l __ x' e' l' __ __ __ _res r0
      (coq_R_equal_rec cmp f f0 f1 f2 l l' _res r0)
  | R_equal_2 (m, m', x, e, l, x', e', l', _x) ->
    f1 m m' x e l __ x' e' l' __ _x __ __
  | R_equal_3 (m, m', _x, _x0) -> f2 m m' _x __ _x0 __ __

  (** val equal_rect :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
      'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
      -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let rec equal_rect cmp f f0 f1 f2 m m' =
    let f3 = f m m' in
    let f4 = f0 m m' in
    let f5 = f1 m m' in
    let f6 = f2 m m' in
    let f7 = f6 m __ in
    let f8 = f7 m' __ in
    (match m with
     | Nil ->
       let f9 = f3 __ in (match m' with
                          | Nil -> f9 __
                          | Cons (_, _) -> f8 __)
     | Cons (a, l) ->
       let Pair (a0, b) = a in
       let f9 = f5 a0 b l __ in
       let f10 = f4 a0 b l __ in
       (match m' with
        | Nil -> f8 __
        | Cons (a1, l0) ->
          let Pair (a2, b0) = a1 in
          let f11 = f9 a2 b0 l0 __ in
          let f12 = let _x = X.compare a0 a2 in f11 _x __ in
          let f13 = f10 a2 b0 l0 __ in
          let f14 = fun _ _ ->
            let hrec = equal_rect cmp f f0 f1 f2 l l0 in f13 __ __ hrec
          in
          (match X.compare a0 a2 with
           | EQ -> f14 __ __
           | _ -> f12 __)))

  (** val equal_rec :
      ('a1 -> 'a1 -> bool) -> ('a1 t -> 'a1 t -> __ -> __ -> 'a2) -> ('a1 t ->
      'a1 t -> X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t,
      'a1) prod list -> __ -> __ -> __ -> 'a2 -> 'a2) -> ('a1 t -> 'a1 t ->
      X.t -> 'a1 -> (X.t, 'a1) prod list -> __ -> X.t -> 'a1 -> (X.t, 'a1)
      prod list -> __ -> X.t compare0 -> __ -> __ -> 'a2) -> ('a1 t -> 'a1 t
      -> 'a1 t -> __ -> 'a1 t -> __ -> __ -> 'a2) -> 'a1 t -> 'a1 t -> 'a2 **)

  let equal_rec =
    equal_rect

  (** val coq_R_equal_correct :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool -> 'a1 coq_R_equal **)

  let coq_R_equal_correct cmp m m' _res =
    equal_rect cmp (fun y y0 _ _ _ _ -> R_equal_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ _ _ y11 _ _ -> R_equal_1 (y, y0, y1, y2,
      y3, y5, y6, y7, (equal cmp y3 y7), (y11 (equal cmp y3 y7) __)))
      (fun y y0 y1 y2 y3 _ y5 y6 y7 _ y9 _ _ _ _ -> R_equal_2 (y, y0, y1, y2,
      y3, y5, y6, y7, y9)) (fun y y0 y1 _ y3 _ _ _ _ -> R_equal_3 (y, y0, y1,
      y3)) m m' _res __

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | Nil -> Nil
  | Cons (p, m') -> let Pair (k, e) = p in Cons ((Pair (k, (f e))), (map f m'))

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | Nil -> Nil
  | Cons (p, m') ->
    let Pair (k, e) = p in Cons ((Pair (k, (f k e))), (mapi f m'))

  (** val option_cons :
      key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list **)

  let option_cons k o l =
    match o with
    | Some e -> Cons ((Pair (k, e)), l)
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | Nil -> Nil
  | Cons (p, l) ->
    let Pair (k, e) = p in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | Nil -> Nil
  | Cons (p, l') ->
    let Pair (k, e') = p in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | Nil -> map2_r f
  | Cons (p, l) ->
    let Pair (k, e) = p in
    let rec map2_aux m' = match m' with
    | Nil -> map2_l f m
    | Cons (p0, l') ->
      let Pair (k', e') = p0 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t **)

  let rec combine m = match m with
  | Nil -> map (fun e' -> Pair (None, (Some e')))
  | Cons (p, l) ->
    let Pair (k, e) = p in
    let rec combine_aux m' = match m' with
    | Nil -> map (fun e0 -> Pair ((Some e0), None)) m
    | Cons (p0, l') ->
      let Pair (k', e') = p0 in
      (match X.compare k k' with
       | LT -> Cons ((Pair (k, (Pair ((Some e), None)))), (combine l m'))
       | EQ -> Cons ((Pair (k, (Pair ((Some e), (Some e'))))), (combine l l'))
       | GT -> Cons ((Pair (k', (Pair (None, (Some e'))))), (combine_aux l')))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p -> f (fst p) (snd p)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key, 'a3)
      prod list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons m1 Nil

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (Pair (o, o'))
    | None -> (match o' with
               | Some _ -> Some (Pair (o, o'))
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> sumbool

  val ge_lt_dec : t -> t -> sumbool

  val eq_dec : t -> t -> sumbool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> sumbool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in (match b with
                          | True -> Left
                          | False -> Right)

  (** val ge_lt_dec : z -> z -> sumbool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in (match b with
                          | True -> Right
                          | False -> Left)

  (** val i2z : t -> z **)

  let i2z n =
    n
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rect f f0 t1) k y t2 (tree_rect f f0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec f f0 = function
  | Leaf -> f
  | Node (t1, k, y, t2, t3) ->
    f0 t1 (tree_rec f f0 t1) k y t2 (tree_rec f f0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> True
  | Node (_, _, _, _, _) -> False

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x = function
  | Leaf -> False
  | Node (l, y, _, r, _) ->
    (match X.compare x y with
     | LT -> mem x l
     | EQ -> True
     | GT -> mem x r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> find x l
     | EQ -> Some d
     | GT -> find x r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x e r =
    Node (l, x, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x d r =
    let hl = height l in
    let hr = height r in
    (match I.gt_le_dec hl (I.add hr I._2) with
     | Left ->
       (match l with
        | Leaf -> assert_false l x d r
        | Node (ll, lx, ld, lr, _) ->
          (match I.ge_lt_dec (height ll) (height lr) with
           | Left -> create ll lx ld (create lr x d r)
           | Right ->
             (match lr with
              | Leaf -> assert_false l x d r
              | Node (lrl, lrx, lrd, lrr, _) ->
                create (create ll lx ld lrl) lrx lrd (create lrr x d r))))
     | Right ->
       (match I.gt_le_dec hr (I.add hl I._2) with
        | Left ->
          (match r with
           | Leaf -> assert_false l x d r
           | Node (rl, rx, rd, rr, _) ->
             (match I.ge_lt_dec (height rr) (height rl) with
              | Left -> create (create l x d rl) rx rd rr
              | Right ->
                (match rl with
                 | Leaf -> assert_false l x d r
                 | Node (rll, rlx, rld, rlr, _) ->
                   create (create l x d rll) rlx rld (create rlr rx rd rr))))
        | Right -> create l x d r))

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x d = function
  | Leaf -> Node (Leaf, x, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x y with
     | LT -> bal (add x d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod **)

  let rec remove_min l x d r =
    match l with
    | Leaf -> Pair (r, (Pair (x, d)))
    | Node (ll, lx, ld, lr, _) ->
      let Pair (l', m) = remove_min ll lx ld lr in Pair ((bal l' x d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let Pair (s2', p) = remove_min l2 x2 d2 r2 in
         let Pair (x, d) = p in bal s1 x d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT -> bal (remove x l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x d ->
      let rec join_aux r = match r with
      | Leaf -> add x d l
      | Node (rl, rx, rd, rr, rh) ->
        (match I.gt_le_dec lh (I.add rh I._2) with
         | Left -> bal ll lx ld (join lr x d r)
         | Right ->
           (match I.gt_le_dec rh (I.add lh I._2) with
            | Left -> bal (join_aux rl) rx rd rr
            | Right -> create l x d r))
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let Pair (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x, d, r, _) ->
    elements_aux (Cons ((Pair (x, d)), (elements_aux acc r))) l

  (** val elements : 'a1 tree -> (key, 'a1) prod list **)

  let elements m =
    elements_aux Nil m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x, d, r, _) -> fold f r (f x d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rect f f0 e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec f f0 = function
  | End -> f
  | More (k, e0, t0, e1) -> f0 k e0 t0 e1 (enumeration_rec f f0 e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x, d, r, _) -> cons l (More (x, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> False
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> (match cmp d1 d2 with
              | True -> cont (cons r2 e3)
              | False -> False)
     | _ -> False)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> True
  | More (_, _, _, _) -> False

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((map f l), x, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, h) -> Node ((mapi f l), x, (f x d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x, d, r, _) ->
    (match f x d with
     | Some d' -> join (map_option f l) x d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt tree
    | R_mem_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem
    | R_mem_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_mem_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t * 
       bool * 'elt coq_R_mem

    (** val coq_R_mem_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rect x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_mem_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2
        -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t ->
        __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2)
        -> 'a1 tree -> bool -> 'a1 coq_R_mem -> 'a2 **)

    let rec coq_R_mem_rec x f f0 f1 f2 _ _ = function
    | R_mem_0 m -> f m __
    | R_mem_1 (m, l, y, _x, r0, _x0, _res, r1) ->
      f0 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 l _res r1)
    | R_mem_2 (m, l, y, _x, r0, _x0) -> f1 m l y _x r0 _x0 __ __ __
    | R_mem_3 (m, l, y, _x, r0, _x0, _res, r1) ->
      f2 m l y _x r0 _x0 __ __ __ _res r1
        (coq_R_mem_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_find =
    | R_find_0 of 'elt tree
    | R_find_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find
    | R_find_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_find_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt option * 'elt coq_R_find

    (** val coq_R_find_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rect x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_find_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 option -> 'a1 coq_R_find -> 'a2 **)

    let rec coq_R_find_rec x f f0 f1 f2 _ _ = function
    | R_find_0 m -> f m __
    | R_find_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1 (coq_R_find_rec x f f0 f1 f2 l _res r1)
    | R_find_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_find_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_find_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_bal =
    | R_bal_0 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_2 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_3 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_bal_4 of 'elt tree * key * 'elt * 'elt tree
    | R_bal_5 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_6 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t
    | R_bal_7 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * key * 
       'elt * 'elt tree * I.t * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_bal_8 of 'elt tree * key * 'elt * 'elt tree

    (** val coq_R_bal_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2)
        -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rect f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    (** val coq_R_bal_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> 'a2) -> ('a1
        tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key ->
        'a1 -> 'a1 tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> key -> 'a1 -> 'a1
        tree -> __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        __ -> __ -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> __ ->
        'a2) -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a2) ->
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> __ -> 'a2)
        -> ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree ->
        key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2) -> ('a1 tree -> key -> 'a1
        -> 'a1 tree -> __ -> __ -> __ -> __ -> 'a2) -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_bal -> 'a2 **)

    let coq_R_bal_rec f f0 f1 f2 f3 f4 f5 f6 f7 _ _ _ _ _ = function
    | R_bal_0 (l, x, d, r) -> f l x d r __ __ __
    | R_bal_1 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f0 l x d r __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_2 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f1 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_3 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f2 l x d r __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_4 (l, x, d, r) -> f3 l x d r __ __ __ __ __
    | R_bal_5 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f4 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __
    | R_bal_6 (l, x, d, r, x0, x1, x2, x3, x4) ->
      f5 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ __
    | R_bal_7 (l, x, d, r, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) ->
      f6 l x d r __ __ __ __ x0 x1 x2 x3 x4 __ __ __ x5 x6 x7 x8 x9 __
    | R_bal_8 (l, x, d, r) -> f7 l x d r __ __ __ __

    type 'elt coq_R_add =
    | R_add_0 of 'elt tree
    | R_add_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add
    | R_add_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_add_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_add

    (** val coq_R_add_rect :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rect x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rect x d f f0 f1 f2 r0 _res r1)

    (** val coq_R_add_rec :
        key -> 'a1 -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key
        -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1
        coq_R_add -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_add ->
        'a2 **)

    let rec coq_R_add_rec x d f f0 f1 f2 _ _ = function
    | R_add_0 m -> f m __
    | R_add_1 (m, l, y, d', r0, h, _res, r1) ->
      f0 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 l _res r1)
    | R_add_2 (m, l, y, d', r0, h) -> f1 m l y d' r0 h __ __ __
    | R_add_3 (m, l, y, d', r0, h, _res, r1) ->
      f2 m l y d' r0 h __ __ __ _res r1
        (coq_R_add_rec x d f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_remove_min =
    | R_remove_min_0 of 'elt tree * key * 'elt * 'elt tree
    | R_remove_min_1 of 'elt tree * key * 'elt * 'elt tree * 'elt tree * 
       key * 'elt * 'elt tree * I.t * ('elt tree, (key, 'elt) prod) prod
       * 'elt coq_R_remove_min * 'elt tree * (key, 'elt) prod

    (** val coq_R_remove_min_rect :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min
        -> 'a2 **)

    let rec coq_R_remove_min_rect f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rect f f0 ll lx ld lr _res r1) l' m __

    (** val coq_R_remove_min_rec :
        ('a1 tree -> key -> 'a1 -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> key
        -> 'a1 -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min -> 'a2 ->
        'a1 tree -> (key, 'a1) prod -> __ -> 'a2) -> 'a1 tree -> key -> 'a1 ->
        'a1 tree -> ('a1 tree, (key, 'a1) prod) prod -> 'a1 coq_R_remove_min
        -> 'a2 **)

    let rec coq_R_remove_min_rec f f0 _ _ _ _ _ = function
    | R_remove_min_0 (l, x, d, r) -> f l x d r __
    | R_remove_min_1 (l, x, d, r, ll, lx, ld, lr, _x, _res, r1, l', m) ->
      f0 l x d r ll lx ld lr _x __ _res r1
        (coq_R_remove_min_rec f f0 ll lx ld lr _res r1) l' m __

    type 'elt coq_R_merge =
    | R_merge_0 of 'elt tree * 'elt tree
    | R_merge_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_merge_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key, 'elt) prod * key * 'elt

    (** val coq_R_merge_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
        prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rect f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    (** val coq_R_merge_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
        prod -> __ -> key -> 'a1 -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1
        tree -> 'a1 coq_R_merge -> 'a2 **)

    let coq_R_merge_rec f f0 f1 _ _ _ = function
    | R_merge_0 (s1, s2) -> f s1 s2 __
    | R_merge_1 (s1, s2, _x, _x0, _x1, _x2, _x3) ->
      f0 s1 s2 _x _x0 _x1 _x2 _x3 __ __
    | R_merge_2 (s1, s2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, s2', p,
                 x, d) ->
      f1 s1 s2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ s2' p __ x d __

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt tree
    | R_remove_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_remove
    | R_remove_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_remove_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt tree * 'elt coq_R_remove

    (** val coq_R_remove_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rect x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rect x f f0 f1 f2 r0 _res r1)

    (** val coq_R_remove_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree ->
        I.t -> __ -> __ -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 tree -> 'a1 coq_R_remove
        -> 'a2 -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 coq_R_remove -> 'a2 **)

    let rec coq_R_remove_rec x f f0 f1 f2 _ _ = function
    | R_remove_0 m -> f m __
    | R_remove_1 (m, l, y, d, r0, _x, _res, r1) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 l _res r1)
    | R_remove_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_remove_3 (m, l, y, d, r0, _x, _res, r1) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_remove_rec x f f0 f1 f2 r0 _res r1)

    type 'elt coq_R_concat =
    | R_concat_0 of 'elt tree * 'elt tree
    | R_concat_1 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t
    | R_concat_2 of 'elt tree * 'elt tree * 'elt tree * key * 'elt * 'elt tree
       * I.t * 'elt tree * key * 'elt * 'elt tree * I.t * 'elt tree
       * (key, 'elt) prod

    (** val coq_R_concat_rect :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
        prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rect f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    (** val coq_R_concat_rec :
        ('a1 tree -> 'a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> 'a2) -> ('a1 tree
        -> 'a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a1 tree -> (key, 'a1)
        prod -> __ -> 'a2) -> 'a1 tree -> 'a1 tree -> 'a1 tree -> 'a1
        coq_R_concat -> 'a2 **)

    let coq_R_concat_rec f f0 f1 _ _ _ = function
    | R_concat_0 (m1, m2) -> f m1 m2 __
    | R_concat_1 (m1, m2, _x, _x0, _x1, _x2, _x3) ->
      f0 m1 m2 _x _x0 _x1 _x2 _x3 __ __
    | R_concat_2 (m1, m2, _x, _x0, _x1, _x2, _x3, l2, x2, d2, r2, _x4, m2', xd) ->
      f1 m1 m2 _x _x0 _x1 _x2 _x3 __ l2 x2 d2 r2 _x4 __ m2' xd __

    type 'elt coq_R_split =
    | R_split_0 of 'elt tree
    | R_split_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree
    | R_split_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
    | R_split_3 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * I.t
       * 'elt triple * 'elt coq_R_split * 'elt tree * 'elt option * 'elt tree

    (** val coq_R_split_rect :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
        option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rect x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rect x f f0 f1 f2 r0 _res r1) rl o rr __

    (** val coq_R_split_rec :
        X.t -> ('a1 tree -> __ -> 'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split
        -> 'a2 -> 'a1 tree -> 'a1 option -> 'a1 tree -> __ -> 'a2) -> ('a1
        tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> __ -> __ ->
        'a2) -> ('a1 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __
        -> __ -> __ -> 'a1 triple -> 'a1 coq_R_split -> 'a2 -> 'a1 tree -> 'a1
        option -> 'a1 tree -> __ -> 'a2) -> 'a1 tree -> 'a1 triple -> 'a1
        coq_R_split -> 'a2 **)

    let rec coq_R_split_rec x f f0 f1 f2 _ _ = function
    | R_split_0 m -> f m __
    | R_split_1 (m, l, y, d, r0, _x, _res, r1, ll, o, rl) ->
      f0 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 l _res r1) ll o rl __
    | R_split_2 (m, l, y, d, r0, _x) -> f1 m l y d r0 _x __ __ __
    | R_split_3 (m, l, y, d, r0, _x, _res, r1, rl, o, rr) ->
      f2 m l y d r0 _x __ __ __ _res r1
        (coq_R_split_rec x f f0 f1 f2 r0 _res r1) rl o rr __

    type ('elt, 'x) coq_R_map_option =
    | R_map_option_0 of 'elt tree
    | R_map_option_1 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option
    | R_map_option_2 of 'elt tree * 'elt tree * key * 'elt * 'elt tree * 
       I.t * 'x tree * ('elt, 'x) coq_R_map_option * 'x tree
       * ('elt, 'x) coq_R_map_option

    (** val coq_R_map_option_rect :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rect f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rect f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rect f f0 f1 f2 r0 _res r2)

    (** val coq_R_map_option_rec :
        (key -> 'a1 -> 'a2 option) -> ('a1 tree -> __ -> 'a3) -> ('a1 tree ->
        'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 -> __ -> 'a2
        tree -> ('a1, 'a2) coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a3) -> ('a1 tree -> 'a1 tree -> key -> 'a1
        -> 'a1 tree -> I.t -> __ -> __ -> 'a2 tree -> ('a1, 'a2)
        coq_R_map_option -> 'a3 -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 -> 'a3) -> 'a1 tree -> 'a2 tree -> ('a1, 'a2) coq_R_map_option ->
        'a3 **)

    let rec coq_R_map_option_rec f f0 f1 f2 _ _ = function
    | R_map_option_0 m -> f0 m __
    | R_map_option_1 (m, l, x, d, r0, _x, d', _res0, r1, _res, r2) ->
      f1 m l x d r0 _x __ d' __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)
    | R_map_option_2 (m, l, x, d, r0, _x, _res0, r1, _res, r2) ->
      f2 m l x d r0 _x __ __ _res0 r1
        (coq_R_map_option_rec f f0 f1 f2 l _res0 r1) _res r2
        (coq_R_map_option_rec f f0 f1 f2 r0 _res r2)

    type ('elt, 'x0, 'x) coq_R_map2_opt =
    | R_map2_opt_0 of 'elt tree * 'x0 tree
    | R_map2_opt_1 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t
    | R_map2_opt_2 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
    | R_map2_opt_3 of 'elt tree * 'x0 tree * 'elt tree * key * 'elt
       * 'elt tree * I.t * 'x0 tree * key * 'x0 * 'x0 tree * I.t * 'x0 tree
       * 'x0 option * 'x0 tree * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt
       * 'x tree * ('elt, 'x0, 'x) coq_R_map2_opt

    (** val coq_R_map2_opt_rect :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __
        -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
        'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2
        -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2
        tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
        r0 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res
        r2 (coq_R_map2_opt_rect f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val coq_R_map2_opt_rec :
        (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
        ('a2 tree -> 'a3 tree) -> ('a1 tree -> 'a2 tree -> __ -> 'a4) -> ('a1
        tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ ->
        __ -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1 tree -> key -> 'a1 -> 'a1
        tree -> I.t -> __ -> 'a2 tree -> key -> 'a2 -> 'a2 tree -> I.t -> __
        -> 'a2 tree -> 'a2 option -> 'a2 tree -> __ -> 'a3 -> __ -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree -> ('a1, 'a2,
        'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> ('a1 tree -> 'a2 tree -> 'a1
        tree -> key -> 'a1 -> 'a1 tree -> I.t -> __ -> 'a2 tree -> key -> 'a2
        -> 'a2 tree -> I.t -> __ -> 'a2 tree -> 'a2 option -> 'a2 tree -> __
        -> __ -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a3 tree
        -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 -> 'a4) -> 'a1 tree -> 'a2
        tree -> 'a3 tree -> ('a1, 'a2, 'a3) coq_R_map2_opt -> 'a4 **)

    let rec coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 _ _ _ = function
    | R_map2_opt_0 (m1, m2) -> f0 m1 m2 __
    | R_map2_opt_1 (m1, m2, l1, x1, d1, r1, _x) ->
      f1 m1 m2 l1 x1 d1 r1 _x __ __
    | R_map2_opt_2 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', e, _res0, r0, _res, r2) ->
      f2 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ e __
        _res0 r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0)
        _res r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)
    | R_map2_opt_3 (m1, m2, l1, x1, d1, r1, _x, _x0, _x1, _x2, _x3, _x4, l2',
                    o2, r2', _res0, r0, _res, r2) ->
      f3 m1 m2 l1 x1 d1 r1 _x __ _x0 _x1 _x2 _x3 _x4 __ l2' o2 r2' __ __ _res0
        r0 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 l1 l2' _res0 r0) _res
        r2 (coq_R_map2_opt_rec f mapl mapr f0 f1 f2 f3 r1 r2' _res r2)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key, 'a1) prod list **)

    let rec flatten_e = function
    | End -> Nil
    | More (x, e0, t0, r) ->
      Cons ((Pair (x, e0)), (app (elements t0) (flatten_e r)))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key, 'a1) prod list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    Raw.cardinal (this m)

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

type pt = { p_x : q; p_y : q }

type edge = { left_pt : pt; right_pt : pt }

type event = { point : pt; outgoing : edge list }

type cell = { left_pts : pt list; right_pts : pt list; low : edge; high : edge }

(** val dummy_pt : pt **)

let dummy_pt =
  { p_x = { qnum = Z0; qden = XH }; p_y = { qnum = (Zpos (XI (XO XH))); qden =
    XH } }

(** val dummy_edge : edge **)

let dummy_edge =
  { left_pt = dummy_pt; right_pt = dummy_pt }

(** val dummy_cell : cell **)

let dummy_cell =
  { left_pts = Nil; right_pts = Nil; low = dummy_edge; high = dummy_edge }

(** val pt_eqb : pt -> pt -> bool **)

let pt_eqb a b =
  let { p_x = a_x; p_y = a_y } = a in
  let { p_x = b_x; p_y = b_y } = b in
  (match qeq_bool a_x b_x with
   | True -> qeq_bool a_y b_y
   | False -> False)

(** val qlt_bool : q -> q -> bool **)

let qlt_bool q1 q2 =
  negb (qle_bool q2 q1)

(** val add_event : pt -> edge -> bool -> event list -> event list **)

let rec add_event p e inc evs = match evs with
| Nil ->
  (match inc with
   | True -> Cons ({ point = p; outgoing = Nil }, Nil)
   | False -> Cons ({ point = p; outgoing = (Cons (e, Nil)) }, Nil))
| Cons (ev1, evs') ->
  let p1 = ev1.point in
  (match pt_eqb p p1 with
   | True ->
     (match inc with
      | True -> Cons ({ point = p1; outgoing = ev1.outgoing }, evs')
      | False ->
        Cons ({ point = p1; outgoing = (Cons (e, ev1.outgoing)) }, evs'))
   | False ->
     (match qlt_bool p.p_x p1.p_x with
      | True ->
        (match inc with
         | True -> Cons ({ point = p; outgoing = Nil }, evs)
         | False -> Cons ({ point = p; outgoing = (Cons (e, Nil)) }, evs))
      | False ->
        (match match qeq_bool p.p_x p1.p_x with
               | True -> qlt_bool p.p_y p1.p_y
               | False -> False with
         | True ->
           (match inc with
            | True -> Cons ({ point = p; outgoing = Nil }, evs)
            | False -> Cons ({ point = p; outgoing = (Cons (e, Nil)) }, evs))
         | False -> Cons (ev1, (add_event p e inc evs')))))

(** val edges_to_events : edge list -> event list **)

let rec edges_to_events = function
| Nil -> Nil
| Cons (e, s') ->
  add_event e.left_pt e False
    (add_event e.right_pt e True (edges_to_events s'))

(** val no_dup_seq : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec no_dup_seq eqb0 s = match s with
| Nil -> Nil
| Cons (a, q0) ->
  (match q0 with
   | Nil -> s
   | Cons (b, _) ->
     (match eqb0 a b with
      | True -> no_dup_seq eqb0 q0
      | False -> Cons (a, (no_dup_seq eqb0 q0))))

(** val valid_edge : edge -> pt -> bool **)

let valid_edge e p =
  match qle_bool e.left_pt.p_x p.p_x with
  | True -> qle_bool p.p_x e.right_pt.p_x
  | False -> False

(** val vertical_intersection_point : pt -> edge -> pt option **)

let vertical_intersection_point p e =
  match valid_edge e p with
  | True ->
    Some { p_x = p.p_x; p_y =
      (qplus
        (qmult (qminus p.p_x e.left_pt.p_x)
          (qdiv (qminus e.right_pt.p_y e.left_pt.p_y)
            (qminus e.right_pt.p_x e.left_pt.p_x))) e.left_pt.p_y) }
  | False -> None

(** val close_cell : pt -> cell -> cell **)

let close_cell p c =
  match vertical_intersection_point p c.low with
  | Some p1 ->
    (match vertical_intersection_point p c.high with
     | Some p2 ->
       { left_pts = c.left_pts; right_pts =
         (no_dup_seq pt_eqb (Cons (p1, (Cons (p, (Cons (p2, Nil))))))); low =
         c.low; high = c.high }
     | None -> c)
  | None -> c

(** val closing_cells : pt -> cell list -> cell list **)

let closing_cells p contact_cells =
  map (fun c -> close_cell p c) contact_cells

(** val opening_cells_aux :
    pt -> edge list -> edge -> edge -> pt list option -> (cell list, cell) prod **)

let rec opening_cells_aux p out low_e high_e leftpts =
  match out with
  | Nil ->
    (match leftpts with
     | Some lpts ->
       let op1 = vertical_intersection_point p high_e in
       (match op1 with
        | Some p1 ->
          Pair (Nil, { left_pts =
            (no_dup_seq pt_eqb (Cons (p1, (behead lpts)))); right_pts = Nil;
            low = low_e; high = high_e })
        | None -> Pair (Nil, dummy_cell))
     | None ->
       let op0 = vertical_intersection_point p low_e in
       let op1 = vertical_intersection_point p high_e in
       (match op0 with
        | Some p0 ->
          (match op1 with
           | Some p1 ->
             Pair (Nil, { left_pts =
               (no_dup_seq pt_eqb (Cons (p1, (Cons (p, (Cons (p0, Nil)))))));
               right_pts = Nil; low = low_e; high = high_e })
           | None -> Pair (Nil, dummy_cell))
        | None -> Pair (Nil, dummy_cell)))
  | Cons (c, q0) ->
    (match leftpts with
     | Some lpts ->
       let Pair (s, nc) = opening_cells_aux p q0 c high_e None in
       Pair ((Cons ({ left_pts =
       (no_dup_seq pt_eqb (Cons (p, (behead lpts)))); right_pts = Nil; low =
       low_e; high = c }, s)), nc)
     | None ->
       let op0 = vertical_intersection_point p low_e in
       let Pair (s, nc) = opening_cells_aux p q0 c high_e None in
       (match op0 with
        | Some p0 ->
          Pair ((Cons ({ left_pts =
            (no_dup_seq pt_eqb (Cons (p, (Cons (p0, Nil))))); right_pts = Nil;
            low = low_e; high = c }, s)), nc)
        | None -> Pair (Nil, dummy_cell)))

(** val pue_formula : pt -> pt -> pt -> q **)

let pue_formula p a b =
  let { p_x = p_x0; p_y = p_y0 } = p in
  let { p_x = a_x; p_y = a_y } = a in
  let { p_x = b_x; p_y = b_y } = b in
  qminus
    (qplus
      (qminus (qminus (qmult b_x p_y0) (qmult p_x0 b_y))
        (qminus (qmult a_x p_y0) (qmult p_x0 a_y))) (qmult a_x b_y))
    (qmult b_x a_y)

(** val point_under_edge : pt -> edge -> bool **)

let point_under_edge p e =
  qle_bool (pue_formula p e.left_pt e.right_pt) { qnum = Z0; qden = XH }

(** val point_strictly_under_edge : pt -> edge -> bool **)

let point_strictly_under_edge p e =
  qlt_bool (pue_formula p e.left_pt e.right_pt) { qnum = Z0; qden = XH }

(** val edge_below : edge -> edge -> bool **)

let edge_below e1 e2 =
  match match point_under_edge e1.left_pt e2 with
        | True -> point_under_edge e1.right_pt e2
        | False -> False with
  | True -> True
  | False ->
    (match negb (point_strictly_under_edge e2.left_pt e1) with
     | True -> negb (point_strictly_under_edge e2.right_pt e1)
     | False -> False)

(** val contains_point : pt -> cell -> bool **)

let contains_point p c =
  match negb (point_strictly_under_edge p c.low) with
  | True -> point_under_edge p c.high
  | False -> False

(** val open_cells_decomposition_contact :
    cell list -> pt -> ((cell list, cell list) prod, cell) prod option **)

let rec open_cells_decomposition_contact open_cells pt0 =
  match open_cells with
  | Nil -> None
  | Cons (c, q0) ->
    (match contains_point pt0 c with
     | True ->
       (match open_cells_decomposition_contact q0 pt0 with
        | Some p ->
          let Pair (p0, c') = p in
          let Pair (cc, lc) = p0 in
          Some (Pair ((Pair ((Cons (c, cc)), lc)), c'))
        | None -> Some (Pair ((Pair (Nil, q0)), c)))
     | False -> None)

(** val open_cells_decomposition_rec :
    cell list -> pt -> (((cell list, cell list) prod, cell) prod, cell list)
    prod **)

let rec open_cells_decomposition_rec open_cells pt0 =
  match open_cells with
  | Nil -> Pair ((Pair ((Pair (Nil, Nil)), dummy_cell)), Nil)
  | Cons (c, q0) ->
    (match contains_point pt0 c with
     | True ->
       (match open_cells_decomposition_contact q0 pt0 with
        | Some p ->
          let Pair (p0, c') = p in
          let Pair (cc, lc) = p0 in
          Pair ((Pair ((Pair (Nil, (Cons (c, cc)))), c')), lc)
        | None -> Pair ((Pair ((Pair (Nil, Nil)), c)), q0))
     | False ->
       let Pair (p, lc) = open_cells_decomposition_rec q0 pt0 in
       let Pair (p0, c') = p in
       let Pair (fc, cc) = p0 in
       Pair ((Pair ((Pair ((Cons (c, fc)), cc)), c')), lc))

(** val open_cells_decomposition :
    cell list -> pt -> (((((cell list, cell list) prod, cell) prod, cell list)
    prod, edge) prod, edge) prod **)

let open_cells_decomposition open_cells p =
  let Pair (p0, lc) = open_cells_decomposition_rec open_cells p in
  let Pair (p1, c') = p0 in
  let Pair (fc, cc) = p1 in
  Pair ((Pair ((Pair ((Pair ((Pair (fc, cc)), c')), lc)), (head c' cc).low)),
  c'.high)

type scan_state = { sc_open1 : cell list; lst_open : cell;
                    sc_open2 : cell list; sc_closed : cell list;
                    lst_closed : cell; lst_high : edge; lst_x : q }

(** val update_closed_cell : cell -> pt -> cell **)

let update_closed_cell c p =
  let ptseq = c.right_pts in
  let newptseq =
    app (belast (head dummy_pt ptseq) (behead ptseq)) (Cons (p, (Cons
      ((last dummy_pt ptseq), Nil))))
  in
  { left_pts = c.left_pts; right_pts = newptseq; low = c.low; high = c.high }

(** val update_open_cell : cell -> event -> (cell list, cell) prod **)

let update_open_cell c e =
  match e.outgoing with
  | Nil ->
    let ptseq = c.left_pts in
    let newptseq = Cons ((head dummy_pt ptseq), (Cons (e.point,
      (behead ptseq))))
    in
    Pair (Nil, { left_pts = newptseq; right_pts = c.right_pts; low = c.low;
    high = c.high })
  | Cons (_, _) ->
    opening_cells_aux e.point (sort edge_below e.outgoing) c.low c.high (Some
      c.left_pts)

(** val pvert_y : pt -> edge -> q **)

let pvert_y p e =
  match vertical_intersection_point p e with
  | Some p' -> p'.p_y
  | None -> { qnum = Z0; qden = XH }

(** val update_open_cell_top :
    cell -> edge -> event -> (cell list, cell) prod **)

let update_open_cell_top c new_high e =
  match e.outgoing with
  | Nil ->
    let newptseq = Cons ({ p_x = e.point.p_x; p_y =
      (pvert_y e.point new_high) }, c.left_pts)
    in
    Pair (Nil, { left_pts = newptseq; right_pts = c.right_pts; low = c.low;
    high = new_high })
  | Cons (_, _) ->
    opening_cells_aux e.point (sort edge_below e.outgoing) c.low new_high
      (Some c.left_pts)

(** val step : event -> scan_state -> scan_state **)

let step e st =
  let p = e.point in
  let { sc_open1 = op1; lst_open = lsto; sc_open2 = op2; sc_closed = cls;
    lst_closed = cl; lst_high = lhigh; lst_x = lx } = st
  in
  (match negb (qeq_bool p.p_x lx) with
   | True ->
     let Pair (p0, higher_edge) =
       open_cells_decomposition (app op1 (Cons (lsto, op2))) p
     in
     let Pair (p1, lower_edge) = p0 in
     let Pair (p2, last_cells) = p1 in
     let Pair (p3, last_contact) = p2 in
     let Pair (first_cells, contact_cells) = p3 in
     let closed = closing_cells p contact_cells in
     let last_closed = close_cell p last_contact in
     let closed_cells = app closed (Cons (cl, cls)) in
     let Pair (new_open_cells, newlastopen) =
       opening_cells_aux p (sort edge_below e.outgoing) lower_edge higher_edge
         None
     in
     { sc_open1 = (app first_cells new_open_cells); lst_open = newlastopen;
     sc_open2 = last_cells; sc_closed = closed_cells; lst_closed =
     last_closed; lst_high = higher_edge; lst_x = e.point.p_x }
   | False ->
     (match negb (point_under_edge p lhigh) with
      | True ->
        let Pair (p0, higher_edge) = open_cells_decomposition op2 p in
        let Pair (p1, low_edge) = p0 in
        let Pair (p2, last_cells) = p1 in
        let Pair (p3, last_contact) = p2 in
        let Pair (fc', contact_cells) = p3 in
        let first_cells = app op1 (Cons (lsto, fc')) in
        let closed = closing_cells p contact_cells in
        let last_closed = close_cell p last_contact in
        let closed_cells = app closed cls in
        let Pair (new_open_cells, newlastopen) =
          opening_cells_aux p (sort edge_below e.outgoing) low_edge
            higher_edge None
        in
        { sc_open1 = (app first_cells new_open_cells); lst_open = newlastopen;
        sc_open2 = last_cells; sc_closed = closed_cells; lst_closed =
        last_closed; lst_high = higher_edge; lst_x = e.point.p_x }
      | False ->
        (match point_strictly_under_edge p lhigh with
         | True ->
           let new_closed = update_closed_cell cl e.point in
           let Pair (new_opens, new_lopen) = update_open_cell lsto e in
           { sc_open1 = (app op1 new_opens); lst_open = new_lopen; sc_open2 =
           op2; sc_closed = cls; lst_closed = new_closed; lst_high = lhigh;
           lst_x = lx }
         | False ->
           let Pair (p0, higher_edge) =
             open_cells_decomposition (Cons (lsto, op2)) p
           in
           let Pair (p1, _) = p0 in
           let Pair (p2, last_cells) = p1 in
           let Pair (p3, last_contact) = p2 in
           let Pair (fc', contact_cells) = p3 in
           let closed = closing_cells p (behead contact_cells) in
           let last_closed = close_cell p last_contact in
           let Pair (new_opens, new_lopen) =
             update_open_cell_top lsto higher_edge e
           in
           { sc_open1 = (app op1 (app fc' new_opens)); lst_open = new_lopen;
           sc_open2 = last_cells; sc_closed = (app closed (Cons (cl, cls)));
           lst_closed = last_closed; lst_high = higher_edge; lst_x = lx })))

(** val leftmost_points : edge -> edge -> pt list **)

let leftmost_points bottom top =
  match qlt_bool bottom.left_pt.p_x top.left_pt.p_x with
  | True ->
    (match vertical_intersection_point top.left_pt bottom with
     | Some pt0 -> Cons (top.left_pt, (Cons (pt0, Nil)))
     | None -> Nil)
  | False ->
    (match vertical_intersection_point bottom.left_pt top with
     | Some pt0 -> Cons (pt0, (Cons (bottom.left_pt, Nil)))
     | None -> Nil)

(** val rightmost_points : edge -> edge -> pt list **)

let rightmost_points bottom top =
  match qlt_bool bottom.right_pt.p_x top.right_pt.p_x with
  | True ->
    (match vertical_intersection_point bottom.right_pt top with
     | Some pt0 -> Cons (bottom.right_pt, (Cons (pt0, Nil)))
     | None -> Nil)
  | False ->
    (match vertical_intersection_point top.right_pt bottom with
     | Some pt0 -> Cons (pt0, (Cons (top.right_pt, Nil)))
     | None -> Nil)

(** val complete_last_open : edge -> edge -> cell -> cell **)

let complete_last_open bottom top c =
  let { left_pts = lpts; right_pts = _; low = le; high = he } = c in
  { left_pts = lpts; right_pts = (rightmost_points bottom top); low = le;
  high = he }

(** val start_open_cell : edge -> edge -> cell **)

let start_open_cell bottom top =
  { left_pts = (leftmost_points bottom top); right_pts = Nil; low = bottom;
    high = top }

(** val start : event -> edge -> edge -> scan_state **)

let start first_event bottom top =
  let Pair (newcells, lastopen) =
    opening_cells_aux first_event.point (sort edge_below first_event.outgoing)
      bottom top None
  in
  { sc_open1 = newcells; lst_open = lastopen; sc_open2 = Nil; sc_closed = Nil;
  lst_closed = (close_cell first_event.point (start_open_cell bottom top));
  lst_high = top; lst_x = first_event.point.p_x }

(** val iter_list : ('a1 -> 'a2 -> 'a2) -> 'a1 list -> 'a2 -> 'a2 **)

let rec iter_list f s init =
  match s with
  | Nil -> init
  | Cons (a, tl) -> iter_list f tl (f a init)

(** val scan : event list -> edge -> edge -> cell list **)

let scan events bottom top =
  match events with
  | Nil ->
    Cons ((complete_last_open bottom top (start_open_cell bottom top)), Nil)
  | Cons (ev0, events0) ->
    let start_scan = start ev0 bottom top in
    let final_scan = iter_list step events0 start_scan in
    app
      (map (complete_last_open bottom top) (Cons (final_scan.lst_open,
        (app final_scan.sc_open1 final_scan.sc_open2)))) (Cons
      (final_scan.lst_closed, final_scan.sc_closed))

(** val edges_to_cells : edge -> edge -> edge list -> cell list **)

let edges_to_cells bottom top edges =
  scan (edges_to_events edges) bottom top

(** val bfs_aux :
    ('a3 -> 'a1 -> 'a2 option) -> ('a3 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> ('a1,
    'a2) prod list) -> ('a1 -> 'a1 -> sumbool) -> ('a1, 'a2) prod list ->
    ('a1, 'a2) prod list -> 'a1 -> 'a3 -> (('a1, 'a2) prod list, 'a3) prod **)

let rec bfs_aux find0 add0 step0 state_eq_dec w w2 sufficient settled =
  match w with
  | Nil -> Pair (w2, settled)
  | Cons (p, w') ->
    let Pair (s, m) = p in
    (match find0 settled s with
     | Some _ -> bfs_aux find0 add0 step0 state_eq_dec w' w2 sufficient settled
     | None ->
       (match state_eq_dec s sufficient with
        | Left -> Pair (Nil, (add0 settled s m))
        | Right ->
          bfs_aux find0 add0 step0 state_eq_dec w' (app (step0 s) w2)
            sufficient (add0 settled s m)))

(** val bfs :
    ('a3 -> 'a1 -> 'a2 option) -> ('a3 -> 'a1 -> 'a2 -> 'a3) -> ('a1 -> ('a1,
    'a2) prod list) -> ('a1 -> 'a1 -> sumbool) -> nat -> ('a1, 'a2) prod list
    -> 'a3 -> 'a1 -> nat -> (('a3, nat) prod, (('a1, 'a2) prod list, 'a3)
    prod) sum **)

let rec bfs find0 add0 step0 state_eq_dec fuel w settled sufficient round =
  match fuel with
  | O -> Inr (Pair (w, settled))
  | S p ->
    let Pair (w0, s) =
      bfs_aux find0 add0 step0 state_eq_dec w Nil sufficient settled
    in
    (match w0 with
     | Nil -> Inl (Pair (s, round))
     | Cons (_, _) ->
       bfs find0 add0 step0 state_eq_dec p w0 s sufficient (add round (S O)))

(** val make_path :
    ('a3 -> 'a1 -> 'a2 option) -> 'a3 -> ('a1 -> bool) -> ('a1 -> 'a2 -> 'a1
    option) -> 'a1 -> nat -> 'a2 list option **)

let rec make_path find0 db targetb play x = function
| O -> None
| S p ->
  (match targetb x with
   | True -> Some Nil
   | False ->
     (match find0 db x with
      | Some m ->
        (match play x m with
         | Some y ->
           (match make_path find0 db targetb play y p with
            | Some l -> Some (Cons (m, l))
            | None -> None)
         | None -> None)
      | None -> None))

type vert_edge = { ve_x : q; ve_top : q; ve_bot : q }

(** val vert_edge_eqb : vert_edge -> vert_edge -> bool **)

let vert_edge_eqb v1 v2 =
  let { ve_x = v1x; ve_top = v1t; ve_bot = v1b } = v1 in
  let { ve_x = v2x; ve_top = v2t; ve_bot = v2b } = v2 in
  (match match qeq_bool v1x v2x with
         | True -> qeq_bool v1t v2t
         | False -> False with
   | True -> qeq_bool v1b v2b
   | False -> False)

(** val seq_to_intervals_aux : 'a1 -> 'a1 list -> ('a1, 'a1) prod list **)

let rec seq_to_intervals_aux a = function
| Nil -> Nil
| Cons (b, tl) -> Cons ((Pair (a, b)), (seq_to_intervals_aux b tl))

(** val seq_to_intervals : 'a1 list -> ('a1, 'a1) prod list **)

let seq_to_intervals = function
| Nil -> Nil
| Cons (a, tl) -> seq_to_intervals_aux a tl

(** val cell_safe_exits_left : cell -> vert_edge list **)

let cell_safe_exits_left c =
  let lx = (head dummy_pt c.left_pts).p_x in
  map (fun p -> { ve_x = lx; ve_top = (fst p).p_y; ve_bot = (snd p).p_y })
    (seq_to_intervals c.left_pts)

(** val cell_safe_exits_right : cell -> vert_edge list **)

let cell_safe_exits_right c =
  let lx = (head dummy_pt c.right_pts).p_x in
  map (fun p -> { ve_x = lx; ve_top = (fst p).p_y; ve_bot = (snd p).p_y })
    (seq_to_intervals (rev c.right_pts))

(** val all_doors : cell list -> (vert_edge, nat) prod list **)

let all_doors cells =
  concat
    (map (fun i ->
      map (fun v -> Pair (v, i))
        (cell_safe_exits_right (nth i cells dummy_cell)))
      (iota O (length cells)))

(** val door_right_cell : cell list -> vert_edge -> nat option **)

let door_right_cell cells v =
  find (fun i ->
    existsb (fun v' -> vert_edge_eqb v v')
      (cell_safe_exits_left (nth i cells dummy_cell))) (iota O (length cells))

(** val vert_edge_midpoint : vert_edge -> pt **)

let vert_edge_midpoint ve =
  { p_x = ve.ve_x; p_y =
    (qdiv (qplus ve.ve_top ve.ve_bot) { qnum = (Zpos (XO XH)); qden = XH }) }

(** val lr_connected : cell -> cell -> bool **)

let lr_connected c1 c2 =
  existsb (fun v ->
    existsb (fun v' -> vert_edge_eqb v v') (cell_safe_exits_left c2))
    (cell_safe_exits_right c1)

(** val bi_connected : cell -> cell -> bool **)

let bi_connected c1 c2 =
  match lr_connected c1 c2 with
  | True -> True
  | False -> lr_connected c2 c1

(** val dummy_vert_edge : vert_edge **)

let dummy_vert_edge =
  { ve_x = { qnum = Z0; qden = XH }; ve_top = { qnum = Z0; qden = XH };
    ve_bot = { qnum = Z0; qden = XH } }

module Coq_natmap = Make(Nat_as_OT)

(** val bfs_find : nat Coq_natmap.t -> nat -> nat option **)

let bfs_find m k =
  Coq_natmap.find k m

(** val bfs_add : nat Coq_natmap.t -> nat -> nat -> nat Coq_natmap.t **)

let bfs_add m k v =
  Coq_natmap.add k v m

(** val reverse_step : cell list -> nat -> (nat, nat) prod list **)

let reverse_step cells cell_i =
  map (fun i -> Pair (i, cell_i))
    (filter (fun c_i ->
      bi_connected (nth c_i cells dummy_cell) (nth cell_i cells dummy_cell))
      (iota O (length cells)))

(** val cell_connection_table :
    cell list -> nat -> nat -> ((nat Coq_natmap.t, nat) prod, ((nat, nat) prod
    list, nat Coq_natmap.t) prod) sum **)

let cell_connection_table cells source_i target_i =
  bfs bfs_find bfs_add (reverse_step cells) Nat.eq_dec (length cells) (Cons
    ((Pair (target_i, target_i)), Nil)) Coq_natmap.empty source_i O

(** val cell_path : cell list -> nat -> nat -> nat list option **)

let cell_path cells source_i target_i =
  match cell_connection_table cells source_i target_i with
  | Inl p ->
    let Pair (table, _) = p in
    make_path bfs_find table (fun c_i -> Nat.eqb c_i target_i) (fun _ n2 ->
      Some n2) source_i (length cells)
  | Inr _ -> None

(** val left_limit : cell -> q **)

let left_limit c =
  (last dummy_pt c.left_pts).p_x

(** val right_limit : cell -> q **)

let right_limit c =
  (last dummy_pt c.right_pts).p_x

(** val common_vert_edge : cell -> cell -> vert_edge option **)

let common_vert_edge c1 c2 =
  match qeq_bool (right_limit c1) (left_limit c2) with
  | True ->
    find (fun v ->
      existsb (fun v' -> vert_edge_eqb v v') (cell_safe_exits_left c2))
      (cell_safe_exits_right c1)
  | False ->
    find (fun v ->
      existsb (fun v' -> vert_edge_eqb v v') (cell_safe_exits_left c1))
      (cell_safe_exits_right c2)

(** val midpoint : pt -> pt -> pt **)

let midpoint p1 p2 =
  { p_x = (qdiv (qplus p1.p_x p2.p_x) { qnum = (Zpos (XO XH)); qden = XH });
    p_y = (qdiv (qplus p1.p_y p2.p_y) { qnum = (Zpos (XO XH)); qden = XH }) }

(** val cell_center : cell -> pt **)

let cell_center c =
  midpoint (midpoint (last dummy_pt c.left_pts) (head dummy_pt c.right_pts))
    (midpoint (head dummy_pt c.left_pts) (last dummy_pt c.right_pts))

type annotated_point = { apt_val : pt; cell_indices : nat list }

(** val on_vert_edge : pt -> vert_edge -> bool **)

let on_vert_edge p v =
  match match qeq_bool p.p_x v.ve_x with
        | True -> qlt_bool v.ve_bot p.p_y
        | False -> False with
  | True -> qlt_bool p.p_y v.ve_top
  | False -> False

(** val point_to_door :
    cell list -> annotated_point -> nat -> nat -> (annotated_point,
    annotated_point) prod list **)

let point_to_door cells p c1i c2i =
  let c1 = nth c1i cells dummy_cell in
  let c2 = nth c2i cells dummy_cell in
  (match common_vert_edge c1 c2 with
   | Some v ->
     (match match qeq_bool p.apt_val.p_x v.ve_x with
            | True -> negb (on_vert_edge p.apt_val v)
            | False -> False with
      | True ->
        Cons ((Pair (p, { apt_val = (cell_center c1); cell_indices = (Cons
          (c1i, Nil)) })), (Cons ((Pair ({ apt_val = (cell_center c1);
          cell_indices = (Cons (c1i, Nil)) }, { apt_val =
          (vert_edge_midpoint v); cell_indices = (Cons (c1i, (Cons (c2i,
          Nil)))) })), Nil)))
      | False ->
        Cons ((Pair (p, { apt_val = (vert_edge_midpoint v); cell_indices =
          (Cons (c1i, (Cons (c2i, Nil)))) })), Nil))
   | None -> Nil)

(** val path_reverse :
    (annotated_point, annotated_point) prod list -> (annotated_point,
    annotated_point) prod list **)

let path_reverse s =
  map (fun p -> Pair ((snd p), (fst p))) (rev_append s Nil)

(** val to_next_door :
    pt option -> pt option -> cell list -> nat -> nat -> nat ->
    (annotated_point, annotated_point) prod list **)

let to_next_door op1 op2 cells c1i c2i c3i =
  let c2 = nth c2i cells dummy_cell in
  let p1 =
    match op1 with
    | Some p1 -> p1
    | None ->
      (match common_vert_edge (nth c1i cells dummy_cell) c2 with
       | Some v -> vert_edge_midpoint v
       | None -> dummy_pt)
  in
  let p2 =
    match op2 with
    | Some p2 -> p2
    | None ->
      (match common_vert_edge c2 (nth c3i cells dummy_cell) with
       | Some v -> vert_edge_midpoint v
       | None -> dummy_pt)
  in
  (match qeq_bool p1.p_x p2.p_x with
   | True ->
     let intermediate_point = { apt_val = (cell_center c2); cell_indices =
       (Cons (c2i, Nil)) }
     in
     Cons ((Pair ({ apt_val = p1; cell_indices = (Cons (c1i, (Cons (c2i,
     Nil)))) }, intermediate_point)), (Cons ((Pair (intermediate_point,
     { apt_val = p2; cell_indices = (Cons (c2i, (Cons (c3i, Nil)))) })), Nil)))
   | False ->
     Cons ((Pair ({ apt_val = p1; cell_indices = (Cons (c1i, (Cons (c2i,
       Nil)))) }, { apt_val = p2; cell_indices = (Cons (c2i, (Cons (c3i,
       Nil)))) })), Nil))

(** val door_to_door :
    cell list -> nat -> nat -> pt option -> pt option -> nat list ->
    (annotated_point, annotated_point) prod list **)

let rec door_to_door cells i1 i2 opt_source opt_target = function
| Nil -> Nil
| Cons (i3, tl') ->
  (match tl' with
   | Nil -> to_next_door opt_source opt_target cells i1 i2 i3
   | Cons (_, _) ->
     let tail_path = door_to_door cells i2 i3 None opt_target tl' in
     app (to_next_door opt_source None cells i1 i2 i3) tail_path)

(** val strict_inside_closed : pt -> cell -> bool **)

let strict_inside_closed p c =
  match match negb (point_under_edge p c.low) with
        | True -> point_strictly_under_edge p c.high
        | False -> False with
  | True ->
    (match qlt_bool (left_limit c) p.p_x with
     | True -> qlt_bool p.p_x (right_limit c)
     | False -> False)
  | False -> False

(** val find_origin_cells : cell list -> pt -> nat list **)

let find_origin_cells cells p =
  match find (fun i -> strict_inside_closed p (nth i cells dummy_cell))
          (iota O (length cells)) with
  | Some n -> Cons (n, Nil)
  | None ->
    head Nil
      (map (fun av -> Cons ((snd av),
        (match door_right_cell cells (fst av) with
         | Some rc -> Cons (rc, Nil)
         | None -> Nil)))
        (filter (fun av -> on_vert_edge p (fst av)) (all_doors cells)))

(** val intersection : nat list -> nat list -> nat list **)

let intersection s1 s2 =
  filter (fun e -> existsb (fun e' -> Nat.eqb e e') s2) s1

(** val point_to_point :
    cell list -> pt -> pt -> (annotated_point, annotated_point) prod list
    option **)

let point_to_point cells source target =
  let source_is = find_origin_cells cells source in
  let target_is = find_origin_cells cells target in
  (match match Nat.ltb O (length source_is) with
         | True -> Nat.ltb O (length target_is)
         | False -> False with
   | True ->
     (match Nat.ltb O (length (intersection source_is target_is)) with
      | True ->
        Some (Cons ((Pair ({ apt_val = source; cell_indices = source_is },
          { apt_val = target; cell_indices = target_is })), Nil))
      | False ->
        let ocp = cell_path cells (head O source_is) (head O target_is) in
        (match ocp with
         | Some cp ->
           (match Nat.leb (S (S O)) (length cp) with
            | True ->
              (match existsb (Nat.eqb (nth O cp O)) source_is with
               | True ->
                 (match existsb
                          (Nat.eqb (nth (sub (length cp) (S (S O))) cp O))
                          target_is with
                  | True ->
                    Some
                      (door_to_door cells (head O source_is) (nth O cp O)
                        (Some source) (Some target) (behead cp))
                  | False ->
                    Some
                      (app
                        (door_to_door cells (head O source_is) (nth O cp O)
                          (Some source) None (behead cp))
                        (path_reverse
                          (point_to_door cells { apt_val = target;
                            cell_indices = target_is }
                            (nth (sub (length cp) (S O)) cp O)
                            (nth (sub (length cp) (S (S O))) cp O)))))
               | False ->
                 (match existsb
                          (Nat.eqb (nth (sub (length cp) (S (S O))) cp O))
                          target_is with
                  | True ->
                    Some
                      (app
                        (point_to_door cells { apt_val = source;
                          cell_indices = source_is } (head O source_is)
                          (nth O cp O))
                        (door_to_door cells (head O source_is) (nth O cp O)
                          None (Some target) (behead cp)))
                  | False ->
                    Some
                      (app
                        (point_to_door cells { apt_val = source;
                          cell_indices = source_is } (head O source_is)
                          (nth O cp O))
                        (app
                          (door_to_door cells (head O source_is) (nth O cp O)
                            None None (behead cp))
                          (path_reverse
                            (point_to_door cells { apt_val = target;
                              cell_indices = target_is }
                              (nth (sub (length cp) (S O)) cp O)
                              (nth (sub (length cp) (S (S O))) cp O)))))))
            | False ->
              (match common_vert_edge
                       (nth (head O source_is) cells dummy_cell)
                       (nth (head O target_is) cells dummy_cell) with
               | Some v ->
                 (match match on_vert_edge source v with
                        | True -> True
                        | False -> on_vert_edge target v with
                  | True ->
                    Some (Cons ((Pair ({ apt_val = source; cell_indices =
                      source_is }, { apt_val = target; cell_indices =
                      target_is })), Nil))
                  | False ->
                    Some
                      (app
                        (point_to_door cells { apt_val = source;
                          cell_indices = source_is } (head O source_is)
                          (head O target_is))
                        (path_reverse
                          (point_to_door cells { apt_val = target;
                            cell_indices = target_is } (head O source_is)
                            (head O target_is)))))
               | None -> None))
         | None -> None))
   | False -> None)

(** val break_segments :
    (annotated_point, annotated_point) prod list -> (annotated_point,
    annotated_point) prod list **)

let rec break_segments = function
| Nil -> Nil
| Cons (p, tl) ->
  let Pair (a, a0) = p in
  let { apt_val = p1; cell_indices = a1 } = a in
  let { apt_val = p2; cell_indices = a2 } = a0 in
  Cons ((Pair ({ apt_val = p1; cell_indices = a1 }, { apt_val =
  (midpoint p1 p2); cell_indices = (intersection a1 a2) })), (Cons ((Pair
  ({ apt_val = (midpoint p1 p2); cell_indices = (intersection a1 a2) },
  { apt_val = p2; cell_indices = a2 })), (break_segments tl))))

type curve_element =
| Straight of annotated_point * annotated_point
| Bezier of annotated_point * annotated_point * annotated_point

(** val smoothen_aux :
    (annotated_point, annotated_point) prod list -> curve_element list **)

let rec smoothen_aux = function
| Nil -> Nil
| Cons (p, l) ->
  let Pair (a, b) = p in
  (match l with
   | Nil -> Cons ((Straight (a, b)), Nil)
   | Cons (p0, tl) ->
     let Pair (_, c) = p0 in Cons ((Bezier (a, b, c)), (smoothen_aux tl)))

(** val smoothen :
    (annotated_point, annotated_point) prod list -> curve_element list **)

let smoothen = function
| Nil -> Nil
| Cons (p, tl) ->
  let Pair (a, b) = p in Cons ((Straight (a, b)), (smoothen_aux tl))

(** val check_bezier_ccw :
    nat -> vert_edge -> pt -> pt -> pt -> bool option **)

let rec check_bezier_ccw fuel v a b c =
  match fuel with
  | O -> None
  | S p ->
    let top_edge = { p_x = v.ve_x; p_y = v.ve_top } in
    (match negb (point_under_edge top_edge { left_pt = a; right_pt = c }) with
     | True -> Some True
     | False ->
       (match match point_under_edge top_edge { left_pt = a; right_pt = b } with
              | True -> True
              | False ->
                point_under_edge top_edge { left_pt = b; right_pt = c } with
        | True -> Some False
        | False ->
          let b' = midpoint a b in
          let b2 = midpoint b c in
          let c' = midpoint b' b2 in
          (match qlt_bool c'.p_x v.ve_x with
           | True -> check_bezier_ccw p v c' b2 c
           | False ->
             (match qlt_bool v.ve_x c'.p_x with
              | True -> check_bezier_ccw p v a b' c'
              | False -> Some (qlt_bool c'.p_y v.ve_top)))))

(** val check_bezier_cw : nat -> vert_edge -> pt -> pt -> pt -> bool option **)

let rec check_bezier_cw fuel v a b c =
  match fuel with
  | O -> None
  | S p ->
    let bot_edge = { p_x = v.ve_x; p_y = v.ve_bot } in
    (match point_strictly_under_edge bot_edge { left_pt = a; right_pt = c } with
     | True -> Some True
     | False ->
       (match match negb
                      (point_strictly_under_edge bot_edge { left_pt = a;
                        right_pt = b }) with
              | True -> True
              | False ->
                negb
                  (point_strictly_under_edge bot_edge { left_pt = b;
                    right_pt = c }) with
        | True -> Some False
        | False ->
          let b' = midpoint a b in
          let b2 = midpoint b c in
          let c' = midpoint b' b2 in
          (match qlt_bool c'.p_x v.ve_x with
           | True -> check_bezier_cw p v c' b2 c
           | False ->
             (match qlt_bool v.ve_x c'.p_x with
              | True -> check_bezier_cw p v a b' c'
              | False -> Some (qlt_bool v.ve_bot c'.p_y)))))

(** val check_curve_element_and_repair :
    nat -> cell list -> curve_element -> curve_element list **)

let rec check_curve_element_and_repair fuel cells = function
| Straight (p1, p2) -> Cons ((Straight (p1, p2)), Nil)
| Bezier (p1, p2, p3) ->
  (match Nat.eqb (length p2.cell_indices) (S (S O)) with
   | True ->
     let i1 = nth O p2.cell_indices O in
     let i2 = nth (S O) p2.cell_indices O in
     let vedge =
       match common_vert_edge (nth i1 cells dummy_cell)
               (nth i2 cells dummy_cell) with
       | Some v -> v
       | None -> dummy_vert_edge
     in
     let e' =
       match qlt_bool p1.apt_val.p_x p2.apt_val.p_x with
       | True -> Bezier (p1, p2, p3)
       | False -> Bezier (p3, p2, p1)
     in
     (match e' with
      | Straight (_, _) -> Cons (e', Nil)
      | Bezier (p1', p2', p3') ->
        let check_function =
          match qlt_bool { qnum = Z0; qden = XH }
                  (pue_formula p1'.apt_val p2'.apt_val p3'.apt_val) with
          | True -> check_bezier_ccw
          | False -> check_bezier_cw
        in
        (match check_function (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S O)))))))))))))))))))) vedge p1'.apt_val
                 p2'.apt_val p3'.apt_val with
         | Some b ->
           (match b with
            | True -> Cons ((Bezier (p1, p2, p3)), Nil)
            | False ->
              (match fuel with
               | O ->
                 Cons ((Straight (p1, p2)), (Cons ((Straight (p2, p3)), Nil)))
               | S p ->
                 Cons ((Straight (p1, { apt_val =
                   (midpoint p1.apt_val p2.apt_val); cell_indices =
                   p1.cell_indices })),
                   (app
                     (check_curve_element_and_repair p cells (Bezier
                       ({ apt_val = (midpoint p1.apt_val p2.apt_val);
                       cell_indices = p1.cell_indices }, p2, { apt_val =
                       (midpoint p2.apt_val p3.apt_val); cell_indices =
                       p3.cell_indices }))) (Cons ((Straight ({ apt_val =
                     (midpoint p2.apt_val p3.apt_val); cell_indices =
                     p3.cell_indices }, p3)), Nil))))))
         | None ->
           (match fuel with
            | O ->
              Cons ((Straight (p1, p2)), (Cons ((Straight (p2, p3)), Nil)))
            | S p ->
              Cons ((Straight (p1, { apt_val =
                (midpoint p1.apt_val p2.apt_val); cell_indices =
                p1.cell_indices })),
                (app
                  (check_curve_element_and_repair p cells (Bezier ({ apt_val =
                    (midpoint p1.apt_val p2.apt_val); cell_indices =
                    p1.cell_indices }, p2, { apt_val =
                    (midpoint p2.apt_val p3.apt_val); cell_indices =
                    p3.cell_indices }))) (Cons ((Straight ({ apt_val =
                  (midpoint p2.apt_val p3.apt_val); cell_indices =
                  p3.cell_indices }, p3)), Nil)))))))
   | False -> Cons ((Bezier (p1, p2, p3)), Nil))

(** val smooth_from_cells : cell list -> pt -> pt -> curve_element list **)

let smooth_from_cells cells initial final =
  match point_to_point cells initial final with
  | Some s ->
    concat
      (map
        (check_curve_element_and_repair (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S O)))))))))))))))))))) cells)
        (smoothen (break_segments s)))
  | None -> Nil

(** val smooth_point_to_point :
    edge -> edge -> edge list -> pt -> pt -> curve_element list **)

let smooth_point_to_point bottom top obstacles initial final =
  let cells = edges_to_cells bottom top obstacles in
  smooth_from_cells cells initial final

(** val example_edge_sets : edge list list **)

let example_edge_sets =
  Cons ((Cons ({ left_pt = { p_x = { qnum = (Zneg (XI XH)); qden = XH }; p_y =
    { qnum = Z0; qden = XH } }; right_pt = { p_x = { qnum = (Zneg (XO XH));
    qden = XH }; p_y = { qnum = (Zpos XH); qden = XH } } }, (Cons ({ left_pt =
    { p_x = { qnum = (Zneg (XI XH)); qden = XH }; p_y = { qnum = Z0; qden =
    XH } }; right_pt = { p_x = { qnum = Z0; qden = XH }; p_y = { qnum = (Zneg
    (XI XH)); qden = XH } } }, (Cons ({ left_pt = { p_x = { qnum = Z0; qden =
    XH }; p_y = { qnum = (Zneg (XI XH)); qden = XH } }; right_pt = { p_x =
    { qnum = (Zpos (XI XH)); qden = XH }; p_y = { qnum = Z0; qden = XH } } },
    (Cons ({ left_pt = { p_x = { qnum = (Zneg (XO XH)); qden = XH }; p_y =
    { qnum = (Zpos XH); qden = XH } }; right_pt = { p_x = { qnum = Z0; qden =
    XH }; p_y = { qnum = (Zpos XH); qden = XH } } }, (Cons ({ left_pt =
    { p_x = { qnum = Z0; qden = XH }; p_y = { qnum = (Zpos XH); qden = XH } };
    right_pt = { p_x = { qnum = (Zpos XH); qden = XH }; p_y = { qnum = Z0;
    qden = XH } } }, (Cons ({ left_pt = { p_x = { qnum = (Zneg XH); qden =
    XH }; p_y = { qnum = Z0; qden = XH } }; right_pt = { p_x = { qnum = Z0;
    qden = XH }; p_y = { qnum = (Zneg XH); qden = XH } } }, (Cons ({ left_pt =
    { p_x = { qnum = Z0; qden = XH }; p_y = { qnum = (Zneg XH); qden = XH } };
    right_pt = { p_x = { qnum = (Zpos XH); qden = XH }; p_y = { qnum = Z0;
    qden = XH } } }, Nil)))))))))))))), (Cons ((Cons ({ left_pt = { p_x =
    { qnum = (Zneg (XO XH)); qden = XH }; p_y = { qnum = (Zneg (XO XH));
    qden = XH } }; right_pt = { p_x = { qnum = (Zpos (XO XH)); qden = XH };
    p_y = { qnum = Z0; qden = XH } } }, (Cons ({ left_pt = { p_x = { qnum =
    (Zpos (XO (XO (XO XH)))); qden = (XO (XI (XO XH))) }; p_y = { qnum = (Zneg
    (XO (XO (XI XH)))); qden = (XO (XI (XO XH))) } }; right_pt = { p_x =
    { qnum = (Zpos (XO XH)); qden = XH }; p_y = { qnum = Z0; qden = XH } } },
    (Cons ({ left_pt = { p_x = { qnum = (Zpos (XO (XO (XO XH)))); qden = (XO
    (XI (XO XH))) }; p_y = { qnum = (Zneg (XO (XO (XI XH)))); qden = (XO (XI
    (XO XH))) } }; right_pt = { p_x = { qnum = (Zpos (XI (XO (XO (XO XH)))));
    qden = (XI (XO XH)) }; p_y = { qnum = (Zneg (XI XH)); qden = XH } } },
    (Cons ({ left_pt = { p_x = { qnum = (Zneg (XO XH)); qden = XH }; p_y =
    { qnum = (Zneg (XO XH)); qden = XH } }; right_pt = { p_x = { qnum = (Zpos
    (XI (XO (XO (XO XH))))); qden = (XI (XO XH)) }; p_y = { qnum = (Zneg (XI
    XH)); qden = XH } } }, Nil)))))))), (Cons ((Cons ({ left_pt = { p_x =
    { qnum = (Zneg XH); qden = XH }; p_y = { qnum = Z0; qden = XH } };
    right_pt = { p_x = { qnum = Z0; qden = XH }; p_y = { qnum = (Zneg XH);
    qden = XH } } }, (Cons ({ left_pt = { p_x = { qnum = Z0; qden = XH };
    p_y = { qnum = (Zpos XH); qden = XH } }; right_pt = { p_x = { qnum = (Zpos
    XH); qden = XH }; p_y = { qnum = Z0; qden = XH } } }, Nil)))), Nil)))))

(** val example_point_spread_sets : (pt, pt) prod list list **)

let example_point_spread_sets =
  Cons ((Cons ((Pair ({ p_x = { qnum = (Zpos (XI (XO XH))); qden = (XO (XI (XO
    XH))) }; p_y = { qnum = (Zpos (XI XH)); qden = (XO (XI (XO XH))) } },
    { p_x = { qnum = (Zneg (XI XH)); qden = XH }; p_y = { qnum = (Zpos (XI (XI
    (XO (XO XH))))); qden = (XO (XI (XO XH))) } })), (Cons ((Pair ({ p_x =
    { qnum = (Zneg (XI XH)); qden = XH }; p_y = { qnum = (Zpos (XI (XI (XO (XO
    XH))))); qden = (XO (XI (XO XH))) } }, { p_x = { qnum = (Zneg XH); qden =
    XH }; p_y = { qnum = (Zpos (XO (XI (XO (XO (XO (XO XH))))))); qden = (XO
    (XO (XI (XO (XO (XI XH)))))) } })), (Cons ((Pair ({ p_x = { qnum = (Zneg
    (XI (XI (XO (XO XH))))); qden = (XO (XI (XO XH))) }; p_y = { qnum = (Zpos
    (XI (XO (XO XH)))); qden = (XO (XI (XO XH))) } }, { p_x = { qnum = (Zpos
    (XI (XI (XI XH)))); qden = (XO (XI (XO XH))) }; p_y = { qnum = (Zneg XH);
    qden = XH } })), Nil)))))), (Cons ((Cons ((Pair ({ p_x = { qnum = Z0;
    qden = XH }; p_y = { qnum = (Zpos (XI XH)); qden = (XO (XI (XO XH))) } },
    { p_x = { qnum = (Zneg (XI XH)); qden = XH }; p_y = { qnum = (Zpos (XI (XI
    (XO (XO XH))))); qden = (XO (XI (XO XH))) } })), (Cons ((Pair ({ p_x =
    { qnum = (Zneg (XI XH)); qden = XH }; p_y = { qnum = (Zpos (XI (XI (XO (XO
    XH))))); qden = (XO (XI (XO XH))) } }, { p_x = { qnum = (Zpos (XI (XI (XI
    XH)))); qden = (XO (XI (XO XH))) }; p_y = { qnum = (Zneg XH); qden =
    XH } })), (Cons ((Pair ({ p_x = { qnum = (Zneg (XI (XI (XO (XO XH)))));
    qden = (XO (XI (XO XH))) }; p_y = { qnum = (Zneg (XI (XO (XI (XO XH)))));
    qden = (XO (XI (XO XH))) } }, { p_x = { qnum = (Zpos (XI (XI (XI XH))));
    qden = (XO (XI (XO XH))) }; p_y = { qnum = (Zneg XH); qden = XH } })),
    Nil)))))), (Cons ((Cons ((Pair ({ p_x = { qnum = (Zneg (XI (XO XH)));
    qden = (XO (XI (XO XH))) }; p_y = { qnum = Z0; qden = XH } }, { p_x =
    { qnum = (Zpos (XI (XO XH))); qden = (XO (XI (XO XH))) }; p_y = { qnum =
    Z0; qden = XH } })), (Cons ((Pair ({ p_x = { qnum = (Zneg (XI (XI (XO
    XH)))); qden = (XO (XI (XO XH))) }; p_y = { qnum = Z0; qden = XH } },
    { p_x = { qnum = (Zpos (XI (XO XH))); qden = (XO (XI (XO XH))) }; p_y =
    { qnum = Z0; qden = XH } })), (Cons ((Pair ({ p_x = { qnum = Z0; qden =
    XH }; p_y = { qnum = Z0; qden = XH } }, { p_x = { qnum = (Zpos XH); qden =
    XH }; p_y = { qnum = (Zpos XH); qden = XH } })), Nil)))))), Nil)))))

(** val example_bottom : edge **)

let example_bottom =
  { left_pt = { p_x = { qnum = (Zneg (XO (XO XH))); qden = XH }; p_y =
    { qnum = (Zneg (XO (XO XH))); qden = XH } }; right_pt = { p_x = { qnum =
    (Zpos (XO (XO XH))); qden = XH }; p_y = { qnum = (Zneg (XO (XO XH)));
    qden = XH } } }

(** val example_top : edge **)

let example_top =
  { left_pt = { p_x = { qnum = (Zneg (XO (XO XH))); qden = XH }; p_y =
    { qnum = (Zpos (XO XH)); qden = XH } }; right_pt = { p_x = { qnum = (Zpos
    (XO (XO XH))); qden = XH }; p_y = { qnum = (Zpos (XO XH)); qden = XH } } }
