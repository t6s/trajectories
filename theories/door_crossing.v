From mathcomp Require Import all_ssreflect all_algebra all_real_closed reals.
From mathcomp.algebra_tactics Require Import ring.
Require Import casteljau convex counterclockwise intersection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Import GRing.Theory.
Import Num.Theory Num.Def.
Local Open Scope ring_scope.

Section sandbox.

Lemma poly_coord {R : rcfType} 
  (c : pair_vectType (regular_vectType R) (regular_vectType R))
  (p : {poly R}) (t : R) :
  p.[t] *: c = c.1 * p.[t] *: (1, 0) + c.2 * p.[t] *: (0, 1).
Proof.
congr (_, _); rewrite /= !scaler0 ?addr0 ?add0r mulrC /GRing.scale /=; ring.
Qed.

  
Variable R : reals.Real.type.

(* This version differs from the one in the hulls development to avoid
  using Program Fixpoint. Here the sequence of control point is given
  by a function and the degree is given as argument. *)
Fixpoint bezier (c : nat -> Plane R) (n : nat) (t : R) :=
  match n with
  | 0 => c 0%N
  | S p => (1 - t) *: (bezier c p t) +
           t *: (bezier (c \o S) p t)
  end.

(* TODO: complain about the wrong error message for the following mistake. *)
(* Lemma bezier_bernstein2 c t :
  bezier c 2 t =  (bernp 0 1 2 0) *: c 0%N. *)

Lemma bezier_bernstein2 c t :
  bezier c 2 t = 
    \sum_(i < 3) (bernp 0 1 2 i).[t] *: c i.
Proof.
rewrite !big_ord_recr big_ord0 /= add0r.
rewrite /= scalerDr scalerA -!addrA; congr (_ *: _ + _).
  by rewrite /bernp !hornerE /= subr0 expr1n invr1; ring.
rewrite !(scalerA, scalerDr) addrA -scalerDl; congr (_ *:_ + _ *: _).
  by rewrite /bernp !hornerE /= subr0 expr1n invr1; ring.
by rewrite /bernp !hornerE /= subr0 expr1n invr1; ring.
Qed.

Lemma bezier2_1 c u : bezier c 1 u = (1 - u) *: c 0%N + u *: c 1%N.
Proof. by []. Qed.


(* The proofs of these lemmas follow a general pattern explained in file casteljau.
  However, here, we can brute force the proof because we are working with a known
  low degree. *)
Lemma bezier2_dichotomy_l (c : nat -> Plane R) (t u : R) :
  bezier c 2 (t * u) =
  bezier [fun n => c n with 1%nat |-> bezier c 1 u, 2%nat |-> bezier c 2 u] 2
    t.
Proof.
rewrite /bezier /= !scalerDr !scalerA !addrA.
(* Make sure all instance of c 0 are grouped on the left and c 0 is factored out. *)
rewrite !(addrAC _ (_ *: c (S O)) (_ *: c O)) -!scalerDl.
rewrite -!addrA; congr (_ *: _ + _); first by ring.
(* Now factor out all instances of c 1 *)
rewrite !addrA -!scalerDl; congr (_ *: _ + _ *: _); ring.
Qed.

Lemma bezier2_dichotomy_r (c : nat -> Plane R) (t u : R) :
  bezier c 2 (u + t * (1 - u)) =
  bezier [fun n => c n with 0%N |-> bezier c 2 u, 1%N |-> bezier (c \o S) 1 u] 2
    t.
Proof.
rewrite /bezier /= !scalerDr !scalerA !addrA.
(* There is only one instance of c 0 on the left, we can process it directly *)
rewrite -!addrA; congr (_ *: _ + _); first by ring.
rewrite !addrA -!scalerDl.
rewrite !(addrAC _ (_ *: c (S (S _))) (_ *: c (S O))) -!scalerDl.
rewrite -!addrA -!scalerDl.
congr (_ *: _ + _ *: _); ring.
Qed.

Record edge := Bedge 
  { left_pt : Plane R;
    right_pt : Plane R; 
    edge_cond : left_pt.1 < right_pt.1}.

Record cell :=
  { left_pts : seq (Plane R); right_pts : seq (Plane R); low : edge; high : edge}.

Definition valid_edge : edge -> Plane R -> bool :=
  fun g p => (left_pt g).1 <= p.1 <= (right_pt g).1.

Definition point_on_edge (p : Plane R) (g : edge) :=
  valid_edge g p && (det (left_pt g) (right_pt g) p == 0).

Notation "p '===' e" := (point_on_edge p e)( at level 70, no associativity).

Definition dummy_pt : Plane R := (0, 0).

Definition closed_cell_side_limit_ok c :=
 [&& left_pts c != [::],
   all (fun p => p.1 == (last dummy_pt (left_pts c)).1) (left_pts c),
   sorted >%R [seq p.2 | p <- left_pts c],
   head dummy_pt (left_pts c) === high c,
   last dummy_pt (left_pts c) === low c,
    right_pts c != [::],
   all (fun p => p.1 == (head dummy_pt (right_pts c)).1) (right_pts c),
   sorted <%R [seq p.2 | p <- right_pts c],
   head dummy_pt (right_pts c) === low c &
   last dummy_pt (right_pts c) === high c].

Definition left_limit (c : cell) := (last dummy_pt (left_pts c)).1.

Definition right_limit c := (last dummy_pt (right_pts c)).1.

Definition point_under_edge (p : Plane R) (e : edge) : bool :=
  det p (left_pt e) (right_pt e) <= 0.

  (* returns true if p is strictly under e *)
Definition point_strictly_under_edge (p : Plane R) (e : edge) : bool :=
  det p (left_pt e) (right_pt e) < 0.

Notation "p '<<=' e" := (point_under_edge p e)( at level 70, no associativity).
Notation "p '<<<' e" := (point_strictly_under_edge p e)(at level 70, no associativity).

Definition strict_inside_closed (p : Plane R) (c : cell) :=
  (p <<< high c) && (~~(p <<= low c)) &&
  (left_limit c < p.1 < right_limit c).

Definition bottom_left_corner (c : cell) := last dummy_pt (left_pts c).

Record vert_edge := { ve_x : R; ve_top : R; ve_bot : R}.

Definition vert_edge_eqb (v1 v2 : vert_edge) :=
  let: Build_vert_edge v1x v1t v1b := v1 in
  let: Build_vert_edge v2x v2t v2b := v2 in
  (v1x == v2x) && (v1t == v2t) && (v1b == v2b).

Lemma vert_edge_eqP : Equality.axiom vert_edge_eqb.
Proof.
move=> [vxa vta vba] [vxb vtb vbb] /=.
have [/eqP <-|/eqP anb] := boolP(vxa == vxb).
  have [/eqP <-|/eqP anb] := boolP(vta == vtb).
    have [/eqP <-| /eqP anb] := boolP(vba == vbb).
      by apply:ReflectT.
    by apply: ReflectF=> [] [].
  by apply: ReflectF=> [] [].
by apply: ReflectF=> [] [].
Qed.

Fail Check (fun (x : vert_edge) (l : seq vert_edge) => x \in l).

Canonical vert_edge_eqType := EqType vert_edge (EqMixin vert_edge_eqP).

Fixpoint seq_to_intervals_aux [A : Type] (a : A) (s : seq A) :=
match s with
| nil => nil
| b :: tl => (a, b) :: seq_to_intervals_aux b tl
end.

Definition seq_to_intervals [A : Type] (s : seq A) :=
match s with
  nil => nil
| a :: tl => seq_to_intervals_aux a tl
end.

Definition cell_safe_exits_left (c : cell) : seq vert_edge :=
  let lx := (seq.head dummy_pt (left_pts c)).1 in
  map (fun p => Build_vert_edge lx (fst p).2 (snd p).2) 
   (seq_to_intervals (left_pts c)).

Definition cell_safe_exits_right (c : cell) : seq vert_edge :=
  let lx := (seq.head dummy_pt (right_pts c)).1 in
  map (fun p => Build_vert_edge lx (fst p).2 (snd p).2) 
   (seq_to_intervals (rev (right_pts c))).

Definition dummy_vert_edge :=
  {| ve_x := 0; ve_top := 0; ve_bot := 0|}.

Definition on_vert_edge (p : Plane R) (v : vert_edge) : bool :=
  (p.1 == ve_x v) && (ve_bot v < p.2 < ve_top v).

Check fun (v : vert_edge) (l : seq vert_edge) => v \in l.
Check fun (v : vert_edge)(c : cell) => 
   v \in cell_safe_exits_left c.

Lemma detDM2 (l p1 p2 q1 q2 r1 r2 : R) :
  l * det (p1, p2) (q1, q2) (r1, r2) =
  det (p1, p2) (p1 + l * (q1 - p1), p2 + l * (q2 - p2)) (r1, r2).
Proof. by rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma detDM1 (l p1 p2 q1 q2 r1 r2 : R) :
  l * det (p1, p2) (q1, q2) (r1, r2) =
  det (q1 + l * (p1 - q1), q2 + l * (p2 - q2)) (q1, q2) (r1, r2).
Proof. by rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma detDM3 (l p1 p2 q1 q2 r1 r2 : R) :
det (p1, p2) (q1, q2) (r1, r2) =
det (p1, p2) (q1, q2) (r1 + l * (q1 - p1), r2 + l * (q2 - p2)).
Proof. by rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma detVert (p1 p2 q1 q2 r2 : R) :
  det (p1, p2) (q1, q2) (q1, r2) =
   (r2 - q2) * (q1 - p1).
Proof. rewrite !develop_det /xcoord /ycoord /=; ring. Qed.

Lemma bezier1_conv c t : bezier c 1 t = c 0%nat <| (1 - t) |> c 1%nat.
Proof.  rewrite /= /conv; congr (_ *: _ + _ *: _); ring. Qed.

Lemma left_vertical_edge_wrt_high c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_left c ->
  (ve_top v <= (head dummy_pt (left_pts c)).2) &&
  ((left_pt (high c)).1 <= ve_x v < (right_pt (high c)).1) &&
  (ve_x v == (head dummy_pt (left_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl /andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have {}samexl : {in left_pts c, forall p, (head dummy_pt (left_pts c)).1 = p.1 }.
  move=> x xin; rewrite (eqP (samexl x xin)).
  rewrite -(eqP (samexl (head dummy_pt (left_pts c)) _)) //.
  by move: leftn0; case (left_pts c)=> //= s l _; rewrite inE eqxx.
have vxleft : ve_x v = left_limit c.
  move: vin.
  rewrite /left_limit /cell_safe_exits_left.
  elim: (left_pts c) leftn0 samexl => [ // | e1 [// | e2 tl] Ih] _ /= samexl.
  rewrite inE=> /orP[/eqP -> /= | vin]; first by apply: samexl; rewrite inE mem_last orbT.
  apply: (Ih isT)=> /=.
     move=> x xin. rewrite -(samexl e2); last by rewrite !inE eqxx orbT.
     by apply: samexl; rewrite inE xin orbT.
  by rewrite -(samexl e2) //; rewrite !inE eqxx orbT.
apply/andP; split; last first.
  rewrite vxleft /left_limit (samexl (last dummy_pt (left_pts c))) //.
  by case: (left_pts c) leftn0=> [// | ? ?]; rewrite /= mem_last.
move: llr.
rewrite vxleft /left_limit -(samexl (last dummy_pt (left_pts c))); last first.
   by case: (left_pts c) leftn0 => //= a tl _ ; rewrite mem_last.
move: lonh=> /andP[] /andP[] -> /= _ _ llr.
rewrite (lt_le_trans llr) ?andbT; last first.
  by rewrite /right_limit; move: ronh=> /andP[] /andP[] _ ->.
move: vin; rewrite /cell_safe_exits_left.
elim: (left_pts c) leftn0 sortl samexl
  => [// | e1 [ // | e2 tl] /(_ isT) Ih] _ /= /andP[] cmp s samexl.
rewrite inE=> /orP[/eqP -> // | vin ].
apply: (le_trans _ (ltW cmp)).
apply Ih=> //=.
  move=> x xin.
  by rewrite -(samexl e2) ?inE ?eqxx ?orbT // (samexl x) // inE xin orbT.
by rewrite -(samexl e2) // !inE eqxx orbT.
Qed.

Lemma seq_to_intervals_rcons [A : Type](e1 e2 : A) l :
  seq_to_intervals (rcons (rcons l e2) e1) =
  rcons (seq_to_intervals (rcons l e2)) (e2, e1).
Proof. by elim: l => [// | e3 [// | e4 l] /= Ih] //; rewrite Ih. Qed.

Lemma right_vertical_edge_wrt_high c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_right c ->
  (ve_top v <= (last dummy_pt (right_pts c)).2) &&
  ((left_pt (high c)).1 < ve_x v <= (right_pt (high c)).1) &&
  (ve_x v == (last dummy_pt (right_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl /andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have vxright : ve_x v = right_limit c.
  move: vin.
  rewrite /right_limit /cell_safe_exits_right.
  elim/last_ind: (right_pts c) rightn0 samexr => [ // | lh e1 Ih] _ /=.
  elim/last_ind: lh Ih => [ // | lh e2 _] Ih samexr.
  rewrite last_rcons !rev_rcons/=.
  rewrite inE=> /orP[/eqP -> /= | vin]. 
    by rewrite (eqP (samexr e1 _)) // mem_rcons inE eqxx.
  rewrite (eqP (samexr e1 _)); last by rewrite mem_rcons inE eqxx.
  rewrite -(eqP (samexr e2 _)); last by rewrite !(mem_rcons, inE) eqxx ?orbT.
  rewrite [e2](_ : _ = last dummy_pt (rcons lh e2)); last by rewrite last_rcons.
  apply: Ih=> /=.
      by case lhq: lh.
     move=> x xin.
     rewrite (eqP (samexr x _)); last by rewrite mem_rcons inE xin orbT.
     by rewrite 3!headI /=.
  rewrite [head _ (rcons _ _)](_ : _ = head dummy_pt (rcons lh e2)) in vin; last first.
    by rewrite 3!headI /=.
  by rewrite rev_rcons; apply: vin.
apply/andP; split; last by rewrite vxright.
move: llr.
rewrite vxright /right_limit.
move: ronh=> /andP[] /andP[] _ -> /= _ llr.
rewrite (le_lt_trans _ llr) ?andbT; last first.
  rewrite /left_limit; move: lonh=> /andP[] /andP[] + _ _.
  rewrite (eqP (samexl (head dummy_pt (left_pts c)) _)) //.
  by case: (left_pts c) leftn0 => [// | a ?]; rewrite /= inE eqxx.
move: vin; rewrite /cell_safe_exits_right.
elim/last_ind: (right_pts c) rightn0 sortr samexr=> [// | + e1 ].
elim/last_ind=> [// | l e2 _] Ih _ sortr samexr.
rewrite 2!rev_rcons /= inE last_rcons=> /orP[/eqP -> | vin]; first by [].
have cmp : e2.2 < e1.2.
  move: sortr; rewrite -2!cats1 -catA /= map_cat=> /cat_sorted2[_ /=].
  by rewrite andbT.
have {}sortr : sorted <%R [seq p.2 | p <- rcons l e2].
  by move: sortr; rewrite -cats1 map_cat=> /cat_sorted2[].
apply: (le_trans _ (ltW cmp)).
rewrite [e2](_ : _ = last dummy_pt (rcons l e2)); last by rewrite last_rcons.
apply Ih=> //=.
   by case lq : l.
  move=> x xin.
  have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
    by case lq : l.
  by apply: samexr; rewrite mem_rcons inE xin orbT.
have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
  by case lq : l.
by rewrite rev_rcons.
Qed.

Lemma left_vertical_edge_wrt_low c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_left c ->
  ((last dummy_pt (left_pts c)).2 <= ve_bot v) &&
  ((left_pt (low c)).1 <= ve_x v < (right_pt (low c)).1) &&
  (ve_x v == (last dummy_pt (left_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl /andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have {}samexl : {in left_pts c, forall p, (head dummy_pt (left_pts c)).1 = p.1 }.
  move=> x xin; rewrite (eqP (samexl x xin)).
  rewrite -(eqP (samexl (head dummy_pt (left_pts c)) _)) //.
  by move: leftn0; case (left_pts c)=> //= s l _; rewrite inE eqxx.
have vxleft : ve_x v = left_limit c.
  move: vin.
  rewrite /left_limit /cell_safe_exits_left.
  elim: (left_pts c) leftn0 samexl => [ // | e1 [// | e2 tl] Ih] _ /= samexl.
  rewrite inE=> /orP[/eqP -> /= | vin]; first by apply: samexl; rewrite inE mem_last orbT.
  apply: (Ih isT)=> /=.
     move=> x xin. rewrite -(samexl e2); last by rewrite !inE eqxx orbT.
     by apply: samexl; rewrite inE xin orbT.
  by rewrite -(samexl e2) //; rewrite !inE eqxx orbT.
apply/andP; split; last by rewrite vxleft.
move: llr.
rewrite vxleft /left_limit.
move: lonl=> /andP[] /andP[] -> /= _ _ llr.
rewrite (lt_le_trans llr) ?andbT; last first.
  rewrite /right_limit; move: ronl=> /andP[] /andP[] _ + _.
  rewrite -(eqP (samexr (last dummy_pt (right_pts c)) _)) //.
  by move: rightn0; case: (right_pts c)=> [// | ? ?]; rewrite /= mem_last.
move: vin; rewrite /cell_safe_exits_left.
elim: (left_pts c) leftn0 sortl samexl
  => [// | e1 [ // | e2 tl] /(_ isT) Ih] _ /= /andP[] cmp s samexl.
rewrite inE=> /orP[/eqP -> /= | vin ].
  have sgt : subrel >%R (>=%R : rel R) by move=> x y /ltW.
  have s' : path >=%R e2.2 [seq p.2 | p <- tl].
    by apply: (sub_path sgt).
  case tlq : tl => [// | e3 tl']; rewrite -tlq.
  move: s'; rewrite path_sortedE; last by apply/rev_trans/le_trans.
  move=> /andP[] /allP /(_ (last e2 tl).2) + _; apply.
  by apply/mapP; exists (last e2 tl); rewrite // tlq /= mem_last.
apply Ih=> //=.
  move=> x xin.
  by rewrite -(samexl e2) ?inE ?eqxx ?orbT // (samexl x) // inE xin orbT.
by rewrite -(samexl e2) // !inE eqxx orbT.
Qed.

Lemma right_vertical_edge_wrt_low c v :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  v \in cell_safe_exits_right c ->
  ((head dummy_pt (right_pts c)).2 <= ve_bot v) &&
  ((left_pt (low c)).1 < ve_x v <= (right_pt (low c)).1) &&
  (ve_x v == (head dummy_pt (right_pts c)).1).
Proof.
move=> llr /andP[] leftn0 /andP[] /allP samexl /andP[] sortl /andP[] lonh /andP[] lonl.
move=> /andP[] rightn0 /andP[] /allP samexr /andP[] sortr /andP[] ronl ronh vin.
have vxright : ve_x v = right_limit c.
  move: vin.
  rewrite /right_limit /cell_safe_exits_right.
  elim/last_ind: (right_pts c) rightn0 samexr => [ // | lh e1 Ih] _ /=.
  elim/last_ind: lh Ih => [ // | lh e2 _] Ih samexr.
  rewrite last_rcons !rev_rcons/=.
  rewrite inE=> /orP[/eqP -> /= | vin]. 
    by rewrite (eqP (samexr e1 _)) // mem_rcons inE eqxx.
  rewrite (eqP (samexr e1 _)); last by rewrite mem_rcons inE eqxx.
  rewrite -(eqP (samexr e2 _)); last by rewrite !(mem_rcons, inE) eqxx ?orbT.
  rewrite [e2](_ : _ = last dummy_pt (rcons lh e2)); last by rewrite last_rcons.
  apply: Ih=> /=.
      by case lhq: lh.
     move=> x xin.
     rewrite (eqP (samexr x _)); last by rewrite mem_rcons inE xin orbT.
     by rewrite 3!headI /=.
  rewrite [head _ (rcons _ _)](_ : _ = head dummy_pt (rcons lh e2)) in vin; last first.
    by rewrite 3!headI /=.
  by rewrite rev_rcons; apply: vin.
apply/andP; split; last first.
  rewrite vxright /right_limit; apply: samexr.
  by case: (right_pts c) rightn0=> [// | ? ?]; rewrite /= mem_last.
move: llr.
rewrite vxright /right_limit.
move: ronl=> /andP[] /andP[] _ + _ /=.
rewrite -(eqP (samexr (last dummy_pt (right_pts c)) _)); last first.
  by case: (right_pts c) rightn0 => [// | ? ?]; rewrite /= mem_last.
move=> -> xcond; rewrite ?andbT.
rewrite (le_lt_trans _ xcond) ?andbT; last by move: lonl=> /andP[] /andP[].
move: vin; rewrite /cell_safe_exits_right.
elim/last_ind: (right_pts c) rightn0 sortr samexr=> [// | + e1 ].
elim/last_ind=> [// | l e2 _] Ih _ sortr samexr.
have cmp : e2.2 < e1.2.
  move: sortr; rewrite -2!cats1 -catA /= map_cat=> /cat_sorted2[_ /=].
  by rewrite andbT.
have {}sortr : sorted <%R [seq p.2 | p <- rcons l e2].
  by move: sortr; rewrite -cats1 map_cat=> /cat_sorted2[].
rewrite [head dummy_pt _](_ : _ = head e2 l); last by rewrite 2!headI /=.
rewrite 2!rev_rcons /= inE => /orP[/eqP -> /= | vin].
  case lq : l => [// | e3 l'] /=.
  move: sortr; rewrite lq /= => /(sub_path ltW).
  rewrite (path_sortedE le_trans)=> /andP[] /allP + _; apply.
  by apply/mapP; exists e2; rewrite // mem_rcons inE eqxx.
rewrite [X in X.2 <= _](_ : _ = head dummy_pt (rcons l e2)); last first.
  by case lq: l.
apply Ih=> //=.
   by case lq : l.
  move=> x xin.
  have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
    by case lq : l.
  by apply: samexr; rewrite mem_rcons inE xin orbT.
have -> : head dummy_pt (rcons l e2) = head dummy_pt (rcons (rcons l e2) e1).
  by case lq : l.
by rewrite rev_rcons 2!headI /=.
Qed.
  
Lemma vert_projr (p q r : Plane R) : 
  p.1 != q.1 -> (det p q r == 0) =
  (r.2 == q.2 + (r.1 - q.1) / (q.1 - p.1) * (q.2 - p.2)).
Proof.
case: p q r=> [p1 p2][q1 q2][r1 r2] /=; rewrite develop_det /= => e_cnd.
apply/idP/eqP; last first.
  move=> -> /=; rewrite !mulrDl -(opprB q1 p1) !mulrN (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  rewrite (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  apply/eqP; ring.
rewrite !(addrAC _ (- (r2 * (p1 - q1)))) subr_eq0 eq_sym => /eqP r2Mdf.
have dn0 : (p1 - q1) != 0 by rewrite subr_eq0.
apply: (mulIf dn0); rewrite r2Mdf mulrDl (mulrAC _ _ (p1 - q1)) -(opprB p1 q1).
rewrite invrN !(mulrN, mulNr).
rewrite mulfVK //; ring.
Qed.

Lemma vert_projl (p q r : Plane R) : 
  p.1 != q.1 -> (det p q r == 0) =
  (r.2 == p.2 + (r.1 - p.1) / (q.1 - p.1) * (q.2 - p.2)).
Proof.
case: p q r=> [p1 p2][q1 q2][r1 r2] /=; rewrite develop_det /= => e_cnd.
apply/idP/eqP; last first.
  move=> -> /=; rewrite !mulrDl -(opprB q1 p1) !mulrN (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  rewrite (mulrAC _ _ (q1 - p1)).
  rewrite mulfVK; last by rewrite subr_eq0 eq_sym.
  apply/eqP; ring.
rewrite !(addrAC _ (- (r2 * (p1 - q1)))) subr_eq0 eq_sym => /eqP r2Mdf.
have dn0 : (p1 - q1) != 0 by rewrite subr_eq0.
apply: (mulIf dn0); rewrite r2Mdf mulrDl (mulrAC _ _ (p1 - q1)) -(opprB p1 q1).
rewrite invrN !(mulrN, mulNr).
rewrite mulfVK //; ring.
Qed.

Lemma on_vert_edge_under_high_left v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_left c ->
  p <<< high c.
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] := left_vertical_edge_wrt_high llr cok vin.
move: (cok)=> /andP[] leftn0 /andP[] samexl /andP[] sortl /andP[] lonh REST.
rewrite /point_strictly_under_edge.
set l := ((right_pt (high c)).1 - p.1) / ((right_pt (high c)).1 - (left_pt (high c)).1).
set q := ((right_pt (high c)).1 - l * ((right_pt (high c)).1 - (left_pt (high c)).1),
        (right_pt (high c)).1 - l * ((right_pt (high c)).2 - (left_pt (high c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (high c)) => [q1 q2].
case rq : (right_pt (high c)) => [r1 r2].
have lv : l = (r1 - p1) / (r1 - q1) by rewrite /l pq rq lq /=.
have p1ltr1 : p1 < r1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (high c)); rewrite lq rq.
rewrite det_cyclique.
rewrite -(pmulr_rlt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = r1 + l * (q1 - r1).
  rewrite lv -(opprB r1 q1) mulrN mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (high c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite nmulr_llt0; last by rewrite subr_lt0.
have proj2: (head dummy_pt (left_pts c)).2 = r2 + (r1 - p1) / (r1 - q1) * (q2 - r2).
  have ecnd : (left_pt (high c)).1 != (right_pt (high c)).1.
    by apply/eqP=> abs; have := edge_cond (high c); rewrite abs lt_irreflexive.
  have := vert_projr (head dummy_pt (left_pts c)) ecnd.
  move: lonh=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_gt0.
apply: lt_le_trans vtople.
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma on_vert_edge_above_low_left v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_left c ->
  ~~ (p <<= low c).
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] := left_vertical_edge_wrt_low llr cok vin.
move: (cok)=> /andP[] leftn0 /andP[] samexl /andP[] sortl /andP[] _ /andP[] lonl REST.
rewrite /point_under_edge -ltNge.
set l := ((right_pt (low c)).1 - p.1) / ((right_pt (low c)).1 - (left_pt (low c)).1).
set q := ((right_pt (low c)).1 - l * ((right_pt (low c)).1 - (left_pt (low c)).1),
        (right_pt (low c)).1 - l * ((right_pt (low c)).2 - (left_pt (low c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (low c)) => [q1 q2].
case rq : (right_pt (low c)) => [r1 r2].
have lv : l = (r1 - p1) / (r1 - q1) by rewrite /l pq rq lq /=.
have p1ltr1 : p1 < r1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (low c)); rewrite lq rq.
rewrite det_cyclique.
rewrite -(pmulr_rgt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = r1 + l * (q1 - r1).
  rewrite lv -(opprB r1 q1) mulrN mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (low c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite nmulr_lgt0; last by rewrite subr_lt0.
have proj2: (last dummy_pt (left_pts c)).2 = r2 + (r1 - p1) / (r1 - q1) * (q2 - r2).
  have ecnd : (left_pt (low c)).1 != (right_pt (low c)).1.
    by apply/eqP=> abs; have := edge_cond (low c); rewrite abs lt_irreflexive.
  have := vert_projr (last dummy_pt (left_pts c)) ecnd.
  move: lonl=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_lt0.
apply: (le_lt_trans vtople).
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma on_vert_edge_under_high_right v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_right c ->
  p <<< high c.
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] := right_vertical_edge_wrt_high llr cok vin.
move: (cok); rewrite /closed_cell_side_limit_ok.
rewrite 4!andbA=> /andP[] _.
move=> /andP[] rightn0 /andP[] samexr /andP[] sortr /andP[] _ ronh.
rewrite /point_strictly_under_edge.
set l := (p.1 - (left_pt (high c)).1) / ((right_pt (high c)).1 - (left_pt (high c)).1).
set q := ((left_pt (high c)).1 + l * ((right_pt (high c)).1 - (left_pt (high c)).1),
        (left_pt (high c)).1 + l * ((right_pt (high c)).2 - (left_pt (high c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (high c)) => [q1 q2].
case rq : (right_pt (high c)) => [r1 r2].
have lv : l = (p1 - q1) / (r1 - q1) by rewrite /l pq rq lq /=.
have q1ltp1 : q1 < p1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (high c)); rewrite lq rq.
rewrite det_inverse det_cyclique oppr_lt0.
rewrite -(pmulr_rgt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = q1 + l * (r1 - q1).
  rewrite lv mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (high c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite pmulr_lgt0; last by rewrite subr_gt0.
have proj2: (last dummy_pt (right_pts c)).2 = q2 + (p1 - q1) / (r1 - q1) * (r2 - q2).
  have ecnd : (left_pt (high c)).1 != (right_pt (high c)).1.
    by apply/eqP=> abs; have := edge_cond (high c); rewrite abs lt_irreflexive.
  have := vert_projl (last dummy_pt (right_pts c)) ecnd.
  move: ronh=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_gt0.
apply: lt_le_trans vtople.
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma on_vert_edge_above_low_right v c p :
  left_limit c < right_limit c ->
  closed_cell_side_limit_ok c ->
  on_vert_edge p v ->
  v \in cell_safe_exits_right c ->
  ~~ (p <<= low c).
Proof.
move=> llr cok onv vin.
have /andP[/andP[vtople xcond] xcond2] := right_vertical_edge_wrt_low llr cok vin.
move: (cok); rewrite /closed_cell_side_limit_ok.
rewrite 4!andbA=> /andP[] _.
move=> /andP[] rightn0 /andP[] samexr /andP[] sortr /andP[] ronl _.
rewrite /point_under_edge -ltNge.
set l := (p.1 - (left_pt (low c)).1) / ((right_pt (low c)).1 - (left_pt (low c)).1).
set q := ((left_pt (low c)).1 + l * ((right_pt (low c)).1 - (left_pt (low c)).1),
        (left_pt (low c)).1 + l * ((right_pt (low c)).2 - (left_pt (low c)).2)).
case pq : p => [p1 p2].
case lq : (left_pt (low c)) => [q1 q2].
case rq : (right_pt (low c)) => [r1 r2].
have lv : l = (p1 - q1) / (r1 - q1) by rewrite /l pq rq lq /=.
have q1ltp1 : q1 < p1.
  move: onv xcond => /andP[] /eqP + _.
  by rewrite lq rq pq /= => -> => /andP[].
have lgt0 : 0 < l.
  rewrite /l divr_gt0 // subr_gt0 ?pq ?lq ?rq //=.
  by move: (edge_cond (low c)); rewrite lq rq.
rewrite det_inverse det_cyclique oppr_gt0.
rewrite -(pmulr_rlt0 _ lgt0).
rewrite detDM1 det_cyclique.
have <- : p1 = q1 + l * (r1 - q1).
  rewrite lv mulfVK; first by ring.
  rewrite subr_eq0; apply/eqP=> abs.
  by have := edge_cond (low c); rewrite lq rq abs lt_irreflexive.
rewrite detVert lv.
rewrite pmulr_llt0; last by rewrite subr_gt0.
have proj2: (head dummy_pt (right_pts c)).2 = q2 + (p1 - q1) / (r1 - q1) * (r2 - q2).
  have ecnd : (left_pt (low c)).1 != (right_pt (low c)).1.
    by apply/eqP=> abs; have := edge_cond (low c); rewrite abs lt_irreflexive.
  have := vert_projl (head dummy_pt (right_pts c)) ecnd.
  move: ronl=> /andP[] _ -> => /esym /eqP; rewrite ?pq ?lq ?rq /= => ->.
  rewrite -(eqP xcond2); move: onv=>/andP[] /eqP <- _; rewrite pq /=; ring.
rewrite -proj2 subr_lt0.
apply: (le_lt_trans vtople).
by move: onv=> /andP[] _ /andP[]; rewrite pq /=.
Qed.

Lemma safe_bezier2 p1 p2 p3 c1 c2 vert_e u :
  closed_cell_side_limit_ok c1 ->
  closed_cell_side_limit_ok c2 ->
  strict_inside_closed p1 c1 ->
  strict_inside_closed p3 c2 ->
  vert_e \in cell_safe_exits_right c1 ->
  vert_e \in cell_safe_exits_left c2 ->
  on_vert_edge p2 vert_e ->
  0 < u < 1 ->
  on_vert_edge (bezier [fun  n => p1 with 1%N |-> p2, 2%N |-> p3] 2 u) vert_e ->
  forall t, 0 <= t <= 1 ->
    let bzt := bezier [fun  n => p1 with 1%N |-> p2, 2%N |-> p3] 2 t in
    (strict_inside_closed bzt c1) ||
    (strict_inside_closed bzt c2) ||
    on_vert_edge bzt vert_e.
Proof.
move=> ok1 ok2 p1in p3in v1 v2 p2in uin bzuin t tin.
have un0 : u != 0 by apply: lt0r_neq0; case/andP: uin.
set bzt := bezier _ 2 t; lazy zeta.
have [tu | nut] := eqVneq t u; first by rewrite /bzt tu bzuin !orbT.
have llr1 : left_limit c1 < right_limit c1.
  by move: p1in=> /andP[] _ /andP[]; apply: lt_trans.
have llr2 : left_limit c2 < right_limit c2.
  by move: p3in=> /andP[] _ /andP[]; apply: lt_trans.
have p2belh1 : p2 <<< high c1.
  by apply: (on_vert_edge_under_high_right _ ok1 p2in v1).
have p2abol1 : ~~(p2 <<= low c1).
  by apply: (on_vert_edge_above_low_right _ ok1 p2in v1).
have bzubelh1 : bezier [fun n => p1 with 1%N |-> p2, 2%N |-> p3] 2 u <<< high c1.
  by apply: (on_vert_edge_under_high_right _ ok1 bzuin v1).
have bzuabol1 : ~~(bezier [fun n => p1 with 1%N |-> p2, 2%N |-> p3] 2 u <<= low c1).
  by apply: (on_vert_edge_above_low_right _ ok1 bzuin v1).
have [P1 | P2] := ltrP t u.
   apply/orP; left; apply/orP; left.

  rewrite /point_strictly_under_edge.

  have -> : det p2 (left_pt (high c1)) (right_pt (high c1)) =
         det p2 (left_pt (high c1)) (last dummy_pt (right_pts c1)) *
           ((right_pt (high c1)).1 - (left_pt (high c1)).1) / 
           (right_limit c1 - (left_pt (high c1)).1).
    rewrite develop_det.
    rewrite /right_limit /det /get_coord.


have [tltu | tgtu'] := boolP(t < u).
  suff: strict_inside_closed bzt c1 by move=> ->.
  set t' := t / u.
  have tt' : t = t' * u by rewrite /t' mulfVK.
  rewrite /bzt tt' bezier2_dichotomy_l.
  have [t0 | tn0] := eqVneq t' 0.
    by rewrite t0 /= subr0 !(scale0r, addr0, add0r, scale1r).
  
