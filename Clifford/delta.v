Require Import mathcomp.ssreflect.ssreflect.
Require Import aux.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
From mathcomp
Require Import perm finset path fingroup.
From CoqEAL
Require Import minor.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.


Local Open Scope ring_scope.
Delimit Scope ext_scope with ext.
Local Open Scope ext_scope.
Section delta.

Import GroupScope.

Context {T : eqType}.

(* first tentative definition of the generalized kronecker symbol *)
(*Definition delta (i k : seq nat) : R :=
  if (perm_eq i (in_tuple k) =P true) isn't ReflectT ik then 0
  else let s := sval (sig_eqW (tuple_perm_eqP ik)) in (-1) ^+ s *+ uniq i.

Lemma deltaC i k : delta i k = delta k i.
Proof.
have [pik|pik] := boolP (perm_eq i k); last first.
  rewrite /delta.
  case: eqP => p; first by rewrite p in pik.
  case: eqP => p0 //; by rewrite perm_eq_sym p0 in pik.
move: (pik); rewrite -[ i]/(val (in_tuple i)) -[k]/(val (in_tuple k)).
move: (in_tuple _) (in_tuple _); rewrite (perm_eq_size pik).
move: (size k) => m {i k pik} i k.
rewrite /delta.
rewrite !tvalK.
case: _ / (esym (size_tuple k)); case: _ / (esym (size_tuple i)) => /=.
  case: eqP => // p.
  case: eqP => // [p' pik|]; last by rewrite {1}perm_eq_sym.
case: sig_eqW => /= s k_eq.
case: sig_eqW => /= s' i_eq.
rewrite -odd_permV.
rewrite (perm_eq_uniq p).
have [i_uniq|] := boolP (uniq (val i)); last by rewrite !mulr0n.
congr (_ ^+ _ *+ _).
congr (odd_perm _).
(* apply: (mulgI s); rewrite mulgV; symmetry. *)
apply/permP => /= j.
apply/val_inj/eqP=> /=.
rewrite -(@nth_uniq _ 0%N (val k)) //=.
Abort.
*)









Fact perm_of_2seq_key : unit. Proof. exact: tt. Qed.


Definition perm_of_2seq :=
  locked_with perm_of_2seq_key
  (fun (T : eqType) n (si so : n.-tuple T) =>
  if (perm_eq si so =P true) isn't ReflectT ik then (1%g)
  else sval (sig_eqW (tuple_perm_eqP ik))).



About sig_eqW.

Canonical perm_of_2seq_unlockable := [unlockable fun perm_of_2seq].


(*
Let _i := [:: 1%N; 2 ; 3].
Let _k := [:: 4; 5; 6].
Let _j := [:: 1%N; 2; 3].
Let _l := [:: 2; 1%N; 3].

Let _si := [tuple of _i].
Let _sk := [tuple of _k].
Let _sj := [tuple of _j].
Let _sl := [tuple of _l].

Eval compute in perm_eq _si _sk.
Eval compute in perm_eq _si _sj.
Eval compute in perm_eq _si _sl.


(* Eval compute in perm_of_2seq _si _sj. *)




Locate tnth.


*)


About tnth.



(** si = Input Sequence
    so = Output Sequence
    This lemma states that :
        if si = so modulo a permutation,
        if σ=(perm_of_2seq si so) then

                  the j   -th element of si
is exactly        the σ(j)-th element of so *)

Lemma perm_of_2seqE n (si so : n.-tuple T) (j : 'I_n) :
  perm_eq si so -> tnth so (perm_of_2seq si so j) = tnth si j.
Proof.
rewrite [perm_of_2seq]unlock ; case: eqP => // H1 H2.
case: sig_eqW => /= s; rewrite /tnth => -> /=.
by rewrite (nth_map j) ?size_enum_ord // nth_ord_enum.
Qed.

(* Definition perm_of_2seq (T : eqType) n (si : seq T) (so : seq T) : 'S_n := *)
(*   if (size so == n) =P true isn't ReflectT so_n then 1%g *)
(*   else if (perm_eq si (Tuple so_n) =P true) isn't ReflectT ik then 1%g *)
(*   else sval (sig_eqW (tuple_perm_eqP ik)). *)

(* Lemma perm_of_2seqE n (T : eqType) (si so : n.-tuple T) (j : 'I_n) : *)
(*   perm_eq si so -> tnth so (perm_of_2seq n si so j) = tnth si j. *)
(* Proof. *)
(* rewrite /perm_of_2seq; case: eqP => // so_n p_si_so; last first. *)
(*   by rewrite size_tuple eqxx in so_n. *)
(* case: eqP => // ?; case: sig_eqW => /= s; rewrite /tnth => -> /=. *)
(* rewrite (nth_map j) ?size_enum_ord // nth_ord_enum /=. *)
(* by apply: set_nth_default; rewrite size_tuple. *)
(* Qed. *)




(** If si is injective (uniq si) ie, if it represents a permutation, then the inverse of
    (perm_of_2seq si so) is exactly (perm_of_2seq so si *)

Lemma perm_of_2seqV n (si so : n.-tuple T) : uniq si ->
  (perm_of_2seq si so)^-1%g = perm_of_2seq so si.
Proof.
move=> uniq_si.
apply/permP => /= j.
apply/val_inj/eqP => /=.
rewrite -(@nth_uniq _ (tnth_default si j) (val si)) //=; last 2 first.
- by rewrite size_tuple.
- by rewrite size_tuple.
rewrite [perm_of_2seq]unlock; case: eqP => p; last first.
  case: eqP => // p0; by [rewrite perm_eq_sym p0 in p | rewrite invg1].
  case: eqP => [p'|]; last first.
    by rewrite perm_eq_sym {1}p.
case: sig_eqW => /= x Hx; case: sig_eqW => /= y Hy.
rewrite {1}Hx (nth_map j); last by rewrite size_enum_ord.
rewrite nth_ord_enum permE f_iinv /tnth Hy (nth_map j); last by rewrite size_enum_ord.
rewrite nth_ord_enum /tnth; apply/eqP/set_nth_default;  by rewrite size_tuple.
Qed.

Variable R : ringType.
Local Open Scope ring_scope.

(*
Locate uniq.

Locate insubd.
Locate in_tuple.
 *)


(** Generalized Kronecker symbol :

I=(i_1, ..., i_n)
K=(k_1, ..., k_n)


δ^{I}_{K} = If I is injective and K = σ(I) then ε(σ) else 0.

Reference :  http://www.unige.ch/math/folks/ronga/lyse_II/2003-2004/chap_IV.pdf (def 1.5)
 *)

Definition delta (i k : seq T) : R :=
  if (perm_eq i k) && (uniq i) then
  (-1) ^+ perm_of_2seq (insubd (in_tuple k) i) (in_tuple k) else 0.

Locate in_tuple.


(*
About in_tuple.
About delta.
*)


Lemma deltaE n (i k : seq T) (si : size i = n) (sk : size k = n) :
  let T l (P : size l = n)  := Tuple (appP eqP idP P) in
  delta i k = if (perm_eq i k) && (uniq i)
              then (-1) ^+ perm_of_2seq (T _ si) (T _ sk) else 0.
Proof.
move=> mkT; rewrite /delta; have [/andP [pik i_uniq]|//] := ifP.
set i' := insubd _ _; set k' := in_tuple _.
have [] : (i' = mkT _ si :> seq _ /\ k' = mkT _ sk :> seq _).
  by rewrite /= val_insubd /= (perm_eq_size pik) eqxx.
move: i' k' (mkT i si) (mkT k sk) => /=.
by case: _ / sk => ??????; congr (_ ^+ perm_of_2seq _ _); apply: val_inj.
Qed.

(* Definition deltaE n (i k : seq nat) (si : size i == n) (sk : size k == n) := *)
(*   deltaE (Tuple si) (Tuple sk). *)

(* Lemma delta_cast n (i k : seq nat) (ni : size i = n) (nk : size k = n) : *)
(*   delta i k = delta (Tuple (appP eqP idP ni)) (Tuple (appP eqP idP nk)). *)




Lemma delta_0 (i : seq T) k : (~~ uniq i) || (~~ uniq k) -> delta i k = 0.
Proof.
case/orP => [Nui|Nuk]; rewrite /delta; case: ifP => // /andP[pik ui].
  by rewrite (negbTE Nui) in ui.
by rewrite -(perm_eq_uniq pik) ui in Nuk.
Qed.


(* Definition scast {m n : nat} (eq_mn : m = n) (s : 'S_m) : 'S_n := *)
(*   ecast n ('S_n) eq_mn s. *)

(* Lemma tcastE (m n : nat) (eq_mn : m = n) (t : 'S_m) (i : 'I_n), *)
(*    tnth (tcast eq_mn t) i = tnth t (cast_ord (esym eq_mn) i) *)
(* tcast_id *)
(*    forall (T : Type) (n : nat) (eq_nn : n = n) (t : n.-tuple T), *)
(*    tcast eq_nn t = t *)
(* tcastK *)
(*    forall (T : Type) (m n : nat) (eq_mn : m = n), *)
(*    cancel (tcast eq_mn) (tcast (esym eq_mn)) *)
(* tcastKV *)
(*    forall (T : Type) (m n : nat) (eq_mn : m = n), *)
(*    cancel (tcast (esym eq_mn)) (tcast eq_mn) *)
(* tcast_trans *)
(*    forall (T : Type) (m n p : nat) (eq_mn : m = n)  *)
(*      (eq_np : n = p) (t : m.-tuple T), *)
(*    tcast (etrans eq_mn eq_np) t = tcast eq_np (tcast eq_mn t) *)
(* L *)

(* Lemma perm_of_2seq_tcast (T : eqType) n m i (k : m.-tuple T) (eq_mn : m = n): *)
(*   perm_of_2seq i (tcast eq_mn k) = scast eq_mn (perm_of_2seq i k). *)


Lemma perm_of_2seq_ii n (i : n.-tuple T) : uniq i ->
  perm_of_2seq i i = (1%g).
Proof.
move=> ?; apply/permP => /= j; apply/val_inj/eqP => /=.
by rewrite permE -(@nth_uniq _ (tnth_default i j) i) ?size_tuple // -tnth_nth
   perm_of_2seqE.
Qed.





Lemma deltaii (i : seq T) : uniq i -> delta i i = 1.
Proof.
move=> i_uniq; rewrite !(@deltaE (size i)) .
by rewrite perm_eq_refl i_uniq /= perm_of_2seq_ii // odd_perm1.
Qed.



Lemma deltaC (i k : seq T) : delta i k = delta k i.
Proof.
have [pik|pik] := boolP (perm_eq i k); last first.
  by rewrite /delta (negPf pik) perm_eq_sym (negPf pik).
have [uk|Nuk] := boolP (uniq k); last by rewrite !delta_0 // Nuk ?orbT.
have si := (perm_eq_size pik); rewrite !(@deltaE (size k)) //.
rewrite pik /= perm_eq_sym pik (perm_eq_uniq pik) uk /=.
by rewrite -perm_of_2seqV // odd_permV.
Qed.

(* Lemma deltaN1 (i : seq nat) k : uniq i -> *)
(*   perm_of_2seq i (in_tuple k) -> delta i k = -1. *)
(* Proof. *)
(* move=> ui; rewrite /delta /perm_of_2seq ui. *)
(* case: eqP => [p|]; last by rewrite odd_perm1. *)
(* case: sig_eqW => /= x ih Hx; by rewrite p Hx expr1. *)
(* Qed. *)

(* Lemma delta_1 (i : seq nat) k : uniq i -> perm_eq i k ->  *)
(*  ~~ perm_of_2seq i (in_tuple k) -> delta i k = 1. *)
(* Proof. *)
(* move=> ui ik. *)
(* rewrite /delta /perm_of_2seq ui. *)
(* case: eqP => [p|]. *)
(*   case: sig_eqW => /= x ih Hx. *)
(*   by rewrite p (negPf Hx) expr0. *)
(* by rewrite ik. *)
(* Qed. *)


(** Composition *)


Lemma perm_of_2seq_comp n (s1 s2 s3 : n.-tuple T) :
  uniq s3 -> perm_eq s1 s2 -> perm_eq s2 s3 ->
  (perm_of_2seq s1 s2 * perm_of_2seq s2 s3)%g = perm_of_2seq s1 s3.
Proof.
move=> us3 s12 s23; have s13 := perm_eq_trans s12 s23.
apply/permP => /= i; rewrite permE /=; apply/val_inj/eqP => /=.
rewrite -(@nth_uniq _ (tnth_default s1 i) s3) ?size_tuple // -!tnth_nth.
by rewrite !perm_of_2seqE.
Qed.


Lemma delta_comp (i j k : seq T) :
  uniq k -> perm_eq i j -> perm_eq j k ->
  delta i k = delta i j * delta j k.
Proof.
move=> uk pij pjk; have pik := perm_eq_trans pij pjk.
have [sj si] := (perm_eq_size pjk, perm_eq_size pik).
rewrite !(@deltaE (size k)) pik pij pjk /=.
rewrite (perm_eq_uniq pij) (perm_eq_uniq pjk) uk.
by  rewrite -signr_addb -odd_permM perm_of_2seq_comp.
Qed.


Lemma perm_of_2seq_perm n (s : n.-tuple T) (σ : 'S_n) :
  uniq s ->
  perm_of_2seq [tuple (tnth s (σ x)) | x < n] s = σ.
Proof.
move=> us; apply/permP => //= i; apply/val_inj/eqP.
rewrite -(nth_uniq (tnth_default s i) _ _ us) ?size_tuple //=.
rewrite -!tnth_nth perm_of_2seqE ?tnth_mktuple //.
by apply/tuple_perm_eqP; exists σ.
Qed.

(*
  rewrite tnth_mktuple.
  Locate "tuple".
  rewrite tupleE.
  *)

Lemma perm_of_2seq_perm2 n (s1 s2 : n.-tuple T) (s : 'S_n) :
  uniq s2 -> perm_eq s1 s2 ->
  perm_of_2seq s1 s2 = (s^-1 * perm_of_2seq [tuple (tnth s1 (s x)) | x < n] s2)%g.
Proof.
move=> us2 s12; rewrite -[in RHS](@perm_of_2seq_comp _ _ s1) //; last first.
  by apply/tuple_perm_eqP; exists s.
by rewrite ?perm_of_2seq_perm ?mulKg ?(perm_eq_uniq s12).
Qed.

(*
apply/permP => /= j.
rewrite [perm_of_2seq]unlock.
case: eqP => // p.
case: eqP => // p0; last first.
have : perm_eq [tuple tnth s1 (s x) | x < n] s1.
  by apply /tuple_perm_eqP; exists s.
  move : p0 p.
  set σ := [tuple tnth s1 (s x) | x < n].
  move => p0 p.
  rewrite perm_eq_sym.
  Check perm_eq s1 σ.
(*  apply /eqP. *)
  move : s12.
  About perm_eq_trans.
  (* Idea :
perm_eq s1 s2 -> perm_eq s1 σ -> perm_eq σ s2.
Yet, p0 states ~~ (perm_eq σ s2). So false -> anything. *)
    by admit.
  (* Quantification ??! *)
   (* rewrite perm_eq_sym p12.
  About perm_eq_trans. *)

  (* by admit. *)
    case: sig_eqW => /= σ1 H1.
    case: sig_eqW => /= σ2 H2.
    (* H1 :    s1    = (σ1 * s2)%g
       H2 : (s*s1)%g = (σ2 * s2)%g
Goal : σ1 j = (s^-1*σ2)%g j

Because (uniq s2), this is equivalent to (using associativity) :
       (σ1*s2)%g j = (s^-1 * (σ2 * s2)%g)%g j

Rewrite H1, H2 :
        s1 j = (s^-1 * (s*s1)%g)%g j

Using associativity + cancel inverse (~ invK) :
        s1 j = s1 j

Which is true *)

    rewrite permM.

    Print perm_invP.
Admitted


Locate nth.
 *)



Lemma delta_perm n (i k : n.-tuple T) (σ : 'S_n) :
  uniq k -> perm_eq i k -> delta [tuple (tnth i (σ x)) | x < n ] k = (-1)^+ σ * delta i k.
Proof.


move => uk pik.
set τ := [tuple tnth i (σ x) | x < n].
have pτi : perm_eq τ i by apply /tuple_perm_eqP; exists σ.
have pτk : perm_eq τ k by rewrite (perm_eq_trans pτi pik).
have ui : uniq i by rewrite (perm_eq_uniq pik).
have uτ : uniq τ by rewrite (perm_eq_uniq pτk).
have sτk : size τ = size k by rewrite !size_tuple.
have sik : size i = size k by rewrite !size_tuple.
have sτi : size τ = size i by rewrite !size_tuple.
have στi : σ = perm_of_2seq τ i by rewrite perm_of_2seq_perm.
rewrite (@delta_comp τ i k uk pτi pik).
congr ( _ * _).
(* rewrite στi. *)

(* rewrite deltaC.*)
rewrite /delta pτi uτ //=.
(* rewrite στi. *)
rewrite in_tupleE.
Admitted.


(*
rewrite (@deltaE (size i)).
rewrite pτi uτ //=.
by [].

rewrite στi.
rewrite !(@deltaE (size k)).
rewrite pτk uτ pik ui //=.
rewrite -signr_addb.

About odd_permM.
About appP.

 rewrite -odd_permM.
rewrite perm_of_2seq_perm.
rewrite -[in RHS]odd_permM. perm_of_2seq_comp.
  About tuple_perm_eqP. *)


(*
move => uk pik.
have sin : size i = n.
 - by rewrite (perm_eq_size pik) (size_tuple).
(* set t := [tuple _ | _ < _]. *)
(* rewrite /delta.
apply /tuple_perm_eqP.*)
have ui : uniq i by rewrite (perm_eq_uniq pik).
have uniq_shuffle : uniq [tuple tnth i (σ x)  | x < n] = uniq i.
   - rewrite -(@perm_uniq _  [tuple tnth i (σ x)  | x < n] _) //.
rewrite !(@deltaE (size k)) ?size_tuple //.
move => Hyp0 Hyp1.
rewrite (@perm_eq_trans _ i).
rewrite !ui pik.
Search _ "uniq" "tuple".
apply /tuple_perm_eqP.
*)


(*
Lemma delta_perm n (i k : seq T) (x0 : T) (s : 'S_n) : size k = n ->
  uniq k -> perm_eq i k ->
  delta i k = (- 1) ^+ s * delta [tuple (nth x0 i (s x)) | x < n] k.
Proof.
move=> kn uk pik.
have sin : size i = n by rewrite (perm_eq_size pik).
have ? : size [tuple nth x0 i (s x)  | x < n] = n by rewrite size_tuple.
have ui : uniq i by rewrite (perm_eq_uniq pik).
rewrite !(@deltaE n) pik ui //=.
Search _ "tuple" "map".
(*
rewrite tnth_mktuple.
rewrite -[in RHS](tnth_nth).
apply /tuple_perm_eqP.
(* set t := [tuple _ |  _ < _]. *)
Search _ "tuple" "perm_eqP".
Search _ "tuple" "seq".
Search _ "nth" "uniq".
Locate uniq_perm_eq.
Locate tuple_perm_eqP.


Check [seq nth x0 i (s x) | x <- enum 'I_n].
Check [tuple tnth  i (s x) | x < n].
*)
case: ifP; last first.

move => /nandP /orP.
case /orP => [Npik|Nu].

case/andP => H1 H2.
rewrite -signr_addb.
congr (_ ^+ _).
rewrite (perm_of_2seq_perm s) //.
rewrite -odd_permV.
Abort.
*)



(* Need for distributivity *)
(** Scheme of a proof :

j ++ i = [tuple (tnth (i++j) (σ x)) | x < n]. Not really easy to compute such a permutation σ though,
maybe using perm_of_2seq cleverly, but it is easy to compute it step by step :

i2 .... ir j1 .... js i1 = i ∘ (1 2 .... r r+1 ... r+s) the (r+s)-cycle whose signature is (-1)^(r+s-1), and one just has to compute it r times to have j ++ i.

Then, using delta_perm :

delta (i ++ j) k = (-1) ^+ (size i + size j - 1) * delta ( i2 ... ir j1 ... js i1) k
                 = ( (-1) ^+ (size i + size j - 1) ) ^+ (size i) delta (j ++ i) k
                 = (-1) ^+ (size i * size j) * (-1) ^+ (size i * (size i - 1)) * delta (j ++ i ) k
                 = (-1) ^+ (size i * size j) * delta (j ++ i) k

because r*(r-1) is even. Qed.


Maybe we will write lemmas to do so. *)

Lemma delta_catC (i j k : seq T) :
  uniq k -> perm_eq (i ++ j) k ->
  delta (i ++ j) k = (- 1) ^+ (size i * size j) * delta (j ++ i) k.
Proof.
Admitted.


End delta.

Section Sorted_enum.


Variable (n' : nat).
Let n := n'.+1.

Definition sorted_enum (s : {set 'I_n}) : seq 'I_n :=
  sort (fun i j : 'I_n => (i <= j)%N) (enum s).

Lemma sorted_enum_set0 : sorted_enum set0 = [::] :> seq 'I_n.
Proof.
  by rewrite /sorted_enum enum_set0.
Qed.


Lemma sorted_enum_uniq (S : {set 'I_n}) : uniq (sorted_enum S).
Proof. by rewrite /sorted_enum sort_uniq enum_uniq. Qed.


End Sorted_enum.



Section Sign_Delta.


Variable (F : comRingType).
Variable (n' : nat).
Let n := n'.+1.




Definition sign_delta (A B : {set 'I_n}) : F :=
  delta F (sorted_enum A ++ sorted_enum B) (sorted_enum (A :|: B)).



Lemma sign_delta0S1 (S : {set 'I_n}) : sign_delta set0 S = 1.
Proof.
rewrite /sign_delta set0U sorted_enum_set0 cat0s.
by rewrite deltaii ?sorted_enum_uniq.
Qed.



Lemma sign_deltaS01 (S : {set 'I_n}) : sign_delta S set0 = 1.
Proof.
rewrite /sign_delta setU0 sorted_enum_set0 cats0.
by rewrite deltaii ?sorted_enum_uniq.
Qed.


(** Idea : ~~[disjoint A & B] = ~~ (uniq ( sorted_enum A ++ sorted_enum B ) ) *)



Lemma disjoint_seq (A B : {set 'I_n}) :
  [disjoint A & B] = [disjoint (sorted_enum A) & (sorted_enum B)].
Proof.
rewrite !disjoint_subset; apply/subsetP/subsetP => AB x;
by have := AB x; rewrite !inE !mem_sort !mem_enum; apply.
Qed.


Lemma sorted_enum_disjoint (A B : {set 'I_n}) :
    [disjoint A & B] = uniq ( sorted_enum A ++ sorted_enum B).
Proof.
rewrite disjoint_sym cat_uniq !sorted_enum_uniq andbT //=.
by rewrite disjoint_seq disjoint_has. Qed.



Lemma sign_deltaND (A B : {set 'I_n}) : ~~ [disjoint A & B] -> sign_delta A B = 0.
Proof.
rewrite sorted_enum_disjoint => ND.
by rewrite /sign_delta delta_0 //= ND.
Qed.


Lemma sign_deltaDl (R S T : {set 'I_n}) : [disjoint R & S] ->
 sign_delta (R :|: S) T = sign_delta R T * sign_delta S T.
Proof.
move => dRS; rewrite /sign_delta.
Admitted.


Lemma sign_deltaii (i : 'I_n) : sign_delta [set i] [set i] = 0.
Proof.
by rewrite sign_deltaND //= -setI_eq0 setIid; apply /set0Pn; exists i; rewrite set11.
Qed.


Lemma sign_delta_single (i j : 'I_n) : sign_delta [set j] [set i] = - sign_delta [set i] [set j].
Proof.
have [->| neq_ij] := eqVneq i j; first by rewrite sign_deltaii oppr0.
rewrite /sign_delta /sorted_enum !enum_set1 setUC.
rewrite delta_catC.
- by rewrite !size_sort muln1 expr1 mulN1r.
- by rewrite sort_uniq enum_uniq.
rewrite -![sort _ [::_]]/[:: _] perm_eq_sym perm_sort.
rewrite uniq_perm_eq ?enum_uniq //= ?inE 1?eq_sym ?neq_ij //.
by move=> x; rewrite !mem_enum !inE orbC.
Qed.

