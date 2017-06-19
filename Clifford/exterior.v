Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
From mathcomp
Require Import perm finset path fingroup.



(** **********************************************************************************
    *******************                                *******************************
    *******************    Beginning of exterior.v     *******************************
    ******************                                 *******************************
    **********************************************************************************
    **)




From mathcomp
Require Import aux.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

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
Admitted.


Locate nth.
 *)



Lemma delta_perm n (i k : n.-tuple T) (σ : 'S_n) : 
  uniq k -> perm_eq i k -> delta [tuple (tnth i (σ x)) | x < n ] k = (-1)^+ σ * delta i k.
Proof.
Admitted.

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

Section Exterior.


Lemma submx_add_cap (F : fieldType) (m1 m2 m3 n : nat)
   (A : 'M[F]_(m1, n)) (B : 'M_(m2, n)) (C : 'M_(m3, n)) :
  (A :&: B + A :&: C <= A :&: (B + C))%MS.
Proof.
apply/rV_subP => x /sub_addsmxP [[u v] /= ->]; rewrite sub_capmx.
by rewrite addmx_sub_adds ?addmx_sub ?mulmx_sub ?capmxSl ?capmxSr.
Qed.


Lemma submx_sum_cap (F : fieldType) (k m1 n : nat)
   (A : 'M[F]_(m1, n)) (B_ : 'I_k -> 'M_n) :
   (\sum_i (A :&: B_ i) <= A :&: \sum_i B_ i)%MS.
Proof.
elim/big_ind2: _; rewrite ?capmx0 => //=.
by move=> ???? /addsmxS H /H /submx_trans -> //; apply: submx_add_cap.
Qed. 

Variable (F : fieldType) (n : nat).

Let dim := #|{set 'I_n}|.



Definition exterior := 'rV[F]_dim.
Canonical exterior_eqType := [eqType of exterior].
Canonical exterior_choiceType := [choiceType of exterior].
Canonical exterior_zmodType := [zmodType of exterior].





Definition exterior_enum (s : {set 'I_n}) : seq 'I_n :=
  sort (fun i j : 'I_n => (i <= j)%N) (enum s).



Definition sign (A B : {set 'I_n}) : F :=
  delta F (exterior_enum A ++ exterior_enum B) (exterior_enum (A :|: B)).

Locate disjoint.
Lemma signND (A B : {set 'I_n}) : ~~ [disjoint A & B] -> sign A B = 0.
Proof.
Admitted.

Locate ":|:".



(** basis vector *)
Definition blade A : exterior := (delta_mx 0 (enum_rank A)).


Definition mul_ext (u v : exterior) : exterior :=
  \sum_(su : {set 'I_n})
   \sum_(sv : {set 'I_n})
   (u 0 (enum_rank su) * v 0 (enum_rank sv) * sign su sv) *: blade (su :|: sv).



Local Notation "*w%F" := (@mul_ext _).
Local Notation "u *w w" := (mul_ext u w) (at level 40).

Definition extn r : 'M[F]_dim :=
 (\sum_(s : {set 'I_n} | #|s| == r) <<blade s>>)%MS.

Lemma dim_extn r : \rank (extn r) = 'C(n, r).
Proof.
rewrite (mxdirectP _) /=; last first.
  by rewrite mxdirect_delta // => i ???; apply: enum_rank_inj.
rewrite (eq_bigr (fun=> 1%N)); last first.
  by move=> s _; rewrite mxrank_gen mxrank_delta.
by rewrite sum1dep_card card_draws card_ord.
Qed.

Lemma dim_exterior : \rank (1%:M : 'M[F]_dim) = (2 ^ n)%N.
Proof.
rewrite mxrank1 /dim (@eq_card _ _ (mem (powerset [set: 'I_n]))); last first.
  by move=> A; rewrite !inE subsetT.
by rewrite card_powerset cardsT card_ord.
Qed.



Lemma mxdirect_extn : mxdirect (\sum_(i < n.+1) extn i).
Proof.
have card_small (A : {set 'I_n}) : (#|A| < n.+1)%N.
  by rewrite ltnS (leq_trans (max_card _)) ?card_ord.
apply/mxdirectP=> /=; rewrite -(@partition_big _ _ _ _ _ xpredT 
          (fun A => Ordinal (card_small A)) xpredT) //=.
rewrite (mxdirectP _) ?mxdirect_delta //=; last by move=> ????/enum_rank_inj.
by rewrite (@partition_big _ _ _ _ _ xpredT 
          (fun A => Ordinal (card_small A)) xpredT) //=.
Qed.




Lemma extnn : (\sum_(i < n.+1) extn i :=: 1%:M)%MS.
Proof.
apply/eqmxP; rewrite -mxrank_leqif_eq ?submx1 // dim_exterior /extn.
rewrite (expnDn 1 1) (mxdirectP _) /=; last exact mxdirect_extn.
apply/eqP/eq_bigr => i _; rewrite (eq_bigr (fun=> 1%N)); last first.
  by move=> A _; rewrite mxrank_gen mxrank_delta.
by rewrite sum1dep_card /= card_draws card_ord !exp1n !muln1.
Qed.

(* Lemma mul_extnV (u v : exterior) r s : (u <= extn r)%MS -> (v <= extn s)%MS -> *)
(*   (u *w v)  = 0. *)


Lemma mul_extE (u v : exterior) (A : {set 'I_n}) :
  (u *w v) 0 (enum_rank A) = 
  \sum_(s in powerset A)
   (u 0 (enum_rank s) * v 0 (enum_rank (A :\: s)) * sign s (A :\: s)).
Proof.
have bm := (@big_morph _ _ (fun M : 'M__ => M 0 _) 0 +%R); move=> [:mid mop].
rewrite [LHS]bm; last first.
- by abstract: mid; rewrite mxE.
- by abstract: mop; move=> ??; rewrite mxE.
rewrite (bigID (mem (powerset A))) /= [X in _ + X]big1 ?addr0 /=; last first.
  move=> su; rewrite inE => NsuA.
  rewrite bm ?big1 => // sv _; rewrite !mxE /= [_ == _]negbTE ?mulr0 //.
  by apply: contraNneq NsuA => /enum_rank_inj ->; rewrite subsetUl.
apply: eq_bigr => su suA; rewrite bm // (bigD1 (A :\: su)) //= big1 ?addr0.
  rewrite setDE setUIr -setDE setUCr setIT (setUidPr _) -?powersetE //.
  by rewrite !mxE ?eqxx ?mulr1.
move=> sv svNADsu; rewrite !mxE /=.
have [duv|Nduv]:= boolP [disjoint su & sv]; last first.
  by rewrite signND ?(mulr0,mul0r).
rewrite [_ == _]negbTE ?mulr0 //.
apply: contraNneq svNADsu => /enum_rank_inj ->.
by rewrite setDUl setDv set0U (setDidPl _) // disjoint_sym.
Qed.

Definition id_ext : exterior := blade set0. 

Delimit Scope ext_scope with ext.
Local Open Scope ext_scope.
Local Notation "\prod_ ( i | P ) B" :=
  (\big[mul_ext/id_ext]_(i | P) B%ext) : ext_scope.
Local Notation "\prod_ ( i < n | P ) B" :=
  (\big[mul_ext/id_ext]_(i < n | P) B%ext) : ext_scope.
Local Notation "\prod_ ( i <- r | P ) B" :=
  (\big[mul_ext/id_ext]_(i <- r | P) B%ext) : ext_scope.
Local Notation "\prod_ i B" :=
  (\big[mul_ext/id_ext]_i B%ext) : ext_scope.
Local Notation "\prod_ ( i < n ) B" :=
  (\big[mul_ext/id_ext]_(i < n) B%ext) : ext_scope.
Local Notation "\prod_ ( i <- r ) B" :=
  (\big[mul_ext/id_ext]_(i <- r) B%ext) : ext_scope.

Definition to_ext (x : 'rV_n) : exterior := 
  \sum_(i : 'I_n) (x 0 i) *: blade [set i].

(* Lemma to_ext1 (u : 'rV_n) : (to_ext u <= extn 1%N)%MS. *)

Definition form_of r := 'M[F]_(r,n) -> F.



Notation "r .-form" := (form_of r)
  (at level 2, format "r .-form") : type_scope.


(* ~ scalar product *)
Definition form_of_ext r (u : exterior) : r.-form := fun v =>
  \sum_(s : {set 'I_n} | #|s| == r)
     u 0 (enum_rank s) * (\prod_i to_ext (row i v))%ext 0 (enum_rank s).

Locate to_ext.
About to_ext.


Locate prod_i.


Definition mul_form r s (a : r.-form) (b : s.-form) : (r + s).-form := 
  fun v => ((r + s)`!)%:R^-1 * \sum_(sigma : 'S_(r + s))
            (- 1) ^ sigma *
                    a (\matrix_(i < r) row (sigma (unsplit (inl i))) v) * 
                    b (\matrix_(i < s) row (sigma (unsplit (inr i))) v).

(*Definition exterior_enum (s : {set 'I_n}) : seq 'I_n :=
  sort (fun i j : 'I_n => i <= j) (enum s).*)

(* Definition size_exterior_enum r (s : {set 'I_n}) : #|s| = r -> size (exterior_enum s) == r. *)
(* Proof. Admitted. *)

(* Definition canon_tuple (s : {set 'I_n}) := Tuple (size_exterior_enum s). *)

Definition ext_of_form r (f : r.-form) : exterior :=
  \sum_(s : {set 'I_n} | #|s| == r)
   f (\matrix_(i < r) nth 0 [seq delta_mx 0 i | i <- exterior_enum s] i) *: blade s.

(* Lemma mul_extDr :  (u v : exterior) (A : {set 'I_n}) : *)

Definition multilinear r (f : r.-form) := 
   forall (A B C : 'M_(r,n)) (i0 : 'I_r) (b c : F),
   row i0 A = b *: row i0 B + c *: row i0 C ->
   row' i0 B = row' i0 A ->
   row' i0 C = row' i0 A -> f A = b * f B + c * f C.

Definition alternate r (f : r.-form) := 
  forall (A : 'M_(r, n)) (i1 i2 : 'I_r), i1 != i2 -> A i1 =1 A i2 -> f A = 0.

Definition multilinear_alternate r (f : r.-form) :=
  multilinear f /\ alternate f.

Lemma ext_of_formK r (f : r.-form) : multilinear_alternate f -> 
  form_of_ext (ext_of_form f) =1 f.
Proof.
move=> f_ma v.
rewrite /form_of_ext /ext_of_form /=.
Abort.

Lemma form_of_multilinear_alternate r (x : exterior) :
  multilinear_alternate (form_of_ext x : r.-form).
Proof.
(* easy *)
Abort.

Lemma mul_ext_form r s (f : r.-form) (g : s.-form) :
  multilinear_alternate f -> multilinear_alternate g -> 
  ext_of_form (mul_form f g) = (ext_of_form f) *w (ext_of_form g).
Proof.
Abort.

(* Definition split_form r (I : {set 'I_r}) (f : r.-form) *)
(*            (v : 'M_(r - #|I|,n)) : #|I|.-form := fun u => *)
(*   f (\matrix_k if k \in I then row k u else row k v). *)
  


(*   (if r isn't r'.+1 return 'I_r -> r.-form -> 'M_(r.-1,n) -> F *)
(*    then fun _ _ _ => 0 else fun k0 f v =>  *)
(*    f (\matrix_k if unlift k0 k is Some k' then row k' v else u)) *)
(*   k0 f v. *)


  

End Exterior.
