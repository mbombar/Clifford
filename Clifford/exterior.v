Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
From mathcomp
Require Import perm finset path fingroup ssrnum.
From CoqEAL
Require Import minor.
From mathcomp
Require Import complex.


Require Import aux.


(** **********************************************************************************
    *******************                                *******************************
    *******************    Beginning of exterior.v     *******************************
    ******************                                 *******************************
    **********************************************************************************
    **)







Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.
Delimit Scope ext_scope with ext.
Local Open Scope ext_scope.
(* Section delta. *)

(* Import GroupScope. *)

(* Context {T : eqType}. *)

(* (* first tentative definition of the generalized kronecker symbol *) *)
(* (*Definition delta (i k : seq nat) : R := *)
(*   if (perm_eq i (in_tuple k) =P true) isn't ReflectT ik then 0 *)
(*   else let s := sval (sig_eqW (tuple_perm_eqP ik)) in (-1) ^+ s *+ uniq i. *)

(* Lemma deltaC i k : delta i k = delta k i. *)
(* Proof. *)
(* have [pik|pik] := boolP (perm_eq i k); last first. *)
(*   rewrite /delta. *)
(*   case: eqP => p; first by rewrite p in pik. *)
(*   case: eqP => p0 //; by rewrite perm_eq_sym p0 in pik. *)
(* move: (pik); rewrite -[ i]/(val (in_tuple i)) -[k]/(val (in_tuple k)). *)
(* move: (in_tuple _) (in_tuple _); rewrite (perm_eq_size pik). *)
(* move: (size k) => m {i k pik} i k. *)
(* rewrite /delta. *)
(* rewrite !tvalK. *)
(* case: _ / (esym (size_tuple k)); case: _ / (esym (size_tuple i)) => /=. *)
(*   case: eqP => // p. *)
(*   case: eqP => // [p' pik|]; last by rewrite {1}perm_eq_sym. *)
(* case: sig_eqW => /= s k_eq. *)
(* case: sig_eqW => /= s' i_eq. *)
(* rewrite -odd_permV. *)
(* rewrite (perm_eq_uniq p). *)
(* have [i_uniq|] := boolP (uniq (val i)); last by rewrite !mulr0n. *)
(* congr (_ ^+ _ *+ _). *)
(* congr (odd_perm _). *)
(* (* apply: (mulgI s); rewrite mulgV; symmetry. *) *)
(* apply/permP => /= j. *)
(* apply/val_inj/eqP=> /=. *)
(* rewrite -(@nth_uniq _ 0%N (val k)) //=. *)
(* Abort. *)
(* *) *)









(* Fact perm_of_2seq_key : unit. Proof. exact: tt. Qed. *)


(* Definition perm_of_2seq := *)
(*   locked_with perm_of_2seq_key *)
(*   (fun (T : eqType) n (si so : n.-tuple T) => *)
(*   if (perm_eq si so =P true) isn't ReflectT ik then (1%g) *)
(*   else sval (sig_eqW (tuple_perm_eqP ik))). *)



(* About sig_eqW. *)

(* Canonical perm_of_2seq_unlockable := [unlockable fun perm_of_2seq]. *)


(* (* *)
(* Let _i := [:: 1%N; 2 ; 3]. *)
(* Let _k := [:: 4; 5; 6]. *)
(* Let _j := [:: 1%N; 2; 3]. *)
(* Let _l := [:: 2; 1%N; 3]. *)

(* Let _si := [tuple of _i]. *)
(* Let _sk := [tuple of _k]. *)
(* Let _sj := [tuple of _j]. *)
(* Let _sl := [tuple of _l]. *)

(* Eval compute in perm_eq _si _sk. *)
(* Eval compute in perm_eq _si _sj. *)
(* Eval compute in perm_eq _si _sl. *)


(* (* Eval compute in perm_of_2seq _si _sj. *) *)




(* Locate tnth. *)


(* *) *)


(* About tnth. *)



(* (** si = Input Sequence *)
(*     so = Output Sequence *)
(*     This lemma states that : *)
(*         if si = so modulo a permutation, *)
(*         if σ=(perm_of_2seq si so) then *)

(*                   the j   -th element of si *)
(* is exactly        the σ(j)-th element of so *) *)

(* Lemma perm_of_2seqE n (si so : n.-tuple T) (j : 'I_n) : *)
(*   perm_eq si so -> tnth so (perm_of_2seq si so j) = tnth si j. *)
(* Proof. *)
(* rewrite [perm_of_2seq]unlock ; case: eqP => // H1 H2. *)
(* case: sig_eqW => /= s; rewrite /tnth => -> /=. *)
(* by rewrite (nth_map j) ?size_enum_ord // nth_ord_enum. *)
(* Qed. *)

(* (* Definition perm_of_2seq (T : eqType) n (si : seq T) (so : seq T) : 'S_n := *) *)
(* (*   if (size so == n) =P true isn't ReflectT so_n then 1%g *) *)
(* (*   else if (perm_eq si (Tuple so_n) =P true) isn't ReflectT ik then 1%g *) *)
(* (*   else sval (sig_eqW (tuple_perm_eqP ik)). *) *)

(* (* Lemma perm_of_2seqE n (T : eqType) (si so : n.-tuple T) (j : 'I_n) : *) *)
(* (*   perm_eq si so -> tnth so (perm_of_2seq n si so j) = tnth si j. *) *)
(* (* Proof. *) *)
(* (* rewrite /perm_of_2seq; case: eqP => // so_n p_si_so; last first. *) *)
(* (*   by rewrite size_tuple eqxx in so_n. *) *)
(* (* case: eqP => // ?; case: sig_eqW => /= s; rewrite /tnth => -> /=. *) *)
(* (* rewrite (nth_map j) ?size_enum_ord // nth_ord_enum /=. *) *)
(* (* by apply: set_nth_default; rewrite size_tuple. *) *)
(* (* Qed. *) *)




(* (** If si is injective (uniq si) ie, if it represents a permutation, then the inverse of *)
(*     (perm_of_2seq si so) is exactly (perm_of_2seq so si *) *)

(* Lemma perm_of_2seqV n (si so : n.-tuple T) : uniq si -> *)
(*   (perm_of_2seq si so)^-1%g = perm_of_2seq so si. *)
(* Proof. *)
(* move=> uniq_si. *)
(* apply/permP => /= j. *)
(* apply/val_inj/eqP => /=. *)
(* rewrite -(@nth_uniq _ (tnth_default si j) (val si)) //=; last 2 first. *)
(* - by rewrite size_tuple. *)
(* - by rewrite size_tuple. *)
(* rewrite [perm_of_2seq]unlock; case: eqP => p; last first. *)
(*   case: eqP => // p0; by [rewrite perm_eq_sym p0 in p | rewrite invg1]. *)
(*   case: eqP => [p'|]; last first. *)
(*     by rewrite perm_eq_sym {1}p. *)
(* case: sig_eqW => /= x Hx; case: sig_eqW => /= y Hy. *)
(* rewrite {1}Hx (nth_map j); last by rewrite size_enum_ord. *)
(* rewrite nth_ord_enum permE f_iinv /tnth Hy (nth_map j); last by rewrite size_enum_ord. *)
(* rewrite nth_ord_enum /tnth; apply/eqP/set_nth_default;  by rewrite size_tuple. *)
(* Qed. *)

(* Variable R : ringType. *)
(* Local Open Scope ring_scope. *)

(* (* *)
(* Locate uniq. *)

(* Locate insubd. *)
(* Locate in_tuple. *)
(*  *) *)


(* (** Generalized Kronecker symbol : *)

(* I=(i_1, ..., i_n) *)
(* K=(k_1, ..., k_n) *)


(* δ^{I}_{K} = If I is injective and K = σ(I) then ε(σ) else 0. *)

(* Reference :  http://www.unige.ch/math/folks/ronga/lyse_II/2003-2004/chap_IV.pdf (def 1.5) *)
(*  *) *)

(* Definition delta (i k : seq T) : R := *)
(*   if (perm_eq i k) && (uniq i) then *)
(*   (-1) ^+ perm_of_2seq (insubd (in_tuple k) i) (in_tuple k) else 0. *)

(* Locate in_tuple. *)


(* (* *)
(* About in_tuple. *)
(* About delta. *)
(* *) *)


(* Lemma deltaE n (i k : seq T) (si : size i = n) (sk : size k = n) : *)
(*   let T l (P : size l = n)  := Tuple (appP eqP idP P) in *)
(*   delta i k = if (perm_eq i k) && (uniq i) *)
(*               then (-1) ^+ perm_of_2seq (T _ si) (T _ sk) else 0. *)
(* Proof. *)
(* move=> mkT; rewrite /delta; have [/andP [pik i_uniq]|//] := ifP. *)
(* set i' := insubd _ _; set k' := in_tuple _. *)
(* have [] : (i' = mkT _ si :> seq _ /\ k' = mkT _ sk :> seq _). *)
(*   by rewrite /= val_insubd /= (perm_eq_size pik) eqxx. *)
(* move: i' k' (mkT i si) (mkT k sk) => /=. *)
(* by case: _ / sk => ??????; congr (_ ^+ perm_of_2seq _ _); apply: val_inj. *)
(* Qed. *)

(* (* Definition deltaE n (i k : seq nat) (si : size i == n) (sk : size k == n) := *) *)
(* (*   deltaE (Tuple si) (Tuple sk). *) *)

(* (* Lemma delta_cast n (i k : seq nat) (ni : size i = n) (nk : size k = n) : *) *)
(* (*   delta i k = delta (Tuple (appP eqP idP ni)) (Tuple (appP eqP idP nk)). *) *)




(* Lemma delta_0 (i : seq T) k : (~~ uniq i) || (~~ uniq k) -> delta i k = 0. *)
(* Proof. *)
(* case/orP => [Nui|Nuk]; rewrite /delta; case: ifP => // /andP[pik ui]. *)
(*   by rewrite (negbTE Nui) in ui. *)
(* by rewrite -(perm_eq_uniq pik) ui in Nuk. *)
(* Qed. *)


(* (* Definition scast {m n : nat} (eq_mn : m = n) (s : 'S_m) : 'S_n := *) *)
(* (*   ecast n ('S_n) eq_mn s. *) *)

(* (* Lemma tcastE (m n : nat) (eq_mn : m = n) (t : 'S_m) (i : 'I_n), *) *)
(* (*    tnth (tcast eq_mn t) i = tnth t (cast_ord (esym eq_mn) i) *) *)
(* (* tcast_id *) *)
(* (*    forall (T : Type) (n : nat) (eq_nn : n = n) (t : n.-tuple T), *) *)
(* (*    tcast eq_nn t = t *) *)
(* (* tcastK *) *)
(* (*    forall (T : Type) (m n : nat) (eq_mn : m = n), *) *)
(* (*    cancel (tcast eq_mn) (tcast (esym eq_mn)) *) *)
(* (* tcastKV *) *)
(* (*    forall (T : Type) (m n : nat) (eq_mn : m = n), *) *)
(* (*    cancel (tcast (esym eq_mn)) (tcast eq_mn) *) *)
(* (* tcast_trans *) *)
(* (*    forall (T : Type) (m n p : nat) (eq_mn : m = n)  *) *)
(* (*      (eq_np : n = p) (t : m.-tuple T), *) *)
(* (*    tcast (etrans eq_mn eq_np) t = tcast eq_np (tcast eq_mn t) *) *)
(* (* L *) *)

(* (* Lemma perm_of_2seq_tcast (T : eqType) n m i (k : m.-tuple T) (eq_mn : m = n): *) *)
(* (*   perm_of_2seq i (tcast eq_mn k) = scast eq_mn (perm_of_2seq i k). *) *)


(* Lemma perm_of_2seq_ii n (i : n.-tuple T) : uniq i -> *)
(*   perm_of_2seq i i = (1%g). *)
(* Proof. *)
(* move=> ?; apply/permP => /= j; apply/val_inj/eqP => /=. *)
(* by rewrite permE -(@nth_uniq _ (tnth_default i j) i) ?size_tuple // -tnth_nth *)
(*    perm_of_2seqE. *)
(* Qed. *)





(* Lemma deltaii (i : seq T) : uniq i -> delta i i = 1. *)
(* Proof. *)
(* move=> i_uniq; rewrite !(@deltaE (size i)) . *)
(* by rewrite perm_eq_refl i_uniq /= perm_of_2seq_ii // odd_perm1. *)
(* Qed. *)



(* Lemma deltaC (i k : seq T) : delta i k = delta k i. *)
(* Proof. *)
(* have [pik|pik] := boolP (perm_eq i k); last first. *)
(*   by rewrite /delta (negPf pik) perm_eq_sym (negPf pik). *)
(* have [uk|Nuk] := boolP (uniq k); last by rewrite !delta_0 // Nuk ?orbT. *)
(* have si := (perm_eq_size pik); rewrite !(@deltaE (size k)) //. *)
(* rewrite pik /= perm_eq_sym pik (perm_eq_uniq pik) uk /=. *)
(* by rewrite -perm_of_2seqV // odd_permV. *)
(* Qed. *)

(* (* Lemma deltaN1 (i : seq nat) k : uniq i -> *) *)
(* (*   perm_of_2seq i (in_tuple k) -> delta i k = -1. *) *)
(* (* Proof. *) *)
(* (* move=> ui; rewrite /delta /perm_of_2seq ui. *) *)
(* (* case: eqP => [p|]; last by rewrite odd_perm1. *) *)
(* (* case: sig_eqW => /= x ih Hx; by rewrite p Hx expr1. *) *)
(* (* Qed. *) *)

(* (* Lemma delta_1 (i : seq nat) k : uniq i -> perm_eq i k ->  *) *)
(* (*  ~~ perm_of_2seq i (in_tuple k) -> delta i k = 1. *) *)
(* (* Proof. *) *)
(* (* move=> ui ik. *) *)
(* (* rewrite /delta /perm_of_2seq ui. *) *)
(* (* case: eqP => [p|]. *) *)
(* (*   case: sig_eqW => /= x ih Hx. *) *)
(* (*   by rewrite p (negPf Hx) expr0. *) *)
(* (* by rewrite ik. *) *)
(* (* Qed. *) *)


(* (** Composition *) *)


(* Lemma perm_of_2seq_comp n (s1 s2 s3 : n.-tuple T) : *)
(*   uniq s3 -> perm_eq s1 s2 -> perm_eq s2 s3 -> *)
(*   (perm_of_2seq s1 s2 * perm_of_2seq s2 s3)%g = perm_of_2seq s1 s3. *)
(* Proof. *)
(* move=> us3 s12 s23; have s13 := perm_eq_trans s12 s23. *)
(* apply/permP => /= i; rewrite permE /=; apply/val_inj/eqP => /=. *)
(* rewrite -(@nth_uniq _ (tnth_default s1 i) s3) ?size_tuple // -!tnth_nth. *)
(* by rewrite !perm_of_2seqE. *)
(* Qed. *)


(* Lemma delta_comp (i j k : seq T) : *)
(*   uniq k -> perm_eq i j -> perm_eq j k -> *)
(*   delta i k = delta i j * delta j k. *)
(* Proof. *)
(* move=> uk pij pjk; have pik := perm_eq_trans pij pjk. *)
(* have [sj si] := (perm_eq_size pjk, perm_eq_size pik). *)
(* rewrite !(@deltaE (size k)) pik pij pjk /=. *)
(* rewrite (perm_eq_uniq pij) (perm_eq_uniq pjk) uk. *)
(* by  rewrite -signr_addb -odd_permM perm_of_2seq_comp. *)
(* Qed. *)


(* Lemma perm_of_2seq_perm n (s : n.-tuple T) (σ : 'S_n) : *)
(*   uniq s -> *)
(*   perm_of_2seq [tuple (tnth s (σ x)) | x < n] s = σ. *)
(* Proof. *)
(* move=> us; apply/permP => //= i; apply/val_inj/eqP. *)
(* rewrite -(nth_uniq (tnth_default s i) _ _ us) ?size_tuple //=. *)
(* rewrite -!tnth_nth perm_of_2seqE ?tnth_mktuple //. *)
(* by apply/tuple_perm_eqP; exists σ. *)
(* Qed. *)

(* (* *)
(*   rewrite tnth_mktuple. *)
(*   Locate "tuple". *)
(*   rewrite tupleE. *)
(*   *) *)

(* Lemma perm_of_2seq_perm2 n (s1 s2 : n.-tuple T) (s : 'S_n) : *)
(*   uniq s2 -> perm_eq s1 s2 -> *)
(*   perm_of_2seq s1 s2 = (s^-1 * perm_of_2seq [tuple (tnth s1 (s x)) | x < n] s2)%g. *)
(* Proof. *)
(* move=> us2 s12; rewrite -[in RHS](@perm_of_2seq_comp _ _ s1) //; last first. *)
(*   by apply/tuple_perm_eqP; exists s. *)
(* by rewrite ?perm_of_2seq_perm ?mulKg ?(perm_eq_uniq s12). *)
(* Qed. *)

(* (* *)
(* apply/permP => /= j. *)
(* rewrite [perm_of_2seq]unlock. *)
(* case: eqP => // p. *)
(* case: eqP => // p0; last first. *)
(* have : perm_eq [tuple tnth s1 (s x) | x < n] s1. *)
(*   by apply /tuple_perm_eqP; exists s. *)
(*   move : p0 p. *)
(*   set σ := [tuple tnth s1 (s x) | x < n]. *)
(*   move => p0 p. *)
(*   rewrite perm_eq_sym. *)
(*   Check perm_eq s1 σ. *)
(* (*  apply /eqP. *) *)
(*   move : s12. *)
(*   About perm_eq_trans. *)
(*   (* Idea : *)
(* perm_eq s1 s2 -> perm_eq s1 σ -> perm_eq σ s2. *)
(* Yet, p0 states ~~ (perm_eq σ s2). So false -> anything. *) *)
(*     by admit. *)
(*   (* Quantification ??! *) *)
(*    (* rewrite perm_eq_sym p12. *)
(*   About perm_eq_trans. *) *)

(*   (* by admit. *) *)
(*     case: sig_eqW => /= σ1 H1. *)
(*     case: sig_eqW => /= σ2 H2. *)
(*     (* H1 :    s1    = (σ1 * s2)%g *)
(*        H2 : (s*s1)%g = (σ2 * s2)%g *)
(* Goal : σ1 j = (s^-1*σ2)%g j *)

(* Because (uniq s2), this is equivalent to (using associativity) : *)
(*        (σ1*s2)%g j = (s^-1 * (σ2 * s2)%g)%g j *)

(* Rewrite H1, H2 : *)
(*         s1 j = (s^-1 * (s*s1)%g)%g j *)

(* Using associativity + cancel inverse (~ invK) : *)
(*         s1 j = s1 j *)

(* Which is true *) *)

(*     rewrite permM. *)

(*     Print perm_invP. *)
(* Admitted *)


(* Locate nth. *)
(*  *) *)



(* Lemma delta_perm n (i k : n.-tuple T) (σ : 'S_n) : *)
(*   uniq k -> perm_eq i k -> delta [tuple (tnth i (σ x)) | x < n ] k = (-1)^+ σ * delta i k. *)
(* Proof. *)


(* move => uk pik. *)
(* set τ := [tuple tnth i (σ x) | x < n]. *)
(* have pτi : perm_eq τ i by apply /tuple_perm_eqP; exists σ. *)
(* have pτk : perm_eq τ k by rewrite (perm_eq_trans pτi pik). *)
(* have ui : uniq i by rewrite (perm_eq_uniq pik). *)
(* have uτ : uniq τ by rewrite (perm_eq_uniq pτk). *)
(* have sτk : size τ = size k by rewrite !size_tuple. *)
(* have sik : size i = size k by rewrite !size_tuple. *)
(* have sτi : size τ = size i by rewrite !size_tuple. *)
(* have στi : σ = perm_of_2seq τ i by rewrite perm_of_2seq_perm. *)
(* rewrite (@delta_comp τ i k uk pτi pik). *)
(* congr ( _ * _). *)
(* (* rewrite στi. *) *)

(* (* rewrite deltaC.*) *)
(* rewrite /delta pτi uτ //=. *)
(* (* rewrite στi. *) *)
(* rewrite in_tupleE. *)
(* Admitted. *)


(* (* *)
(* rewrite (@deltaE (size i)). *)
(* rewrite pτi uτ //=. *)
(* by []. *)

(* rewrite στi. *)
(* rewrite !(@deltaE (size k)). *)
(* rewrite pτk uτ pik ui //=. *)
(* rewrite -signr_addb. *)

(* About odd_permM. *)
(* About appP. *)

(*  rewrite -odd_permM. *)
(* rewrite perm_of_2seq_perm. *)
(* rewrite -[in RHS]odd_permM. perm_of_2seq_comp. *)
(*   About tuple_perm_eqP. *) *)


(* (* *)
(* move => uk pik. *)
(* have sin : size i = n. *)
(*  - by rewrite (perm_eq_size pik) (size_tuple). *)
(* (* set t := [tuple _ | _ < _]. *) *)
(* (* rewrite /delta. *)
(* apply /tuple_perm_eqP.*) *)
(* have ui : uniq i by rewrite (perm_eq_uniq pik). *)
(* have uniq_shuffle : uniq [tuple tnth i (σ x)  | x < n] = uniq i. *)
(*    - rewrite -(@perm_uniq _  [tuple tnth i (σ x)  | x < n] _) //. *)
(* rewrite !(@deltaE (size k)) ?size_tuple //. *)
(* move => Hyp0 Hyp1. *)
(* rewrite (@perm_eq_trans _ i). *)
(* rewrite !ui pik. *)
(* Search _ "uniq" "tuple". *)
(* apply /tuple_perm_eqP. *)
(* *) *)


(* (* *)
(* Lemma delta_perm n (i k : seq T) (x0 : T) (s : 'S_n) : size k = n -> *)
(*   uniq k -> perm_eq i k -> *)
(*   delta i k = (- 1) ^+ s * delta [tuple (nth x0 i (s x)) | x < n] k. *)
(* Proof. *)
(* move=> kn uk pik. *)
(* have sin : size i = n by rewrite (perm_eq_size pik). *)
(* have ? : size [tuple nth x0 i (s x)  | x < n] = n by rewrite size_tuple. *)
(* have ui : uniq i by rewrite (perm_eq_uniq pik). *)
(* rewrite !(@deltaE n) pik ui //=. *)
(* Search _ "tuple" "map". *)
(* (* *)
(* rewrite tnth_mktuple. *)
(* rewrite -[in RHS](tnth_nth). *)
(* apply /tuple_perm_eqP. *)
(* (* set t := [tuple _ |  _ < _]. *) *)
(* Search _ "tuple" "perm_eqP". *)
(* Search _ "tuple" "seq". *)
(* Search _ "nth" "uniq". *)
(* Locate uniq_perm_eq. *)
(* Locate tuple_perm_eqP. *)


(* Check [seq nth x0 i (s x) | x <- enum 'I_n]. *)
(* Check [tuple tnth  i (s x) | x < n]. *)
(* *) *)
(* case: ifP; last first. *)

(* move => /nandP /orP. *)
(* case /orP => [Npik|Nu]. *)

(* case/andP => H1 H2. *)
(* rewrite -signr_addb. *)
(* congr (_ ^+ _). *)
(* rewrite (perm_of_2seq_perm s) //. *)
(* rewrite -odd_permV. *)
(* Abort. *)
(* *) *)



(* (* Need for distributivity *) *)
(* (** Scheme of a proof : *)

(* j ++ i = [tuple (tnth (i++j) (σ x)) | x < n]. Not really easy to compute such a permutation σ though, *)
(* maybe using perm_of_2seq cleverly, but it is easy to compute it step by step : *)

(* i2 .... ir j1 .... js i1 = i ∘ (1 2 .... r r+1 ... r+s) the (r+s)-cycle whose signature is (-1)^(r+s-1), and one just has to compute it r times to have j ++ i. *)

(* Then, using delta_perm : *)

(* delta (i ++ j) k = (-1) ^+ (size i + size j - 1) * delta ( i2 ... ir j1 ... js i1) k *)
(*                  = ( (-1) ^+ (size i + size j - 1) ) ^+ (size i) delta (j ++ i) k *)
(*                  = (-1) ^+ (size i * size j) * (-1) ^+ (size i * (size i - 1)) * delta (j ++ i ) k *)
(*                  = (-1) ^+ (size i * size j) * delta (j ++ i) k *)

(* because r*(r-1) is even. Qed. *)


(* Maybe we will write lemmas to do so. *) *)

(* Lemma delta_catC (i j k : seq T) : *)
(*   uniq k -> perm_eq (i ++ j) k -> *)
(*   delta (i ++ j) k = (- 1) ^+ (size i * size j) * delta (j ++ i) k. *)
(* Proof. *)
(* Admitted. *)


(* End delta. *)

Section Useful_Lemma.


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

End Useful_Lemma.


Section Sorted_Enum.

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

End Sorted_Enum.



Section Exterior.


(*****************************************************************************)
(****************************Type Definition**********************************)
(*****************************************************************************)


Section ExteriorDef.

Variable (F : comRingType).
Variable (n' : nat).
Let n := n'.+1.

Let dim  := #|{set 'I_n}|.

(*
Inductive exterior : predArgType := Exterior of 'rV[F]_(dim n).
Definition ext_val E := let: Exterior g := E in g.

Canonical exterior_subType := Eval hnf in [newType for ext_val].
*)

Definition exterior := 'rV[F]_(dim).

Canonical exterior_eqType := [eqType of exterior].
Canonical exterior_choiceType := [choiceType of exterior].
Canonical exterior_zmodType := [zmodType of exterior].



Section ExteriorAlgebra.



Lemma scale1ext (u : exterior) : 1 *: u = u.
Proof. by rewrite scale1r. Qed.

(*
rewrite sorted_uniq.
apply /card_uniqP.
About sort.
rewrite map_val_ord_enum.
rewrite ord_enum_uniq.
Search _ "uniq" "enum".
About uniq.
*)


(* (** useful for non commutative product *) *)
(* Definition sign2 (A B : {set 'I_n}) : F := *)
(*   delta F (enum A ++ enum B) (enum (A :|: B)). *)



(* Lemma sign20S1 (S : {set 'I_n}) : sign2 set0 S = 1. *)
(* Proof. *)
(* rewrite /sign2 set0U enum_set0 cat0s. *)
(* by rewrite deltaii ?enum_uniq. *)
(* Qed. *)



(* Lemma sign2S01 (S : {set 'I_n}) : sign2 S set0 = 1. *)
(* Proof. *)
(* rewrite /sign2 setU0 enum_set0 cats0. *)
(* by rewrite deltaii ?enum_uniq. *)
(* Qed. *)


(* (** Idea : ~~[disjoint A & B] = ~~ (uniq ( enum A ++ enum B ) ) *) *)



(* Lemma disjoint_seq (A B : {set 'I_n}) : *)
(*   [disjoint A & B] = [disjoint (enum A) & (enum B)]. *)
(* Proof. *)
(* rewrite !disjoint_subset; apply/subsetP/subsetP => AB x; *)
(* by have := AB x; rewrite !inE !mem_sort !mem_enum; apply. *)
(* Qed. *)


(* Lemma enum_disjoint (A B : {set 'I_n}) : *)
(*     [disjoint A & B] = uniq ( enum A ++ enum B). *)
(* Proof. *)
(* rewrite disjoint_sym cat_uniq !enum_uniq andbT //=. *)
(* by rewrite disjoint_seq disjoint_has. Qed. *)



(* Lemma sign2ND (A B : {set 'I_n}) : ~~ [disjoint A & B] -> sign2 A B = 0. *)
(* Proof. *)
(* rewrite enum_disjoint => ND. *)
(* by rewrite /sign2 delta_0 //= ND. *)
(* Qed. *)


(* Lemma sign2Dl (R S T : {set 'I_n}) : [disjoint R & S] -> *)
(*  sign2 (R :|: S) T = sign2 R T * sign2 S T. *)
(* Proof. *)
(* move => dRS; rewrite /sign2. *)
(* Admitted. *)


(* Lemma sign2ii (i : 'I_n) : sign2 [set i] [set i] = 0. *)
(* Proof. *)
(* by rewrite sign2ND //= -setI_eq0 setIid; apply /set0Pn; exists i; rewrite set11. *)
(* Qed. *)


(* Lemma sign_single (i j : 'I_n) : sign2 [set j] [set i] = - sign2 [set i] [set j]. *)
(* Proof. *)
(* have [->| neq_ij] := eqVneq i j; first by rewrite sign2ii oppr0. *)
(* rewrite /sign2 /enum !enum_set1 setUC. *)
(* rewrite delta_catC. *)
(* - by rewrite !size_sort muln1 expr1 mulN1r. *)
(* - by rewrite sort_uniq enum_uniq. *)
(* rewrite -![sort _ [::_]]/[:: _] perm_eq_sym perm_sort. *)
(* rewrite uniq_perm_eq ?enum_uniq //= ?inE 1?eq_sym ?neq_ij //. *)
(* by move=> x; rewrite !mem_enum !inE orbC. *)
(* Qed. *)


(* (* Definition sign (A B : {set 'I_n}) : F := *) *)
(* (*   \prod_(i in A) \prod_(j in B) if i == j then 0 else (if (i > j)%N then 1 else -1). *) *)

Definition sign (I J: {set 'I_n}) : F :=
  \prod_(i in I) \prod_(j in J) (sgz (i%:Z - j%:Z))%:~R.

Lemma sign0I (I : {set 'I_n}) : sign set0 I = 1.
Proof. by rewrite /sign big_pred0; last  by move=> ?; rewrite in_set0. Qed.

Lemma signI0 (I : {set 'I_n}) : sign I set0 = 1.
Proof.
by rewrite /sign exchange_big big_pred0; last by move=> ?; rewrite in_set0.
Qed.

(* Lemma disjointC (A B : {set 'I_n}) : [disjoint A & B] = [disjoint B & A]. *)
(* Proof. by rewrite -setI_eq0 setIC setI_eq0. Qed. *)


(* Search _ (mem _ _ = mem ).
Search _ "mem" "C".
rewrite /enum //=.
Search _ "mem" "sort".
(* rewrite mem_sort. *)
Admitted.
*)

Lemma signND (A B : {set 'I_n}) : ~~ [disjoint A & B] -> sign A B = 0.
Proof.
rewrite -setI_eq0 => /set0Pn [/= k]; rewrite inE => /andP[kA kB].
by rewrite /sign (bigD1 k) //= (bigD1 k) //= subrr !mul0r.
Qed.

Lemma signii (i : 'I_n) : sign [set i] [set i] = 0.
Proof. by rewrite /sign !big_set1 subrr. Qed.

Lemma signC (I J : {set 'I_n}) : sign I J = (-1) ^+ (#|I| * #|J|) * sign J I.
Proof.
rewrite /sign exchange_big /= exprM.
do 2?[rewrite -prodr_const -big_split /=; apply: eq_bigr=> ? _].
by rewrite mulN1r -rmorphN -sgzN opprB.
Qed.

Lemma signiC (i j : 'I_n) : sign [set j] [set i] = - sign [set i] [set j].
Proof. by rewrite signC !cards1 mulN1r. Qed.

Lemma sqr_sign I J : sign I J ^+ 2 = [disjoint I & J]%:R.
Proof.
have [disjIJ|?] := boolP [disjoint _ & _]; last by rewrite signND ?expr0n.
rewrite /sign pair_big -prodrXl big1 //= => ij /andP[iI jJ].
rewrite -rmorphX /= sgz_odd // subr_eq0.
apply: contraTneq disjIJ => [] [] /val_inj eq_ij.
by rewrite -setI_eq0; apply/set0Pn; exists ij.1; rewrite inE iI eq_ij.
Qed.

Lemma signUl (I J K : {set 'I_n}) :
  sign (I :|: J) K = sign I K * sign J K * sign (I :&: J) K.
Proof.
wlog disjIJ : I J K / [disjoint I & J] => [hwlog|]; last first.
  rewrite disjoint_setI0 ?sign0I ?mulr1 //.
  by rewrite /sign (eq_bigl [predU I & J]) ?bigU=> // ?; rewrite !inE.
set L := I :&: J; pose J' := J :\: L.
have [disjLK|ndisjLK] := boolP [disjoint L & K]; last first.
  rewrite (signND ndisjLK) mulr0 signND //.
  apply: contra ndisjLK; apply: disjoint_trans.
  by rewrite subIset // !subsetU // !subxx // orbC.
rewrite (_ : J = J' :|: L); last first.
  by apply/setP=> i; rewrite !inE; case: (_ \in _) (_ \in _) => [] [].
rewrite setUA setUAC (setUidPl (subsetIl _ _)).
have disjIJ': [disjoint I & J'] by rewrite -setI_eq0 /J' setIDA setDv.
  (* TODO: report: why the v? *)
have disjJ'L: [disjoint J' & L].
  by rewrite -setI_eq0 /J' setDE setIAC -setIA setICr setI0.
rewrite hwlog // (disjoint_setI0 disjIJ') sign0I mulr1.
rewrite hwlog // (disjoint_setI0 disjJ'L) sign0I mulr1.
by rewrite mulrA -mulrA [sign L K * _]sqr_sign disjLK mulr1.
Qed.

(* for compatibility *)
Lemma signDl (I J K : {set 'I_n}) : [disjoint I & J] ->
  sign (I :|: J) K = sign I K * sign J K.
Proof. by rewrite signUl => /disjoint_setI0->; rewrite sign0I mulr1. Qed.

Lemma signUr (I J K : {set 'I_n}) :
  sign I (J :|: K) = sign I J * sign I K * sign I (J :&: K).
Proof.
rewrite ![sign I _]signC signUl !mulrA; congr (_ * _).
rewrite [RHS]mulrC mulrA; congr (_ * _).
rewrite !mulrA -exprD mulrAC -exprD; congr (_ * _).
rewrite -!mulnDr ![(#|I| * _)%N]mulnC !exprM; congr (_ ^+ _).
rewrite cardsU -[in RHS]addnA [in RHS]addnC.
rewrite -intr_sign exprB ?cardsI ?leq_subr //.
by rewrite invr_sign -exprD intr_sign.
Qed.

Lemma signDr (I J K : {set 'I_n}) : [disjoint J & K] ->
  sign I (J :|: K) = sign I J * sign I K.
Proof. by rewrite signUr => /disjoint_setI0->; rewrite signI0 mulr1. Qed.

(*
Search _ (_^~ _ = _ ^~ _).


Search _ (count^~ _).



Search _ (enum [set _]).

(* apply /perm_eqP.

apply perm_eq_refl. *)


have enum_set2 : enum [set i; j] = enum [:: i; j].

Search _ "enum".


rewrite (eq_enum (in_set _)).

Search _ (perm_eq _ ( enum _) ).


apply sort_sorted.
rewrite eq_sorted.
rewrite perm_sort.
Search _ "perm" "sort".
Admitted.
*)


(** basis vector of the exterior algebra *)
Definition blade A : exterior := 'e_(enum_rank A).

Definition to_ext (x : 'rV_n) : exterior :=
  \sum_(i : 'I_n) (x 0 i) *: blade [set i].

Local Notation "x %:ext" := (to_ext x) (format "x %:ext", at level 2).

Lemma to_ext_add (x y : 'rV_n) : x%:ext + y%:ext = (x + y)%:ext.
Proof.
by rewrite /to_ext -big_split; apply: eq_bigr => i _; rewrite mxE scalerDl.
Qed.

Lemma blade_eq (I J : {set 'I_n}) : J = I -> blade I 0 (enum_rank J) = 1.
Proof.
move => eqIJ.
rewrite /blade/delta_mx mxE //=.
have eqrank : enum_rank J == enum_rank I.
apply /eqP.
rewrite (@f_equal _ _ _ _ I) //=.
by rewrite eqrank.
Qed.


Lemma blade_diff (I J : {set 'I_n}) : J != I -> blade I 0 (enum_rank J) = 0.
Proof.
move => JnI; rewrite /blade /delta_mx mxE //=.
have NeqIJ : (enum_rank J == enum_rank I) = false; last first.
 -  by  rewrite NeqIJ.
apply negbTE; rewrite eq_sym.
move : JnI; rewrite eq_sym.
move : (@enum_rank_inj _ I J).
by apply contra_neq.
Qed.


(** Exterior algebra is indeed a Unital Algebra *)

Print Canonical Projections.

(** First : Ring structure *)

(** For blades *)
Definition mul_blade (I J : {set 'I_n}) : exterior := sign I J *: blade (I :|: J).
Local Notation "*b%F" := (@mul_blade _).
Local Notation "R *b I" := (mul_blade R I) (at level 40).

Definition id_ext : exterior := blade set0.

(** id_ext is an identity element *)
Lemma lmul_blade_1 (I : {set 'I_n}) : I *b set0 = blade I.
Proof.
by rewrite /mul_blade setU0 signI0 scale1ext. Qed.

Lemma rmul_blade_1 (I : {set 'I_n}) : set0 *b I  = blade I.
Proof.
by rewrite /mul_blade set0U sign0I scale1ext. Qed.



(** A definition of wedge product *)
Definition mul_ext (u v : exterior) : exterior :=
  \sum_(su : {set 'I_n})
   \sum_(sv : {set 'I_n})
   (u 0 (enum_rank su) * v 0 (enum_rank sv) * sign su sv) *: blade (su :|: sv).

Local Notation "*w%F" := (@mul_ext _).
Local Notation "u *w w" := (mul_ext u w) (left associativity, at level 40).

Lemma mul_extE (u v : exterior) (I : {set 'I_n}) :
  (u *w v) 0 (enum_rank I) =
  \sum_(J in powerset I)
   (u 0 (enum_rank J) * v 0 (enum_rank (I :\: J)) * sign J (I :\: J)).
Proof.
have bm := (@big_morph _ _ (fun M : 'M__ => M 0 _) 0 +%R) ; move=> [:mid mop].
rewrite [LHS]bm; last first.
- by abstract: mid; rewrite mxE.
- by abstract: mop; move=> ??; rewrite mxE.
rewrite (bigID (mem (powerset I))) /=.
rewrite [X in _ + X]big1 ?addr0 /=; last first.
  move=> su; rewrite inE => NsuA.
  rewrite bm ?big1 => // sv _; rewrite !mxE /= [_ == _]negbTE ?mulr0 //.
  by apply: contraNneq NsuA => /enum_rank_inj ->; rewrite subsetUl.
apply: eq_bigr => su suA; rewrite bm // (bigD1 (I :\: su)) //= big1 ?addr0.
  rewrite setDE setUIr -setDE setUCr setIT (setUidPr _) -?powersetE //.
  by rewrite !mxE ?eqxx ?mulr1.
move=> sv svNADsu; rewrite !mxE /=.
have [duv|Nduv]:= boolP [disjoint su & sv]; last first.
  by rewrite signND ?(mulr0,mul0r).
rewrite [_ == _]negbTE ?mulr0 //.
apply: contraNneq svNADsu => /enum_rank_inj ->.
by rewrite setDUl setDv set0U (setDidPl _) // disjoint_sym.
Qed.



(** id_ext is indeed an identity element *)
Lemma mul_ext1x : left_id id_ext mul_ext.
Proof.
move=> u; apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i.
rewrite mul_extE.
rewrite (bigD1 (set0)) //=; last first.
  - by rewrite powersetE sub0set.
rewrite big1 => [|s sneq0]; last first.
  - rewrite blade_diff ?mul0r //=.
    by move : sneq0; case : (s \in powerset A).
rewrite blade_eq //=.
by rewrite sign0I setD0 mulr1 mul1r addr0.
Qed.



Lemma mul_extx1 : right_id id_ext mul_ext.
Proof.
move=> u; apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i.
rewrite mul_extE (bigD1 (A)) //=;  last first. by rewrite powersetE.
rewrite big1 => [|s spropA]; last first.
  - have sub_sA : s \subset A.
       by move : spropA; rewrite andbC => /andP[ _]; rewrite powersetE.
  - have ADSneq0 : A :\: s != set0.
    by rewrite -card_gt0 cardsDS ?SsubA ?subn_gt0;
      move : spropA; rewrite powersetE andbC -properEneq properEcard => /andP[_ card].
  - rewrite blade_diff; last first. by rewrite ADSneq0.
      by rewrite mulrAC mulr0.
rewrite blade_eq; last first. by rewrite setDv.
by rewrite setDv addr0 signI0 ?mulr1.
Qed.




(*
apply /set0Pn.
apply: existsP.




have cardge0 : #|A :\: s| > 0.
rewrite cardsDS ?SsubA ?subn_gt0.

Search _ (_ - _ > 0) .

apply /setP => x.



rewrite setD_eq0.


rewrite subEproper.
apply /norP.
move : spropA => /andP[SsubsetA sneqA2].
rewrite eq_sym.
suff AnpropS : ~~ (A \proper s).
 - by move : sneqA AnpropS.
Search _ ( ~~ ( _ \proper _) ).
rewrite properE.
apply /nandP.

Check (s \subset A).
case (s \subset A).
rewrite //=.
apply /orP.
by rewrite orbT.
rewrite //=.
apply /orP.
rewrite orbF.



(*
move : sneqA.
rewrite eqEsubset.
rewrite negb_and.
case (s \subset A).
rewrite //=.
rewrite //=.
move : Aneqs.
rewrite eqEsubset negb_and.
*)


(*
rewrite (@negbNE (s \subset A)) //=.
move : SsubsetA.
rewrite powersetE //=.


move => /andP [A B].


have sneqA : s != A.
move : spropA.
by case : (s\in powerset A).
have Aneqs : A != s.
move : sneqA.
by rewrite eq_sym.
rewrite //=.



have sneqA : s != A.
move : spropA.
by case : (s\in powerset A).
have Aneqs : A != s.
move : sneqA.
by rewrite eq_sym.
move : Aneqs.
rewrite eqEsubset.
case : (A \subset s); last first.
 - by [].
rewrite //=.
have SsubA : s \subset A.
move : spropA.
rewrite andbC powersetE.
case : (s \subset A).
 - by [].
 - by rewrite andbF.
have NnSsubA : ~~ ~~ (s \subset A).
move : SsubA.
rewrite (@negbTE (~~ (s \subset A))).
Search _ (_ -> ~~ _ -> _).

(*
rewrite contraT.
rewrite powersetE andbC -properEneq.
rewrite //=.
rewrite eqEsubset.
rewrite negb_and.
case : (s \subset A).
rewrite //=.
About proj2.
rewrite negb_and.
Search _ (_ || _ -> _).
apply /nandP.
rewrite powersetE andbC -properEneq.
move=> spropA.
apply/set0Pn.
apply /setDP.

rewrite proper_card.
apply /properP.
move : sneqA. case : (s \in powerset A).
rewrite //=.

(* Qed.
*)*)
*)
Admitted.
*)


(** Blade product is a particular case of wedge product of two exterior *)
Lemma mul_blade_ext (I J : {set 'I_n}) : I *b J = blade I *w blade J.
Proof.
rewrite /mul_blade /mul_ext.
rewrite (bigD1 I) //= addrC.
rewrite big1 => [|K KneqI]; last first.
  - rewrite blade_diff ?KneqI //=.
    rewrite (bigD1 J) //=.
    rewrite big1 => [| L LneqJ]; last first.
      - by rewrite blade_diff ?LneqJ ?mul0r ?scale0r.
    by rewrite blade_eq ?mul0r ?scale0r ?addr0.
rewrite add0r (bigD1 J) //=.
rewrite big1 => [| U UneqJ]; last first.
 - by rewrite blade_eq ?blade_diff ?mul1r ?mul0r ?scale0r.
by rewrite !blade_eq ?mul1r ?addr0.
Qed.

(** Better Alternative: *)


(** 0 is 0 *)
Lemma ext0 (I : {set 'I_n}) : (0 : exterior) 0 (enum_rank I) = 0.
Proof. by rewrite mxE. Qed.


(** 0 is absorbing *)
Lemma mul0ext (u : exterior) : 0 *w u = 0.
Proof.
apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i.
rewrite mul_extE.
rewrite big1 //=.
rewrite ext0 //=.
by move => j; rewrite ext0 !mul0r.
Qed.


Lemma mulext0 (u : exterior) : u *w 0 = 0.
Proof.
apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i.
rewrite mul_extE.
rewrite big1 //=.
rewrite ext0 //=.
by move => j; rewrite ext0 mulrC !mulr0.
Qed.



Lemma ext_sum_blade (u : exterior) :
  u = \sum_su u 0 (enum_rank su) *: blade su.
Proof.
apply /rowP=> i; rewrite -(enum_valK i); set A := enum_val i.
rewrite summxE.
rewrite (eq_bigr (fun k => u``_(enum_rank k) * ((blade k) 0 (enum_rank A)))).
rewrite (bigD1 A) //=.
by rewrite blade_eq ?mulr1 ?big1 ?addr0 //;
move => ??; rewrite blade_diff ?mulr0 //=; rewrite eq_sym.
by move => ??; rewrite mxE.
Qed.


(** Homogeneity of wedge product *)


Lemma scaleextAl (k : F) (u v : exterior) : k *: (u *w v) = (k *: u) *w v.
Proof.
apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i; rewrite mxE !mul_extE.
rewrite big_distrr //=.
by apply eq_bigr => S _; rewrite !mulrA mxE.
Qed.

Lemma scaleextAr a (u v : exterior) : a *: (u *w v) = u *w (a *: v).
Proof.
apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i; rewrite mxE !mul_extE.
rewrite big_distrr //=.
apply eq_bigr => S _.
rewrite mxE !mulrA.
by congr ( _ * _); congr (_ * _) ; rewrite mulrC.
Qed.

(* Lemma scalebladeAr a (S T : {set 'I_n}) : a *: (blade S *w blade T) = blade S *w (a *: blade T). *)
(* Proof. *)
(* apply /rowP => i; rewrite -(enum_valK i). *)
(* set A := enum_val i; rewrite mxE !mul_extE. *)
(* rewrite big_distrr //=; apply eq_bigr => R _. *)
(* by rewrite !mxE !mulrA //= [a * _]mulrC. *)
(* Qed. *)

Lemma mul_extN (u v : exterior) : u *w (-v) = - (u *w v).
Proof.
apply/rowP=> i; rewrite -(enum_valK i); set A := enum_val i.
rewrite !mxE !mul_extE -sumrN.
apply: eq_bigr=> s _.
by rewrite mxE -mulNr; congr ( _ * _); rewrite mulrN.
Qed.

Lemma mul_Next (u v : exterior) : -u *w v = - (u *w v).
Proof.
apply/rowP=> i; rewrite -(enum_valK i); set A := enum_val i.
rewrite !mxE !mul_extE -sumrN.
apply: eq_bigr=> s _.
by rewrite mxE -mulNr; congr ( _ * _); rewrite mulNr.
Qed.

(** Left Distributivity *)
Lemma mul_extDl : left_distributive mul_ext +%R.
Proof.
move => u v w; apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i.
rewrite mxE !mul_extE -big_split //=.
by apply : eq_bigr => s _; rewrite mxE !mulrDl.
Qed.

(** Right Distributivity *)
Lemma mul_extDr : right_distributive mul_ext +%R.
Proof.
move => u v w; apply /rowP => i; rewrite -(enum_valK i).
set A := enum_val i.
rewrite mxE !mul_extE -big_split //=.
by apply : eq_bigr => s _; rewrite mxE !mulrDr mulrDl.
Qed.

Lemma mul_extBl (u v w : exterior) : (u - v) *w w = u *w w - v *w w.
Proof. by rewrite mul_extDl mul_Next. Qed.

Lemma mul_extBr (u v w : exterior) : u *w (v - w) = u *w v - u *w w.
Proof. by rewrite mul_extDr mul_extN. Qed.


(** bilinearity *)
Lemma mul_ext_suml (u : exterior) I r P (v_ : I -> exterior) :
   (\sum_(i <- r | P i) v_ i) *w u = \sum_(i <- r | P i) v_ i *w u.
Proof.
by apply: (big_morph (mul_ext^~ u)) => [v w|]; rewrite ?mul0ext ?mul_extDl.
Qed.

Lemma mul_ext_sumr (u : exterior) I r P (v_ : I -> exterior) :
   u *w (\sum_(i <- r | P i) v_ i) = \sum_(i <- r | P i) u *w v_ i.
Proof.
by apply: (big_morph (mul_ext u)) => [v w|]; rewrite ?mulext0 ?mul_extDr.
Qed.



Lemma mul_ext_sumlr I J rI rJ pI pJ (u_ : I -> exterior) (v_ : J -> exterior) :
  (\sum_(i <- rI | pI i) u_ i) *w (\sum_(j <- rJ | pJ j) v_ j) = \sum_(i <- rI | pI i) \sum_(j <- rJ | pJ j) (u_ i) *w (v_ j).
Proof. by rewrite mul_ext_suml; apply: eq_bigr => i _; rewrite mul_ext_sumr. Qed.




(** Exterior product is associative *)

Lemma mul_bladeA (I J K : {set 'I_n}) :
   blade I *w (blade J *w blade K) = blade I *w blade J *w blade K.
Proof.
rewrite -!mul_blade_ext /mul_blade -scaleextAr -scaleextAl.
rewrite -!mul_blade_ext /mul_blade !scalerA setUA; congr ( _ *: _).
have [disIJ|NdisIJ] := boolP [disjoint I & J]; last first.
    - have NdisIJuK : ~~ [disjoint I & J :|: K]; last first.
      by rewrite [sign I ( J :|: K)]signND ?[sign I J]signND
                 ?mulr0 ?mul0r ?NdisIJuK.
      have subIJK : ((I :&: J) \subset I :&: (J :|: K)); last first.
        - move: subIJK NdisIJ; rewrite -!setI_eq0.
          exact: subset_neq0.
      rewrite setIUr subsetUl //=.
have [disJK|NdisJK] := boolP [disjoint J & K].
  by rewrite signDl ?signDr ?disIJ ?disJK //= mulrC mulrA.
have NdisIuJK : ~~ [disjoint I :|: J & K]; last first.
  rewrite [sign (I :|: J) K]signND ?[sign J K]signND;
  by rewrite ?mulr0 ?mul0r ?NdisIJuK.
have subIJK : ((J :&: K) \subset (I :|: J) :&: K); last first.
   move: subIJK NdisJK; rewrite -!setI_eq0.
   exact: subset_neq0.
by rewrite setIUl subsetUr.
Qed.

Lemma mul_extA : associative mul_ext.
Proof.
move => u v w.
rewrite [in RHS](ext_sum_blade u) [in LHS](ext_sum_blade w) (ext_sum_blade v).
rewrite !mul_ext_sumlr.
rewrite [X in X *w _ = _]ext_sum_blade [X in _ = _*w X]ext_sum_blade.
rewrite [in LHS]mul_ext_suml [in RHS]mul_ext_sumr.
rewrite [in LHS](eq_bigr (fun (i : {set 'I_n}) =>
\sum_j \sum_k ((u``_(enum_rank i) * v``_(enum_rank j) * w``_(enum_rank k)) *: ((blade i) *w ( (blade j) *w (blade k)))))).
rewrite [in RHS](eq_bigr (fun (i : {set 'I_n}) =>
\sum_su (\sum_sv (u``_(enum_rank su) * v``_(enum_rank sv) * w``_(enum_rank i)) *: ( ( (blade su) *w (blade sv) ) *w (blade i) )))) .
rewrite [in RHS]exchange_big //=.
apply eq_bigr => R _.
rewrite [X in _ = X]exchange_big //=.
apply eq_bigr => S _.
apply eq_bigr => T _.
by rewrite mul_bladeA.
move => T _.
rewrite [in LHS]mul_ext_suml.
apply: eq_bigr => R _.
rewrite [in LHS]mul_ext_suml.
apply: eq_bigr => S _.
  rewrite -scaleextAl -(scaleextAr (v``_(enum_rank S))) scalerA.
  by rewrite -scaleextAl -scaleextAr scalerA.
move=> R _.
rewrite [in LHS]mul_ext_sumr.
apply: eq_bigr => S _.
rewrite [in LHS]mul_ext_sumr.
apply: eq_bigr => T _.
rewrite -scaleextAl -(scaleextAl (v``_(enum_rank S))).
rewrite -(scaleextAr (w``_(enum_rank T))) scalerA.
by rewrite -(scaleextAr (v``_(enum_rank S) * w``_(enum_rank T))) scalerA mulrA.
Qed.


Section ExteriorRing.



(** Non trivial ring *)
Lemma ext_nonzero1 : id_ext != 0 :> exterior.
Proof.
apply/eqP=> /rowP /(_ (enum_rank set0)); rewrite !mxE /= eqxx.
by move=> /eqP; rewrite oner_eq0.
Qed.

Definition exterior_ringMixin :=
  RingMixin (mul_extA) (mul_ext1x) (mul_extx1)
            (mul_extDl) (mul_extDr) (ext_nonzero1).

Canonical exterior_ringType := Eval hnf in RingType exterior exterior_ringMixin.
Canonical exterior_lAlgType := Eval hnf in LalgType F exterior (scaleextAl).
Canonical exterior_AlgType  := Eval hnf in AlgType  F exterior (scaleextAr).


Lemma mulextE : mul_ext = *%R. Proof. by []. Qed.
Lemma id_extE : id_ext = 1. Proof. by []. Qed.

End ExteriorRing.


(* Local Notation "\prod_ ( i | P ) B" := *)
(*   (\big[mul_ext/id_ext]_(i | P) B%ext) : ext_scope. *)
(* Local Notation "\prod_ ( i < n | P ) B" := *)
(*   (\big[mul_ext/id_ext]_(i < n | P) B%ext) : ext_scope. *)
(* Local Notation "\prod_ ( i <- r | P ) B" := *)
(*   (\big[mul_ext/id_ext]_(i <- r | P) B%ext) : ext_scope. *)
(* Local Notation "\prod_ i B" := *)
(*   (\big[mul_ext/id_ext]_i B%ext) : ext_scope. *)
(* Local Notation "\prod_ ( i < n ) B" := *)
(*   (\big[mul_ext/id_ext]_(i < n) B%ext) : ext_scope. *)
(* Local Notation "\prod_ ( i <- r ) B" := *)
(*   (\big[mul_ext/id_ext]_(i <- r) B%ext) : ext_scope. *)

Lemma mul_blades I J : blade I * blade J = sign I J *: blade (I :|: J).
Proof.
rewrite -mulextE /mul_ext.
rewrite (bigD1 I) //= addrC.
rewrite big1 => [|K KneqI]; last first.
  rewrite blade_diff ?KneqI //=.
  rewrite (bigD1 J) //=.
  rewrite big1 => [|L LneqJ]; last first.
    by rewrite blade_diff ?UneqJ ?mul0r ?scale0r.
  by rewrite blade_eq ?mul0r ?scale0r ?addr0.
rewrite add0r (bigD1 J) //=.
rewrite big1 => [|L LneqJ]; last first.
  by rewrite blade_eq ?blade_diff ?mul1r ?mul0r ?scale0r.
by rewrite !blade_eq ?mul1r ?addr0.
Qed.


Lemma mul_bladexx0 (i : 'I_n) : (blade [set i]) * (blade [set i]) = 0.
Proof. by rewrite -mulextE -mul_blade_ext /mul_blade signii scale0r. Qed.

Lemma mul_bladeC (I J : {set 'I_n}) :
  blade I * blade J = (-1) ^+ (#|I| * #|J|) *: (blade J * blade I).
Proof. by rewrite !mul_blades signC -scalerA setUC. Qed.

Lemma mul_1bladeC (i j : 'I_n) :
  blade [set i] * blade [set j] = - blade [set j] * blade [set i].
Proof. by rewrite mul_bladeC !cards1 scaleN1r mulNr. Qed.


(** Only true for vectors from the original vector space *)

Lemma mulxx0 (x : 'rV_n) : x%:ext ^+ 2 = 0.
Proof.
rewrite /to_ext expr2 big_distrlr //=. (* pair_big /=. *)
rewrite (eq_bigr (fun (i : 'I_n) =>
  \sum_(j < n | (j < i)%N) x``_i * x``_j *: (blade [set i] * blade [set j]) +
  \sum_(j < n | (j > i)%N) x``_i * x``_j *: (blade [set i] * blade [set j]))).
rewrite big_split /= [X in _ + X](exchange_big_dep predT) //=.
rewrite -big_split /= big1 //=.
  move=> i _; rewrite -big_split big1 //=.
  move=> j _; rewrite mulrC -scalerDr [X in _ + X]mul_1bladeC.
  by rewrite -[X in X + _]add0r mulNr addrK scaler0.
move=> i _; rewrite (bigD1 i) //=.
rewrite -scalerAl -scalerAr mul_bladexx0 !scaler0 add0r.
rewrite (bigID (fun j : 'I__ => j < i)%N) //=.
rewrite (eq_bigl (fun j : 'I__ => j < i)%N); last first.
  by move=> j; rewrite -val_eqE /=; case: ltngtP.
rewrite [X in _ + X](eq_bigl (fun j : 'I__ => i < j)%N); last first.
  by move=> j; rewrite -val_eqE /=; case: ltngtP.
move=> [: disj_lelt]; rewrite -!bigU /=; last 2 first.
- abstract: disj_lelt; rewrite disjoint_subset; apply /subsetP => j;
  by rewrite !inE !unfold_in eqnE -leqNgt; apply: leq_trans.
- by apply: disj_lelt.
by apply : eq_bigr => j _; rewrite -scalerAr -scalerAl scalerA mulrC.
Qed.

(* rewrite eq_bigr. *)
(* rewrite (bigID (fun (j : 'I_n) => (j<i))) //=. *)


(* move : neq_ltn => H. *)





(* rewrite eqVneq.  *)

(* rewrite (eq_bigr (fun (i : 'I_n) =>  *)
(* \sum_(j<n | j<i)x``_i*x``_j*:((blade [set i])*(blade [set j]) + (blade) + \sum_(j<n | j>i)x``_i*x``_j*:((blade [set i])*(blade [set j])))). *)


(* rewrite big1 //= => i _. *)
(* rewrite (bigD1 i) //=. *)
(* rewrite -scaleextAr !scalerAl scalerA -scalerAl. *)
(* rewrite mul_bladexx0 scaler0 add0r. *)
(* rewrite big1 //= => j _. *)
(* rewrite mulrA. *)
(* rewrite scaleextAr. *)
(* (* rewrite -big_split_ord.*) *)
(* (* rewrite big1_eq.  *) *)
(* (* rewrite -scaleextAr. *) *)
(* Search _ "sum" "eq0". *)
(* *)


Lemma sqextrD (u v : exterior) : (u + v)^+2 = u^+2 + u*v + v*u + v^+2.
Proof. by rewrite expr2 mulrDl !mulrDr addrA -!expr2. Qed.

(** Probleme de typage ? zmodtype ?? *)
Lemma mul_extNC (x y : 'rV_n) : x%:ext * y%:ext = - y%:ext * x%:ext.
Proof.
rewrite mulNr.
have: (x%:ext + y%:ext)^+2 = 0.
  by rewrite expr2 to_ext_add -expr2 mulxx0.
rewrite sqextrD !mulxx0 addr0 add0r.
by move=> /eqP; rewrite addr_eq0 => /eqP->.
Qed.




End ExteriorAlgebra.


Section Form.

Definition form_of r := 'M[F]_(r,n) -> F.

Notation "r .-form" := (form_of r)
  (at level 2, format "r .-form") : type_scope.

(* (* Exterior product of two alternating form *) *)
(* Definition mul_form r s (a : r.-form) (b : s.-form) : (r + s).-form :=  *)
(*   fun v => ((r + s)`!)%:R^-1 * \sum_(sigma : 'S_(r + s)) *)
(*             (- 1) ^ sigma * *)
(*                     a (\matrix_(i < r) row (sigma (unsplit (inl i))) v) *  *)
(*                     b (\matrix_(i < s) row (sigma (unsplit (inr i))) v). *)


(*Definition enum (s : {set 'I_n}) : seq 'I_n :=
  sort (fun i j : 'I_n => i <= j) (enum s).*)

(* Definition size_enum r (s : {set 'I_n}) : #|s| = r -> size (enum s) == r. *)
(* Proof. Admitted. *)

(* Definition canon_tuple (s : {set 'I_n}) := Tuple (size_enum s). *)

Definition multilinear r (f : r.-form) :=
   forall (A B C : 'M_(r,n)) (i0 : 'I_r) (b c : F),
   row i0 A = b *: row i0 B + c *: row i0 C ->
   row' i0 B = row' i0 A ->
   row' i0 C = row' i0 A -> f A = b * f B + c * f C.

Definition alternate r (f : r.-form) :=
  forall (A : 'M_(r, n)) (i1 i2 : 'I_r), i1 != i2 -> A i1 =1 A i2 -> f A = 0.

Definition multilinear_alternate r (f : r.-form) :=
  multilinear f /\ alternate f.


(** I wanted to say that two multilinear forms which take the same value
    on a basis are in fact equal. I don't use alternate because otherwise
    I need to go through permutations. Not sure about the formulation of this lemma. *)
Lemma multilinear_eq_basis r (f : r.-form) (g : r.-form) :
multilinear f -> multilinear g ->
(forall i j, f (delta_mx i j) = g (delta_mx i j)) -> f =1 g.
Admitted.


Section form_of1.

(* ~ scalar product *)
Definition form_of_ext r (u : exterior) : r.-form := fun v =>
  \sum_(s : {set 'I_n} | #|s| == r)
     u 0 (enum_rank s) * (\prod_i to_ext (row i v)) 0 (enum_rank s).

Definition ext_of_form r (f : r.-form) : exterior :=
  \sum_(s : {set 'I_n} | #|s| == r)
   f (\matrix_(i < r) [seq 'e_i | i <- enum s]`_i) *: blade s.


Definition mul_form r s (a : r.-form) (b : s.-form) : (r + s).-form :=
form_of_ext (ext_of_form a * ext_of_form b).


Lemma ext_of_formK r (f : r.-form) : multilinear_alternate f ->
  form_of_ext (ext_of_form f) =1 f.
Proof.
move=> f_ma v.
have f_m : multilinear f. exact : (proj1 f_ma).
have f_a : alternate f. exact : (proj2 f_ma).
rewrite /form_of_ext /ext_of_form /=.
Admitted.


Lemma form_of_extK r (u : exterior) : (* u \in extn r-> *)
  ext_of_form (@form_of_ext r u) =1 u.
Proof.
Admitted.



Lemma multilinear_form_of_ext r (x : exterior) :
  (* r <= n -> *) multilinear (form_of_ext x : r.-form).
Proof.
move => (* leqrn *) U V W i a b.
rewrite -[_ + _](row_id 0); move/row_eq=> uvw.
move/row'_eq=> vu; move/row'_eq=> wu.
rewrite !big_distrr -big_split; apply: eq_bigr => s sR /=.
rewrite (mulrCA a) (mulrCA b) -mulrDr; congr ( _ * _).
have rewr :   a * (\prod_(i0 < r) to_ext (row i0 V)) 0 (enum_rank s) +
  b * (\prod_(i0 < r) to_ext (row i0 W)) 0 (enum_rank s) =
  (a *: \prod_(i0 < r) to_ext (row i0 V) +
  b *: \prod_(i0 < r) to_ext (row i0 W)) 0 (enum_rank s); last first.

rewrite rewr.



have eq_prod : \prod_(i0 < r) to_ext (row i0 U) = a *: \prod_(i0 < r) to_ext (row i0 V) + b *: \prod_(i0 < r) to_ext (row i0 W); last first.

by rewrite eq_prod.


(* have prod_cat1 : \prod_(i0 < r) to_ext (row i0 u) = (\prod_(i0 < i) to_ext (row i0 u))*(\prod_(i <= i0 < r) to_ext (row i0 u)). *)



(* rewrite [in RHS]summxE. *)
(* rewrite (@big_cat_nat _ _ _ i 0 r). *)
Admitted.

Lemma alternate_form_of_ext r (x : exterior) : (* r <= n -> *)
  alternate (form_of_ext x : r.-form).
Proof.
Admitted.



Lemma form_of_multilinear_alternate r (x : exterior) :
  multilinear_alternate (form_of_ext x : r.-form).
Proof.
by move :
multilinear_form_of_ext
alternate_form_of_ext.
Qed.

Lemma mul_ext_form r s (f : r.-form) (g : s.-form) :
  multilinear_alternate f -> multilinear_alternate g ->
  ext_of_form (mul_form f g) =1 (ext_of_form f) * (ext_of_form g).
Proof.
move=> f_ma g_ma; rewrite /mul_form.
Abort.

End form_of1.


(* Alternative definition *)
Section form_of2.

(* Definition form_of_ext r (u : exterior) : r.-form := fun v => *)
(*   \sum_(s : {set 'I_n} | #|s| == r) *)
(*      u 0 (enum_rank s) * (\prod_i to_ext (row i v)) 0 (enum_rank s). *)

Definition form_of_ext2 r (u : exterior) : r.-form := fun v =>
   \sum_(s : {set 'I_n} | #|s| == r)
      u 0 (enum_rank s) * (minor id (nth 0 (enum s)) v).


Definition mul_form2 r s (a : r.-form) (b : s.-form) : (r + s).-form :=
  form_of_ext2 (ext_of_form a * ext_of_form b).

Definition add_form2 r (a : r.-form) (b : r.-form) : r.-form :=
  form_of_ext2 (ext_of_form a + ext_of_form b).


End form_of2.

Section null_form.

Definition null_form r : r.-form := fun _ => 0.

Lemma null_form0 r v : @null_form r v = 0.
Proof. by []. Qed.

Lemma null_form_ext r : @form_of_ext2 r 0 =1 @null_form r.
Proof.
move=> v; rewrite /form_of_ext2 /null_form.
by apply: big1=> s  _; rewrite ext0 mul0r.
Qed.

Lemma null_ext_form r : ext_of_form (@null_form r) = 0.
Proof.
apply/rowP=> i; rewrite /ext_of_form /null_form summxE mxE.
by apply: big1=> s _; rewrite mxE mul0r.
Qed.

Lemma ext_of_form0 r (f : r.-form) : (r > n)%N -> ext_of_form f = 0.
Proof.
move => leqnr; rewrite /ext_of_form.
apply: big_pred0 => s.
have card_small (A : {set 'I_n}) : (#|A| <= n)%N.
  by rewrite (leq_trans (max_card _)) ?card_ord.
have card_ler (A : {set 'I_n}) : (#|A| < r)%N.
  by move : (card_small A) leqnr; apply : leq_ltn_trans.
by move: (card_ler s); apply: ltn_eqF.
Qed.

Lemma form_of_ext0 r (u : exterior) : (r > n)%N -> form_of_ext u =1 (@null_form r).
Proof.
move=> leqnr v; rewrite null_form0 /form_of_ext.
apply: big_pred0 => s.
have card_small (A : {set 'I_n}) : (#|A| <= n)%N.
  by rewrite (leq_trans (max_card _)) ?card_ord.
have card_ler (A : {set 'I_n}) : (#|A| < r)%N.
  by move : (card_small A) leqnr; apply : leq_ltn_trans.
by move: (card_ler s); apply: ltn_eqF.
Qed.

End null_form.

(** Apply ext_of_form2 on basis elements, then there is the same determinant as 
    form_of_extK. Just need multilinearity *)
Lemma ext_of_formK2 r (f : r.-form) : multilinear_alternate f ->
  form_of_ext2 (ext_of_form f) =1 f.
Proof.
move=> f_ma v.
have f_m : multilinear f. exact : (proj1 f_ma).
have f_a : alternate f. exact : (proj2 f_ma).
rewrite /form_of_ext2 /ext_of_form.
Admitted.


Lemma rowK_sub  T (p' q' p q : nat) (M : 'M[T]_(p, q)) f g k:
  row k (\matrix_(i < p', j < q') M (f i) (g j)) = \row_j (M (f k) (g j)).
Proof. by apply /rowP=> j; rewrite !mxE. Qed.

Lemma rowK_sub_hinc T (p : nat) (M : 'M[T]_(p, n)) k (S : {set 'I_n}) :
  row k (\matrix_(i < p, j < n) M i (nth ord0 (enum S) j)) =
  \row_j (M k (nth ord0 (enum S) j)).
Proof. by rewrite rowK_sub. Qed.

Lemma row_scale (R : comRingType) (a : R) (p q : nat) (M : 'M[R]_(p,q)) i :
  a *: row i M = row i (a *: M).
Proof. by rewrite !rowE scalemxAr. Qed.

Lemma row_add (R : comRingType) (p q : nat) (M N : 'M[R]_(p,q)) i :
  row i M + row i N = row i (M + N).
Proof. by rewrite !rowE mulmxDr. Qed.


Lemma multilinear_form_of_ext2 r (x : exterior) :
  multilinear (@form_of_ext2 r x).
Proof.
move=> U V W i0 b c.
rewrite !row_scale row_add; move/row_eq=> uvw.
move/row'_eq=> vu; move/row'_eq=> wu.
rewrite !big_distrr -big_split; apply: eq_bigr => s sR /=.
rewrite (mulrCA b) (mulrCA c) -mulrDr; congr (_ * _).
pose exterior_mat X : 'M[F]_(r, r) :=
   submatrix id (fun j : 'I_r => nth ord0 (enum s) j) X.
set A := exterior_mat U; set B := exterior_mat V; set C := exterior_mat W.
(* set A := submatrix _ _ U; set B := submatrix _ _ V; set C := submatrix _ _ W. *)
rewrite [LHS](@determinant_multilinear _ _ A B C i0 b c) //; do ?[
  by apply/matrixP=> i j; rewrite !mxE (vu, wu) // inE eq_sym neq_lift].
rewrite !row_scale !row_add -!submatrix_scale -submatrix_add !rowK_sub.
by apply/rowP=> j; rewrite !mxE uvw !mxE.
Qed.

Lemma alternate_form_of_ext2 r (x : exterior) : alternate (@form_of_ext2 r x).
Proof.
move=> A i1 i2 neq_i12 eqA12.
rewrite /form_of_ext2.
rewrite big1 //.
move=> s sr.
have min0 : minor id (fun j : 'I_r => (enum s)`_j) A = 0; last first.
  by rewrite min0 ?mulr0.
rewrite /minor.
rewrite (@determinant_alternate _ _ _ i1 i2) //.
by move=> j1; rewrite !mxE eqA12.
Qed.

Lemma form_of2_multilinear_alternate r (x : exterior) :
  multilinear_alternate (@form_of_ext2 r x).
Proof.
by move :
multilinear_form_of_ext2
alternate_form_of_ext2.
Qed.

Lemma multilinear_alternate_mul_form2 r s (f : r.-form) (g : s.-form) :
  multilinear_alternate (mul_form2 f g).
Proof. exact: form_of2_multilinear_alternate. Qed.

End Form.

End ExteriorDef.

Notation "x %:ext" := (to_ext x) (format "x %:ext", at level 2) : ext_scope.
Notation "r .-form[ F ^ n ]" := (form_of F n r)
  (at level 2, F at level 0, n at next level,
   format "r .-form[ F ^ n ]") : type_scope.

Arguments blade {F n'}.

Section ExteriorField.

Variable (F : fieldType).
Variable (n' : nat).
Let n := n'.+1.

Let dim  := #|{set 'I_n}|.

(** r-th exterior power *)
Definition extn r : 'M[F]_dim :=
  (\sum_(s : {set 'I_n} | #|s| == r) <<blade s>>)%MS.

Lemma extnP {u : exterior F n'} {r} :
  reflect (u = \sum_(s : {set 'I_n} | #|s| == r) (u 0 (enum_rank s) *: blade s))
          (u <= extn r)%MS.
Proof.
apply: (iffP (complex.sub_sums_genmxP _ _ _))=> [[/= u_ ->]|u_eq]; last first.
  exists (fun A : {set 'I_n} => u``_(enum_rank A)%:M).
  by rewrite [LHS]u_eq; apply: eq_bigr=> //= ??; rewrite mul_scalar_mx.
apply: eq_bigr=> A cAr; rewrite summxE (bigD1 A) //= !mxE big_ord1 blade_eq //.
rewrite mulr1 big1; first by rewrite addr0 -mul_scalar_mx -mx11_scalar.
by move=> B /andP[_ neqBA]; rewrite mxE big_ord1 blade_diff 1?eq_sym ?mulr0.
Qed.

Lemma extn_mul r s (u v : (@exterior F n')) :
  (u <= extn r)%MS -> (v <= extn s)%MS -> ((u * v)%R <= extn (r + s)%N)%MS.
Proof.
move => /extnP -> /extnP ->.
rewrite mulr_suml summx_sub // => I Ir.
rewrite mulr_sumr summx_sub // => J Js.
rewrite -scalerAr -scalerAl !scalemx_sub // mul_blades.
have [dIJ|/signND->] := boolP [disjoint I & J]; last by rewrite scale0r sub0mx.
rewrite scalemx_sub // /extn.
apply /extnP; rewrite (bigD1 (I :|: J)) /=; last first.
  by rewrite -(eqP Ir) -(eqP Js) leq_card_setU. 
rewrite blade_eq // scale1r big1 ?addr0 //.
by move=> K /andP[_ KIJ]; rewrite blade_diff ?scale0r.
Qed.

(** Stability by addition, already exists *)
Lemma extn_add r (u v : (@exterior F n')) :
  (u <= extn r)%MS -> (v <= extn r)%MS -> ((u + v)%R <= extn r)%MS.
Proof.
move=> /extnP -> /extnP ->.
rewrite -big_split /=.
apply /extnP; apply eq_bigr=> S Sr; rewrite summxE (bigD1 S) //= !mxE /=.
rewrite big1; last first.
 - move=> R /andP[_ neqRS]; rewrite !mxE /=.
   by admit.
admit.
Admitted.


(* Notation "'Λ_r" := (extn r) (only parsing): type_scope. *)
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


(** The exterior algebra is the direct sum of the i-th exterior power as modules *)
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

Lemma ext_of_form_extn r (f : r.-form[F ^ n']) : (ext_of_form f <= extn r)%MS.
Proof.
apply /extnP; rewrite /ext_of_form.
apply : eq_bigr => S Sr. 
rewrite !summxE (bigD1 S) ?mxE ?big1 ?addr0 //=; last first.
  - by move=> K /andP[_  neqKS]; rewrite mxE blade_diff ?mulr0 // eq_sym.
congr( _ *: _); rewrite addr0.
Admitted.

Hint Resolve ext_of_form_extn. 




Lemma form_of_extK2 r (u : exterior F n') :  (* u = \sum_(s : {set 'I_n} | #|s| == r) u 0 (enum_rank s) *: (blade s) *)
(u <= extn r)%MS
 -> ext_of_form (@form_of_ext2 F n' r u) = u.
Proof.
move=> /extnP uinextr.
rewrite /ext_of_form (* /form_of_ext2 *) [in RHS]uinextr.
apply: eq_bigr=> s sr; congr ( _ *: _ ).
have size_ees: size (enum s) = r by rewrite -cardE (eqP sr).
rewrite /form_of_ext2.
rewrite (bigD1 s) //=.
rewrite big1 ?addr0.
  have minor1 : minor id (fun j : 'I_r => nth ord0 (enum s) j)
    (\matrix_i [seq 'e_i0 | i0 <- enum s]`_i : 'M[F]__) = 1; last first.
    by rewrite minor1 mulr1.
  (* expand_det_(row || col) *)
  rewrite /minor [X in \det X](_ : _ = 1%:M) ?det1 //.
  apply/matrixP=> i j; rewrite !mxE (nth_map 0) ?size_ees // mxE eqxx /=.
  by rewrite nth_uniq ?size_ees // 1?eq_sym // enum_uniq.
move=> A /andP [Ar A_neqs].
have minor0 (B : {set _}) : #|B| = #|s| -> B != s ->
  minor id (fun j : 'I_r => nth ord0 (enum B) j)
    (\matrix_i [seq ('e_i0 : 'M[F]__) | i0 <- enum s]`_i) = 0; last first.
  by rewrite minor0 ?mulr0 // (eqP Ar) (eqP sr).
move=> Bs neq_Bs; have: B :\: s != set0.
  apply: contra_neq neq_Bs=> /eqP; rewrite setD_eq0.
  by move=> /subset_leqif_cards; rewrite Bs => /leqif_refl /eqP.
have size_eeB: size (enum B) = r by rewrite -cardE Bs (eqP sr).
move=> /set0Pn [k]; rewrite inE => /andP [kNs kB]; rewrite /minor.
set k' := index k (enum B).
have k'lt : (k' < r)%N by rewrite -size_eeB index_mem mem_enum kB.
rewrite (expand_det_col _ (Ordinal k'lt)) big1 // => i _.
rewrite !mxE (nth_map 0) ?size_ees // mxE eqxx /=.
rewrite nth_index ?mem_sort ?mem_enum //.
have [k_eq|] := altP eqP; last by rewrite mul0r.
have: {subset enum s <= s} by move=> ?; rewrite mem_enum.
by move=> /(_ k); rewrite (negPf kNs) k_eq mem_nth ?size_ees // => /(_ isT).
Qed.


(** morphism *)
Lemma mul_ext_form2 r s (f : r.-form[F ^ n']) (g : s.-form[F ^ n']) :
  ext_of_form (mul_form2 f g) =1 (ext_of_form f) * (ext_of_form g).
Proof.
by rewrite /mul_form2 form_of_extK2 ?extn_mul.
Qed.

Lemma add_ext_form2 r (f : r.-form[F ^ n']) (g : r.-form[F ^ n']) :
  ext_of_form (add_form2 f g) =1 (ext_of_form f) + (ext_of_form g).
Proof.
by rewrite /add_form2 form_of_extK2 ?extn_add.
Qed.
(* Definition split_form r (I : {set 'I_r}) (f : r.-form) *)
(*            (v : 'M_(r - #|I|,n)) : #|I|.-form := fun u => *)
(*   f (\matrix_k if k \in I then row k u else row k v). *)



(*   (if r isn't r'.+1 return 'I_r -> r.-form -> 'M_(r.-1,n) -> F *)
(*    then fun _ _ _ => 0 else fun k0 f v =>  *)
(*    f (\matrix_k if unlift k0 k is Some k' then row k' v else u)) *)
(*   k0 f v. *)


End ExteriorField.
End Exterior.
