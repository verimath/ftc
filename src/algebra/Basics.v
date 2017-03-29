(* $Id: Basics.v,v 1.12 2003/03/11 13:35:50 lcf Exp $ *)

Require Export Omega.
Require Export Even.
Require Export Max.
Require Export Min.

(* Tex_Prose
\chapter{Basics}
This is random stuff that should be in the Coq basic library.
*)

(* Begin_Tex_Verb *)
Lemma lt_le_dec:(n,m:nat){lt n m}+{le m n}.
(* End_Tex_Verb *)
Intros.
Case (le_lt_dec m n); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_z_two: (lt O (2)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma le_pred : (n,m:nat)(le n m)->(le (pred n)(pred m)).
(* End_Tex_Verb *)
Proof.
Induction n. Simpl. Auto with arith.
Intros n0 Hn0. Induction m. Simpl. Intro H. Inversion H.
Intros n1 H H0. Simpl. Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_mult_right :
  (x,y,z:nat) (lt x y) -> (lt (0) z) -> (lt (mult x z) (mult y z)).
(* End_Tex_Verb *)
Intros x y z H H0.
Induction z.
Elim (lt_n_n ? H0).
Rewrite mult_sym.
Replace (mult y (S z)) with (mult (S z) y); Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma le_mult_right : (x,y,z:nat)(le x y)->(le (mult x z) (mult y z)).
(* End_Tex_Verb *)
Intros x y z H.
Rewrite mult_sym. Rewrite (mult_sym y).
Auto with arith.
Qed.

(* Tex_Prose
Factorial function. Does not exist in Arith.
Needed for special operations on polynomials.
*)
(* Begin_Tex_Verb *)
Fixpoint fac [n:nat] :nat :=
	Cases n of
	   O 		=> (S O)
	   | (S m)	=> (mult (S m)(fac m))
	end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma nat_fac_gtzero:(n:nat)(lt O (fac n)).
(* End_Tex_Verb *)
Proof.
Induction n; Simpl; Auto with arith.
Qed.

(* needed for computational behavior of "Inversion" tactic *)
Transparent sym_eq.
Transparent f_equal.

Syntactic Definition Pair := (pair ??).
Syntactic Definition Proj1 := (proj1 ??).
Syntactic Definition Proj2 := (proj2 ??).

(* Following only needed in finite, but tha's now obsolete

* Begin_Tex_Verb *
Lemma deMorgan_or_and: (A,B,X:Prop)((A\/B)->X) -> (A->X)/\(B->X).
* End_Tex_Verb *
Tauto.
Qed.

* Begin_Tex_Verb *
Lemma deMorgan_and_or: (A,B,X:Prop)(A->X)/\(B->X) -> (A\/B->X).
* End_Tex_Verb *
Tauto.
Qed.

* Begin_Tex_Verb *
Lemma deMorgan_ex_all:
  (A:Set)(P:A->Prop)(X:Prop)((Ex P)->X) -> (a:A)(P a)->X.
* End_Tex_Verb *
Intros. Apply H; Exists a; Assumption.
Qed.

* Begin_Tex_Verb *
Lemma deMorgan_all_ex:
  (A:Set)(P:A->Prop)(X:Prop)((a:A)(P a)->X) -> (Ex P)->X.
* End_Tex_Verb *
Intros. Elim H0; Assumption.
Qed.

Implicit Arguments Off.

* Tex_Prose
Three lemmas for proving properties about definitions made with case
distinction to a sumbool, i.e. \verb!{A} + {B}!.
*
* Begin_Tex_Verb *
Lemma sumbool_rec_or : (A,B:Prop)(S:Set)(l,r:S)(s:{A}+{B})
                  (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r s) = l \/
                  (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r s) = r.
* End_Tex_Verb *
Intros. Elim s.
Intros. Left. Reflexivity.
Intros. Right. Reflexivity.
Qed.
*)
(* Begin_Tex_Verb *)
Lemma not_r_sumbool_rec : (A,B:Prop)(S:Set)(l,r:S)~B->(H:{A}+{B})
                  (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r H) = l.
(* End_Tex_Verb *)
Intros. Elim H0.
Intros. Reflexivity.
Intro. Elim H. Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma not_l_sumbool_rec : (A,B:Prop)(S:Set)(l,r:S)~A->(H:{A}+{B})
                          (sumbool_rec A B [_:{A}+{B}]S [x:A]l [x:B]r H) = r.
(* End_Tex_Verb *)
Intros. Elim H0.
Intro. Elim H. Assumption.
Intros. Reflexivity.
Qed.

Implicit Arguments On.

(* Tex_Prose
\section{Some results about Z}
*)

(* Tex_Prose
We consider the injection \verb!inject_nat! from \verb!nat! to !Z! as a
coercion.
*)
Coercion inject_nat: nat>->Z.

(* Begin_Tex_Verb *)
Lemma POS_anti_convert :
  (n:nat)`(S n) = (POS (anti_convert n))`.
(* End_Tex_Verb *)
Induction n.
Simpl.
Reflexivity.
Intros n0 H.
Simpl.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma NEG_anti_convert :
  (n:nat)`-(S n) = (NEG (anti_convert n))`.
(* End_Tex_Verb *)
Induction n.
Simpl.
Reflexivity.
Intros n0 H.
Simpl.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_O_positive_to_nat :
  (p:positive)(m:nat)(lt O m)->(lt O (positive_to_nat p m)).
(* End_Tex_Verb *)
Intro p.
Elim p.
Intros p0 H m H0.
Simpl.
Auto with arith.
Intros p0 H m H0.
Simpl.
Apply H.
Auto with arith.
Intros m H.
Simpl.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma anti_convert_pred_convert :
  (p:positive)(p = (anti_convert (pred (convert p)))).
(* End_Tex_Verb *)
Intro p.
Pattern 1 p.
Rewrite <- bij3.
Cut (EX n:nat | (convert p) = (S n)).

Intro H.
Elim H; Intros x H0.
Rewrite H0.
Elim x.

Simpl.
Reflexivity.

Intros n H1.
Simpl.
Rewrite sub_add_one.
Reflexivity.

Exists (pred (convert p)).
Apply S_pred with O.
Unfold convert.
Apply lt_O_positive_to_nat.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma p_is_some_anti_convert : (p:positive)(EX n:nat | p = (anti_convert n)).
(* End_Tex_Verb *)
Intro p.
Exists (pred (convert p)).
Apply anti_convert_pred_convert.
Qed.

(* Begin_Tex_Verb *)
Lemma convert_is_POS :
              (p:positive)`(convert p) = (POS p)`.
(* End_Tex_Verb *)
Intro p.
Elim (p_is_some_anti_convert p).
Intros x H.
Rewrite H.
Rewrite bij1.
Apply POS_anti_convert.
Qed.

(* Begin_Tex_Verb *)
Lemma min_convert_is_NEG :
              (p:positive)`-(convert p) = (NEG p)`.
(* End_Tex_Verb *)
Intro p.
Elim (p_is_some_anti_convert p).
Intros x H.
Rewrite H.
Rewrite bij1.
Apply NEG_anti_convert.
Qed.

(* Begin_Tex_Verb *)
Lemma Z_exh : (z:Z)(EX n:nat | z=n) \/ (EX n:nat | z=`-n`).
(* End_Tex_Verb *)
Intro z.
Elim z.

Left.
Exists O.
Auto.

Intro p.
Left.
Exists (convert p).
Rewrite convert_is_POS.
Reflexivity.

Intro p.
Right.
Exists (convert p).
Rewrite min_convert_is_NEG.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma nats_Z_ind :
                 (P:Z->Prop)((n:nat)(P n)) -> ((n:nat)(P `-n`)) -> (z:Z)(P z).
(* End_Tex_Verb *)
Intros P H H0 z.
Elim (Z_exh z); Intro H1.

Elim H1; Intros x H2.
Rewrite H2.
Apply H.

Elim H1; Intros x H2.
Rewrite H2.
Apply H0.
Qed.

(* Begin_Tex_Verb *)
Lemma pred_succ_Z_ind : (P:Z->Prop)(P `0`) ->
                                   ((n:Z)(P n)->(P `n+1`)) ->
                                   ((n:Z)(P n)->(P `n-1`)) ->
                                   (z:Z)(P z).
(* End_Tex_Verb *)
Intros P H H0 H1 z.
Apply nats_Z_ind.

Intro n.
Elim n.

Exact H.

Intros n0 H2.
Replace ((S n0)::Z) with `n0+1`.

Apply H0.
Assumption.

Rewrite inj_S.
Reflexivity.

Intro n.
Elim n.

Exact H.

Intros n0 H2.
Replace `-(S n0)` with `-n0-1`.

Apply H1.
Assumption.

Rewrite inj_S.
Unfold Zs.
Rewrite Zopp_Zplus.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma Zmult_minus_distr_r : (n,m,p:Z)`p*(n-m) = p*n-p*m`.
(* End_Tex_Verb *)
Intros n m p.
Rewrite Zmult_sym.
Rewrite Zmult_minus_distr.
Rewrite Zmult_sym.
Pattern `m*p`.
Rewrite Zmult_sym.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma Zodd_Zeven_min1 : (x:Z)(Zodd x) -> (Zeven `x-1`).
(* End_Tex_Verb *)
Intro x.
Elim x.

Simpl.
Auto.
Induction p.

Simpl.
Auto.

Intros p0 H H0.
Simpl in H0.
Tauto.

Simpl; Auto.

Induction p.

Simpl; Auto.

Simpl; Auto.

Auto.
Qed.

Implicit Arguments On.

(* Begin_Tex_Verb *)
Definition caseZ_diff := [A:Set][z:Z][f:nat->nat->A]
  Cases z of
    ZERO => (f O O)
  | (POS m) => (f (convert m) O)
  | (NEG m) => (f O (convert m))
  end.
(* End_Tex_Verb *)
Implicit Arguments Off.

(* Begin_Tex_Verb *)
Lemma caseZ_diff_O : (A:Set)(f:nat->nat->A)(caseZ_diff `0` f) = (f O O).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma caseZ_diff_Pos : (A:Set)(f:nat->nat->A)(n:nat)
                       (caseZ_diff `n` f) = (f n O).
(* End_Tex_Verb *)
Intros A f n.
Elim n.

Reflexivity.

Intros n0 H.
Simpl.
Rewrite bij1.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma caseZ_diff_Neg : (A:Set)(f:nat->nat->A)(n:nat)
                       (caseZ_diff `-n` f) = (f O n).
(* End_Tex_Verb *)
Intros A f n.
Elim n.

Reflexivity.

Intros n0 H.
Simpl.
Rewrite bij1.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma proper_caseZ_diff : (A:Set)(f:nat->nat->A)
              ((m,n,p,q:nat)(plus m q) = (plus n p) -> (f m n) = (f p q)) ->
              (m,n:nat)(caseZ_diff `m-n` f) = (f m n).
(* End_Tex_Verb *)
Intros A F H m n.
Pattern m n.
Apply nat_double_ind.

Intro n0.
Replace `O-n0` with `-n0`.

Rewrite caseZ_diff_Neg.
Reflexivity.

Simpl.
Reflexivity.

Intro n0.
Replace `(S n0)-O` with (inject_nat `(S n0)`).

Rewrite caseZ_diff_Pos.
Reflexivity.

Simpl.
Reflexivity.

Intros n0 m0 H0.
Rewrite H with (S n0) (S m0) n0 m0.

Rewrite <- H0.
Replace `(S n0)-(S m0)` with `n0-m0`.

Reflexivity.

Repeat Rewrite inj_S.
Auto with zarith.

Auto with zarith.
Qed.

(* Begin_Tex_Verb *)
Lemma diff_Z_ind : (P:Z->Prop)((m,n:nat)(P `m-n`)) -> ((z:Z)(P z)).
(* End_Tex_Verb *)
Intros P H z.
Apply nats_Z_ind.

Intro n.
Replace (inject_nat `n`) with `n-O`.

Apply H.

Simpl.
Auto with zarith.

Intro n.
Replace `-n` with `O-n`.

Apply H.

Simpl.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma Zlt_reg_mult_l: (x,y,z:Z)`x>0`->`y<z`->`x*y < x*z`.
(* End_Tex_Verb *)
Proof.
 Intros x y z H H0.
 Case (SUPERIEUR_POS x `0`).

 Unfold Zgt in H.
 Assumption.

 Intros x0 H1.
 Cut (`x = (POS x0)`).

 Intro H2.
 Rewrite H2.
 Unfold Zlt in H0.
 Unfold Zlt.
 Cut ( (Zcompare `(POS x0)*y` `(POS x0)*z`) = (Zcompare y z)).

 Intro H3.
 Exact (trans_eq relation `(POS x0)*y ?= (POS x0)*z` `y ?= z`  INFERIEUR H3 H0).

 Apply Zcompare_Zmult_compatible.

 Cut (`x = x + (Zopp 0)`).
 Intro H2.
 Exact ( trans_eq Z x `x+(Zopp 0)` (POS x0) H2 H1).

 Simpl.
 Apply (sym_eq Z).
 Exact (Zero_right x).
Qed.


(* Begin_Tex_Verb *)
Lemma Zlt_opp: (x,y:Z)`x<y`->`(-x)>(-y)`.
(* End_Tex_Verb *)
Proof.
 Intros x y H.
 Red.
 Apply sym_eq.
 Cut(SUPERIEUR =(Zcompare y x)).

 Intro H0.
 Cut ((Zcompare y x)=(Zcompare (Zopp x) (Zopp y))).

 Intro H1.
 Exact (trans_eq relation SUPERIEUR (Zcompare y x) (Zcompare (Zopp x) (Zopp y)) H0 H1). 

 Exact (Zcompare_Zopp y x).

 Apply sym_eq.
 Exact (Zlt_gt x y H).
Qed.

(* Begin_Tex_Verb *)
Lemma Zlt_conv_mult_l :(x,y,z:Z)`x<0`->`y<z`->`x*y>x*z`.
(* End_Tex_Verb *)
Proof.
 Intros x y z H H0.
 Cut (`(-x)>0`).

 Intro H1.
 Cut (`(-x)*y<(-x)*z`).

 Intro H2.
 Cut (`(-((-x)*y))>(-((-x)*z))`).

 Intro H3.
 Cut (`(-(-(x*y)))>(-(-(x*z)))`).

 Intro H4.
 Cut (`(-(-(x*y)))=x*y`).

 Intro H5.
 Rewrite H5 in H4.
 Cut (`(-(-(x*z)))=x*z`).

 Intro H6.
 Rewrite H6 in H4.
 Assumption.

 Exact (Zopp_Zopp (`x*z`)).

 Exact (Zopp_Zopp (`x*y`)).

 Cut (`(-((-x)*y))=(-(-(x*y)))`).
 Intro H4.
 Rewrite H4 in H3.
 Cut (`(-((-x)*z))=(-(-(x*z)))`).

 Intro H5.
 Rewrite H5 in H3.
 Assumption.

 Cut (`(-x)*z=(-(x*z))`).
 Intro H5.
 Exact (f_equal Z Z Zopp `(-x)*z` `(-(x*z))` H5).

 Exact (Zopp_Zmult x z).

 Cut (`(-x)*y=(-(x*y))`).
 Intro H4.

 Exact (f_equal Z Z Zopp `(-x)*y` `(-(x*y))` H4).

 Exact (Zopp_Zmult x y).

 Exact (Zlt_opp `(-x)*y` `(-x)*z` H2).

 Exact (Zlt_reg_mult_l `(-x)` y z H1 H0).

 Exact (Zlt_opp x `0` H).
Qed.

(* Begin_Tex_Verb *)
Lemma Zgt_not_eq :(x,y:Z)`x>y`->(~(x=y)).
(* End_Tex_Verb *)
Proof.
 Intros x y H.
 Cut (`y<x`).

 Intro H0.
 Cut (`y<>x`).

 Intro H1.
 Red.
 Intro H2.
 Cut (`y=x`).

 Intro H3.
 Apply H1.
 Assumption.

 Exact (sym_eq Z x y H2).

 Exact (Zlt_not_eq y x H0).

 Exact (Zgt_lt x y H).
Qed.

(* Begin_Tex_Verb *)
Lemma Zmult_absorb : (x,y,z: Z)~(x=ZERO)->(Zmult x y)=(Zmult x z)->y=z.
(* End_Tex_Verb *)
Proof.
 Intros x y z H H0.
 Case (dec_eq y z).

 Intro H1.
 Assumption.

 Intro H1.
 Case (not_Zeq y z).

 Assumption.

 Intro H2.
 Case (not_Zeq x `0`).

 Assumption.

 Intro H3.
 ElimType False.
 Cut (`x*y>x*z`).

 Intro H4.
 Cut (`x*y <> x*z`).

 Intro H5.
 Apply H5.
 Assumption.

 Exact (Zgt_not_eq `x*y` `x*z` H4 ).

 Exact (Zlt_conv_mult_l x y z H3 H2).

 Intro H3.
 ElimType False.
 Cut (`x*y<x*z`).

 Intro H4.
 Cut(`x*y<>x*z`).

 Intro H5.
 Apply H5.
 Assumption.

 Exact (Zlt_not_eq `x*y` `x*z` H4).

 Apply Zlt_reg_mult_l.

 Exact (Zlt_gt `0` x H3).

 Assumption.

 Intro H2.
 Apply False_ind.
 Cut(`x*z<x*y`).

 Intro H3.
 Cut(`x*z<>x*y`).

 Intro H4.
 Apply H4.
 Apply (sym_eq Z).
 Assumption.

 Exact (Zlt_not_eq `x*z` `x*y` H3).

 Apply False_ind.
 Case (not_Zeq x `0`).

 Assumption.

 Intro H3.
 Cut(`x*z>x*y`).

 Intro H4.
 Cut (`x*z<>x*y`).

 Intro H5.
 Apply H5.
 Apply (sym_eq Z).
 Assumption.

 Exact (Zgt_not_eq `x*z` `x*y` H4).

 Exact (Zlt_conv_mult_l x z y H3 H2).

 Intro H3.
 Cut(`x*z<x*y`).

 Intro H4.
 Cut (`x*z<>x*y`).

 Intro H5.
 Apply H5.
 Apply (sym_eq Z).
 Assumption.

 Exact (Zlt_not_eq `x*z` `x*y` H4).

 Apply Zlt_reg_mult_l.

 Exact (Zlt_gt `0` x H3).
 Auto.
Qed.
