(* $Id: IntegralLemmas.v,v 1.14 2003/03/11 13:36:04 lcf Exp $ *)

Require Export Partitions.

Section Lemmas.

(* Tex_Prose
\chapter{Lemmas for Integration}

In this file we prepare the way for the definition of integral with lots of (very) technical stuff.

\begin{convention} Throughout this section, let \verb!a,b:IR! and \verb!I!$=[a,b]$.
\end{convention}

\section{Lemmas}
*)

(* Begin_Tex_Verb *)
Lemma not_to_CNot : (P:Prop)(toCProp ~P)->~P.
(* End_Tex_Verb *)
Intros.
Apply toCProp_e with ~P; Auto.
Qed.

(* Tex_Prose
We now prove that any two strictly ordered sets of points which have an empty intersection can be ordered as one (this will be the core of the proof that any two partitions with no common point have a common refinement).  The lemmas are too technical and completely uninteresting, so we won't even show their statement.
*)

Definition pred_well_def' := [S:CSetoid; P:(S->Prop)](x,y:S)(P x)->(x [=] y)->(P y).

Variable F:COrdField.

Local ordered_insertion_fun [n:nat][f:(i:nat)(lt i n)->F][x:F] : (i:nat)(lt i (S n))->F.
Intros.
Red in H.
Elim (le_lt_eq_dec ?? H); Intro.
Apply (f i (lt_S_n ?? a)).
Apply x.
Defined.

(* Begin_Tex_Verb *)
Lemma ordered_insertion
(* End_Tex_Verb *)
 : (n:nat)(f:(i:nat)(lt i n)->F)(nat_less_n_fun ?? f)->
  ((i,i':nat)(Hi:(lt i n))(Hi':(lt i' n))(lt i i')->((f i Hi)[<](f i' Hi')))->
  (x:F)(((i:nat)(Hi:(lt i n))(f i Hi)[#]x)->
  {h:(i:nat)(lt i (S n))->F &
    {nat_less_n_fun ?? h}*
    {(P:F->Prop)(pred_well_def' F P)->((i:nat)(Hi:(lt i n))(P (f i Hi)))->(P x)->
      (j:nat)(Hj:(lt j (S n)))(P (h j Hj))}*
    ((P:F->CProp)(pred_well_def F P)->((i:nat)(Hi:(lt i n))(P (f i Hi)))->(P x)->
      (j:nat)(Hj:(lt j (S n)))(P (h j Hj)))*
    ((i,i':nat)(Hi:(lt i (S n)))(Hi':(lt i' (S n)))(lt i i')->((h i Hi)[<](h i' Hi')))*
    ((P:F->Prop)(pred_well_def' F P)->({i:nat & {Hi:(Clt i n) | (P (f i (Clt_to ?? Hi)))}}+{P x})->
      {j:nat & {Hj:(Clt j (S n)) | (P (h j (Clt_to ?? Hj)))}})*
    ((P:F->CProp)(pred_well_def F P)->({i:nat & {Hi:(Clt i n) & (P (f i (Clt_to ?? Hi)))}}+(P x))->
      {j:nat & {Hj:(Clt j (S n)) & (P (h j (Clt_to ?? Hj)))}})}).
Induction n.
Intros.
Exists [i:nat][Hi:(lt i (1))]x.
Repeat Split.
Red; Intros; Algebra.
Intros; Assumption.
Intros; Assumption.
Intros; ElimType False.
Inversion Hi'.
Rewrite H4 in H2; Inversion H2.
Inversion H4.
Intros.
Inversion_clear H3.
Elim H4; Intros i Hi; Elim Hi; Intros.
Cut (lt i O); [Intro; ElimType False; Inversion H3 | Exact (Clt_to ?? x0)].
Exists O; Exists (toCProp_lt ?? (lt_n_Sn O)); Assumption.
Intros.
Inversion_clear H3.
Elim H4; Intros i Hi; Elim Hi; Intros.
Cut (lt i O); [Intro; ElimType False; Inversion H3 | Exact (Clt_to ?? x0)].
Exists O; Exists (toCProp_lt ?? (lt_n_Sn O)); Assumption.
Clear n; Intros.
Elim (ap_imp_less ??? (H2 n (lt_n_Sn n))); Intro.
Exists (ordered_insertion_fun ? f x); Unfold ordered_insertion_fun.
Repeat Split.
Red; Do 3 Intro.
Rewrite H3; Intros.
Elim (le_lt_eq_dec ?? H4); Elim (le_lt_eq_dec ?? H'); Intros; Simpl.
Apply H0; Auto.
ElimType False; Rewrite b in a0; Exact (lt_n_n ? a0).
ElimType False; Rewrite b in a0; Exact (lt_n_n ? a0).
Algebra.
Intros.
Elim (le_lt_eq_dec ?? Hj); Intro; Simpl.
Apply H4.
Assumption.
Intros.
Elim (le_lt_eq_dec ?? Hj); Intro; Simpl.
Apply H4.
Assumption.
Intros.
Elim (le_lt_eq_dec ?? Hi); Elim (le_lt_eq_dec ?? Hi'); Intros; Simpl.
Apply H1; Auto.
EApply leEq_less_trans.
2: Apply a.
Cut (le i n); Intros.
Elim (le_lt_eq_dec ?? H4); Intro.
Apply less_leEq; Apply H1; Assumption.
Apply eq_imp_leEq; Apply H0; Assumption.
Do 2 Apply le_S_n; Auto.
ElimType False; Omega.
ElimType False; Omega.
Intros.
Inversion_clear H4.
Elim H5; Clear H5; Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i.
Exists (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hi))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hi))))); Intro; Simpl.
EApply H3.
Apply Hi'.
Apply H0; Reflexivity.
LetTac H4:=(Clt_to ?? Hi).
ElimType False; ClearBody H4; Inversion b.
Clear Hi'; Rewrite H6 in H4; Exact (lt_n_n ? H4).
Exists (S n); Exists (toCProp_lt ?? (lt_n_Sn (S n))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_n_Sn (S n))))); Intro; Simpl.
ElimType False; Exact (lt_n_n ? a0).
Assumption.
Intros.
Inversion_clear H4.
Elim H5; Clear H5; Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i.
Exists (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hi))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hi))))); Intro; Simpl.
EApply H3.
Apply Hi'.
Apply H0; Reflexivity.
LetTac H4:=(Clt_to ?? Hi).
ElimType False; ClearBody H4; Inversion b.
Clear Hi'; Rewrite H6 in H4; Exact (lt_n_n ? H4).
Exists (S n); Exists (toCProp_lt ?? (lt_n_Sn (S n))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_n_Sn (S n))))); Intro; Simpl.
ElimType False; Exact (lt_n_n ? a0).
Assumption.
LetTac f':=[i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)).
Cut (nat_less_n_fun ?? f'); Intro.
2: Intros; Unfold f'; Apply H0; Assumption.
Cut (i,i':nat)(Hi:(lt i n))(Hi':(lt i' n))(lt i i')->(f' i Hi)[<](f' i' Hi'); Intros.
2: Unfold f'; Apply H1; Assumption.
Elim (H f' H3 H4 x).
2: Intros; Unfold f'; Apply H2.
Intros h' Hh'.
Elim Hh'; Clear Hh'; Intros Hh' Hh'1.
Elim Hh'; Clear Hh'; Intros Hh' Hh'0.
Elim Hh'; Clear Hh'; Intros Hh' Hh'2.
Elim Hh'; Clear Hh'; Intros Hh'2a Hh'2b.
Elim Hh'2a; Clear Hh'2a; Intros Hh' Hh''.
Exists (ordered_insertion_fun ? h' (f n (lt_n_Sn n))); Unfold ordered_insertion_fun.
Repeat Split.
Red; Do 3 Intro.
Rewrite H5; Intros.
Elim (le_lt_eq_dec ?? H6); Elim (le_lt_eq_dec ?? H'); Intros; Simpl.
Apply Hh'; Auto.
ElimType False; Rewrite b0 in a; Exact (lt_n_n ? a).
ElimType False; Rewrite b0 in a; Exact (lt_n_n ? a).
Algebra.
Intros.
Elim (le_lt_eq_dec ?? Hj); Intro; Simpl.
Apply Hh''.
Intros; Unfold f'; Apply H5.
Intros; Unfold f'; Apply H6.
Assumption.
Apply H6.
Intros.
Elim (le_lt_eq_dec ?? Hj); Intro; Simpl.
Apply Hh'2b.
Intros; Unfold f'; Apply H5.
Intros; Unfold f'; Apply H6.
Assumption.
Apply H6.
Intros.
Elim (le_lt_eq_dec ?? Hi); Elim (le_lt_eq_dec ?? Hi'); Intros; Simpl.
Apply Hh'2; Auto.
Apply leEq_less_trans with (h' ? (lt_n_Sn ?)).
Elim (le_lt_eq_dec ?? a); Intro.
Apply less_leEq; Apply Hh'2; Do 2 Apply lt_S_n; Auto.
Apply eq_imp_leEq; Apply Hh'; Do 2 Apply eq_add_S; Auto.
Apply Hh'2b.
Red; Intros.
Apply less_wdl with x0; Assumption.
Clear a b0 H5 Hi' Hi i' i.
Intros; Unfold f'; Apply H1; Assumption.
Assumption.
ElimType False; Omega.
ElimType False; Omega.
Intros.
Inversion_clear H6.
Elim H7; Clear H7; Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Elim (le_lt_eq_dec ?? (Clt_to ?? Hi)); Intro.
Cut {i:nat & {Hi:(Clt i n) | (P (f' i (Clt_to ?? Hi)))}}+{P x}; [Intro | Left].
Elim (Hh'0 ? H5 H6); Intros j Hj.
Elim Hj; Clear Hj; Intros Hj Hj'.
Exists j; Exists (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))))); Intro; Simpl.
EApply H5.
Apply Hj'.
Apply Hh'; Reflexivity.
ElimType False.
LetTac H7:=(Clt_to ?? Hj).
Clear Hj'; Omega.
Unfold f'.
Cut (lt i n); [Intro | Auto with arith].
Exists i; Exists (toCProp_lt ?? H6).
EApply H5.
Apply Hi'.
Apply H0; Reflexivity.
Exists (S n); Exists (toCProp_lt ?? (lt_n_Sn (S n))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_n_Sn (S n))))); Intro; Simpl.
ElimType False; Exact (lt_n_n ? a).
EApply H5.
Apply Hi'.
Apply H0; Auto.
Cut {i:nat & {Hi:(Clt i n) | (P (f' i (Clt_to ?? Hi)))}}+{P x}; [Intro | Right; Assumption].
Elim (Hh'0 ? H5 H6); Intros j Hj.
Elim Hj; Clear Hj; Intros Hj Hj'.
Exists j; Exists (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))))); Intro; Simpl.
EApply H5.
Apply Hj'.
Apply Hh'; Reflexivity.
ElimType False.
Apply (lt_n_n (S j)).
Pattern 2 (S j); Rewrite b0; Apply lt_n_S.
Apply Clt_to; Auto.
Intros.
Inversion_clear H6.
Elim H7; Clear H7; Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Elim (le_lt_eq_dec ?? (Clt_to ?? Hi)); Intro.
Cut {i:nat & {Hi:(Clt i n) & (P (f' i (Clt_to ?? Hi)))}}+(P x); [Intro | Left].
Elim (Hh'1 ? H5 H6); Intros j Hj.
Elim Hj; Clear Hj; Intros Hj Hj'.
Exists j; Exists (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))))); Intro; Simpl.
EApply H5.
Apply Hj'.
Apply Hh'; Reflexivity.
ElimType False.
LetTac H7:=(Clt_to ?? Hj).
Clear Hj'; Omega.
Unfold f'.
Cut (lt i n); [Intro | Auto with arith].
Exists i; Exists (toCProp_lt ?? H6).
EApply H5.
Apply Hi'.
Apply H0; Reflexivity.
Exists (S n); Exists (toCProp_lt ?? (lt_n_Sn (S n))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_n_Sn (S n))))); Intro; Simpl.
ElimType False; Exact (lt_n_n ? a).
EApply H5.
Apply Hi'.
Apply H0; Auto.
Cut {i:nat & {Hi:(Clt i n) & (P (f' i (Clt_to ?? Hi)))}}+(P x); [Intro | Right; Assumption].
Elim (Hh'1 ? H5 H6); Intros j Hj.
Elim Hj; Clear Hj; Intros Hj Hj'.
Exists j; Exists (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))).
Elim (le_lt_eq_dec ?? (Clt_to ?? (toCProp_lt ?? (lt_S ?? (Clt_to ?? Hj))))); Intro; Simpl.
EApply H5.
Apply Hj'.
Apply Hh'; Reflexivity.
ElimType False.
Apply (lt_n_n (S j)).
Pattern 2 (S j); Rewrite b0; Apply lt_n_S.
Apply Clt_to; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma can_be_ordered
(* End_Tex_Verb *)
 : (m,n:nat)(f:(i:nat)(lt i n)->F)(g:(j:nat)(lt j m)->F)(nat_less_n_fun ?? f)->(nat_less_n_fun ?? g)->
  ((i,i':nat)(Hi:(lt i n))(Hi':(lt i' n))(lt i i')->((f i Hi)[<](f i' Hi')))->
  ((j,j':nat)(Hj:(lt j m))(Hj':(lt j' m))(lt j j')->((g j Hj)[<](g j' Hj')))->
  ((i,j:nat)(Hi:(lt i n))(Hj:(lt j m))(f i Hi)[#](g j Hj))->
  {h:(i:nat)(lt i (plus m n))->F & 
    {nat_less_n_fun ?? h}*
    ((i,i':nat)(Hi:(lt i (plus m n)))(Hi':(lt i' (plus m n)))(lt i i')->((h i Hi)[<](h i' Hi')))*
    ((i:nat)(Hi:(lt i n)){j:nat & {Hj:(Clt j (plus m n)) | (f i Hi)[=](h j (Clt_to ?? Hj))}})*
    ((j:nat)(Hj:(lt j m)){i:nat & {Hi:(Clt i (plus m n)) | (g j Hj)[=](h i (Clt_to ?? Hi))}})*
    ((P:F->CProp)(pred_well_def F P)->((i:nat)(Hi:(lt i n))(P (f i Hi)))->((j:nat)(Hj:(lt j m))(P (g j Hj)))->
       (k:nat)(Hk:(lt k (plus m n)))(P (h k Hk)))*
    ((P:F->CProp)(pred_well_def F P)->
      ({i:nat & {Hi:(Clt i n) & (P (f i (Clt_to ?? Hi)))}}+{j:nat & {Hj:(Clt j m) & (P (g j (Clt_to ?? Hj)))}})->
        {k:nat & {Hk:(Clt k (plus m n)) & (P (h k (Clt_to ?? Hk)))}})*
    {((P:F->Prop)(pred_well_def' F P)->((i:nat)(Hi:(lt i n))(P (f i Hi)))->((j:nat)(Hj:(lt j m))(P (g j Hj)))->
       (k:nat)(Hk:(lt k (plus m n)))(P (h k Hk)))}*
    (P:F->Prop)(pred_well_def' F P)->
      ({i:nat & {Hi:(Clt i n) | (P (f i (Clt_to ?? Hi)))}}+{j:nat & {Hj:(Clt j m) | (P (g j (Clt_to ?? Hj)))}})->
        {k:nat & {Hk:(Clt k (plus m n)) | (P (h k (Clt_to ?? Hk)))}}}.
Induction m.
Clear m; Simpl; Intros.
Exists f.
Repeat Split.
Assumption.
Assumption.
Intros; Exists i.
Exists (toCProp_lt ?? Hi).
Apply H; Reflexivity.
Intros; ElimType False; Inversion Hj.
Do 4 Intro; Assumption.
Intros; Inversion_clear H5.
Assumption.
Inversion_clear H6.
Inversion_clear H5.
ElimType False.
LetTac Hx0:= (Clt_to ?? x0); Inversion Hx0.
Do 4 Intro; Assumption.
Intros; Inversion_clear H5.
Assumption.
Inversion_clear H6.
Inversion_clear H5.
ElimType False.
LetTac Hx0:= (Clt_to ?? x0); Inversion Hx0.
Clear m; Intro m; Intros.
LetTac g':=[j:nat][Hj:(lt j m)](g j (lt_S ?? Hj)).
Cut (nat_less_n_fun ?? g'); Intro.
2: Intros; Unfold g'; Apply H1; Assumption.
Cut (j,j':nat)(Hj:(lt j m))(Hj':(lt j' m))(lt j j')->(g' j Hj)[<](g' j' Hj'); Intros.
2: Unfold g'; Apply H3; Assumption.
Cut (i,j:nat)(Hi:(lt i n))(Hj:(lt j m))(f i Hi)[#](g' j Hj); Intros.
2: Unfold g'; Apply H4; Assumption.
Elim (H n f g' H0 H5 H2 H6 H7).
Intros h' Hh'.
Inversion_clear Hh'.
Rename H9 into h_PropEx.
Inversion_clear H8.
Rename H10 into h_PropAll.
Inversion_clear H9.
Rename H10 into h_CPropEx.
Inversion_clear H8.
Rename H10 into h_CPropAll.
Inversion_clear H9.
Rename H10 into g'_h'_Ex.
Inversion_clear H8.
Rename H10 into f_h'_Ex.
Inversion_clear H9.
Rename H10 into h'_mon.
Rename H8 into h'_less.
Elim (ordered_insertion ?? h'_less h'_mon (g ? (lt_n_Sn ?))).
Intros h Hh.
Inversion_clear Hh.
Rename H9 into H_CPropEx.
Inversion_clear H8.
Rename H10 into H_PropEx.
Inversion_clear H9.
Rename H10 into h_less.
Inversion_clear H8.
Rename H10 into H_CProp.
Inversion_clear H9.
Rename H8 into h_mon.
Rename H10 into H_Prop.
Exists h; Repeat Split.
Assumption.
Assumption.
Intros.
Elim (f_h'_Ex i Hi); Intros j Hj.
Elim Hj; Clear Hj; Intros Hj Hj'.
Cut (lt j (plus m n)); [Intro | Apply Clt_to; Assumption].
Simpl.
Apply H_PropEx with P:=[x:F](f i Hi)[=]x.
Red; Intros.
Apply eq_transitive_unfolded with x; Assumption.
Left; Exists j; Exists Hj; Exact Hj'.
Intros.
Elim (le_lt_eq_dec ?? Hj); Intro.
Cut (lt j m); [Clear a; Intro Hj' | Auto with arith].
Elim (g'_h'_Ex j Hj'); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Cut (lt i (plus m n)); [Intro | Apply Clt_to; Assumption].
Apply H_PropEx with P:=[x:F](g j Hj)[=]x.
Red; Intros.
Apply eq_transitive_unfolded with x; Assumption.
Unfold g' in Hi'.
Left; Exists i; Exists Hi.
EApply eq_transitive_unfolded.
2: Apply Hi'.
Apply H1; Reflexivity.
Apply H_PropEx with P:=[x:F](g j Hj)[=]x.
Red; Intros.
Apply eq_transitive_unfolded with x; Assumption.
Right; Apply H1; Auto.
Intros.
Simpl in Hk.
Apply H_CProp.
Assumption.
Intros; Apply h_CPropAll.
Assumption.
Assumption.
Unfold g'; Intros; Apply H10.
Apply H10.
Intros.
Apply H_CPropEx.
Assumption.
Inversion_clear H9.
Left; Apply h_CPropEx.
Assumption.
Left; Assumption.
Elim H10; Intros j Hj.
Elim Hj; Clear H10 Hj; Intros Hj Hj'.
Elim (le_lt_eq_dec ?? (Clt_to ?? Hj)); Intro.
Cut (lt j m); [Intro | Auto with arith].
Left.
Elim (g'_h'_Ex j H9); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i; Exists Hi.
EApply H8.
2: Apply Hi'.
Unfold g'.
EApply H8.
Apply Hj'.
Apply H1; Reflexivity.
Right.
EApply H8.
Apply Hj'.
Apply H1; Auto.
Intros.
Simpl in Hk.
Apply H_Prop.
Assumption.
Intros; Apply h_PropAll.
Assumption.
Assumption.
Unfold g'; Intros; Apply H10.
Apply H10.
Intros.
Apply H_PropEx.
Assumption.
Inversion_clear H9.
Left; Apply h_PropEx.
Assumption.
Left; Assumption.
Elim H10; Intros j Hj.
Elim Hj; Clear H10 Hj; Intros Hj Hj'.
Elim (le_lt_eq_dec ?? (Clt_to ?? Hj)); Intro.
Cut (lt j m); [Intro | Auto with arith].
Left.
Elim (g'_h'_Ex j H9); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i; Exists Hi.
EApply H8.
2: Apply Hi'.
Unfold g'.
EApply H8.
Apply Hj'.
Apply H1; Reflexivity.
Right.
EApply H8.
Apply Hj'.
Apply H1; Auto.
Apply h_CPropAll with P:=[x:F](x[#](g m (lt_n_Sn m))).
Red; Intros.
Step x; Assumption.
Intros; Apply H4.
Unfold g'; Intros; Apply less_imp_ap.
Apply H3; Assumption.
Qed.

Variable f:nat->nat.
Hypothesis f0 : (f O)=O.
Hypothesis f_mon : (i,j:nat)(lt i j)->(lt (f i) (f j)).

Variable h:nat->F.

(* Tex_Prose
Also, some technical stuff on Sums.  The first lemma relates two different kinds of Sums; the other two ones are variations, where the structure of the arguments is analyzed in more detail.
*)

(* Begin_Tex_Verb *)
Lemma Sumx_Sum_Sum
(* End_Tex_Verb *)
 : (n:nat)(Sumx [i:nat][H:(lt i n)](Sum (f i) (pred (f (S i))) h))[=](Sumx [i:nat][H:(lt i (f n))](h i)).
Induction n.
Rewrite f0; Simpl; Algebra.
Clear n; Intros.
Elim (le_lt_dec n O); Intro.
Cut n=O; [Clear a; Intro | Auto with arith].
Rewrite H0 in H.
Rewrite H0.
Simpl.
Step (Sum (f O) (pred (f (1))) h).
Rewrite f0.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply Sumx_to_Sum.
Pattern 1 O; Rewrite <- f0; Apply f_mon; Apply lt_n_Sn.
Red; Intros.
Rewrite H1; Algebra.
Clear H; Apply Sum_wd'; Unfold part_tot_nat_fun.
Auto with arith.
Intros.
Elim (le_lt_dec (f (1)) i); Intro; Simpl.
Cut (lt O (f (1))).
Intro; ElimType False; Omega.
Pattern 1 O; Rewrite <- f0; Apply f_mon; Apply lt_n_Sn.
Algebra.
Cut (lt O (f n)); [Intro | Rewrite <- f0; Apply f_mon; Assumption].
Simpl.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply Sumx_to_Sum.
Apply eq_transitive_unfolded with (Sum O (pred (f n)) (part_tot_nat_fun ?? [i:nat][H:(lt i (f n))](h i)))[+](Sum (f n) (pred (f (S n))) h).
Apply bin_op_wd_unfolded.
EApply eq_transitive_unfolded.
Apply H.
Apply Sumx_to_Sum.
Assumption.
Red; Intros.
Rewrite H1; Algebra.
Algebra.
Cut (f n)=(S (pred (f n))); [Intro | Apply S_pred with O; Auto].
Pattern 4 (f n); Rewrite H1.
EApply eq_transitive_unfolded.
2: Apply Sum_Sum with m:=(pred (f n)).
Apply bin_op_wd_unfolded; Apply Sum_wd'.
Rewrite <- H1; Apply lt_le_weak; Assumption.
Intros; Unfold part_tot_nat_fun.
Elim (le_lt_dec (f n) i); Intro; Simpl.
ElimType False; Omega.
Elim (le_lt_dec (f (S n)) i); Intro; Simpl.
Cut (lt (f n) (f (S n))); [Intro | Apply f_mon; Apply lt_n_Sn].
ElimType False; Apply (le_not_lt (f n) i); Auto.
Apply le_trans with (f (S n)); Auto with arith.
Algebra.
Rewrite <- H1.
Cut (lt O (f (S n))); [Intro | Rewrite <- f0; Auto with arith].
Cut (f (S n))=(S (pred (f (S n)))); [Intro | Apply S_pred with O; Auto].
Rewrite <- H3.
Apply lt_le_weak; Auto with arith.
Intros.
Unfold part_tot_nat_fun.
Elim (le_lt_dec (f (S n)) i); Intro; Simpl.
ElimType False; Omega.
Algebra.
Apply lt_trans with (f n); Auto with arith.
Red; Intros.
Rewrite H1; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma str_Sumx_Sum_Sum
(* End_Tex_Verb *)
 : (n:nat)(g:(i:nat)(Hi:(lt i n))nat->F)
  ((i,j:nat)(Hi:(lt i n))(le (f i) j)->(lt j (f (S i)))->(g i Hi j)[=](h j))->
  ((m:nat)(m=(f n))->(Sumx [i:nat][H:(lt i n)](Sum (f i) (pred (f (S i))) (g i H)))[=](Sumx [i:nat][H:(lt i m)](h i))).
Intros.
Rewrite H0.
EApply eq_transitive_unfolded.
2: Apply Sumx_Sum_Sum.
Apply Sumx_wd.
Intros.
Apply Sum_wd'.
Cut (lt O (f (S i))); [Intro | Rewrite <- f0; Auto with arith].
Cut (f (S i))=(S (pred (f (S i)))); [Intro | Apply S_pred with O; Auto].
Rewrite <- H3.
Apply lt_le_weak; Auto with arith.
Intros; Apply H.
Assumption.
Rewrite (S_pred (f (S i)) O); Auto with arith.
Rewrite <- f0; Auto with arith.
Qed.

End Lemmas.

Section More_Lemmas.

Local f' [m:nat][f:(i:nat)(le i m)->nat] : nat->nat.
Intros m f i.
Elim (le_lt_dec i m); Intro.
Apply (f i a).
Apply (plus (f m (le_n m)) i).
Defined.

(* Begin_Tex_Verb *)
Lemma str_Sumx_Sum_Sum'
(* End_Tex_Verb *)
 : (m:nat)(F:COrdField)(f:(i:nat)(le i m)->nat)(f O (le_O_n ?))=O->
  ((i,j:nat)(Hi:?)(Hj:?)i=j->(f i Hi)=(f j Hj))->
  ((i,j:nat)(Hi:?)(Hj:?)(lt i j)->(lt (f i Hi) (f j Hj)))->
  (h:(nat->F))(n:nat)(g:((i:nat)(lt i m)->nat->F))
    ((i,j:nat)(Hi:?)(Hi':?)(Hi'':?)(le (f i Hi') j)->(lt j (f (S i) Hi''))->(g i Hi j)[=](h j))->
    ((H:?)(n=(f m H)))->
  (Sumx [i:nat][H:(lt i m)](Sum (f i (lt_le_weak ?? H)) (pred (f (S i) H)) (g i H)))[=](Sumx [i:nat][_:(lt i n)](h i)).
Intros.
Cut (i:nat)(H:(le i m))(f i H)=(f' m f i).
Intros.
Apply eq_transitive_unfolded with (Sumx [i:nat][H3:(lt i m)](Sum (f' m f i) (pred (f' m f (S i))) (g i H3))).
Apply Sumx_wd; Intros.
Rewrite <- (H4 i (lt_le_weak ?? H5)); Rewrite <- (H4 (S i) H5); Apply Sum_wd'.
Rewrite <- (S_pred (f (S i) H5) (f i (lt_le_weak ?? H5)) (H1 ???? (lt_n_Sn i))).
Apply lt_le_weak; Apply H1; Apply lt_n_Sn.
Intros; Algebra.
Apply str_Sumx_Sum_Sum.
Unfold f'; Simpl.
Elim (le_lt_dec O m); Intro; Simpl.
Transitivity (f O (le_O_n m)).
Apply H0; Auto.
Apply H.
ElimType False; Inversion b.
Intros; Apply nat_local_mon_imp_mon.
Clear H5 j i; Intros.
Unfold f'.
Elim (le_lt_dec i m); Elim (le_lt_dec (S i) m); Intros; Simpl.
Apply H1; Apply lt_n_Sn.
Cut i=m; [Intro | Apply le_antisym; Auto with arith].
Generalize a; Clear a; Pattern 1 2 i; Rewrite H5; Intro.
LetTac x:=(f m a).
Cut x=(f m (le_n m)).
2: Unfold x; Apply H0; Auto.
Intro.
Rewrite <- H6.
Rewrite <- plus_n_Sm; Auto with arith.
ElimType False; Apply (le_not_lt i m); Auto with arith.
LetTac x:=(f m (le_n m)); ClearBody x; Auto with arith.
Assumption.
Intros.
Apply H2 with Hi':=(lt_le_weak ?? Hi) Hi'':=Hi.
Rewrite H4; Assumption.
Rewrite H4; Assumption.
Unfold f'.
Elim (le_lt_dec m m); Intro; Simpl.
Apply H3.
Elim (lt_n_n ? b).
Clear H3 H2 g n h; Intros.
Unfold f'.
Elim (le_lt_dec i m); Intro; Simpl.
Apply H0; Auto.
Elim (le_not_lt i m); Auto.
Qed.

(* Tex_Prose
A different version of a lemma already proved for natural numbers.
*)

(* Begin_Tex_Verb *)
Lemma weird_mon_covers : (n:nat)(f:nat->nat)
  ((i:nat)(lt (f i) n)->(lt (f i) (f (S i))))->{m:nat |
    (le n (f m)) | ((i:nat)(lt i m)->(lt (f i) n))}.
(* End_Tex_Verb *)
Intros; Induction n.
Exists O.
Auto with arith.
Intros; Inversion H0.
Elim Hrecn.
2: Auto.
Intros m Hm Hm'.
Elim (le_lt_eq_dec ?? Hm); Intro.
Exists m.
Assumption.
Auto with arith.
Exists (S m).
Apply le_lt_trans with (f m).
Rewrite b; Auto with arith.
Apply H.
Rewrite b; Apply lt_n_Sn.
Intros.
Elim (le_lt_eq_dec ?? H0); Intro.
Auto with arith.
Cut i=m; [Intro | Auto].
Rewrite b; Rewrite <- H1.
Apply lt_n_Sn.
Qed.

Variables a,b:IR.
Local I:=(compact a b).
Hypothesis Hab:(a[<=]b).

(* Tex_Prose
An interesting property: in a partition $\{a_0,\ldots,a_n\}$, if $a_i<a_j$ then $i<j$.
*)

(* Begin_Tex_Verb *)
Lemma Partition_Points_mon : (n:nat)(P:(Partition Hab n))
  (i,j:nat)(Hi,Hj:?)((Pts P i Hi)[<](Pts P j Hj))->(lt i j).
(* End_Tex_Verb *)
Intros.
Cut ~(le j i); Intro.
Apply not_ge; Auto.
ElimType False.
Apply less_irreflexive_unfolded with x:=(Pts P i Hi).
Apply less_leEq_trans with (Pts P j Hj).
Assumption.
Apply local_mon'_imp_mon'_le with f:=[i:nat][Hi:(le i n)](Pts P i Hi).
Intros; Apply prf2.
Intro; Intros; Apply prf1; Assumption.
Assumption.
Qed.

End More_Lemmas.

Section More_Definitions.

(* Tex_Prose
\section{Definitions}

Some auxiliary definitions.  A partition is said to be Separated if all its points are distinct.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.

(* Begin_Tex_Verb *)
Definition _Separated [n:nat][P:(Partition Hab n)] :=
  (i:nat)(Hi,H':?)(Pts P i Hi)[<](Pts P (S i) H').
(* End_Tex_Verb *)

(* Tex_Prose
Two partitions are said to be (mutually) Separated if they are both Separated and all their points are distinct (except for the endpoints).

\begin{convention} Let \verb!P,Q! be partitions of \verb!I! with, respectively, \verb!n! and \verb!m! points.
\end{convention}
*)

Variables n,m:nat.

Variable P:(Partition Hab n).
Variable Q:(Partition Hab m).

(* Begin_Tex_Verb *)
Definition Separated := (_Separated ? P)*((_Separated ? Q)*
  (i,j:nat)(lt O i)->(lt O j)->(lt i n)->(lt j m)->
    (Hi:(le i n))(Hj:(le j m))(Pts P i Hi)[#](Pts Q j Hj)).
(* End_Tex_Verb *)

End More_Definitions.

Implicits _Separated [1 2 3 4].
Implicits Separated [1 2 3 4 5].

Section Even_Partitions.

(* Tex_Prose
\section{More Lemmas}

More technical stuff.  Two equal partitions have the same Mesh.
*)

(* Begin_Tex_Verb *)
Lemma Mesh_wd : (n:nat)(a,b,b':IR)(Hab:a[<=]b)(Hab':a[<=]b')
  (P:(Partition Hab n))(Q:(Partition Hab' n))
  ((i:nat)(Hi:(le i n))(Pts P i Hi)[=](Pts Q i Hi))->
    (Mesh P)[=](Mesh Q).
(* End_Tex_Verb *)
Induction n.
Intros.
Unfold Mesh; Simpl; Algebra.
Clear n; Intro.
Case n.
Intros.
Unfold Mesh; Simpl.
Apply cg_minus_wd; Apply H0.
Clear n; Intros.
Unfold Mesh.
Apply eq_transitive_unfolded with 
  (Max (Pts P ? (le_n (S (S n))))[-](Pts P ? (le_S ?? (le_n (S n)))) (maxlist (Part_Mesh_List (Partition_Pred P)))).
Simpl; Algebra.
Apply eq_transitive_unfolded with 
  (Max (Pts Q ? (le_n (S (S n))))[-](Pts Q ? (le_S ?? (le_n (S n)))) (maxlist (Part_Mesh_List (Partition_Pred Q)))).
2: Simpl; Algebra.
Apply max_wd_unfolded.
Apply cg_minus_wd; Apply H0.
Apply eq_transitive_unfolded with (Mesh (Partition_Pred P)).
Unfold Mesh; Algebra.
Apply eq_transitive_unfolded with (Mesh (Partition_Pred Q)).
Apply H.
Intros.
Unfold Partition_Pred; Simpl.
Apply H0.
Unfold Mesh; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Mesh_wd' : (n:nat)(a,b:IR)(Hab:a[<=]b)
  (P,Q:(Partition Hab n))
  ((i:nat)(Hi:(le i n))(Pts P i Hi)[=](Pts Q i Hi))->
    (Mesh P)[=](Mesh Q).
(* End_Tex_Verb *)
Intros.
Apply Mesh_wd.
Intros; Apply H.
Qed.

(* Tex_Prose
The Mesh of an even partition is easily calculated.
*)

(* Begin_Tex_Verb *)
Lemma even_partition_Mesh : (m:nat)(Hm:~O=m)(a,b:IR)(Hab:a[<=]b)
  (Mesh (Even_Partition Hab m Hm))[=]
    (b[-]a)[/]?[//](nring_ap_zero' ?? Hm).
(* End_Tex_Verb *)
Induction m.
Intros; ElimType False; Apply Hm; Auto.
Intros.
Unfold Mesh.
Elim (le_lt_dec n O); Intro.
Cut O=n; [Intro | Auto with arith].
Generalize Hm; Clear H a0 Hm.
Rewrite <- H0; Intros.
Simpl.
Rational.
Apply eq_transitive_unfolded with
  (Max (a[+](nring (S n))[*]((b[-]a)[/]?[//](nring_ap_zero' ?? Hm)))[-](a[+](nring n)[*]((b[-]a)[/]?[//](nring_ap_zero' ?? Hm)))
     (maxlist (Part_Mesh_List (Partition_Pred (Even_Partition Hab ? Hm))))).
Cut n=(S (pred n)); [Intro | Apply S_pred with O; Auto].
Generalize Hm; Rewrite H0; Clear Hm; Intro.
Simpl; Algebra.
EApply eq_transitive_unfolded.
Apply Max_comm.
Simpl.
EApply eq_transitive_unfolded.
Apply leEq_imp_Max_is_rht.
2: Rational.
Apply eq_imp_leEq.
RStepr (b[-]a)[/]((nring n)[+]One)[//](nring_ap_zero' ?? Hm).
Apply eq_transitive_unfolded with (Mesh (Partition_Pred (Even_Partition Hab ? Hm))).
Simpl; Algebra.
Cut ~O=n; Intro.
EApply eq_transitive_unfolded.
Apply Mesh_wd' with Q:=(Even_Partition (part_pred_lemma ?? Hab (S n) (Even_Partition Hab ? Hm) n (le_n_Sn n)) ? H0).
Intros; Simpl; Rational.
EApply eq_transitive_unfolded.
Apply H.
Simpl; Rational.
Apply (lt_O_neq n); Auto.
Qed.

(* Tex_Prose
Even partitions always have a common refinement.
*)

Variables a,b:IR.
Local I:=(compact a b).
Hypothesis Hab:a[<=]b.

(* Begin_Tex_Verb *)
Lemma refinement_resp_mult : (m,n:nat)(Hm,Hn:?){k:nat |
  m=(mult n k)}->
  (Refinement (Even_Partition Hab n Hn)
              (Even_Partition Hab m Hm)).
(* End_Tex_Verb *)
Intros.
Elim H; Intros k Hk.
Red.
Cut ~O=k; Intro.
Exists [i:nat](mult i k); Repeat Split.
Symmetry; Assumption.
Intros.
Apply lt_mult_right.
Assumption.
Apply neq_O_lt; Auto.
Intros.
Cut (le (mult i k) m).
Intro.
Exists (toCle ?? H2).
Simpl.
Apply bin_op_wd_unfolded.
Algebra.
Generalize Hm; Rewrite Hk.
Clear Hm; Intro.
RStep ((nring i)[*](nring k))[*]((b[-]a)[/]?[//](mult_resp_ap_zero ??? (nring_ap_zero' ?? Hn) (nring_ap_zero' ?? H0))).
Apply mult_wd.
Apply eq_symmetric_unfolded; Apply nring_comm_mult.
Apply div_wd.
Algebra.
Apply eq_symmetric_unfolded; Apply nring_comm_mult.
Rewrite Hk.
Apply le_mult_right; Assumption.
Apply Hm.
Rewrite Hk.
Rewrite <- H0.
Auto.
Qed.

(* Tex_Prose
\begin{convention} Assume \verb!m,n! are positive natural numbers and denote by \verb!P! and \verb!Q! the even partitions with, respectively, \verb!m! and \verb!n! points.
\end{convention}
*)

Variables m,n:nat.
Hypothesis Hm:~O=m.
Hypothesis Hn:~O=n.

Local P:=(Even_Partition Hab m Hm).
Local Q:=(Even_Partition Hab n Hn).

(* Begin_Tex_Verb *)
Lemma even_partition_refinement : {N:nat & {HN:(toCProp ~O=N) & 
  (Refinement P (Even_Partition Hab N (not_to_CNot ? HN))) &
  (Refinement Q (Even_Partition Hab N (not_to_CNot ? HN)))}}.
(* End_Tex_Verb *)
Exists (mult m n).
Cut ~O=(mult m n); Intro.
Exists (ts ? H).
Unfold P; Apply refinement_resp_mult.
Exists n; Auto.
Unfold Q; Apply refinement_resp_mult.
Exists m; Auto with arith.
ElimType False.
Clear P Q.
Cut (!nring IR (mult m n))[#]Zero.
Rewrite <- H; Simpl.
Apply ap_irreflexive_unfolded.
Step (nring m)[*](!nring IR n).
Apply mult_resp_ap_zero; Apply Greater_imp_ap; Step (!nring IR O); Apply nring_less; Apply neq_O_lt; Auto.
Qed.

End Even_Partitions.

Section Partitions.

Variables a,b:IR.
Local I:=(compact a b).
Hypothesis Hab:(a[<=]b).

(* Tex_Prose
The AntiMesh of a Separated partition is always positive.
*)

(* Begin_Tex_Verb *)
Lemma pos_AntiMesh : (n:nat)(P:(Partition Hab n))(lt O n)->
  (_Separated P)->Zero[<](AntiMesh P).
(* End_Tex_Verb *)
Intro; Case n; Clear n; Intros.
ElimType False; Apply (lt_n_n ? H).
Unfold AntiMesh.
Apply less_minlist.
Simpl; Auto with arith.
Intros.
Elim (Part_Mesh_List_lemma ?????? H1); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Elim Hi'; Clear Hi'; Intros Hi' H'.
EApply less_wdr.
2: Apply eq_symmetric_unfolded; Apply H'.
Apply shift_less_minus; Step (Pts P i (Cle_to ?? Hi)).
Apply H0.
Qed.

(* Tex_Prose
A partition can have only one point iff the endpoints of the interval are the same; moreover, if the partition is Separated and the endpoints of the interval are the same then it \emph{must} have one point.
*)

(* Begin_Tex_Verb *)
Lemma partition_length_zero : (Partition Hab O)->a[=]b.
(* End_Tex_Verb *)
Intro.
Apply eq_transitive_unfolded with (Pts H O (le_O_n O)).
Apply eq_symmetric_unfolded; Apply start.
Apply finish.
Qed.

(* Begin_Tex_Verb *)
Lemma _Separated_imp_length_zero :
  (n:nat)(P:(Partition Hab n))(_Separated P)->(a[=]b)->O=n.
(* End_Tex_Verb *)
Intros.
Cut ~~O=n; [Omega | Intro].
Cut (lt O n); [Intro | Apply neq_O_lt; Auto].
ElimType False.
Cut a[#]b.
Exact (eq_imp_not_ap ??? H0).
Apply ap_well_def_lft_unfolded with (Pts P ? (le_O_n ?)).
2: Apply start.
Apply ap_well_def_rht_unfolded with (Pts P ? (le_n ?)).
2: Apply finish.
Apply less_imp_ap.
Apply local_mon_imp_mon_le with f:=[i:nat][H:(le i n)](Pts P i H).
Exact H.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma partition_less_imp_gt_zero :
  (n:nat)(P:(Partition Hab n))(a[<]b)->(lt O n).
(* End_Tex_Verb *)
Intros.
Cut ~O=n; Intro.
Apply neq_O_lt; Auto.
ElimType False.
Cut a[=]b.
Intro; Apply less_irreflexive_unfolded with x:=a.
Stepr b; Assumption.
Apply partition_length_zero.
Rewrite H0; Apply P.
Qed.

End Partitions.
