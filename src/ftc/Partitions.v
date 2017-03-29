(* $Id: Partitions.v,v 1.13 2003/03/13 12:06:22 lcf Exp $ *)

Require Export Continuity.

Section Definitions.

(* Tex_Prose
\chapter{Partitions}

We now begin to lay the way for the definition of integral.  This will be done in the Riemann way, through the definition of a sequence of sums that is proved to be convergent; in order to do that, we first need to do a bit of work on partitions.

\section{Definitions}

A partition is defined as a record type.  For each compact interval $[a,b]$ and each natural number $n$, a partition of $[a,b]$ with $n+1$ points is a choice of real numbers $a=a_0\leq a_1\leq\ldots\leq a_n=b$; the following specification works as follows:
\begin{description}
\item[Pts] is the function that chooses the points;
\item[prf1] states that \verb!Pts! is a setoid function;
\item[prf2] states that the points are ordered;
\item[start] requires that $a_0=a$ and
\item[finish] requires that $a_n=b$.
\end{description}
*)

(* Begin_Tex_Verb *)
Record Partition [a,b:IR][Hab:a[<=]b][lng:nat] : Set :=
  {Pts : (i:nat)(le i lng)->IR;
   prf1 : (i,j:nat)i=j->(Hi:(le i lng))(Hj:(le j lng))(Pts i Hi)[=](Pts j Hj);
   prf2 : (i:nat)(H:(le i lng))(H':(le (S i) lng))(Pts i H)[<=](Pts (S i) H');
   start : (H:(le O lng))(Pts O H)[=]a;
   finish : (H:(le lng lng))(Pts lng H)[=]b}.
(* End_Tex_Verb *)

(* Tex_Prose
Two immediate consequences of this are that $a_i\leq a_j$ whenever $i\leq j$ and that $a_i\in[a,b]$ for all $i$.
*)

(* Begin_Tex_Verb *)
Lemma Partition_mon : (a,b,Hab,lng:?)(P:(Partition a b Hab lng))
  (i,j:nat)(Hi,Hj:?)(le i j)->
    (Pts ???? P i Hi)[<=](Pts ???? P j Hj).
(* End_Tex_Verb *)
Intros; Induction j.
Cut i=O; [Intro | Auto with arith].
Apply eq_imp_leEq; Apply prf1; Auto.
Elim (le_lt_eq_dec ?? H); Intro H1.
Cut (le j lng); [Intro | Clear Hrecj; Omega].
Apply leEq_transitive with (Pts ???? P j H0).
Apply Hrecj; Clear Hrecj; Auto with arith.
Apply prf2.
Apply eq_imp_leEq; Apply prf1; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Partition_in_compact : (a,b,Hab,lng:?)
  (P:(Partition a b Hab lng))(i:nat)(H:(le i lng))
    (compact a b Hab (Pts ???? P i H)).
(* End_Tex_Verb *)
Intros.
Split.
Apply leEq_wdl with (Pts ???? P ? (le_O_n ?)).
Apply Partition_mon; Auto with arith.
Apply start.
Apply leEq_wdr with (Pts ???? P ? (le_n ?)).
Apply Partition_mon; Auto with arith.
Apply finish.
Qed.

(* Tex_Prose
Each partition $\{a_0,\ldots,a_n\}$ implies a partition $\{a_0,\ldots,a_{n-1}\}$ of the interval $[a,a_{n-1}]$.  This partition will play an important role in much of our future work, so we take some care to define it.
*)

(* Begin_Tex_Verb *)
Lemma part_pred_lemma : (a,b,Hab,lng:?)
  (P:(Partition a b Hab lng))(i:nat)(Hi:(le i lng))
    a[<=](Pts ???? P i Hi).
(* End_Tex_Verb *)
Intros.
Apply leEq_wdl with (Pts ???? P O (le_O_n ?)).
Apply Partition_mon; Auto with arith.
Apply start.
Qed.

(* Begin_Tex_Verb *)
Definition Partition_Pred [a,b,Hab,n,P:?] :
  (Partition a ?
    (part_pred_lemma a b Hab (S n) P n (le_n_Sn n)) n).
(* End_Tex_Verb *)
Intros.
Apply Build_Partition with [i:nat][Hi:(le i n)](Pts ???? P i (le_S ?? Hi)).
Intros; Simpl; Apply prf1; Assumption.
Intros; Simpl; Apply prf2.
Intros; Simpl; Apply start.
Intros; Simpl; Apply prf1; Auto.
Defined.

(* Tex_Prose
The \emph{mesh} of a partition is the greatest distance between two consecutive points.  For convenience's sake we also define the dual concept, which is very helpful in some situations.  In order to do this, we begin by building a list with all the distances between consecutive points; next we only need to extract the maximum and the minimum of this list\footnote{Notice that this list is nonempty except in the case when $a=b$ and $n=0$; this means that the convention we took of defining the minimum and maximum of the empty list to be 0 actually helps us in this case.}.
*)

(* Begin_Tex_Verb *)
Definition Part_Mesh_List
  [n,a,b,Hab:?][P:(Partition a b Hab n)] : (list IR).
(* End_Tex_Verb *)
Intro; Induction n; Intros.
Apply nil.
Apply cons.
Apply (Pts ???? P ? (le_n (S n)))[-](Pts ???? P ? (le_S ?? (le_n n))).
Apply Hrecn with a (Pts ???? P ? (le_n_Sn n)) (part_pred_lemma ???? P n (le_n_Sn n)).
Apply Partition_Pred.
Defined.

(* Begin_Tex_Verb *)
Definition Mesh [a,b,Hab,n,P:?] :=
  (maxlist (Part_Mesh_List n a b Hab P)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition AntiMesh [a,b,Hab,n,P:?] :=
  (minlist (Part_Mesh_List n a b Hab P)).
(* End_Tex_Verb *)

(* Tex_Prose
Even partitions (partitions where all the points are evenly spaced) will also play a central role in our work; the first two lemmas are presented simply to make the definition of even partition lighter.
*)

(* Begin_Tex_Verb *)
Lemma even_part_1 : (a,b:IR)(n:nat)(Hn:~(O=n))
  a[+](nring O)[*]((b[-]a)[/]?[//](nring_ap_zero' ? n Hn))[=]a.
(* End_Tex_Verb *)
Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma even_part_2 : (a,b:IR)(n:nat)(Hn:~(O=n))
  a[+](nring n)[*]((b[-]a)[/]?[//](nring_ap_zero' ? n Hn))[=]b.
(* End_Tex_Verb *)
Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Definition Even_Partition [a,b,Hab,n:?][Hn:~(O=n)] :
  (Partition a b Hab n).
(* End_Tex_Verb *)
Intros.
Apply Build_Partition with [i:nat][Hi:(le i n)]a[+](nring i)[*]((b[-]a)[/]?[//](nring_ap_zero' ? n Hn)).
Intros; Simpl.
Rewrite H; Algebra.
Intros; Simpl.
Apply plus_resp_leEq_lft.
Apply mult_resp_leEq_rht.
Apply less_leEq; Apply less_plusOne.
Apply shift_leEq_div.
Apply nring_pos; Clear H; Apply neq_O_lt; Auto.
Apply shift_leEq_minus.
Step Zero[+]a.
Step a; Assumption.
Intros; Simpl; Apply even_part_1; Auto.
Intros; Simpl; Apply even_part_2; Auto.
Defined.

(* Tex_Prose
We will also need to consider arbitrary sums of the form \[\sum_{i=0}^{n-1}f(x_i)(a_{i+1}-a_i)\] where $x_i\in[a_i,a_{i+1}]$.  For this, we again need a choice function $x$ which has to satisfy some condition.  We define the condition and the sum:
*)

(* Begin_Tex_Verb *)
Definition Points_in_Partition [a,b,Hab,n:?]
  [P:(Partition a b Hab n)][g:(i:nat)(lt i n)->IR] : CProp :=
  (i:nat)(H:(lt i n))
    (Compact (prf2 ???? P i (lt_le_weak ?? H) H) (g i H)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Pts_part_lemma : (a,b,Hab,n,P,g:?)
  (Points_in_Partition a b Hab n P g)->
    (i:nat)(H:(lt i n))(compact a b Hab (g i H)).
(* End_Tex_Verb *)
Intros.
Elim (H i H0); Intros.
Split.
EApply leEq_transitive.
2: Apply a0.
Apply leEq_wdl with (Pts ???? P O (le_O_n ?)).
Apply Partition_mon; Auto with arith.
Apply start.
EApply leEq_transitive.
Apply b0.
Apply leEq_wdr with (Pts ???? P n (le_n ?)).
Apply Partition_mon; Auto with arith.
Apply finish.
Qed.

(* Begin_Tex_Verb *)
Definition Partition_Sum [a,b,Hab,n:?][P:(Partition a b Hab n)]
  [g,F:?][H:(Points_in_Partition ???? P g)]
  [incF:(included (Compact Hab) (Pred F))] :=
  (Sumx [i:nat][Hi:(lt i n)]
    (F (g i Hi) (incF ? (Pts_part_lemma ?????? H i Hi)))[*]
      ((Pts ???? P (S i) Hi)[-]
        (Pts ???? P i (lt_le_weak ?? Hi)))).
(* End_Tex_Verb *)

(* Tex_Prose
\section{Constructions}

We now formalize some trivial and helpful constructions.

\begin{convention} We will assume a fixed compact interval $[a,b]$, denoted by \verb!I!.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab : a[<=]b.
Local I:=(compact a b Hab).

Section Getting_Points.

(* Tex_Prose
From a partition we always have a canonical choice of points at which to evaluate a function: just take all but the last points of the partition.

\begin{convention} Let \verb!Q! be a partition of \verb!I! with \verb!m! points.
\end{convention}
*)

Variable m:nat.
Variable Q:(Partition a b Hab m).

(* Begin_Tex_Verb *)
Definition Partition_imp_points : (i:nat)(lt i m)->IR.
(* End_Tex_Verb *)
Intros.
Apply (Pts ???? Q i (lt_le_weak ?? H)).
Defined.

(* Begin_Tex_Verb *)
Lemma Partition_imp_points_1 :
  (Points_in_Partition ???? Q Partition_imp_points).
(* End_Tex_Verb *)
Red; Intros.
Unfold Partition_imp_points; Split.
Apply leEq_reflexive.
Apply prf2.
Qed.

(* Begin_Tex_Verb *)
Lemma Partition_imp_points_2 :
  (nat_less_n_fun ?? Partition_imp_points).
(* End_Tex_Verb *)
Red; Intros.
Unfold Partition_imp_points; Simpl.
Apply prf1; Auto.
Qed.

End Getting_Points.

(* Tex_Prose
As a corollary, given any continuous function $F$ and a natural number we have an immediate choice of a sum of $F$ in $[a,b]$.
*)

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).

(* Begin_Tex_Verb *)
Definition Even_Partition_Sum [n:nat][Hn:~(O=n)] : IR.
(* End_Tex_Verb *)
Intros.
Apply Partition_Sum with a b Hab n (Even_Partition a b Hab n Hn) (Partition_imp_points ? (Even_Partition a b Hab n Hn)) F.
Apply Partition_imp_points_1.
Apply contin_imp_inc; Assumption.
Defined.

End Definitions.

Implicits Partition [1 2].
Implicits Partition_Pred [1 2 3 4].
Implicits Mesh [1 2 3 4].
Implicits AntiMesh [1 2 3 4].
Implicits Pts [1 2 3 4].
Implicits Part_Mesh_List [1 2 3 4].
Implicits Points_in_Partition [1 2 3 4].
Implicits Partition_Sum [1 2 3 4 5 6 7].
Implicits Even_Partition [1 2].
Implicits Even_Partition_Sum [1 2].

Section Lemmas.

(* Tex_Prose
\section{Lemmas}

Finally, we include some important lemmas about partitions.

If a partition has more than one point then its mesh list is nonempty.
*)

(* Begin_Tex_Verb *)
Lemma length_Part_Mesh_List : (n:nat)(a,b:IR)(Hab:(a[<=]b))
  (P:(Partition Hab n))(lt O n)->
    (lt O (length (Part_Mesh_List P))).
(* End_Tex_Verb *)
Intro; Case n; Intros.
ElimType False; Inversion H.
Simpl; Auto with arith.
Qed.

(* Tex_Prose
Any element of the auxiliary list defined to calculate the mesh of a partition has a very specific form.
*)

(* Begin_Tex_Verb *)
Lemma Part_Mesh_List_lemma : (n:nat)(a,b:IR)(Hab:(a[<=]b))
  (P:(Partition Hab n))(x:IR)(member x (Part_Mesh_List P))->
  {i:nat & {Hi:(Cle i n) & {Hi':(Cle (S i) n) | x[=]
    (Pts P ? (Cle_to ?? Hi'))[-](Pts P ? (Cle_to ?? Hi))}}}.
(* End_Tex_Verb *)
Intro; Induction n.
Simpl; Intros.
ElimType CFalse; Assumption.
Intros.
Simpl in H; Inversion_clear H.
Elim (Hrecn ????? H0); Clear Hrecn.
Intros i H; Elim H; Clear H.
Intros Hi H; Elim H; Clear H.
Intros Hi' H.
Simpl in H.
Exists i; Exists (toCle ?? (le_S ?? (Cle_to ?? Hi))); Exists (toCle ?? (le_S ?? (Cle_to ?? Hi'))).
EApply eq_transitive_unfolded.
Apply H.
Apply cg_minus_wd; Apply prf1; Auto.
Exists n.
Exists (toCle ?? (le_S ?? (le_n n))).
Exists (toCle ?? (le_n (S n))).
EApply eq_transitive_unfolded.
Apply H0.
Apply cg_minus_wd; Apply prf1; Auto.
Qed.

(* Tex_Prose
Mesh and antimesh are always nonnegative.
*)

(* Begin_Tex_Verb *)
Lemma Mesh_nonneg : (n:nat)(a,b:IR)(Hab:(a[<=]b))
  (P:(Partition Hab n))Zero[<=](Mesh P).
(* End_Tex_Verb *)
Induction n.
Intros; Unfold Mesh; Simpl.
Apply leEq_reflexive.
Clear n; Intros.
Unfold Mesh.
Apply leEq_transitive with (Pts P ? (le_n (S n)))[-](Pts P ? (le_S ?? (le_n n))).
Apply shift_leEq_minus; Step (Pts P ? (le_S ?? (le_n n))).
Apply prf2.
Apply maxlist_greater.
Right; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma AntiMesh_nonneg : (n:nat)(a,b:IR)(Hab:(a[<=]b))
  (P:(Partition Hab n))Zero[<=](AntiMesh P).
(* End_Tex_Verb *)
Intro; Induction n.
Intros; Unfold AntiMesh; Simpl.
Apply leEq_reflexive.
Intros.
Unfold AntiMesh.
Apply leEq_minlist.
Simpl; Auto with arith.
Intros.
Simpl in H; Inversion_clear H.
Unfold AntiMesh in Hrecn.
Apply leEq_transitive with (minlist (Part_Mesh_List (Partition_Pred P))).
2: Apply minlist_smaller; Assumption.
Apply Hrecn.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply H0.
Apply shift_leEq_minus; Step (Pts P ? (le_S ?? (le_n n))).
Apply prf2.
Qed.

(* Tex_Prose
Most important, AntiMesh and Mesh provide lower and upper bounds for the distance between any two consecutive points in a partition.

\begin{convention} Let \verb!I!$=[a,b]$ and \verb!P! be a partition of \verb!I! with \verb!n! points.
\end{convention}
*)

Variables a,b:IR.
Local I:=(compact a b).
Hypothesis Hab:(a[<=]b).

Variable n:nat.
Variable P:(Partition Hab n).

(* Begin_Tex_Verb *)
Lemma Mesh_lemma : (i:nat)(H,H':?)
  (Pts P (S i) H')[-](Pts P i H)[<=](Mesh P).
(* End_Tex_Verb *)
Clear I; Generalize n a b Hab P; Clear P n Hab a b.
Induction n.
Intros; ElimType False; Inversion H'.
Clear n; Intro m; Intros.
Induction m.
Cut O=i; [Intro | Inversion H'; Auto; Inversion H2].
Generalize H0 H'; Clear H0 H'; Rewrite <- H1.
Intros.
Unfold Mesh; Simpl.
Apply eq_imp_leEq; Apply cg_minus_wd; Apply prf1; Auto.
Elim (le_lt_eq_dec ?? H'); Intro H1.
Cut (le i (S m)); [Intro | Auto with arith].
Cut (le (S i) (S m)); [Intro | Auto with arith].
LetTac P':=(Partition_Pred P).
Apply leEq_wdl with (Pts P' ? H3)[-](Pts P' ? H2).
2: Simpl; Apply cg_minus_wd; Apply prf1; Auto.
Apply leEq_transitive with (Mesh P').
Apply H.
Unfold Mesh; Simpl; Apply rht_leEq_Max.
Cut i=(S m); [Intro | Auto with arith].
Generalize H' H0; Clear H0 H'.
Rewrite H2; Intros.
Unfold Mesh; Apply maxlist_greater; Right.
Apply cg_minus_wd; Apply prf1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma AntiMesh_lemma : (i:nat)(H,H':?)
  (AntiMesh P)[<=](Pts P (S i) H')[-](Pts P i H).
(* End_Tex_Verb *)
Clear I; Generalize n a b Hab P; Clear P n Hab a b.
Induction n.
Intros; ElimType False; Inversion H'.
Clear n; Intro m; Intros.
Induction m.
Cut O=i; [Intro | Inversion H'; Auto; Inversion H2].
Generalize H0 H'; Clear H0 H'; Rewrite <- H1.
Intros.
Unfold AntiMesh; Simpl.
Apply eq_imp_leEq; Apply cg_minus_wd; Apply prf1; Auto.
Elim (le_lt_eq_dec ?? H'); Intro H1.
Cut (le i (S m)); [Intro | Auto with arith].
Cut (le (S i) (S m)); [Intro | Auto with arith].
LetTac P':=(Partition_Pred P).
Apply leEq_wdr with (Pts P' ? H3)[-](Pts P' ? H2).
2: Simpl; Apply cg_minus_wd; Apply prf1; Auto.
Apply leEq_transitive with (AntiMesh P').
2: Apply H.
Unfold AntiMesh; Simpl.
EApply leEq_wdr.
2: Apply cg_inv_inv.
Apply inv_resp_leEq; Apply rht_leEq_Max.
Cut i=(S m); [Intro | Auto with arith].
Generalize H' H0; Clear H0 H'.
Rewrite H2; Intros.
Unfold AntiMesh; Apply minlist_smaller; Right.
Apply cg_minus_wd; Apply prf1; Auto.
Qed.

(* Tex_Prose
Finally, we define what it means for a partition $Q$ to be a refinement of $P$ and prove the two main properties of refinements.
*)

(* Begin_Tex_Verb *)
Definition Refinement [m:nat][Q:(Partition Hab m)] :=
  {f:nat->nat | 
    ((f O)=O)/\((f n)=m)/\
    ((i,j:nat)(lt i j)->(lt (f i) (f j))) &
      (i:nat)(H:(le i n)){H':(Cle (f i) m) |
        (Pts P i H)[=](Pts Q (f i) (Cle_to ?? H'))}}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Refinement_lemma : (m,Q:?)(Refinement m Q)->
  (i:nat)(Hi:(le i m))(Hi':(le (S i) m))
    {j:nat & {Hj:(Cle j n) & {Hj':(Cle (S j) n) |
      ((Pts P ? (Cle_to ?? Hj))[<=](Pts Q ? Hi)) |
      ((Pts Q ? Hi')[<=](Pts P ? (Cle_to ?? Hj')))}}}.
(* End_Tex_Verb *)
Intros.
Elim H; Clear H; Intros f Hf.
Elim Hf; Clear Hf; Intros Hf0 Hf.
Elim Hf; Clear Hf; Intros Hfn Hfmon.
Intro Hf.
Cut {j:nat | (le (f j) i) | (le (S i) (f (S j)))}.
Intro.
Elim H; Clear H; Intros j Hj Hj'.
Exists j.
Cut (lt j n).
Intro.
Cut (le j n); [Intro | Auto with arith].
Cut (Cle j n); [Intro Hj1 | Auto].
Exists Hj1.
Elim (Hf j H0); Intros H' HPts.
Cut (le (S j) n); [Intro | Apply H].
Cut (Cle (S j) n); [Intro Hj2 | Auto].
Elim (Hf (S j) H1); Intros H'' HPts'.
Exists Hj2.
EApply leEq_wdl.
2: EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply HPts.
Apply Partition_mon; Assumption.
Apply prf1; Auto.
EApply leEq_wdr.
2: EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply HPts'.
Apply Partition_mon; Assumption.
Apply prf1; Auto.
Clear Hj' Hf Hf0.
Cut (lt i (f n)).
Intro.
Cut (lt (f j) (f n)); [Intro | Apply le_lt_trans with i; Auto].
Apply not_ge.
Intro; Red in H1.
Apply (le_not_lt (f j) (f n)); Auto with arith.
Apply Hfmon.
Elim (le_lt_eq_dec ?? H1); Intro; Auto.
Rewrite b0 in H0; Elim (lt_n_n (f j)); Auto.
Rewrite <- Hfn in Hi'; Auto.
Apply mon_fun_covers; Auto.
Exists n; Clear Hf Hfmon.
Rewrite Hfn; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Mesh_leEq : (m,Q:?)(Refinement m Q)->(Mesh Q)[<=](Mesh P).
(* End_Tex_Verb *)
Intro; Case m.
Intros.
Unfold 1 Mesh; Simpl.
Apply Mesh_nonneg.
Clear m; Intro m; Intros.
Unfold 1 Mesh.
Apply maxlist_leEq.
Simpl; Auto with arith.
Intros.
Cut {i:nat & {Hi:(Cle i (S m)) & {Hi':(Cle (S i) (S m)) |  x[=](Pts Q ? (Cle_to ?? Hi'))[-](Pts Q ? (Cle_to ?? Hi))}}}.
2: Apply Part_Mesh_List_lemma; Assumption.
Clear H0; Intro.
Elim H0; Clear H0; Intros i H0.
Elim H0; Clear H0; Intros Hi H0.
Elim H0; Clear H0; Intros Hi' H0.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply H0.
Elim H; Intros f Hf.
Elim Hf; Clear Hf; Intros Hf' Hf.
Cut {j:nat & {Hj:(Cle j n) & {Hj':(Cle (S j) n) |
      ((Pts P ? (Cle_to ?? Hj))[<=](Pts Q ? (Cle_to ?? Hi))) | ((Pts Q ? (Cle_to ?? Hi'))[<=](Pts P ? (Cle_to ?? Hj')))}}}.
Intro.
Elim H1; Intros j Hj.
Elim Hj; Clear H1 Hj; Intros Hj Hjaux.
Elim Hjaux; Clear Hjaux; Intros Hj' Hjaux.
Intros HPts HPts'.
Apply leEq_transitive with (Pts P ? (Cle_to ?? Hj'))[-](Pts P ? (Cle_to ?? Hj)).
Unfold cg_minus; Apply plus_resp_leEq_both.
Assumption.
Apply inv_resp_leEq; Assumption.
Apply Mesh_lemma.
Apply Refinement_lemma; Assumption.
Qed.

End Lemmas.

Implicits Refinement [1 2 3 4 6].
