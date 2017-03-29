(* $Id: PartInterval.v,v 1.8 2003/03/13 12:06:21 lcf Exp $ *)

Require Export IntervalFunct.

Section Conversion.

(* Tex_Prose
\chapter{Correspondence}

In this file we prove that there are mappings going in both ways between the set of partial functions whose domain contains $[a,b]$ and the set of real-valued functions with domain on that interval.  These mappings form an adjunction, and thus they have all the good properties for preservation results.

\section{Mappings}

We begin by defining the map from partial functions to setoid functions as simply being the restriction of the partial function to the interval $[a,b]$.

\begin{convention} Let \verb!F! be a partial function and \verb!a,b:IR! such that \verb!I!$=[a,b]$ is included in the domain of \verb!F!.
\end{convention}
*)

Variable F:PartIR.
Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(compact a b Hab).

Hypothesis Hf:(included I (Pred F)).

(* Begin_Tex_Verb *)
Lemma int_partIR_strext : (fun_strong_ext
  [x:(subset I)](F (scs_elem ?? x)
    (Hf (scs_elem ?? x) (scs_prf ?? x)))).
(* End_Tex_Verb *)
Red; Intros.
Generalize (pfstrx ?????? H).
Case x; Case y; Auto.
Qed.

(* Begin_Tex_Verb *)
Definition int_partIR : (CSetoid_fun (subset I) IR).
(* End_Tex_Verb *)
Apply Build_CSetoid_fun with [x:(subset I)](Part F (scs_elem ?? x) (Hf (scs_elem ?? x) (scs_prf ?? x))).
Exact int_partIR_strext.
Defined.

End Conversion.

(* Tex_Prose
\begin{notation} We define {\tt\hypertarget{Syntactic_52}{IntPartIR}} to be \verb!(int_partIR ????)!. \end{notation}
*)

Syntactic Definition IntPartIR := (int_partIR ????).

Section AntiConversion.

(* Tex_Prose
To go the other way around, we simply take a setoid function \verb!f! with domain $[a,b]$ and build the corresponding partial function.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(compact a b Hab).

Variable f:(CSetoid_fun (subset I) IR).

(* Begin_Tex_Verb *)
Lemma partIR_int_strext : (x,y:IR)(Hx:?)(Hy:?)
  (((f (Build_subcsetoid_crr IR ? x Hx))[#]
    (f (Build_subcsetoid_crr IR ? y Hy)))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Exact (csetoid_fun_strext_unfolded ????? H).
Qed.

(* Begin_Tex_Verb *)
Definition partIR_int : PartIR.
(* End_Tex_Verb *)
Apply Build_PartFunct with pfpfun:=[x:IR][Hx:?](f (Build_subcsetoid_crr IR ? x Hx)).
Exact (compact_wd ???).
Exact partIR_int_strext.
Defined.

End AntiConversion.

(* Tex_Prose
\begin{notation} We define {\tt\hypertarget{Syntactic_53}{PartInt}} to be \verb!(partIR_int ???)!. \end{notation}
*)

Syntactic Definition PartInt := (partIR_int ???).

Section Inverses.

(* Tex_Prose
In one way these operators are inverses\footnote{Actually they form an adjunction, but that is completely irrelevant for our purpose, so we will ignore that in this formalization.}.
*)

(* Begin_Tex_Verb *)
Lemma int_part_int : (a,b:IR)(Hab:?)(F:PartIR)
  (Hf:(included (compact a b Hab) (Pred F)))
  (Feq (compact a b Hab) F (PartInt (IntPartIR Hf))).
(* End_Tex_Verb *)
Intros; FEQ.
Qed.

End Inverses.

Section Equivalences.

(* Tex_Prose
\section{Mappings Preserve Operations}

We now prove that all the operations we have defined on both sets are preserved by \verb!PartInt!.

\begin{convention} Let \verb!F,G! be partial functions and \verb!a,b:IR! and denote by \verb!I! the interval $[a,b]$.  Let \verb!f,g! be setoid functions of type \verb!I->IR! equal respectively to \verb!F! and \verb!G! in \verb!I!.
\end{convention}
*)

Variables F,G:PartIR.
Variables a,b,c:IR.
Hypothesis Hab:a[<=]b.
Local I:=(compact a b Hab).

Variables f,g:(CSetoid_fun (subset (compact a b Hab)) IR).

Hypothesis Ff : (Feq I F (PartInt f)).
Hypothesis Gg : (Feq I G (PartInt g)).

(* Begin_Tex_Verb *)
Lemma part_int_const :
  (Feq I {-C-}c (PartInt (ifunct_const a b Hab c))).
(* End_Tex_Verb *)
Apply eq_imp_Feq.
Red; Simpl; Intros; Auto.
Unfold I; Apply included_refl.
Intros; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma part_int_id : (Feq I FId (PartInt (ifunct_id a b Hab))).
(* End_Tex_Verb *)
Apply eq_imp_Feq.
Red; Simpl; Intros; Auto.
Unfold I; Apply included_refl.
Intros; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma part_int_plus : (Feq I F{+}G (PartInt (IPlus f g))).
(* End_Tex_Verb *)
Elim Ff; Intros Ff' Hf.
Elim Ff'; Clear Ff Ff'; Intros incF incF'.
Elim Gg; Intros Gg' Hg.
Elim Gg'; Clear Gg Gg'; Intros incG incG'.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl; Simpl in Hf Hg.
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma part_int_inv : (Feq I {--}F (PartInt (IInv f))).
(* End_Tex_Verb *)
Elim Ff; Intros Ff' Hf.
Elim Ff'; Clear Ff Ff'; Intros incF incF'.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl; Simpl in Hf.
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma part_int_minus : (Feq I F{-}G (PartInt (IMinus f g))).
(* End_Tex_Verb *)
Elim Ff; Intros Ff' Hf.
Elim Ff'; Clear Ff Ff'; Intros incF incF'.
Elim Gg; Intros Gg' Hg.
Elim Gg'; Clear Gg Gg'; Intros incG incG'.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl; Simpl in Hf Hg.
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma part_int_mult : (Feq I F{*}G (PartInt (IMult f g))).
(* End_Tex_Verb *)
Elim Ff; Intros Ff' Hf.
Elim Ff'; Clear Ff Ff'; Intros incF incF'.
Elim Gg; Intros Gg' Hg.
Elim Gg'; Clear Gg Gg'; Intros incG incG'.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl; Simpl in Hf Hg.
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma part_int_nth : (n:nat)(Feq I F{^}n (PartInt (INth f n))).
(* End_Tex_Verb *)
Intro.
Elim Ff; Intros Ff' Hf.
Elim Ff'; Clear Ff Ff'; Intros incF incF'.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl; Simpl in Hf.
Step (Part F x Hx)[^]n; Stepr (f (Build_subcsetoid_crr IR ? x Hx'))[^]n.
Apply nexp_wd; Algebra.
Qed.

(* Begin_Tex_Verb *)
Hypothesis HG:(bnd_away_zero I G).
Hypothesis Hg:(x:(subset I))(g x)[#]Zero.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma part_int_recip : (Feq I {1/}G (PartInt (IRecip g Hg))).
(* End_Tex_Verb *)
Elim Gg; Intros Gg' Hg'.
Elim Gg'; Clear Gg Gg'; Intros incG incG'.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl in Hg'; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma part_int_div : (Feq I F{/}G (PartInt (IDiv f g Hg))).
(* End_Tex_Verb *)
Elim Ff; Intros Ff' Hf.
Elim Ff'; Clear Ff Ff'; Intros incF incF'.
Elim Gg; Intros Gg' Hg'.
Elim Gg'; Clear Gg Gg'; Intros incG incG'.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl in Hf Hg'; Simpl.
Algebra.
Qed.

End Equivalences.
