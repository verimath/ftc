(* $Id: FunctSequence.v,v 1.19 2003/03/13 12:06:19 lcf Exp $ *)

Require Export Continuity.
Require Export PartInterval.

Section Definitions.

(* Tex_Prose
\chapter{Sequences of Functions}

In this file we define some more operators on functions, namely sequences and limits.  These concepts are defined only for continuous functions.

\begin{convention} Throughout this section:
\begin{itemize}
\item \verb!a! and \verb!b! will be real numbers and the interval $[a,b]$ will be denoted by \verb!I!;
\item \verb!f, g! and \verb!h! will denote sequences of \emph{continuous} functions;
\item \verb!F, G! and \verb!H! will denote continuous functions.
\end{itemize}
\end{convention}

\section{Definitions}

A sequence of functions is simply an object of type \verb!nat->PartIR!.  However, we will be interested mostly in \emph{convergent} and Cauchy sequences.  Several definitions of these concepts will be formalized; they mirror the several different ways in which a Cauchy sequence can be defined.  For a discussion on the different notions of convergent see Bishop [1967].
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable f:nat->PartIR.
Variable F:PartIR.

Hypothesis contf:(n:nat)(Continuous_I Hab (f n)).
Hypothesis contF:(Continuous_I Hab F).

Local incf [n:nat] := (contin_imp_inc ???? (contf n)).
Local incF := (contin_imp_inc ???? contF).

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq := (e:IR)(Zero[<]e)->{N:nat |
  (m,n:nat)(le N m)->(le N n)->(x:IR)(Hx:(I x))
  (AbsIR ((f m) x (incf m x Hx))[-]((f n) x (incf n x Hx)))[<=]e}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition conv_fun_seq' := (e:IR)(Zero[<]e)->{N:nat |
  (n:nat)(le N n)->(x:IR)(Hx:(I x))
  (AbsIR ((f n) x (incf n x Hx))[-](F x (incF x Hx)))[<=]e}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition conv_norm_fun_seq := (k:nat){N:nat |
  (n:nat)(le N n)->
  (Norm_Funct (Continuous_I_minus ????? (contf n) contF))
    [<=](one_div_succ k)}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq1:=(k:nat){N:nat |
  (m,n:nat)(le N m)->(le N n)->
  (Norm_Funct (Continuous_I_minus ????? (contf m) (contf n)))
    [<=](one_div_succ k)}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq' := (k:nat){N:nat |
  (m,n:nat)(le N m)->(le N n)->(x:IR)(Hx:(I x))
  (AbsIR (pfpfun ? ? (incf m x Hx))[-](pfpfun ? ? (incf n x Hx)))
    [<=](one_div_succ k)}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq2 := (e:IR)(Zero[<]e)->{N:nat |
  (m:nat)(le N m)->(x:IR)(Hx:(I x))
  (AbsIR (pfpfun ? ? (incf m x Hx))[-](pfpfun ? ? (incf N x Hx)))[<=]e}.
(* End_Tex_Verb *)

(* Tex_Prose
These definitions are all shown to be equivalent.
*)

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq_seq' : Cauchy_fun_seq->Cauchy_fun_seq'.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intro.
Exact (H (one_div_succ k) (one_div_succ_pos ? k)).
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq'_seq : Cauchy_fun_seq'->Cauchy_fun_seq.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros e He.
Elim (Archimedes One[/]e[//](pos_ap_zero ?? He)).
Intros i Hei.
Cut (Zero[<](!nring IR i)).
Intro Hi.
Elim (H i).
Intros N HN; Exists N.
Intros.
Apply leEq_transitive with (!one_div_succ IR i).
Apply HN; Assumption.
Unfold one_div_succ.
RStepr (One[/]?[//](recip_ap_zero ?? (pos_ap_zero ?? He))).
Unfold Snring.
Apply recip_resp_leEq.
Apply recip_resp_pos; Assumption.
Apply less_leEq; Apply leEq_less_trans with (!nring IR i).
Assumption.
Simpl; Apply less_plusOne.
Apply less_leEq_trans with (One[/]e[//](pos_ap_zero ?? He)).
Apply recip_resp_pos; Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_Cauchy_fun_seq' : conv_fun_seq'->Cauchy_fun_seq.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros e He.
Elim (H ? (pos_div_two ?? He)).
Intros N HN.
Exists N; Intros.
Apply leEq_wdl with 
  (AbsIR (((f m) x (incf m x Hx))[-](F x (incF x Hx)))[+]((F x (incF x Hx))[-]((f n) x (incf n x Hx)))).
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR.
RStepr e[/]TwoNZ[+]e[/]TwoNZ.
Apply plus_resp_leEq_both.
Apply HN; Assumption.
EApply leEq_wdl.
2: Apply AbsIR_minus.
Apply HN; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq_seq2 : Cauchy_fun_seq->Cauchy_fun_seq2.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros.
Elim (H e H0); Intros N HN; Exists N.
Intros; Apply HN; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq2_seq : Cauchy_fun_seq2->Cauchy_fun_seq.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros.
Elim (H ? (pos_div_two ?? H0)); Intros N HN; Exists N; Intros.
Apply leEq_wdl with (AbsIR ((pfpfun ? ? (incf m x Hx))[-](pfpfun ? ? (incf N x Hx)))[-]((pfpfun ? ? (incf n x Hx))[-](pfpfun ? ? (incf N x Hx)))).
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR_minus.
RStepr e[/]TwoNZ[+]e[/]TwoNZ.
Apply plus_resp_leEq_both; Apply HN; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_norm : conv_fun_seq'->conv_norm_fun_seq.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intro.
Elim (H (one_div_succ k) (one_div_succ_pos ? k)).
Intros N HN.
Exists N.
Intros.
Apply leEq_Norm_Funct.
Fold I; Intros.
EApply leEq_wdl.
Apply (HN n H0 x H1).
Apply AbsIR_wd; Simpl; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_norm_seq : conv_norm_fun_seq->conv_fun_seq'.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros e He.
Elim (Archimedes One[/]?[//](pos_ap_zero ?? He)).
Intros k Hk.
Elim (H k); Clear H.
Intros N HN.
Exists N.
Intros.
Cut (Pred (f n){-}F x); Intros.
Apply leEq_wdl with (AbsIR ((f n){-}F x H0)).
EApply leEq_transitive.
2: Apply leEq_transitive with (!one_div_succ IR k).
2: Apply HN with n:=n; Assumption.
Apply norm_bnd_AbsIR; Assumption.
Unfold one_div_succ.
Unfold Snring.
Apply less_leEq; Apply swap_div with (pos_ap_zero ?? He).
Apply pos_nring_S.
Assumption.
EApply leEq_less_trans.
Apply Hk.
Simpl; Apply less_plusOne.
Apply AbsIR_wd; Simpl; Rational.
Split.
Apply incf; Assumption.
Apply incF; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq1_seq' : Cauchy_fun_seq1->Cauchy_fun_seq'.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intro.
Elim (H k); Clear H; Intros N HN.
Exists N; Intros.
EApply leEq_transitive.
2: Apply HN with m:=m n:=n; Assumption.
Cut (Pred (f m){-}(f n) x); Intros.
Apply leEq_wdl with (AbsIR (pfpfun ? ? H1)).
Apply norm_bnd_AbsIR; Assumption.
Apply AbsIR_wd; Simpl; Rational.
Split; Simpl; Apply incf; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq'_seq1 : Cauchy_fun_seq'->Cauchy_fun_seq1.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intro.
Elim (H k); Clear H; Intros N HN.
Exists N; Intros.
Apply leEq_Norm_Funct.
Intros.
EApply leEq_wdl.
Apply (HN m n H H0 x H1).
Apply AbsIR_wd; Simpl; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq_seq1 : Cauchy_fun_seq->Cauchy_fun_seq1.
(* End_Tex_Verb *)
Intro.
Apply Cauchy_fun_seq'_seq1.
Apply Cauchy_fun_seq_seq'.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq1_seq : Cauchy_fun_seq1->Cauchy_fun_seq.
(* End_Tex_Verb *)
Intro.
Apply Cauchy_fun_seq'_seq.
Apply Cauchy_fun_seq1_seq'.
Assumption.
Qed.

(* Tex_Prose
A Cauchy sequence of functions is pointwise a Cauchy sequence.
*)

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_real : Cauchy_fun_seq->
  (x:IR)(Hx:(I x))(Cauchy_prop [n:nat](pfpfun ? ? (incf n x Hx))).
(* End_Tex_Verb *)
Intros.
Red; Red in H.
Intros e He.
Elim (H ? He); Clear H; Intros N HN.
Exists N.
Intros.
Apply AbsIR_imp_AbsSmall.
Apply HN.
Assumption.
Apply le_n.
Qed.

End Definitions.

Section More_Definitions.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable f:nat->PartIR.
Hypothesis contf:(n:nat)(Continuous_I Hab (f n)).

(* Tex_Prose
We can also say that $f$ is simply convergent if it converges to some continuous function\footnote{Notice that we do not quantify directly over partial functions, for reasons which were already explained.}.
*)

(* Begin_Tex_Verb *)
Definition conv_fun_seq :=
  {f':(CSetoid_fun (subset (Compact Hab)) IR) &
    {contf':(Continuous_I Hab (PartInt f')) & 
      (conv_fun_seq' a b Hab f (PartInt f') contf contf')}}.
(* End_Tex_Verb *)

(* Tex_Prose
It is useful to extract the Limit as a partial function:
*)

(* Begin_Tex_Verb *)
Hypothesis H:(Cauchy_fun_seq ??? f contf).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq_Lim : PartIR.
(* End_Tex_Verb *)
Apply Build_PartFunct with 
  pfpfun:=[x:IR][Hx:(I x)](Lim (Build_CauchySeq ? [n:nat](pfpfun ? ? (contin_imp_inc ???? (contf n) x Hx)) 
    (Cauchy_fun_real ???? contf H x Hx))).
Unfold I; Apply compact_wd.
Intros.
Elim (Lim_strext ?? H0).
Intros n Hn.
Simpl in Hn.
Exact (pfstrx ?????? Hn).
Defined.

End More_Definitions.

Section Irrelevance_of_Proofs.

(* Tex_Prose
\section{Irrelevance of Proofs}

This section contains a number of technical results stating mainly that being a Cauchy sequence or converging to some Limit is a property of the sequence itself and independent of the proofs we supply of its continuity or the continuity of its Limit.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable f:nat->PartIR.
(* Begin_Tex_Verb *)
Hypothesis contf,contf0:(n:nat)(Continuous_I Hab (f n)).
(* End_Tex_Verb *)

Variable F:PartIR.
(* Begin_Tex_Verb *)
Hypothesis contF,contF0:(Continuous_I Hab F).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wd : (conv_fun_seq' ????? contf contF)->
  (conv_fun_seq' ????? contf0 contF0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Elim (H e H0); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN n H1 x Hx).
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq'_wd : (Cauchy_fun_seq' ???? contf)->
  (Cauchy_fun_seq' ???? contf0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Elim (H k); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN m n H0 H1 x Hx).
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq2_wd : (Cauchy_fun_seq2 ???? contf)->
  (Cauchy_fun_seq2 ???? contf0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Elim (H e H0); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN m H1 x Hx).
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_norm_fun_seq_wd :
  (conv_norm_fun_seq ????? contf contF)->
  (conv_norm_fun_seq ????? contf0 contF0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Elim (H k); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN n H0).
Apply Norm_Funct_wd.
Apply Feq_reflexive; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq1_wd : (Cauchy_fun_seq1 ???? contf)->
  (Cauchy_fun_seq1 ???? contf0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Elim (H k); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN m n H0 H1).
Apply Norm_Funct_wd.
Apply Feq_reflexive; Included.
Qed.

End Irrelevance_of_Proofs.

Section More_Proof_Irrelevance.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq_wd : (a,b,Hab,f,contf,contf0:?)
  (conv_fun_seq a b Hab f contf)->(conv_fun_seq a b Hab f contf0).
(* End_Tex_Verb *)
Intro; Red; Intros.
Elim H; Intros f' Hf'.
Exists f'.
Inversion_clear Hf'.
Exists x.
EApply conv_fun_seq'_wd.
Apply H0.
Qed.

End More_Proof_Irrelevance.

Section More_Properties.

(* Tex_Prose
\section{Other Properties}

Still more technical details---a convergent sequence converges to its Limit; the Limit is a continuous function; and convergence is well defined with respect to functional equality in the interval $[a,b]$.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables f,g:nat->PartIR.
(* Begin_Tex_Verb *)
Hypothesis contf,contf0:(n:nat)(Continuous_I Hab (f n)).
Hypothesis contg,contg0:(n:nat)(Continuous_I Hab (g n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Cauchy_conv_fun_seq' : (H:(Cauchy_fun_seq ??? f contf))
  (contf':(Continuous_I Hab (Cauchy_fun_seq_Lim ????? H)))
  (conv_fun_seq' ????? contf contf').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H e H0).
Intros N HN.
Exists N.
Intros.
LetTac incf:=[n:nat](contin_imp_inc ???? (contf n)).
LetTac incf':=(contin_imp_inc ???? contf').
Apply leEq_wdl with (AbsIR (Lim (Cauchy_const ((f n) x (incf n x Hx))))[-](Part (Cauchy_fun_seq_Lim ????? H) x (incf' x Hx))).
2: Apply AbsIR_wd; Apply cg_minus_wd.
2: Apply eq_symmetric_unfolded; Apply Lim_const.
2: Algebra.
Simpl.
Apply leEq_wdl with (AbsIR (Lim (Build_CauchySeq IR ? 
  (Cauchy_minus (Cauchy_const (pfpfun ? ? (incf n x Hx))) (Build_CauchySeq ?? (Cauchy_fun_real ????? H x (incf' x Hx))))))).
2: Apply AbsIR_wd; Apply Lim_minus.
EApply leEq_wdl.
2: Apply Lim_abs.
Simpl.
Apply str_seq_leEq_so_Lim_leEq.
Exists N; Intros.
Simpl.
EApply leEq_wdl.
Apply (HN n i H1 H2 x Hx).
Apply AbsIR_wd; Rational.
Qed.

Variables F,G:PartIR.
(* Begin_Tex_Verb *)
Hypothesis contF,contF0:(Continuous_I Hab F).
Hypothesis contG,contG0:(Continuous_I Hab G).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdl : ((n:nat)(Feq I (f n) (g n)))->
  (conv_fun_seq' ????? contf contF)->
  (conv_fun_seq' ????? contg contF0).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H0 e H1); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN n H2 x Hx).
Apply AbsIR_wd; Apply cg_minus_wd.
Elim (H n); Intros Haux inc.
Inversion_clear Haux.
Auto.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdr : (Feq I F G)->
  (conv_fun_seq' ????? contf contF)->
  (conv_fun_seq' ????? contf0 contG).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H0 e H1); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN n H2 x Hx).
Apply AbsIR_wd; Apply cg_minus_wd.
Algebra.
Elim H; Intros Haux inc.
Inversion_clear Haux.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdl' : ((n:nat)(Feq I (f n) (g n)))->
  (conv_fun_seq' ????? contf contF)->
  (conv_fun_seq' ????? contg contF).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H0 e H1); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN n H2 x Hx).
Apply AbsIR_wd; Apply cg_minus_wd.
Elim (H n); Intros Haux inc.
Inversion_clear Haux.
Auto.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdr' : (Feq I F G)->
  (conv_fun_seq' ????? contf contF)->
  (conv_fun_seq' ????? contf contG).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H0 e H1); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN n H2 x Hx).
Apply AbsIR_wd; Apply cg_minus_wd.
Algebra.
Elim H; Intros Haux inc.
Inversion_clear Haux.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq_wd : ((n:nat)(Feq I (f n) (g n)))->
  (Cauchy_fun_seq ???? contf)->(Cauchy_fun_seq ???? contg).
(* End_Tex_Verb *)
Intros.
Red; Red in H0.
Intros.
Elim (H0 e H1); Clear H0; Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN m n H0 H2 x Hx).
Elim (H n); Intros.
Inversion_clear a0.
Elim (H m); Intros.
Inversion_clear a0.
Apply AbsIR_wd; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_cont_Lim : (H:(Cauchy_fun_seq a b Hab f contf))
  (Continuous_I Hab (Cauchy_fun_seq_Lim ???? contf H)).
(* End_Tex_Verb *)
Intros.
Split.
Included.
Intros e He.
Elim (H ? (pos_div_three ?? He)); Intros N HN.
Elim (contf N); Intros incf contf'.
Elim (contf' ? (pos_div_three ?? He)).
Intros d H0 H1.
Exists d.
Assumption.
Intros.
Cut (x,y,z,w:IR)(AbsIR x[-]w)[=](AbsIR (x[-]y)[+](y[-]z)[+](z[-]w)); Intros.
2: Apply AbsIR_wd; Rational.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply H5 with y:=(pfpfun ? ? (incf x H2)) z:=(pfpfun ? ? (incf y H3)).
RStepr e[/]ThreeNZ[+]e[/]ThreeNZ[+]e[/]ThreeNZ.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
Apply leEq_wdl with (AbsIR (pfpfun ? ? Hx)[-](Lim (Cauchy_const (pfpfun ? ? (incf x H2))))).
2: Apply AbsIR_wd; Apply cg_minus_wd.
2: Algebra.
2: Apply eq_symmetric_unfolded; Apply Lim_const.
Simpl.
Apply leEq_wdl with (AbsIR (Lim (Build_CauchySeq IR ? 
  (Cauchy_minus (Build_CauchySeq ?? (Cauchy_fun_real ????? H x Hx)) (Cauchy_const (pfpfun ? ? (incf x H2))))))).
2: Apply AbsIR_wd; Apply Lim_minus.
EApply leEq_wdl.
2: Apply Lim_abs.
Simpl.
Apply str_seq_leEq_so_Lim_leEq.
Exists N; Intros.
Simpl.
EApply leEq_wdl.
Apply (HN i N) with x:=x Hx:=Hx; Auto with arith.
Apply AbsIR_wd; Rational.
Apply H1; Assumption.
Apply leEq_wdl with (AbsIR (Lim (Cauchy_const (pfpfun ? ? (incf y H3))))[-](Part (Cauchy_fun_seq_Lim ????? H) y Hy)).
2: Apply AbsIR_wd; Apply cg_minus_wd.
2: Apply eq_symmetric_unfolded; Apply Lim_const.
2: Algebra.
Simpl.
Apply leEq_wdl with (AbsIR (Lim (Build_CauchySeq IR ? 
  (Cauchy_minus (Cauchy_const (pfpfun ? ? (incf y H3))) (Build_CauchySeq ?? (Cauchy_fun_real ????? H y Hy)))))).
2: Apply AbsIR_wd; Apply Lim_minus.
EApply leEq_wdl.
2: Apply Lim_abs.
Simpl.
Apply str_seq_leEq_so_Lim_leEq.
Exists N; Intros.
Simpl.
EApply leEq_wdl.
Apply (HN N i) with x:=y Hx:=Hy; Auto.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_conv_fun_seq :
  (Cauchy_fun_seq ???? contf)->(conv_fun_seq ???? contf).
(* End_Tex_Verb *)
Intros.
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? H)); Intros.
Exists (IntPartIR (contin_imp_inc ???? H0)).
Cut (Continuous_I Hab (PartInt (IntPartIR (contin_imp_inc ???? H0)))).
2: EApply Continuous_I_wd.
3: Apply Cauchy_cont_Lim with H:=H.
2: FEQ.
2: Simpl; Apply Lim_wd'; Intros; Algebra.
Intro H2; Exists H2.
Red; Intros.
Elim (Cauchy_conv_fun_seq' H H0 e H1); Intros N HN.
Exists N; Intros.
EApply leEq_wdl.
Apply (HN n H3 x Hx).
Apply AbsIR_wd; Apply cg_minus_wd.
Algebra.
Simpl; Apply Lim_wd'; Intros; Simpl; Rational.
Simpl; Algebra.
Simpl; Apply Cauchy_cont_Lim.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_Cauchy_fun_seq :
  (conv_fun_seq ???? contf)->(Cauchy_fun_seq ???? contf).
(* End_Tex_Verb *)
Intro.
Elim H; Intros ff Hff.
Inversion_clear Hff.
Apply conv_Cauchy_fun_seq' with (PartInt ff) x.
Unfold I; EApply conv_fun_seq'_wd.
Apply H0.
Qed.

(* Tex_Prose
More interesting is the fact that a convergent sequence of functions converges pointwise as a sequence of real numbers.
*)

(* Begin_Tex_Verb *)
Lemma fun_conv_imp_seq_conv :
  (conv_fun_seq' ????? contf contF)->
  (x:IR)(Compact Hab x)->(Hxf,HxF:?)
  (Cauchy_Lim_prop2 [n:nat]((f n) x (Hxf n)) (F x HxF)).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H eps H1).
Intros N HN.
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_wdl.
Apply (HN m H2 x H0).
Apply AbsIR_wd; Algebra.
Qed.

(* Tex_Prose
And a sequence of real numbers converges iff the corresponding sequence of constant functions converges to the corresponding constant function.
*)

(* Begin_Tex_Verb *)
Lemma seq_conv_imp_fun_conv : (x,y:?)(Cauchy_Lim_prop2 x y)->
  (Hf,HF:?)(conv_fun_seq' a b Hab [n:nat]{-C-}(x n) {-C-}y Hf HF).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H e H0); Intros N HN.
Exists N; Intros; Simpl.
Apply AbsSmall_imp_AbsIR.
Auto.
Qed.

End More_Properties.

Hints Resolve Cauchy_cont_Lim : continuous.

Section Algebraic_Properties.

(* Tex_Prose
\section{Algebraic Properties}

We now study how convergence is affected by algebraic operations, and some algebraic properties of the Limit function.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables f,g:nat->PartIR.
Hypothesis contf:(n:nat)(Continuous_I Hab (f n)).
Hypothesis contg:(n:nat)(Continuous_I Hab (g n)).

(* Tex_Prose
First, the Limit function is unique.
*)

(* Begin_Tex_Verb *)
Lemma FLim_unique : (F,G,HF,HG:?)
  (conv_fun_seq' a b Hab f F contf HF)->
  (conv_fun_seq' a b Hab f G contf HG)->
  (Feq (Compact Hab) F G).
(* End_Tex_Verb *)
Intros.
Cut (Cauchy_fun_seq ?? Hab ? contf); Intros.
Apply Feq_transitive with (Cauchy_fun_seq_Lim ????? H1).
FEQ.
Simpl.
Apply Limits_unique.
Simpl.
EApply fun_conv_imp_seq_conv with Hab:=Hab Hxf:=[n:nat](contin_imp_inc ?? Hab ? (contf n) x Hx'); Auto.
Apply H.
Apply Feq_symmetric.
FEQ.
Simpl.
Apply Limits_unique.
Simpl.
EApply fun_conv_imp_seq_conv with Hab:=Hab Hxf:=[n:nat](contin_imp_inc ?? Hab ? (contf n) x Hx'); Auto.
Apply H0.
Apply conv_Cauchy_fun_seq' with F HF; Auto.
Qed.

(* Tex_Prose
Constant sequences\footnote{Not to be confused with sequences of constant functions!} always converge.
*)

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_const : (H:PartIR)(contH,contH':?)
  (conv_fun_seq' a b Hab [n:nat]H H contH contH').
(* End_Tex_Verb *)
Exists O; Intros.
EApply leEq_wdl.
2: EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Apply less_leEq; Assumption.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_const : (H:PartIR)(contH:?)
  (Cauchy_fun_seq a b Hab [n:nat]H contH).
(* End_Tex_Verb *)
Intros.
Apply conv_Cauchy_fun_seq' with H (contH O).
Apply fun_Lim_seq_const.
Qed.

(* Tex_Prose
We now prove that if two sequences converge than their Sum (difference, product) also converge to the Sum (difference, product) of their Limits.
*)

Variables F,G:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis contG:(Continuous_I Hab G).

(* Begin_Tex_Verb *)
Hypothesis convF:(conv_fun_seq' a b Hab f F contf contF).
Hypothesis convG:(conv_fun_seq' a b Hab g G contg contG).
(* End_Tex_Verb *)

Local incf:=[n:nat](contin_imp_inc ???? (contf n)).
Local incg:=[n:nat](contin_imp_inc ???? (contg n)).
Local incF:=(contin_imp_inc ???? contF).
Local incG:=(contin_imp_inc ???? contG).

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_plus' : (H,H':?)
  (conv_fun_seq' a b Hab [n:nat](f n){+}(g n) F{+}G H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (convF ? (pos_div_two ?? H0)); Intros Nf HNf.
Elim (convG ? (pos_div_two ?? H0)); Intros Ng HNg.
Cut (le Nf (max Nf Ng)); [Intro | Apply le_max_l].
Cut (le Ng (max Nf Ng)); [Intro | Apply le_max_r].
Exists (max Nf Ng); Intros.
Apply leEq_wdl with (AbsIR ((pfpfun ? ? (incf n x Hx))[+](pfpfun ? ? (incg n x Hx)))[-]((pfpfun ? ? (incF x Hx))[+](pfpfun ? ? (incG x Hx)))).
2: Apply AbsIR_wd; Simpl; Algebra.
Apply leEq_wdl with (AbsIR ((pfpfun ? ? (incf n x Hx))[-](pfpfun ? ? (incF x Hx)))[+]((pfpfun ? ? (incg n x Hx))[-](pfpfun ? ? (incG x Hx)))).
2: Apply AbsIR_wd; Simpl; Rational.
RStepr e[/]TwoNZ[+]e[/]TwoNZ.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
Unfold incf; Apply HNf; Apply le_trans with (max Nf Ng); Auto.
Unfold incg; Apply HNg; Apply le_trans with (max Nf Ng); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_minus' : (H,H':?)
  (conv_fun_seq' a b Hab [n:nat](f n){-}(g n) F{-}G H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (convF ? (pos_div_two ?? H0)); Intros Nf HNf.
Elim (convG ? (pos_div_two ?? H0)); Intros Ng HNg.
Cut (le Nf (max Nf Ng)); [Intro | Apply le_max_l].
Cut (le Ng (max Nf Ng)); [Intro | Apply le_max_r].
Exists (max Nf Ng); Intros.
Apply leEq_wdl with (AbsIR ((pfpfun ? ? (incf n x Hx))[-](pfpfun ? ? (incg n x Hx)))[-]((pfpfun ? ? (incF x Hx))[-](pfpfun ? ? (incG x Hx)))).
2: Apply AbsIR_wd; Simpl; Algebra.
Apply leEq_wdl with (AbsIR ((pfpfun ? ? (incf n x Hx))[-](pfpfun ? ? (incF x Hx)))[-]((pfpfun ? ? (incg n x Hx))[-](pfpfun ? ? (incG x Hx)))).
2: Apply AbsIR_wd; Simpl; Rational.
RStepr e[/]TwoNZ[+]e[/]TwoNZ.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both.
Unfold incf; Apply HNf; Apply le_trans with (max Nf Ng); Auto.
Unfold incg; Apply HNg; Apply le_trans with (max Nf Ng); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_mult' : (H,H':?)
  (conv_fun_seq' a b Hab [n:nat](f n){*}(g n) F{*}G H H').
(* End_Tex_Verb *)
Intros.
LetTac nF := (Norm_Funct contF).
LetTac nG := (Norm_Funct contG).
Red; Intros.
LetTac ee:=(Min e One).
Cut (Zero[<]ee); Intros.
LetTac eg:= (ee[/]ThreeNZ)[/]?[//](max_one_ap_zero nF).
LetTac ef:= (ee[/]ThreeNZ)[/]?[//](max_one_ap_zero nG).
Cut (Zero[<]eg).
Intro Heg.
Cut (Zero[<]ef).
Intro Hef.
Elim (convF ? Hef); Intros NF HNF; Clear convF.
Elim (convG ? Heg); Intros NG HNG; Clear convG.
Cut (le NF (max NF NG)); [Intro | Apply le_max_l].
Cut (le NG (max NF NG)); [Intro | Apply le_max_r].
Exists (max NF NG); Intros.
Apply leEq_transitive with ee.
2: Unfold ee; Apply Min_leEq_lft.
Apply leEq_wdl with (AbsIR ((pfpfun ? ? (incf n x Hx))[*](pfpfun ? ? (incg n x Hx)))[-]((pfpfun ? ? (incF x Hx))[*](pfpfun ? ? (incG x Hx)))).
2: Apply AbsIR_wd; Simpl; Algebra.
Apply leEq_wdl with (AbsIR (pfpfun ? ? (incF x Hx))[*]((pfpfun ? ? (incg n x Hx))[-](pfpfun ? ? (incG x Hx)))[+]
  ((pfpfun ? ? (incf n x Hx))[-](pfpfun ? ? (incF x Hx)))[*]((pfpfun ? ? (incg n x Hx))[-](pfpfun ? ? (incG x Hx)))[+]
  (pfpfun ? ? (incG x Hx))[*]((pfpfun ? ? (incf n x Hx))[-](pfpfun ? ? (incF x Hx)))).
2: Apply AbsIR_wd; Simpl; Rational.
RStepr ee[/]ThreeNZ[+]ee[/]ThreeNZ[+]ee[/]ThreeNZ.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with (Max nF One)[*](AbsIR (pfpfun ? ? (incg n x Hx))[-](pfpfun ? ? (incG x Hx))).
Apply mult_resp_leEq_rht.
Apply leEq_transitive with nF.
Unfold nF; Apply norm_bnd_AbsIR; Assumption.
Apply lft_leEq_Max.
Apply AbsIR_nonneg.
EApply shift_mult_leEq'.
Apply pos_max_one.
Unfold eg in HNG; Unfold incg; Apply HNG; Apply le_trans with (max NF NG); Auto.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with (ee[/]ThreeNZ)[*](ee[/]ThreeNZ).
2: Stepr ee[/]ThreeNZ[*]One; Apply mult_resp_leEq_lft.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
EApply leEq_transitive.
Unfold incf; Apply HNF; Apply le_trans with (max NF NG); Auto.
Unfold ef.
Apply shift_div_leEq.
Apply pos_max_one.
Step (ee[/]ThreeNZ)[*]One; Apply mult_resp_leEq_lft.
Apply rht_leEq_Max.
Apply less_leEq; Apply shift_less_div; Step (Zero::IR); [Apply pos_three | Assumption].
EApply leEq_transitive.
Unfold incg; Apply HNG; Apply le_trans with (max NF NG); Auto.
Unfold eg.
Apply shift_div_leEq.
Apply pos_max_one.
Step (ee[/]ThreeNZ)[*]One; Apply mult_resp_leEq_lft.
Apply rht_leEq_Max.
Apply less_leEq; Apply shift_less_div; Step (Zero::IR); [Apply pos_three | Assumption].
Apply shift_div_leEq.
Apply pos_three.
Stepr (Three::IR).
Unfold ee; Apply leEq_transitive with (One::IR).
Apply Min_leEq_rht.
Apply less_leEq; Apply one_less_three.
Apply less_leEq; Apply shift_less_div.
Apply pos_three.
Step (Zero::IR); Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with (Max nG One)[*](AbsIR (pfpfun ? ? (incf n x Hx))[-](pfpfun ? ? (incF x Hx))).
Apply mult_resp_leEq_rht.
Apply leEq_transitive with nG.
Unfold nG; Apply norm_bnd_AbsIR; Assumption.
Apply lft_leEq_Max.
Apply AbsIR_nonneg.
EApply shift_mult_leEq'.
Apply pos_max_one.
Unfold ef in HNF; Unfold incf; Apply HNF; Apply le_trans with (max NF NG); Auto.
Unfold ef.
Apply div_resp_pos.
Apply pos_max_one.
Apply shift_less_div; Step (Zero::IR); [Apply pos_three | Assumption].
Unfold eg.
Apply div_resp_pos.
Apply pos_max_one.
Apply shift_less_div; Step (Zero::IR); [Apply pos_three | Assumption].
Unfold ee; Apply less_Min.
Assumption.
Apply pos_one.
Qed.

End Algebraic_Properties.

Section More_Algebraic_Properties.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables f,g:nat->PartIR.
Hypothesis contf : (n:nat)(Continuous_I Hab (f n)).
Hypothesis contg : (n:nat)(Continuous_I Hab (g n)).

(* Tex_Prose
The same is true if we don't make the limits explicit.
*)

(* Begin_Tex_Verb *)
Hypothesis Hf:(Cauchy_fun_seq ???? contf).
Hypothesis Hg:(Cauchy_fun_seq ???? contg).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_plus : (H,H':?)
  (conv_fun_seq' a b Hab [n:nat](f n){+}(g n)
    (Cauchy_fun_seq_Lim ????? Hf){+}(Cauchy_fun_seq_Lim ????? Hg)
    H H').
(* End_Tex_Verb *)
Intros.
LetTac F:=(Cauchy_fun_seq_Lim ????? Hf).
Cut (Continuous_I Hab F); Intros.
2: Unfold F; Apply Cauchy_cont_Lim.
Cut (conv_fun_seq' ????? contf H0).
2: Unfold F; Apply Cauchy_conv_fun_seq'; Assumption.
Intro Hf'.
LetTac G:=(Cauchy_fun_seq_Lim ????? Hg).
Cut (Continuous_I Hab G); Intros.
2: Unfold G; Apply Cauchy_cont_Lim.
Cut (conv_fun_seq' ????? contg H1).
2: Unfold G; Apply Cauchy_conv_fun_seq'; Assumption.
Intro Hg'.
Apply fun_Lim_seq_plus' with contf contg H0 H1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_plus : (H:?)
  (Cauchy_fun_seq a b Hab [n:nat](f n){+}(g n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? Hf){+}(Cauchy_fun_seq_Lim ????? Hg)); [Intro | Contin].
Apply conv_Cauchy_fun_seq' with (Cauchy_fun_seq_Lim ????? Hf){+}(Cauchy_fun_seq_Lim ????? Hg) H0.
Apply fun_Lim_seq_plus.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_minus : (H,H':?)
  (conv_fun_seq' a b Hab [n:nat](f n){-}(g n)
    (Cauchy_fun_seq_Lim ????? Hf){-}(Cauchy_fun_seq_Lim ????? Hg)
    H H').
(* End_Tex_Verb *)
Intros.
LetTac F:=(Cauchy_fun_seq_Lim ????? Hf).
Cut (Continuous_I Hab F); Intros.
2: Unfold F; Apply Cauchy_cont_Lim.
Cut (conv_fun_seq' ????? contf H0).
2: Unfold F; Apply Cauchy_conv_fun_seq'; Assumption.
Intro Hf'.
LetTac G:=(Cauchy_fun_seq_Lim ????? Hg).
Cut (Continuous_I Hab G); Intros.
2: Unfold G; Apply Cauchy_cont_Lim.
Cut (conv_fun_seq' ????? contg H1).
2: Unfold G; Apply Cauchy_conv_fun_seq'; Assumption.
Intro Hg'.
Apply fun_Lim_seq_minus' with contf contg H0 H1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_minus : (H:?)
  (Cauchy_fun_seq a b Hab [n:nat](f n){-}(g n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? Hf){-}(Cauchy_fun_seq_Lim ????? Hg)); [Intro | Contin].
Apply conv_Cauchy_fun_seq' with ((Cauchy_fun_seq_Lim ????? Hf){-}(Cauchy_fun_seq_Lim ????? Hg)) H0.
Apply fun_Lim_seq_minus.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_mult : (H,H':?)
  (conv_fun_seq' a b Hab [n:nat](f n){*}(g n)
    (Cauchy_fun_seq_Lim ????? Hf){*}(Cauchy_fun_seq_Lim ????? Hg)
    H H').
(* End_Tex_Verb *)
Intros.
LetTac F:=(Cauchy_fun_seq_Lim ????? Hf).
Cut (Continuous_I Hab F); [Intro | Unfold F; Contin].
Cut (conv_fun_seq' ????? contf H0).
2: Unfold F; Apply Cauchy_conv_fun_seq'; Assumption.
Intro convF.
LetTac G:=(Cauchy_fun_seq_Lim ????? Hg).
Cut (Continuous_I Hab G); [Intro | Unfold G; Contin].
Cut (conv_fun_seq' ????? contg H1).
2: Unfold G; Apply Cauchy_conv_fun_seq'; Assumption.
Intro convG.
Cut (Continuous_I Hab F); [Intro HF' | Unfold F I; Apply Cauchy_cont_Lim; Assumption].
Cut (Continuous_I Hab G); [Intro HG' | Unfold G I; Apply Cauchy_cont_Lim; Assumption].
Apply fun_Lim_seq_mult' with contf contg H0 H1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_mult : (H:?)
  (Cauchy_fun_seq a b Hab [n:nat](f n){*}(g n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous_I Hab ((Cauchy_fun_seq_Lim ????? Hf){*}(Cauchy_fun_seq_Lim ????? Hg))); [Intro | Contin].
Apply conv_Cauchy_fun_seq' with ((Cauchy_fun_seq_Lim ????? Hf){*}(Cauchy_fun_seq_Lim ????? Hg)) H0.
Apply fun_Lim_seq_mult.
Qed.

End More_Algebraic_Properties.

Section Still_More_Algebraic_Properties.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable f:nat->PartIR.
Hypothesis contf : (n:nat)(Continuous_I Hab (f n)).
Hypothesis Hf:(Cauchy_fun_seq ???? contf).

(* Tex_Prose
As a corollary, we get the analogous property for the sequence of algebraic inverse functions.
*)

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_inv : (H,H':?)
  (conv_fun_seq' a b Hab [n:nat]{--}(f n)
    {--}(Cauchy_fun_seq_Lim ????? Hf) H H').
(* End_Tex_Verb *)
Intros.
Cut (n:nat)(Continuous_I Hab ({-C-}Zero{-}(f n))); Intros.
Unfold I; EApply conv_fun_seq'_wdl with [n:nat]{-C-}Zero{-}(f n) H0 H'.
Intro; FEQ; Try (Apply contin_imp_inc; Apply contf).
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (fun_Cauchy_prop_const a b Hab {-C-}Zero [n:nat](Continuous_I_const ????))){-}(Cauchy_fun_seq_Lim ????? Hf)); Intros.
Apply conv_fun_seq'_wdr with H0
  (Cauchy_fun_seq_Lim ????? (fun_Cauchy_prop_const a b Hab {-C-}Zero [n:nat](Continuous_I_const ????))){-}(Cauchy_fun_seq_Lim ????? Hf) H1.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl.
Stepr Zero[-](Lim (Build_CauchySeq ?? (Cauchy_fun_real ???? contf Hf x Hx'))).
Apply cg_minus_wd.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply Lim_const.
Apply Lim_wd'; Intros; Simpl; Algebra.
Apply Lim_wd'; Intros; Simpl; Rational.
Apply fun_Lim_seq_minus with f:=[n:nat]({-C-}Zero::PartIR).
Contin.
Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_inv : (H:?)
  (Cauchy_fun_seq a b Hab [n:nat]{--}(f n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous_I Hab {--}(Cauchy_fun_seq_Lim ????? Hf)); [Intro | Contin].
Apply conv_Cauchy_fun_seq' with ({--}(Cauchy_fun_seq_Lim ????? Hf)) H0.
Apply fun_Lim_seq_inv.
Qed.

End Still_More_Algebraic_Properties.

Hints Resolve Continuous_I_Sum Continuous_I_Sumx Continuous_I_Sum0 : continuous.
