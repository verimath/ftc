(* $Id: FunctSeries.v,v 1.17 2003/03/13 12:06:19 lcf Exp $ *)

Require Export FunctSequence.
Require Export Series.

Section Definitions.

(* Tex_Prose
\chapter{Series of Functions}

We now turn our attention to series of functions.  Like it was already the case for sequences, we will mainly rewrite the results we proved for series of real numbers in a different way.

\begin{convention} Throughout this section:
\begin{itemize}
\item \verb!a! and \verb!b! will be real numbers and the interval $[a,b]$ will be denoted by \verb!I!;
\item \verb!f, g! and \verb!h! will denote sequences of \emph{continuous} functions;
\item \verb!F, G! and \verb!H! will denote continuous functions.
\end{itemize}
\end{convention}

\section{Definitions}

As before, we will consider only sequences of continuous functions defined in a compact interval.  For this, partial Sums are defined and convergence is simply the convergence of the sequence of partial Sums.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable f:nat->PartIR.

(* Begin_Tex_Verb *)
Definition fun_seq_part_sum [n:nat] := (FSum0 n f).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_seq_part_sum_cont : ((n:nat)(Continuous_I Hab (f n)))->
  (n:nat)(Continuous_I Hab (fun_seq_part_sum n)).
(* End_Tex_Verb *)
Intros; Unfold fun_seq_part_sum.
Contin.
Qed.

(* Begin_Tex_Verb *)
Definition fun_series_convergent := {contf:? &
  (Cauchy_fun_seq ?? Hab
    fun_seq_part_sum (fun_seq_part_sum_cont contf))}.
(* End_Tex_Verb *)

(* Tex_Prose
For what comes up next we need to know that the convergence of a series of functions implies pointwise convergence of the corresponding real number series.
*)

(* Begin_Tex_Verb *)
Lemma fun_series_conv_imp_conv : fun_series_convergent->
  (x:IR)(I x)->(Hx:?)(convergent [n:nat]((f n) x (Hx n))).
(* End_Tex_Verb *)
Intros.
Red.
Red.
Intros e He.
Elim H; Intros incF convF.
Elim (convF ? He).
Intros N HN.
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
Simpl in HN.
EApply leEq_wdl.
Apply (HN m N H1 (le_n N) x H0).
Apply AbsIR_wd.
Apply cg_minus_wd; Unfold seq_part_sum; Apply Sum0_wd; Intros; Rational.
Qed.

(* Tex_Prose
We then define the Sum of the series as being the pointwise Sum of the corresponding series.
*)

(* Begin_Tex_Verb *)
Hypothesis H:fun_series_convergent.
(* End_Tex_Verb *)

Local contf:=(ProjS1 H).
Local incf:=[n:nat](contin_imp_inc ???? (contf n)).

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_strext : (x,y:IR)(Hx:(I x))(Hy:(I y))
  (((series_sum ?
    (fun_series_conv_imp_conv H x Hx [n:nat](incf n x Hx)))[#]
  (series_sum ?
    (fun_series_conv_imp_conv H y Hy [n:nat](incf n y Hy))))->
  (x[#]y)).
(* End_Tex_Verb *)
Intros.
Unfold series_sum in H0.
Elim (Lim_strext ?? H0); Intros m Hm.
Simpl in Hm; Unfold seq_part_sum in Hm.
Elim (Sum0_strext ???? Hm); Intros i H1 H2.
Exact (pfstrx ?????? H2).
Qed.

(* Begin_Tex_Verb *)
Definition Fun_Series_Sum : PartIR.
(* End_Tex_Verb *)
Apply Build_PartFunct with pfpfun:=[x:IR][Hx:(I x)](series_sum ? (fun_series_conv_imp_conv H x Hx [n:nat](incf n x Hx))).
Unfold I; Apply compact_wd.
Exact Fun_Series_Sum_strext.
Defined.

End Definitions.

Implicits Fun_Series_Sum [1 2 3 4].

Hints Resolve fun_seq_part_sum_cont : continuous.

Section More_Definitions.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.

Variable f:nat->PartIR.
(* Tex_Prose
A series can also be absolutely convergent.
*)

(* Begin_Tex_Verb *)
Definition fun_series_abs_convergent := (fun_series_convergent ?? Hab [n:nat](FAbs (f n))).
(* End_Tex_Verb *)

End More_Definitions.

Section Operations.

(* Tex_Prose
\section{Algebraic Properties}

All of these are analogous to the properties for series of real numbers, so we won't comment much about them.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Lemma fun_seq_part_sum_n :
  (f:nat->PartIR)(H':(n:nat)(Continuous_I Hab (f n)))
  (m,n:nat)(lt O n)->(le m n)->(Feq I
    (fun_seq_part_sum f n){-}(fun_seq_part_sum f m)
    (FSum m (pred n) f)).
(* End_Tex_Verb *)
Intros.
Unfold fun_seq_part_sum.
Apply eq_imp_Feq.
Unfold I; Apply contin_imp_inc; Contin.
Unfold I; Apply contin_imp_inc; Contin.
Intros; Simpl.
Unfold Sum Sum1.
Rewrite (S_pred n O); Auto.
Apply cg_minus_wd; Apply Sum0_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_const_series : (x:nat->IR)(convergent x)->
  (fun_series_convergent ?? Hab [n:nat]{-C-}(x n)).
(* End_Tex_Verb *)
Intros.
Red.
Exists [n:nat](Continuous_I_const ?? Hab (x n)).
Apply Cauchy_fun_seq2_seq.
Red; Intros e He.
Elim (H e He); Intros N HN.
Exists N; Intros.
Simpl.
Apply AbsSmall_imp_AbsIR.
Apply AbsSmall_wd_rht_unfolded with (seq_part_sum x m)[-](seq_part_sum x N).
Apply HN; Assumption.
Unfold seq_part_sum; Simpl.
Apply cg_minus_wd; Apply Sum0_wd; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_const_series_sum : (y:nat->IR)(H:(convergent y))
  (H':(fun_series_convergent ?? Hab [n:nat]{-C-}(y n)))
  (x:IR)(Hx:(I x))((Fun_Series_Sum H') x Hx)[=]
    (series_sum ? H).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply series_sum_wd.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_zero_fun_series :
  (fun_series_convergent ?? Hab [n:nat]{-C-}Zero).
(* End_Tex_Verb *)
Apply conv_fun_const_series with x:=[n:nat](Zero::IR).
Apply conv_zero_series.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_zero :
  (H:(fun_series_convergent ?? Hab [n:nat]{-C-}Zero))
  (x:IR)(Hx:?)((Fun_Series_Sum H) x Hx)[=]Zero.
(* End_Tex_Verb *)
Intros.
Simpl.
Apply series_sum_zero.
Qed.

(* Begin_Tex_Verb *)
Variables f,g:nat->PartIR.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_series_convergent_wd : ((n:nat)(Feq I (f n) (g n)))->
  (fun_series_convergent ?? Hab f)->
  (fun_series_convergent ?? Hab g).
(* End_Tex_Verb *)
Intros.
Red; Red in H0.
Elim H0; Intros contF convF.
Cut (n:nat)(Continuous_I Hab (g n)); Intros.
Exists H1.
Apply Cauchy_fun_seq_wd with (fun_seq_part_sum f) (fun_seq_part_sum_cont ???? contF).
2: Assumption.
Intros.
Apply eq_imp_Feq.
Apply contin_imp_inc; Contin.
Apply contin_imp_inc; Contin.
Intros; Simpl.
Apply Sum0_wd.
Intro; Elim (H i); Intros.
Inversion_clear a0; Auto.
Apply Continuous_I_wd with (f n); Auto.
Qed.

(* Begin_Tex_Verb *)
Hypothesis convF : (fun_series_convergent ?? Hab f).
Hypothesis convG : (fun_series_convergent ?? Hab g).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_wd' : ((n:nat)(Feq I (f n) (g n)))->
  (Feq I (Fun_Series_Sum convF) (Fun_Series_Sum convG)).
(* End_Tex_Verb *)
Intros.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl.
Apply series_sum_wd.
Intro; Elim (H n); Intros.
Inversion_clear a0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_series_plus :
  (fun_series_convergent ?? Hab [n:nat](f n){+}(g n)).
(* End_Tex_Verb *)
Elim convF; Intros contF convF'.
Elim convG; Intros contG convG'.
LetTac H:=[n:nat](Continuous_I_plus ????? (contF n) (contG n)); Exists H.
Cut (n:nat)(Continuous_I Hab (fun_seq_part_sum f n){+}(fun_seq_part_sum g n)); [Intro | Contin].
Apply Cauchy_fun_seq_wd with f:=[n:nat](fun_seq_part_sum f n){+}(fun_seq_part_sum g n) contf:=H0.
2: EApply fun_Cauchy_prop_plus; Auto; [Apply convF' | Apply convG'].
Intros; Apply eq_imp_Feq.
Included.
Apply contin_imp_inc; Contin.
Intros; Simpl.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply Sum0_plus_Sum0.
Apply Sum0_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_plus :
  (H:(fun_series_convergent ?? Hab [n:nat](f n){+}(g n)))
  (Feq I (Fun_Series_Sum H)
         (Fun_Series_Sum convF){+}(Fun_Series_Sum convG)).
(* End_Tex_Verb *)
Intros.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl.
Elim convF; Intros contF convF'.
Elim convG; Intros contG convG'.
Cut (convergent 
  [n:nat](pfpfun ? ? (contin_imp_inc ???? (contF n) x (ProjIR1 Hx')))[+](pfpfun ? ? (contin_imp_inc ???? (contG n) x (ProjIR2 Hx')))); Intros.
EApply eq_transitive_unfolded.
2: Apply series_sum_plus with
  x:=[n:nat](pfpfun ? ? (contin_imp_inc ???? (contF n) x (ProjIR1 Hx'))) 
  y:=[n:nat](pfpfun ? ? (contin_imp_inc ???? (contG n) x (ProjIR2 Hx'))) 
  H:=H1.
Apply series_sum_wd; Intro; Rational.
Red; Red; Intros.
Elim H; Intros cont H'.
Elim (H' ? H1); Intros N HN.
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_wdl.
Apply (HN m N H2 (le_n N) x H0).
Apply AbsIR_wd; Unfold fun_seq_part_sum.
Simpl.
Unfold seq_part_sum; Apply cg_minus_wd; Apply Sum0_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_series_minus :
  (fun_series_convergent ?? Hab [n:nat](f n){-}(g n)).
(* End_Tex_Verb *)
Elim convF; Intros contF convF'.
Elim convG; Intros contG convG'.
LetTac H:=[n:nat](Continuous_I_minus ????? (contF n) (contG n)); Exists H.
Cut (n:nat)(Continuous_I Hab (fun_seq_part_sum f n){-}(fun_seq_part_sum g n)); [Intro | Contin].
Apply Cauchy_fun_seq_wd with f:=[n:nat](fun_seq_part_sum f n){-}(fun_seq_part_sum g n) contf:=H0.
2: EApply fun_Cauchy_prop_minus; Auto; [Apply convF' | Apply convG'].
Intros; Apply eq_imp_Feq.
Included.
Apply contin_imp_inc; Contin.
Intros; Simpl.
Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with (Sum0 n [i:nat]((f i) x (ProjIR1 Hx i)))[+](Sum0 n [i:nat][--]((g i) x (ProjIR2 Hx i))).
EApply eq_transitive_unfolded.
2: Apply Sum0_plus_Sum0.
Apply Sum0_wd; Intros; Rational.
Unfold cg_minus.
Apply bin_op_wd_unfolded.
Algebra.
EApply eq_transitive_unfolded.
2: Apply inv_Sum0.
Apply Sum0_wd; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_minus :
  (H:(fun_series_convergent ?? Hab [n:nat](f n){-}(g n)))
  (Feq I (Fun_Series_Sum H)
         (Fun_Series_Sum convF){-}(Fun_Series_Sum convG)).
(* End_Tex_Verb *)
Intros.
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl.
Elim convF; Intros contF convF'.
Elim convG; Intros contG convG'.
Cut (convergent 
  [n:nat](pfpfun ? ? (contin_imp_inc ???? (contF n) x (ProjIR1 Hx')))[-](pfpfun ? ? (contin_imp_inc ???? (contG n) x (ProjIR2 Hx')))); Intros.
Apply eq_transitive_unfolded with 
  (series_sum ? (fun_series_conv_imp_conv ???? convF x (ProjIR1 Hx') [n:nat](contin_imp_inc ???? (contF n) x (ProjIR1 Hx'))))[-]
  (series_sum ? (fun_series_conv_imp_conv ???? convG x (ProjIR2 Hx') [n:nat](contin_imp_inc ???? (contG n) x (ProjIR2 Hx')))).
EApply eq_transitive_unfolded.
2: Apply series_sum_minus with
  x:=[n:nat](pfpfun ? ? (contin_imp_inc ???? (contF n) x (ProjIR1 Hx'))) 
  y:=[n:nat](pfpfun ? ? (contin_imp_inc ???? (contG n) x (ProjIR2 Hx'))) 
  H:=H1.
Apply series_sum_wd; Intro; Rational.
Apply cg_minus_wd; Apply series_sum_wd; Intro; Rational.
Red; Red; Intros.
Elim H; Intros cont H'.
Elim (H' ? H1); Intros N HN.
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_wdl.
Apply (HN m N H2 (le_n N) x H0).
Apply AbsIR_wd; Unfold fun_seq_part_sum.
Simpl.
Unfold seq_part_sum; Apply cg_minus_wd; Apply Sum0_wd; Intros; Rational.
Qed.

(* Tex_Prose
\begin{convention} Let \verb!c:IR!.
\end{convention}
*)

Variable c:IR.
Variable H:PartIR.
Hypothesis contH:(Continuous_I Hab H).

(* Begin_Tex_Verb *)
Lemma conv_fun_series_mult_scal :
  (fun_series_convergent ?? Hab [n:nat]H{*}(f n)).
(* End_Tex_Verb *)
Elim convF; Intros contF convF'.
LetTac H':=[n:nat](Continuous_I_mult ????? contH (contF n)); Exists H'.
Cut (n:nat)(Continuous_I Hab (fun_seq_part_sum f n)); [Intro | Contin].
Cut (n:nat)(Continuous_I Hab H{*}(fun_seq_part_sum f n)); [Intro | Contin].
Unfold I; Apply Cauchy_fun_seq_wd with [n:nat]H{*}(fun_seq_part_sum f n) H1.
2: Apply fun_Cauchy_prop_mult with f:=[n:nat]H contf:=[n:nat]contH g:=(fun_seq_part_sum f) contg:=H0.
Intro; FEQ.
Apply contin_imp_inc; Contin.
Simpl.
Unfold seq_part_sum.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
2: Apply Sum0_comm_scal' with x:=[m:nat]((f m) x (ProjIR2 Hx m)).
Apply Sum0_wd; Intros; Rational.
Apply fun_Cauchy_prop_const.
Apply Cauchy_fun_seq_wd with f:=(fun_seq_part_sum f) contf:=(fun_seq_part_sum_cont ???? contF).
2: Assumption.
Intro; Apply Feq_reflexive; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_mult_scal :
  (H':(fun_series_convergent ?? Hab [n:nat]H{*}(f n)))
  (Feq I (Fun_Series_Sum H') H{*}(Fun_Series_Sum convF)).
(* End_Tex_Verb *)
Elim convF; Intros contF convF'.
Intros.
Unfold I; FEQ.
Cut (convergent [n:nat](Part H x (ProjIR1 Hx'))[*]((f n) x (contin_imp_inc ???? (contF n) ? (ProjIR2 Hx')))); Intros.
Apply eq_transitive_unfolded with 
  (series_sum [n:nat](Part H x (ProjIR1 Hx'))[*]((f n) x (contin_imp_inc ???? (contF n) ? (ProjIR2 Hx'))) H1).
2: Simpl; Apply series_sum_mult_scal with x:=[n:nat]((f n) x (contin_imp_inc ???? (contF n) ? (ProjIR2 Hx'))).
Simpl; Unfold series_sum.
Apply Lim_wd'; Intros; Simpl.
Unfold seq_part_sum; Apply Sum0_wd; Intros; Rational.
Red; Red; Intros.
Elim H'; Intros H'' H'''.
Elim (H''' ? H1); Intros N HN.
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_wdl.
Apply (HN m N H2 (le_n N) x Hx).
Apply AbsIR_wd; Simpl.
Unfold seq_part_sum; Apply cg_minus_wd; Apply Sum0_wd; Intros; Rational.
Qed.

End Operations.

Section More_Operations.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable f:nat->PartIR.
Hypothesis convF : (fun_series_convergent ?? Hab f).

(* Begin_Tex_Verb *)
Lemma conv_fun_series_inv :
  (fun_series_convergent ?? Hab [n:nat]{--}(f n)).
(* End_Tex_Verb *)
Elim convF; Intros contF convF'.
Exists [n:nat](Continuous_I_inv ???? (contF n)).
Cut (n:nat)(Continuous_I Hab {--}(fun_seq_part_sum f n)); Intros.
Apply Cauchy_fun_seq_wd with f:=[n:nat]{--}(fun_seq_part_sum f n) contf:=H.
2: Apply fun_Cauchy_prop_inv with (fun_seq_part_sum_cont ???? contF).
Intro; FEQ.
Apply contin_imp_inc; Contin.
Simpl; Unfold seq_part_sum.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply inv_Sum0.
Apply Sum0_wd; Intro; Rational.
Assumption.
Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_inv :
  (H:(fun_series_convergent ?? Hab [n:nat]{--}(f n)))
  (Feq I (Fun_Series_Sum H) {--}(Fun_Series_Sum convF)).
(* End_Tex_Verb *)
Intros.
FEQ.
Cut (convergent [n:nat][--]((f n) x (contin_imp_inc ???? (ProjS1 convF n) x Hx'))); Intros.
Simpl; Apply eq_transitive_unfolded with (series_sum ? H1).
2: Apply series_sum_inv with x:=[n:nat]((f n) x (contin_imp_inc ???? (ProjS1 convF n) x Hx')).
Unfold series_sum; Apply Lim_wd'; Intros; Simpl.
Unfold seq_part_sum; Apply Sum0_wd; Intros.
Rational.
Apply conv_series_inv with x:=[n:nat]((f n) x (contin_imp_inc ???? (ProjS1 convF n) x Hx')).
Apply fun_series_conv_imp_conv with Hab:=Hab Hx:=[n:nat](contin_imp_inc ???? (ProjS1 convF n) x Hx'); Assumption.
Qed.

End More_Operations.

Section Other_Results.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.

Variable f:nat->PartIR.

Hypothesis convF:(fun_series_convergent a b Hab f).

(* Tex_Prose
The following relate the Sum series with the limit of the sequence of partial Sums; as a corollary we get the continuity of the Sum of the series.
*)

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_char' : (contf,H:?)(Feq (Compact Hab)
  (Fun_Series_Sum convF)
  (Cauchy_fun_seq_Lim ?? Hab (fun_seq_part_sum f) contf H)).
(* End_Tex_Verb *)
Intros.
FEQ.
Simpl; Unfold series_sum.
Apply Lim_wd'; Simpl; Intros.
Unfold seq_part_sum; Apply Sum0_wd; Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_series_conv : (H,H':?)(conv_fun_seq' a b Hab
  (fun_seq_part_sum f) (Fun_Series_Sum convF) H H').
(* End_Tex_Verb *)
Intros.
Inversion_clear convF.
Apply conv_fun_seq'_wdr with
  contf:=(fun_seq_part_sum_cont ???? x)
  contF:=(Cauchy_cont_Lim ????? H0).
2: Apply Cauchy_conv_fun_seq'.
Apply Feq_symmetric; Apply Fun_Series_Sum_char'.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_cont :
  (Continuous_I Hab (Fun_Series_Sum convF)).
(* End_Tex_Verb *)
Intros.
Inversion_clear convF.
EApply Continuous_I_wd.
Apply Feq_symmetric; Apply (Fun_Series_Sum_char' [n:nat](fun_seq_part_sum_cont ???? x n) H).
Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_char : (Feq (Compact Hab)
  (Cauchy_fun_seq_Lim ?? Hab
    (fun_seq_part_sum f) ? (ProjS2 convF))
  (Fun_Series_Sum convF)).
(* End_Tex_Verb *)
Intros.
FEQ.
Simpl.
Unfold series_sum; Apply Lim_wd'.
Intro; Simpl.
Unfold seq_part_sum; Apply Sum0_wd; Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Fun_Series_Sum_as_Lim : (Hf,H':?)(conv_fun_seq' ?? Hab
  (fun_seq_part_sum f) (Fun_Series_Sum convF) Hf H').
(* End_Tex_Verb *)
Intros.
Apply conv_fun_seq'_wdr with 
  (fun_seq_part_sum_cont ???? (ProjS1 convF)) (Cauchy_fun_seq_Lim ????? (ProjS2 convF)) (Cauchy_cont_Lim ????? (ProjS2 convF)).
Apply Fun_Series_Sum_char.
Apply Cauchy_conv_fun_seq'.
Qed.

End Other_Results.

Hints Resolve Fun_Series_Sum_cont : continuous.

Section Convergence_Criteria.

(* Tex_Prose
\section{Convergence Criteria}

Most of the convergence criteria for series of real numbers carry over to series of real-valued functions, so again we just present them without comments.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable f:nat->PartIR.
Hypothesis contF : (n:nat)(Continuous_I Hab (f n)).

(* Begin_Tex_Verb *)
Lemma fun_str_comparison : (g:nat->PartIR)
  (fun_series_convergent ?? Hab g)->
  {k:nat | ((n:nat)(le k n)->(x:IR)((I x)->(Hx,Hx':?)
    (AbsIR ((f n) x Hx))[<=](Part (g n) x Hx')))}->
  (fun_series_convergent ?? Hab f).
(* End_Tex_Verb *)
LetTac H0:=contF.
Intros.
Elim H1; Intros k Hk.
Exists H0.
Apply Cauchy_fun_seq2_seq.
Red; Intros.
Elim H; Intros contG convG.
Cut {N:nat | (lt k N)/\((m:nat)(le N m)->(x:IR)(I x)->(Hx,Hx':?)
  (AbsSmall e (Part (fun_seq_part_sum g m) x Hx)[-](Part (fun_seq_part_sum g N) x Hx')))}; Intros.
Elim H3; Clear H3.
Intros N HN; Elim HN; Clear HN; Intros HN' HN.
Exists N; Intros.
LetTac H':=[n:nat](contin_imp_inc ???? (fun_seq_part_sum_cont ???? contG n)).
Apply leEq_transitive with (Part (fun_seq_part_sum g m) x (H' m x Hx))[-](Part (fun_seq_part_sum g N) x (H' N x Hx)).
Cut (n:nat)(included (Compact Hab) (Pred (FAbs (f n)))); Intros.
Cut (Pred (FSum N (pred m) [n:nat](FRestr (H4 n))) x); Intros.
Apply leEq_transitive with (Part (FSum N (pred m) [n:nat](FRestr (H4 n))) x H5).
Cut (Pred (FSum N (pred m) [n:nat](FRestr (contin_imp_inc ???? (H0 n)))) x); Intros.
Apply leEq_wdl with (AbsIR (Part (FSum N (pred m) [n:nat](FRestr (contin_imp_inc ???? (H0 n)))) x H6)).
Opaque Frestr.
Simpl.
Transparent Frestr.
EApply leEq_wdr.
Apply triangle_SumIR.
Rewrite <- (S_pred m k); Auto; Apply lt_le_trans with N; Auto.
Simpl; Apply Sum_wd; Intros; Apply AbsIR_wd; Rational.
Apply AbsIR_wd; Apply eq_symmetric_unfolded.
Cut (Pred ((fun_seq_part_sum f m){-}(fun_seq_part_sum f N)) x); Intros.
Opaque fun_seq_part_sum.
Apply eq_transitive_unfolded with (pfpfun ? ? H7).
Simpl; Rational.
Unfold Frestr.
Apply Feq_imp_eq with I.
Apply Feq_transitive with (FSum N (pred m) f).
Unfold I; Apply fun_seq_part_sum_n; Auto with arith.
Apply le_lt_trans with k; [Idtac | Apply lt_le_trans with N]; Auto with arith.
FEQ.
Unfold I; Apply contin_imp_inc; Contin.
Simpl.
Red; Intros; Auto.
Simpl.
Apply Sum_wd; Intros; Rational.
Auto.
Split; Simpl.
Apply (contin_imp_inc ???? (fun_seq_part_sum_cont ???? H0 m)); Auto.
Apply (contin_imp_inc ???? (fun_seq_part_sum_cont ???? H0 N)); Auto.
Simpl; Auto.
Cut (Pred (FSum N (pred m) g) x); Intros.
Apply leEq_wdr with (pfpfun ? ? H6).
Apply FSum_resp_leEq.
Rewrite <- (S_pred m k); Auto; Apply lt_le_trans with N; Auto.
Intros.
Simpl.
Apply Hk.
Apply le_trans with N; Auto with arith.
Simpl in HxF.
Apply (HxF O).
Cut (Pred ((fun_seq_part_sum g m){-}(fun_seq_part_sum g N)) x); Intros.
Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with (pfpfun ? ? H7).
Simpl; Rational.
Apply Feq_imp_eq with I.
Unfold I; Apply fun_seq_part_sum_n; Auto with arith.
Apply le_lt_trans with k; [Idtac | Apply lt_le_trans with N]; Auto with arith.
Auto.
Split; Simpl.
Apply (contin_imp_inc ???? (fun_seq_part_sum_cont ???? contG m)); Auto.
Apply (contin_imp_inc ???? (fun_seq_part_sum_cont ???? contG N)); Auto.
Simpl; Intro; Apply (contin_imp_inc ???? (contG n)); Auto.
Simpl; Auto.
Unfold I; Simpl; Apply contin_imp_inc; Auto.
EApply leEq_transitive.
Apply leEq_AbsIR.
Apply AbsSmall_imp_AbsIR.
Apply HN; Assumption.
Elim (convG ? H2).
Intros N HN; Exists (S (max N k)).
Cut (le N (max N k)); [Intro | Apply le_max_l].
Cut (le k (max N k)); [Intro | Apply le_max_r].
Split.
Auto with arith.
Intros.
Apply AbsIR_imp_AbsSmall.
Cut (le N m); [Intro | Apply le_trans with (max N k); Auto with arith].
EApply leEq_wdl.
Transparent fun_seq_part_sum.
Simpl in Hx'.
Apply (HN m ? H7 (le_S ?? H3) x H6).
Opaque fun_seq_part_sum.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_comparison : (g:nat->PartIR)
  (fun_series_convergent ?? Hab g)->
  ((n:nat)(x:IR)(I x)->(Hx,Hx':?)
    (AbsIR ((f n) x Hx))[<=]((g n) x Hx'))->
  (fun_series_convergent ?? Hab f).
(* End_Tex_Verb *)
Intros.
Apply fun_str_comparison with g; Auto.
Exists O; Intros; Apply H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma abs_imp_conv : (fun_series_abs_convergent ?? Hab f)->
  (fun_series_convergent ?? Hab f).
(* End_Tex_Verb *)
Intros.
Apply fun_comparison with [n:nat](FAbs (f n)).
Apply H.
Intros; Simpl; Apply eq_imp_leEq; Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_ratio_test_conv : {N:nat & {c:IR & 
  c[<]One | (Zero[<=]c) /\
  (x:IR)(I x)->(n:nat)(le N n)->(Hx,Hx':?)
    (AbsIR ((f (S n)) x Hx'))[<=]
      c[*](AbsIR ((f n) x Hx))}}->
  (fun_series_convergent ?? Hab f).
(* End_Tex_Verb *)
Intro.
Elim H; Clear H; Intros N H.
Elim H; Clear H; Intros c Hc1 H.
Elim H; Clear H; Intros H0c H.
Cut (x:IR)(I x)->(n:nat)(le N n)->(Hx,Hx':?)(AbsIR ((f n) x Hx'))[<=](AbsIR ((f N) x Hx))[*](c[^](minus n N)).
Intro.
Apply fun_str_comparison with [n:nat]((FAbs (f N)){*}({-C-} c[^](minus n N))).
2: Exists N; Simpl; Intros.
2: Simpl in H0; Apply H0; Auto with arith.
Apply conv_fun_series_mult_scal with f:=[n:nat]({-C-}c[^](minus n N)).
Apply conv_fun_const_series with x:=[n:nat]c[^](minus n N).
Apply join_series with (power_series c).
Apply power_series_conv; Auto.
Exists N.
Exists O.
Intro.
Rewrite plus_sym; Rewrite Minus.minus_plus.
Algebra.
Contin.
Do 3 Intro; Induction n.
Intro.
Cut N=O; [Intro | Auto with arith].
Rewrite H2.
Intros.
Apply eq_imp_leEq.
Simpl.
Step (AbsIR (pfpfun ? ? Hx'))[*]One; Apply mult_wd_lft; Apply AbsIR_wd; Algebra.
Intro.
Elim (le_lt_eq_dec ?? H1); Intro.
Intros; Apply leEq_transitive with c[*](AbsIR ((f n) x (contin_imp_inc ???? (contF n) x H0))).
Apply H; Auto with arith.
Apply leEq_wdr with ((AbsIR ((f N) x Hx))[*](c[^](minus n N))[*]c).
RStepr c[*]((AbsIR (pfpfun ? ? Hx))[*](c[^](minus n N))).
Apply mult_resp_leEq_lft.
Apply Hrecn; Auto with arith.
Assumption.
Rewrite <- minus_Sn_m.
Simpl; Rational.
Auto with arith.
Rewrite b0; Intros.
Rewrite <- minus_n_n.
Apply eq_imp_leEq.
Simpl; EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply mult_one.
Apply AbsIR_wd; Algebra.
Qed.

End Convergence_Criteria.
