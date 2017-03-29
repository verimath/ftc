(* $Id: Series.v,v 1.22 2003/03/13 12:06:26 lcf Exp $ *)

Require Export CSumsReals.
Require Export NRootIR.

Opaque IR.

Section Definitions.

(* Tex_Prose
\chapter{Series of Real Numbers}

In this file we develop a theory of series of real numbers.

\section{Definitions}

A series is simply a sequence from the natural numbers into the reals.  To each such sequence we can assign a sequence of partial Sums.

\begin{convention} Let \verb!x:nat->IR!.
\end{convention}
*)

Variable x:nat->IR.

(* Begin_Tex_Verb *)
Definition seq_part_sum := [n:nat](Sum0 n x).
(* End_Tex_Verb *)

(* Tex_Prose
For subsequent purposes it will be very useful to be able to write the difference between two arbitrary elements of the sequence of partial Sums as a Sum of elements of the original sequence.
*)

(* Begin_Tex_Verb *)
Lemma seq_part_sum_n : (m,n:nat)(lt O n)->(le m n)->
  (seq_part_sum n)[-](seq_part_sum m)[=](Sum m (pred n) x).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_eq_dec ?? H0); Intro.
Unfold seq_part_sum.
Unfold Sum Sum1.
Rewrite <- S_pred with n O; Auto.
Algebra.
Rewrite b.
Step_lft (Zero::IR).
Apply eq_symmetric_unfolded; Apply Sum_empty.
Assumption.
Qed.

(* Tex_Prose
A series is convergent iff its sequence of partial Sums is a Cauchy sequence.  To each convergent series we can assign a Sum.
*)

(* Begin_Tex_Verb *)
Definition convergent := (Cauchy_prop seq_part_sum).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition series_sum [H:convergent]:=
  (Lim (Build_CauchySeq ?? H)).
(* End_Tex_Verb *)

(* Tex_Prose
Divergence can be characterized in a positive way, which will sometimes be useful.  We thus define divergence of sequences and series and prove the obvious fact that no sequence can be both convergent and divergent, whether considered either as a sequence or as a series.
*)

(* Begin_Tex_Verb *)
Definition divergent_seq [a:nat->IR] := {e:IR &
  (Zero[<]e) & (k:nat){m:nat & {n:nat |
    (le k m)/\(le k n)/\(e[<=](AbsIR (a m)[-](a n)))}}}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition divergent := (divergent_seq seq_part_sum).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma conv_imp_not_div : (a:nat->IR)
  (Cauchy_prop a)->(Not (divergent_seq a)).
(* End_Tex_Verb *)
Intros a Hconv.
Intro Hdiv.
Red in Hconv Hdiv.
Elim Hdiv; Clear Hdiv; Intros e He He'.
Elim (Hconv ? (pos_div_three ?? He)); Clear Hconv; Intros N HN.
Elim (He' N); Clear He'; Intros m Hm.
Elim Hm; Clear Hm; Intros n Hm'.
Elim Hm'; Clear Hm'; Intros Hm Hn.
Elim Hn; Clear Hn; Intros Hn Hmn.
Apply Hmn.
RStepr e[/]ThreeNZ[+]e[/]ThreeNZ[+]e[/]ThreeNZ.
Apply leEq_less_trans with (AbsIR (a m)[-](a N))[+](AbsIR (a N)[-](a n)).
EApply leEq_wdl.
Apply triangle_IR.
Apply AbsIR_wd; Rational.
Step Zero[+](AbsIR (a m)[-](a N))[+](AbsIR (a N)[-](a n)).
Repeat Apply plus_resp_less_leEq; Try Apply AbsSmall_imp_AbsIR; Try Exact (pos_div_three ?? He).
Auto.
Apply AbsSmall_minus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma div_imp_not_conv : (a:nat->IR)
  (divergent_seq a)->(Not (Cauchy_prop a)).
(* End_Tex_Verb *)
Intros.
Red; Intro.
Generalize H; Generalize H0.
Apply conv_imp_not_div.
Qed.

(* Begin_Tex_Verb *)
Lemma convergent_imp_not_divergent : convergent->(Not divergent).
(* End_Tex_Verb *)
Intro.
Intro.
Red in H H0.
Generalize H0; Apply conv_imp_not_div.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma divergent_imp_not_convergent : divergent->(Not convergent).
(* End_Tex_Verb *)
Intro.
Intro.
Red in H H0.
Generalize H0; Apply div_imp_not_conv.
Assumption.
Qed.

(* Tex_Prose
Finally we have the well known fact that every convergent series converges to zero as a sequence.
*)

(* Begin_Tex_Verb *)
Lemma series_seq_Lim : convergent->(Cauchy_Lim_prop2 x Zero).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Red in H.
Red in H.
Elim (H ? (pos_div_two ?? H0)).
Intros N HN.
Exists (max N (1)); Intros.
Apply AbsSmall_wd_rht_unfolded with (seq_part_sum (S m))[-](seq_part_sum m).
Apply AbsSmall_wd_rht_unfolded with ((seq_part_sum (S m))[-](seq_part_sum N))[+]((seq_part_sum N)[-](seq_part_sum m)).
RStep eps[/]TwoNZ[+]eps[/]TwoNZ.
Apply AbsSmall_plus.
Apply HN.
Apply le_trans with (max N (1)); Auto with arith.
Apply AbsSmall_minus; Apply HN.
Apply le_trans with (max N (1)); Auto with arith.
Rational.
EApply eq_transitive_unfolded.
Apply seq_part_sum_n; Auto with arith.
Simpl; Stepr (x m); Apply Sum_one.
Qed.

(* Begin_Tex_Verb *)
Lemma series_seq_Lim' : convergent->
  (H:(Cauchy_prop x))(Lim (Build_CauchySeq ?? H))[=]Zero.
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded; Apply Limits_unique.
Apply series_seq_Lim; Auto.
Qed.

End Definitions.

Section More_Definitions.

Variable x:nat->IR.

(* Tex_Prose
We also define absolute convergence.
*)

(* Begin_Tex_Verb *)
Definition abs_convergent := (convergent [n:nat](AbsIR (x n))).
(* End_Tex_Verb *)

End More_Definitions.

Section Power_Series.

(* Tex_Prose
\section{Power Series}

Power series are an important special case.
*)

(* Begin_Tex_Verb *)
Definition power_series [c:IR] := [n:nat]c[^]n.
(* End_Tex_Verb *)

(* Tex_Prose
Specially important is the case when $c$ is a positive real number less than 1; in this case not only the power series is convergent, but we can also compute its Sum.

\begin{convention} Let \verb!c! be a real number between $0$ and $1$.
\end{convention}
*)

Variable c:IR.
Hypothesis H0c : Zero[<=]c.
Hypothesis Hc1 : c[<]One.

(* Begin_Tex_Verb *)
Lemma c_exp_Lim : (Cauchy_Lim_prop2 (power_series c) Zero).
(* End_Tex_Verb *)
Red; Intros.
Elim (qi_yields_zero c H0c Hc1 eps H).
Intros N Hn.
Exists N; Intros.
Unfold power_series.
Stepr c[^]m.
Apply AbsSmall_transitive with c[^]N.
Apply AbsIR_imp_AbsSmall.
EApply leEq_wdl.
Apply Hn.
Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply nexp_resp_nonneg; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply nexp_resp_nonneg; Assumption.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply nexp_resp_nonneg; Assumption.
Apply nexp_resp_le'.
Assumption.
Apply less_leEq; Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma power_series_Lim1 : (H:(One[-]c)[#]Zero)
  (Cauchy_Lim_prop2 (seq_part_sum (power_series c))
                    One[/]?[//]H).
(* End_Tex_Verb *)
Intro.
Red.
Intros.
Unfold power_series; Unfold seq_part_sum.
Cut {N:nat | c[^]N[<=]eps[*](AbsIR One[-]c)}.
Intro.
Elim H1; Clear H1; Intros N HN.
Exists N; Intros.
Apply AbsSmall_wd_rht_unfolded with [--]((c[^]m)[/]?[//]H).
Apply inv_resp_AbsSmall.
Apply AbsIR_imp_AbsSmall.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded.
2: Apply (!AbsIR_division c[^]m One[-]c H (AbsIR_resp_ap_zero ? H)).
Apply shift_div_leEq.
Apply AbsIR_pos; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
EApply leEq_transitive.
2: Apply HN.
Apply nexp_resp_le'; Auto.
Apply less_leEq; Auto.
Apply nexp_resp_nonneg; Auto.
Step_lft ([--]((c[^]m)[/]?[//]H)[+]One[/]?[//]H)[-]One[/]?[//]H.
Apply cg_minus_wd.
2: Algebra.
Cut c[-]One[#]Zero; Intros.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
Apply Sum0_c_exp with H:=H2.
Rational.
Apply less_imp_ap.
Apply shift_minus_less; Stepr (One::IR); Assumption.
Apply qi_yields_zero.
Assumption.
Assumption.
Apply less_wdl with Zero[*](AbsIR One[-]c).
Apply mult_resp_less.
Assumption.
Apply AbsIR_pos.
Apply Greater_imp_ap; Apply shift_less_minus; Step c; Assumption.
Apply cring_mult_zero_op.
Qed.

(* Begin_Tex_Verb *)
Lemma power_series_conv : (convergent (power_series c)).
(* End_Tex_Verb *)
Intros.
Red.
Apply Cauchy_prop2_prop.
Cut (One[-]c)[#]Zero.
Intro.
Exists One[/]?[//]H.
Apply power_series_Lim1.
Apply Greater_imp_ap; Apply shift_less_minus; Step c; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma power_series_sum : (H:(One[-]c)[#]Zero)
  (Hc:(Cauchy_prop (seq_part_sum (power_series c))))
  (series_sum ? Hc)[=]One[/]?[//]H.
(* End_Tex_Verb *)
Intros.
Unfold series_sum.
Apply eq_symmetric_unfolded; Apply Limits_unique.
Apply power_series_Lim1.
Qed.

End Power_Series.

Section Operations.

(* Tex_Prose
\section{Operations}

Some operations with series preserve convergence.  We start by defining the series that is zero everywhere.
*)

(* Begin_Tex_Verb *)
Lemma conv_zero_series : (convergent [n:nat]Zero).
(* End_Tex_Verb *)
Exists O.
Intros.
Simpl.
EApply AbsSmall_wd_rht_unfolded.
Apply zero_AbsSmall; Apply less_leEq; Assumption.
Unfold seq_part_sum.
Induction m.
Simpl; Algebra.
Simpl.
EApply eq_transitive_unfolded.
Apply Hrecm; Auto with arith.
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma series_sum_zero : (H:(convergent [n:nat]Zero))
  (series_sum ? H)[=]Zero.
(* End_Tex_Verb *)
Intro.
Unfold series_sum.
Apply eq_symmetric_unfolded; Apply Limits_unique.
Exists O.
Intros.
Simpl.
EApply AbsSmall_wd_rht_unfolded.
Apply zero_AbsSmall; Apply less_leEq; Assumption.
Unfold seq_part_sum.
Induction m.
Simpl; Algebra.
Simpl.
EApply eq_transitive_unfolded.
Apply Hrecm; Auto with arith.
Rational.
Qed.

(* Tex_Prose
Next we consider welldefinedness, as well as the Sum and difference of two convergent series.

\begin{convention} Let \verb!x,y:nat->IR! be convergent series.
\end{convention}
*)

Variables x,y:nat->IR.

Hypothesis convX : (convergent x).
Hypothesis convY : (convergent y).

(* Begin_Tex_Verb *)
Lemma convergent_wd : ((n:nat)(x n)[=](y n))->
  (convergent x)->(convergent y).
(* End_Tex_Verb *)
Intros.
Red; Red in H0.
Apply Cauchy_prop_wd with (seq_part_sum x).
Assumption.
Intro.
Unfold seq_part_sum.
Apply Sum0_wd.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma series_sum_wd : ((n:nat)(x n)[=](y n))->
  (series_sum ? convX)[=](series_sum ? convY).
(* End_Tex_Verb *)
Intros.
Unfold series_sum.
Apply Lim_wd'.
Intro; Simpl.
Unfold seq_part_sum.
Apply Sum0_wd; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_series_plus : (convergent [n:nat](x n)[+](y n)).
(* End_Tex_Verb *)
Red.
Red in convX convY.
EApply Cauchy_prop_wd.
Apply Cauchy_plus with seq1:=(Build_CauchySeq ?? convX) seq2:=(Build_CauchySeq ?? convY).
Simpl.
Unfold seq_part_sum.
Intro.
Apply eq_symmetric_unfolded; Apply Sum0_plus_Sum0.
Qed.

(* Begin_Tex_Verb *)
Lemma series_sum_plus : (H:(convergent [n:nat](x n)[+](y n)))
  (series_sum ? H)[=](series_sum ? convX)[+](series_sum ? convY).
(* End_Tex_Verb *)
Intros.
Unfold series_sum.
EApply eq_transitive_unfolded.
2: Apply Lim_plus.
Apply Lim_wd'.
Intro; Simpl.
Unfold seq_part_sum.
Apply Sum0_plus_Sum0.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_series_minus : (convergent [n:nat](x n)[-](y n)).
(* End_Tex_Verb *)
Red.
Red in convX convY.
EApply Cauchy_prop_wd.
Apply Cauchy_minus with seq1:=(Build_CauchySeq ?? convX) seq2:=(Build_CauchySeq ?? convY).
Simpl.
Unfold seq_part_sum.
Intro.
Apply eq_symmetric_unfolded; Unfold cg_minus.
EApply eq_transitive_unfolded.
Apply Sum0_plus_Sum0 with g:=[n:nat][--](y n).
Apply bin_op_wd_unfolded.
Algebra.
Apply inv_Sum0.
Qed.

(* Begin_Tex_Verb *)
Lemma series_sum_minus : (H:(convergent [n:nat](x n)[-](y n)))
  (series_sum ? H)[=](series_sum ? convX)[-](series_sum ? convY).
(* End_Tex_Verb *)
Intros.
Unfold series_sum.
EApply eq_transitive_unfolded.
2: Apply Lim_minus.
Apply Lim_wd'.
Intro; Simpl.
Unfold seq_part_sum.
Unfold cg_minus.
EApply eq_transitive_unfolded.
Apply Sum0_plus_Sum0 with g:=[n:nat][--](y n).
Apply bin_op_wd_unfolded.
Algebra.
Apply inv_Sum0.
Qed.

(* Tex_Prose
Multiplication by a scalar $c$ is also permitted.
*)

Variable c:IR.

(* Begin_Tex_Verb *)
Lemma conv_series_mult_scal : (convergent [n:nat]c[*](x n)).
(* End_Tex_Verb *)
Red.
Red in convX.
EApply Cauchy_prop_wd.
Apply Cauchy_mult with seq2:=(Build_CauchySeq ?? convX) seq1:=(Cauchy_const c).
Simpl.
Unfold seq_part_sum.
Intro.
Apply eq_symmetric_unfolded.
Apply Sum0_comm_scal'.
Qed.

(* Begin_Tex_Verb *)
Lemma series_sum_mult_scal : (H:(convergent [n:nat]c[*](x n)))
  (series_sum ? H)[=]c[*](series_sum ? convX).
(* End_Tex_Verb *)
Intros.
Unfold series_sum.
Apply eq_transitive_unfolded with (Lim (Cauchy_const c))[*](Lim (Build_CauchySeq ?? convX)).
2: Apply mult_wd_lft; Apply eq_symmetric_unfolded; Apply Lim_const.
EApply eq_transitive_unfolded.
2: Apply Lim_mult.
Apply Lim_wd'.
Intro; Simpl.
Unfold seq_part_sum.
Apply Sum0_comm_scal'.
Qed.

End Operations.

Section More_Operations.

Variable x:nat->IR.
Hypothesis convX : (convergent x).

(* Tex_Prose
As a corollary, we get the inverse series.
*)

(* Begin_Tex_Verb *)
Lemma conv_series_inv : (convergent [n:nat][--](x n)).
(* End_Tex_Verb *)
Red.
Red in convX.
EApply Cauchy_prop_wd.
Apply Cauchy_minus with seq1:=(Cauchy_const Zero) seq2:=(Build_CauchySeq ?? convX).
Simpl.
Unfold seq_part_sum.
Intro.
Apply eq_symmetric_unfolded; Apply eq_transitive_unfolded with Zero[+](Sum0 n [n:nat][--](x n)).
Algebra.
Unfold cg_minus; Apply bin_op_wd_unfolded.
Algebra.
Apply inv_Sum0.
Qed.

(* Begin_Tex_Verb *)
Lemma series_sum_inv : (H:(convergent [n:nat][--](x n)))(series_sum ? H)[=][--](series_sum ? convX).
(* End_Tex_Verb *)
Intros.
LetTac y:=(Cauchy_const Zero).
Cut (convergent y); Intros.
EApply eq_transitive_unfolded.
Apply series_sum_wd with y:=[n:nat]((y n)[-](x n)) convY:=(conv_series_minus ?? H0 convX).
Intro; Unfold y; Simpl; Algebra.
Cut (series_sum y H0)[=]Zero; Intros.
Step_rht Zero[-](series_sum x convX).
Step_rht (series_sum y H0)[-](series_sum x convX).
Apply series_sum_minus.
Apply series_sum_zero.
Apply conv_zero_series.
Qed.

End More_Operations.

Section Almost_Everywhere.

(* Tex_Prose
\section{Almost Everywhere}

In this section we strengthen some of the convergence results for sequences and derive an important corollary for series.

\begin{convention} Let \verb!x,y:nat->IR! be equal after some natural number.
\end{convention}
*)

Variables x,y:nat->IR.

(* Begin_Tex_Verb *)
Definition aew_eq := {n:nat | (k:nat)(le n k)->(x k)[=](y k)}.
(* End_Tex_Verb *)

Hypothesis aew_equal : aew_eq.

(* Begin_Tex_Verb *)
Lemma aew_Cauchy : (Cauchy_prop x)->(Cauchy_prop y).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Elim (H ? (pos_div_two ?? H0)).
Intros N HN.
Elim aew_equal; Intros n Hn.
Exists (max n N).
Intros.
Apply AbsSmall_wd_rht_unfolded with (x m)[-](x (max n N)).
RStepr ((x m)[-](x N))[+]((x N)[-](x (max n N))).
RStep e[/]TwoNZ[+]e[/]TwoNZ.
Apply AbsSmall_plus.
Apply HN; Apply le_trans with (max n N); Auto with arith.
Apply AbsSmall_minus; Apply HN; Apply le_trans with (max n N); Auto with arith.
Apply cg_minus_wd; Apply Hn.
Apply le_trans with (max n N); Auto with arith.
Apply le_max_l.
Qed.

(* Begin_Tex_Verb *)
Lemma aew_Cauchy2 : (c:IR)
  (Cauchy_Lim_prop2 x c)->(Cauchy_Lim_prop2 y c).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Elim (H eps H0).
Intros N HN.
Elim aew_equal; Intros n Hn.
Exists (max n N).
Intros.
Apply AbsSmall_wd_rht_unfolded with (x m)[-]c.
Apply HN; Apply le_trans with (max n N); Auto with arith.
Apply cg_minus_wd; [Apply Hn | Algebra].
Apply le_trans with (max n N); Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma aew_series_conv : (convergent x)->(convergent y).
(* End_Tex_Verb *)
Intro.
Red; Red; Intros.
Elim (H ? (pos_div_two ?? H0)); Intros N HN.
Elim aew_equal; Intros n Hn.
LetTac k:=(max (max n N) (1)).
Exists k; Intros.
Apply AbsSmall_wd_rht_unfolded with (seq_part_sum x m)[-](seq_part_sum x k).
RStepr ((seq_part_sum x m)[-](seq_part_sum x N))[+]((seq_part_sum x N)[-](seq_part_sum x k)).
RStep e[/]TwoNZ[+]e[/]TwoNZ.
Apply AbsSmall_plus.
Apply HN; Cut (le N k).
Omega.
Apply le_trans with (max n N); Unfold k; Auto with arith.
Apply AbsSmall_minus; Apply HN; Auto.
Apply le_trans with (max n N); Unfold k; Auto with arith.
Cut (le (1) k); Intros.
EApply eq_transitive_unfolded.
Apply seq_part_sum_n; Auto.
Apply lt_le_trans with k; Auto.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply seq_part_sum_n; Auto.
2: Apply lt_le_trans with k; Auto.
Apply Sum_wd'.
Rewrite <- S_pred with m (0);  Auto with arith.
Apply lt_le_trans with k; Auto.
Intros; Apply Hn.
Apply le_trans with (max n N); Auto with arith.
Apply le_trans with k; Unfold k; Auto with arith.
Unfold k; Apply le_max_r.
Qed.

End Almost_Everywhere.

Section Cauchy_Almost_Everywhere.

(* Tex_Prose
Suppose furthermore that \verb!x,y! are Cauchy sequences.
*)

Variables x,y:(CauchySeq IR).

Hypothesis aew_equal : (aew_eq x y).

(* Begin_Tex_Verb *)
Lemma aew_Lim : (Lim x)[=](Lim y).
(* End_Tex_Verb *)
Intros.
Cut (Cauchy_Lim_prop2 x (Lim y)).
Intro.
Apply eq_symmetric_unfolded.
Apply Limits_unique; Assumption.
Apply aew_Cauchy2 with (y::nat->IR).
Elim aew_equal; Intros n Hn; Exists n; Intros.
Apply eq_symmetric_unfolded; Apply Hn; Auto.
Apply Cauchy_complete.
Qed.

End Cauchy_Almost_Everywhere.

Section Convergence_Criteria.

(* Tex_Prose
\section{Convergence Criteria}

\begin{convention} Let \verb!x:nat->IR!.
\end{convention}
*)

Variable x:nat->IR.

(* Tex_Prose
We include the comparison test for series, both in a strong and in a less general (but simpler) form.
*)

(* Begin_Tex_Verb *)
Lemma str_comparison : (y:nat->IR)(convergent y)->
  {k:nat | ((n:nat)(le k n)->(AbsIR (x n))[<=](y n))}->
  (convergent x).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros k Hk.
Red; Red; Intros.
Cut {N:nat | (lt k N)/\((m:nat)(le N m)->(AbsSmall e (seq_part_sum y m)[-](seq_part_sum y N)))}; Intros.
Elim H2; Clear H2.
Intros N HN; Elim HN; Clear HN; Intros HN' HN.
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
Apply leEq_transitive with (seq_part_sum y m)[-](seq_part_sum y N).
Apply leEq_transitive with (Sum N (pred m) [n:nat](AbsIR (x n))).
Apply leEq_wdl with (AbsIR (Sum N (pred m) x)).
2: Apply AbsIR_wd; Apply eq_symmetric_unfolded; Apply seq_part_sum_n; Auto.
2: Apply lt_le_trans with N; Auto; Apply le_lt_trans with k; Auto with arith.
Apply triangle_SumIR.
Rewrite <- (S_pred m k); Auto with arith.
Apply lt_le_trans with N; Auto.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply seq_part_sum_n; Auto.
2: Apply le_lt_trans with k; Auto with arith; Apply lt_le_trans with N; Auto.
Apply Sum_resp_leEq.
Rewrite <- (S_pred m k); Auto with arith.
Apply lt_le_trans with N; Auto.
Intros.
Apply Hk; Apply le_trans with N; Auto with arith.
EApply leEq_transitive.
Apply leEq_AbsIR.
Apply AbsSmall_imp_AbsIR.
Apply HN; Assumption.
Elim (H ? (pos_div_two ?? H1)).
Intros N HN; Exists (S (max N k)).
Cut (le N (max N k)); [Intro | Apply le_max_l].
Cut (le k (max N k)); [Intro | Apply le_max_r].
Split.
Auto with arith.
Intros.
RStepr ((seq_part_sum y m)[-](seq_part_sum y N))[+]((seq_part_sum y N)[-](seq_part_sum y (S (max N k)))).
RStep e[/]TwoNZ[+]e[/]TwoNZ.
Apply AbsSmall_plus.
Apply HN; Apply le_trans with (max N k); Auto with arith.
Apply AbsSmall_minus; Apply HN; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma comparison : (y:nat->IR)(convergent y)->
  ((n:nat)(AbsIR (x n))[<=](y n))->(convergent x).
(* End_Tex_Verb *)
Intros.
Apply str_comparison with y.
Assumption.
Exists O; Intros; Apply H0.
Qed.

(* Tex_Prose
As a corollary, we get that every absolutely convergent series converges.
*)

(* Begin_Tex_Verb *)
Lemma abs_imp_conv : (abs_convergent x)->(convergent x).
(* End_Tex_Verb *)
Intros.
Apply comparison with [n:nat](AbsIR (x n)).
Apply H.
Intro; Apply leEq_reflexive.
Qed.

(* Tex_Prose
Next we have the ratio test, both as a positive and negative result.
*)

(* Begin_Tex_Verb *)
Lemma divergent_crit : {r:IR & (Zero[<]r) &
  (n:nat){m:nat | (le n m) | (r[<=](AbsIR (x m)))}}->
  (divergent x).
(* End_Tex_Verb *)
Intro.
Elim H; Clear H; Intros r Hr H.
Exists r.
Assumption.
Intro.
Elim (H k); Clear H; Intros m Hm Hrm.
Exists (S m).
Exists m.
Split.
Auto.
Split.
Assumption.
EApply leEq_wdr.
Apply Hrm.
Apply AbsIR_wd.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply seq_part_sum_n; Auto with arith.
Apply Sum_one.
Qed.

Lemma Sum_big_shift : (G:CGroup)(a,b:nat->G)
  (k,m,n:nat)((j:nat)(le m j)->(a j)[=](b (plus j k)))->
  (le m (S n))->(Sum m n a)[=](Sum (plus m k) (plus n k) b).
Do 4 Intro; Generalize a b; Clear a b.
Induction k.
Intros; Repeat Rewrite <- plus_n_O.
Apply Sum_wd'; Intros.
Auto.
Pattern 2 i; Rewrite (plus_n_O i); Apply H; Auto.
Intros; Repeat Rewrite <- plus_n_Sm.
Apply eq_transitive_unfolded with (Sum (plus m k) (plus n k) [n:nat](b (S n))).
2: Apply Sum_shift; Algebra.
Apply Hreck.
Intros; Rewrite plus_n_Sm; Apply H; Auto with arith.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma tail_series : (y:nat->IR)(convergent y)->
  {k:nat & {N:nat | (n:nat)(le N n)->(x n)[=](y (plus n k))}}->(convergent x).
(* End_Tex_Verb *)
Red; Intros.
Elim H0; Intros k Hk.
Elim Hk; Intros N HN.
Clear Hk H0.
Red; Intros.
Elim (H e[/]TwoNZ (pos_div_two ?? H0)); Intros M HM.
Exists (S (max N M)); Intros.
RStep e[/]TwoNZ[+]e[/]TwoNZ.
Apply AbsSmall_wd_rht_unfolded with (seq_part_sum y (plus m k))[-](seq_part_sum y (plus (S (max N M)) k)).
RStepr ((seq_part_sum y (plus m k))[-](seq_part_sum y M))[+]((seq_part_sum y M)[-](seq_part_sum y (plus (S (max N M)) k))).
Apply AbsSmall_plus.
Apply HM.
Apply le_trans with (max N M); Auto with arith.
Apply AbsSmall_minus.
Apply HM.
Auto with arith.
Unfold seq_part_sum.
Step (Sum (plus (S (max N M)) k) (pred (plus m k)) y).
Unfold Sum Sum1.
Rewrite <- S_pred with m:=O.
Algebra.
Apply lt_le_trans with (S (max N M)); Auto with arith.
Stepr (Sum (S (max N M)) (pred m) x).
2: Unfold Sum Sum1.
2: Rewrite <- S_pred with m:=O.
2: Algebra.
2: Apply lt_le_trans with (S (max N M)); Auto with arith.
Replace (pred (plus m k)) with (plus (pred m) k).
Apply eq_symmetric_unfolded; Apply Sum_big_shift.
Intros; Apply HN.
Apply le_trans with (max N M); Auto with arith.
Rewrite <- S_pred with m:=O; Auto.
Apply lt_le_trans with (S (max N M)); Auto with arith.
Omega.
Qed.

(* Begin_Tex_Verb *)
Lemma join_series : (convergent x)->(y:nat->IR)
  {k:nat & {N:nat | (n:nat)(le N n)->(x n)[=](y (plus n k))}}->(convergent y).
(* End_Tex_Verb *)
Red; Intros.
Elim H0; Intros k Hk.
Elim Hk; Intros N HN.
Clear Hk H0.
Red; Intros.
Elim (H e[/]TwoNZ (pos_div_two ?? H0)); Intros M HM.
Exists (S (plus (max N M) k)); Intros.
RStep e[/]TwoNZ[+]e[/]TwoNZ.
Apply AbsSmall_wd_rht_unfolded with (seq_part_sum x (minus m k))[-](seq_part_sum x (minus (S (plus (max N M) k)) k)).
RStepr ((seq_part_sum x (minus m k))[-](seq_part_sum x M))[+]((seq_part_sum x M)[-](seq_part_sum x (minus (S (plus (max N M) k)) k))).
Apply AbsSmall_plus.
Apply HM.
Apply simpl_le_plus_l with k.
Rewrite <- le_plus_minus.
Apply le_trans with (plus (max N M) k); Auto with arith.
Rewrite plus_sym; Auto with arith.
Apply le_trans with (S (plus (max N M) k)); Auto with arith.
Apply AbsSmall_minus.
Apply HM.
Apply simpl_le_plus_l with k.
Rewrite <- le_plus_minus.
Apply le_trans with (plus (max N M) k); Auto.
Rewrite plus_sym; Auto with arith.
Apply le_trans with (S (plus (max N M) k)); Auto with arith.
Unfold seq_part_sum.
Step (Sum (minus (S (plus (max N M) k)) k) (pred (minus m k)) x).
Unfold Sum Sum1.
Rewrite <- S_pred with m:=O.
Algebra.
Omega.
Stepr (Sum (S (plus (max N M) k)) (pred m) y).
2: Unfold Sum Sum1.
2: Rewrite <- S_pred with m:=O.
2: Algebra.
2: Omega.
Replace (pred m) with (plus (pred (minus m k)) k).
2: Omega.
Pattern 2 (S (plus (max N M) k)); Replace (S (plus (max N M) k)) with (plus (minus (S (plus (max N M) k)) k) k).
2: Omega.
Apply Sum_big_shift.
Intros; Apply HN.
Apply le_trans with (max N M); Auto with arith.
Omega.
Rewrite <- S_pred with m:=O; Auto.
Omega.
Apply lt_le_trans with (S (max N M)); Auto with arith.
Omega.
Qed.

End Convergence_Criteria.

Section More_CC.

Variable x:nat->IR.

(* Begin_Tex_Verb *)
Lemma ratio_test_conv : {N:nat & {c:IR & (c[<]One) | (Zero[<=]c) /\
  (n:nat)(le N n)->(AbsIR (x (S n)))[<=]c[*](AbsIR (x n))}}->
  (convergent x).
(* End_Tex_Verb *)
Intro.
Elim H; Clear H; Intros N H.
Elim H; Clear H; Intros c Hc1 H.
Elim H; Clear H; Intros H0c H.
Cut (n:nat)(le N n)->(AbsIR (x n))[<=](AbsIR (x N))[*](c[^](minus n N)).
Intro.
Apply str_comparison with [n:nat](AbsIR (x N))[*](c[^](minus n N)).
2: Exists N; Assumption.
Apply conv_series_mult_scal with x:=[n:nat](c[^](minus n N)).
Apply join_series with (power_series c).
Apply power_series_conv; Assumption.
Exists N.
Exists O.
Intro.
Rewrite plus_sym; Rewrite Minus.minus_plus.
Algebra.
Induction n.
Intro.
Cut N=O; [Intro | Auto with arith].
Rewrite H1.
Apply eq_imp_leEq.
Simpl; Algebra.
Clear n; Intros.
Cut {lt N (S n)}+{N=(S n)}.
2: Apply le_lt_eq_dec; Assumption.
Intro; Inversion_clear H2.
Apply leEq_transitive with c[*](AbsIR (x n)).
Apply H; Auto with arith.
Rewrite <- minus_Sn_m.
Stepr (AbsIR (x N))[*](c[*](c[^](minus n N))).
RStepr c[*]((AbsIR (x N))[*](c[^](minus n N))).
Apply mult_resp_leEq_lft.
Apply H0; Auto with arith.
Assumption.
Auto with arith.
Rewrite H3.
Rewrite <- minus_n_n.
Apply eq_imp_leEq.
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma ratio_test_div : {N:nat & {c:IR | One[<=]c &
  ((n:nat)(le N n)->c[*](AbsIR (x n))[<](AbsIR (x (S n))))}}->
  (divergent x).
(* End_Tex_Verb *)
Intros.
Elim H; Clear H; Intros N H.
Elim H; Clear H; Intros c Hc Hn.
Apply divergent_crit.
Exists (AbsIR (x (S N))).
Apply leEq_less_trans with c[*](AbsIR (x N)).
Step c[*]Zero; Apply mult_resp_leEq_lft.
Apply AbsIR_nonneg.
Apply less_leEq; EApply less_leEq_trans; [Apply pos_one | Assumption].
Apply Hn; Auto with arith.
Cut (n:nat)(le (S N) n)->{m:nat | (le n m)/\((AbsIR (x (S N)))[<=](AbsIR (x m)))}.
Intro.
Clear Hn.
Intro.
Cut (le (S N) (max (S N) n)); [Intro | Apply le_max_l].
Elim (H ? H0); Intros m Hm; Elim Hm; Clear H Hm; Intros Hm H; Exists m.
Apply le_trans with (max (S N) n); Auto with arith.
Assumption.
Intros; Exists n.
Split.
Auto.
Induction n.
Inversion H.
Clear Hrecn; Induction n.
Inversion H.
Rewrite <- H1; Apply eq_imp_leEq; Algebra.
Inversion H1.
Elim (le_lt_eq_dec ?? H); Intro.
Apply leEq_transitive with (AbsIR (x (S n))).
Apply Hrecn; Auto with arith.
Apply less_leEq; Apply leEq_less_trans with c[*](AbsIR (x (S n))).
Step One[*](AbsIR (x (S n))); Apply mult_resp_leEq_rht.
Assumption.
Apply AbsIR_nonneg.
Apply Hn; Auto with arith.
Rewrite b; Apply eq_imp_leEq; Algebra.
Qed.

End More_CC.

Section Alternate_Series.

(* Tex_Prose
\section{Alternate Series}

Alternate series are a special case.  Suppose that \verb!x! is nonnegative and decreasingly convergent to $0$.
*)

Variable x:nat->IR.

Hypothesis pos_x : (n:nat)(Zero[<=](x n)).
Hypothesis Lim_x : (Cauchy_Lim_prop2 x Zero).
Hypothesis mon_x : (n:nat)(x (S n))[<=](x n).

Local y:=[n:nat]([--]One)[^]n[*](x n).

Local alternate_lemma1 : (n,m:nat)([--]One)[^]n[*](Sum n (plus n (plus m m)) y)[<=](x n).
Intros; Induction m.
Cut n=(plus n (plus O O)); [Intro | Auto with arith].
Rewrite <- H.
Apply eq_imp_leEq.
Cut (Sum n n y)[=](y n); [Intro | Apply Sum_one].
Step_lft ([--]One)[^]n[*](y n).
Unfold y; Simpl.
Apply eq_transitive_unfolded with ([--](One::IR))[^](plus n n)[*](x n).
Step_lft (([--]One)[^]n[*]([--]One)[^]n)[*](x n).
Apply mult_wd_lft.
Apply nexp_plus.
Step_rht One[*](x n).
Apply mult_wd_lft.
Apply inv_one_even_nexp.
Auto with arith.
Cut (plus n (plus (S m) (S m)))=(S (S (plus n (plus m m)))); [Intro | Simpl; Repeat Rewrite plus_n_Sm; Auto].
Rewrite H.
Apply leEq_wdl with ([--]One)[^]n[*](Sum n (plus n (plus m m)) y)[+]([--]One)[^]n[*]((y (S (plus n (plus m m))))[+](y (S (S (plus n (plus m m)))))).
Apply leEq_transitive with (x n)[+]([--]One)[^]n[*]((y (S (plus n (plus m m))))[+](y (S (S (plus n (plus m m)))))).
Apply plus_resp_leEq.
Apply Hrecm.
Apply shift_plus_leEq'; Stepr (Zero::IR).
Unfold y.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply ring_dist_unfolded.
Apply leEq_wdl with [--](x (S (plus n (plus m m))))[+](x (S (S (plus n (plus m m))))).
Apply shift_plus_leEq'; RStepr (x (S (plus n (plus m m)))).
Apply mon_x.
Apply bin_op_wd_unfolded.
RStep [--]One[*](x (S (plus n (plus m m)))).
RStepr (([--]One)[^]n[*]([--]One)[^](S (plus n (plus m m))))[*](x (S (plus n (plus m m)))).
Apply mult_wd_lft.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply nexp_plus.
Apply inv_one_odd_nexp.
Cut (plus n (S (plus n (plus m m))))=(S (plus (plus n n) (plus m m))); [Intro | Rewrite <- plus_n_Sm; Auto with arith].
Rewrite H0.
Auto with arith.
Step_lft One[*](x (S (S (plus n (plus m m))))).
RStepr (([--]One)[^]n[*]([--]One)[^](S (S (plus n (plus m m)))))[*](x (S (S (plus n (plus m m))))).
Apply mult_wd_lft.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply nexp_plus.
Apply inv_one_even_nexp.
Cut (plus n (S (S (plus n (plus m m)))))=(S (S (plus (plus n n) (plus m m)))); [Intro | Omega].
Rewrite H0.
Auto with arith.
Unfold Sum; Simpl.
Unfold Sum1; Simpl.
Rational.
Qed.

Local alternate_lemma2 : (n,m:nat)([--]One)[^]n[*](Sum n (plus n (S (plus m m))) y)[<=](x n).
Intros.
Cut (plus n (S (plus m m)))=(S (plus n (plus m m))); [Intro | Auto with arith].
Rewrite H.
Apply leEq_wdl with ([--]One)[^]n[*](Sum n (plus n (plus m m)) y)[+]([--]One)[^]n[*](y (S (plus n (plus m m)))).
Apply leEq_transitive with (x n)[+]([--]One)[^]n[*](y (S (plus n (plus m m)))).
Apply plus_resp_leEq.
Apply alternate_lemma1.
Apply shift_plus_leEq'; RStepr (Zero::IR)[*](x (S (plus n (plus m m)))).
Unfold y.
RStep (([--]One)[^]n[*]([--]One)[^](S (plus n (plus m m))))[*](x (S (plus n (plus m m)))).
Apply mult_resp_leEq_rht.
Apply leEq_wdl with [--](One::IR).
Stepr [--](Zero::IR); Apply less_leEq; Apply inv_resp_less; Apply pos_one.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
Apply nexp_plus.
Apply inv_one_odd_nexp.
Cut (plus n (S (plus n (plus m m))))=(S (plus (plus n n) (plus m m))); [Intro | Rewrite <- plus_n_Sm; Auto with arith].
Rewrite H0.
Auto with arith.
Apply pos_x.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply ring_dist_unfolded.
Apply mult_wd_rht.
Unfold Sum; Unfold Sum1; Simpl; Rational.
Qed.

Local alternate_lemma3 : (n,m:nat)(Zero[<=]([--]One)[^]n[*](Sum n (plus n (S (plus m m))) y)).
Intros; Induction m.
Cut (S n)=(plus n (S (plus O O))); [Intro | Rewrite <- plus_n_Sm; Auto].
Rewrite <- H.
Cut (Sum n (S n) y)[=](y n)[+](y (S n)).
Intro; Stepr ([--]One)[^]n[*]((y n)[+](y (S n))).
Unfold y.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply ring_dist_unfolded.
Apply leEq_wdr with (x n)[-](x (S n)).
Apply shift_leEq_minus; Step (x (S n)).
Apply mon_x.
Unfold cg_minus; Apply bin_op_wd_unfolded.
Step One[*](x n).
Step_rht (([--]One)[^]n[*]([--]One)[^]n)[*](x n).
Apply mult_wd_lft.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply nexp_plus.
Apply inv_one_even_nexp.
Auto with arith.
RStep [--]One[*](x (S n)).
Step_rht (([--]One)[^]n[*]([--]One)[^](S n))[*](x (S n)).
Apply mult_wd_lft.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply nexp_plus.
Apply inv_one_odd_nexp.
Cut (plus n (S n))=(S (plus n n)); [Intro | Auto with arith].
Rewrite H1.
Auto with arith.
Unfold Sum Sum1; Simpl; Rational.
Cut (plus n (S (plus (S m) (S m))))=(S (S (plus n (S (plus m m))))); [Intro | Simpl; Repeat Rewrite <- plus_n_Sm; Auto with arith].
Rewrite H.
Apply leEq_wdr with ([--]One)[^]n[*]((Sum n (plus n (S (plus m m))) y)[+]((y (S (plus n (S (plus m m)))))[+](y (S (S (plus n (S (plus m m)))))))).
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply ring_dist_unfolded.
Step (Zero::IR)[+]Zero.
Apply plus_resp_leEq_both.
Apply Hrecm.
Unfold y.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply ring_dist_unfolded.
Apply leEq_wdr with (x (S (plus n (S (plus m m)))))[-](x (S (S (plus n (S (plus m m)))))).
Apply shift_leEq_minus; Step (x (S (S (plus n (S (plus m m)))))); Apply mon_x.
Unfold cg_minus; Apply bin_op_wd_unfolded.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply mult_assoc_unfolded.
Step_lft One[*](x (S (plus n (S (plus m m))))); Apply mult_wd_lft.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded; [Apply nexp_plus | Apply inv_one_even_nexp].
Cut (plus n (S (plus n (S (plus m m)))))=(S (S (plus (plus n n) (plus m m)))); [Intro | Simpl; Repeat Rewrite <- plus_n_Sm; Auto with arith].
Rewrite H0.
Auto with arith.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply mult_assoc_unfolded.
RStep [--]One[*](x (S (S (plus n (S (plus m m)))))); Apply mult_wd_lft.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded; [Apply nexp_plus | Apply inv_one_odd_nexp].
Cut (plus n (S (S (plus n (S (plus m m))))))=(S (plus (plus (S n) (S n)) (plus m m))); [Intro | Simpl; Repeat Rewrite <- plus_n_Sm; Simpl; Auto with arith].
Rewrite H0.
Auto with arith.
Apply mult_wd_rht.
Unfold Sum Sum1; Simpl; Rational.
Qed.

Local alternate_lemma4 : (n,m:nat)(Zero[<=]([--]One)[^]n[*](Sum n (plus n (plus m m)) y)).
Intros.
Case m.
Cut (plus n (plus O O))=n; [Intro | Auto].
Rewrite H.
Cut (Sum n n y)[=](y n); [Intro | Apply Sum_one].
Stepr ([--]One)[^]n[*](y n).
Unfold y.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply mult_assoc_unfolded.
Step Zero[*](x n).
Apply mult_resp_leEq_rht.
Apply leEq_wdr with (One::IR).
Apply less_leEq; Apply pos_one.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
Apply nexp_plus.
Apply inv_one_even_nexp; Auto with arith.
Apply pos_x.
Clear m; Intro m.
Cut (plus n (plus (S m) (S m)))=(S (plus n (S (plus m m)))); [Intro | Simpl; Rewrite <- plus_n_Sm; Auto].
Rewrite H.
Apply leEq_wdr with ([--]One)[^]n[*](Sum n (plus n (S (plus m m))) y)[+]([--]One)[^]n[*](y (S (plus n (S (plus m m))))).
Apply leEq_transitive with Zero[+]([--]One)[^]n[*](y (S (plus n (S (plus m m))))).
Stepr ([--]One)[^]n[*](y (S (plus n (S (plus m m))))).
Unfold y.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply mult_assoc_unfolded.
Step Zero[*](x (S (plus n (S (plus m m))))).
Apply mult_resp_leEq_rht.
Apply leEq_wdr with (One::IR).
Apply less_leEq; Apply pos_one.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
Apply nexp_plus.
Cut (plus n (S (plus n (S (plus m m)))))=(plus (plus n n) (plus (S m) (S m))); [Intro | Simpl; Repeat Rewrite <- plus_n_Sm; Simpl; Auto with arith].
Rewrite H0; Apply inv_one_even_nexp.
Auto with arith.
Apply pos_x.
Apply plus_resp_leEq.
Apply alternate_lemma3.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply ring_dist_unfolded.
Apply mult_wd_rht.
Unfold Sum; Unfold Sum1; Simpl; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma alternate_series_conv : (convergent [n:nat]([--]One)[^]n[*](x n)).
(* End_Tex_Verb *)
Red.
Red.
Intros.
Elim (Lim_x e H).
Intros N' HN'.
Cut {N:nat | (lt O N) | (m:nat)((le N m)->(AbsSmall e (x m)))}.
Intro.
Elim H0; Clear H0; Intros N HNm HN.
Exists N; Intros.
Apply AbsSmall_transitive with (x N).
Apply HN; Auto.
Cut (AbsIR (seq_part_sum [n:nat](([--]One)[^]n)[*](x n) m)
  [-](seq_part_sum [n:nat](([--]One)[^]n)[*](x n) N))[=](AbsIR ([--]One)[^]N[*](Sum N (pred m) y)).
Intro.
Apply leEq_wdl with (AbsIR ([--]One)[^]N[*](Sum N (pred m) y)).
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x; Apply pos_x.
Cut {lt N m}+{N=m}; Intros.
2: Apply le_lt_eq_dec; Assumption.
Apply leEq_wdl with (Max ([--]One)[^]N[*](Sum N (pred m) y) [--](([--]One)[^]N[*](Sum N (pred m) y))).
Apply Max_leEq.
Inversion_clear H2.
Cut {j:nat & {(pred m)=(plus N (plus j j))}+{(pred m)=(plus N (S (plus j j)))}}.
2: Apply even_or_odd_plus_gt; Apply le_2; Auto.
Intro.
Elim H2; Intros j Hj.
Clear H2; Inversion_clear Hj.
Rewrite H2; Apply alternate_lemma1.
Rewrite H2; Apply alternate_lemma2.
Rewrite <- H3.
Cut (Sum N (pred N) y)[=]Zero; [Intro | Apply Sum_empty; Auto].
Step ([--]One)[^]N[*](Zero::IR).
Step (Zero::IR); Apply pos_x.
Stepr [--][--](x N); Apply inv_resp_leEq.
Apply leEq_transitive with (Zero::IR).
Stepr [--](Zero::IR); Apply inv_resp_leEq; Apply pos_x.
Inversion_clear H2.
Cut {j:nat & {(pred m)=(plus N (plus j j))}+{(pred m)=(plus N (S (plus j j)))}}.
2: Apply even_or_odd_plus_gt; Apply le_2; Auto.
Intro.
Elim H2; Intros j Hj.
Clear H2; Inversion_clear Hj.
Rewrite H2; Apply alternate_lemma4.
Rewrite H2; Apply alternate_lemma3.
Rewrite <- H3.
Cut (Sum N (pred N) y)[=]Zero; [Intro | Apply Sum_empty; Auto].
Stepr ([--]One)[^]N[*](Zero::IR).
Stepr (Zero::IR); Apply leEq_reflexive.
Simpl; Unfold ABSIR; Apply eq_reflexive_unfolded.
Apply eq_symmetric_unfolded; Assumption.
Elim (even_odd_dec N); Intro.
Apply AbsIR_wd.
EApply eq_transitive_unfolded.
Apply seq_part_sum_n; Auto; Apply lt_le_trans with N; Auto.
EApply eq_transitive_unfolded.
2: Apply Sum_comm_scal'.
Apply Sum_wd.
Intro.
Unfold y.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply mult_assoc_unfolded.
Apply mult_wd_lft.
Step (One::IR)[*]([--]One)[^]i.
Apply mult_wd_lft.
Apply eq_symmetric_unfolded; Apply inv_one_even_nexp; Assumption.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply AbsIR_inv.
Apply AbsIR_wd.
EApply eq_transitive_unfolded.
Apply seq_part_sum_n; Auto; Apply lt_le_trans with N; Auto.
RStepr ([--](([--]One)[^]N))[*](Sum N (pred m) y).
EApply eq_transitive_unfolded.
2: Apply Sum_comm_scal'.
Apply Sum_wd.
Intro.
Unfold y.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply mult_assoc_unfolded.
Apply mult_wd_lft.
Step (One::IR)[*]([--]One)[^]i.
Apply mult_wd_lft.
Apply eq_symmetric_unfolded.
RStep ([--](One::IR))[^](1)[*]([--]One)[^]N.
EApply eq_transitive_unfolded.
Apply nexp_plus.
Apply inv_one_even_nexp.
Simpl.
Auto with arith.
Exists (S N').
Auto with arith.
Intros.
Stepr (x m)[-]Zero; Apply HN'; Auto with arith.
Qed.

End Alternate_Series.

Section Important_Numbers.

(* Tex_Prose
\section{Important Numbers}

We end this chapter by defining two important numbers in mathematics: $\pi$ and $e$, both as Sums of convergent series.
*)

(* Begin_Tex_Verb *)
Definition e_series := [n:nat]
  (One[/]?[//](nring_fac_ap_zero IR n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma e_series_conv : (convergent e_series).
(* End_Tex_Verb *)
Apply ratio_test_conv.
Exists (1).
Exists (One::IR)[/]TwoNZ.
Apply pos_div_two'; Apply pos_one.
Split.
Apply less_leEq; Apply pos_div_two; Apply pos_one.
Intros.
Unfold e_series.
EApply leEq_wdr.
2: Apply mult_commutes.
EApply leEq_wdr.
2: Apply AbsIR_product_positive.
2: Apply less_leEq; Apply pos_div_two; Apply pos_one.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
RStepr (One[*]One)[/]?[//](mult_resp_ap_zero ??? (two_ap_zero IR) (nring_fac_ap_zero ? n)).
RStepr One[/]?[//](mult_resp_ap_zero ??? (two_ap_zero IR) (nring_fac_ap_zero ? n)).
Apply recip_resp_leEq.
Step (Two::IR)[*]Zero; Apply mult_resp_less_lft.
Apply pos_nring_fac.
Apply pos_two.
Cut (fac (S n))=(mult (S n) (fac n)).
2: Simpl; Auto with arith.
Intro.
Rewrite H0.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply nring_comm_mult.
Apply mult_resp_leEq_rht.
Apply nring_leEq; Auto with arith.
Apply less_leEq; Apply pos_nring_fac.
Apply less_leEq; Apply mult_resp_pos; Apply recip_resp_pos.
Apply pos_nring_fac.
Apply pos_two.
Apply less_leEq; Apply recip_resp_pos; Apply pos_nring_fac.
Qed.

(* Begin_Tex_Verb *)
Definition E := (series_sum ? e_series_conv).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition pi_series :=
  [n:nat]([--]One)[^]n[*](One[/]?[//]
    (Greater_imp_ap IR ?? (pos_nring_S ? (plus n n)))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma pi_series_conv : (convergent pi_series).
(* End_Tex_Verb *)
Unfold pi_series.
Apply alternate_series_conv with x:=[n:nat](One[/]?[//](Greater_imp_ap IR ?? (pos_nring_S ? (plus n n)))).
Intro; Apply less_leEq.
Apply recip_resp_pos; Apply pos_nring_S.
Apply Cauchy_Lim_prop3_prop2.
Red; Intros.
Exists (S k); Intros.
Apply AbsIR_imp_AbsSmall.
Apply less_leEq.
Apply less_wdl with One[/]?[//](Greater_imp_ap IR ?? (pos_nring_S ? (plus m m))).
Unfold one_div_succ Snring.
Apply recip_resp_less.
Apply pos_nring_S.
Apply nring_less; Auto with arith.
Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with (AbsIR One[/]?[//](Greater_imp_ap IR ?? (pos_nring_S ? (plus m m)))).
Apply AbsIR_wd; Algebra.
Apply AbsIR_eq_x; Apply less_leEq.
Apply recip_resp_pos; Apply pos_nring_S.
Intros.
Apply less_leEq; Apply recip_resp_less.
Apply pos_nring_S.
Apply nring_less; Simpl; Rewrite <- plus_n_Sm; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Definition pi:=Four[*](series_sum ? pi_series_conv).
(* End_Tex_Verb *)

End Important_Numbers.
