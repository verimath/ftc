(* $Id: CReals1.v,v 1.21 2003/03/13 12:06:24 lcf Exp $ *)

Require Export Max_AbsIR.
Require Export Expon.

Section More_Cauchy_Props.

(* Tex_Prose
\section{More properties of Cauchy sequences}

We will now define some special Cauchy sequences and prove some more useful properties about them.

The sequence defined by $x_n=\frac2(n+1)$. (don't ask why!)
*)

(* Begin_Tex_Verb *)
Lemma twice_inv_seq_Lim :
  (!SeqLimit IR [n:nat]Two[*](one_div_succ n) Zero).
(* End_Tex_Verb *)
Red; Fold (Cauchy_Lim_prop2 [n:nat]Two[*](one_div_succ n) Zero).
Apply Cauchy_Lim_prop3_prop2.
Red; Intro.
Exists (mult (2) (S k)); Intros.
Stepr ((Two::IR)[*](one_div_succ m)).
Apply AbsIR_imp_AbsSmall.
Apply leEq_wdl with (Two::IR)[*](one_div_succ m).
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Step (!one_div_succ IR m)[*]Two.
Unfold one_div_succ; Simpl; Fold (Two::IR).
Apply shift_mult_leEq with (two_ap_zero IR).
Apply pos_two.
Unfold Snring.
RStepr (One[/]((nring (S k))[*]Two)[//](mult_resp_ap_zero ??? (nring_ap_zero ? (S k) (sym_not_eq nat (0) (S k) (O_S k))) (two_ap_zero IR))).
Apply recip_resp_leEq.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive.
Apply pos_nring_S.
Apply pos_two.
Step (Two::IR)[*](nring (S k)).
Apply leEq_transitive with (!nring IR m).
Apply leEq_wdl with (!nring IR (mult (2) (S k))).
Apply nring_leEq.
Assumption.
Apply nring_comm_mult.
Simpl; Step (!nring IR m)[+]Zero; Apply plus_resp_leEq_lft; Apply less_leEq; Apply pos_one.
Step (Zero::IR)[*]Zero; Apply mult_resp_leEq_both; Try Apply leEq_reflexive.
Apply less_leEq; Apply pos_two.
Apply less_leEq; Apply one_div_succ_pos.
Qed.

(* Begin_Tex_Verb *)
Definition twice_inv_seq : (CauchySeq IR).
(* End_Tex_Verb *)
Apply Build_CauchySeq with [n:nat]Two[*](!one_div_succ IR n).
Apply Cauchy_prop2_prop.
Red; Exists (Zero::IR).
Red; Fold (SeqLimit [n:nat]Two[*](!one_div_succ IR n) Zero).
Apply twice_inv_seq_Lim.
Defined.

(* Tex_Prose
Next, we prove that the sequence of absolute values of a Cauchy sequence is also Cauchy.
*)

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_abs : (seq:nat->IR)(y:IR)(Cauchy_Lim_prop2 seq y)->
  (Cauchy_Lim_prop2 [n:nat](AbsIR (seq n)) (AbsIR y)).
(* End_Tex_Verb *)
Intros.
Red; Red in H.
Intros eps He.
Elim (H eps He); Clear H.
Intros N HN.
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
Cut (AbsIR (seq m)[-]y)[<=]eps.
Intro.
2: Apply AbsSmall_imp_AbsIR; Apply HN; Assumption.
Cut (seq m)[-]y[<=]eps.
2: EApply leEq_transitive; [Apply leEq_AbsIR | Apply H0].
Intro.
Cut y[-](seq m)[<=]eps.
2: EApply leEq_transitive; [Apply leEq_AbsIR | EApply leEq_wdl; [Apply H0 | Apply AbsIR_minus]].
Intro.
Simpl; Unfold ABSIR.
Apply Max_leEq.
Apply shift_minus_leEq.
Apply Max_leEq.
Apply shift_leEq_plus'.
Apply leEq_transitive with y.
Apply shift_minus_leEq; Apply shift_leEq_plus'; Assumption.
Apply lft_leEq_Max.
Apply shift_leEq_plus'.
Apply leEq_transitive with [--]y.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
RStep y[-](seq m).
Assumption.
Apply rht_leEq_Max.
Stepr [--][--]eps; Apply inv_resp_leEq.
Apply shift_leEq_minus; Apply shift_plus_leEq'.
Apply leEq_wdr with (Max (seq m) [--](seq m))[+]eps.
Apply Max_leEq.
Apply leEq_transitive with (seq m)[+]eps.
Apply shift_leEq_plus'; Assumption.
Apply plus_resp_leEq.
Apply lft_leEq_Max.
Apply leEq_transitive with [--](seq m)[+]eps.
Apply shift_leEq_plus'; RStep (seq m)[-]y; Assumption.
Apply plus_resp_leEq.
Apply rht_leEq_Max.
Unfold cg_minus.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_abs : (seq:(CauchySeq IR))
  (Cauchy_prop [n:nat](AbsIR (seq n))).
(* End_Tex_Verb *)
Intro.
Apply Cauchy_prop2_prop.
Exists (AbsIR (Lim seq)).
Apply Cauchy_Lim_abs.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_abs : (seq:(CauchySeq IR))
  (Lim (Build_CauchySeq IR ? (Cauchy_abs seq)))[=](AbsIR (Lim seq)).
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded; Apply Limits_unique.
Simpl; Apply Cauchy_Lim_abs.
Apply Cauchy_complete.
Qed.

End More_Cauchy_Props.

Section Subsequences.

(* Tex_Prose
\section{Subsequences}

We will now examine (although without formalizing it) the concept of subsequence and some of its properties.

\begin{convention} Let \verb!seq1,seq2:nat->IR!.
\end{convention}

In order for \verb!seq1! to be a subsequence of \verb!seq2!, there must be an increasing function \verb!f! growing to infinity such that \verb!(n:nat)(seq1 n)[=](seq2 (f n))!.  We assume \verb!f! to be such a function.

Finally, for some of our results it is important to assume that \verb!seq2! is monotonous.  We will mark the lemmas where this hypothesis is actually used by comment marks.
*)

Variables seq1,seq2:nat->IR.
Variable f:nat->nat.

Hypothesis monF : (m,n:nat)(le m n)->(le (f m) (f n)).
Hypothesis crescF : (n:nat){m:nat | (lt n m)/\(lt (f n) (f m))}.
Hypothesis subseq : (n:nat)(seq1 n)[=](seq2 (f n)).

Hypothesis mon_seq2 : ((m,n:nat)(le m n)->(seq2 m)[<=](seq2 n))\/((m,n:nat)(le m n)->(seq2 n)[<=](seq2 m)).

(* Begin_Tex_Verb *)
Lemma unbnd_f : (m:nat){n:nat | (lt m (f n))}.
(* End_Tex_Verb *)
Induction m.
Elim (crescF O).
Intros n Hn.
Exists n.
Inversion_clear Hn.
Apply le_lt_trans with (f O); Auto with arith.
Intros.
Elim H; Clear H; Intros n' Hn'.
Elim (crescF n').
Intros i Hi; Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i.
Apply le_lt_trans with (f n'); Auto.
Qed.

Local mon_F' : (m,n:nat)(lt (f m) (f n))->(lt m n).
Intros.
Cut ~(le n m).
Intro; Apply not_ge; Auto.
Intro.
Cut (le (f n) (f m)).
Apply lt_not_le; Auto.
Apply monF; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_subseq_imp_conv_seq :
  (Cauchy_prop seq1)->(Cauchy_prop seq2). (* *)
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros.
Elim (H e H0).
Intros N HN.
Exists (f N).
Intros.
Elim (unbnd_f m); Intros i Hi.
Apply AbsIR_imp_AbsSmall.
Apply leEq_transitive with (AbsIR (seq2 (f i))[-](seq2 (f N))).
Elim mon_seq2; Intro.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (seq2 (f N)); Apply H2; Assumption.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (seq2 (f N)); Apply H2; Apply le_trans with m; Auto with arith.
Apply minus_resp_leEq.
Apply H2; Auto with arith.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_inv_x.
2: Apply shift_minus_leEq; Stepr (seq2 (f N)); Auto.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_inv_x.
2: Apply shift_minus_leEq; Stepr (seq2 (f N)); Apply H2; Apply le_trans with m; Auto with arith.
Apply inv_resp_leEq; Apply minus_resp_leEq.
Apply H2; Auto with arith.
Apply leEq_wdl with (AbsIR (seq1 i)[-](seq1 N)).
Apply AbsSmall_imp_AbsIR; Apply HN.
Apply lt_le_weak.
Apply mon_F'; Apply le_lt_trans with m; Auto.
Apply AbsIR_wd; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Cprop2_seq_imp_Cprop2_subseq : (a:IR)
  (Cauchy_Lim_prop2 seq2 a)->(Cauchy_Lim_prop2 seq1 a).
(* End_Tex_Verb *)
Intros.
Red; Red in H.
Intros.
Elim (H ? H0).
Intros N HN.
Elim (unbnd_f N); Intros i Hi.
Exists i.
Intros.
Stepr (seq2 (f m))[-]a.
Apply HN.
Cut (le (f i) (f m)).
Intros; Apply le_trans with (f i); Auto with arith.
Apply monF; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_seq_imp_conv_subseq :
  (Cauchy_prop seq2)->(Cauchy_prop seq1).
(* End_Tex_Verb *)
Intro.
Apply Cauchy_prop2_prop.
Cut (Cauchy_prop2 (Build_CauchySeq ?? H)).
Intro.
Elim H0; Intros a Ha; Exists a.
Apply Cprop2_seq_imp_Cprop2_subseq.
Assumption.
Exists (Lim (Build_CauchySeq ?? H)).
Apply Lim_Cauchy.
Qed.

(* Begin_Tex_Verb *)
Lemma Cprop2_subseq_imp_Cprop2_seq : (a:IR)
  (Cauchy_Lim_prop2 seq1 a)->(Cauchy_Lim_prop2 seq2 a). (* *)
(* End_Tex_Verb *)
Intros.
Cut (Cauchy_prop seq1); Intros.
2: Apply Cauchy_prop2_prop.
2: Exists a; Assumption.
Cut (Cauchy_prop seq2); Intros.
2: Apply conv_subseq_imp_conv_seq; Assumption.
Cut (Cauchy_Lim_prop2 (Build_CauchySeq ?? H1) (Lim (Build_CauchySeq ?? H1))); Intros.
2: Apply Cauchy_complete.
Cut (Cauchy_Lim_prop2 seq1 (Lim (Build_CauchySeq ?? H1))); Intros.
2: Apply Cprop2_seq_imp_Cprop2_subseq; Assumption.
Cut (Lim (Build_CauchySeq ?? H1))[=]a.
Intro.
EApply Lim_wd.
Apply H4.
Assumption.
Apply Lim_unique with seq1; Assumption.
Qed.

End Subsequences.

Section Cauchy_Subsequences.

Variables seq1,seq2:(CauchySeq IR).
Variable f:nat->nat.

Hypothesis monF : (m,n:nat)(le m n)->(le (f m) (f n)).
Hypothesis crescF : (n:nat){m:nat | (lt n m)/\(lt (f n) (f m))}.
Hypothesis subseq : (n:nat)(seq1 n)[=](seq2 (f n)).

Hypothesis mon_seq2 : ((m,n:nat)(le m n)->(seq2 m)[<=](seq2 n))\/((m,n:nat)(le m n)->(seq2 n)[<=](seq2 m)).

(* Begin_Tex_Verb *)
Lemma Lim_seq_eq_Lim_subseq : (Lim seq1)[=](Lim seq2).
(* End_Tex_Verb *)
Cut (Cauchy_Lim_prop2 seq1 (Lim seq2)).
2: Apply Cprop2_seq_imp_Cprop2_subseq with (CS_seq ? seq2) f; Auto; Apply Cauchy_complete.
Intro.
Apply eq_symmetric_unfolded.
Apply Limits_unique; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_subseq_eq_Lim_seq : (Lim seq1)[=](Lim seq2). (* *)
(* End_Tex_Verb *)
Cut (Cauchy_Lim_prop2 seq2 (Lim seq1)).
2: Exact (Cprop2_subseq_imp_Cprop2_seq seq1 seq2 f monF crescF subseq mon_seq2 ? (Cauchy_complete seq1)).
Intro.
Apply Limits_unique; Assumption.
Qed.

End Cauchy_Subsequences.

Section Properties_of_Exponentiation.

(* Tex_Prose
\section{More properties of Exponentiation}

Finally, we prove that $x^n$ grows to infinity if $x>1$.
*)

(* Begin_Tex_Verb *)
Lemma power_big' : (R:COrdField)(x:R; n:nat)(Zero [<=] x) ->
  One[+](nring n)[*]x [<=] (One[+]x)[^]n.
(* End_Tex_Verb *)
Intros.
Induction n; Intros.
RStep (One::R).
Stepr (One::R).
Apply leEq_reflexive.
Simpl.
Apply leEq_transitive with (One[+](nring n)[*]x)[*](One[+]x).
RStepr One[+]((nring n)[+]One)[*]x[+](nring n)[*]x[^](2).
Step One[+]((nring n)[+]One)[*]x[+]Zero.
Apply plus_resp_leEq_lft.
Apply mult_resp_nonneg.
Step ((nring (0))::R). Apply nring_leEq. Auto with arith.
Apply sqr_nonneg.
Apply mult_resp_leEq_rht.
Auto.
Apply less_leEq. Step (Zero::R)[+]Zero.
Apply plus_resp_less_leEq. Apply pos_one. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma power_big : (x,y:IR)(Zero [<=] x) -> (One [<] y) ->
  {N:nat | x [<=] y[^]N}.
(* End_Tex_Verb *)
Intros.
Cut Zero [<] y[-]One. Intro.
Cut y[-]One [#] Zero. Intro.
Elim (Archimedes (x[-]One)[/](y[-]One)[//]H2). Intro N. Intros. Exists N.
Apply leEq_transitive with One[+](nring N)[*](y[-]One).
Apply shift_leEq_plus'.
Stepr (y[-]One)[*](nring N).
Apply shift_leEq_mult' with H2. Auto.
Auto.
Apply leEq_wdr with (One[+](y[-]One))[^]N.
Apply power_big'. Apply less_leEq. Auto.
Apply un_op_wd_unfolded. Rational.
Apply Greater_imp_ap. Auto.
Apply shift_less_minus. Step (One::IR). Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma qi_yields_zero : (q:IR)(Zero[<=]q) -> (q[<]One) -> 
  (e:IR)(Zero[<]e) -> {N:nat | q[^]N [<=] e}.
(* End_Tex_Verb *)
Intros.
Cut Zero [<] (One[+]q)[/]TwoNZ. Intro Haux.
Cut (One[+]q)[/]TwoNZ [#] Zero. Intro H2.
Cut e [#] Zero. Intro H3.
Elim (power_big One[/]e[//]H3 One[/]?[//]H2). Intro N. Intros H4. Exists N.
Cut Zero [<] ((One[+]q)[/]TwoNZ)[^]N. Intro.
Apply leEq_transitive with ((One[+]q)[/]TwoNZ)[^]N.
Apply nexp_resp_leEq.
Auto.
Apply shift_leEq_div.
Apply pos_two.
Apply shift_leEq_plus.
RStep q. Apply less_leEq. Auto.
Step One[*]((One[+]q)[/]TwoNZ)[^]N.
LetTac H6:=(pos_ap_zero ?? H5).
Apply shift_mult_leEq with H6. Auto.
RStepr e[*](One[/]?[//]H6).
Apply shift_leEq_mult' with H3. Auto.
Stepr (One[^]N)[/]?[//]H6.
Stepr (One[/]?[//]H2)[^]N. Auto.
Apply nexp_resp_pos. Apply pos_div_two.
Step Zero[+](Zero::IR). Apply plus_resp_less_leEq.
Apply pos_one. Auto.
Apply less_leEq. Apply recip_resp_pos. Auto. 
Apply shift_less_div. Apply pos_div_two.
Step Zero[+](Zero::IR). Apply plus_resp_less_leEq.
Apply pos_one. Auto.
Step (One[+]q)[/]TwoNZ. Apply shift_div_less.
Apply pos_two. RStepr One[+](One::IR).
Apply plus_resp_less_lft. Auto.
Apply Greater_imp_ap. Auto.
Apply Greater_imp_ap. Auto.
Apply pos_div_two.
Step Zero[+](Zero::IR). Apply plus_resp_less_leEq.
Apply pos_one. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma qi_lim_zero : (q:IR)(Zero [<=] q) -> (q [<] One)
	-> (SeqLimit [i:nat](q[^]i) Zero).
(* End_Tex_Verb *)
Intros.
Unfold SeqLimit. Unfold AbsSmall. Intros.
Elim (qi_yields_zero q H H0 e); Auto.
Intro N. Intros. Exists (S N). Intros. Split.
Apply less_leEq.
Apply less_leEq_trans with (Zero::IR).
Stepr [--](Zero::IR). Apply inv_resp_less. Auto.
Stepr q[^]m.
Apply nexp_resp_nonneg. Auto.
Step q[^]m.
Replace m with (plus N (minus m N)).
Step q[^]N[*]q[^](minus m N). Stepr e[*]One.
Apply mult_resp_leEq_both.
Apply nexp_resp_nonneg. Auto. 
Apply nexp_resp_nonneg. Auto.
Auto.
Stepr (One::IR)[^](minus m N).
Apply nexp_resp_leEq. Auto. Apply less_leEq. Auto.
Auto with arith.
Qed.

End Properties_of_Exponentiation.
