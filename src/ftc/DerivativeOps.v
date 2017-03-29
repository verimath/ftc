(* $Id: DerivativeOps.v,v 1.13 2003/03/13 12:06:18 lcf Exp $ *)

Require Export Derivative.

Section Lemmas.

(* Tex_Prose
\chapter{Derivative and Algebraic Operations}

We will now prove the main results about deriving functions built from the algebraic operators\footnote{Composition presents some tricky questions, and is therefore discussed in a separated context.}.

\begin{convention} Let \verb!a,b:IR! with $a<b$ and denote by \verb!I! the interval $[a,b]$.  Throughout this section, \verb!F,F',G,G'! and \verb!H! will be partial functions with domains respectively \verb!P,P',Q,Q'! and \verb!R!.  As suggested by the notation, \verb!F'! and \verb!G'! will be the derivatives, respectively, of \verb!F! and \verb!G!.
\end{convention}

We begin with some technical stuff that will be necessary for division.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable F:PartIR.
Local P:=(Pred F).

(* Begin_Tex_Verb *)
Hypothesis Fbnd:(bnd_away_zero I F).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma bnd_away_zero_square : (bnd_away_zero I F{*}F).
(* End_Tex_Verb *)
Inversion_clear Fbnd.
Inversion_clear H0.
Split.
Included.
Exists x[*]x.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive; Assumption.
Intros.
Unfold I in H; Apply leEq_wdr with (AbsIR ((FRestr H) y Hy))[*](AbsIR ((FRestr H) y Hy)).
Apply mult_resp_leEq_both; Try (Apply less_leEq; Assumption); Simpl; Apply H2; Try Assumption.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply AbsIR_wd; Simpl; Rational.
Qed.

End Lemmas.

Hints Resolve bnd_away_zero_square : included.

Section Local_Results.

(* Tex_Prose
\section{Local Results}

We can now derive all the usual rules for deriving constant and identity functions, sums, inverses and products of functions with a known derivative.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Lemma Derivative_I_const :
  (c:IR)(Derivative_I Hab' {-C-}c {-C-}Zero).
(* End_Tex_Verb *)
Intros.
Apply Derivative_I_char.
Included.
Included.
Intros e He.
Exists (One::IR).
Apply pos_one.
Intros.
Simpl.
Apply leEq_wdl with (Zero::IR).
Step (Zero::IR)[*]Zero; Apply mult_resp_leEq_both; Try Apply leEq_reflexive.
Apply less_leEq; Assumption.
Apply AbsIR_nonneg.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_id : (Derivative_I Hab' FId {-C-}One).
(* End_Tex_Verb *)
Intros.
Apply Derivative_I_char.
Included.
Included.
Intros e He.
Exists e.
Assumption.
Intros.
Apply leEq_wdl with (Zero::IR).
Step (Zero::IR)[*]Zero; Apply mult_resp_leEq_both; Try Apply leEq_reflexive.
Apply less_leEq; Assumption.
Apply AbsIR_nonneg.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Apply AbsIR_wd; Simpl; Rational.
Qed.

Variables F,F',G,G':PartIR.

Hypothesis derF : (Derivative_I Hab' F F').
Hypothesis derG : (Derivative_I Hab' G G').

(* Begin_Tex_Verb *)
Lemma Derivative_I_plus : (Derivative_I Hab' F{+}G F'{+}G').
(* End_Tex_Verb *)
Elim derF; Intros incF H1.
Elim H1; Intros incF' H2.
Elim derG; Intros incG H5.
Elim H5; Intros incG' H6.
Clear H5 H1.
Apply Derivative_I_char.
Included.
Included.
Intros e He.
Elim (H2 ? (pos_div_two ?? He)).
Intros df H H0.
Elim (H6 ? (pos_div_two ?? He)).
Intros dg H1 H3.
Clear H2 H6.
Exists (Min df dg).
Apply less_Min; Assumption.
Intros.
RStepr (e[/]TwoNZ)[*](AbsIR y[-]x)[+](e[/]TwoNZ)[*](AbsIR y[-]x); Simpl.
LetTac fx:=(F x (ProjIR1 Hx)).
LetTac fy:=(F y (ProjIR1 Hy)).
LetTac gx:=(G x (ProjIR2 Hx)).
LetTac gy:=(G y (ProjIR2 Hy)).
LetTac f'x:=(F' x (ProjIR1 Hx')).
LetTac g'x:=(G' x (ProjIR2 Hx')).
Apply leEq_wdl with (AbsIR ((fy[-]fx)[-]f'x[*](y[-]x))[+]((gy[-]gx)[-]g'x[*](y[-]x))).
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both; Unfold fx fy gx gy f'x g'x; [Apply H0 | Apply H3]; Try Assumption; Apply leEq_transitive with (Min df dg).
Assumption.
Apply Min_leEq_lft.
Assumption.
Apply Min_leEq_rht.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_inv : (Derivative_I Hab' {--}F {--}F').
(* End_Tex_Verb *)
Clear derG.
Elim derF; Intros incF H1.
Elim H1; Intros incF' H2.
Clear H1.
Apply Derivative_I_char.
Included.
Included.
Intros e He.
Elim (H2 e He); Intros d H0 H1.
Exists d.
Assumption.
Intros.
Simpl.
Apply leEq_wdl with (AbsIR [--](((F y Hy)[-](F x Hx))[-](F' x Hx')[*](y[-]x))).
EApply leEq_wdl.
2: Apply AbsIR_inv.
Auto.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_mult :
  (Derivative_I Hab' F{*}G F{*}G'{+}F'{*}G).
(* End_Tex_Verb *)
Elim derF; Intros incF H1.
Elim H1; Intros incF' H2.
Elim derG; Intros incG H5.
Elim H5; Intros incG' H6.
Clear H5 H1.
LetTac contF:=(deriv_imp_contin_I ????? (less_leEq ??? Hab') derF).
LetTac contG:=(deriv_imp_contin_I ????? (less_leEq ??? Hab') derG).
LetTac contG':=(deriv_imp_contin'_I ????? (less_leEq ??? Hab') derG).
LetTac nF:=(Norm_Funct contF).
LetTac nG:=(Norm_Funct contG).
LetTac nG':=(Norm_Funct contG').
Apply Derivative_I_char.
Contin.
Contin.
Intros e He.
LetTac M:=(Max (Max nF nG) nG')[+]One.
Cut Zero[<]M.
Intro HM'.
Cut M[#]Zero.
Intro HM.
2: Apply Greater_imp_ap; Assumption.
Cut Three[*]M[#]Zero.
Intro H3M.
2: Apply mult_resp_ap_zero; [Apply three_ap_zero | Assumption].
Cut Zero[<]e[/]?[//]H3M.
Intro HeM.
Elim (contin_prop ???? contF ? HeM); Intros dc H H0.
Elim (H2 ? HeM); Intros df H1 H3.
Elim (H6 ? HeM); Intros dg H4 H5.
Clear H2 H6.
LetTac d:=(Min (Min df dg) dc).
Exists d.
Unfold d; Repeat Apply less_Min; Assumption.
Intros.
Simpl.
LetTac fx:=(F x (ProjIR1 Hx)).
LetTac fy:=(F y (ProjIR1 Hy)).
LetTac gx:=(G x (ProjIR2 Hx)).
LetTac gy:=(G y (ProjIR2 Hy)).
LetTac f'x:=(F' x (ProjIR1 (ProjIR2 Hx'))).
LetTac g'x:=(G' x (ProjIR2 (ProjIR1 Hx'))).
Apply leEq_wdl with (AbsIR (fy[*]gy[-]fx[*]gx)[-](fx[*]g'x[+]f'x[*]gx)[*](y[-]x)).
2: Apply AbsIR_wd; Unfold fx f'x gx g'x; Rational.
Apply leEq_wdl with (AbsIR fy[*]((gy[-]gx)[-]g'x[*](y[-]x))[+](fy[-]fx)[*]g'x[*](y[-]x)[+]gx[*]((fy[-]fx)[-]f'x[*](y[-]x))).
Stepr e[*](AbsIR y[-]x).
RStepr ((e[/]ThreeNZ)[*](AbsIR y[-]x))[+]((e[/]ThreeNZ)[*](AbsIR y[-]x))[+]((e[/]ThreeNZ)[*](AbsIR y[-]x)).
EApply leEq_transitive; [Apply triangle_IR | Apply plus_resp_leEq_both].
EApply leEq_transitive; [Apply triangle_IR | Apply plus_resp_leEq_both].
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with M[*](AbsIR (gy[-]gx)[-]g'x[*](y[-]x)).
Apply mult_resp_leEq_rht; [Apply leEq_transitive with nF | Apply AbsIR_nonneg].
Unfold nF I fy; Apply norm_bnd_AbsIR.
Assumption.
Unfold M; EApply leEq_transitive.
2: Apply less_leEq; Apply less_plusOne.
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Apply lft_leEq_Max.
Apply shift_mult_leEq' with HM.
Assumption.
RStepr (e[/]?[//]H3M[*](AbsIR y[-]x)).
Unfold gx gy g'x; Apply H5; Try Assumption.
Apply leEq_transitive with d.
Assumption.
Unfold d; EApply leEq_transitive; [Apply Min_leEq_lft | Apply Min_leEq_rht].
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_rht.
2: Apply AbsIR_nonneg.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with (AbsIR fy[-]fx)[*]M.
Apply mult_resp_leEq_lft.
Unfold M; EApply leEq_transitive.
2: Apply less_leEq; Apply less_plusOne.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Unfold nG' I g'x; Apply norm_bnd_AbsIR; Assumption.
Apply AbsIR_nonneg.
Apply shift_mult_leEq with HM.
Assumption.
RStepr e[/]?[//]H3M.
Unfold fx fy; Apply H0; Try Assumption.
Apply leEq_transitive with d.
2: Unfold d; Apply Min_leEq_rht.
EApply leEq_wdl.
Apply H7.
Apply AbsIR_minus.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with M[*](AbsIR (fy[-]fx)[-]f'x[*](y[-]x)).
Apply mult_resp_leEq_rht; [Apply leEq_transitive with nG | Apply AbsIR_nonneg].
Unfold nG I gx; Apply norm_bnd_AbsIR; Assumption.
Unfold M; EApply leEq_transitive.
2: Apply less_leEq; Apply less_plusOne.
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Apply rht_leEq_Max.
Apply shift_mult_leEq' with HM.
Assumption.
RStepr (e[/]?[//]H3M[*](AbsIR y[-]x)).
Unfold fx fy f'x; Apply H3; Try Assumption.
Apply leEq_transitive with d.
Assumption.
Unfold d; EApply leEq_transitive; [Apply Min_leEq_lft | Apply Min_leEq_lft].
Apply AbsIR_wd; Rational.
Apply div_resp_pos.
Step Three[*](Zero::IR); Apply mult_resp_less_lft.
Assumption.
Apply pos_three.
Assumption.
Unfold M; EApply leEq_less_trans.
2: Apply less_plusOne.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Unfold nG'; Apply positive_norm.
Qed.

(* Tex_Prose
As was the case for continuity, the rule for the reciprocal function has a side condition.
*)

(* Begin_Tex_Verb *)
Hypothesis Fbnd:(bnd_away_zero I F).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Derivative_I_recip :
  (Derivative_I Hab' {1/}F {--}(F'{/}(F{*}F))).
(* End_Tex_Verb *)
Cut (x:IR)(Hx:(I x))(Hx':?)(F x Hx')[#]Zero.
Cut (x:IR)(Hx:(I x))(Hx':?)(F{*}F x Hx')[#]Zero.
Intros Hff Hf.
Clear derG.
Elim derF; Intros incF H1.
Elim H1; Intros incF' H2.
LetTac contF := (deriv_imp_contin_I ????? Hab derF).
LetTac contF' := (deriv_imp_contin'_I ????? Hab derF).
LetTac contF_ :=(contin_prop ???? contF).
Clear H1.
Apply Derivative_I_char.
Contin.
Contin.
Intros e He.
Cut (Continuous_I Hab {1/}F); [Intro | Contin].
LetTac nF1:=(Norm_Funct H).
LetTac nF':=(Norm_Funct contF').
LetTac M:=(Max nF1 nF')[+]One.
Cut Zero[<]M.
Intro HM.
Cut M[#]Zero.
Intro.
2: Apply Greater_imp_ap; Assumption.
Cut Two[*]M[*]M[#]Zero.
Intro HM2.
Cut Two[*]M[*]M[*]M[*]M[#]Zero.
Intro HM4.
Cut Zero[<]e[/]?[//]HM2.
Intro HeM2.
Cut Zero[<]e[/]?[//]HM4.
Intro HeM4.
Elim (contF_ ? HeM4).
Intros d1 H1 H3.
Elim (H2 ? HeM2).
Intros d2 H4 H5.
Clear H2.
Exists (Min d1 d2).
Apply less_Min; Assumption.
Intros.
Cut (x:IR)(Hx:(I x))(Hx':?)(AbsIR (One[/]?[//](Hf x Hx Hx')))[<=]M.
Intro leEqM.
2: Intros z Hz Hz'.
2: Apply leEq_wdl with (AbsIR ({1/}F z (contin_imp_inc ???? H z Hz))).
2: Unfold M; EApply leEq_transitive.
3: Apply less_leEq; Apply less_plusOne.
2: EApply leEq_transitive.
3: Apply lft_leEq_Max.
2: Unfold nF1; Apply norm_bnd_AbsIR; Assumption.
2: Apply AbsIR_wd; Simpl; Algebra.
Cut (Pred F x); [Intro Hxx | Simpl in Hx; Unfold extend in Hx; Inversion_clear Hx; Assumption].
Cut (Pred F y); [Intro Hyy | Simpl in Hy; Unfold extend in Hy; Inversion_clear Hy; Assumption].
Cut (Pred F' x); [Intro Hxx' | Simpl in Hx'; Unfold extend in Hx'; Inversion_clear Hx'; Assumption].
Apply leEq_wdl with (AbsIR ((One[/]?[//](Hf y H6 Hyy))[-](One[/]?[//](Hf x H2 Hxx)))
  [+]((F' x Hxx')[/]?[//](mult_resp_ap_zero ??? (Hf x H2 Hxx) (Hf x H2 Hxx)))[*](y[-]x)).
Apply leEq_wdl with (AbsIR ([--](One[/]?[//](mult_resp_ap_zero ??? (Hf x H2 Hxx) (Hf y H6 Hyy))))[*]
  ((((F y Hyy)[-](F x Hxx))[-](F' x Hxx')[*](y[-]x))[+](F' x Hxx')[*]
    (((F x Hxx)[-](F y Hyy))[/]?[//](Hf x H2 Hxx))[*](y[-]x))).
2: Apply AbsIR_wd; Rational.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
RStepr (M[*]M)[*]((e[/]?[//](mult_resp_ap_zero ??? H0 H0))[*](AbsIR y[-]x)).
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
EApply leEq_wdl.
2: Apply AbsIR_inv.
Apply leEq_wdl with (AbsIR (One[/]?[//](Hf x H2 Hxx))[*](One[/]?[//](Hf y H6 Hyy))).
2: Apply AbsIR_wd; Rational.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg; Apply leEqM.
EApply leEq_transitive.
Apply triangle_IR.
RStepr (e[/]?[//]HM2)[*](AbsIR y[-]x)[+](e[/]?[//]HM2)[*](AbsIR y[-]x).
Apply plus_resp_leEq_both.
Apply H5; Try Assumption.
EApply leEq_transitive.
Apply H7.
Apply Min_leEq_rht.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_rht.
2: Apply AbsIR_nonneg.
Apply leEq_wdl with (AbsIR ((F x Hxx)[-](F y Hyy))[*]((F' x Hxx')[/]?[//](Hf x H2 Hxx))).
2: Apply AbsIR_wd; Rational.
RStepr (e[/]?[//]HM4)[*](M[*]M).
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
Apply H3; Try Assumption.
EApply leEq_transitive.
Apply H7.
Apply Min_leEq_lft.
Apply leEq_wdl with (AbsIR (F' x Hxx')[*](One[/]?[//](Hf x H2 Hxx))).
2: Apply AbsIR_wd; Rational.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
Unfold M; EApply leEq_transitive.
2: Apply less_leEq; Apply less_plusOne.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Unfold nF'; Apply norm_bnd_AbsIR; Assumption.
Apply leEqM.
Apply AbsIR_wd.
Simpl; Rational.
Apply div_resp_pos.
Repeat (Step (Zero::IR)[*]Zero; Apply mult_resp_less_both); Try Apply leEq_reflexive; Try Assumption.
Apply pos_two.
Assumption.
Apply div_resp_pos.
Repeat (Step (Zero::IR)[*]Zero; Apply mult_resp_less_both); Try Apply leEq_reflexive; Try Assumption.
Apply pos_two.
Assumption.
Repeat Apply mult_resp_ap_zero; Try Assumption.
Apply two_ap_zero.
Repeat Apply mult_resp_ap_zero; Try Assumption.
Apply two_ap_zero.
Unfold M; EApply leEq_less_trans.
2: Apply less_plusOne.
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Unfold nF1; Apply positive_norm.
Intros.
Apply bnd_imp_ap_zero with I; Auto.
Unfold I; Included.
Intros.
Apply bnd_imp_ap_zero with I; Auto.
Qed.

End Local_Results.

Hints Immediate derivative_imp_inc derivative_imp_inc' : included.

Tactic Definition Deriv := EAuto with derivate continuous included.

Hints Resolve Derivative_I_const Derivative_I_id Derivative_I_plus Derivative_I_inv Derivative_I_mult Derivative_I_recip : derivate.

Section Corolaries.

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

Variables F,F',G,G':PartIR.

Hypothesis derF : (Derivative_I Hab' F F').
Hypothesis derG : (Derivative_I Hab' G G').

(* Tex_Prose
From this lemmas the rules for the other algebraic operations follow directly.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_I_minus : (Derivative_I Hab' F{-}G F'{-}G').
(* End_Tex_Verb *)
Apply Derivative_I_wdl with F{+}{--}G.
FEQ.
Apply Derivative_I_wdr with F'{+}{--}G'.
FEQ.
Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_scal : (c:IR)(Derivative_I Hab' c{**}F c{**}F').
(* End_Tex_Verb *)
Intro.
Unfold Fscalmult.
Apply Derivative_I_wdr with ({-C-}c{*}F'){+}{-C-}Zero{*}F.
FEQ.
Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_nth : (n:nat)(Derivative_I Hab' F{^}(S n) (nring (S n)){**}(F'{*}F{^}n)).
(* End_Tex_Verb *)
Unfold Fscalmult.
Intro; Induction n.
Apply Derivative_I_wdl with F.
FEQ.
Apply Derivative_I_wdr with F'.
FEQ.
Assumption.
Apply Derivative_I_wdl with F{*}F{^}(S n).
Apply FNth_mult'; Included.
Apply Derivative_I_wdr with F{*}(({-C-}(nring (S n))){*}(F'{*}F{^}n)){+}F'{*}F{^}(S n).
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl.
LetTac fx:=(F x (ProjIR1 (ProjIR1 Hx))); Simpl in fx; Fold fx.
LetTac f'x:=(F' x (ProjIR1 (ProjIR2 (ProjIR2 (ProjIR1 Hx))))); Simpl in f'x; Fold f'x.
LetTac fx':=(F x (ProjIR2 (ProjIR2 (ProjIR2 (ProjIR1 Hx))))); Simpl in fx'; Fold fx'.
LetTac f'x':=(F' x (ProjIR1 (ProjIR2 Hx))); Simpl in f'x'; Fold f'x'.
LetTac fx'':=(F x (ProjIR2 (ProjIR2 Hx))); Simpl in fx''; Fold fx''.
LetTac f'x'':=(F' x (ProjIR1 (ProjIR2 Hx'))); Simpl in f'x''; Fold f'x''.
LetTac fx''':=(F x (ProjIR2 (ProjIR2 Hx'))); Simpl in fx'''; Fold fx'''.
Apply eq_transitive_unfolded with (fx[*](((nring n)[+]One)[*](f'x[*](fx[^]n))))[+](f'x[*]((fx[^]n)[*]fx)).
Step (fx[*](((nring n)[+]One)[*](f'x[*](fx'[^]n))))[+](f'x'[*]((fx''[^]n)[*]fx'')).
Repeat Apply bin_op_wd_unfolded; Try Apply nexp_wd; Unfold fx f'x fx' f'x' fx''; Rational.
RStep (((nring n)[+]One)[+]One)[*]((f'x[*]((fx[^]n)[*]fx))).
Stepr (((nring n)[+]One)[+]One)[*]((f'x''[*]((fx'''[^]n)[*]fx'''))).
Repeat Apply bin_op_wd_unfolded; Try Apply nexp_wd; Unfold fx f'x f'x'' fx'''; Rational.
Deriv.
Qed.

Hypothesis Gbnd:(bnd_away_zero I G).

(* Begin_Tex_Verb *)
Lemma Derivative_I_div : (Derivative_I Hab' F{/}G (F'{*}G{-}F{*}G'){/}(G{*}G)).
(* End_Tex_Verb *)
Cut (Derivative_I Hab' F{/}G F{*}{--}(G'{/}(G{*}G)){+}(F'{*}{1/}G)).
Intro.
EApply Derivative_I_wdr.
2: Apply H.
Apply eq_imp_Feq.
Included.
Apply included_FDiv.
Included.
Included.
Intros; Apply bnd_imp_ap_zero with I; Unfold I; Included.
Intros; Simpl; Rational.
Apply Derivative_I_wdl with F{*}{1/}G.
FEQ.
Deriv.
Qed.

End Corolaries.

Hints Resolve Derivative_I_minus Derivative_I_nth Derivative_I_scal Derivative_I_div : derivate.
