(* $Id: MoreIntegrals.v,v 1.15 2003/03/13 12:06:21 lcf Exp $ *)

Require Export Integral.
Require Export MoreFunctions.

Section Lemmas.

(* Tex_Prose
\chapter{The generalized integral}

In this file we extend the definition of integral to allow for arbitrary integration domains (that is, not requiring that the lower endpoint of integration be less or equal than the upper endpoint) and we prove the fundamental properties of the new operator.

\begin{convention} Let \verb!a,b:IR! and assume \verb!F,G! are partial functions continuous in $[\min(a,b),\max(a,b)]$.
\end{convention}

\section{Definitions}

Before we define the new integral we need to some trivial interval inclusions.
*)

Variables a,b:IR.
Hypothesis Hab:(Min a b)[<=](Max a b).

(* Begin_Tex_Verb *)
Lemma compact_inc_Min_lft : (H:?)
  (included (compact (Min a b) a H) (Compact Hab)).
(* End_Tex_Verb *)
Intros.
Apply included_compact; Split.
Apply leEq_reflexive.
Apply Min_leEq_Max.
Apply Min_leEq_lft.
Apply lft_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma compact_inc_Min_rht : (H:?)
  (included (compact (Min a b) b H) (Compact Hab)).
(* End_Tex_Verb *)
Intros.
Apply included_compact; Split.
Apply leEq_reflexive.
Apply Min_leEq_Max.
Apply Min_leEq_rht.
Apply rht_leEq_Max.
Qed.

End Lemmas.

Section Definitions.

(* Tex_Prose
The integral is defined by the formula $\int_a^bf=\int_{\min(a,b)}^bf-\int_{\min(a,b)}^af$, inspired by the domain union rule; obviously it coincides with the classical definition, and it collapses to the old one in the case $a\leq b$.
*)

Variables a,b:IR.
Hypothesis Hab:(Min a b)[<=](Max a b).
Variable F:PartIR.

Hypothesis HF:(Continuous_I Hab F).

(* Begin_Tex_Verb *)
Lemma Integral_inc1 :
  (Continuous_I (Min_leEq_lft a b) F).
(* End_Tex_Verb *)
EApply included_imp_contin with Hab:=Hab.
2: Apply HF.
Apply compact_inc_Min_lft.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_inc2 :
  (Continuous_I (Min_leEq_rht a b) F).
(* End_Tex_Verb *)
EApply included_imp_contin with Hab:=Hab.
2: Apply HF.
Apply compact_inc_Min_rht.
Qed.

(* Begin_Tex_Verb *)
Definition Integral :=
  (integral ?? (Min_leEq_rht a b) F Integral_inc2)
    [-](integral ?? (Min_leEq_lft a b) ? Integral_inc1).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Integral_integral : (Hab':a[<=]b)(HF':?)
  Integral[=](integral ?? Hab' F HF').
(* End_Tex_Verb *)
Intros.
Unfold Integral.
Stepr (integral a b Hab' F HF')[-]Zero.
Apply cg_minus_wd.
Apply integral_wd'.
Apply leEq_imp_Min_is_lft; Assumption.
Algebra.
Apply integral_empty.
Apply leEq_imp_Min_is_lft; Assumption.
Qed.

End Definitions.

Implicits Integral [1 2 3 4].

Section Properties_of_Integral.

(* Tex_Prose
\section{Properties of the Integral}

All our old properties carry over to this new definition---and some new ones, too.  We begin with welldefinedness and strong extensionality.
*)

Variables a,b:IR.
Hypothesis Hab:(Min a b)[<=](Max a b).
Variables F,G:PartIR.

Hypothesis contF : (Continuous_I Hab F).
Hypothesis contG : (Continuous_I Hab G).

(* Begin_Tex_Verb *)
Lemma Integral_strext : ((Integral contF)[#](Integral contG))->
  {x:IR & (Compact Hab x) & 
    (Hx,Hx':?)(Part F x Hx)[#](Part G x Hx')}.
(* End_Tex_Verb *)
Intro.
Unfold Integral in H.
Elim (cg_minus_strext ????? H); Intro.
Elim (integral_strext ??????? a0); Intros.
Exists x.
Apply compact_inc_Min_rht with H:=(Min_leEq_rht a b); Assumption.
Assumption.
Elim (integral_strext ??????? b0); Intros.
Exists x.
Apply compact_inc_Min_lft with H:=(Min_leEq_lft a b); Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_strext' : (c,d,Hcd,HF1,HF2:?)
  (((!Integral ?? Hab F HF1)[#](!Integral c d Hcd F HF2))->
    (a[#]c)+(b[#]d)).
(* End_Tex_Verb *)
Intros.
Elim (cg_minus_strext ????? H); Clear H; Intro H; Elim (integral_strext' ????????? H); Clear H; Intro H.
Elim (min_strext_unfolded ???? H); Auto.
Auto.
Elim (min_strext_unfolded ???? H); Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_wd : (Feq (Compact Hab) F G)->
  (Integral contF)[=](Integral contG).
(* End_Tex_Verb *)
Intros; Unfold Integral.
Apply cg_minus_wd; Apply integral_wd.
Apply included_Feq with (Compact Hab).
Apply compact_inc_Min_rht.
Assumption.
Apply included_Feq with (Compact Hab).
Apply compact_inc_Min_lft.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_wd' : (a',b',Ha'b',contF':?)
  (a[=]a')->(b[=]b')->
  (Integral contF)[=](!Integral a' b' Ha'b' F contF').
(* End_Tex_Verb *)
Intros.
Unfold Integral.
Apply cg_minus_wd; Apply integral_wd'; Try Apply bin_op_wd_unfolded; Algebra.
Qed.

(* Tex_Prose
The integral is a linear operator.
*)

(* Begin_Tex_Verb *)
Lemma Integral_const : (c:IR)
  (H:(Continuous_I Hab {-C-}c))(Integral H)[=]c[*](b[-]a).
(* End_Tex_Verb *)
Intros.
Unfold Integral.
RStepr c[*](b[-](Min a b))[-]c[*](a[-](Min a b)).
Apply cg_minus_wd; Apply integral_const.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_comm_scal : (c:IR)
  (H:(Continuous_I Hab c{**}F))
    (Integral H)[=]c[*](Integral contF).
(* End_Tex_Verb *)
Intros.
Unfold Integral.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply dist_2a.
Apply cg_minus_wd; Apply integral_comm_scal.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_plus : (H:(Continuous_I Hab F{+}G))
  (Integral H)[=](Integral contF)[+](Integral contG).
(* End_Tex_Verb *)
Intro.
Unfold Integral.
Cut (x,y,z,w:IR)((x[-]y)[+](z[-]w))[=]((x[+]z)[-](y[+]w)); Intros.
2: Rational.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply H0.
Apply cg_minus_wd; Apply integral_plus.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_inv : (H:(Continuous_I Hab {--}F))
  (Integral H)[=][--](Integral contF).
(* End_Tex_Verb *)
Intro.
Unfold Integral.
Cut (x,y:IR)([--](x[-]y)[=]([--]x[-][--]y)); Intros.
2: Rational.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply H0.
Apply cg_minus_wd; Apply integral_inv.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_minus : (H:(Continuous_I Hab F{-}G))
  (Integral H)[=](Integral contF)[-](Integral contG).
(* End_Tex_Verb *)
Intro.
Unfold Integral.
Cut (x,y,z,w:IR)((x[-]y)[-](z[-]w))[=]((x[-]z)[-](y[-]w)); Intros.
2: Rational.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply H0.
Apply cg_minus_wd; Apply integral_minus.
Qed.

(* Begin_Tex_Verb *)
Lemma linear_Integral : (alpha,beta:IR)
  (H:(Continuous_I Hab alpha{**}F{+}beta{**}G))
  (Integral H)[=]
    alpha[*](Integral contF)[+]beta[*](Integral contG).
(* End_Tex_Verb *)
Intros; Unfold Integral.
Cut (x,y,z,r,s,t:IR)(x[*](y[-]z)[+]r[*](s[-]t))[=](x[*]y[+]r[*]s)[-](x[*]z[+]r[*]t).
2: Intros; Rational.
Intro; EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply H0.
Clear H0.
Apply cg_minus_wd; Apply linear_integral.
Qed.

(* Tex_Prose
If the endpoints are equal then the integral vanishes.
*)

(* Begin_Tex_Verb *)
Lemma Integral_empty : (a[=]b)->(Integral contF)[=]Zero.
(* End_Tex_Verb *)
Intros.
Unfold Integral.
Stepr (Zero::IR)[-]Zero.
Apply cg_minus_wd; Apply integral_empty.
Stepr a; Apply leEq_imp_Min_is_lft; Apply eq_imp_leEq; Assumption.
Apply leEq_imp_Min_is_lft; Apply eq_imp_leEq; Assumption.
Qed.

(* Tex_Prose
And the norm provides an upper bound for the absolute value of the integral.
*)

(* Begin_Tex_Verb *)
Lemma Integral_leEq_norm : (AbsIR (Integral contF))[<=]
  (Norm_Funct contF)[*](AbsIR b[-]a).
(* End_Tex_Verb *)
Unfold Integral.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply leEq_transitive with (Norm_Funct contF)[*](b[-](Min a b))[+](Norm_Funct contF)[*](a[-](Min a b)).
Apply plus_resp_leEq_both; (EApply leEq_transitive; [Apply integral_leEq_norm | Apply mult_resp_leEq_rht]).
Apply leEq_Norm_Funct; Intros.
Apply norm_bnd_AbsIR; Apply compact_inc_Min_rht with H:=(Min_leEq_rht a b); Assumption.
Apply shift_leEq_minus; Step (Min a b); Apply Min_leEq_rht.
Apply leEq_Norm_Funct; Intros.
Apply norm_bnd_AbsIR; Apply compact_inc_Min_lft with H:=(Min_leEq_lft a b); Assumption.
Apply shift_leEq_minus; Step (Min a b); Apply Min_leEq_lft.
EApply leEq_wdl.
2: Apply ring_dist_unfolded.
Apply mult_resp_leEq_lft.
2: Apply positive_norm.
RStep (a[+]b)[-]Two[*](Min a b).
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Apply shift_leEq_mult' with (two_ap_zero IR).
Apply pos_two.
Apply leEq_Min.
Apply shift_div_leEq.
Apply pos_two.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
RStep b[-]a; Apply leEq_AbsIR.
Apply shift_div_leEq.
Apply pos_two.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
RStep [--](b[-]a); Apply inv_leEq_AbsIR.
Qed.

End Properties_of_Integral.

Section More_Properties.

(* Tex_Prose
Two other ways of stating the addition law for domains.
*)

(* Begin_Tex_Verb *)
Lemma integral_plus_Integral :
  (a,b,Hab,F,c,Hac,Hcb,Hab',Hac',Hcb':?)
    (integral c b Hcb F Hcb')[=]
      (integral a b Hab F Hab')[-](integral a c Hac F Hac').
(* End_Tex_Verb *)
Intros.
RStep ((integral a c Hac F Hac')[+](integral c b Hcb F Hcb'))[-](integral a c Hac F Hac').
Apply cg_minus_wd.
Apply integral_plus_integral.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_plus_integral' :
  (a,b,Hab,F,c,Hac,Hcb,Hab',Hac',Hcb':?)
    (integral a c Hac F Hac')[=]
      (integral a b Hab F Hab')[-](integral c b Hcb F Hcb').
(* End_Tex_Verb *)
Intros.
RStep ((integral a c Hac F Hac')[+](integral c b Hcb F Hcb'))[-](integral c b Hcb F Hcb').
Apply cg_minus_wd.
Apply integral_plus_integral.
Algebra.
Qed.

(* Tex_Prose
And now we can prove the addition law for domains with our general operator.

\begin{convention} Assume \verb!c:IR!.
\end{convention}
*)

Variables a,b,c:IR.
(* Begin_Tex_Verb *)
Hypothesis Hab':(Min a b)[<=](Max a b).
Hypothesis Hac':(Min a c)[<=](Max a c).
Hypothesis Hcb':(Min c b)[<=](Max c b).
Hypothesis Habc':(Min (Min a b) c)[<=](Max (Max a b) c).
(* End_Tex_Verb *)

Variable F:PartIR.

(* Begin_Tex_Verb *)
Hypothesis Hab:(Continuous_I Hab' F).
Hypothesis Hac:(Continuous_I Hac' F).
Hypothesis Hcb:(Continuous_I Hcb' F).
Hypothesis Habc:(Continuous_I Habc' F).
(* End_Tex_Verb *)

Local le_abc_ab : (Min (Min a b) c)[<=](Min a b).
Apply Min_leEq_lft.
Qed.

Local le_abc_ac : (Min (Min a b) c)[<=](Min a c).
Apply leEq_Min.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply Min_leEq_lft.
Apply Min_leEq_rht.
Qed.

Local le_abc_cb : (Min (Min a b) c)[<=](Min c b).
Apply leEq_Min.
Apply Min_leEq_rht.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply Min_leEq_rht.
Qed.

Local le_abc_a : (Min (Min a b) c)[<=]a.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply Min_leEq_lft.
Qed.

Local le_abc_b : (Min (Min a b) c)[<=]b.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply Min_leEq_rht.
Qed.

Local le_abc_c : (Min (Min a b) c)[<=]c.
Apply Min_leEq_rht.
Qed.

Local le_ab_a : (Min a b)[<=]a.
Apply Min_leEq_lft.
Qed.

Local le_cb_c : (Min c b)[<=]c.
Apply Min_leEq_lft.
Qed.

Local le_ac_a : (Min a c)[<=]a.
Apply Min_leEq_lft.
Qed.

Local le_ab_b : (Min a b)[<=]b.
Apply Min_leEq_rht.
Qed.

Local le_cb_b : (Min c b)[<=]b.
Apply Min_leEq_rht.
Qed.

Local le_ac_c : (Min a c)[<=]c.
Apply Min_leEq_rht.
Qed.

Local Habc_abc : (Compact Habc' (Min (Min a b) c)).
Apply compact_inc_lft.
Qed.

Local Habc_ab : (Continuous_I le_abc_ab F).
Apply included_imp_contin with Hab:=Habc'.
2: Apply Habc.
Apply included_compact; [Apply Habc_abc | Split].
Apply Min_leEq_lft.
EApply leEq_transitive.
Apply Min_leEq_Max.
Apply lft_leEq_Max.
Qed.

Local Habc_ac : (Continuous_I le_abc_ac F).
Apply included_imp_contin with Hab:=Habc'.
2: Apply Habc.
Apply included_compact; [Apply Habc_abc | Split].
Apply le_abc_ac.
EApply leEq_transitive.
Apply Min_leEq_Max.
Apply Max_leEq.
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Apply lft_leEq_Max.
Apply rht_leEq_Max.
Qed.

Local Habc_cb : (Continuous_I le_abc_cb F).
Apply included_imp_contin with Hab:=Habc'.
2: Apply Habc.
Apply included_compact; [Apply Habc_abc | Split].
Apply le_abc_cb.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Apply Min_leEq_lft.
Qed.

Local Habc_a : (Continuous_I le_abc_a F).
Apply included_imp_contin with Hab:=Habc'.
2: Apply Habc.
Apply included_compact; [Apply Habc_abc | Split].
Apply le_abc_a.
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Apply lft_leEq_Max.
Qed.

Local Habc_b : (Continuous_I le_abc_b F).
Apply included_imp_contin with Hab:=Habc'.
2: Apply Habc.
Apply included_compact; [Apply Habc_abc | Split].
Apply le_abc_b.
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Apply rht_leEq_Max.
Qed.

Local Habc_c : (Continuous_I le_abc_c F).
Apply included_imp_contin with Hab:=Habc'.
2: Apply Habc.
Apply included_compact; [Apply Habc_abc | Split].
Apply le_abc_c.
Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_plus_Integral :
  (Integral Hab)[=](Integral Hac)[+](Integral Hcb).
(* End_Tex_Verb *)
Unfold Integral.
Apply eq_transitive_unfolded with ((integral ?? le_abc_b ? Habc_b)[-](integral ?? le_abc_ab ? Habc_ab))
  [-]((integral ?? le_abc_a ? Habc_a)[-](integral ?? le_abc_ab ? Habc_ab)).
Apply cg_minus_wd; Apply integral_plus_Integral.
RStep (integral ?? le_abc_b ? Habc_b)[-](integral ?? le_abc_a ? Habc_a).
RStep (((integral ?? le_abc_c ? Habc_c)[-](integral ?? le_abc_ac ? Habc_ac))[-]
    ((integral ?? le_abc_a ? Habc_a)[-](integral ?? le_abc_ac ? Habc_ac)))[+]
  (((integral ?? le_abc_b ? Habc_b)[-](integral ?? le_abc_cb ? Habc_cb))[-]
    ((integral ?? le_abc_c ? Habc_c)[-](integral ?? le_abc_cb ? Habc_cb))).
Apply eq_symmetric_unfolded; Apply bin_op_wd_unfolded; Apply cg_minus_wd; Apply integral_plus_Integral.
Qed.

(* Tex_Prose
Notice that, unlike in the classical case, an extra hypothesis (the continuity of $F$ in the interval $[\min(a,b,c),\max(a,b,c)]$) must be assumed.
*)

End More_Properties.

Section Corollaries.

Variables a,b:IR.
Hypothesis Hab:(Min a b)[<=](Max a b).
Variable F:PartIR.

Hypothesis contF:(Continuous_I Hab F).

(* Tex_Prose
As a corollary, we get the following rule:
*)
(* Begin_Tex_Verb *)
Lemma Integral_op : (Hab':?)
  (contF':(!Continuous_I (Min b a) (Max b a) Hab' F))
  (Integral contF)[=][--](Integral contF').
(* End_Tex_Verb *)
Intros.
Apply cg_inv_unique'.
Cut (Continuous_I (Min_leEq_Max a a) F); Intros.
Apply eq_transitive_unfolded with (Integral H).
Cut (Min (Min a a) b)[<=](Max (Max a a) b); Intros.
Apply eq_symmetric_unfolded; Apply Integral_plus_Integral with H0.
Cut (included (Compact H0) (Compact Hab)); Intros.
Exact (included_imp_contin ??????? H1 contF).
Apply included_compact.
Split.
Apply leEq_Min.
Apply leEq_transitive with a.
Apply Min_leEq_lft.
Apply eq_imp_leEq; Apply eq_symmetric_unfolded; Apply Min_id.
Apply Min_leEq_rht.
Apply leEq_transitive with b.
Apply Min_leEq_rht.
Apply rht_leEq_Max.
Split.
Apply leEq_transitive with b.
Apply Min_leEq_rht.
Apply rht_leEq_Max.
Apply Max_leEq.
Apply leEq_wdl with a.
Apply lft_leEq_Max.
Apply eq_symmetric_unfolded; Apply Max_id.
Apply rht_leEq_Max.
Apply leEq_transitive with b.
Apply Min_leEq_rht.
Apply rht_leEq_Max.
Apply Integral_empty; Algebra.
Apply included_imp_contin with Hab:=Hab.
2: Apply contF.
Red; Intros.
Apply compact_wd with a.
Split.
Apply Min_leEq_lft.
Apply lft_leEq_Max.
Inversion_clear H.
Apply leEq_imp_eq.
EApply leEq_wdl.
Apply H0.
Apply Min_id.
EApply leEq_wdr.
Apply H1.
Apply Max_id.
Qed.

(* Tex_Prose
Finally, some miscellaneous results:
*)

(* Begin_Tex_Verb *)
Lemma Integral_less_norm : (a[#]b)->
  (x:IR)(Compact Hab x)->(Hx:?)
    ((AbsIR (F x Hx))[<](Norm_Funct contF))->
  (AbsIR (Integral contF))[<](Norm_Funct contF)[*](AbsIR b[-]a).
(* End_Tex_Verb *)
Intros.
LetTac N:=(Norm_Funct contF).
Elim (ap_imp_less ??? H); Intro.
Apply less_wdr with N[*](b[-]a).
EApply less_wdl.
EApply less_leEq_trans.
Apply integral_less_norm with contF:=(included_imp_contin ??????? (compact_map2 a b (less_leEq ??? a0) Hab) contF) Hx:=Hx; Auto.
Apply compact_map1 with Hab':=Hab; Auto.
EApply less_leEq_trans.
Apply H1.
Unfold N; Apply included_imp_norm_leEq.
Apply compact_map1.
Apply mult_resp_leEq_rht.
Unfold N; Apply included_imp_norm_leEq.
Apply compact_map2.
Apply shift_leEq_minus; Apply less_leEq.
Step a; Auto.
Apply AbsIR_wd; Apply eq_symmetric_unfolded.
Apply Integral_integral.
Apply mult_wd_rht.
Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply shift_leEq_minus; Apply less_leEq.
Step a; Auto.

Apply less_wdr with N[*](a[-]b).
LetTac Hmin := (Min_leEq_Max b a).
Cut (included (Compact Hmin) (Compact Hab)).
Cut (included (Compact Hab) (Compact Hmin)); Intros.
Cut (Continuous_I Hmin F); Intros.
EApply less_wdl.
EApply less_leEq_trans.
Apply integral_less_norm with contF:=(included_imp_contin ??????? (compact_map2 ?? (less_leEq ??? b0) Hmin) H4) Hx:=Hx; Auto.
Apply compact_map1 with Hab':=Hmin; Auto.
EApply less_leEq_trans.
Apply H1.
Unfold N; Apply included_imp_norm_leEq.
EApply included_trans.
2: Apply compact_map1 with Hab':=Hmin.
Apply H2.
Apply mult_resp_leEq_rht.
Unfold N; Apply included_imp_norm_leEq.
EApply included_trans.
Apply compact_map2 with Hab':=Hmin.
Apply H3.
Apply shift_leEq_minus; Apply less_leEq.
Step b; Auto.
EApply eq_transitive_unfolded.
Apply AbsIR_inv.
Apply AbsIR_wd; Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with [--](Integral (included_imp_contin ??????? H3 contF)).
Apply Integral_op.
Apply un_op_wd_unfolded.
Apply Integral_integral.
Apply included_imp_contin with Hab:=Hab; Auto.
Red; Intros.
Apply compact_wd' with Hab:=Hab.
Apply Min_comm.
Apply Max_comm.
Auto.
Red; Intros.
Apply compact_wd' with Hab:=Hmin.
Apply Min_comm.
Apply Max_comm.
Auto.
Apply mult_wd_rht.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply shift_leEq_minus; Apply less_leEq.
Step b; Auto.
Apply AbsIR_minus.
Qed.

(* Begin_Tex_Verb *)
Lemma ub_Integral : (a[#]b)->(c:IR)
  ((x:IR)(Compact Hab x)->(Hx:?)((AbsIR (F x Hx))[<=]c))->
  (x:IR)(Compact Hab x)->(Hx:?)((AbsIR (F x Hx))[<]c)->
  (AbsIR (Integral contF))[<]c[*](AbsIR b[-]a).
(* End_Tex_Verb *)
Intros.
LetTac N:=(Norm_Funct contF).
Cut N[<=]c; Intros.
Elim (cotrans_less_unfolded ??? H2 N); Intros.
Apply less_leEq_trans with N[*](AbsIR b[-]a).
Unfold N; Apply Integral_less_norm with x Hx; Auto.
Apply mult_resp_leEq_rht; Auto.
Apply AbsIR_nonneg.
Apply leEq_less_trans with N[*](AbsIR b[-]a).
Unfold N; Apply Integral_leEq_norm.
Apply mult_resp_less; Auto.
Apply AbsIR_pos.
Apply minus_ap_zero.
Apply ap_symmetric_unfolded; Auto.
Unfold N; Apply leEq_Norm_Funct; Auto.
Qed.

End Corollaries.

(* Begin_Tex_Verb *)
Lemma Integral_ap_zero :
  (a,b,Hab:?)(F:PartIR)(contF:?)(a[#]b)->
  (x:IR)(Compact Hab x)->(Hx:?)(Zero[<](F x Hx))->
  ((x:IR)(Compact Hab x)->(Hx:?)(Zero[<=](F x Hx)))->
  Zero[<](AbsIR (!Integral a b Hab F contF)).
(* End_Tex_Verb *)
Intros.
Elim (ap_imp_less ??? H); Intro.
EApply less_leEq_trans.
2: Apply leEq_AbsIR.
EApply less_wdr.
2: Apply eq_symmetric_unfolded.
2: Apply Integral_integral with HF':=(included_imp_contin ??????? (compact_map2 a b (less_leEq ??? a0) Hab) contF).
EApply integral_gt_zero with x Hx; Auto.
Exact (compact_map1 ?? (less_leEq ??? a0) Hab x H0).
Intros; Apply H2.
Exact (compact_map2 ?? (less_leEq ??? a0) Hab ? H3).

Cut (included (Compact (Min_leEq_Max b a)) (Compact Hab)).
2: Apply included_compact; Split.
2: Apply eq_imp_leEq; Apply Min_comm.
2: Apply leEq_transitive with a; [Apply Min_leEq_rht | Apply lft_leEq_Max].
2: Apply leEq_transitive with b; [Apply Min_leEq_rht | Apply lft_leEq_Max].
2: Apply eq_imp_leEq; Apply Max_comm.
Cut (included (Compact Hab) (Compact (Min_leEq_Max b a))).
2: Apply included_compact; Split.
2: Apply eq_imp_leEq; Apply Min_comm.
2: Apply leEq_transitive with b; [Apply Min_leEq_rht | Apply lft_leEq_Max].
2: Apply leEq_transitive with a; [Apply Min_leEq_rht | Apply lft_leEq_Max].
2: Apply eq_imp_leEq; Apply Max_comm.
Intros.
EApply less_leEq_trans.
2: Apply inv_leEq_AbsIR.
EApply less_wdr.
2: Apply Integral_op with contF:=(included_imp_contin ??????? H4 contF).
EApply less_wdr.
2: Apply eq_symmetric_unfolded.
2: Apply Integral_integral with
  HF':=(included_imp_contin ??????? (compact_map2 ?? (less_leEq ??? b0) (Min_leEq_Max b a)) (included_imp_contin ??????? H4 contF)).
EApply integral_gt_zero with x Hx; Auto.
Exact (compact_map1 ?? (less_leEq ??? b0) (Min_leEq_Max b a) x (H3 x H0)).
Intros; Apply H2.
Exact (H4 ? (compact_map2 ?? (less_leEq ??? b0) (Min_leEq_Max ??) ? H5)).
Qed.

(* Begin_Tex_Verb *)
Lemma Integral_eq_zero :
  (a,b,Hab:?)(F:PartIR)(contF:?)
  (x:IR)(Compact Hab x)->((Hx:?)(Zero[<](F x Hx)))->
  ((x:IR)(Compact Hab x)->(Hx:?)(Zero[<=](F x Hx)))->
  (((!Integral a b Hab F contF)[=]Zero)->(a[=]b)).
(* End_Tex_Verb *)
Intros.
Apply not_ap_imp_eq; Intro.
Apply less_irreflexive_unfolded with x:=(Zero::IR).
Apply less_wdr with (AbsIR (Integral contF)).
2: Step_final (AbsIR Zero).
Apply Integral_ap_zero with x (contin_imp_inc ???? contF x H); Auto.
Qed.
