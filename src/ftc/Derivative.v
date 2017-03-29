(* $Id: Derivative.v,v 1.16 2003/03/13 12:06:18 lcf Exp $ *)

Require Export Continuity.

Section Definitions.

(* Tex_Prose
\chapter{Derivatives}

We will now proceed toward the development of differential calculus.  To begin with, the main notion is that of derivative.

At this stage we will not define a notion of differentiable function, mainly because the natural definition (that of being a function which has some derivative) poses some technical problems; thus, we will postpone that part of our work to a subsequent stage.

Derivative is a binary relation in the type of partial functions, dependent (once again) on a compact interval\footnote{As before, we do not define pointwise differentiability, mainly for coherence reasons.  See Bishop [1967] for a discussion on the relative little interest of that concept.} with distinct endpoints.  The reason for requiring the endpoints to be apart is mainly to be able to derive the usual properties of the derivative relation---namely, that any two derivatives of the same function must coincide.

\begin{convention} Let \verb!a,b:IR! with $a<b$ and denote by \verb!I! the interval $[a,b]$.  Throughout this section, \verb!F,F',G,G'! and \verb!H! will be partial functions with domains respectively \verb!P,P',Q,Q'! and \verb!R!.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

Variable F:PartIR.
Local P:=(Pred F).

(* Begin_Tex_Verb *)
Definition Derivative_I [F':PartIR][P':=(Pred F')] := 
  (included I (Pred F))*((included I (Pred F'))*
  ((e:IR)(Zero[<]e)->{d:IR & (Zero[<]d) |
    (x,y:IR)(I x)->(I y)->(Hx,Hy,Hx':?)((AbsIR x[-]y)[<=]d)->
      (AbsIR ((F y Hy)[-](F x Hx))[-](F' x Hx')[*](y[-]x))
    [<=]e[*](AbsIR y[-]x)})).
(* End_Tex_Verb *)

End Definitions.

Implicits Derivative_I [1 2].

Section Basic_Properties.

(* Tex_Prose
\section{Basic Properties}
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

(* Tex_Prose
Like we did for equality, we begin by stating a lemma that makes proofs of derivation easier in practice.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_I_char :
  (F,F':PartIR)[P:=(Pred F)][P':=(Pred F')]
  (included I (Pred F))->(included I (Pred F'))->
  ((e:IR)(Zero[<]e)->{d:IR & (Zero[<]d) |
    (x,y:IR)(I x)->(I y)->(Hx,Hy,Hx':?)((AbsIR x[-]y)[<=]d)->
      (AbsIR ((F y Hy)[-](F x Hx))[-](F' x Hx')[*](y[-]x))
    [<=]e[*](AbsIR y[-]x)})->(Derivative_I Hab' F F').
(* End_Tex_Verb *)
Unfold Hab.
Intros.
Repeat (Split; Auto).
Qed.

(* Tex_Prose
Derivative is a well defined relation; we will make this explicit for both arguments:
*)

Variables F,G,H:PartIR.

Local P:=(Pred F).
Local Q:=(Pred G).
Local R:=(Pred H).

(* Begin_Tex_Verb *)
Lemma Derivative_I_wdl : (Feq I F G)->
  (Derivative_I Hab' F H)->(Derivative_I Hab' G H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros H0' Heq.
Elim H0'; Intros incF incG.
Elim H1; Intros incF' H2.
Elim H2; Intros incH H3.
Clear H0' H1 H2.
Apply Derivative_I_char; Auto.
Intros e He.
Elim (H3 e He); Clear H3; Intros d H1 H2.
Exists d; Auto.
Intros.
Step (AbsIR ((F y (incF y H4))[-](F x (incF x H3)))[-](H x Hx')[*](y[-]x)); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_wdr : (Feq I F G)->
  (Derivative_I Hab' H F)->(Derivative_I Hab' H G).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros H0' Heq.
Elim H0'; Intros incF incG.
Elim H1; Intros incH H2.
Elim H2; Intros incF0 H3.
Apply Derivative_I_char; Auto.
Intros e He.
Elim (H3 e He); Clear H3; Intros d H3 H4.
Exists d; Auto.
Intros.
Step (AbsIR ((H y Hy)[-](H x Hx))[-](F x (incF x H5))[*](y[-]x)); Auto.
Qed.

Local Derivative_I_unique_lemma : (x:IR)(Compact Hab x)->(d:IR)(Zero[<]d)->{y:IR | (AbsIR x[-]y)[<=]d & (Compact Hab y)*(y[-]x[#]Zero)}.
Intros x Hx d Hd.
Elim (cotrans_less_unfolded ??? Hab' x); Intro.
Exists (Max a x[-]d[/]TwoNZ); Auto.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply less_leEq; Apply shift_minus_less'; Apply shift_less_plus.
Apply less_leEq_trans with x[-](d[/]TwoNZ).
Apply minus_resp_less_rht.
Apply pos_div_two'; Assumption.
Simpl.
Apply rht_leEq_Max.
Apply shift_leEq_minus.
Simpl.
Step (Max a x[-]d[/]TwoNZ).
Apply less_leEq.
Apply Max_less; [Assumption | Stepr x[-]Zero].
Apply minus_resp_less_rht; Apply pos_div_two; Assumption.
Split.
Split.
Apply lft_leEq_Max.
Apply Max_leEq.
Apply less_leEq; Assumption.
Apply leEq_transitive with x.
Apply shift_minus_leEq; Apply shift_leEq_plus'; Step (Zero::IR).
Apply less_leEq; Apply pos_div_two; Assumption.
Inversion_clear Hx; Assumption.
Apply less_imp_ap; Apply shift_minus_less; Stepr x; Apply Max_less.
Assumption.
Apply shift_minus_less; Apply shift_less_plus'; Step (Zero::IR).
Apply pos_div_two with eps:=d; Assumption.
Exists (Min b x[+]d[/]TwoNZ).
Apply leEq_wdl with (Min b x[+](d[/]TwoNZ))[-]x.
Apply less_leEq.
Apply shift_minus_less.
RStepr x[+]d.
EApply leEq_less_trans.
Apply Min_leEq_rht.
Apply plus_resp_less_lft.
Apply pos_div_two'; Assumption.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded; [Apply AbsIR_minus | Apply AbsIR_eq_x].
Apply less_leEq; Apply shift_less_minus; Step x; Apply less_Min.
Assumption.
Step x[+]Zero; Apply plus_resp_less_lft.
Apply pos_div_two; Assumption.
Split.
Split.
Apply leEq_Min.
Auto.
Apply leEq_transitive with x.
Inversion_clear Hx; Auto.
Step x[+](Zero::IR); Apply plus_resp_leEq_lft; Apply less_leEq; Apply pos_div_two; Assumption.
Apply Min_leEq_lft.
Apply Greater_imp_ap.
Apply shift_less_minus; Step x.
Stepr (Min b x[+](d[/]TwoNZ)); Apply less_Min.
Assumption.
Step x[+]Zero; Apply plus_resp_less_lft; Apply pos_div_two; Assumption.
Qed.

(* Tex_Prose
Derivative is unique.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_I_unique :
  (Derivative_I Hab' F G)->(Derivative_I Hab' F H)->(Feq I G H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF H2.
Elim H2; Intros incG H3.
Elim H1; Intros incF' H6.
Elim H6; Intros incH H4.
Clear H0 H2 H6.
Apply eq_imp_Feq; Auto.
Intros.
Apply cg_inv_unique_2.
Apply AbsIR_approach_zero; Intros.
Elim (H3 ? (pos_div_two ?? H2)).
Intros dg H6 H7.
Elim (H4 ? (pos_div_two ?? H2)).
Clear H4 H3; Intros dh H3 H4.
LetTac d:=(Min (Min dg dh) One).
Elim (Derivative_I_unique_lemma x H0 d).
Intros y Hy' Hy''.
Elim Hy''; Clear Hy''; Intros Hy'' Hy.
Apply mult_cancel_leEq with (AbsIR y[-]x).
Apply AbsIR_pos; Assumption.
EApply leEq_wdl.
2: Apply AbsIR_resp_mult.
LetTac Hxx:=(incF x H0).
LetTac Hyy:=(incF y Hy'').
Apply leEq_wdl with (AbsIR (((F y Hyy)[-](F x Hxx))[-](H x Hx')[*](y[-]x))[-](((F y Hyy)[-](F x Hxx))[-](G x Hx)[*](y[-]x))).
2: Apply un_op_wd_unfolded; Rational.
EApply leEq_transitive.
Apply triangle_IR_minus.
RStepr (e[/]TwoNZ)[*](AbsIR y[-]x)[+](e[/]TwoNZ)[*](AbsIR y[-]x).
Apply plus_resp_leEq_both; [Apply H4 | Apply H7]; Try Assumption; EApply leEq_transitive; Try Apply Hy'; Unfold d; EApply leEq_transitive.
Apply Min_leEq_lft.
Apply Min_leEq_rht.
Apply Min_leEq_lft.
Apply Min_leEq_lft.
Unfold d; Repeat Apply less_Min; [Assumption | Assumption | Apply pos_one].
Qed.

(* Tex_Prose
Finally, the set where we are considering the relation is included in the domain of both functions.
*)

(* Begin_Tex_Verb *)
Lemma derivative_imp_inc : (Derivative_I Hab' F G)->(included I P).
(* End_Tex_Verb *)
Intro.
Inversion_clear H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma derivative_imp_inc' : (Derivative_I Hab' F G)->(included I Q).
(* End_Tex_Verb *)
Intro.
Inversion_clear H0.
Inversion_clear H2; Assumption.
Qed.

(* Tex_Prose
Any function that is or has a derivative is continuous.
*)

Variable Hab'': a[<=]b.

(* Begin_Tex_Verb *)
Lemma deriv_imp_contin'_I : (Derivative_I Hab' F G)->(Continuous_I Hab'' G).
(* End_Tex_Verb *)
Intro derF.
Elim derF; Intros incF H0.
Elim H0; Intros incG derivFG.
Clear derF H0.
Split.
Included.
Intros e He.
Elim (derivFG ? (pos_div_two ?? He)); Intros d posd Hde; Clear derivFG.
Exists d; Auto; Intros.
LetTac Hx':=(incF ? H0).
LetTac Hy':=(incF ? H1).
Apply equal_less_leEq with a:=(Zero::IR) b:=(AbsIR y[-]x); Intros.
3: Apply AbsIR_nonneg.
Apply mult_cancel_leEq with (AbsIR y[-]x); Auto.
RStepr (e[/]TwoNZ)[*](AbsIR y[-]x)[+](e[/]TwoNZ)[*](AbsIR y[-]x).
EApply leEq_wdl.
2: Apply AbsIR_resp_mult.
Apply leEq_wdl with (AbsIR (((F y Hy')[-](F x Hx'))[-]((G x Hx)[*](y[-]x)))[+](((F x Hx')[-](F y Hy'))[-]((G y Hy)[*](x[-]y)))).
2: EApply eq_transitive_unfolded.
2: Apply AbsIR_inv.
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
Auto.
Apply leEq_wdr with (e[/]TwoNZ)[*](AbsIR x[-]y).
Apply Hde; Auto.
EApply leEq_wdl.
Apply H2.
Apply AbsIR_minus.
Apply mult_wd_rht; Apply AbsIR_minus.
Apply leEq_wdl with (Zero::IR).
Apply less_leEq; Auto.
Step (AbsIR Zero).
Apply AbsIR_wd.
Apply eq_symmetric_unfolded; Apply x_minus_x.
Apply pfwdef.
Apply cg_inv_unique_2.
Apply AbsIR_eq_zero.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
Apply H3.
Apply AbsIR_minus.
Qed.

(* Begin_Tex_Verb *)
Lemma deriv_imp_contin_I : (Derivative_I Hab' F G)->(Continuous_I Hab'' F).
(* End_Tex_Verb *)
Intro derF.
Elim derF; Intros incF H2; Elim H2; Clear H2; Intros incG deriv.
Split; Auto.
Intros e He.
Elim deriv with e; Auto.
Clear deriv; Intros d posd Hd.
LetTac contG:=(deriv_imp_contin'_I derF).
LetTac M:=(Norm_Funct contG).
LetTac D:=(Min d (Min One[/]TwoNZ e[/]?[//](mult_resp_ap_zero ??? (two_ap_zero IR) (max_one_ap_zero M)))).
Exists D.
Unfold D; Repeat Apply less_Min.
Auto.
Apply (pos_half IR).
Apply div_resp_pos; Auto.
Apply shift_less_mult' with (two_ap_zero IR).
Apply pos_two.
Step (Zero::IR).
EApply less_leEq_trans.
2: Apply rht_leEq_Max.
Apply pos_one.
Intros.
Apply leEq_wdl with (AbsIR (((F x Hx)[-](F y Hy))[-](G y (incG ? H1))[*](x[-]y))[+](G y (incG ? H1))[*](x[-]y)).
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR.
RStepr e[/]TwoNZ[+]e[/]TwoNZ.
Apply plus_resp_leEq_both.
Apply leEq_transitive with e[*](AbsIR x[-]y).
Apply Hd; Auto.
Apply leEq_transitive with D.
EApply leEq_wdl; [Apply H2 | Apply AbsIR_minus].
Unfold D; Apply Min_leEq_lft.
RStepr e[*](One[/]TwoNZ).
Apply mult_resp_leEq_lft.
Apply leEq_transitive with D; Auto.
Unfold D; EApply leEq_transitive; [Apply Min_leEq_rht | Apply Min_leEq_lft].
Apply less_leEq; Auto.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with (Max M One)[*](AbsIR x[-]y).
Apply mult_resp_leEq_rht.
2: Apply AbsIR_nonneg.
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Unfold M; Apply norm_bnd_AbsIR; Auto.
Apply shift_mult_leEq' with (max_one_ap_zero M).
EApply less_leEq_trans; [Apply pos_one | Apply rht_leEq_Max].
EApply leEq_wdr.
EApply leEq_transitive.
Apply H2.
Unfold D.
EApply leEq_transitive; Apply Min_leEq_rht.
Rational.
Qed.

End Basic_Properties.

(* Tex_Prose
If $G$ is the derivative of $F$ in a given interval, then $G$ is also the derivative of $F$ in any smaller interval.
*)

(* Begin_Tex_Verb *)
Lemma included_imp_deriv : (a,b,Hab,c,d,Hcd,F,F':?)
  (included (compact c d (less_leEq ??? Hcd))
            (compact a b (less_leEq ??? Hab)))->
  (Derivative_I Hab F F')->(Derivative_I Hcd F F').
(* End_Tex_Verb *)
Intros.
Elim H0; Clear H0; Intros incF H0.
Elim H0; Clear H0; Intros incF' H0.
Apply Derivative_I_char.
Apply included_trans with (Compact (less_leEq ??? Hab)); Auto.
Apply included_trans with (Compact (less_leEq ??? Hab)); Auto.
Intros e He; Elim (H0 e He); Intros e' He'.
Exists e'; Auto.
Qed.
