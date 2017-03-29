(* $Id: Composition.v,v 1.20 2003/03/13 12:06:17 lcf Exp $ *)

Require Export MoreFunctions.

Section Maps_into_Compacts.

Section Part_Funct.

(* Tex_Prose
\chapter{Composition}

Preservation results for functional composition are treated in this separate file.  We start by defining some auxiliary predicates, and then prove the preservation of continuity through composition and the chain rule for differentiation, both for compact and arbitrary intervals.

\begin{convention} Throughout this section:
\begin{itemize}
\item \verb!a,b:IR! and \verb!I! will denote $[a,b]$;
\item \verb!c,d:IR! and \verb!J! will denote $[a,b]$;
\item \verb!F,F',G,G'! will be partial functions.
\end{itemize}
\end{convention}

\section{Maps into Compacts}

Both continuity and differentiability proofs require extra hypothesis on the functions involved---namely, that every compact interval is mapped into another compact interval.  We define this concept for partial functions, and prove some trivial results.
*)

Variables F,G:PartIR.
Variables a,b:IR.
Hypothesis Hab:a[<=]b.

Variables c,d:IR.
Hypothesis Hcd:c[<=]d.
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Hypothesis Hf:(included (Compact Hab) (Pred F)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition maps_into_compacts := 
  (c[<]d)*((included (Compact Hcd) (Pred G))*
  (x:IR)(Hx:(Pred F x))(I x)->(Compact Hcd (F x Hx))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Hypothesis maps:maps_into_compacts.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma maps_lemma' :
   (x:IR)(Hx:(Pred F x))(I x)->(Compact Hcd (F x Hx)).
(* End_Tex_Verb *)
Inversion_clear maps.
Inversion_clear H0.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma maps_lemma :
  (x:IR)(I x)->(Hx:(Pred F x))(Compact Hcd (F x Hx)).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply maps_lemma'.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma maps_lemma_less : c[<]d.
(* End_Tex_Verb *)
Inversion_clear maps; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma maps_lemma_inc : (included (Compact Hcd) (Pred G)).
(* End_Tex_Verb *)
Inversion_clear maps.
Inversion_clear H0.
Assumption.
Qed.

End Part_Funct.

End Maps_into_Compacts.

Section Mapping.

(* Tex_Prose
As was the case for division of partial functions, this condition completely characterizes the domain of the composite function.
*)

Variables F,G:PartIR.
Variables a,b:IR.
Hypothesis Hab:a[<=]b.

Variables c,d:IR.
Hypothesis Hcd:c[<=]d.

(* Begin_Tex_Verb *)
Hypothesis Hf:(included (Compact Hab) (Pred F)).
Hypothesis Hg:(included (Compact Hcd) (Pred G)).
Hypothesis maps:(maps_into_compacts F G a b Hab c d Hcd).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma included_comp : (included (Compact Hab) (Pred G{o}F)).
(* End_Tex_Verb *)
Red.
Intros.
Simpl.
Exists (Hf x H).
Apply Hg.
Apply maps_lemma' with G a b Hab; Assumption.
Qed.

End Mapping.

Section Interval_Continuity.

(* Tex_Prose
\section{Continuity}

We now prove that the composition of two continuous partial functions is continuous.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables c,d:IR.
Hypothesis Hcd:c[<=]d.

Variables F,G:PartIR.

(* Begin_Tex_Verb *)
Hypothesis contF:(Continuous_I Hab F).
Hypothesis contG:(Continuous_I Hcd G).
Hypothesis Hmap:(maps_into_compacts F G a b Hab c d Hcd).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Continuous_I_comp : (Continuous_I Hab G{o}F).
(* End_Tex_Verb *)
Red.
Elim contF; Intros incF contF'.
Elim contG; Intros incG contG'.
Split.
Exact (included_comp F G a b Hab c d Hcd incF incG Hmap).
Intros.
Elim (contG' e H).
Intros dh H0 H1.
Elim (contF' dh H0).
Intros df H2 H3.
Exists df.
Assumption.
Intros.
Simpl.
Cut (x:IR)(Compact Hab x)->(Hx:?)(Compact Hcd (F x Hx)); Intros.
Apply leEq_wdl with (AbsIR (G ? (incG ? (H7 x H4 (incF x H4))))[-](G ? (incG ? (H7 y H5 (incF y H5))))).
Apply H1; Simpl.
Apply H7; Assumption.
Apply H7; Assumption.
Apply H3; Assumption.
Apply AbsIR_wd; Rational.
Apply maps_lemma with G a b Hab; Simpl; Assumption.
Qed.

End Interval_Continuity.

Section Derivative.

(* Tex_Prose
\section{Derivative}

We now work with the derivative relation and prove the chain rule for partial functions.
*)

Variables F,F',G,G':PartIR.

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Variables c,d:IR.
Hypothesis Hcd':c[<]d.

Local Hab:=(less_leEq ??? Hab').
Local Hcd:=(less_leEq ??? Hcd').
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Hypothesis derF:(Derivative_I Hab' F F').
Hypothesis derG:(Derivative_I Hcd' G G').
Hypothesis Hmap:(maps_into_compacts F G a b Hab c d Hcd).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma included_comp' : (included (Compact Hab) (Pred G'{o}F)).
(* End_Tex_Verb *)
Red.
Intros.
Simpl.
Exists (derivative_imp_inc ????? derF x H).
Apply (derivative_imp_inc' ????? derG).
Apply maps_lemma' with G a b Hab; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma maps':(maps_into_compacts F G' a b Hab c d Hcd).
(* End_Tex_Verb *)
Inversion_clear Hmap; Inversion_clear H0.
Split.
Assumption.
Split.
Unfold Hcd; Apply derivative_imp_inc' with G; Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_comp :
  (Derivative_I Hab' G{o}F (G'{o}F){*}F').
(* End_Tex_Verb *)
Elim derF; Intros incF H1.
Elim H1; Intros incF' H2.
Elim derG; Intros incG H4.
Elim H4; Intros incG' H5.
Clear H1 H4.
Apply Derivative_I_char.
Exact (included_comp ???????? incF incG Hmap).
Exact (included_FMult ??? (included_comp ???????? incF incG' maps') incF').
Intros e He.
LetTac contF' := (deriv_imp_contin'_I ????? Hab derF).
LetTac nF':=(Norm_Funct contF').
Cut Zero[<]One[+]nF'; Intros.
Cut (One[+]nF')[#]Zero.
Intro HnF'.
2: Apply Greater_imp_ap; Assumption.
LetTac alpha:=(One[/]?[//]HnF')[*](e[/]TwoNZ).
LetTac contG' := (deriv_imp_contin'_I ????? Hcd derG).
LetTac nH':=(Norm_Funct contG').
Cut Zero[<]alpha.
Intro Halpha.
Cut Zero[<]alpha[+]nH'; Intros.
Cut (alpha[+]nH')[#]Zero.
Intro HnH'.
2: Apply Greater_imp_ap; Assumption.
LetTac beta:=(One[/]?[//]HnH')[*](e[/]TwoNZ).
Cut (Zero[<]beta).
Intro Hbeta.
Elim (H2 ? Hbeta).
Intros df H1 H3.
Elim (H5 ? Halpha).
Intros dg H4 H6.
Elim (contin_prop ???? (deriv_imp_contin_I ????? Hab derF) ? H4).
Intros dc H7 H8.
Exists (Min dc df).
Apply less_Min; Assumption.
Intros.
Simpl.
LetTac fx:=(F x (ProjS1 Hx)).
LetTac fy:=(F y (ProjS1 Hy)).
LetTac gfx:=(G fx (ProjS2 Hx)).
LetTac gfy:=(G fy (ProjS2 Hy)).
LetTac fx':=(F' x (ProjIR2 Hx')).
LetTac gfx':=(G' (F x (ProjS1 (ProjIR1 Hx'))) (ProjS2 (ProjIR1 Hx'))).
Simpl in fx' gfx'; Fold fx' gfx'.
Apply leEq_wdl with (AbsIR ((gfy[-]gfx)[-]gfx'[*](fy[-]fx))[+]gfx'[*]((fy[-]fx)[-]fx'[*](y[-]x))).
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR.
Apply leEq_transitive with 
  (alpha[*]nF'[*](AbsIR y[-]x)[+]alpha[*](AbsIR (fy[-]fx)[-]fx'[*](y[-]x)))[+](nH'[*](AbsIR (fy[-]fx)[-]fx'[*](y[-]x))).
Apply plus_resp_leEq_both.
Apply leEq_transitive with alpha[*](AbsIR fy[-]fx).
Unfold gfx'.
Cut (Pred G' fx); Intros.
Apply leEq_wdl with (AbsIR (gfy[-]gfx)[-](G' fx H12)[*](fy[-]fx)).
Unfold gfy gfx; Apply H6; Unfold fx fy.
Apply maps_lemma with G a b Hab; Assumption.
Apply maps_lemma with G a b Hab; Assumption.
Apply H8; Try Assumption.
EApply leEq_transitive.
Apply H11.
Apply Min_leEq_lft.
Apply AbsIR_wd; Unfold fx fy gfx gfy; Rational.
Apply (pfprwd ? G' ? fx (ProjS2 (ProjIR1 Hx'))).
Unfold fx; Rational.
RStepr alpha[*](nF'[*](AbsIR y[-]x)[+](AbsIR (fy[-]fx)[-]fx'[*](y[-]x))).
Apply mult_resp_leEq_lft.
2: Apply less_leEq; Assumption.
Apply leEq_wdl with (AbsIR fx'[*](y[-]x)[+]((fy[-]fx)[-]fx'[*](y[-]x))).
2: Apply un_op_wd_unfolded; Rational.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_rht.
2: Apply AbsIR_nonneg.
Unfold fx' nF' I; Apply norm_bnd_AbsIR; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_rht.
2: Apply AbsIR_nonneg.
Unfold gfx' nH'; Apply norm_bnd_AbsIR; Apply maps_lemma with G a b Hab; Assumption.
RStep alpha[*]nF'[*](AbsIR y[-]x)[+](alpha[+]nH')[*](AbsIR (fy[-]fx)[-]fx'[*](y[-]x)).
RStepr e[/]TwoNZ[*](ABSIR y[-]x)[+]e[/]TwoNZ[*](ABSIR y[-]x).
Apply plus_resp_leEq_both.
Apply mult_resp_leEq_rht.
2: Apply AbsIR_nonneg.
Unfold alpha.
RStep nF'[/]?[//]HnF'[*](e[/]TwoNZ).
Stepr One[*](e[/]TwoNZ).
Apply mult_resp_leEq_rht.
2: Apply less_leEq; Apply pos_div_two; Assumption.
Apply shift_div_leEq'.
Apply leEq_less_trans with nF'.
Unfold nF'; Apply positive_norm.
Stepr nF'[+]One; Apply less_plusOne.
Apply less_leEq; RStepr nF'[+]One; Apply less_plusOne.
Apply shift_mult_leEq' with HnH'.
Assumption.
Apply leEq_wdr with beta[*](ABSIR y[-]x).
2: Unfold beta; Rational.
Unfold fx fy fx'; Apply H3; Try Assumption.
EApply leEq_transitive.
Apply H11.
Apply Min_leEq_rht.
Unfold beta.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive.
Apply recip_resp_pos; Assumption.
Apply pos_div_two; Assumption.
Apply leEq_less_trans with nH'.
Unfold nH'; Apply positive_norm.
Step Zero[+]nH'; Apply plus_resp_less_rht; Assumption.
Unfold alpha.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive.
Apply recip_resp_pos; Assumption.
Apply pos_div_two; Assumption.
Apply leEq_less_trans with nF'.
Unfold nF'; Apply positive_norm.
Stepr nF'[+]One; Apply less_plusOne.
Qed.

(* Tex_Prose
The next lemma will be useful when we move on to differentiability.
*)

(* Begin_Tex_Verb *)
Lemma Diffble_I_comp_aux : (Diffble_I Hab' G{o}F).
(* End_Tex_Verb *)
Elim derF; Intros incF H1.
Elim H1; Intros incF' H2.
Elim derG; Intros incG H4.
Elim H4; Intros incG' H5.
Clear H1 H4.
Exists (IntPartIR (included_FMult ??? (included_comp ???????? incF incG' maps') incF')).
EApply Derivative_I_wdr.
2: Apply Derivative_I_comp.
FEQ.
Exact (included_FMult ??? (included_comp ???????? incF incG' maps') incF').
Qed.

End Derivative.

Section Differentiability.

(* Tex_Prose
\section{Differentiability}

Finally, we move on to differentiability.
*)

Variables F,G:PartIR.

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Variables c,d:IR.
Hypothesis Hcd':c[<]d.

Local Hab:=(less_leEq ??? Hab').
Local Hcd:=(less_leEq ??? Hcd').
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Hypothesis diffF:(Diffble_I Hab' F).
Hypothesis diffG:(Diffble_I Hcd' G).
Hypothesis Hmap:(maps_into_compacts F G a b Hab c d Hcd).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Diffble_I_comp : (Diffble_I Hab' G{o}F).
(* End_Tex_Verb *)
Elim diffF; Intros f' derF.
Elim diffG; Intros g' derG.
Apply Diffble_I_comp_aux with (PartInt f') (PartInt g') c d Hcd'; Auto.
Qed.

End Differentiability.

Section Generalized_Intervals.

(* Tex_Prose
\section{Generalizations}

We now generalize this results to arbitrary intervals.  We begin by generalizing the notion of mapping compacts into compacts.

\begin{convention} We assume \verb!I,J! to be proper intervals.
\end{convention}
*)

Variables I,J:interval.
Hypothesis pI:(proper I).
Hypothesis pJ:(proper J).

(* Begin_Tex_Verb *)
Definition maps_compacts_into [F:PartIR] := (a,b,Hab:?)
  (included (compact a b Hab) (iprop I))->{c:IR & {d:IR & {Hcd:? & 
    (included (compact c d (less_leEq ??? Hcd)) (iprop J))*
  ((x:IR)(Hx:?)(Compact Hab x)->
    (Compact (less_leEq ??? Hcd) (F x Hx)))}}}.
(* End_Tex_Verb *)

(* Tex_Prose
Now everything comes naturally:
*)

(* Begin_Tex_Verb *)
Lemma comp_inc_lemma : (F:?)(maps_compacts_into F)->
  (x:IR)(Hx:?)(iprop I x)->(iprop J (F x Hx)).
(* End_Tex_Verb *)
Intros.
Cut (included (Compact (leEq_reflexive ? x)) (iprop I)); Intros.
Elim (H ??? H1); Intros c Hc.
Elim Hc; Clear Hc; Intros d Hd.
Elim Hd; Clear Hd; Intros Hcd Hmap'.
Inversion_clear Hmap'.
Apply H2; Apply H3; Auto.
Split; Apply leEq_reflexive.
Red; Intros.
Inversion_clear H1.
Apply iprop_wd with x; Auto.
Apply leEq_imp_eq; Auto.
Qed.

Variables F,F',G,G':PartIR.
(* Begin_Tex_Verb *)
Hypothesis Hmap:(maps_compacts_into F).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Continuous_comp : (Continuous I F)->(Continuous J G)->
  (Continuous I G{o}F).
(* End_Tex_Verb *)
Intros.
Elim H; Clear H; Intros incF contF.
Elim H0; Clear H0; Intros incG contG.
Split.
Red; Intros.
Exists (incF ? H).
Apply incG.
Apply comp_inc_lemma; Auto.
Intros.
Elim (Hmap ?? Hab H); Clear Hmap; Intros c Hc.
Elim Hc; Clear Hc; Intros d Hd.
Elim Hd; Clear Hd; Intros Hcd Hmap'.
Inversion_clear Hmap'.
Apply Continuous_I_comp with c d (less_leEq ??? Hcd); Auto.
Red; Intros.
Split; Auto.
Split; Auto.
Included.
Qed.

(* Begin_Tex_Verb *)
Hypothesis Hmap':(maps_compacts_into F').
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Derivative_comp :
  (Derivative I pI F F')->(Derivative J pJ G G')->
  (Derivative I pI G{o}F (G'{o}F){*}F').
(* End_Tex_Verb *)
Intros.
Elim H; Clear H; Intros incF H'.
Elim H'; Clear H'; Intros incF' derF.
Elim H0; Clear H0; Intros incG H'.
Elim H'; Clear H'; Intros incG' derG.
Split.
Simpl; Red; Intros; Exists (incF ? H).
Apply incG; Apply comp_inc_lemma; Auto.
Split.
Apply included_FMult.
Simpl; Red; Intros; Exists (incF ? H).
Apply incG'; Apply comp_inc_lemma; Auto.
Included.
Intros.
Elim (Hmap ?? (less_leEq ??? Hab) H); Clear Hmap; Intros c Hc.
Elim Hc; Clear Hc; Intros d Hd.
Elim Hd; Clear Hd; Intros Hcd Hmap2.
Inversion_clear Hmap2.
Apply Derivative_I_comp with c d Hcd; Auto.
Red; Intros.
Split; Auto.
Split; Auto.
Included.
Qed.

End Generalized_Intervals.

Section Corollaries.

(* Tex_Prose
Finally, some criteria to prove that a function with a specific domain maps compacts into compacts:
*)

(* Begin_Tex_Verb *)
Definition positive_fun [P:IR->CProp][F:PartIR] :=
  (included P (Pred F))*
  ({c:IR & (Zero[<]c) | (y:IR)(P y)->(Hy:?)(c[<=](F y Hy))}).

Definition negative_fun [P:IR->CProp][F:PartIR] :=
  (included P (Pred F))*
  ({c:IR & (c[<]Zero) | (y:IR)(P y)->(Hy:?)((F y Hy)[<=]c)}).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma positive_imp_maps_compacts_into : (J,F:?)
  (positive_fun (iprop J) F)->(Continuous J F)->
  (maps_compacts_into J (openl Zero) F).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim H; Intros incF H2.
Elim H2; Clear H H2 incF; Intros MinF H H2.
LetTac MaxF:=(Norm_Funct (included_imp_Continuous ?? H0 ??? H1))[+]One.
Cut (MinF[<]MaxF); Intros.
Exists MinF; Exists MaxF; Exists H3.
Split.
EApply included_trans.
Apply compact_map2 with Hab':=(Min_leEq_Max MinF MaxF).
Apply included_interval; Simpl.
Auto.
Unfold MaxF; EApply leEq_less_trans.
2: Apply less_plusOne.
Apply positive_norm.
Intros; Split.
Auto.
Unfold MaxF; EApply leEq_transitive.
2: Apply less_leEq; Apply less_plusOne.
EApply leEq_transitive.
Apply leEq_AbsIR.
Apply norm_bnd_AbsIR; Auto.
Unfold MaxF; EApply leEq_less_trans.
2: Apply less_plusOne.
Apply leEq_transitive with (F a (Continuous_imp_inc ?? H0 ? (H1 a (compact_inc_lft ?? Hab)))).
Apply H2; Auto.
Apply H1; Apply compact_inc_lft.
EApply leEq_transitive.
Apply leEq_AbsIR.
Apply norm_bnd_AbsIR; Apply compact_inc_lft.
Qed.

(* Begin_Tex_Verb *)
Lemma negative_imp_maps_compacts_into : (J,F:?)
  (negative_fun (iprop J) F)->(Continuous J F)->
  (maps_compacts_into J (openr Zero) F).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim H; Intros incF H2.
Elim H2; Clear H H2 incF; Intros MaxF H H2.
LetTac MinF:=[--](Norm_Funct (included_imp_Continuous ?? H0 ??? H1))[-]One.
Cut (MinF[<]MaxF); Intros.
Exists MinF; Exists MaxF; Exists H3.
Split.
EApply included_trans.
Apply compact_map2 with Hab':=(Min_leEq_Max MinF MaxF).
Apply included_interval; Simpl.
Unfold MinF; EApply less_leEq_trans.
Apply minusOne_less.
Stepr [--](Zero::IR); Apply inv_resp_leEq; Apply positive_norm.
Auto.
Intros; Split.
Unfold MinF; EApply leEq_transitive.
Apply less_leEq; Apply minusOne_less.
Stepr [--][--](pfpfun ? ? Hx); Apply inv_resp_leEq.
EApply leEq_transitive.
Apply inv_leEq_AbsIR.
Apply norm_bnd_AbsIR; Auto.
Auto.
Unfold MinF; EApply less_leEq_trans.
Apply minusOne_less.
Apply leEq_transitive with (F a (Continuous_imp_inc ?? H0 ? (H1 a (compact_inc_lft ?? Hab)))).
2: Apply H2; Auto.
2: Apply H1; Apply compact_inc_lft.
Stepr [--][--](pfpfun ? ? (Continuous_imp_inc ?? H0 ? (H1 ? (compact_inc_lft ?? Hab)))); Apply inv_resp_leEq.
EApply leEq_transitive.
Apply inv_leEq_AbsIR.
Apply norm_bnd_AbsIR; Apply compact_inc_lft.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_imp_maps_compacts_into : (J,F:?)
  (Continuous J F)->(maps_compacts_into J realline F).
(* End_Tex_Verb *)
Intros.
Red; Intros.
LetTac ModF:=(Norm_Funct (included_imp_Continuous ?? H ??? H0)).
Cut [--]ModF[<]ModF[+]One; Intros.
Exists [--]ModF; Exists ModF[+]One; Exists H1; Split.
Repeat Split.
Intros; Unfold ModF; Split.
Stepr [--][--](pfpfun ? ? Hx); Apply inv_resp_leEq.
EApply leEq_transitive; [Apply inv_leEq_AbsIR | Apply norm_bnd_AbsIR]; Auto.
EApply leEq_transitive.
2: Apply less_leEq; Apply less_plusOne.
EApply leEq_transitive; [Apply leEq_AbsIR | Apply norm_bnd_AbsIR]; Auto.
Unfold ModF.
EApply leEq_less_trans; [Apply leEq_transitive with (Zero::IR) | Apply less_plusOne].
Stepr [--](Zero::IR); Apply inv_resp_leEq; Apply positive_norm.
Apply positive_norm.
Qed.

(* Tex_Prose
As a corollary, we get the generalization of differentiability property.
*)

(* Begin_Tex_Verb *)
Lemma Diffble_comp : (I,J,pI,pJ,F,G:?)(maps_compacts_into I J F)->(Diffble I pI F)->(Diffble J pJ G)->(Diffble I pI G{o}F).
(* End_Tex_Verb *)
Intros.
Apply Derivative_imp_Diffble with ((Deriv ??? H1){o}F){*}(Deriv ??? H0).
Apply Derivative_comp with J pJ; Auto; Apply Deriv_lemma.
Qed.

End Corollaries.

Hints Immediate included_comp : included.
Hints Immediate Continuous_I_comp Continuous_comp : continuous.
