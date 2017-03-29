(* $Id: FTC.v,v 1.18 2003/03/13 12:06:18 lcf Exp $ *)

Require Export MoreIntegrals.
Require Export CalculusTheorems.
Require Export PFunct.

Opaque Min.

Section Indefinite_Integral.

(* Tex_Prose
\chapter{The FTC}

Finally we can prove the fundamental theorem of calculus and its most important corollaries---which are the main tools to formalize most of real analysis.

\section{Indefinite Integrals}

We define the indefinite integral of a function in a proper interval in the obvious way; we just need to state a first lemma so that the continuity proofs become unnecessary.

\begin{convention} Let \verb!I:interval!, \verb!F:PartIR! be continuous in \verb!I! and \verb!a! be a point in \verb!I!.
\end{convention}
*)

Variable I:interval.
Variable F:PartIR.

Hypothesis contF:(Continuous I F).

Variable a:IR.
Hypothesis Ha:(iprop I a).

(* Begin_Tex_Verb *)
Lemma prim_lemma : (x:IR)(iprop I x)->
  (Continuous_I (Min_leEq_Max a x) F).
(* End_Tex_Verb *)
Intros.
Elim contF; Intros incI contI.
Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Fprim_strext : (x,y,Hx,Hy:?)
  (((Integral (prim_lemma x Hx))[#](Integral (prim_lemma y Hy)))->
    (x[#]y)).
(* End_Tex_Verb *)
Intros.
Elim (Integral_strext' ????????? H).
Intro; ElimType False.
Generalize a0; Apply ap_irreflexive_unfolded.
Auto.
Qed.

(* Begin_Tex_Verb *)
Definition Fprim : PartIR.
(* End_Tex_Verb *)
Apply Build_PartFunct with pfpfun:=[x:IR][Hx:(iprop I x)](Integral (prim_lemma x Hx)).
Apply iprop_wd.
Exact Fprim_strext.
Defined.

End Indefinite_Integral.

(* Tex_Prose
\begin{notation}
{\tt\hypertarget{Operator_28}{(\{-S-\} contF)}} denotes \verb!(Fprim ?? contF)!.
\end{notation}
*)

Implicits Fprim [1 2].

Notation "{-S-} F" := (Fprim F).

Section FTC.

(* Tex_Prose
\section{The Fundamental Theorem of Calculus}

We can now prove our main theorem.  We begin by remarking that the primitive function is always continuous.

\begin{convention} Assume that \verb!J:interval!, \verb!F:PartIR! is continuous in \verb!J! and \verb!x0! is a point in \verb!J!.  Denote by \verb!G! the indefinite integral of \verb!F! from \verb!x0!.
\end{convention}
*)

Variable J:interval.
Variable F:PartIR.

Hypothesis contF:(Continuous J F).

Variable x0:IR.
Hypothesis Hx0:(iprop J x0).

Local G:=({-S-}contF x0 Hx0).

(* Begin_Tex_Verb *)
Lemma Continuous_prim : (Continuous J G).
(* End_Tex_Verb *)
Split.
Included.
Split.
Included.
Intros.
Simpl; Simpl in H.
Exists e[/]?[//](max_one_ap_zero (Norm_Funct (included_imp_Continuous ?? contF ??? H))).
Apply div_resp_pos.
Apply pos_max_one.
Assumption.
Intros.
Cut (included (Compact (Min_leEq_Max y x)) (Compact Hab)).
Intro Hinc.
Cut (Continuous_I (Min_leEq_Max y x) F); Intros.
Apply leEq_wdl with (AbsIR (Integral H4)).
EApply leEq_transitive.
Apply Integral_leEq_norm.
Apply leEq_transitive with (Max (Norm_Funct (included_imp_Continuous ?? contF ??? H)) One)[*](AbsIR x[-]y).
Apply mult_resp_leEq_rht.
Apply leEq_transitive with (Norm_Funct (included_imp_Continuous ?? contF ??? H)).
Apply leEq_Norm_Funct.
Intros.
Apply norm_bnd_AbsIR.
Apply Hinc; Auto.
Apply lft_leEq_Max.
Apply AbsIR_nonneg.
EApply shift_mult_leEq'.
Apply pos_max_one.
Apply H3.
Apply AbsIR_wd.
RStep ((Integral (prim_lemma J F contF x0 Hx0 y Hy))[+](Integral H4))[-](Integral (prim_lemma J F contF x0 Hx0 y Hy)).
Apply cg_minus_wd.
Apply eq_symmetric_unfolded; Apply Integral_plus_Integral with (Min3_leEq_Max3 x0 x y).
Apply included_imp_Continuous with J; Auto.
Apply included3_interval; Auto.
Apply Integral_wd.
Apply Feq_reflexive.
Apply included_trans with (iprop J); Included.
Apply included_imp_Continuous with J; Auto.
Included.
Included.
Qed.

(* Tex_Prose
The derivative of \verb!G! is simply \verb!F!.
*)

Hypothesis pJ:(proper J).

(* Begin_Tex_Verb *)
Theorem FTC1 : (Derivative J pJ G F).
(* End_Tex_Verb *)
Split; Included.
Split; Included.
Intros; Apply Derivative_I_char.
Included.
Inversion_clear contF.
Included.
Intros.
Red in contF.
Inversion_clear contF.
Elim (contin_prop ???? (H2 ??? H) e H0); Intros d H3 H4.
Exists d.
Assumption.
Intros.
Simpl.
Rename Hab into Hab'.
LetTac Hab:=(less_leEq ??? Hab').
Cut (included (Compact (Min_leEq_Max x y)) (Compact Hab)).
Intro Hinc.
Cut (Continuous_I (Min_leEq_Max x y) F).
2: Apply included_imp_Continuous with J; Auto.
Intro.
Apply leEq_wdl with (AbsIR (Integral H8)[-](Integral (Continuous_I_const ?? (Min_leEq_Max x y) (F x Hx')))).
Apply leEq_wdl with (AbsIR (Integral (Continuous_I_minus ????? H8 (Continuous_I_const ??? (F x Hx'))))).
EApply leEq_transitive.
Apply Integral_leEq_norm.
Apply mult_resp_leEq_rht.
2: Apply AbsIR_nonneg.
Apply leEq_Norm_Funct.
Intros z Hz Hz1.
Simpl.
Apply leEq_wdl with (AbsIR (F z (H1 z (H z (Hinc z Hz))))[-](F x Hx')).
2: Apply AbsIR_wd; Algebra.
Apply H4; Auto.
EApply leEq_transitive.
2: Apply H7.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply Abs_Max.
EApply leEq_wdr.
2: Apply AbsIR_eq_x; Apply shift_leEq_minus.
2: Step (Min x y); Apply Min_leEq_Max.
Apply compact_elements with (Min_leEq_Max x y); Auto.
Apply compact_Min_lft.
Apply AbsIR_wd; Apply Integral_minus.
Apply AbsIR_wd; Apply cg_minus_wd.
RStep ((Integral (prim_lemma ?? contF x0 Hx0 ? Hx))[+](Integral H8))[-](Integral (prim_lemma ?? contF x0 Hx0 ? Hx)).
Apply cg_minus_wd.
Apply eq_symmetric_unfolded; Apply Integral_plus_Integral with (Min3_leEq_Max3 x0 y x).
Apply included_imp_Continuous with J; Auto.
Apply included3_interval; Auto.
Apply Integral_wd; Apply Feq_reflexive; Apply included_trans with (iprop J); Try Apply included_interval; Auto.
Apply Integral_const.
Included.
Included.
Qed.

(* Tex_Prose
Any other function \verb!G0! with derivative \verb!F! must differ from \verb!G! by a constant.
*)

Variable G0:PartIR.
Hypothesis derG0:(Derivative J pJ G0 F).

(* Begin_Tex_Verb *)
Theorem FTC2 : {c:IR & (Feq (iprop J) G{-}G0 {-C-}c)}.
(* End_Tex_Verb *)
Apply FConst_prop with pJ.
Apply Derivative_wdr with F{-}F.
FEQ.
Apply Derivative_minus; Auto.
Apply FTC1.
Qed.

(* Tex_Prose
The following is another statement of the Fundamental Theorem of Calculus, often known as Barrow's rule.
*)

Local G0_inc := (Derivative_imp_inc ???? derG0).

(* Begin_Tex_Verb *)
Theorem Barrow : (a,b:IR)(iprop J a)->(iprop J b)->
  (H:(Continuous_I (Min_leEq_Max a b) F))(Ha,Hb:?)
  [Ha':=(G0_inc a Ha)][Hb':=(G0_inc b Hb)]
  (Integral H)[=](G0 b Hb')[-](G0 a Ha').
(* End_Tex_Verb *)
Intros.
Elim FTC2; Intros c Hc.
Inversion_clear Hc.
Inversion_clear H2.
(* Allow G0a to be G0 of a.
Allow G0b to be G0 of b. *)
ttb G0a G0 a; ttb G0b G0 b.
RStepr (G0b[+]c)[-](G0a[+]c).
(* Allow Ga to be G of a.*)
ttb Ga G a. 2: Simpl; Auto.
(* Allow Gb to be G of b.*)
ttb Gb G b. 2: Simpl; Auto.
Apply eq_transitive_unfolded with Gb[-]Ga.
Unfold Ga Gb G; Simpl.
Cut (x,y,z:IR)(z[=]x[+]y)->(y[=]z[-]x); Intros.
Apply H7.
Apply Integral_plus_Integral with (Min3_leEq_Max3 x0 b a).
Apply included_imp_Continuous with J.
Auto.
Apply included3_interval; Auto.
Apply eq_symmetric_unfolded.
RStepr (x[+]y)[-]x; Algebra.
Cut (x,y,z:IR)(x[-]y[=]z)->(x[=]y[+]z); Intros.
Opaque G.
Cut (x:IR)(iprop J x)->(Hx,Hx':?)(G x Hx)[-](G0 x Hx')[=]c; Intros.
Apply cg_minus_wd; Unfold Ga Gb G0a G0b; Apply H7; Auto.
Simpl in H3.
EApply eq_transitive_unfolded.
2: Apply H3 with Hx:=(Hx,Hx').
Algebra.
Auto.
Auto.
RStep y[+](x[-]y).
Algebra.
Qed.

End FTC.

Hints Resolve Continuous_prim : continuous.
Hints Resolve FTC1 : derivate.

Section Limit_of_Integral_Seq.

(* Tex_Prose
\section{Corollaries}

With these tools in our hand, we can prove several useful results.

\begin{convention} From this point onwards:
\begin{itemize}
\item \verb!J:interval!;
\item \verb!f:nat->PartIR! is a sequence of continuous functions (in \verb!J!);
\item \verb!F:PartIR! is continuous in \verb!J!.
\end{itemize}
\end{convention}

In the first place, if a sequence of continuous functions converges then the sequence of their primitives also converges, and the limit commutes with the indefinite integral.
*)

Variable J:interval.

Variable f:nat->PartIR.
Variable F:PartIR.

Hypothesis contf:(n:nat)(Continuous J (f n)).
Hypothesis contF:(Continuous J F).

Section Compact.

(* Tex_Prose
We need to prove this result first for compact intervals.

\begin{convention} Assume that \verb!a,b,x0:IR! with \verb!(f n)! and \verb!F! continuous in $[a,b]$, $x0\in[a,b]$; denote by \verb!(g n)! and \verb!G! the indefinite integrals respectively of \verb!(f n)! and \verb!F! with origin \verb!x0!.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Hypothesis contIf:(n:nat)(Continuous_I Hab (f n)).
Hypothesis contIF:(Continuous_I Hab F).
(* Begin_Tex_Verb *)
Hypothesis convF : (conv_fun_seq' a b Hab f F contIf contIF).
(* End_Tex_Verb *)

Variable x0:IR.
Hypothesis Hx0:(iprop J x0).
Hypothesis Hx0':(Compact Hab x0).

Local g:=[n:nat]({-S-}(contf n) x0 Hx0).
Local G:=({-S-}contF x0 Hx0).

(* Begin_Tex_Verb *)
Hypothesis contg:(n:nat)(Continuous_I Hab (g n)).
Hypothesis contG:(Continuous_I Hab G).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_lim_seq_integral :
  (conv_fun_seq' a b Hab g G contg contG).
(* End_Tex_Verb *)
Cut (conv_norm_fun_seq ????? contIf contIF); Intros.
2: Apply conv_fun_seq'_norm; Assumption.
Red; Intros.
Elim (Archimedes (AbsIR b[-]a)[/]?[//](pos_ap_zero ?? H0)); Intros k Hk.
Elim (H k); Intros N HN.
Exists N; Intros.
Cut (included (Compact (Min_leEq_Max x0 x)) (Compact Hab)); [Intro | Apply included2_compact; Auto].
Simpl.
Apply leEq_wdl with (AbsIR (Integral (Continuous_I_minus ????? 
  (prim_lemma ?? (contf n) x0 Hx0 ? (contin_imp_inc ???? (contg n) ? Hx)) 
  (prim_lemma ?? contF x0 Hx0 ? (contin_imp_inc ???? contG ? Hx))))).
2: Apply AbsIR_wd; Apply Integral_minus.
EApply leEq_transitive.
Apply Integral_leEq_norm.
Apply leEq_transitive with (one_div_succ k)[*](AbsIR b[-]a).
Apply mult_resp_leEq_both.
Apply positive_norm.
Apply AbsIR_nonneg.
EApply leEq_transitive.
2: Apply (HN n H1).
Apply leEq_Norm_Funct; Intros.
Apply norm_bnd_AbsIR.
Apply H2; Auto.
Apply compact_elements with Hab; Auto.
Unfold one_div_succ Snring.
RStep (AbsIR b[-]a)[/]?[//](nring_ap_zero ?? (sym_not_eq ??? (O_S k))).
Apply shift_div_leEq.
Apply pos_nring_S.
EApply shift_leEq_mult'.
Assumption.
Apply less_leEq; EApply leEq_less_trans.
Apply Hk.
Simpl.
Apply less_plusOne.
Qed.

End Compact.

(* Tex_Prose
And now we can generalize it step by step.
*)

(* Begin_Tex_Verb *)
Lemma limit_of_integral : (conv_fun_seq'_IR J f F contf contF)->
  (x,y,Hxy:?)(included (Compact Hxy) (iprop J))->(Hf,HF:?)
  (Cauchy_Lim_prop2
    [n:nat](integral x y Hxy (f n) (Hf n))
    (integral x y Hxy F HF)).
(* End_Tex_Verb *)
Intros.
Cut (iprop J x); [Intro Hx | Apply H0; Apply compact_inc_lft].
Cut (iprop J y); [Intro Hy | Apply H0; Apply compact_inc_rht].
LetTac g:=[n:nat]({-S-}(contf n) x Hx).
LetTac G:=({-S-}contF x Hx).
LetTac Hxg:=[n:nat]Hy.
Apply Lim_wd with (Part G y Hy).
Simpl; Apply Integral_integral.
Apply Cauchy_Lim_prop2_wd with [n:nat](Part (g n) y (Hxg n)).
2: Intro; Simpl; Apply Integral_integral.
Cut (n:nat)(Continuous_I Hxy (g n)); Intros.
Cut (Continuous_I Hxy G); Intros.
Apply fun_conv_imp_seq_conv with contf:=H1 contF:=H2.
LetTac H4:=[n:nat](included_imp_Continuous ?? (contf n) ??? H0).
LetTac H5:=(included_imp_Continuous ?? contF ??? H0).
Unfold g G.
Apply fun_lim_seq_integral with H4 H5.
Unfold H4 H5.
Apply H; Auto.
Apply compact_inc_lft.
Apply compact_inc_rht.
Unfold G; Apply included_imp_Continuous with J; Contin.
Unfold g; Apply included_imp_Continuous with J; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma limit_of_Integral : (conv_fun_seq'_IR J f F contf contF)->
  (x,y:IR)(included (Compact (Min_leEq_Max x y)) (iprop J))->
  (Hxy,Hf,HF:?)(Cauchy_Lim_prop2
    [n:nat](!Integral x y Hxy (f n) (Hf n))
    (!Integral x y Hxy F HF)).
(* End_Tex_Verb *)
Intros convF x y.
LetTac x0:=(Min x y).
Intros.
Cut (iprop J x0).
2: Apply H; Apply compact_inc_lft.
Intro Hx0.
Cut (Compact Hxy x0).
2: Apply compact_inc_lft.
Intro Hx0'.
LetTac g:=[n:nat]({-S-}(contf n) x0 Hx0).
LetTac G:=({-S-}contF x0 Hx0).
Unfold Integral; Fold x0.
Apply (Cauchy_Lim_minus [n:nat](integral ???? (Integral_inc2 ???? (Hf n))) [n:nat](integral ???? (Integral_inc1 ???? (Hf n)))); Fold x0.
Apply limit_of_integral with Hf:=[n:nat](Integral_inc2 ?? Hxy ? (Hf n)); Auto.
Apply included_trans with (Compact (Min_leEq_Max x y)); Included.
Apply included_compact.
Apply compact_inc_lft.
Apply compact_Min_rht.
Apply limit_of_integral with Hf:=[n:nat](Integral_inc1 ?? Hxy ? (Hf n)); Auto.
Apply included_trans with (Compact (Min_leEq_Max x y)); Auto.
Apply included_compact.
Apply compact_inc_lft.
Apply compact_Min_lft.
Qed.

Section General.

(* Tex_Prose
Finally, with \verb!x0,g,G! as before,
*)

(* Begin_Tex_Verb *)
Hypothesis convF : (conv_fun_seq'_IR J f F contf contF).
(* End_Tex_Verb *)

Variable x0:IR.
Hypothesis Hx0:(iprop J x0).

Local g:=[n:nat]({-S-}(contf n) x0 Hx0).
Local G:=({-S-}contF x0 Hx0).

Hypothesis contg:(n:nat)(Continuous J (g n)).
Hypothesis contG:(Continuous J G).

(* Begin_Tex_Verb *)
Lemma fun_lim_seq_integral_IR :
  (conv_fun_seq'_IR J g G contg contG).
(* End_Tex_Verb *)
Red; Intros.
Unfold g G.
Cut (iprop J a); Intros.
LetTac h:=[n:nat]{-C-}(Integral (prim_lemma ?? (contf n) x0 Hx0 a H)).
LetTac g':=[n:nat](h n){+}({-S-}(contf n) a H).
LetTac G':={-C-}(Integral (prim_lemma ?? contF x0 Hx0 a H)){+}({-S-}contF a H).
Cut (n:nat)(Continuous_I Hab (h n)); Intros.
2: Unfold h; Contin.
Cut (n:nat)(Continuous_I Hab ({-S-}(contf n) a H)); Intros.
Cut (n:nat)(Continuous_I Hab (g' n)); Intros.
2: Unfold g'; Contin.
Cut (Continuous_I Hab ({-S-}contF a H)); Intros.
Cut (Continuous_I Hab G'); Intros.
2: Unfold G'; Contin.
Apply conv_fun_seq'_wdl with g' H2 (included_imp_Continuous ?? contG ??? Hinc).
Intro; FEQ.
Simpl.
Apply eq_symmetric_unfolded; Apply Integral_plus_Integral with (Min3_leEq_Max3 x0 x a).
Apply included_imp_Continuous with J; Contin.
Apply conv_fun_seq'_wdr with H2 G' H4.
FEQ.
Simpl.
Apply eq_symmetric_unfolded; Apply Integral_plus_Integral with (Min3_leEq_Max3 x0 x a).
Apply included_imp_Continuous with J; Contin.
Unfold g' G'.
Apply conv_fun_seq'_wdl with f:=g' contf:=[n:nat](Continuous_I_plus ????? (H0 n) (H1 n)) contF:=H4.
Unfold g' in H2.
Intro; Apply Feq_reflexive; Included.
Unfold g' G'.
Apply (fun_Lim_seq_plus' ?? Hab h [n:nat]({-S-}(contf n) a H) H0 H1 ?? 
  (Continuous_I_const ??? (Integral (prim_lemma ?? contF x0 Hx0 a H))) H3).
Unfold h.
Apply seq_conv_imp_fun_conv with x:=[n:nat](Integral (prim_lemma ?? (contf n) x0 Hx0 a H)).
Apply limit_of_Integral with Hf:=[n:nat](prim_lemma ?? (contf n) x0 Hx0 a H); Auto.
Included.
Apply fun_lim_seq_integral with [n:nat](included_imp_Continuous ?? (contf n) ??? Hinc) (included_imp_Continuous ?? contF ??? Hinc).
Apply convF; Auto.
Apply compact_inc_lft.
Apply included_imp_Continuous with J; Contin.
Apply included_imp_Continuous with J; Contin.
Apply Hinc; Apply compact_inc_lft.
Qed.

End General.

End Limit_of_Integral_Seq.

Section Limit_of_Derivative_Seq.

(* Tex_Prose
Similar results hold for the sequence of derivatives of a converging sequence; this time the proof is easier, as we can do it directly for any kind of interval.

\begin{convention} Let \verb!g! be the sequence of derivatives of \verb!f! and \verb!G! be the derivative of \verb!F!.
\end{convention}
*)

Variable J:interval.
Hypothesis pJ:(proper J).

Variables f,g:nat->PartIR.
Variables F,G:PartIR.

Hypothesis contf:(n:nat)(Continuous J (f n)).
Hypothesis contF:(Continuous J F).
Hypothesis convF : (conv_fun_seq'_IR J f F contf contF).

Hypothesis contg:(n:nat)(Continuous J (g n)).
Hypothesis contG:(Continuous J G).
Hypothesis convG : (conv_fun_seq'_IR J g G contg contG).

Hypothesis derf:(n:nat)(Derivative J pJ (f n) (g n)).

(* Begin_Tex_Verb *)
Lemma fun_lim_seq_derivative : (Derivative J pJ F G).
(* End_Tex_Verb *)
Elim (nonvoid_point ? (proper_nonvoid ? pJ)); Intros a Ha.
LetTac h:=[n:nat]({-S-}(contg n) a Ha).
LetTac H:=({-S-}contG a Ha).
Cut (Derivative J pJ H G).
2: Unfold H; Apply FTC1.
Intro.
Cut (n:nat)(Derivative J pJ (h n) (g n)).
2: Intro; Unfold h; Apply FTC1.
Intro.
Cut (conv_fun_seq'_IR J ?? [n:nat](Derivative_imp_Continuous ???? (H1 n)) (Derivative_imp_Continuous ???? H0)).
2: Unfold h H.
2: EApply fun_lim_seq_integral_IR with contf:=contg; Auto.
Intro.
Cut {c:IR & (Feq (iprop J) F{-}H {-C-}c)}.
Intro.
Elim H3; Clear H3; Intros c Hc.
Apply Derivative_wdl with H{+}{-C-}c.
Apply Feq_transitive with H{+}(F{-}H).
Apply Feq_plus.
Apply Feq_reflexive; Included.
Apply Feq_symmetric; Assumption.
Clear Hc H2 H1; ClearBody H.
FEQ.
Apply Derivative_wdr with G{+}{-C-}Zero.
FEQ.
Apply Derivative_plus; Auto.
Apply Derivative_const.
Cut (n:nat){c:IR & (Feq (iprop J) (f n){-}(h n) {-C-}c)}; Intros.
2: Apply FConst_prop with pJ.
2: Cut (Derivative J pJ (f n) (g n)); [Intro | Auto].
2: Cut (Derivative J pJ (h n) (g n)); [Intro | Auto].
2: Apply Derivative_wdr with (g n){-}(g n).
2: FEQ.
2: Apply Derivative_minus; Auto.
Cut (n:nat)(Continuous J (f n){-}(h n)); [Intro contw | Unfold h; Contin].
Cut (Continuous J F{-}H); [Intro contW | Unfold H; Contin].
Apply fun_const_Lim with [n:nat](f n){-}(h n) contw contW.
Auto.
EApply fun_Lim_seq_minus'_IR.
Apply convF.
Apply H2.
Assumption.
Qed.

End Limit_of_Derivative_Seq.

Section Derivative_Series.

(* Tex_Prose
As a very important case of this result, we get a rule for deriving series.
*)

Variable J:interval.
Hypothesis pJ:(proper J).
Variables f,g:nat->PartIR.

(* Begin_Tex_Verb *)
Hypothesis convF:(fun_series_convergent_IR J f).
Hypothesis convG:(fun_series_convergent_IR J g).
(* End_Tex_Verb *)
Hypothesis derF:(n:nat)(Derivative J pJ (f n) (g n)).

(* Begin_Tex_Verb *)
Lemma Derivative_FSeries :
  (Derivative J pJ (FSeries_Sum convF) (FSeries_Sum convG)).
(* End_Tex_Verb *)
Apply fun_lim_seq_derivative with
  f:=[n:nat](FSum0 n f)
  contf:=(Continuous_Sum0 ?? (convergent_imp_Continuous ?? convF))
  contF:=(Continuous_FSeries_Sum ?? convF)
  g:=[n:nat](FSum0 n g)
  contg:=(Continuous_Sum0 ?? (convergent_imp_Continuous ?? convG))
  contG:=(Continuous_FSeries_Sum ?? convG).
3: Deriv.
Apply FSeries_conv.
Apply FSeries_conv.
Qed.

End Derivative_Series.
