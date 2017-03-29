(* $Id: MoreFunctions.v,v 1.12 2003/03/13 12:06:20 lcf Exp $ *)

Require Export MoreIntervals.

Opaque Min Max.

Section Basic_Results.

(* Tex_Prose
\chapter{More about Functions}

Here we state all the main results about properties of functions that we already proved for compact intervals in the more general setting of arbitrary intervals.

\begin{convention} Let \verb!I:interval! and \verb!F,F',G,G'! be partial functions.
\end{convention}

\section{Continuity}
*)

Variable I:interval.

(* Tex_Prose
Trivial stuff.
*)

(* Begin_Tex_Verb *)
Lemma Continuous_imp_inc : (F:PartIR)
  (Continuous I F)->(included (iprop I) (Pred F)).
(* End_Tex_Verb *)
Intros; Elim H; Intros; Auto.
Qed.

(* Tex_Prose
\begin{convention} Assume that \verb!I! is compact and \verb!F! is continuous in \verb!I!.
\end{convention}
*)

Hypothesis cI:(compact_ I).
Variable F:PartIR.
Hypothesis contF:(Continuous I F).

(* Begin_Tex_Verb *)
Lemma continuous_compact :
  (H:?)(!Continuous_I (Lend cI) (Rend cI) H F).
(* End_Tex_Verb *)
Intros.
Elim contF; Intros incF contF'.
Contin.
Qed.

(* Begin_Tex_Verb *)
Hypothesis Hinc:(included (iprop I) (Pred F)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Continuous_I_imp_tb_image :
  (totally_bounded [x:IR]
    {y:IR & {Hy:(iprop I y) | x[=](F y (Hinc y Hy))}}).
(* End_Tex_Verb *)
Cut (Continuous_I (Lend_leEq_Rend ? cI) F); Intros.
Elim (Continuous_I_imp_tb_image ???? H); Intros.
Split; [Clear b | Clear a].
Elim a; Intros x Hx.
Elim Hx; Intros y Hy.
Elim Hy; Clear a Hx Hy; Intros Hy Hx.
Exists x; Exists y; Exists (compact_interval_inc ???? Hy).
EApply eq_transitive_unfolded.
Apply Hx.
Algebra.
Intros e He.
Elim (b e He); Intros l H0 H1.
Exists l; Clear b; [Clear H1 | Clear H0].
Intros x Hx.
Elim (H0 x Hx); Intros y Hy.
Elim Hy; Clear H0 Hy Hx; Intros Hy Hx.
Exists y; Exists (compact_interval_inc ???? Hy).
EApply eq_transitive_unfolded.
Apply Hx.
Algebra.
Intros.
Apply H1.
Clear H1.
Elim H0; Intros y Hy.
Elim Hy; Clear H0 Hy; Intros Hy Hx.
Exists y; Exists (interval_compact_inc ?? (Lend_leEq_Rend ? cI) ? Hy).
EApply eq_transitive_unfolded.
Apply Hx.
Algebra.
Apply continuous_compact.
Qed.

(* Begin_Tex_Verb *)
Definition FNorm :=
  (Norm_Funct (continuous_compact (Lend_leEq_Rend ? cI))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma FNorm_bnd_AbsIR :
  (x:IR)(iprop I x)->(Hx:?)(AbsIR (F x Hx))[<=]FNorm.
(* End_Tex_Verb *)
Intros; Unfold FNorm.
Apply norm_bnd_AbsIR.
Apply interval_compact_inc; Auto.
Qed.

End Basic_Results.

Hints Resolve Continuous_imp_inc : included.

Section Other_Results.

(* Tex_Prose
The usual stuff.
*)

Variable I:interval.

Variables F,G:PartIR.

(* Begin_Tex_Verb *)
Lemma Continuous_wd :
  (Feq (iprop I) F G)->(Continuous I F)->(Continuous I G).
(* End_Tex_Verb *)
Intros.
Elim H; Intros H' eqFG.
Elim H'; Clear H H'; Intros incF incG.
Elim H0; Clear H0; Intros incF' contF.
Split.
Auto.
Intros.
Apply Continuous_I_wd with F.
FEQ.
Simpl; Algebra.
Auto.
Qed.

(* Begin_Tex_Verb *)
Hypothesis contF : (Continuous I F).
Hypothesis contG : (Continuous I G).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma included_imp_Continuous : (a,b,Hab:?)
  (included (compact a b Hab) (iprop I))->(Continuous_I Hab F).
(* End_Tex_Verb *)
Intros.
Elim contF; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Included_imp_Continuous : (J:interval)
  (included (iprop J) (iprop I))->(Continuous J F).
(* End_Tex_Verb *)
Intros.
Split.
Exact (included_trans ??? H (Continuous_imp_inc ?? contF)).
Intros.
Apply included_imp_Continuous; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_const : (c:IR)(Continuous I {-C-}c).
(* End_Tex_Verb *)
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_id : (Continuous I FId).
(* End_Tex_Verb *)
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_plus : (Continuous I F{+}G).
(* End_Tex_Verb *)
Elim contF; Intros incF' contF'.
Elim contG; Intros incG' contG'.
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_inv : (Continuous I {--}F).
(* End_Tex_Verb *)
Elim contF; Intros incF' contF'.
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_minus : (Continuous I F{-}G).
(* End_Tex_Verb *)
Elim contF; Intros incF' contF'.
Elim contG; Intros incG' contG'.
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_mult : (Continuous I F{*}G).
(* End_Tex_Verb *)
Elim contF; Intros incF' contF'.
Elim contG; Intros incG' contG'.
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_nth : (n:nat)(Continuous I F{^}n).
(* End_Tex_Verb *)
Elim contF; Intros incF' contF'.
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_scal : (c:IR)(Continuous I c{**}F).
(* End_Tex_Verb *)
Elim contF; Intros incF' contF'.
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_abs : (Continuous I (FAbs F)).
(* End_Tex_Verb *)
Elim contF; Intros incF' contF'.
Split; Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_recip :
  (bnd_away_zero_in_P G (iprop I))->(Continuous I {1/}G).
(* End_Tex_Verb *)
Intro.
Elim contG; Intros incG' contG'.
Cut (x:IR)(iprop I x)->(Hx:?)(G x Hx)[#]Zero; Intros.
Split; Contin.
Apply bnd_imp_ap_zero with (Compact (leEq_reflexive ? x)); Auto.
Apply H; Auto.
Exact (compact_single_iprop I x H0).
Exact (compact_single_prop x).
Qed.

End Other_Results.

Hints Resolve continuous_compact Continuous_const Continuous_id Continuous_plus Continuous_inv
  Continuous_minus Continuous_mult Continuous_scal Continuous_nth Continuous_recip Continuous_abs : continuous.

Hints Immediate included_imp_Continuous Included_imp_Continuous : continuous.

Section Corollaries.

Variable I:interval.

Hypothesis cI:(compact_ I).
Variables F,G:PartIR.

Hypothesis contF : (Continuous I F).
Hypothesis contG : (Continuous I G).

(* Begin_Tex_Verb *)
Lemma Continuous_div :
  (bnd_away_zero_in_P G (iprop I))->(Continuous I F{/}G).
(* End_Tex_Verb *)
Intros.
Apply Continuous_wd with F{*}{1/}G.
FEQ.
Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma FNorm_wd :
  (Feq (iprop I) F G)->(FNorm I cI F contF)[=](FNorm I cI G contG).
(* End_Tex_Verb *)
Intros; Unfold FNorm; Apply Norm_Funct_wd.
EApply included_Feq.
2: Apply H.
Included.
Qed.

End Corollaries.

Hints Resolve Continuous_div : continuous.

Section Sums.

Variable I:interval.

(* Begin_Tex_Verb *)
Lemma Continuous_Sumx : (n:nat)(f:(i:nat)(lt i n)->PartIR)
  ((i:nat)(Hi:?)(Continuous I (f i Hi)))->
  (Continuous I (FSumx n f)).
(* End_Tex_Verb *)
Intro; Induction n; Intros f contF.
Simpl; Contin.
Simpl; Contin.
Qed.

(* Tex_Prose
\begin{convention} Assume \verb!f! is a sequence of continuous functions.
\end{convention}
*)

Variable f:nat->PartIR.
Hypothesis contF : (n:nat)(Continuous I (f n)).

(* Begin_Tex_Verb *)
Lemma Continuous_Sum0 : (n:nat)(Continuous I (FSum0 n f)).
(* End_Tex_Verb *)
Intros.
Induction n.
EApply Continuous_wd.
Apply FSum0_0; Included.
Contin.
EApply Continuous_wd.
Apply FSum0_S; Included.
Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_Sum : (m,n:nat)(Continuous I (FSum m n f)).
(* End_Tex_Verb *)
Intros.
EApply Continuous_wd.
Apply Feq_symmetric; Apply FSum_FSum0'; Included.
Apply Continuous_minus; Apply Continuous_Sum0.
Qed.

End Sums.

Hints Resolve Continuous_Sum0 Continuous_Sumx Continuous_Sum : continuous.

Section Basic_Properties.

(* Tex_Prose
\section{Derivative}

Derivative is not that much different.

\begin{convention} From this point on we assume \verb!I! to be proper.
\end{convention}
*)

Variable I:interval.
Hypothesis pI:(proper I).

Variables F,G,H:PartIR.

(* Begin_Tex_Verb *)
Lemma Derivative_wdl : (Feq (iprop I) F G)->
  (Derivative I pI F H)->(Derivative I pI G H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros H0' Heq.
Elim H0'; Intros incF incG.
Elim H1; Intros incF' H1'.
Elim H1'; Intros incH' derF.
Split.
Auto.
Split.
Auto.
Intros; Apply Derivative_I_wdl with F; Auto.
Apply included_Feq with (iprop I); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_wdr : (Feq (iprop I) F G)->
  (Derivative I pI H F)->(Derivative I pI H G).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros H0' Heq.
Elim H0'; Intros incF incG.
Elim H1; Intros incF' H1'.
Elim H1'; Intros incH' derF.
Split.
Auto.
Split.
Auto.
Intros; Apply Derivative_I_wdr with F; Auto.
Apply included_Feq with (iprop I); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_unique : (Derivative I pI F G)->
  (Derivative I pI F H)->(Feq (iprop I) G H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF H0'.
Elim H0'; Intros incG derFG.
Elim H1; Intros incF' H1'.
Elim H1'; Intros incH derFH.
Apply included_Feq''; Intros.
Auto.
Apply Derivative_I_unique with F; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_imp_inc :
  (Derivative I pI F G)->(included (iprop I) (Pred F)).
(* End_Tex_Verb *)
Intro.
Inversion_clear H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_imp_inc' :
  (Derivative I pI F G)->(included (iprop I) (Pred G)).
(* End_Tex_Verb *)
Intro.
Inversion_clear H0.
Inversion_clear H2; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_imp_Continuous :
  (Derivative I pI F G)->(Continuous I F).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF H'.
Elim H'; Intros incG derF.
Clear H0 H'.
Split; Intros.
Included.
Elim (compact_proper_in_interval ??? Hab H0 pI); Intros a' Ha.
Elim Ha; Clear Ha; Intros b' Hb.
Elim Hb; Clear Hb; Intros Hab' H2 H3.
Apply included_imp_contin with Hab:=(less_leEq ??? Hab').
Auto.
Apply deriv_imp_contin_I with Hab' G; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_imp_Continuous' :
  (Derivative I pI F G)->(Continuous I G).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF H'.
Elim H'; Intros incG derF.
Clear H0 H'.
Split; Intros.
Included.
Elim (compact_proper_in_interval ??? Hab H0 pI); Intros a' Ha.
Elim Ha; Clear Ha; Intros b' Hb.
Elim Hb; Clear Hb; Intros Hab' H2 H3.
Apply included_imp_contin with Hab:=(less_leEq ??? Hab').
Auto.
Apply deriv_imp_contin'_I with Hab' F; Auto.
Qed.

End Basic_Properties.

Hints Immediate Derivative_imp_inc Derivative_imp_inc' : included.
Hints Immediate Derivative_imp_Continuous Derivative_imp_Continuous' : continuous.

Section More_Results.

Variable I:interval.
Hypothesis pI:(proper I).

(* Tex_Prose
\begin{convention} Assume that \verb!F'! and \verb!G'! are derivatives of \verb!F! and \verb!G!, respectively, in \verb!I!.
\end{convention}
*)

Variables F,F',G,G':PartIR.

Hypothesis derF : (Derivative I pI F F').
Hypothesis derG : (Derivative I pI G G').

(* Begin_Tex_Verb *)
Lemma included_imp_Derivative : (a,b,Hab:?)
  (included (compact a b (less_leEq ??? Hab)) (iprop I))->
    (Derivative_I Hab F F').
(* End_Tex_Verb *)
Intros.
Elim derF; Intros incF H'.
Elim H'; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Included_imp_Derivative : (J,pJ:?)
  (included (iprop J) (iprop I))->(Derivative J pJ F F').
(* End_Tex_Verb *)
Intros.
Split.
Exact (included_trans ??? H (Derivative_imp_inc ???? derF)).
Split.
Exact (included_trans ??? H (Derivative_imp_inc' ???? derF)).
Intros.
Apply included_imp_Derivative; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_const :
  (c:IR)(Derivative I pI {-C-}c {-C-}Zero).
(* End_Tex_Verb *)
Intros; Split.
Included.
Split; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_id : (Derivative I pI FId {-C-}One).
(* End_Tex_Verb *)
Split.
Included.
Split; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_plus : (Derivative I pI F{+}G F'{+}G').
(* End_Tex_Verb *)
Elim derF; Intros incF H.
Elim H; Intros incF' derivF.
Elim derG; Intros incG H'.
Elim H'; Intros incG' derivG.
Split.
Included.
Split; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_inv : (Derivative I pI {--}F {--}F').
(* End_Tex_Verb *)
Elim derF; Intros incF H.
Elim H; Intros incF' derivF.
Split.
Included.
Split; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_minus : (Derivative I pI F{-}G F'{-}G').
(* End_Tex_Verb *)
Elim derF; Intros incF H.
Elim H; Intros incF' derivF.
Elim derG; Intros incG H'.
Elim H'; Intros incG' derivG.
Split.
Included.
Split; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_mult : (Derivative I pI F{*}G F{*}G'{+}F'{*}G).
(* End_Tex_Verb *)
Elim derF; Intros incF H.
Elim H; Intros incF' derivF.
Elim derG; Intros incG H'.
Elim H'; Intros incG' derivG.
Split.
Included.
Split.
Apply included_FPlus; Included.
Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_scal : (c:IR)(Derivative I pI c{**}F c{**}F').
(* End_Tex_Verb *)
Intro.
Elim derF; Intros incF H.
Elim H; Intros incF' derivF.
Split.
Included.
Split; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_nth : (n:nat)
  (Derivative I pI F{^}(S n) (nring (S n)){**}(F'{*}F{^}n)).
(* End_Tex_Verb *)
Elim derF; Intros incF H.
Elim H; Intros incF' derivF.
Split.
Included.
Split; Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_recip : (bnd_away_zero_in_P G (iprop I))->
  (Derivative I pI {1/}G {--}(G'{/}(G{*}G))).
(* End_Tex_Verb *)
Elim derG; Intros incG H'.
Elim H'; Intros incG' derivG.
Clear derF derG H'.
Intro.
Cut (x:IR)(iprop I x)->(Hx:?)(Part G x Hx)[#]Zero; Intros.
Cut (x:IR)(iprop I x)->(Hx:?)(G{*}G x Hx)[#]Zero; Intros.
Split.
Included.
Split; Deriv.
Simpl; Apply mult_resp_ap_zero; Auto.
Included.
Qed.

End More_Results.

Section More_Corollaries.

Variable I:interval.
Hypothesis pI:(proper I).

Variables F,F',G,G':PartIR.

Hypothesis derF : (Derivative I pI F F').
Hypothesis derG : (Derivative I pI G G').

(* Begin_Tex_Verb *)
Hypothesis Gbnd:(bnd_away_zero_in_P G (iprop I)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Derivative_div :
  (Derivative I pI F{/}G (F'{*}G{-}F{*}G'){/}(G{*}G)).
(* End_Tex_Verb *)
Elim derF; Intros incF Hf.
Elim Hf; Intros incF' Hf'.
Elim derG; Intros incG derivG.
Elim derivG; Intros incG' Hg'.
Clear Hf derivG.
Cut (x:IR)(iprop I x)->(Hx:?)(Part G x Hx)[#]Zero; Intros.
Split.
Included.
Split.
Apply included_FDiv.
Apply included_FMinus; Included.
Included.
Intros; Simpl; Apply mult_resp_ap_zero; Auto.
Deriv.
Included.
Qed.

End More_Corollaries.

Section More_Sums.

Variable I:interval.
Hypothesis pI:(proper I).

(* Begin_Tex_Verb *)
Lemma Derivative_Sumx : (n:nat)(f,f':(i:nat)(lt i n)->PartIR)
  ((i:nat)(Hi,Hi':?)(Derivative I pI (f i Hi) (f' i Hi')))->
  (Derivative I pI (FSumx n f) (FSumx n f')).
(* End_Tex_Verb *)
Intro; Induction n; Intros f f' derF.
Simpl; Apply Derivative_const; Auto.
Simpl; Apply Derivative_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Variables f,f':nat->PartIR.
Hypothesis derF : (n:nat)(Derivative I pI (f n) (f' n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Derivative_Sum0 : (n:nat)
  (Derivative I pI (FSum0 n f) (FSum0 n f')).
(* End_Tex_Verb *)
Intros.
Induction n.
EApply Derivative_wdl.
Apply FSum0_0; Included.
EApply Derivative_wdr.
Apply FSum0_0; Included.
Apply Derivative_const.
EApply Derivative_wdl.
Apply FSum0_S; Included.
EApply Derivative_wdr.
Apply FSum0_S; Included.
Apply Derivative_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_Sum : (m,n:nat)
  (Derivative I pI (FSum m n f) (FSum m n f')).
(* End_Tex_Verb *)
Intros.
EApply Derivative_wdl.
Apply Feq_symmetric; Apply FSum_FSum0'; Included.
EApply Derivative_wdr.
Apply Feq_symmetric; Apply FSum_FSum0'; Included.
Apply Derivative_minus; Apply Derivative_Sum0.
Qed.

End More_Sums.

Section Diffble_Basic_Properties.

(* Tex_Prose
\section{Differentiability}

\emph{Mutatis mutandis} for differentiability.
*)

Variable I:interval.
Hypothesis pI:(proper I).

(* Begin_Tex_Verb *)
Lemma Diffble_imp_inc : (F:PartIR)
  (Diffble I pI F)->(included (iprop I) (Pred F)).
(* End_Tex_Verb *)
Intros.
Inversion_clear H.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_imp_Diffble : (F,F':PartIR)
  (Derivative I pI F F')->(Diffble I pI F).
(* End_Tex_Verb *)
Intros.
Elim H; Intros incF H'.
Elim H'; Intros incF' derivF.
Split; Auto.
Intros; Apply deriv_imp_Diffble_I with F'; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_wd : (F,H:PartIR)(Feq (iprop I) F H)->
  (Diffble I pI F)->(Diffble I pI H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros H2 eqFH.
Elim H2; Intros incF incH.
Inversion_clear H1.
Split; Auto.
Intros; Apply Diffble_I_wd with F; Auto.
Apply included_Feq with (iprop I); Auto.
Qed.

Variables F,G:PartIR.

Hypothesis diffF:(Diffble I pI F).
Hypothesis diffG:(Diffble I pI G).

(* Tex_Prose
\begin{convention} Assume \verb!F! and \verb!G! are differentiable in \verb!I!.
\end{convention}
*)

(* Begin_Tex_Verb *)
Lemma included_imp_Diffble : (a,b,Hab:?)
  (included (compact a b (less_leEq ??? Hab)) (iprop I))->
    (Diffble_I Hab F).
(* End_Tex_Verb *)
Intros.
Elim diffF; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Included_imp_Diffble : (J,pJ:?)
  (included (iprop J) (iprop I))->(Diffble J pJ F).
(* End_Tex_Verb *)
Intros.
Split.
Exact (included_trans ??? H (Diffble_imp_inc ? diffF)).
Intros; Apply included_imp_Diffble; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_const : (c:IR)(Diffble I pI {-C-}c).
(* End_Tex_Verb *)
Intro.
Split.
Included.
Intros; Apply Diffble_I_const.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_id : (Diffble I pI FId).
(* End_Tex_Verb *)
Split.
Included.
Intros; Apply Diffble_I_id.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_plus : (Diffble I pI F{+}G).
(* End_Tex_Verb *)
Elim diffF; Intros incF diffbleF.
Elim diffG; Intros incG diffbleG.
Split.
Included.
Intros; Apply Diffble_I_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_inv : (Diffble I pI {--}F).
(* End_Tex_Verb *)
Elim diffF; Intros incF diffbleF.
Split.
Included.
Intros; Apply Diffble_I_inv; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_minus : (Diffble I pI F{-}G).
(* End_Tex_Verb *)
Elim diffF; Intros incF diffbleF.
Elim diffG; Intros incG diffbleG.
Split.
Included.
Intros; Apply Diffble_I_minus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_mult : (Diffble I pI F{*}G).
(* End_Tex_Verb *)
Elim diffF; Intros incF diffbleF.
Elim diffG; Intros incG diffbleG.
Split.
Included.
Intros; Apply Diffble_I_mult; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_nth : (n:nat)(Diffble I pI F{^}n).
(* End_Tex_Verb *)
Elim diffF; Intros incF diffbleF.
Split.
Included.
Intros; Apply Diffble_I_nth; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_scal : (c:IR)(Diffble I pI c{**}F).
(* End_Tex_Verb *)
Elim diffF; Intros incF diffbleF.
Split.
Included.
Intros; Apply Diffble_I_scal; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_recip :
  (bnd_away_zero_in_P G (iprop I))->(Diffble I pI {1/}G).
(* End_Tex_Verb *)
Elim diffG; Intros incG diffbleG Gbnd.
Cut (x:IR)(iprop I x)->(Hx:?)(Part G x Hx)[#]Zero; Intros.
Split.
Included.
Intros; Apply Diffble_I_recip; Auto.
Included.
Qed.

End Diffble_Basic_Properties.

Hints Immediate Diffble_imp_inc : included.

Section Diffble_Corollaries.

Variable I:interval.
Hypothesis pI:(proper I).

Variables F,G:PartIR.

Hypothesis diffF:(Diffble I pI F).
Hypothesis diffG:(Diffble I pI G).

(* Begin_Tex_Verb *)
Lemma Diffble_div :
  (bnd_away_zero_in_P G (iprop I))->(Diffble I pI F{/}G).
(* End_Tex_Verb *)
Intro.
Apply Diffble_wd with F{*}{1/}G.
Apply eq_imp_Feq.
Apply included_FMult.
Apply Diffble_imp_inc with pI; Apply diffF.
Apply included_FRecip.
Apply Diffble_imp_inc with pI; Apply diffG.
Included.
Apply included_FDiv.
Apply Diffble_imp_inc with pI; Apply diffF.
Apply Diffble_imp_inc with pI; Apply diffG.
Included.
Intros; Simpl; Rational.
Apply Diffble_mult; Auto.
Apply Diffble_recip; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_Sum0 : (f:?)((n:nat)(Diffble I pI (f n)))->
  (n:nat)(Diffble I pI (FSum0 n f)).
(* End_Tex_Verb *)
Intros f hypF n.
Split.
Red; Simpl; Intros.
Elim (hypF n0); Intros.
Exact (a x H).
Intros; Apply Diffble_I_Sum0; Auto.
Intro; Elim (hypF n0); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_Sumx : (n:nat)(f:?)(good_fun_seq' n f)->
  ((i:nat)(Hi:?)(Diffble I pI (f i Hi)))->(Diffble I pI (FSumx n f)).
(* End_Tex_Verb *)
Intros n f Hgood hypF.
Split.
Red; Intros.
Apply FSumx_pred'; Auto.
Intros.
Elim (hypF i Hi); Auto.
Intros; Apply Diffble_I_Sumx.
Intros i Hi; Elim (hypF i Hi); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_Sum : (f:?)((n:nat)(Diffble I pI (f n)))->
  (m,n:nat)(Diffble I pI (FSum m n f)).
(* End_Tex_Verb *)
Intros f hypF m n.
EApply Diffble_wd.
Apply Feq_symmetric; Apply FSum_FSum0'.
Intro; Apply Diffble_imp_inc with pI; Auto.
Apply Diffble_minus; Apply Diffble_Sum0; Auto.
Qed.

End Diffble_Corollaries.

Section Nth_Derivative.

(* Tex_Prose
\section{N$^{\mathrm{th}}$ Derivative}

Higher order derivatives pose more interesting problems.  It turns out that it really becomes necessary to generalize our \verb!n_deriv! operator to any interval.
*)

Variable I:interval.
Hypothesis pI : (proper I).

Section Definitions.

(* Tex_Prose
\begin{convention} Let \verb!n:nat!, \verb!F:PartIR! and assume that \verb!F! is $n$-times differentiable in \verb!I!.
\end{convention}
*)

Variable n:nat.
Variable F:PartIR.
Hypothesis diffF:(Diffble_n n I pI F).

(* Begin_Tex_Verb *)
Definition N_Deriv_fun : (x:IR)(iprop I x)->IR.
(* End_Tex_Verb *)
Intros.
LetTac J:=(compact_in_interval I pI x H).
Elim diffF; Intros incF diffbleF.
LetTac a:=(Lend (compact_compact_in_interval I pI x H)).
LetTac b:=(Rend (compact_compact_in_interval I pI x H)).
Fold J in a b.
Cut a[<]b; Intros.
Cut (Diffble_I_n H0 n F); Intros.
Apply (Part (n_deriv_I ????? H1) x).
Apply n_deriv_inc.
Unfold a b J; Apply iprop_compact_in_interval_inc2.
Apply iprop_compact_in_interval.
Apply diffbleF.
Apply included_trans with (iprop J); Unfold a b J; Included.
Unfold a b J; Apply proper_compact_in_interval'.
Defined.

(* Begin_Tex_Verb *)
Lemma N_Deriv_char
(* End_Tex_Verb *)
 : (x,Hx,H:?)(N_Deriv_fun x Hx)[=]
  (Part (n_deriv_I ?? (proper_compact_in_interval' ???? (compact_compact_in_interval I pI x Hx)) n F H) x 
    (n_deriv_inc ??????? (iprop_compact_in_interval_inc2 ???? (compact_compact_in_interval ????)
      (less_leEq ??? (proper_compact_in_interval' ???? (compact_compact_in_interval ????))) ? (iprop_compact_in_interval ????)))).
Intros.
Unfold N_Deriv_fun.
Elim diffF; Intros; Simpl.
Apply n_deriv_I_wd'.
Algebra.
Apply iprop_compact_in_interval'.
Apply iprop_compact_in_interval'.
Apply b.
Apply included_trans with (Compact (less_leEq ??? (proper_compact_in_interval' ???? (compact_compact_in_interval I pI x Hx)))).
2: Included.
Red; Intros.
Inversion_clear H0.
Split.
EApply leEq_wdl.
Apply H1.
EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft; Apply eq_imp_leEq.
Apply compact_in_interval_wd1; Algebra.
EApply leEq_wdr.
Apply H2.
Apply leEq_imp_Max_is_rht; Apply eq_imp_leEq.
Apply compact_in_interval_wd2; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma N_Deriv_strext : (x,y:IR)(Hx,Hy:?)
  (((N_Deriv_fun x Hx)[#](N_Deriv_fun y Hy))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Elim diffF; Intros incF diffbleF.
Cut (Diffble_I_n (proper_compact_in_interval2' ?????? (compact_compact_in_interval2 I pI x y Hx Hy)) n F); Intros.
Cut (Diffble_I_n (proper_compact_in_interval' ???? (compact_compact_in_interval I pI x Hx)) n F); Intros.
Cut (Diffble_I_n (proper_compact_in_interval' ???? (compact_compact_in_interval I pI y Hy)) n F); Intros.
Cut (Pred (n_deriv_I ????? H0) x); Intros.
Cut (Pred (n_deriv_I ????? H0) y); Intros.
Apply pfstrx with Hx:=H3 Hy:=H4.
EApply ap_well_def_lft_unfolded.
EApply ap_well_def_rht_unfolded.
Apply H.
EApply eq_transitive_unfolded.
Apply (N_Deriv_char y Hy H2).
Apply n_deriv_I_wd'.
Algebra.
Apply iprop_compact_in_interval_inc2; Apply iprop_compact_in_interval.
Apply iprop_compact_in_interval2_inc2; Apply iprop_compact_in_interval2y.
Apply included_imp_diffble_n with Hab':=(proper_compact_in_interval2' ?????? (compact_compact_in_interval2 I pI x y Hx Hy)).
2: Apply H0.
Red; Intros z Hz.
Inversion_clear Hz; Split.
EApply leEq_wdl.
Apply H5.
EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft.
Apply compact_in_interval_y_lft.
EApply leEq_wdr.
Apply H6.
Apply leEq_imp_Max_is_rht.
Apply compact_in_interval_y_rht.
EApply eq_transitive_unfolded.
Apply (N_Deriv_char x Hx H1).
Apply n_deriv_I_wd'.
Algebra.
Apply iprop_compact_in_interval_inc2; Apply iprop_compact_in_interval.
Apply iprop_compact_in_interval2_inc2; Apply iprop_compact_in_interval2x.
Apply included_imp_diffble_n with Hab':=(proper_compact_in_interval2' ?????? (compact_compact_in_interval2 I pI x y Hx Hy)).
2: Apply H0.
Red; Intros z Hz.
Inversion_clear Hz; Split.
EApply leEq_wdl.
Apply H5.
EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft.
Apply compact_in_interval_x_lft.
EApply leEq_wdr.
Apply H6.
Apply leEq_imp_Max_is_rht.
Apply compact_in_interval_x_rht.
Apply n_deriv_inc.
Apply iprop_compact_in_interval2_inc2; Apply iprop_compact_in_interval2y.
Apply n_deriv_inc.
Apply iprop_compact_in_interval2_inc2; Apply iprop_compact_in_interval2x.
Apply diffbleF.
Simpl; Included.
Apply diffbleF.
Simpl; Included.
Apply diffbleF.
Simpl; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma N_Deriv_wd : (x,y:IR)(Hx,Hy:?)(x[=]y)->
  (N_Deriv_fun x Hx)[=](N_Deriv_fun y Hy).
(* End_Tex_Verb *)
Intros.
Apply not_ap_imp_eq; Intro.
Cut x[#]y.
Apply eq_imp_not_ap; Auto.
Exact (N_Deriv_strext ???? H0).
Qed.

(* Begin_Tex_Verb *)
Definition N_Deriv : PartIR.
(* End_Tex_Verb *)
Apply Build_PartFunct with pfpfun:=N_Deriv_fun.
Apply iprop_wd.
Exact N_Deriv_strext.
Defined.

End Definitions.

Section Basic_Results.

(* Tex_Prose
All the usual results hold.
*)

(* Begin_Tex_Verb *)
Lemma Diffble_n_wd : (n:nat)(F,G:PartIR)(Feq (iprop I) F G)->
  (Diffble_n n I pI F)->(Diffble_n n I pI G).
(* End_Tex_Verb *)
Intros.
Elim H; Intros H1.
Elim H1; Intros incG incF.
Split.
Auto.
Intros; Apply Diffble_I_n_wd with F.
Apply included_Feq with (iprop I); Auto.
Elim H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_wdr : (n,F,G,H:?)(Feq (iprop I) G H)->
  (Derivative_n n I pI F G)->(Derivative_n n I pI F H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros H2 Heq.
Elim H2; Intros incG incH.
Elim H1; Intros incF H0'.
Elim H0'; Intros incG' derivF.
Clear H2 H0'.
Split; Auto.
Split; Auto.
Intros; Apply Derivative_I_n_wdr with G.
Apply included_Feq with (iprop I); Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_wdl : (n,F,G,H:?)(Feq (iprop I) F G)->
  (Derivative_n n I pI F H)->(Derivative_n n I pI G H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros H2 Heq.
Elim H2; Intros incG incH.
Elim H1; Intros incF H0'.
Elim H0'; Intros incG' derivF.
Clear H2 H0'.
Split; Auto.
Split; Auto.
Intros; Apply Derivative_I_n_wdl with F.
Apply included_Feq with (iprop I); Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_unique : (n:nat)(F,G,H:PartIR)
  (Derivative_n n I pI F G)->(Derivative_n n I pI F H)->
  (Feq (iprop I) G H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF H2.
Elim H2; Intros incG derivFG.
Elim H1; Intros incF' H3.
Elim H3; Intros incH derivFH.
FEQ.
Apply Feq_imp_eq with (Compact (less_leEq ??? (proper_compact_in_interval' ???? (compact_compact_in_interval I pI x H4)))).
Apply Derivative_I_n_unique with n F.
Apply derivFG.
Simpl; Included.
Apply derivFH.
Simpl; Included.
Apply interval_compact_inc.
Apply iprop_compact_in_interval.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_n_imp_Diffble : (n:nat)(lt O n)->(F:PartIR)
  (Diffble_n n I pI F)->(Diffble I pI F).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF diffF.
Split; Auto.
Intros; Apply Diffble_I_n_imp_diffble with n; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_imp_Diffble : (n:nat)(lt O n)->(F,F':PartIR)
  (Derivative_n n I pI F F')->(Diffble I pI F).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF H1.
Elim H1; Intros incF' derivF.
Split; Auto.
Intros; Apply deriv_n_imp_diffble with n F'; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma le_imp_Diffble_n : (m,n:nat)(le m n)->(F:PartIR)
  (Diffble_n n I pI F)->(Diffble_n m I pI F).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF diffF.
Split; Auto.
Intros; Apply le_imp_Diffble_I with n; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_n_imp_le : (n:nat)(lt O n)->(F,F':PartIR)
  (Diffble_n n I pI F)->(Derivative I pI F F')->
    (Diffble_n (pred n) I pI F').
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF diffF.
Elim H1; Intros incFa H2.
Elim H2; Intros incF' derivF.
Split; Auto.
Intros; Apply Diffble_I_imp_le with F; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_n_imp_inc : (n:nat)(F:PartIR)
  (Diffble_n n I pI F)->(included (iprop I) (Pred F)).
(* End_Tex_Verb *)
Intros.
Inversion_clear H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_imp_Diffble_n : (n:nat)(F,F':PartIR)
  (Derivative_n n I pI F F')->(Diffble_n n I pI F).
(* End_Tex_Verb *)
Intros.
Elim H; Intros incF H1.
Elim H1; Intros incF' derivF.
Split; Auto.
Intros; Apply deriv_n_imp_Diffble_I_n with F'; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_imp_inc : (n:nat)(F,F':PartIR)
  (Derivative_n n I pI F F')->(included (iprop I) (Pred F)).
(* End_Tex_Verb *)
Intros.
Inversion_clear H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_imp_inc' : (n:nat)(F,F':PartIR)
  (Derivative_n n I pI F F')->(included (iprop I) (Pred F')).
(* End_Tex_Verb *)
Intros.
Inversion_clear H; Inversion_clear H1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_imp_Derivative_n : (n,F,F',a,b,Hab:?)
  (Derivative_n n I pI F F')->
  (included (Compact (less_leEq ??? Hab)) (iprop I))->
  (!Derivative_I_n a b Hab n F F').
(* End_Tex_Verb *)
Intros.
Elim H; Intros incF H1.
Elim H1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_imp_Diffble_n : (n,F,a,b,Hab:?)
  (Diffble_n n I pI F)->
  (included (Compact (less_leEq ??? Hab)) (iprop I))->
  (!Diffble_I_n a b Hab n F).
(* End_Tex_Verb *)
Intros.
Elim H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Included_imp_Derivative_n : (n:nat)(J,pJ:?)(F,F':PartIR)
  (included (iprop J) (iprop I))->(Derivative_n n I pI F F')->
  (Derivative_n n J pJ F F').
(* End_Tex_Verb *)
Intros.
Inversion_clear H0.
Inversion_clear H2.
Split.
Included.
Split.
Included.
Intros; Apply H3.
Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Included_imp_Diffble_n : (n:nat)(J,pJ:?)(F:PartIR)
  (included (iprop J) (iprop I))->
  (Diffble_n n I pI F)->(Diffble_n n J pJ F).
(* End_Tex_Verb *)
Intros.
Inversion_clear H0.
Split.
Included.
Intros; Apply H2.
Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_plus : (J,pJ,n,m,k,F,G,H:?)
  (Derivative_n m J pJ F G)->(Derivative_n n J pJ G H)->
  k=(plus m n)->(Derivative_n k J pJ F H).
(* End_Tex_Verb *)
Intros.
Elim H0; Intros incF Hf.
Elim Hf; Intros incG derFG.
Elim H1; Intros incG' Hg.
Elim Hg; Intros incH derGH.
Clear Hf Hg.
Split; Auto.
Split; Auto.
Intros; Apply Derivative_I_n_plus with n m G; Auto.
Qed.

End Basic_Results.

Section More_Results.

(* Tex_Prose
Some new results hold, too:
*)

(* Begin_Tex_Verb *)
Lemma N_Deriv_Feq : (n,F,diffF,a,b,Hab,H:?)
  (incN:(included (Compact (less_leEq ??? Hab))
                  (Pred (N_Deriv n F diffF))))
  (Feq (Compact (less_leEq ??? Hab))
       (N_Deriv n F diffF) (n_deriv_I a b Hab n F H)).
(* End_Tex_Verb *)
Intros.
FEQ.
Apply n_deriv_inc.
Simpl.
Cut (!Diffble_I_n ?? (proper_compact_in_interval' ???? (compact_compact_in_interval I pI x Hx)) n F); Intros.
EApply eq_transitive_unfolded.
Apply (N_Deriv_char n F diffF x Hx H1).
Apply n_deriv_I_wd'; Auto.
Algebra.
Apply iprop_compact_in_interval_inc2; Apply iprop_compact_in_interval.
Apply included_imp_Diffble_n; Auto.
Apply included_interval'.
Apply (included_compact_in_interval I pI x Hx).
Apply (iprop_compact_in_interval_inc1 ???? (compact_compact_in_interval I pI x Hx) 
  (Lend_leEq_Rend ? (compact_compact_in_interval I pI x Hx))).
Apply compact_inc_lft.
Apply (included_compact_in_interval I pI x Hx).
Apply (iprop_compact_in_interval_inc1 ???? (compact_compact_in_interval I pI x Hx) 
  (Lend_leEq_Rend ? (compact_compact_in_interval I pI x Hx))).
Apply compact_inc_rht.
Apply incN; Apply compact_inc_lft.
Apply incN; Apply compact_inc_rht.
Elim diffF; Intros incF diffbleF.
Apply diffbleF; Auto.
EApply included_trans.
Apply iprop_compact_in_interval_inc1.
Included.
Qed.

(* Begin_Tex_Verb *)
Lemma N_Deriv_lemma : (n:nat)(F:PartIR)(H:(Diffble_n n I pI F))
  (Derivative_n n I pI F (N_Deriv ?? H)).
(* End_Tex_Verb *)
Intros.
Elim H; Intros incF diffF.
Split; Auto.
Split; Included.
Intros.
Cut (Diffble_I_n Hab n F); Intros; Auto.
EApply Derivative_I_n_wdr.
Apply Feq_symmetric; Apply (N_Deriv_Feq n F (incF,diffF) ?? Hab H1 H0).
Apply n_deriv_lemma.
Qed.

(* Begin_Tex_Verb *)
Lemma N_Deriv_S : (n:nat)(F:PartIR)
  (H:(Diffble_n n I pI F))(H':(Diffble_n (S n) I pI F))
  (Derivative I pI (N_Deriv ?? H) (N_Deriv ?? H')).
(* End_Tex_Verb *)
Intros.
Split; Included.
Split; Included.
Elim H; Intros incF diffFn.
Elim H'; Intros incF' diffFSn.
Intros.
Cut (Diffble_I_n Hab n F); Intros; Auto.
Cut (Diffble_I_n Hab (S n) F); Intros; Auto.
EApply Derivative_I_wdl.
Apply Feq_symmetric; Apply (N_Deriv_Feq n F (incF,diffFn) ?? Hab H1 H0).
EApply Derivative_I_wdr.
Apply Feq_symmetric; Apply (N_Deriv_Feq ?? (incF',diffFSn) ?? Hab H2 H0).
Apply n_Sn_deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma N_Deriv_plus : 
  (m,n:nat)(F:PartIR)(H:(Diffble_n n I pI F))
  (H':(Diffble_n (plus m n) I pI F))
  (Derivative_n m I pI (N_Deriv ?? H) (N_Deriv ?? H')).
(* End_Tex_Verb *)
Intros.
Split; Included.
Split; Included.
Intros.
Cut (Diffble_I_n Hab n F); Intros.
Cut (Diffble_I_n Hab (plus m n) F); Intros.
EApply Derivative_I_n_wdl.
Apply Feq_symmetric; Apply (N_Deriv_Feq n F H ?? Hab H1 H0).
EApply Derivative_I_n_wdr.
Apply Feq_symmetric; Apply (N_Deriv_Feq ?? H' ?? Hab H2 H0).
Apply n_deriv_plus.
Elim H'; Auto.
Elim H; Auto.
Qed.

(* Tex_Prose
Some useful characterization results.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_n_O : (F:?)
  (included (iprop I) (Pred F))->(Derivative_n O I pI F F).
(* End_Tex_Verb *)
Intros.
Split; Included.
Split; Included.
Intros.
Red; Apply Feq_reflexive; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_Sn : (F,n,fn,fSn:?)
  (Derivative_n n I pI F fn)->
  (Derivative_n (S n) I pI F fSn)->(Derivative I pI fn fSn).
(* End_Tex_Verb *)
Intros.
Cut (Diffble_n n I pI F); [Intro | EApply Derivative_n_imp_Diffble_n; Apply H].
Cut (Diffble_n (S n) I pI F); [Intro | EApply Derivative_n_imp_Diffble_n; Apply H0].
Apply Derivative_wdl with (N_Deriv ?? H1).
Apply Derivative_n_unique with n F.
Apply N_Deriv_lemma.
Auto.
Apply Derivative_wdr with (N_Deriv ?? H2).
Apply Derivative_n_unique with (S n) F.
Apply N_Deriv_lemma.
Auto.
Apply N_Deriv_S.
Qed.

End More_Results.

Section Derivating_Diffble.

(* Tex_Prose
As a special case we get a differentiation operator\ldots
*)

Variable F:PartIR.

(* Begin_Tex_Verb *)
Hypothesis diffF:(Diffble I pI F).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Diffble_imp_Diffble_n : (Diffble_n (1) I pI F).
(* End_Tex_Verb *)
Elim diffF; Intros incF diffbleF.
Split; Auto.
Intros; Exists (diffbleF a b Hab H).
Simpl; Included.
Qed.

(* Begin_Tex_Verb *)
Definition Deriv := (N_Deriv (1) F Diffble_imp_Diffble_n).
(* End_Tex_Verb *)

End Derivating_Diffble.

Section Corollaries.

(* Tex_Prose
\ldots for which the expected property also holds.
*)

(* Begin_Tex_Verb *)
Lemma Deriv_lemma : (F:PartIR)(diffF:?)(Derivative I pI F (Deriv F diffF)).
(* End_Tex_Verb *)
Intros; Unfold Deriv.
Apply Derivative_wdl with (N_Deriv (0) F (le_imp_Diffble_n (0) (1) (le_n_Sn (0)) F (Diffble_imp_Diffble_n ? diffF))).
Apply Derivative_n_unique with (0) F.
Apply N_Deriv_lemma.
Apply Derivative_n_O; Elim diffF; Auto.
Apply N_Deriv_S.
Qed.

(* Tex_Prose
Some more interesting properties.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_n_1 : (F,G:?)(Derivative I pI F G)->
  (Derivative_n (1) I pI F G).
(* End_Tex_Verb *)
Intros.
Cut (Diffble I pI F); Intros.
Apply Derivative_n_wdr with (Deriv ? H0).
Apply Derivative_unique with pI F.
Apply Deriv_lemma.
Auto.
Unfold Deriv; Apply N_Deriv_lemma.
Apply Derivative_imp_Diffble with G; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_chain : (F,f:?)
  (Feq (iprop I) F (f O))->
  ((n:nat)(Derivative I pI (f n) (f (S n))))->
  (n:nat)(Derivative_n n I pI F (f n)).
(* End_Tex_Verb *)
Intros.
Induction n.
Apply Derivative_n_wdr with F.
Auto.
Apply Derivative_n_O.
Inversion_clear H; Inversion_clear H1; Auto.
Apply Derivative_n_plus with (1) n (f n); Auto.
Apply Derivative_n_1; Auto.
Rewrite plus_sym; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_imp_Continuous : (n,F,G:?)(lt O n)->
  (Derivative_n n I pI F G)->(Continuous I F).
(* End_Tex_Verb *)
Intros.
Cut (Diffble I pI F); Intros.
Apply Derivative_imp_Continuous with pI (Deriv ? H1).
Apply Deriv_lemma.
Apply Diffble_n_imp_Diffble with n; Auto.
Apply Derivative_n_imp_Diffble_n with G; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_n_imp_Continuous' : (n,F,G:?)(lt O n)->
  (Derivative_n n I pI F G)->(Continuous I G).
(* End_Tex_Verb *)
Intros.
Cut (Diffble_n (pred n) I pI F); Intros.
Apply Derivative_imp_Continuous' with pI (N_Deriv ?? H1).
Apply Derivative_wdr with (N_Deriv ?? (Derivative_n_imp_Diffble_n ??? H0)).
Apply Derivative_n_unique with n F; Auto; Apply N_Deriv_lemma.
Cut n=(S (pred n)); [Intro | Apply S_pred with O; Auto].
Generalize H0.
Pattern 1 3 4 n; Rewrite H2.
Intro; Apply N_Deriv_S.
Apply le_imp_Diffble_n with n.
Auto with arith.
Apply Derivative_n_imp_Diffble_n with G; Auto.
Qed.

End Corollaries.

End Nth_Derivative.

Hints Resolve Derivative_const Derivative_id Derivative_plus Derivative_inv Derivative_minus Derivative_mult
  Derivative_scal Derivative_nth Derivative_recip Derivative_div Derivative_Sumx Derivative_Sum0 Derivative_Sum : derivate.

Hints Immediate Derivative_n_imp_inc Derivative_n_imp_inc' Diffble_n_imp_inc : included.

Hints Resolve Deriv_lemma N_Deriv_lemma : derivate.

Hints Immediate Derivative_n_imp_Continuous Derivative_n_imp_Continuous' : continuous.
