(* $Id: Rolle.v,v 1.20 2003/03/13 12:06:23 lcf Exp $ *)

Require Export FunctTactics.
Require Export MoreFunctions.

Section Rolle.

(* Tex_Prose
\chapter{Rolle's Theorem}

We now begin to work with partial functions.  We begin by stating and proving Rolle's theorem in various forms and some of its corollaries.

\begin{convention} Assume that:
\begin{itemize}
\item \verb!a,b:IR! with $a<b$ and denote by \verb!I!$=[a,b]$;
\item \verb!F,F'! are partial functions such that \verb!F'! is the derivative of \verb!F! in \verb!I!;
\item \verb!e! is a positive real number.
\end{itemize}
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

Variables F,F':PartIR.

Hypothesis derF:(Derivative_I Hab' F F').
Hypothesis Ha:(Pred F a).
Hypothesis Hb:(Pred F b).

(* Begin_Tex_Verb *)
Hypothesis Fab:(F a Ha)[=](F b Hb).
(* End_Tex_Verb *)

Variable e:IR.
Hypothesis He:Zero[<]e.

Local contF' : (Continuous_I Hab F').
Apply deriv_imp_contin'_I with Hab' F.
Assumption.
Qed.

Local derivF : (e:IR)(Zero[<]e)->{d:IR & (Zero[<]d) | (x,y:IR)(I x)->(I y)->(Hx,Hy,Hx':?)((AbsIR x[-]y)[<=]d)->
  (AbsIR ((F y Hy)[-](F x Hx))[-](F' x Hx')[*](y[-]x))[<=]e[*](AbsIR y[-]x)}.
Elim derF.
Intros a0 b0.
Elim b0; Intros H b1.
Unfold I; Assumption.
Qed.

Local Rolle_lemma2 : {d:IR & (Zero[<]d) | (x,y:IR)(I x)->(I y)->(Hx,Hy,Hx':?)((AbsIR x[-]y)[<=]d)->
  (AbsIR ((F y Hy)[-](F x Hx))[-](F' x Hx')[*](y[-]x))[<=](e[/]TwoNZ)[*](AbsIR y[-]x)}.
Exact (derivF ? (pos_div_two ?? He)).
Qed.

Local df:=(proj1_sigS2P ??? Rolle_lemma2).

Local Hdf : (Zero[<]df) := (proj2a_sigS2P ??? Rolle_lemma2).

Local Hf : ((x,y:IR)(I x)->(I y)->(Hx,Hy,Hx':?)((AbsIR x[-]y)[<=]df)->
  (AbsIR ((F y Hy)[-](F x Hx))[-](F' x Hx')[*](y[-]x))[<=](e[/]TwoNZ)[*](AbsIR y[-]x))
  := (proj2b_sigS2P ??? Rolle_lemma2).

Local Rolle_lemma3 : {d:IR & (Zero[<]d) | (x,y:IR)(I x)->(I y)->(Hx,Hy:?)((AbsIR x[-]y)[<=]d)->
  (AbsIR (F' x Hx)[-](F' y Hy))[<=]e[/]TwoNZ}.
Elim contF'; Intros.
Exact (b0 ? (pos_div_two ?? He)).
Qed.

Local df':=(proj1_sigS2P ??? Rolle_lemma3).

Local Hdf' : Zero[<]df' := (proj2a_sigS2P ??? Rolle_lemma3).

Local Hf' : ((x,y:IR)(I x)->(I y)->(Hx,Hy:?)((AbsIR x[-]y)[<=]df')->(AbsIR (F' x Hx)[-](F' y Hy))[<=]e[/]TwoNZ)
  := (proj2b_sigS2P ??? Rolle_lemma3).

Local d:=(Min df df').

Local Hd : (Zero[<]d).
Unfold d; Apply less_Min; Auto.
Qed.

Local incF : (included (Compact Hab) (Pred F)).
Elim derF; Intros; Assumption.
Qed.

Local n:=(compact_nat a b d Hd).

Local fcp [i:nat][Hi:(le i n)] := (F (compact_part a b Hab' d Hd i Hi) (incF ? (compact_part_hyp a b Hab Hab' d Hd i Hi))).

Local Rolle_lemma1 : (Sumx [i:nat; H:(lt i n)] (fcp (S i) H)[-](fcp i (lt_le_weak i n H))) [=] Zero.
Apply eq_transitive_unfolded with (fcp ? (le_n n))[-](fcp (0) (le_O_n n)).
Apply Mengolli_Sum with f:=[i:nat][H:(le i n)](fcp ? H).
Red; Do 3 Intro.
Rewrite H; Intros.
Unfold fcp; Simpl; Algebra.
Intros; Algebra.
Apply eq_transitive_unfolded with (F b Hb)[-](F a Ha).
Unfold fcp compact_part n; Simpl.
Apply cg_minus_wd; Apply pfwdef; Rational.
Step_rht (F a Ha)[-](F a Ha); Apply cg_minus_wd.
Apply eq_symmetric_unfolded; Apply Fab.
Algebra.
Qed.

Local incF' : (included (Compact Hab) (Pred F')).
Elim derF; Intros.
Elim b0; Intros.
Assumption.
Qed.

Local fcp' [i:nat][Hi:(le i n)] := (F' (compact_part a b Hab' d Hd i Hi) (incF' ? (compact_part_hyp a b Hab Hab' d Hd i Hi))).

Syntactic Definition cp := (compact_part a b Hab' d Hd).

Local Rolle_lemma4 : {i:nat & {H:(Clt i n) & 
  Zero[<](((fcp' ? (lt_le_weak ?? (Clt_to ?? H)))[+]e)[*]((cp (S i) (Cle_to ?? H))[-](cp i (lt_le_weak ?? (Cle_to ?? H)))))}}.
Apply positive_Sumx with f:=[i:nat][H:(lt i n)]((fcp' ? (lt_le_weak ?? H))[+]e)[*]((cp ? H)[-](cp ? (lt_le_weak ?? H))).
Red; Do 3 Intro.
Rewrite H; Intros.
Unfold fcp'; Algebra.
Apply less_wdl with (Sumx [i:nat][H:(lt i n)](fcp ? H)[-](fcp ? (lt_le_weak ?? H))).
2: Apply Rolle_lemma1.
Apply Sumx_resp_less.
Apply less_nring with (IR::COrdField); Simpl; Unfold n; Apply pos_compact_nat; Auto.
Intros.
Apply leEq_less_trans with ((fcp' i (lt_le_weak ?? H))[+]e[/]TwoNZ)[*]((cp (S i) H)[-](cp i (lt_le_weak ?? H))).
2: Apply mult_resp_less.
3: Apply compact_less.
2: Apply plus_resp_less_lft.
2: Apply pos_div_two'; Assumption.
RStep (fcp' i (lt_le_weak ?? H))[*]((cp ? H)[-](cp ? (lt_le_weak ?? H)))[+]
  (((fcp ? H)[-](fcp ? (lt_le_weak ?? H)))[-](fcp' i (lt_le_weak ?? H))[*]((cp ? H)[-](cp ? (lt_le_weak ?? H)))).
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply ring_distl_unfolded.
Apply plus_resp_leEq_lft.
Apply leEq_wdr with (e[/]TwoNZ)[*](AbsIR (cp (S i) H)[-](cp i (lt_le_weak ?? H))).
2: Apply mult_wd.
2: Algebra.
2: Apply AbsIR_eq_x.
2: Apply less_leEq; Apply compact_less.
EApply leEq_transitive.
Apply leEq_AbsIR.
Unfold fcp fcp'; Apply Hf.
Unfold I; Apply compact_part_hyp.
Unfold I; Apply compact_part_hyp.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_minus.
Apply leEq_transitive with d.
2: Unfold d; Apply Min_leEq_lft.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply compact_leEq.
Apply less_leEq; Apply compact_less.
Qed.

Local Rolle_lemma5 : {i:nat & {H:(Cle i n) & [--]e[<](fcp' ? (Cle_to ?? H))}}.
Elim Rolle_lemma4; Intros i Hi; Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i; Exists (Clt_le_weak ?? Hi).
Step Zero[-]e; Apply shift_minus_less.
Apply less_wdr with (fcp' ? (lt_le_weak ?? (Clt_to ?? Hi)))[+]e.
EApply mult_cancel_less.
2: EApply less_wdl.
2: Apply Hi'.
2: Algebra.
Apply compact_less.
Unfold fcp'; Algebra.
Qed.

Local Rolle_lemma6 : {i:nat & {H:(Clt i n) & 
  (((fcp' ? (lt_le_weak ?? (Clt_to ?? H)))[-]e)[*]((cp (S i) (Cle_to ?? H))[-](cp i (lt_le_weak ?? (Cle_to ?? H)))))[<]Zero}}.
Apply negative_Sumx with f:=[i:nat][H:(lt i n)]((fcp' ? (lt_le_weak ?? H))[-]e)[*]((cp ? H)[-](cp ? (lt_le_weak ?? H))).
Red; Do 3 Intro.
Rewrite H; Intros.
Unfold fcp'; Algebra.
Apply less_wdr with (Sumx [i:nat][H:(lt i n)](fcp ? H)[-](fcp ? (lt_le_weak ?? H))).
2: Apply Rolle_lemma1.
Apply Sumx_resp_less.
Apply less_nring with (IR::COrdField); Simpl; Unfold n; Apply pos_compact_nat; Auto.
Intros.
Apply less_leEq_trans with ((fcp' ? (lt_le_weak ?? H))[-]e[/]TwoNZ)[*]((cp ? H)[-](cp ? (lt_le_weak ?? H))).
Apply mult_resp_less.
2: Apply compact_less.
Unfold cg_minus; Apply plus_resp_less_lft.
Apply inv_resp_less; Apply pos_div_two'; Assumption.
RStepr (fcp' ? (lt_le_weak ?? H))[*]((cp ? H)[-](cp ? (lt_le_weak ?? H)))[+]
  [--][--](((fcp ? H)[-](fcp ? (lt_le_weak ?? H)))[-](fcp' ? (lt_le_weak ?? H))[*]((cp ? H)[-](cp ? (lt_le_weak ?? H)))).
RStep 
  (fcp' ? (lt_le_weak ?? H))[*]((cp ? H)[-](cp ? (lt_le_weak ?? H)))[-](e[/]TwoNZ)[*]((cp ? H)[-](cp ? (lt_le_weak ?? H))).
Unfold 1 cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq; Apply leEq_wdr with (e[/]TwoNZ)[*](AbsIR (cp ? H)[-](cp ? (lt_le_weak ?? H))).
2: Apply mult_wd.
2: Algebra.
2: Apply AbsIR_eq_x.
2: Apply less_leEq; Apply compact_less.
EApply leEq_transitive.
Apply inv_leEq_AbsIR.
Unfold fcp fcp'; Apply Hf.
Unfold I; Apply compact_part_hyp.
Unfold I; Apply compact_part_hyp.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_minus.
Apply leEq_transitive with d.
2: Unfold d; Apply Min_leEq_lft.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply compact_leEq.
Apply less_leEq; Apply compact_less.
Qed.

Local Rolle_lemma7 : {i:nat & {H:(Cle i n) & (fcp' ? (Cle_to ?? H))[<]e}}.
Elim Rolle_lemma6; Intros i Hi; Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i; Exists (Clt_le_weak ?? Hi).
Stepr e[+]Zero; Apply shift_less_plus'.
Apply less_wdl with (fcp' ? (lt_le_weak ?? (Clt_to ?? Hi)))[-]e.
EApply mult_cancel_less.
2: EApply less_wdr.
2: Apply Hi'.
2: Algebra.
Apply shift_less_minus.
Step (cp ? (lt_le_weak ?? (Cle_to ?? Hi))).
Unfold compact_part.
Apply plus_resp_less_lft.
Apply mult_resp_less.
Simpl; Apply less_plusOne.
Apply div_resp_pos.
2: Apply shift_less_minus; Step a; Auto.
Apply pos_compact_nat; Auto.
Unfold fcp'; Algebra.
Qed.

Local j:=(ProjS1 Rolle_lemma5).

Local Hj := (ProjS1 (ProjS2 Rolle_lemma5)).

Local Hj' : [--]e[<](fcp' ? (Cle_to j ? Hj)).
Exact (ProjS2 (ProjS2 Rolle_lemma5)).
Qed.

Local k:=(ProjS1 Rolle_lemma7).

Local Hk:=(ProjS1 (ProjS2 Rolle_lemma7)).

Local Hk' : (fcp' ? (Cle_to k ? Hk))[<]e.
Exact (ProjS2 (ProjS2 Rolle_lemma7)).
Qed.

Local Rolle_lemma8 : (i:nat)(H:(le i n))(((AbsIR (fcp' ? H))[<]e)+(e[/]TwoNZ[<](AbsIR (fcp' ? H)))).
Intros.
Cut ((e[/]TwoNZ)[<](AbsIR (fcp' ? H)))+((AbsIR (fcp' ? H))[<]e).
Intro; Inversion_clear H0; [Right | Left]; Assumption.
Apply cotrans_less_unfolded.
Apply pos_div_two'; Assumption.
Qed.

Local Rolle_lemma9 : 
  {m:nat & {Hm:(Cle m n) & (((AbsIR (fcp' ? (Cle_to ?? Hm)))[<]e))}}+(i:nat)(H:(le i n))(e[/]TwoNZ[<](AbsIR (fcp' ? H))).
LetTac P := [i:nat][H:(le i n)]((AbsIR (fcp' ? H))[<]e).
LetTac Q := [i:nat][H:(le i n)]((e[/]TwoNZ)[<](AbsIR (fcp' ? H))).
Apply finite_or_elim with P:=P Q:=Q.
Red.
Intros i i' Hii'; Rewrite Hii'; Intros Hi Hi' HP.
Red; Red in HP.
EApply less_wdl.
Apply HP.
Apply AbsIR_wd; Unfold fcp'; Algebra.
Red.
Intros i i' Hii'; Rewrite Hii'; Intros Hi Hi' HQ.
Red; Red in HQ.
EApply less_wdr.
Apply HQ.
Apply AbsIR_wd; Unfold fcp'; Algebra.
Apply Rolle_lemma8.
Qed.

Local Rolle_lemma10 : {m:nat & {Hm:(Cle m n) & (((AbsIR (fcp' ? (Cle_to ?? Hm)))[<]e))}}->
  {x:IR & (I x) | (Hx:?)(AbsIR (F' x Hx))[<=]e}.
Intro.
Elim H; Intros m Hm; Elim Hm; Clear H Hm; Intros Hm Hm'.
Exists (cp ? (Cle_to ?? Hm)).
Red; Apply compact_part_hyp.
Intro; Apply less_leEq; EApply less_wdl.
Apply Hm'.
Apply AbsIR_wd; Unfold fcp'; Algebra.
Qed.

Local Rolle_lemma11 : ((i:nat)(H:(le i n))(e[/]TwoNZ[<](AbsIR (fcp' ? H))))->
  ((H:(le O n))((fcp' ? H)[<][--](e[/]TwoNZ)))->((i:nat)(H:(le i n))(fcp' ? H)[<]Zero).
Intros H H0.
Cut ((H:(le O n))(fcp' ? H)[<]Zero).
Intro.
Induction i.
Assumption.
Intros i' Hrec HSi'.
Stepr (e[/]TwoNZ)[-](e[/]TwoNZ).
Apply shift_less_minus.
Cut (le i' n).
2: Auto with arith.
Intro Hi'.
Apply less_leEq_trans with (fcp' ? HSi')[-](fcp' ? Hi').
Unfold cg_minus; Apply plus_resp_less_lft.
Cut ((e[/]TwoNZ)[<](fcp' ? Hi'))+((fcp' ? Hi')[<][--](e[/]TwoNZ)).
Intro.
Inversion_clear H2.
ElimType False.
Cut (e[/]TwoNZ)[<]Zero.
Apply less_antisymmetric_unfolded.
Apply pos_div_two; Assumption.
EApply less_transitive_unfolded; [Apply H3 | Apply Hrec].
Step [--][--](e[/]TwoNZ); Apply inv_resp_less; Assumption.
Cut (e[/]TwoNZ)[<](AbsIR (fcp' ? Hi')).
2: Exact (H i' Hi').
Intro.
Apply less_AbsIR.
Apply pos_div_two; Assumption.
Assumption.
EApply leEq_transitive.
Apply leEq_AbsIR.
Unfold fcp'; Apply Hf'.
Red; Apply compact_part_hyp.
Red; Apply compact_part_hyp.
Apply leEq_transitive with d.
2: Unfold d; Apply Min_leEq_rht.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply compact_leEq.
Apply less_leEq; Apply compact_less.
Intro.
EApply less_transitive_unfolded.
Apply (H0 H1).
Stepr [--](Zero::IR); Apply inv_resp_less; Apply pos_div_two; Assumption.
Qed.

Local Rolle_lemma12 : ((i:nat)(H:(le i n))(e[/]TwoNZ[<](AbsIR (fcp' ? H))))->
  ((H:(le O n))((e[/]TwoNZ)[<](fcp' ? H)))->((i:nat)(H:(le i n))Zero[<](fcp' ? H)).
Intros H H0.
Cut ((H:(le O n))(Zero[<](fcp' ? H))).
Intro.
Induction i.
Assumption.
Intros i' Hrec HSi'.
Step [--](Zero::IR); Stepr [--][--](fcp' ? HSi'); Apply inv_resp_less.
Stepr (e[/]TwoNZ)[-](e[/]TwoNZ).
Apply shift_less_minus'.
Step (e[/]TwoNZ)[-](fcp' ? HSi').
Cut (le i' n).
2: Auto with arith.
Intro Hi'.
Apply less_leEq_trans with (fcp' ? Hi')[-](fcp' ? HSi').
Unfold cg_minus; Apply plus_resp_less_rht.
Cut ((e[/]TwoNZ)[<](fcp' ? Hi'))+((fcp' ? Hi')[<][--](e[/]TwoNZ)).
Intro; Inversion_clear H2.
Assumption.
ElimType False.
Cut Zero[<][--](e[/]TwoNZ).
Apply less_antisymmetric_unfolded.
Stepr [--](Zero::IR); Apply inv_resp_less; Apply pos_div_two; Assumption.
EApply less_transitive_unfolded; [Apply (Hrec Hi') | Apply H3].
Cut (e[/]TwoNZ)[<](AbsIR (fcp' ? Hi')).
2: Exact (H i' Hi').
Intro.
Apply less_AbsIR.
Apply pos_div_two; Assumption.
Assumption.
EApply leEq_transitive.
Apply leEq_AbsIR.
Unfold fcp'; Apply Hf'.
Red; Apply compact_part_hyp.
Red; Apply compact_part_hyp.
Apply leEq_transitive with d.
2: Unfold d; Apply Min_leEq_rht.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_minus.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply compact_leEq.
Apply less_leEq; Apply compact_less.
Intro.
EApply less_transitive_unfolded.
2: Apply (H0 H1).
Apply pos_div_two; Assumption.
Qed.

Local Rolle_lemma13 : (((i:nat)(H:(le i n))(fcp' ? H)[<]Zero)+((i:nat)(H:(le i n))Zero[<](fcp' ? H)))->
  {x:IR & (I x) | (Hx:?)(AbsIR (F' x Hx))[<=]e}.
Intro; Inversion_clear H.
Exists (cp ? (Cle_to ?? Hj)).
Red; Apply compact_part_hyp.
Intro; Simpl; Unfold ABSIR; Apply Max_leEq.
Apply less_leEq; Apply less_transitive_unfolded with (Zero::IR).
EApply less_wdl.
Apply (H0 ? (Cle_to ?? Hj)).
Unfold fcp'; Algebra.
Assumption.
Stepr [--][--]e; Apply inv_resp_leEq.
Apply less_leEq; EApply less_wdr.
Apply Hj'.
Unfold fcp'; Algebra.
Exists (cp ? (Cle_to ?? Hk)).
Red; Apply compact_part_hyp.
Intros.
Simpl; Unfold ABSIR; Apply Max_leEq.
Apply less_leEq; EApply less_wdl.
Apply Hk'.
Unfold fcp'; Algebra.
Apply less_leEq; Apply less_transitive_unfolded with (Zero::IR).
Stepr [--](Zero::IR); Apply inv_resp_less; EApply less_wdr.
Apply (H0 ? (Cle_to ?? Hk)).
Unfold fcp'; Rational.
Assumption.
Qed.

Local Rolle_lemma15 : ((i:nat)(H:(le i n))(e[/]TwoNZ[<](AbsIR (fcp' ? H))))->
  ((fcp' ? (le_O_n n))[<][--](e[/]TwoNZ))+((e[/]TwoNZ)[<](fcp' ? (le_O_n n))).
Intro.
Cut ((e[/]TwoNZ)[<](fcp' ? (le_O_n n)))+((fcp' ? (le_O_n n))[<][--](e[/]TwoNZ)).
Intro; Inversion_clear H0; [Right | Left]; Assumption.
Apply less_AbsIR.
Apply pos_div_two; Assumption.
Apply H.
Qed.

(* Begin_Tex_Verb *)
Theorem Rolle : {x:IR & (I x) | (Hx:?)(AbsIR (F' x Hx))[<=]e}.
(* End_Tex_Verb *)
Elim Rolle_lemma9.
Exact Rolle_lemma10.
Intro.
Apply Rolle_lemma13.
Elim (Rolle_lemma15 b0).
Left; Apply Rolle_lemma11.
Assumption.
Intro.
EApply less_wdl.
Apply a0.
Unfold fcp'; Algebra.
Right; Apply Rolle_lemma12.
Assumption.
Intro.
EApply less_wdr.
Apply b1.
Unfold fcp'; Algebra.
Qed.

End Rolle.

Section Mean_Law.

(* Tex_Prose
The following is a simple corollary:
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

Variables F,F':PartIR.

Hypothesis HF:(Derivative_I Hab' F F').

Hypothesis HA:(Pred F a).
Hypothesis HB:(Pred F b).

(* Begin_Tex_Verb *)
Lemma Mean_Law_simple : (e:IR)(Zero[<]e)->{x:IR & (I x) | (Hx:?)
  ((AbsIR ((F b HB)[-](F a HA))[-](F' x Hx)[*](b[-]a))[<=]e)}.
(* End_Tex_Verb *)
Intros.
LetTac h:=(FId{-}({-C-}a)){*}({-C-}((F b HB)[-](F a HA))){-}F{*}({-C-}(b[-]a)).
LetTac h':=({-C-}((F b HB)[-](F a HA)){-}F'{*}({-C-}(b[-]a))).
Cut (Derivative_I Hab' h h').
Intro.
Cut {x:IR & (I x) | (Hx:?)(AbsIR (h' x Hx))[<=]e}.
Intro.
Elim H1; Intros x Ix Hx.
Exists x.
Assumption.
Intro.
EApply leEq_wdl.
Apply (Hx (derivative_imp_inc' ????? H0 x Ix)).
Apply AbsIR_wd; Simpl; Rational.
Unfold I Hab; EApply Rolle with 
  h (derivative_imp_inc ????? H0 ? (compact_inc_lft ???)) (derivative_imp_inc ????? H0 ? (compact_inc_rht ???)).
Assumption.
Simpl; Rational.
Assumption.
Unfold h h'; Clear h h'.
New_Deriv.
Apply Feq_reflexive.
Apply included_FMinus; Included.
Apply eq_imp_Feq.
Apply included_FMinus.
Apply included_FPlus; Included.
Included.
Included.
Intros.
Simpl; Rational.
Qed.

End Mean_Law.

Section Corollaries.

(* Tex_Prose
We can also state these theorems without expliciting the derivative of $F$.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Variable F:PartIR.

(* Begin_Tex_Verb *)
Hypothesis HF:(Diffble_I Hab' F).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Theorem Rolle' : ((Ha:?)(Hb:?)((F a Ha)[=](F b Hb)))->
  (e:IR)(Zero[<]e)->{x:IR & (Compact Hab x) |
    (Hx:?)(AbsIR ((PartInt (ProjS1 HF)) x Hx))[<=]e}.
(* End_Tex_Verb *)
Intros.
Unfold Hab.
Apply Rolle with F (diffble_imp_inc ???? HF ? (compact_inc_lft a b Hab)) (diffble_imp_inc ???? HF ? (compact_inc_rht a b Hab)).
Apply projS2.
Apply H.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Mean_Law'_simple : (HA,HB:?)(e:IR)(Zero[<]e)->
  {x:IR & (Compact Hab x) | (Hx:?)
  (AbsIR ((F b HB)[-](F a HA))[-]
    ((PartInt (ProjS1 HF)) x Hx)[*](b[-]a))[<=]e}.
(* End_Tex_Verb *)
Intros.
Unfold Hab.
Apply Mean_Law_simple.
Apply projS2.
Assumption.
Qed.

End Corollaries.

Section Generalizations.

(* Tex_Prose
The mean law is more useful if we abstract $a$ and $b$ from the context---allowing them in particular to be equal.  In the case where $F(a)=F(b)$ we get Rolle's theorem again, so there is no need to state it also in this form.

\begin{convention} Assume \verb!I! is a proper interval, \verb!F,F':PartIR!.
\end{convention}
*)

Variable I:interval.
Hypothesis pI:(proper I).

Variables F,F':PartIR.
(* Begin_Tex_Verb *)
Hypothesis derF:(Derivative I pI F F').
(* End_Tex_Verb *)

Local incF:=(Derivative_imp_inc ???? derF).
Local incF':=(Derivative_imp_inc' ???? derF).

(* Begin_Tex_Verb *)
Theorem Mean_Law : (a,b:IR)(iprop I a)->(iprop I b)->
  (e:IR)(Zero[<]e)->{x:IR & (Compact (Min_leEq_Max a b) x) |
    (Ha,Hb,Hx:?)(AbsIR ((F b Hb)[-](F a Ha))[-]
                         (F' x Hx)[*](b[-]a))[<=]e}.
(* End_Tex_Verb *)
Intros a b Ha Hb e He.
Cut (included (Compact (Min_leEq_Max a b)) (iprop I)); Intros.
2: Apply included_interval'; Auto.
Elim (cotrans_less_unfolded ??? He
  (AbsIR ((F b (incF ? Hb))[-](F a (incF ? Ha)))[-](F' a (incF' ? Ha))[*](b[-]a))); Intros.
Cut (Min a b)[<](Max a b); Intros.
Cut (included (Compact (less_leEq ??? H0)) (iprop I)); Intros.
2: Apply included_interval'; Auto.
Elim (ap_imp_less ??? (Min_less_Max_imp_ap ?? H0)); Intro.
Cut (included (Compact (less_leEq ??? a1)) (iprop I)); Intros.
2: Apply included_trans with (Compact (less_leEq ??? H0)); [Apply compact_map2 | Apply H1].
Elim (Mean_Law_simple ?? a1 ?? (included_imp_Derivative ???? derF ?? a1 H2) (incF ? Ha) (incF ? Hb) e He).
Intros x H3 H4.
Exists x; Auto.
Apply compact_map2 with Hab:=(less_leEq ??? a1); Auto.
Intros.
EApply leEq_wdl.
Apply (H4 Hx).
Apply AbsIR_wd; Algebra.
Cut (included (Compact (Min_leEq_Max b a)) (Compact (Min_leEq_Max a b))); Intros.
Cut (included (Compact (less_leEq ??? b0)) (iprop I)); Intros.
2: Apply included_trans with (Compact (Min_leEq_Max b a)); [Apply compact_map2 | 
  Apply included_trans with (Compact (less_leEq ??? H0)); [Apply H2 | Apply H1]].
Elim (Mean_Law_simple ?? b0 ?? (included_imp_Derivative ???? derF ?? b0 H3) (incF ? Hb) (incF ? Ha) e He).
Intros x H4 H5.
Exists x; Auto.
Apply H2; Apply compact_map2 with Hab:=(less_leEq ??? b0); Auto.
Intros.
EApply leEq_wdl.
Apply (H5 Hx).
EApply eq_transitive_unfolded.
Apply AbsIR_minus.
Apply AbsIR_wd; Rational.
Red; Intros.
Inversion_clear H2; Split.
EApply leEq_wdl; [Apply H3 | Apply Min_comm].
EApply leEq_wdr; [Apply H4 | Apply Max_comm].
Apply ap_imp_Min_less_Max.
Cut ((pfpfun ? ? (incF b Hb))[-](pfpfun ? ? (incF a Ha))[#]Zero)+((pfpfun ? ? (incF' a Ha))[*](b[-]a)[#]Zero).
Intro.
Inversion_clear H0.
Apply pfstrx with F (incF a Ha) (incF b Hb).
Apply ap_symmetric_unfolded; Apply zero_minus_apart; Auto.
Apply ap_symmetric_unfolded; Apply zero_minus_apart.
EApply cring_mult_ap_zero_op; Apply H1.
Apply cg_minus_strext.
Stepr (Zero::IR).
Apply AbsIR_cancel_ap_zero.
Apply Greater_imp_ap; Auto.
Exists a.
Apply compact_Min_lft.
Intros; Apply less_leEq.
EApply less_wdl.
Apply b0.
Apply AbsIR_wd; Algebra.
Qed.

(* Tex_Prose
We further generalize the mean law by writing as an explicit bound.
*)

(* Begin_Tex_Verb *)
Theorem Mean_Law_ineq : (a,b:IR)(iprop I a)->(iprop I b)->(c:IR)
  ((x:IR)(Compact (Min_leEq_Max a b) x)->(Hx:?)(AbsIR (F' x Hx))[<=]c)->
  (Ha,Hb:?)((F b Hb)[-](F a Ha))[<=]c[*](AbsIR b[-]a).
(* End_Tex_Verb *)
Intros a b Ia Ib c Hc Ha Hb.
Stepr c[*](AbsIR b[-]a)[+]Zero.
Apply shift_leEq_plus'.
Red; Apply approach_zero_weak.
Intros.
Elim Mean_Law with a b e; Auto.
Intros x H0 H1.
Cut (Pred F' x); Intros.
EApply leEq_transitive.
2: Apply (H1 Ha Hb H2).
EApply leEq_transitive.
2: Apply leEq_AbsIR.
Unfold 1 4 cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq.
EApply leEq_transitive.
Apply leEq_AbsIR.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_rht.
Auto.
Apply AbsIR_nonneg.
Apply (Derivative_imp_inc' ???? derF).
Exact (included_interval I a b Ia Ib (Min_leEq_Max a b) x H0).
Qed.

End Generalizations.
