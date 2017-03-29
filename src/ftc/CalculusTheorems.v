(* $Id: CalculusTheorems.v,v 1.23 2003/03/13 12:06:17 lcf Exp $ *)

Require Export Rolle.
Require Export MoreFunTactics.

Opaque Min Max.

Section Various_Theorems.

(* Tex_Prose
\chapter{Calculus Theorems}

This file is intended to present a collection of miscellaneous, mostly technical results in differential calculus that are interesting or useful in future work.

We begin with some properties of continuous functions.  Every continuous function commutes with the Limit of a numerical sequence (sometimes called Heine continuity).
*)

(* Begin_Tex_Verb *)
Lemma Continuous_imp_comm_Lim : (F,x,e:?)
  (Zero[<]e)->(Continuous (clcr (Lim x)[-]e (Lim x)[+]e) F)->
  (Hx,Hxn,H:?)((F (Lim x) Hx)[=]
    (Lim (Build_CauchySeq IR [n:nat](F (x n) (Hxn n)) H))).
(* End_Tex_Verb *)
Intros.
LetTac a:=(Lim x).
LetTac I:=(clcr a[-]e a[+]e).
Cut (compact_ I); Intros.
2: Simpl; Apply ts.
2: Apply less_leEq; Apply less_transitive_unfolded with a.
2: Apply shift_minus_less; Apply shift_less_plus'.
2: Step (Zero::IR); Auto.
2: Apply shift_less_plus'.
2: Step (Zero::IR); Auto.
Apply Limits_unique.
Simpl.
Red; Intros.
LetTac H2':=H2.
Simpl in H2'; Elim H2'; Clear H2'; Intro H2'.
Cut (!Continuous_I (Lend H2) (Rend H2) H2' F); Intros.
2: Apply Int_Continuous; Auto.
Elim (contin_prop ???? H4 ? H3); Intros d H5 H6.
Elim (Cauchy_complete x (Min d e)).
2: Apply less_Min; Auto.
Intros N HN.
Exists N; Intros.
Fold a in HN.
Apply AbsIR_imp_AbsSmall.
Elim (HN m H7); Intros.
Apply H6.
Split; Simpl.
Unfold cg_minus; Apply shift_plus_leEq'.
EApply leEq_transitive.
2: Apply H8.
Apply inv_resp_leEq; Apply Min_leEq_rht.
Apply shift_leEq_plus'.
EApply leEq_transitive.
Apply H9.
Apply Min_leEq_rht.
Split; Simpl.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Apply shift_leEq_plus'; Step (Zero::IR).
Apply less_leEq; Auto.
Apply AbsSmall_imp_AbsIR.
Apply AbsSmall_leEq_trans with (Min d e).
Apply Min_leEq_lft.
Auto.
Qed.

(* Tex_Prose
This is a tricky result: if $F$ is continuous and positive in both $[a,b]$ and $]b,c]$, then it is positive in $[a,c]$.
*)

(* Begin_Tex_Verb *)
Lemma Continuous_imp_pos : (a,b,c:IR)(Hac:a[<=]c)
  (a[<=]b)->(b[<]c)->(F:PartIR)(Continuous_I Hac F)->
  ((t:IR)(a[<=]t)->(t[<=]b)->(Ht:?)(Zero[<](F t Ht)))->
  ((t:IR)(b[<]t)->(t[<=]c)->(Ht:?)(Zero[<](F t Ht)))->
  ((t:IR)(a[<=]t)->(t[<=]c)->(Ht:?)(Zero[<](F t Ht))).
(* End_Tex_Verb *)
Intros.
Inversion_clear H1.
Cut (Compact Hac b); [Intro | Split; Auto].
2: Apply less_leEq; Auto.
LetTac e:=(F b (H6 ? H1))[/]TwoNZ.
Cut Zero[<]e; Intros.
2: Unfold e; Apply pos_div_two; Apply H2; Auto.
2: Apply leEq_reflexive.
Elim H7 with e; Auto.
Intros d H9 H10.
Cut b[-]d[<]b.
2: Apply shift_minus_less; Apply shift_less_plus'.
2: Step (Zero::IR); Auto.
Intro.
Elim (cotrans_less_unfolded ??? H11 t); Intro.
Clear H11.
Elim (cotrans_less_unfolded ??? H9 t[-]b); Intro.
Apply H3.
Step Zero[+]b; Apply shift_plus_less; Auto.
Auto.
Apply cont_no_sign_change_pos with Hab:=Hac e:=e Hx:=(H6 ? H1); Auto.
Split; Auto.
Apply H10; Auto.
Split; Auto.
Apply AbsSmall_imp_AbsIR.
Apply AbsIR_eq_AbsSmall.
RStepr [--](t[-]b); Apply inv_resp_leEq.
Apply less_leEq; Auto.
Apply less_leEq; Apply shift_minus_less; Apply shift_less_plus'; Auto.
Unfold e.
EApply less_leEq_trans.
Apply pos_div_two'.
Apply H2; Auto.
Apply leEq_reflexive.
Apply leEq_AbsIR.
Unfold e.
Apply pos_div_two'.
Apply H2; Auto.
Apply leEq_reflexive.
Apply H2; Auto.
Apply less_leEq; Auto.
Qed.

(* Tex_Prose
Similar results for increasing functions:
*)

(* Begin_Tex_Verb *)
Lemma strict_inc_glues : (a,b,c:IR)(F:PartIR)
  (Hab:a[<=]b)(Hbc:b[<=]c)(Hac:a[<=]c)
  (included (Compact Hac) (Pred F))->
  ((x,y:IR)(Compact Hab x)->(Compact Hab y)->
    (x[<]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  ((x,y:IR)(Compact Hbc x)->(Compact Hbc y)->
    (x[<]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  (x,y:IR)(Compact Hac x)->(Compact Hac y)->
    (x[<]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)).
(* End_Tex_Verb *)
Intros.
Cut (Pred F a); [Intro Ha | Apply H; Apply compact_inc_lft].
Cut (Pred F b); [Intro Hb | Apply H; Split; Auto].
Cut (Pred F c); [Intro Hc | Apply H; Apply compact_inc_rht].
Elim (cotrans_less_unfolded ??? H4 b); Intro.
Cut (Pred F (Min b y)); [Intro | Apply H; Split].
2: Apply leEq_Min; Auto; Elim H3; Auto.
2: EApply leEq_transitive; [Apply Min_leEq_lft | Auto].
Apply less_leEq_trans with (F ? H5).
Cut (Pred F (Min (x[+]b)[/]TwoNZ y)); [Intro Hxy | Apply H; Split].
3: Elim H3; Intros; EApply leEq_transitive; [Apply Min_leEq_rht | Auto].
2: Apply leEq_Min.
3: Elim H3; Auto.
2: Apply shift_leEq_div; [Apply pos_two | RStep a[+]a].
2: Apply plus_resp_leEq_both; Elim H2; Auto.
Apply less_leEq_trans with (F ? Hxy).
Apply H0; Try Split.
Elim H2; Auto.
Apply less_leEq; Auto.
Apply leEq_Min.
2: Elim H3; Auto.
Apply shift_leEq_div; [Apply pos_two | RStep a[+]a].
Apply plus_resp_leEq_both; Elim H2; Auto.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply shift_div_leEq; [Apply pos_two | RStepr b[+]b].
Apply plus_resp_leEq; Apply less_leEq; Auto.
Apply less_Min; Auto.
Apply shift_less_div; [Apply pos_two | RStep x[+]x].
Apply plus_resp_leEq_less; [Apply leEq_reflexive | Auto].
Apply part_mon_imp_mon' with (Compact Hab); Auto.
Intros; Apply H; Inversion_clear H6; Split; Auto.
Apply leEq_transitive with b; Auto.
Split.
Apply leEq_Min.
Apply shift_leEq_div; [Apply pos_two | RStep a[+]a].
Apply plus_resp_leEq_both; Auto; Elim H2; Auto.
Elim H3; Auto.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply shift_div_leEq; [Apply pos_two | RStepr b[+]b].
Apply plus_resp_leEq; Apply less_leEq; Auto.
Split.
Apply leEq_Min; Auto; Elim H3; Auto.
Apply Min_leEq_lft.
Apply leEq_Min.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply shift_div_leEq; [Apply pos_two | RStepr b[+]b].
Apply plus_resp_leEq; Apply less_leEq; Auto.
Apply Min_leEq_rht.
Intro.
Cut y[<=]b; Intro.
Apply (less_irreflexive_unfolded ? (F y Hy)).
EApply less_wdr.
Apply H6.
Apply pfwdef; EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft; Auto.
Apply (less_irreflexive_unfolded ? (F y Hy)).
EApply less_transitive_unfolded.
Apply H6.
Apply less_wdl with (F b Hb).
2: Apply pfwdef; Apply eq_symmetric_unfolded; Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
Apply H1; Auto.
Apply compact_inc_lft.
Split; [Apply less_leEq | Elim H3]; Auto.

Cut (Pred F (Max b x)); [Intro | Apply H; Split].
3: Apply Max_leEq; Auto; Elim H2; Auto.
2: EApply leEq_transitive; [Apply Hab | Apply lft_leEq_Max].
Apply leEq_less_trans with (F ? H5).
2: Cut (Pred F (Max (y[+]b)[/]TwoNZ x)); [Intro Hxy | Apply H; Split].
3: Elim H2; Intros; EApply leEq_transitive; [Apply a0 | Apply rht_leEq_Max].
3: Apply Max_leEq.
4: Elim H2; Auto.
3: Apply shift_div_leEq; [Apply pos_two | RStepr c[+]c].
3: Apply plus_resp_leEq_both; Elim H3; Auto.
2: Apply leEq_less_trans with (F ? Hxy).
3: Apply H1; Try Split.
6: Elim H3; Auto.
5: Apply less_leEq; Auto.
4: Apply Max_leEq.
5: Elim H2; Auto.
4: Apply shift_div_leEq; [Apply pos_two | RStepr c[+]c].
4: Apply plus_resp_leEq_both; Elim H3; Auto.
3: EApply leEq_transitive.
4: Apply lft_leEq_Max.
3: Apply shift_leEq_div; [Apply pos_two | RStep b[+]b].
3: Apply plus_resp_leEq; Apply less_leEq; Auto.
3: Apply Max_less; Auto.
3: Apply shift_div_less; [Apply pos_two | RStepr y[+]y].
3: Apply plus_resp_less_lft; Auto.
2: Apply part_mon_imp_mon' with (Compact Hbc); Auto.
2: Intros; Apply H; Inversion_clear H6; Split; Auto.
2: Apply leEq_transitive with b; Auto.
3: Split.
4: Apply Max_leEq.
4: Apply shift_div_leEq; [Apply pos_two | RStepr c[+]c].
4: Apply plus_resp_leEq_both; Auto; Elim H3; Auto.
4: Elim H2; Auto.
3: EApply leEq_transitive.
4: Apply lft_leEq_Max.
3: Apply shift_leEq_div; [Apply pos_two | RStep b[+]b].
3: Apply plus_resp_leEq; Apply less_leEq; Auto.
2: Split.
3: Apply Max_leEq; Auto; Elim H2; Auto.
2: Apply lft_leEq_Max.
2: Apply Max_leEq.
2: EApply leEq_transitive.
3: Apply lft_leEq_Max.
2: Apply shift_leEq_div; [Apply pos_two | RStep b[+]b].
2: Apply plus_resp_leEq; Apply less_leEq; Auto.
2: Apply rht_leEq_Max.
Intro.
Cut b[<=]x; Intro.
Apply (less_irreflexive_unfolded ? (F x Hx)).
EApply less_wdl.
Apply H6.
Apply pfwdef; Apply leEq_imp_Max_is_rht; Auto.
Apply (less_irreflexive_unfolded ? (F x Hx)).
EApply less_transitive_unfolded.
2: Apply H6.
Apply less_wdr with (F b Hb).
2: Apply pfwdef; Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply Max_comm.
2: Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Apply H0; Auto.
2: Apply compact_inc_rht.
Split; [Elim H2 | Apply less_leEq]; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma strict_inc_glues' : (a,b,c:IR)(F:PartIR)
  (a[<]b)->(b[<]c)->
  (included (iprop (olor a c)) (Pred F))->
  ((x,y:IR)(iprop (olcr a b) x)->(iprop (olcr a b) y)->
    (x[<]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  ((x,y:IR)(iprop (clor b c) x)->(iprop (clor b c) y)->
    (x[<]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  (x,y:IR)(iprop (olor a c) x)->(iprop (olor a c) y)->
    (x[<]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)).
(* End_Tex_Verb *)
Intros a b c F Hab Hbc; Intros.
Cut (Pred F b); [Intro Hb | Apply H; Split; Auto].
Elim (cotrans_less_unfolded ??? H4 b); Intro.
Cut (Pred F (Min b y)); [Intro | Apply H; Split].
2: Apply less_Min; Auto; Elim H3; Auto.
2: EApply leEq_less_trans; [Apply Min_leEq_lft | Auto].
Apply less_leEq_trans with (F ? H5).
Cut (Pred F (Min (x[+]b)[/]TwoNZ y)); [Intro Hxy | Apply H; Split].
3: Elim H3; Intros; EApply leEq_less_trans; [Apply Min_leEq_rht | Auto].
2: Apply less_Min.
3: Elim H3; Auto.
2: Apply shift_less_div; [Apply pos_two | RStep a[+]a].
2: Apply plus_resp_less_both; Elim H2; Auto.
Apply less_leEq_trans with (F ? Hxy).
Apply H0; Try Split.
Elim H2; Auto.
Apply less_leEq; Auto.
Apply less_Min.
2: Elim H3; Auto.
Apply shift_less_div; [Apply pos_two | RStep a[+]a].
Apply plus_resp_less_both; Elim H2; Auto.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply shift_div_leEq; [Apply pos_two | RStepr b[+]b].
Apply plus_resp_leEq; Apply less_leEq; Auto.
Apply less_Min; Auto.
Apply shift_less_div; [Apply pos_two | RStep x[+]x].
Apply plus_resp_leEq_less; [Apply leEq_reflexive | Auto].
Apply part_mon_imp_mon' with (iprop (olcr a b)); Auto.
Intros; Apply H; Inversion_clear H6; Split; Auto.
Apply leEq_less_trans with b; Auto.
Split.
Apply less_Min.
Apply shift_less_div; [Apply pos_two | RStep a[+]a].
Apply plus_resp_less_both; Auto; Elim H2; Auto.
Elim H3; Auto.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply shift_div_leEq; [Apply pos_two | RStepr b[+]b].
Apply plus_resp_leEq; Apply less_leEq; Auto.
Split.
Apply less_Min; Auto; Elim H3; Auto.
Apply Min_leEq_lft.
Apply leEq_Min.
EApply leEq_transitive.
Apply Min_leEq_lft.
Apply shift_div_leEq; [Apply pos_two | RStepr b[+]b].
Apply plus_resp_leEq; Apply less_leEq; Auto.
Apply Min_leEq_rht.
Intro.
Cut y[<=]b; Intro.
Apply (less_irreflexive_unfolded ? (F y Hy)).
EApply less_wdr.
Apply H6.
Apply pfwdef; EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft; Auto.
Apply (less_irreflexive_unfolded ? (F y Hy)).
EApply less_transitive_unfolded.
Apply H6.
Apply less_wdl with (F b Hb).
2: Apply pfwdef; Apply eq_symmetric_unfolded; Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
Apply H1; Auto.
Split; Auto; Apply leEq_reflexive.
Split; [Apply less_leEq | Elim H3]; Auto.

Cut (Pred F (Max b x)); [Intro | Apply H; Split].
3: Apply Max_less; Auto; Elim H2; Auto.
2: EApply less_leEq_trans; [Apply Hab | Apply lft_leEq_Max].
Apply leEq_less_trans with (F ? H5).
2: Cut (Pred F (Max (y[+]b)[/]TwoNZ x)); [Intro Hxy | Apply H; Split].
3: Elim H2; Intros; EApply less_leEq_trans; [Apply a0 | Apply rht_leEq_Max].
3: Apply Max_less.
4: Elim H2; Auto.
3: Apply shift_div_less; [Apply pos_two | RStepr c[+]c].
3: Apply plus_resp_less_both; Elim H3; Auto.
2: Apply leEq_less_trans with (F ? Hxy).
3: Apply H1; Try Split.
6: Elim H3; Auto.
5: Apply less_leEq; Auto.
4: Apply Max_less.
5: Elim H2; Auto.
4: Apply shift_div_less; [Apply pos_two | RStepr c[+]c].
4: Apply plus_resp_less_both; Elim H3; Auto.
3: EApply leEq_transitive.
4: Apply lft_leEq_Max.
3: Apply shift_leEq_div; [Apply pos_two | RStep b[+]b].
3: Apply plus_resp_leEq; Apply less_leEq; Auto.
3: Apply Max_less; Auto.
3: Apply shift_div_less; [Apply pos_two | RStepr y[+]y].
3: Apply plus_resp_less_lft; Auto.
2: Apply part_mon_imp_mon' with (iprop (clor b c)); Auto.
2: Intros; Apply H; Inversion_clear H6; Split; Auto.
2: Apply less_leEq_trans with b; Auto.
3: Split.
4: Apply Max_less.
4: Apply shift_div_less; [Apply pos_two | RStepr c[+]c].
4: Apply plus_resp_less_both; Auto; Elim H3; Auto.
4: Elim H2; Auto.
3: EApply leEq_transitive.
4: Apply lft_leEq_Max.
3: Apply shift_leEq_div; [Apply pos_two | RStep b[+]b].
3: Apply plus_resp_leEq; Apply less_leEq; Auto.
2: Split.
3: Apply Max_less; Auto; Elim H2; Auto.
2: Apply lft_leEq_Max.
2: Apply Max_leEq.
2: EApply leEq_transitive.
3: Apply lft_leEq_Max.
2: Apply shift_leEq_div; [Apply pos_two | RStep b[+]b].
2: Apply plus_resp_leEq; Apply less_leEq; Auto.
2: Apply rht_leEq_Max.
Intro.
Cut b[<=]x; Intro.
Apply (less_irreflexive_unfolded ? (F x Hx)).
EApply less_wdl.
Apply H6.
Apply pfwdef; Apply leEq_imp_Max_is_rht; Auto.
Apply (less_irreflexive_unfolded ? (F x Hx)).
EApply less_transitive_unfolded.
2: Apply H6.
Apply less_wdr with (F b Hb).
2: Apply pfwdef; Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply Max_comm.
2: Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Apply H0; Auto.
Split; [Elim H2 | Apply less_leEq]; Auto.
Split; Auto; Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma strict_dec_glues : (a,b,c:IR)(F:PartIR)
  (Hab:a[<=]b)(Hbc:b[<=]c)(Hac:a[<=]c)
  (included (Compact Hac) (Pred F))->
  ((x,y:IR)(Compact Hab x)->(Compact Hab y)->
    (x[>]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  ((x,y:IR)(Compact Hbc x)->(Compact Hbc y)->
    (x[>]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  (x,y:IR)(Compact Hac x)->(Compact Hac y)->
    (x[>]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)).
(* End_Tex_Verb *)
Intros.
Apply inv_cancel_less.
Step ({--}F y Hy); Stepr ({--}F x Hx).
Apply strict_inc_glues with a b c Hab Hbc Hac; Auto.
Intros; Simpl; Apply inv_resp_less; Auto.
Intros; Simpl; Apply inv_resp_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma strict_dec_glues' : (a,b,c:IR)(F:PartIR)
  (a[<]b)->(b[<]c)->
  (included (iprop (olor a c)) (Pred F))->
  ((x,y:IR)(iprop (olcr a b) x)->(iprop (olcr a b) y)->
    (x[>]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  ((x,y:IR)(iprop (clor b c) x)->(iprop (clor b c) y)->
    (x[>]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)))->
  (x,y:IR)(iprop (olor a c) x)->(iprop (olor a c) y)->
    (x[>]y)->(Hx,Hy:?)((F x Hx)[<](F y Hy)).
(* End_Tex_Verb *)
Intros.
Apply inv_cancel_less.
Step ({--}F y Hy); Stepr ({--}F x Hx).
Apply strict_inc_glues' with a b c; Auto.
Intros; Simpl; Apply inv_resp_less; Auto.
Intros; Simpl; Apply inv_resp_less; Auto.
Qed.

(* Tex_Prose
More on glueing intervals.
*)

(* Begin_Tex_Verb *)
Lemma olor_pos_clor_nonneg : (a,b:IR)(F:PartIR)
  ((x:IR)(iprop (olor a b) x)->(Hx:?)(Zero[<](F x Hx)))->
  (Ha:?)(Zero[<=](F a Ha))->
  (x:IR)(iprop (clor a b) x)->(Hx:?)(Zero[<=](F x Hx)).
(* End_Tex_Verb *)
Intros; Intro.
Cut (Not (iprop (olor a b) x)); Intro.
Cut x[=]a; Intros.
Apply H0.
EApply less_wdl; [Apply H2 | Algebra].
Red in H3.
Apply not_ap_imp_eq; Intro.
Inversion_clear H1.
Elim (ap_imp_less ??? H4); Intros.
Apply (less_irreflexive_unfolded ? a); Apply leEq_less_trans with x; Auto.
Apply H3; Split; Auto.
Apply (less_irreflexive_unfolded IR Zero); Apply less_transitive_unfolded with (F x Hx); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma olor_pos_olcr_nonneg : (a,b:IR)(F:PartIR)
  ((x:IR)(iprop (olor a b) x)->(Hx:?)(Zero[<](F x Hx)))->
  (Hb:?)(Zero[<=](F b Hb))->
  (x:IR)(iprop (olcr a b) x)->(Hx:?)(Zero[<=](F x Hx)).
(* End_Tex_Verb *)
Intros; Intro.
Cut (Not (iprop (olor a b) x)); Intro.
Cut x[=]b; Intros.
Apply H0.
EApply less_wdl; [Apply H2 | Algebra].
Red in H3.
Apply not_ap_imp_eq; Intro.
Inversion_clear H1.
Elim (ap_imp_less ??? H4); Intros.
Apply H3; Split; Auto.
Apply (less_irreflexive_unfolded ? b); Apply less_leEq_trans with x; Auto.
Apply (less_irreflexive_unfolded IR Zero); Apply less_transitive_unfolded with (F x Hx); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma olor_pos_clcr_nonneg : (a,b:IR)(F:PartIR)(a[<]b)->
  ((x:IR)(iprop (olor a b) x)->(Hx:?)(Zero[<](F x Hx)))->
  (Ha:?)(Zero[<=](F a Ha))->(Hb:?)(Zero[<=](F b Hb))->
  (x:IR)(iprop (clcr a b) x)->(Hx:?)(Zero[<=](F x Hx)).
(* End_Tex_Verb *)
Intros a b F Hab; Intros; Intro.
Cut (Not (iprop (olor a b) x)); Intro.
Elim (cotrans_less_unfolded ??? Hab x); Intro.
Cut (x[=]b); Intros.
Apply H1.
EApply less_wdl; [Apply H3 | Algebra].
Red in H4.
Apply not_ap_imp_eq; Intro.
Inversion_clear H2.
Elim (ap_imp_less ??? H5); Intros.
Apply H4; Split; Auto.
Apply (less_irreflexive_unfolded ? b); Apply less_leEq_trans with x; Auto.
Cut (x[=]a); Intros.
Apply H0.
EApply less_wdl; [Apply H3 | Algebra].
Red in H4.
Apply not_ap_imp_eq; Intro.
Inversion_clear H2.
Elim (ap_imp_less ??? H5); Intros.
Apply (less_irreflexive_unfolded ? a); Apply leEq_less_trans with x; Auto.
Apply H4; Split; Auto.
Apply (less_irreflexive_unfolded IR Zero); Apply less_transitive_unfolded with (F x Hx); Auto.
Qed.

(* Tex_Prose
Any function that has the null function as its derivative must be constant.
*)

(* Begin_Tex_Verb *)
Lemma FConst_prop :
  (J,pJ:?)(F':PartIR)(Derivative J pJ F' {-C-}Zero)->
    {c:IR & (Feq (iprop J) F' {-C-}c)}.
(* End_Tex_Verb *)
Intros.
Elim (nonvoid_point ? (proper_nonvoid ? pJ)); Intros x0 Hx0.
Exists (F' x0 (Derivative_imp_inc ???? H x0 Hx0)).
FEQ.
Simpl.
Apply cg_inv_unique_2.
Apply AbsIR_approach_zero; Intros.
Simpl in Hx'.
Elim (Mean_Law ???? H ?? Hx0 H0 e H1).
Intros y H2 H3.
EApply leEq_wdl.
Apply (H3 (Derivative_imp_inc ???? H ? Hx0) Hx CI).
Apply AbsIR_wd; Simpl; Rational.
Qed.

(* Tex_Prose
As a corollary, two functions with the same derivative must differ by a constant.
*)

(* Begin_Tex_Verb *)
Lemma Feq_crit_with_const : (J,pJ,F,G,H:?)
  (Derivative J pJ F H)->(Derivative J pJ G H)->
    {c:IR & (Feq (iprop J) F{-}G {-C-}c)}.
(* End_Tex_Verb *)
Intros.
Apply FConst_prop with pJ.
Derivative_Help; FEQ.
Qed.

(* Tex_Prose
This yields the following known result: any differential equation of the form $f'=g$ with initial condition $f(a)=b$ has a unique solution.
*)

(* Begin_Tex_Verb *)
Lemma Feq_criterium : (J,pJ,F,G,H:?)
  (Derivative J pJ F H)->(Derivative J pJ G H)->
  (x:IR)((iprop J x)->((Hx,Hx':?)(F x Hx)[=](G x Hx'))->
    (Feq (iprop J) F G)).
(* End_Tex_Verb *)
Intros.
Elim (Feq_crit_with_const ????? H0 H1); Intros c Hc.
Apply Feq_transitive with (F{-}G){+}G.
FEQ.
Apply Feq_transitive with {-C-}Zero{+}G.
2: FEQ.
Apply Feq_plus.
2: Apply Feq_reflexive; Included.
Apply Feq_transitive with {-C-}c.
Auto.
FEQ.
Simpl.
Inversion_clear Hc.
Clear H5 Hx' Hx.
Simpl in H6.
Cut (Conj (Pred F) (Pred G) x); Intros.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply H6 with Hx:=H5; Auto.
Apply eq_symmetric_unfolded; Apply x_minus_x; Auto.
Split.
Exact (Derivative_imp_inc ???? H0 ? H2).
Exact (Derivative_imp_inc ???? H1 ? H2).
Qed.

(* Tex_Prose
Finally, a well known result: any function with a (strictly) positive derivative is (strictly) increasing.  Although the two lemmas look quite similar the proofs are completely different, both from the formalization and from the mathematical point of view.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_imp_resp_less : (J,pJ,a,b,F,F':?)
  (Derivative J pJ F F')->(a[<]b)->(iprop J a)->(iprop J b)->
  ((contF':?)Zero[<](glb_funct ?? (Min_leEq_Max a b) F' contF'))->
    (Ha,Hb:?)(F a Ha)[<](F b Hb).
(* End_Tex_Verb *)
Intros J pJ a b F F' derF Hab HaJ HbJ Hglb Ha Hb.
Step Zero[+](pfpfun ? ? Ha); Apply shift_plus_less.
Cut (Continuous_I (Min_leEq_Max a b) F'); Intros.
2: Apply included_imp_Continuous with J; [Apply Derivative_imp_Continuous' with pJ F | Apply included_interval]; Auto.
Elim (glb_is_glb ???? H).
Simpl; Intros Hglb1 Hglb2.
Cut Zero[<](glb_funct ???? H); [Intro | Auto].
Elim (Mean_Law ???? derF a b) with e:=((glb_funct ???? H)[*](b[-]a))[/]TwoNZ; Auto.
Intros x H1 H2.
Apply less_leEq_trans with (F' x (contin_imp_inc ???? H x H1))[*](b[-]a)[-]((glb_funct ???? H)[*](b[-]a))[/]TwoNZ.
RStepr ((F' x (contin_imp_inc ???? H x H1))[-](glb_funct ???? H)[/]TwoNZ)[*](b[-]a).
Apply mult_resp_pos.
Apply shift_less_minus; Step (glb_funct ???? H)[/]TwoNZ.
EApply less_leEq_trans.
Apply pos_div_two'; Auto.
Auto.
Apply shift_less_minus; Step a; Auto.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
RStep [--](((pfpfun ? ? Hb)[-](pfpfun ? ? Ha))[-](pfpfun ? ? (contin_imp_inc ???? H ? H1))[*](b[-]a)).
EApply leEq_transitive.
Apply inv_leEq_AbsIR.
Apply H2.
Apply pos_div_two; Apply mult_resp_pos; Auto.
Apply shift_less_minus; Step a; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_imp_resp_leEq : (J,pJ,a,b,F,F':?)
  (Derivative J pJ F F')->(a[<=]b)->(iprop J a)->(iprop J b)->
  ((contF':?)Zero[<=](glb_funct ?? (Min_leEq_Max b a) F' contF'))->
    (Ha,Hb:?)(F a Ha)[<=](F b Hb).
(* End_Tex_Verb *)
Intros J pJ a b F F' derF Hab HaJ HbJ Hglb Ha Hb.
Stepr Zero[+](pfpfun ? ? Hb); Apply shift_leEq_plus.
Cut (Continuous_I (Min_leEq_Max b a) F'); Intros.
2: Apply included_imp_Continuous with J; [Apply Derivative_imp_Continuous' with pJ F | Apply included_interval]; Auto.
Elim (glb_is_glb ???? H).
Simpl; Intros Hglb1 Hglb2.
Cut Zero[<=](glb_funct ???? H); [Intro | Auto].
Red; Apply approach_zero_weak.
Intros.
Elim (Mean_Law ???? derF b a) with e:=e; Auto.
Intros x H2 H3.
EApply leEq_transitive.
2: Apply (H3 Hb Ha (contin_imp_inc ???? H x H2)).
EApply leEq_transitive.
2: Apply leEq_AbsIR.
RStep ((pfpfun ? ? Ha)[-](pfpfun ? ? Hb))[-][--]Zero.
Unfold 1 3 cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq.
RStep [--]((pfpfun ? ? (contin_imp_inc ???? H ? H2))[*](b[-]a)).
Apply inv_resp_leEq.
Apply mult_resp_nonneg.
EApply leEq_transitive; [Apply H0 | Apply Hglb1].
Apply shift_leEq_minus; Step a; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_imp_resp_less' : (J,pJ,a,b,F,F':?)
  (Derivative J pJ F F')->(a[<]b)->
  (iprop J a)->(iprop J b)->
  ((contF':?)(Zero[<=](glb_funct ?? (Min_leEq_Max b a) F' contF')))->
  (Ha,Hb:?)(((F a Ha)[#](F b Hb))->(F a Ha)[<](F b Hb)).
(* End_Tex_Verb *)
Intros.
Elim (ap_imp_less ??? H4); Intro; Auto.
ElimType False.
Apply less_irreflexive_unfolded with x:=(F a Ha).
Apply leEq_less_trans with (F b Hb); Auto.
Apply Derivative_imp_resp_leEq with J pJ F'; Auto.
Apply less_leEq; Auto.
Qed.

(* Tex_Prose
From these results we can finally prove that exponentiation to a real power preserves the less or equal than relation!
*)

(* Begin_Tex_Verb *)
Lemma nexp_resp_leEq_odd : (n:nat)
  (odd n)->(x,y:IR)(x[<=]y)->(x[^]n)[<=](y[^]n).
(* End_Tex_Verb *)
Intro; Case n.
Intros; ElimType False; Inversion H.
Clear n; Intros.
Step (Part FId{^}(S n) x CI).
Stepr (Part FId{^}(S n) y CI).
Apply Derivative_imp_resp_leEq with realline CI (!nring IR (S n)){**}(FId{^}n).
Opaque nring.
Derivative_Help.
FEQ.
Transparent nring.
Auto.
Split.
Split.
Intros.
Apply leEq_glb; Intros.
Simpl.
Apply mult_resp_nonneg.
Apply less_leEq; EApply leEq_less_trans.
2: Apply less_plusOne.
Apply nring_nonneg.
Stepr y0[^]n; Apply nexp_even_nonneg.
Inversion H; Auto.
Qed.

End Various_Theorems.
