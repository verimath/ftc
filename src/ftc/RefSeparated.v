(* $Id: RefSeparated.v,v 1.12 2003/03/13 12:06:22 lcf Exp $ *)

Require Export IntegralLemmas.

Section Separating__Separated.

Variables a,b:IR.
Hypothesis Hab:(a[<=]b).
Local I:=(compact a b Hab).

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis incF:(included (Compact Hab) (Pred F)).

Hypothesis Hab':a[<]b.
Variables m,n:nat.
Variable P:(Partition Hab n).
Variable R:(Partition Hab m).

Hypothesis HP : (_Separated P).
Hypothesis HR : (_Separated R).

Local pos_n : (lt O n).
Apply partition_less_imp_gt_zero with a b Hab; Assumption.
Qed.

Local pos_m : (lt O m).
Apply partition_less_imp_gt_zero with a b Hab; Assumption.
Qed.

Variable alpha : IR.
Hypothesis Halpha : Zero[<]alpha.

Local e:=(alpha[/]TwoNZ)[/]?[//](max_one_ap_zero b[-]a).

Local He:Zero[<]e.
Unfold e; Apply div_resp_pos.
Apply pos_max_one.
Apply pos_div_two; Assumption.
Qed.

Local contF' := (contin_prop ???? contF).

Local d : IR.
Elim (contF' e He).
Intros; Apply x.
Defined.

Local Hd:Zero[<]d.
Unfold d; Elim (contF' e He); Auto.
Qed.

Local Hd' : (x,y:IR)(I x)->(I y)->(Hx,Hy:?)((AbsIR x[-]y)[<=]d)->(AbsIR (Part F x Hx)[-](Part F y Hy))[<=]e.
Unfold d; Elim (contF' e He); Auto.
Qed.

Variable csi : IR.
Hypothesis Hcsi : Zero[<]csi.

Local M:=(Norm_Funct contF).

Local deltaP:=(AntiMesh P).
Local deltaR:=(AntiMesh R).
Local delta:=(Min (Min deltaP deltaR) (Min (alpha[/]TwoNZ)[/]?[//](max_one_ap_zero (nring n)[*]M) (Min csi d))).

Local delta_deltaP : delta[<=]deltaP.
Unfold delta; EApply leEq_transitive.
Apply Min_leEq_lft.
Apply Min_leEq_lft.
Qed.

Local delta_deltaR : delta[<=]deltaR.
Unfold delta; EApply leEq_transitive.
Apply Min_leEq_lft.
Apply Min_leEq_rht.
Qed.

Local delta_csi : delta[<=]csi.
Unfold delta; EApply leEq_transitive.
Apply Min_leEq_rht.
EApply leEq_transitive.
Apply Min_leEq_rht.
Apply Min_leEq_lft.
Qed.

Local delta_d : delta[<=]d.
Unfold delta; EApply leEq_transitive.
Apply Min_leEq_rht.
EApply leEq_transitive; Apply Min_leEq_rht.
Qed.

Local pos_delta : (Zero[<]delta).
Unfold delta; Apply less_Min; Apply less_Min.
Unfold deltaP; Apply pos_AntiMesh; [Apply pos_n | Assumption].
Unfold deltaR; Apply pos_AntiMesh; [Apply pos_m | Assumption].
Apply div_resp_pos.
Apply pos_max_one.
Apply pos_div_two; Assumption.
Apply less_Min.
Assumption.
Apply Hd.
Qed.

Section Defining_ai'.

Variable i:nat.
Hypothesis Hi:(le i n).

Local separation_conseq : (j:nat)(Hj:(le j m))((AbsIR (Pts P i Hi)[-](Pts R j Hj))[<]delta[/]TwoNZ)->
    (j':nat)~j=j'->(Hj':(le j' m))((delta[/]TwoNZ)[<](AbsIR (Pts P i Hi)[-](Pts R j' Hj'))).
Intros.
Elim (Cnat_total_order ?? H0); Clear H0; Intro H0.
Elim (le_lt_dec j' m); Intro.
Cut (le (S j) m); [Intro | Clear H; Apply le_trans with j'; Auto].
EApply less_wdr.
2: Apply AbsIR_minus.
Cut (Pts R (S j) H1)[<=](Pts R j' Hj'); Intros.
EApply less_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
RStepr ((Pts R ? Hj')[-](Pts R ? H1))[+]((Pts R ? H1)[-](Pts R ? Hj))[+]((Pts R ? Hj)[-](Pts P i Hi)).
RStep Zero[+]delta[+][--]delta[/]TwoNZ.
Apply plus_resp_leEq_less.
Apply plus_resp_leEq_both.
Apply shift_leEq_minus; Step (Pts R ? H1).
Assumption.
Apply leEq_transitive with deltaR.
Apply delta_deltaR.
Unfold deltaR; Apply AntiMesh_lemma.
RStep [--](delta[/]TwoNZ).
RStepr [--]((Pts P i Hi)[-](Pts R j Hj)).
Apply inv_resp_less.
EApply leEq_less_trans.
Apply leEq_AbsIR.
Assumption.
Apply shift_leEq_minus; Step (Pts P i Hi).
EApply leEq_transitive.
2: Apply H2.
Apply less_leEq; Apply less_transitive_unfolded with (Pts R j Hj)[+]delta[/]TwoNZ.
Apply shift_less_plus'.
EApply leEq_less_trans; [Apply leEq_AbsIR | Apply H].
Apply shift_plus_less'.
Apply less_leEq_trans with delta.
Apply pos_div_two'; Exact pos_delta.
Apply leEq_transitive with deltaR.
Apply delta_deltaR.
Unfold deltaR; Apply AntiMesh_lemma.
Apply local_mon_imp_mon'_le with f:=[i:nat][Hi:(le i m)](Pts R i Hi).
Intros; Apply HR.
Red; Intros; Apply prf1; Auto.
Assumption.
ElimType False; Apply (le_not_lt j' m); Auto.
Elim (le_lt_dec j O); Intro.
ElimType False; Apply lt_n_O with j'; Red; Apply le_trans with j; Auto.
Generalize Hj H H0; Clear H0 H Hj.
LetTac jj:=(pred j).
Cut j=(S jj); [Intro | Unfold jj; Apply S_pred with O; Auto].
Rewrite H; Intros.
Cut (le jj m); [Intro | Auto with arith].
Cut (Pts R j' Hj')[<=](Pts R jj H2); Intros.
EApply less_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
RStepr ((Pts P i Hi)[-](Pts R ? Hj))[+]((Pts R ? Hj)[-](Pts R jj H2))[+]((Pts R jj H2)[-](Pts R j' Hj')).
RStep [--](delta[/]TwoNZ)[+]delta[+]Zero.
Apply plus_resp_less_leEq.
Apply plus_resp_less_leEq.
EApply less_wdr.
2: Apply cg_inv_inv.
Apply inv_resp_less; EApply leEq_less_trans.
2: Apply H0.
Apply inv_leEq_AbsIR.
EApply leEq_transitive.
Apply delta_deltaR.
Unfold deltaR; Apply AntiMesh_lemma.
Apply shift_leEq_minus; EApply leEq_wdl.
Apply H3.
Algebra.
Apply shift_leEq_minus; Step (Pts R j' Hj').
EApply leEq_transitive.
Apply H3.
Apply less_leEq; Apply less_transitive_unfolded with (Pts R ? Hj)[-]delta[/]TwoNZ.
Apply shift_less_minus; Apply shift_plus_less'.
Apply less_leEq_trans with delta.
Apply pos_div_two'; Exact pos_delta.
EApply leEq_transitive.
Apply delta_deltaR.
Unfold deltaR; Apply AntiMesh_lemma.
Apply shift_minus_less; Apply shift_less_plus'.
EApply leEq_less_trans.
2: Apply H0.
EApply leEq_wdr.
2: Apply AbsIR_minus.
Apply leEq_AbsIR.
Apply local_mon_imp_mon'_le with f:=[i:nat][Hi:(le i m)](Pts R i Hi).
Intros; Apply HR.
Red; Intros; Apply prf1; Auto.
Auto with arith.
Qed.

Local pred1:=[j:nat][Hj:(le j m)](Hi':(le i n))(AbsIR (Pts P i Hi')[-](Pts R j Hj))[<]delta[/]TwoNZ.
Local pred2:=[j:nat][Hj:(le j m)](Hi':(le i n))delta[/]FourNZ[<](AbsIR (Pts P i Hi')[-](Pts R j Hj)).

Lemma sep__sep_aux_lemma : {j:nat & {Hj:(Cle j m) & (pred1 j (Cle_to ?? Hj))}}+(j:nat)(Hj:(le j m))(pred2 j Hj).
Apply finite_or_elim.
Red; Unfold pred1; Do 3 Intro.
Rewrite H; Intros.
EApply less_wdl.
Apply H1 with Hi':=Hi'.
Apply AbsIR_wd; Apply cg_minus_wd; Apply prf1; Auto.
Red; Unfold pred2; Intros.
EApply less_wdr.
Apply H1 with Hi':=Hi'.
Apply AbsIR_wd; Apply cg_minus_wd; Apply prf1; Auto.
Intros j Hj.
Cut (pred2 j Hj)+(pred1 j Hj).
Intro; Inversion_clear H; [Right | Left]; Assumption.
Unfold pred1 pred2.
Cut (Hi':(le i n))((delta[/]FourNZ[<](AbsIR (Pts P i Hi')[-](Pts R j Hj))))+((AbsIR (Pts P i Hi')[-](Pts R j Hj))[<]delta[/]TwoNZ); Intro.
Elim (le_lt_dec i n); Intro.
Elim (H a0); Intro.
Left; Intro.
EApply less_wdr.
Apply a1.
Apply AbsIR_wd; Apply cg_minus_wd; Apply prf1; Auto.
Right; Intro.
EApply less_wdl.
Apply b0.
Apply AbsIR_wd; Apply cg_minus_wd; Apply prf1; Auto.
Left; Intro.
ElimType False; Apply le_not_lt with i n; Auto.
Apply cotrans_less_unfolded.
RStep (delta[/]TwoNZ)[/]TwoNZ.
Apply pos_div_two'; Apply pos_div_two; Apply pos_delta.
Qed.

Hypothesis Hi0 : (lt O i).
Hypothesis Hin : (lt i n).

Definition sep__sep_fun_i : IR.
Elim sep__sep_aux_lemma; Intros.
2: Apply (Pts P i Hi).
Apply (Pts P i Hi)[+]delta[/]TwoNZ.
Defined.

Lemma sep__sep_leEq : (Hi':(le i n))(Pts P i Hi')[<=]sep__sep_fun_i.
Unfold sep__sep_fun_i.
Elim sep__sep_aux_lemma; Intros; Simpl.
2: Apply eq_imp_leEq; Apply prf1; Auto.
Apply leEq_wdl with (Pts P i Hi).
2: Apply prf1; Auto.
Apply shift_leEq_plus'; Step (Zero::IR).
Stepr delta[/]TwoNZ.
Apply less_leEq; Apply pos_div_two; Exact pos_delta.
Qed.

Lemma sep__sep_less : (Hi':(le (S i) n))sep__sep_fun_i[<](Pts P (S i) Hi').
Unfold sep__sep_fun_i.
Elim sep__sep_aux_lemma; Intros; Simpl.
2: Apply HP.
Apply shift_plus_less'.
Apply less_leEq_trans with delta.
Step delta[/]TwoNZ.
Apply pos_div_two'; Exact pos_delta.
Apply leEq_transitive with deltaP.
Apply delta_deltaP.
Unfold deltaP; Apply AntiMesh_lemma.
Qed.

Lemma sep__sep_ap : (j:nat)(Hj:(le j m))sep__sep_fun_i[#](Pts R j Hj).
Intros.
Unfold sep__sep_fun_i; Elim sep__sep_aux_lemma; Intro; Simpl.
2: Apply zero_minus_apart; Apply AbsIR_cancel_ap_zero; Apply Greater_imp_ap.
Elim a0; Intros j' H.
Elim H; Clear a0 H; Intros Hj' H.
Unfold pred1 in H.
RStepr (Pts P i Hi)[+]((Pts R j Hj)[-](Pts P i Hi)).
Apply op_lft_resp_ap.
Apply un_op_strext_unfolded with AbsIR.
Apply ap_well_def_lft_unfolded with delta[/]TwoNZ.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply less_leEq; Apply pos_div_two; Exact pos_delta.
EApply ap_well_def_rht_unfolded.
2: Apply AbsIR_minus.
Elim (le_lt_dec j j'); Intro.
Elim (le_lt_eq_dec ?? a0); Clear a0; Intro.
Apply less_imp_ap; Apply separation_conseq with j' (Cle_to ?? Hj').
Apply H.
Intro; Rewrite H0 in a0; Apply (lt_n_n ? a0).
Apply Greater_imp_ap.
EApply less_wdl.
Apply H with Hi':=Hi.
Apply AbsIR_wd.
Apply cg_minus_wd.
Algebra.
Apply prf1; Auto.
Apply less_imp_ap; Apply separation_conseq with j' (Cle_to ?? Hj').
Apply H.
Intro; Rewrite H0 in b0; Apply (lt_n_n ? b0).
Unfold pred2 in b0.
EApply less_transitive_unfolded.
2: Apply b0.
Apply pos_div_four; Exact pos_delta.
Qed.

End Defining_ai'.

Definition sep__sep_fun : (i:nat)(le i n)->IR.
Intros.
Elim (le_lt_dec i O); Intro.
Apply a.
Elim (le_lt_eq_dec ?? H); Intro.
Apply (sep__sep_fun_i i H).
Apply b.
Defined.

Lemma sep__sep_fun_i_delta : (i:nat)(Hi,Hi':(le i n))(Hi0:(lt i n))(AbsIR (sep__sep_fun_i i Hi)[-](Pts P i Hi'))[<=]delta[/]TwoNZ.
Intros.
Unfold sep__sep_fun_i.
Elim (sep__sep_aux_lemma i); Intro; Simpl.
Apply eq_imp_leEq.
EApply eq_transitive_unfolded.
2: Apply AbsIR_eq_x.
Apply AbsIR_wd.
RStepr ((Pts P i Hi')[+]delta[/]TwoNZ)[-](Pts P i Hi').
Apply cg_minus_wd.
Apply bin_op_wd_unfolded.
Apply prf1; Auto.
Algebra.
Algebra.
Stepr delta[/]TwoNZ; Apply less_leEq; Apply pos_div_two; Exact pos_delta.
Apply leEq_wdl with (Zero::IR).
Stepr delta[/]TwoNZ; Apply less_leEq; Apply pos_div_two; Exact pos_delta.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Apply AbsIR_wd.
Step (Pts P i Hi)[-](Pts P i Hi).
Apply cg_minus_wd; Apply prf1; Auto.
Qed.

Lemma sep__sep_fun_delta : (i:nat)(Hi,Hi':(le i n))(AbsIR (sep__sep_fun i Hi)[-](Pts P i Hi'))[<=]delta[/]TwoNZ.
Intros.
Unfold sep__sep_fun.
Elim (le_lt_dec i O); Intro; Simpl.
Cut i=O; [Intro | Auto with arith].
Generalize Hi'; Rewrite H; Intros.
Apply leEq_wdl with (Zero::IR).
Stepr delta[/]TwoNZ; Apply less_leEq; Apply pos_div_two; Exact pos_delta.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Apply AbsIR_wd.
Step a[-]a.
Apply cg_minus_wd; [Algebra | Apply eq_symmetric_unfolded; Apply start].
Elim (le_lt_eq_dec ?? Hi); Intro; Simpl.
Apply sep__sep_fun_i_delta; Assumption.
Generalize Hi'; Rewrite b1; Intros.
Apply leEq_wdl with (Zero::IR).
Stepr delta[/]TwoNZ; Apply less_leEq; Apply pos_div_two; Exact pos_delta.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Apply AbsIR_wd.
Step b[-]b.
Apply cg_minus_wd; [Algebra | Apply eq_symmetric_unfolded; Apply finish].
Qed.

Lemma sep__sep_mon_i : (i:nat)(Hi:(le i n))(Hi':(le (S i) n))(Hi0:(lt i n))(sep__sep_fun_i i Hi)[<](sep__sep_fun_i (S i) Hi').
Intros.
Apply less_leEq_trans with (Pts P (S i) Hi0).
Apply sep__sep_less.
Apply sep__sep_leEq.
Qed.

Lemma sep__sep_mon : (i:nat)(Hi:(le i n))(Hi':(le (S i) n))(sep__sep_fun i Hi)[<](sep__sep_fun (S i) Hi').
Intros.
Unfold sep__sep_fun.
Elim (le_lt_dec (S i) O); Intro; Simpl.
ElimType False; Apply (le_Sn_O ? a0).
Elim (le_lt_dec i O); Intro; Simpl.
Elim (le_lt_eq_dec ?? Hi'); Intro; Simpl.
Apply less_leEq_trans with (Pts P (S i) Hi').
Apply leEq_less_trans with (Pts P i Hi).
Elim (Partition_in_compact ???? P i Hi); Intros; Auto.
Apply HP.
Apply sep__sep_leEq.
Assumption.
Elim (le_lt_eq_dec ?? Hi); Intro; Simpl.
Elim (le_lt_eq_dec ?? Hi'); Intro; Simpl.
Apply sep__sep_mon_i; Assumption.
EApply less_wdr.
2: Apply finish with p:=P H:=(le_n n).
EApply less_wdr.
Apply sep__sep_less with Hi':=Hi'.
Generalize Hi'; Rewrite b2.
Intro; Apply prf1; Auto.
ElimType False; Rewrite b2 in Hi'; Apply (le_Sn_n ? Hi').
Qed.

Lemma sep__sep_fun_i_wd : (i,j:nat)i=j->(Hi:(le i n))(Hj:(le j n))(sep__sep_fun_i i Hi)[=](sep__sep_fun_i j Hj).
Do 3 Intro.
Rewrite <- H.
Intros.
Unfold sep__sep_fun_i.
Elim (sep__sep_aux_lemma i); Intros; Simpl.
Apply bin_op_wd_unfolded; [Apply prf1; Auto | Algebra].
Apply prf1; Auto.
Qed.

Lemma sep__sep_fun_wd : (i,j:nat)i=j->(Hi:(le i n))(Hj:(le j n))(sep__sep_fun i Hi)[=](sep__sep_fun j Hj).
Intros.
Unfold sep__sep_fun.
Elim (le_lt_dec i O); Elim (le_lt_dec j O); Intros; Simpl.
Algebra.
ElimType False; Apply (lt_n_n O); Apply lt_le_trans with j; Auto; Rewrite <- H; Auto.
ElimType False; Apply (lt_n_n O); Apply lt_le_trans with j; Auto; Rewrite <- H; Auto.
Elim (le_lt_eq_dec ?? Hi); Elim (le_lt_eq_dec ?? Hj); Intros; Simpl.
Apply sep__sep_fun_i_wd; Auto.
ElimType False; Rewrite H in a0; Rewrite b2 in a0; Apply (lt_n_n ? a0).
ElimType False; Rewrite <- H in a0; Rewrite b2 in a0; Apply (lt_n_n ? a0).
Algebra.
Qed.

Definition sep__sep_part : (Partition Hab n).
Apply Build_Partition with sep__sep_fun.
Exact sep__sep_fun_wd.
Intros; Apply less_leEq; Apply sep__sep_mon.
Intros; Unfold sep__sep_fun.
Elim (le_lt_dec O O); Intro; Simpl.
Algebra.
ElimType False; Inversion b0.
Intros; Unfold sep__sep_fun.
Elim (le_lt_dec n O); Intro; Simpl.
Apply partition_length_zero with Hab.
Cut n=O; [Intro | Auto with arith].
Rewrite <- H0; Apply P.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
ElimType False; Apply (lt_n_n ? a0).
Algebra.
Defined.

Lemma sep__sep_lemma : (Separated sep__sep_part R).
Repeat Split; Unfold _Separated; Intros.
Apply sep__sep_mon.
Apply HR.
Unfold sep__sep_part; Simpl.
Unfold sep__sep_fun; Simpl.
Elim (le_lt_dec i O); Intro; Simpl.
ElimType False; Apply lt_n_n with O; Apply lt_le_trans with i; Auto.
Elim (le_lt_eq_dec ?? Hi); Intro; Simpl.
Apply sep__sep_ap.
ElimType False; Rewrite b1 in H1; Apply (lt_n_n ? H1).
Qed.

Variable g:(i:nat)(lt i n)->IR.
Hypothesis gP : (Points_in_Partition P g).

Definition sep__sep_points [i:nat][Hi:(lt i n)] : IR.
Intros.
Apply (Max (sep__sep_fun_i i (lt_le_weak ?? Hi)) (g i Hi)).
Defined.

Lemma sep__sep_points_lemma : (Points_in_Partition sep__sep_part sep__sep_points).
Red; Intros.
Split.
Unfold sep__sep_part; Simpl.
Unfold sep__sep_fun sep__sep_points.
Elim (le_lt_dec i O); Intro; Simpl.
Apply leEq_transitive with (g i H).
Elim (Pts_part_lemma ?????? gP i H); Intros; Assumption.
Apply rht_leEq_Max.
Elim (le_lt_eq_dec ?? (lt_le_weak ?? H)); Intro; Simpl.
EApply leEq_wdl.
Apply lft_leEq_Max.
Apply sep__sep_fun_i_wd; Auto.
ElimType False; Rewrite b1 in H; Apply (lt_n_n ? H).
Unfold sep__sep_part; Simpl.
Unfold sep__sep_fun sep__sep_points.
Elim (le_lt_dec (S i) O); Intro; Simpl.
ElimType False; Inversion a0.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
Apply Max_leEq.
Apply less_leEq; Apply sep__sep_mon_i; Assumption.
Apply leEq_transitive with (Pts P (S i) H).
Elim (gP i H); Intros; Auto.
Apply sep__sep_leEq.
Apply Max_leEq.
Unfold sep__sep_fun_i.
Elim (sep__sep_aux_lemma i); Intro; Simpl.
Apply leEq_transitive with (Pts P (S i) H).
Apply shift_plus_leEq'.
Apply leEq_transitive with delta.
Step delta[/]TwoNZ; Apply less_leEq; Apply pos_div_two'; Exact pos_delta.
Apply leEq_transitive with deltaP.
Apply delta_deltaP.
Unfold deltaP; Apply AntiMesh_lemma.
Elim (Partition_in_compact ???? P (S i) H); Intros; Assumption.
Elim (Partition_in_compact ???? P i (lt_le_weak ?? H)); Intros; Assumption.
Elim (Pts_part_lemma ?????? gP i H); Intros; Assumption.
Qed.

Local sep__sep_aux : (i:nat)(H:(lt i n))(Hg,Hs:?)(AbsIR (Part F (g i H) Hg)[-](Part F (sep__sep_points i H) Hs))[<=]e.
Intros.
Apply Hd'.
Unfold I; Apply Pts_part_lemma with n P; Assumption.
Unfold I; Apply Pts_part_lemma with n sep__sep_part; Apply sep__sep_points_lemma.
Unfold sep__sep_points; Simpl.
EApply leEq_wdl.
2: Apply AbsIR_minus.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply shift_minus_leEq; Apply Max_leEq.
Unfold sep__sep_fun_i.
Elim sep__sep_aux_lemma; Intro; Simpl.
Apply leEq_transitive with (Pts P i (lt_le_weak ?? H))[+]delta.
Apply plus_resp_leEq_lft.
Apply less_leEq; Step delta[/]TwoNZ; Apply pos_div_two'; Exact pos_delta.
EApply leEq_wdr.
2: Apply cm_commutes.
Apply plus_resp_leEq_both.
Elim (gP i H); Intros; Assumption.
Apply delta_d.
Step Zero[+](Pts P i (lt_le_weak ?? H)).
Apply plus_resp_leEq_both.
Apply less_leEq; Exact Hd.
Elim (gP i H); Intros; Auto.
Apply shift_leEq_plus; Step (Zero::IR); Apply less_leEq; Exact Hd.
Apply shift_leEq_minus.
EApply leEq_wdl.
Apply rht_leEq_Max.
Algebra.
Qed.

Syntactic Definition just1:=(incF ? (Pts_part_lemma ?????? gP ??)).
Syntactic Definition just2:=(incF ? (Pts_part_lemma ?????? sep__sep_points_lemma ??)).

Lemma sep__sep_Sum : (AbsIR (Partition_Sum gP incF)[-](Partition_Sum sep__sep_points_lemma incF))[<=]alpha.
Unfold Partition_Sum; Simpl.
RStepr alpha[/]TwoNZ[+]alpha[/]TwoNZ.
Apply leEq_transitive with e[*](b[-]a)[+](nring n)[*]M[*]delta.
Apply leEq_wdr with e[*](Sumx [i:nat][Hi:(lt i n)](Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi)))[+]
  (Sumx [i:nat][Hi:(lt i n)]M[*]delta).
Apply leEq_transitive with (Sumx [i:nat][Hi:(lt i n)](AbsIR (Part F (g i Hi) just1)[-](Part F (sep__sep_points i Hi) just2))[*]
    ((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi))))[+]
  (Sumx [i:nat][Hi:(lt i n)](AbsIR (Part F (sep__sep_points i Hi) just2))[*]
    ((AbsIR (sep__sep_fun ? Hi)[-](Pts P ? Hi))[+](AbsIR (Pts P ? (lt_le_weak ?? Hi))[-](sep__sep_fun ? (lt_le_weak ?? Hi))))).
Apply leEq_transitive with (AbsIR (Sumx [i:nat][Hi:(lt i n)]
  ((Part F (g i Hi) just1)[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi))))[-]
    ((Part F (sep__sep_points i Hi) just2))[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi)))))[+]
  (AbsIR (Sumx [i:nat][Hi:(lt i n)](Part F (sep__sep_points i Hi) just2)[*]
    (((sep__sep_fun ? Hi)[-](Pts P ? Hi))[+]((Pts P ? (lt_le_weak ?? Hi))[-](sep__sep_fun ? (lt_le_weak ?? Hi)))))).
EApply leEq_wdl.
Apply triangle_IR_minus.
Apply eq_symmetric_unfolded.
Apply AbsIR_wd.
EApply eq_transitive_unfolded.
Apply Sumx_minus_Sumx.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply Sumx_minus_Sumx.
Apply Sumx_wd; Intros.
Step (Part F (g i H) just1)[*]((Pts P ? H)[-](Pts P ? (lt_le_weak ?? H)))[-]
  (Part F (sep__sep_points i H) just2)[*]((sep__sep_fun ? H)[-](sep__sep_fun ? (lt_le_weak ?? H))).
Rational.
Apply plus_resp_leEq_both.
EApply leEq_wdr.
Apply triangle_SumxIR.
Apply Sumx_wd; Intros.
Apply eq_transitive_unfolded with (AbsIR (Part F (g i H) just1)[-](Part F (sep__sep_points i H) just2))[*]
  (AbsIR (Pts P ? H)[-](Pts P ? (lt_le_weak ?? H))).
EApply eq_transitive_unfolded.
2: Apply AbsIR_resp_mult.
Apply AbsIR_wd; Algebra.
Apply mult_wd_rht.
Apply AbsIR_eq_x.
Apply shift_leEq_minus; Step (Pts P i (lt_le_weak ?? H)); Apply prf2.
EApply leEq_transitive.
Apply triangle_SumxIR.
Apply Sumx_resp_leEq; Intros.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_lft.
Apply triangle_IR.
Apply AbsIR_nonneg.
Apply plus_resp_leEq_both.
EApply leEq_wdr.
2: Apply Sumx_comm_scal'.
Apply Sumx_resp_leEq; Intros.
Apply mult_resp_leEq_rht.
Apply sep__sep_aux.
Apply shift_leEq_minus; Step (Pts P i (lt_le_weak ?? H)); Apply prf2.
Apply Sumx_resp_leEq; Intros.
Apply mult_resp_leEq_both.
Apply AbsIR_nonneg.
Step (Zero::IR)[+]Zero; Apply plus_resp_leEq_both; Apply AbsIR_nonneg.
Unfold I M; Apply norm_bnd_AbsIR.
Apply Pts_part_lemma with n sep__sep_part; Apply sep__sep_points_lemma.
RStepr delta[/]TwoNZ[+]delta[/]TwoNZ.
Apply plus_resp_leEq_both.
Apply sep__sep_fun_delta.
EApply leEq_wdl.
2: Apply AbsIR_minus.
Apply sep__sep_fun_delta.
Apply bin_op_wd_unfolded.
Apply mult_wd_rht.
EApply eq_transitive_unfolded.
Apply Mengolli_Sum with f:=[i:nat][Hi:(le i n)](Pts P i Hi).
Red; Intros; Apply prf1; Auto.
Intros; Algebra.
Apply cg_minus_wd.
Apply finish.
Apply start.
Stepr (nring n)[*](M[*]delta); Apply sumx_const.
Apply plus_resp_leEq_both.
Unfold e.
Apply leEq_wdl with (alpha[/]TwoNZ)[*]((b[-]a)[/]?[//](max_one_ap_zero b[-]a)).
RStepr (alpha[/]TwoNZ)[*]One.
Apply mult_resp_leEq_lft.
Apply shift_div_leEq.
Apply pos_max_one.
Stepr (Max b[-]a One); Apply lft_leEq_Max.
Apply less_leEq; Apply pos_div_two; Assumption.
Simpl; Rational.
Apply leEq_transitive with (Max (nring n)[*]M One)[*]delta.
Apply mult_resp_leEq_rht.
Apply lft_leEq_Max.
Apply less_leEq; Apply pos_delta.
Apply shift_mult_leEq' with (max_one_ap_zero (nring n)[*]M).
Apply pos_max_one.
Unfold delta.
EApply leEq_transitive.
Apply Min_leEq_rht.
Apply Min_leEq_lft.
Qed.

Lemma sep__sep_Mesh : (Mesh sep__sep_part)[<=](Mesh P)[+]csi.
Unfold Mesh.
Apply maxlist_leEq.
Apply length_Part_Mesh_List.
Exact pos_n.
Intros.
Elim (Part_Mesh_List_lemma ?????? H); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Elim Hi'; Clear Hi'; Intros Hi' Hx.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply Hx.
Unfold sep__sep_part; Simpl.
Unfold sep__sep_fun; Simpl.
Elim (le_lt_dec (S i) O); Intro; Simpl.
ElimType False; Inversion a0.
Elim (le_lt_eq_dec ?? (Cle_to ?? Hi')); Intro; Simpl.
Elim (le_lt_dec i O); Intro; Simpl.
Cut i=O; [Intro | Auto with arith].
Unfold sep__sep_fun_i; Simpl.
Elim (sep__sep_aux_lemma (S i)); Intro; Simpl.
Generalize Hi'; Rewrite H0; Clear Hx Hi'; Intro.
Apply leEq_wdl with ((Pts P (1) (Cle_to ?? Hi'))[+](delta[/]TwoNZ))[-](Pts P O (le_O_n ?)).
RStep ((Pts P (1) (Cle_to ?? Hi'))[-](Pts P O (le_O_n ?)))[+]delta[/]TwoNZ.
Apply plus_resp_leEq_both.
Fold (Mesh P); Apply Mesh_lemma.
Apply leEq_transitive with delta.
Apply less_leEq; Apply pos_div_two'; Exact pos_delta.
Apply delta_csi.
Apply cg_minus_wd; [Algebra | Apply start].
Generalize Hi'; Rewrite H0; Clear Hx Hi'; Intro.
Apply leEq_wdl with ((Pts P (1) (Cle_to ?? Hi'))[-](Pts P O (le_O_n ?))).
Fold (Mesh P); Apply leEq_transitive with (Mesh P)[+]Zero.
Stepr (Mesh P); Apply Mesh_lemma.
Apply plus_resp_leEq_lft.
Apply less_leEq; Assumption.
Apply cg_minus_wd; [Algebra | Apply start].
Elim (le_lt_eq_dec ?? (Cle_to ?? Hi)); Intro; Simpl.
Unfold sep__sep_fun_i.
Elim (sep__sep_aux_lemma (S i)); Elim (sep__sep_aux_lemma i); Intros; Simpl.
RStep (Pts P (S i) (Cle_to ?? Hi'))[-](Pts P i (Cle_to ?? Hi)).
Fold (Mesh P); Apply leEq_transitive with (Mesh P)[+]Zero.
Stepr (Mesh P); Apply Mesh_lemma.
Apply plus_resp_leEq_lft.
Apply less_leEq; Assumption.
RStep ((Pts P ? (Cle_to ?? Hi'))[-](Pts P ? (Cle_to ?? Hi)))[+]delta[/]TwoNZ.
Apply plus_resp_leEq_both.
Fold (Mesh P); Apply Mesh_lemma.
Apply leEq_transitive with delta.
Apply less_leEq; Apply pos_div_two'; Exact pos_delta.
Apply delta_csi.
RStep ((Pts P ? (Cle_to ?? Hi'))[-](Pts P ? (Cle_to ?? Hi)))[-]delta[/]TwoNZ.
Unfold 1 cg_minus; Apply plus_resp_leEq_both.
Fold (Mesh P); Apply Mesh_lemma.
Apply leEq_transitive with (Zero::IR).
Stepr [--](Zero::IR); Apply inv_resp_leEq.
Apply less_leEq; Apply pos_div_two; Exact pos_delta.
Apply leEq_transitive with delta.
Apply less_leEq; Exact pos_delta.
Apply delta_csi.
Fold (Mesh P); Apply leEq_transitive with (Mesh P)[+]Zero.
Stepr (Mesh P); Apply Mesh_lemma.
Apply plus_resp_leEq_lft.
Apply less_leEq; Assumption.
ElimType False; Rewrite b2 in a0; Apply lt_n_n with (S n); Apply lt_trans with (S n); Auto with arith.
Elim (le_lt_dec i O); Intro; Simpl.
Cut i=O; [Intro | Auto with arith].
Rewrite H0 in b1.
Clear Hx; Rewrite H0 in Hi'.
Apply leEq_wdl with (Pts P (1) (Cle_to ?? Hi'))[-](Pts P (0) (le_O_n n)).
Fold (Mesh P); Apply leEq_transitive with (Mesh P)[+]Zero.
Stepr (Mesh P); Apply Mesh_lemma.
Apply plus_resp_leEq_lft.
Apply less_leEq; Assumption.
Apply cg_minus_wd.
Generalize Hi'; Rewrite b1; Intro; Apply finish.
Apply start.
Elim (le_lt_eq_dec ?? (Cle_to ?? Hi)); Intro; Simpl.
Unfold sep__sep_fun_i.
Elim (sep__sep_aux_lemma i); Intro; Simpl.
Apply leEq_wdl with (Pts P (S i) (Cle_to ?? Hi'))[-]((Pts P i (Cle_to ?? Hi))[+]delta[/]TwoNZ).
RStep ((Pts P (S i) (Cle_to ?? Hi'))[-](Pts P i (Cle_to ?? Hi)))[-]delta[/]TwoNZ.
Unfold 1 cg_minus; Apply plus_resp_leEq_both.
Fold (Mesh P); Apply Mesh_lemma.
Apply leEq_transitive with (Zero::IR).
Stepr [--](Zero::IR); Apply inv_resp_leEq.
Apply less_leEq; Apply pos_div_two; Exact pos_delta.
Apply leEq_transitive with delta.
Apply less_leEq; Exact pos_delta.
Apply delta_csi.
Apply cg_minus_wd.
Generalize Hi'; Rewrite b1; Intro; Apply finish.
Algebra.
Apply leEq_wdl with (Pts P (S i) (Cle_to ?? Hi'))[-](Pts P i (Cle_to ?? Hi)).
Fold (Mesh P); Apply leEq_transitive with (Mesh P)[+]Zero.
Stepr (Mesh P); Apply Mesh_lemma.
Apply plus_resp_leEq_lft.
Apply less_leEq; Assumption.
Apply cg_minus_wd.
Generalize Hi'; Rewrite b1; Intro; Apply finish.
Algebra.
ElimType False; Rewrite b3 in b1; Apply n_Sn with n; Auto.
Qed.

End Separating__Separated.
