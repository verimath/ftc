(* $Id: RefSeparating.v,v 1.15 2003/03/13 12:06:22 lcf Exp $ *)

Require Export IntegralLemmas.

Section Separating_Partition.

Variables a,b:IR.
Hypothesis Hab:(a[<=]b).
Local I:=(compact a b Hab).

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis incF:(included (compact a b Hab) (Pred F)).

Hypothesis Hab':a[<]b.
Variable n:nat.
Variable P:(Partition Hab n).

Variable alpha:IR.
Hypothesis Halpha:Zero[<]alpha.

Variable csi:IR.
Hypothesis Hcsi:Zero[<]csi.

Local M:=(Norm_Funct contF).

Local pos_n : (lt O n).
Apply partition_less_imp_gt_zero with a b Hab; Assumption.
Qed.

Lemma SPap_n : ~n=O.
Intro.
Apply (lt_O_neq n).
Exact pos_n.
Auto.
Qed.

Local delta:=(Min csi alpha[/]?[//](mult_resp_ap_zero ??? (nring_ap_zero ?? SPap_n) (max_one_ap_zero M))).

Local pos_delta : Zero[<]delta.
Unfold delta; Apply less_Min.
Assumption.
Apply div_resp_pos.
Apply mult_resp_pos.
Step (!nring IR O); Apply nring_less; Apply pos_n.
Apply pos_max_one.
Assumption.
Qed.

Local delta_csi : delta[<=]csi.
Unfold delta; Apply Min_leEq_lft.
Qed.

Hypothesis Hab'' : delta[/]TwoNZ[<]b[-]a.

Lemma sep__part_lemma : (i:nat)(Hi:(le i n)){j:nat & {Hj:(Cle j n) &
  ((delta[/]FourNZ[<]((Pts P j (Cle_to ?? Hj))[-](Pts P i Hi)))*
    (j':nat)(Hj':(le j' n))(lt j' j)->((Pts P j' Hj')[-](Pts P i Hi)[<]delta[/]TwoNZ))}}+
  (((Pts P n (le_n n))[-](Pts P i Hi))[<]delta[/]TwoNZ).
Intros.
Elim (str_finite_or_elim ? [j:nat][Hj:(le j n)]delta[/]FourNZ[<]((Pts P j Hj)[-](Pts P i Hi))
  [j:nat][Hj:(le j n)]((Pts P j Hj))[-](Pts P i Hi)[<]delta[/]TwoNZ); Intros.
Left.
Elim a0; Intros j a'.
Elim a'; Intros Hj Hj'.
Elim Hj'; Clear a0 a' Hj'; Intros Hj' H0.
Exists j; Exists Hj.
Split; Assumption.
Right; Auto.
Red; Intros.
EApply less_wdr.
Apply H1.
Apply cg_minus_wd; Apply prf1; Auto.
Red; Intros.
EApply less_wdl.
Apply H1.
Apply cg_minus_wd; Apply prf1; Auto.
Apply cotrans_less_unfolded.
Apply shift_div_less.
Apply pos_four.
RStepr delta[+]delta.
Step Zero[+]delta.
Apply plus_resp_less_leEq.
Apply pos_delta.
Apply leEq_reflexive.
Qed.

Definition sep__part_h:nat->nat.
Intro i; Induction i.
Apply O.
Elim (le_lt_dec Hreci n); Intro.
Elim (sep__part_lemma Hreci a0); Intro.
Apply (ProjS1 a1).
Apply n.
Apply n.
Defined.

Lemma sep__part_h_bnd : (i:nat)(le (sep__part_h i) n).
Intro.
Induction i.
Apply le_O_n.
Simpl.
Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a0); Intro; Simpl.
LetTac j:=(ProjS1 a1); Fold j.
Elim (ProjS2 a1); Intros Hj Hj'; Fold j in Hj Hj'.
Apply Cle_to; Assumption.
Apply le_n.
Apply le_n.
Qed.

Lemma sep__part_h_mon_1 : (i:nat)(le (sep__part_h i) (sep__part_h (S i))).
Intros; Simpl.
Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a0); Intro; Simpl.
LetTac j:=(ProjS1 a1); Fold j.
Elim (ProjS2 a1); Intros Hj Hj'; Fold j in Hj Hj'.
Elim Hj'; Clear Hj'; Intros Hj0 Hj1.
Cut (lt (sep__part_h i) j); Intros.
Apply lt_le_weak; Assumption.
Apply (Partition_Points_mon ???? P) with a0 (Cle_to ?? Hj).
Apply less_transitive_unfolded with (Pts P (sep__part_h i) a0)[+]delta[/]FourNZ.
Apply shift_less_plus'; Step (Zero::IR).
Apply pos_div_four; Exact pos_delta.
Apply shift_plus_less'; Assumption.
Assumption.
Apply sep__part_h_bnd.
Qed.

Lemma sep__part_h_mon_2 : (i:nat)(lt (sep__part_h i) n)->(lt (sep__part_h i) (sep__part_h (S i))).
Intros; Simpl.
Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a0); Intro; Simpl.
LetTac j:=(ProjS1 a1); Fold j.
Elim (ProjS2 a1); Intros Hj Hj'; Fold j in Hj Hj'.
Elim Hj'; Clear Hj'; Intros Hj0 Hj1.
Apply (Partition_Points_mon ???? P) with a0 (Cle_to ?? Hj).
Apply less_transitive_unfolded with (Pts P (sep__part_h i) a0)[+]delta[/]FourNZ.
Apply shift_less_plus'; Step (Zero::IR).
Apply pos_div_four; Exact pos_delta.
Apply shift_plus_less'; Assumption.
Assumption.
Assumption.
Qed.

Lemma sep__part_h_mon_3 : (i,j:nat)(lt (sep__part_h i) n)->(lt i j)->(lt (sep__part_h i) (sep__part_h j)).
Intros; Induction j.
ElimType False; Inversion H0.
Cut (le (sep__part_h j) (sep__part_h (S j))); Intros.
2: Apply sep__part_h_mon_1.
Elim (le_lt_eq_dec ?? H0); Intro.
Apply lt_le_trans with (sep__part_h j); Auto.
Apply Hrecj; Auto with arith.
Rewrite <- b0; Apply sep__part_h_mon_2; Auto.
Qed.

Lemma sep__part_app_n : {m:nat | (sep__part_h (S m))=n /\ ((i:nat)(le i m)->(lt (sep__part_h i) n))}.
Elim (weird_mon_covers ?? (sep__part_h_mon_2)); Intros m Hm Hm'.
LetTac m':=(pred m).
Exists m'.
Cut ~m=O; Intro.
Split.
Cut (S m')=m; [Intro | Unfold m'; Symmetry; Apply S_pred with O; Apply neq_O_lt; Auto].
Rewrite H0; Clear H0 m'.
Cut (le n (sep__part_h m)).
Cut (le (sep__part_h m) n); Intros.
Auto with arith.
Apply sep__part_h_bnd.
Assumption.
Intros; Apply Hm'.
Unfold m' in H0; Rewrite S_pred with m O; Auto with arith.
Apply neq_O_lt; Auto.
Apply SPap_n.
Rewrite H in Hm.
Simpl in Hm.
Apply le_antisym; Auto with arith.
Qed.

Lemma sep__part_h_lemma : (i:nat)(lt (sep__part_h (S i)) n)->(Hi:?)(Hi':?)
  (Pts P (sep__part_h i) Hi)[<](Pts P (sep__part_h (S i)) Hi').
Do 3 Intro; Simpl.
Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a0); Intro; Simpl.
LetTac m':=(ProjS1 a1).
Change (Hi':(le m' n))(Pts P (sep__part_h i) Hi)[<](Pts P m' Hi'); Intros.
Elim (ProjS2 a1); Fold m'; Intros Hm' Hm''.
Inversion_clear Hm''.
Apply less_transitive_unfolded with (Pts P (sep__part_h i) Hi)[+]delta[/]FourNZ.
Apply shift_less_plus'; Step (Zero::IR); Apply pos_div_four; Exact pos_delta.
Apply shift_plus_less'; EApply less_wdr.
Apply H0.
Apply cg_minus_wd; Apply prf1; Auto.
Generalize H.
Simpl.
Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a1); Intro; Simpl.
2: Intro; ElimType False; Apply (lt_n_n n); Auto.
2: Intro; ElimType False; Apply (lt_n_n n); Auto.
LetTac m':=(ProjS1 a2).
Change (lt m' n)->(Hi':(le n n))(Pts P (sep__part_h i) Hi)[<](Pts P n Hi'); Intros.
Elim (ProjS2 a2); Fold m'; Intros Hm' Hm''.
Inversion_clear Hm''.
Apply less_leEq_trans with (Pts P ? (Cle_to ?? Hm')).
Apply less_transitive_unfolded with (Pts P (sep__part_h i) Hi)[+]delta[/]FourNZ.
Apply shift_less_plus'; Step (Zero::IR); Apply pos_div_four; Exact pos_delta.
Apply shift_plus_less'; EApply less_wdr.
Apply H1.
Apply cg_minus_wd; Apply prf1; Auto.
Apply local_mon'_imp_mon'2_le with f:=[i:nat][Hi:?](Pts P i Hi).
Intros; Apply prf2.
Assumption.
ElimType False; Apply (le_not_lt ?? Hi b0).
Qed.

Lemma sep__part_h_lemma2 : (i:nat)(Hi:?)(Hi':?)(Pts P (pred (sep__part_h (S i))) Hi')[-](Pts P (sep__part_h i) Hi)[<=]delta[/]TwoNZ.
Do 2 Intro; Simpl.
Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a0); Intro; Simpl.
LetTac j:=(ProjS1 a1).
Elim (ProjS2 a1); Fold j; Intros Hj Hj'; Inversion_clear Hj'.
Change (Hi':?)(Pts P (pred j) Hi')[-](Pts P ? Hi)[<=]delta[/]TwoNZ.
Intros; Apply less_leEq.
Apply less_wdl with (Pts P (pred j) Hi')[-](Pts P ? a0); Intros.
2: Apply cg_minus_wd; Apply prf1; Auto.
Apply H0.
Apply lt_pred_n_n.
Apply le_lt_trans with (sep__part_h i).
Apply le_O_n.
Apply Partition_Points_mon with P:=P Hi:=a0 Hj:=(Cle_to ?? Hj).
Apply less_transitive_unfolded with (Pts P (sep__part_h i) a0)[+]delta[/]FourNZ.
Apply shift_less_plus'; Step (Zero::IR); Apply pos_div_four; Exact pos_delta.
Apply shift_plus_less'; Assumption.
Intros; EApply leEq_transitive.
2: Apply less_leEq; Apply b0.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply Partition_mon; Assumption.
Apply inv_resp_leEq; Apply eq_imp_leEq; Apply prf1; Auto.
ElimType False; Exact (le_not_lt ?? (sep__part_h_bnd ?) b0).
Qed.

Lemma sep__part_h_lemma3 : (i,k:nat)(Hk:?)(Hk':?)(le (sep__part_h i) k)->(lt k (pred (sep__part_h (S i))))->
  (Pts P (S k) Hk')[-](Pts P k Hk)[<=]delta[/]TwoNZ.
Intros.
Cut (le (sep__part_h i) n).
Cut (le (pred (sep__part_h (S i))) n); Intros.
EApply leEq_transitive.
2: Apply sep__part_h_lemma2 with Hi:=H2 Hi':=H1.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply Partition_mon; Assumption.
Apply inv_resp_leEq; Apply Partition_mon; Assumption.
Apply le_trans with (sep__part_h (S i)).
Auto with arith.
Apply sep__part_h_bnd.
Apply sep__part_h_bnd.
Qed.

Local delta2_delta4 : (m:nat)
  (delta[/]FourNZ[<](Pts P ? (sep__part_h_bnd (S m)))[-](Pts P ? (sep__part_h_bnd m)))+
  ((Pts P ? (sep__part_h_bnd (S m)))[-](Pts P ? (sep__part_h_bnd m))[<]delta[/]TwoNZ).
Intro; Apply cotrans_less_unfolded.
RStep (delta[/]TwoNZ)[/]TwoNZ.
Apply pos_div_two'; Apply pos_div_two; Exact pos_delta.
Qed.

Local m1 := (proj1_sig ?? (sep__part_app_n)).

Local m:nat.
Elim (delta2_delta4 m1); Intro.
Apply (S m1).
Apply m1.
Defined.

Definition sep__part_length := m.

Local m_m1 : {m=m1}+{m=(S m1)}.
Unfold m; Clear m.
Elim (delta2_delta4 m1); Intro; Simpl.
Right; Auto.
Left; Auto.
Qed.

Local pos_m : (lt O m).
Unfold m.
Elim (delta2_delta4 m1); Intro; Simpl.
Auto with arith.
Elim (proj2_sig ?? sep__part_app_n); Fold m1; Intros.
Cut ~O=m1; Intro.
Auto with arith.
ElimType False.
Apply less_irreflexive_unfolded with x:=delta[/]TwoNZ.
Apply less_transitive_unfolded with b[-]a.
Assumption.
EApply less_wdl.
Apply b0.
Apply cg_minus_wd.
EApply eq_transitive_unfolded.
2: Apply finish with p:=P H:=(le_n n).
Apply prf1.
Auto.
EApply eq_transitive_unfolded.
2: Apply start with p:=P H:=(le_O_n n).
Apply prf1.
Rewrite <- H1.
Simpl; Auto.
Qed.

Definition sep__part_fun : (i:nat)(le i m)->nat.
Intros i Hi.
Elim (le_lt_eq_dec ?? Hi); Intro.
Apply (sep__part_h i).
Apply n.
Defined.

Lemma sep__part_fun_bnd : (i:nat)(H:(le i m))(le (sep__part_fun i H) n).
Intros.
Unfold sep__part_fun.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
Apply sep__part_h_bnd.
Apply le_n.
Qed.

Lemma sep__part_fun_0 : (H:(le O m))(sep__part_fun O H)=O.
Intros.
Unfold sep__part_fun.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
Reflexivity.
ElimType False.
Generalize b0.
Apply lt_O_neq; Apply pos_m.
Qed.

Lemma sep__part_fun_i : (i:nat)(H:(le i m))(lt i m)->(sep__part_fun i H)=(sep__part_h i).
Intros.
Unfold sep__part_fun.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
Reflexivity.
Rewrite b0 in H0; Elim (lt_n_n ? H0).
Qed.

Lemma sep__part_fun_m : (H:(le m m))(sep__part_fun m H)=n.
Intros.
Unfold sep__part_fun.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
Elim (lt_n_n ? a0).
Reflexivity.
Qed.

Lemma sep__part_fun_i' : (i:nat)(H:(le i m))(le (sep__part_h i) (sep__part_fun i H)).
Intros.
Unfold sep__part_fun.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
Apply le_n.
Apply sep__part_h_bnd.
Qed.

Lemma sep__part_fun_bnd' : (i:nat)(H:(le i m))(lt i m)->(lt (sep__part_fun i H) n).
Intros.
Unfold sep__part_fun.
Elim (le_lt_eq_dec ?? H); Intro; Simpl.
Elim (proj2_sig ?? sep__part_app_n).
Intros.
Apply H2.
Generalize a0; Clear a0.
Unfold m; Elim (delta2_delta4 m1); Intro; Simpl.
Auto with arith.
Auto with arith.
Rewrite b0 in H0; Elim (lt_n_n ? H0).
Qed.

Lemma sep__part_fun_wd : (i,j:nat)(Hi:?)(Hj:?)i=j->(sep__part_fun i Hi)=(sep__part_fun j Hj).
ClearBody m; Intros.
Unfold sep__part_fun.
Elim (le_lt_eq_dec ?? Hi); Elim (le_lt_eq_dec ?? Hj); Intros; Simpl.
Rewrite H; Auto.
Rewrite H in a0; Rewrite b0 in a0; Elim (lt_n_n ? a0).
Rewrite <- H in a0; Rewrite b0 in a0; Elim (lt_n_n ? a0).
Auto.
Qed.

Lemma sep__part_fun_mon : (i,j:nat)(Hi:?)(Hj:?)(lt i j)->(lt (sep__part_fun i Hi) (sep__part_fun j Hj)).
ClearBody m; Intros.
Apply less_nring with (IR::COrdField).
Apply local_mon_imp_mon_le with f:=[i:nat][Hi:(le i m)](!nring IR (sep__part_fun i Hi)).
Clear H Hj Hi j i; Intros; Apply nring_less.
2: Assumption.
Elim (le_lt_eq_dec ?? H'); Intro.
Rewrite sep__part_fun_i with i:=(S i).
2: Assumption.
Simpl; Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a1); Intro; Simpl.
Elim (ProjS2 a2); LetTac j:=(ProjS1 a2).
Intros Hj Hj'.
Inversion_clear Hj'.
Rewrite sep__part_fun_i.
2: Auto with arith.
Apply (Partition_Points_mon ???? P) with a1 (Cle_to ?? Hj).
Apply less_transitive_unfolded with (Pts P ? a1)[+](delta[/]FourNZ).
Apply shift_less_plus'; Step (Zero::IR); Apply pos_div_four; Exact pos_delta.
Apply shift_plus_less'; Apply H0.
Apply sep__part_fun_bnd'; Auto with arith.
Apply sep__part_fun_bnd'; Auto with arith.
Generalize H'; Rewrite b0.
Intro; Rewrite sep__part_fun_m.
Apply sep__part_fun_bnd'.
Auto with arith.
Qed.

Definition sep__part : (Partition Hab sep__part_length).
Apply Build_Partition with [i:nat][Hi:(le i m)](Pts P ? (sep__part_fun_bnd i Hi)).
Intros; Apply prf1.
Apply sep__part_fun_wd; Auto.
Intros.
Apply local_mon'_imp_mon'2_le with f:=[i:nat][Hi:(le i n)](Pts P i Hi).
Intros; Apply prf2.
Apply sep__part_fun_mon; Auto.
Intro.
Apply eq_transitive_unfolded with (Pts P O (le_O_n ?)).
Apply prf1.
Apply sep__part_fun_0.
Apply start.
Intro; EApply eq_transitive_unfolded.
2: Apply finish with p:=P H:=(le_n n).
Apply prf1.
Apply sep__part_fun_m.
Defined.

Lemma sep__part_fun_mon_pts : (i:nat)(Hi:?)(Hi':?)(Hi0:?)(Hi'0:?)(Pts P (sep__part_fun i Hi) Hi0)[<](Pts P (sep__part_fun (S i) Hi') Hi'0).
Do 3 Intro.
Rewrite sep__part_fun_i.
2: Auto with arith.
Elim (le_lt_eq_dec ?? Hi'); Intro.
Rewrite sep__part_fun_i with i:=(S i).
2: Assumption.
Intros.
Apply sep__part_h_lemma.
Rewrite <- sep__part_fun_i with H:=Hi'.
Apply sep__part_fun_bnd'; Assumption.
Assumption.
Generalize Hi'; Clear Hi'; Rewrite b0.
Intro; Rewrite sep__part_fun_m.
Intros.
Cut m=m.
2: Auto.
Unfold 2 m; Elim (delta2_delta4 m1); Intro; Simpl; Intro.
Cut i=m1; [Clear b0; Intro | Rewrite <- b0 in H; Auto with arith].
Generalize Hi0; Clear Hi0; Rewrite H0.
Intro.
Elim (proj2_sig ?? (sep__part_app_n)); Fold m1; Intros.
Apply less_transitive_unfolded with (Pts P (sep__part_h m1) Hi0)[+]delta[/]FourNZ.
Apply shift_less_plus'; Step (Zero::IR); Apply pos_div_four; Apply pos_delta.
Apply shift_plus_less'; EApply less_wdr.
Apply a0.
Apply cg_minus_wd; Apply prf1.
Auto.
Auto.
Elim (proj2_sig ?? (sep__part_app_n)); Fold m1; Intros.
Generalize Hi'0; Clear Hi'0.
Cut (S i)=m1; [Intro | Transitivity m; Auto].
Pattern 1 5 n; Rewrite <- H0.
Rewrite <- H2.
Intro.
Apply less_leEq_trans with (Pts P ? (sep__part_h_bnd (S i))).
2: Apply local_mon'_imp_mon'_le with f:=[i:nat][Hi:(le i n)](Pts P i Hi).
2: Intros; Apply prf2.
2: Red; Intros; Apply prf1; Assumption.
2: Apply sep__part_h_mon_1.
Apply sep__part_h_lemma.
Apply H1.
Rewrite H2; Apply le_n.
Qed.

Lemma sep__part_mon : (i:nat)(Hi:?)(Hi':?)(Pts sep__part i Hi)[<](Pts sep__part (S i) Hi').
Intros.
Unfold sep__part; Simpl.
Apply sep__part_fun_mon_pts.
Qed.

Lemma sep__part_mon_Mesh : (Mesh sep__part)[<=](Mesh P)[+]csi.
Unfold 1 Mesh.
Apply maxlist_leEq.
Apply length_Part_Mesh_List.
Apply pos_m.
Intros.
Elim (Part_Mesh_List_lemma ?????? H).
Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Elim Hi'; Clear Hi'; Intros Hi' Hx.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply Hx.
Clear Hx H x.
Simpl.
Cut (Ha:?)(Hb:?)(Pts P (sep__part_fun (S i) (Cle_to ?? Hi')) Ha)[-](Pts P (sep__part_fun i (Cle_to ?? Hi)) Hb)[<=](Mesh P)[+]csi.
Intro.
Apply H.
Cut (lt i m); [Intro | Red; Apply Cle_to; Assumption].
Rewrite sep__part_fun_i with i:=i.
2: Assumption.
Elim (le_lt_eq_dec ?? H); Intro.
Rewrite sep__part_fun_i.
2: Assumption.
Intros.
Cut (le (pred (sep__part_h (S i))) n); [Intro | EApply le_trans; [Apply le_pred_n | Auto]].
RStep ((Pts P ? Ha)[-](Pts P ? H0))[+]((Pts P ? H0)[-](Pts P ? Hb)).
Apply plus_resp_leEq_both.
Generalize Ha; Pattern 1 2 (sep__part_h (S i)); Replace (sep__part_h (S i)) with (S (pred (sep__part_h (S i)))); Intros.
Apply Mesh_lemma.
Symmetry; Apply S_pred with (sep__part_h i); Apply sep__part_h_mon_2.
Rewrite <- sep__part_fun_i with H:=(lt_le_weak ?? H).
Apply sep__part_fun_bnd'; Assumption.
Assumption.
EApply leEq_transitive.
Apply sep__part_h_lemma2.
Apply less_leEq; Apply less_leEq_trans with delta.
Apply pos_div_two'; Exact pos_delta.
Apply delta_csi.
Generalize Hi'; Clear Hi'; Rewrite b0; Intro.
Rewrite sep__part_fun_m.
Cut m=m; [Unfold 2 m | Auto].
Elim delta2_delta4; Intro; Simpl; Intro.
Intros.
Cut (sep__part_h (S m1))=n.
Intro; Generalize Ha Hb; Pattern 1 5 n.
Rewrite <- H1.
Cut i=m1; [Intro | Rewrite <- b0 in H0; Auto with arith].
Rewrite H2.
Intros.
Cut (le (pred (sep__part_h (S m1))) n); [Intro | EApply le_trans; [Apply le_pred_n | Auto]].
RStep ((Pts P ? Ha0)[-](Pts P ? H3))[+]((Pts P ? H3)[-](Pts P ? Hb0)).
Apply plus_resp_leEq_both.
Generalize Ha0; Pattern 1 2 (sep__part_h (S m1)); Replace (sep__part_h (S m1)) with (S (pred (sep__part_h (S m1)))); Intros.
Apply Mesh_lemma.
Symmetry; Apply S_pred with (sep__part_h m1); Apply sep__part_h_mon_2.
Cut (le m1 m).
2: Rewrite H0; Apply le_n_Sn.
Intro.
Rewrite <- sep__part_fun_i with H:=H4.
Apply sep__part_fun_bnd'.
Rewrite H0; Apply lt_n_Sn.
Rewrite H0; Apply lt_n_Sn.
EApply leEq_transitive.
Apply sep__part_h_lemma2.
Apply less_leEq; Apply less_leEq_trans with delta.
Apply pos_div_two'; Exact pos_delta.
Apply delta_csi.
Elim (proj2_sig ?? sep__part_app_n); Fold m1; Intros.
Auto.
Cut (sep__part_h (S m1))=n.
Intro; Pattern 1 5 n.
Rewrite <- H1.
Intros.
Cut (le (sep__part_h m1) n); [Intro | Apply sep__part_h_bnd].
RStep ((Pts P ? Ha)[-](Pts P ? H2))[+]((Pts P ? H2)[-](Pts P ? Hb)).
Apply leEq_transitive with (delta[/]TwoNZ)[+]((Mesh P)[+]delta[/]TwoNZ).
Apply plus_resp_leEq_both.
Apply less_leEq; EApply less_wdl.
Apply b1.
Apply cg_minus_wd; Apply prf1; Auto.
Generalize H2; Clear H2; Rewrite <- H0; Rewrite <- b0.
Simpl.
Elim (le_lt_dec (sep__part_h i) n); Intro; Simpl.
Elim (sep__part_lemma (sep__part_h i) a0); Intro; Simpl.
LetTac j:=(ProjS1 a1).
Change (H0:?)(Pts P j H0)[-](Pts P (sep__part_h i) Hb)[<=](Mesh P)[+]delta[/]TwoNZ.
Elim (ProjS2 a1); Fold j; Intros Hj Hj'.
Inversion_clear Hj'.
Intros.
Cut (le (pred j) n); [Intro | Apply le_trans with j; Auto with arith].
RStep ((Pts P j H4)[-](Pts P (pred j) H5))[+]((Pts P (pred j) H5)[-](Pts P (sep__part_h i) Hb)).
Cut (lt O j); Intros.
Apply plus_resp_leEq_both.
Cut j=(S (pred j)); [Intro | Apply S_pred with O; Auto].
Generalize H4; Pattern 1 2 j; Rewrite H7; Intro.
Apply Mesh_lemma.
Apply less_leEq.
Apply less_wdl with (Pts P (pred j) H5)[-](Pts P ? a0).
2: Apply cg_minus_wd; Apply prf1; Auto.
Apply H3.
Auto with arith.
Apply le_lt_trans with (sep__part_h i); Auto with arith.
Apply Partition_Points_mon with P:=P Hi:=a0 Hj:=(Cle_to ?? Hj).
Apply less_transitive_unfolded with (Pts P (sep__part_h i) a0)[+]delta[/]FourNZ.
Apply shift_less_plus'; Step (Zero::IR); Apply pos_div_four; Exact (pos_delta).
Apply shift_plus_less'; Assumption.
Intros.
Apply less_leEq; Apply less_leEq_trans with delta[/]TwoNZ.
EApply less_wdl.
Apply b2.
Apply cg_minus_wd; Apply prf1; Auto.
Step Zero[+]delta[/]TwoNZ; Apply plus_resp_leEq; Apply Mesh_nonneg.
ElimType False.
Exact (le_not_lt ?? (sep__part_h_bnd ?) b2).
RStep (Mesh P)[+]delta.
Apply plus_resp_leEq_lft; Apply delta_csi.
Elim (proj2_sig ?? sep__part_app_n); Fold m1; Intros.
Auto.
Qed.

Variable g:(i:nat)(lt i n)->IR.
Hypothesis gP : (Points_in_Partition P g).
Hypothesis gP' : (nat_less_n_fun ?? g).

Definition sep__part_pts [i:nat][Hi:(lt i sep__part_length)] : IR.
Intros.
Cut (lt (pred (sep__part_h (S i))) n); Intros.
Apply (g ? H).
Cut (lt (sep__part_h i) (sep__part_h (S i))).
2: Apply sep__part_h_mon_3.
Intro.
Red.
Replace (S (pred (sep__part_h (S i)))) with (sep__part_h (S i)); Intros.
Apply sep__part_h_bnd.
Apply S_pred with (sep__part_h i); Assumption.
Rewrite <- sep__part_fun_i with H:=(lt_le_weak ?? Hi).
Apply sep__part_fun_bnd'; Assumption.
Assumption.
Apply lt_n_Sn.
Defined.

Lemma sep__part_pts_lemma : (i:nat)(Hi:?)(Hi':?)(sep__part_pts i Hi)[=](g (pred (sep__part_h (S i))) Hi').
Intros; Unfold sep__part_pts.
Apply gP'; Auto.
Qed.

Lemma sep__part_pts_in_Partition : (Points_in_Partition sep__part sep__part_pts).
Red; Intros i Hi.
LetTac H:=(sep__part_h_mon_3 ?? (eq_ind nat (sep__part_fun i (lt_le_weak ?? Hi)) [n0:nat](lt n0 n) (sep__part_fun_bnd' i (lt_le_weak ?? Hi) Hi)
  (sep__part_h i) (sep__part_fun_i i (lt_le_weak ?? Hi) Hi)) (lt_n_Sn i)).
LetTac H0:=(S_pred (sep__part_h (S i)) (sep__part_h i) H).
LetTac H':=(eq_ind nat (sep__part_h (S i)) [j:nat](le j n) (sep__part_h_bnd (S i)) (S (pred (sep__part_h (S i)))) H0).
Elim (gP ? H'); Intros.
Simpl; Unfold sep__part_pts.
Split.
EApply leEq_transitive.
2: Apply a0.
Apply Partition_mon; Apply le_2.
Rewrite sep__part_fun_i; Assumption.
EApply leEq_transitive.
Apply b0.
Apply Partition_mon.
Rewrite <- H0.
Apply sep__part_fun_i'.
Qed.

Local Hsep_S : (i,j:nat)(Hi:(le (S i) m))(le j (pred (sep__part_fun (S i) Hi)))->(le (S j) n).
Intros.
Apply le_trans with (sep__part_fun (S i) Hi).
2: Apply sep__part_fun_bnd.
Rewrite (S_pred (sep__part_fun (S i) Hi) (sep__part_fun i (lt_le_weak ?? Hi))).
Auto with arith.
Apply sep__part_fun_mon; Apply lt_n_Sn.
Qed.

Local Hsep : (i,j:nat)(Hi:(le (S i) m))(le j (pred (sep__part_fun (S i) Hi)))->(le j n).
Intros.
Apply le_trans with (sep__part_fun (S i) Hi).
2: Apply sep__part_fun_bnd.
Rewrite (S_pred (sep__part_fun (S i) Hi) (sep__part_fun i (lt_le_weak ?? Hi))).
Apply le_S; Assumption.
Apply sep__part_fun_mon; Apply lt_n_Sn.
Qed.

Local h : nat->IR.
Intro i.
Elim (le_lt_dec i n); Intro.
Apply (Pts P i a0).
Apply (Zero::IR).
Defined.

Syntactic Definition just1:=(incF ? (Pts_part_lemma ?????? gP ??)).
Syntactic Definition just2:=(incF ? (Pts_part_lemma ?????? sep__part_pts_in_Partition ??)).

Local sep__part_sum1 : (i:nat)(Hi:(lt i m))
  (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
     (Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj')))[=](Pts sep__part ? Hi)[-](Pts sep__part ? (lt_le_weak ?? Hi)).
Intros; Simpl.
Unfold Sum2.
Cut (sep__part_fun (S i) Hi)=(S (pred (sep__part_fun (S i) Hi))).
2: Apply S_pred with (sep__part_fun i (lt_le_weak ?? Hi)); Apply sep__part_fun_mon; Apply lt_n_Sn.
Intro.
Cut (le (S (pred (sep__part_fun (S i) Hi))) n).
2: Rewrite <- H; Apply sep__part_fun_bnd.
Intro.
Apply eq_transitive_unfolded with (Pts P ? H0)[-](Pts P ? (sep__part_fun_bnd i (lt_le_weak ?? Hi))).
2: Apply cg_minus_wd; Apply prf1; Auto.
EApply eq_transitive_unfolded.
Apply str_Mengolli_Sum_gen with f:=h.
Rewrite <- H; Apply lt_le_weak; Apply sep__part_fun_mon; Apply lt_n_Sn.
Intro j; Intros.
Do 2 Elim le_lt_dec; Intros; Simpl.
Unfold h.
Do 2 Elim le_lt_dec; Intros; Simpl.
Apply cg_minus_wd; Apply prf1; Auto.
ElimType False; Apply le_not_lt with j n.
Apply le_trans with (S j); Auto with arith.
Assumption.
ElimType False; Apply le_not_lt with (S j) n.
Exact (Hsep_S ?? Hi a1).
Assumption.
ElimType False; Apply le_not_lt with (S j) n.
Exact (Hsep_S ?? Hi a1).
Assumption.
ElimType False; Exact (le_not_lt ?? H1 b0).
ElimType False; Exact (le_not_lt ?? H2 b0).
ElimType False; Exact (le_not_lt ?? H1 b0).
Unfold h.
Apply cg_minus_wd.
Elim le_lt_dec; Simpl; Intros.
Apply prf1; Auto.
ElimType False; Exact (le_not_lt ?? H0 b0).
Elim le_lt_dec; Intro; Simpl.
Apply prf1; Auto.
ElimType False; Rewrite <- H in H0; Apply le_not_lt with (sep__part_fun i (lt_le_weak ?? Hi)) n.
Apply sep__part_fun_bnd.
Assumption.
Qed.

Local sep__part_Sum2 : (Partition_Sum gP incF)[=](Sumx [i:nat][Hi:(lt i m)]
  (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
    (Part F (g j (Hsep_S ??? Hj')) just1)[*]((Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj'))))).
Unfold Partition_Sum.
Apply eq_symmetric_unfolded.
Unfold Sum2.
Apply eq_transitive_unfolded with (Sumx [j:nat][Hj:(lt j n)]
  (part_tot_nat_fun ?? [i:nat][H:(lt i n)](Part F (g i H) just1)[*]((Pts P ? H)[-](Pts P ? (lt_le_weak ?? H))) j)).
Apply str_Sumx_Sum_Sum' with g:=[i:nat][Hi:(lt i m)][i0:nat]
         (sumbool_rec (le (sep__part_fun i (lt_le_weak i m Hi)) i0)
           (lt i0 (sep__part_fun i (lt_le_weak i m Hi)))
           [_:(sumbool (le (sep__part_fun i (lt_le_weak i m Hi)) i0)
                (lt i0 (sep__part_fun i (lt_le_weak i m Hi))))]IR
           [_:(le (sep__part_fun i (lt_le_weak i m Hi)) i0)]
            (sumbool_rec (le i0 (pred (sep__part_fun (S i) Hi)))
              (lt (pred (sep__part_fun (S i) Hi)) i0)
              [_:(sumbool (le i0 (pred (sep__part_fun (S i) Hi)))
                   (lt (pred (sep__part_fun (S i) Hi)) i0))]IR
              [H0:(le i0 (pred (sep__part_fun (S i) Hi)))]
               (F (g i0 (Hsep_S i i0 Hi H0))
                  (incF (g i0 (Hsep_S i i0 Hi H0))
                    (Pts_part_lemma a b Hab n P g gP i0
                      (Hsep_S i i0 Hi H0))))[*]
                 ((Pts P (S i0) (Hsep_S i i0 Hi H0))[-]
                    (Pts P i0 (Hsep i i0 Hi H0)))
              [_:(lt (pred (sep__part_fun (S i) Hi)) i0)]Zero
              (le_lt_dec i0 (pred (sep__part_fun (S i) Hi))))
           [_:(lt i0 (sep__part_fun i (lt_le_weak i m Hi)))]Zero
           (le_lt_dec (sep__part_fun i (lt_le_weak i m Hi)) i0))
  h:=(part_tot_nat_fun ?? [i:nat][H:(lt i n)](Part F (g i H) just1)[*]
       ((Pts P ? H)[-](Pts P ? (lt_le_weak ?? H)))).
Apply sep__part_fun_0.
Intros; Apply sep__part_fun_wd; Auto.
Intros; Apply sep__part_fun_mon; Auto.
Intros.
Elim le_lt_dec; Intro; Simpl.
Elim le_lt_dec; Intro; Simpl.
Unfold part_tot_nat_fun.
Elim (le_lt_dec n j); Intro; Simpl.
ElimType False.
Apply le_not_lt with n j.
Assumption.
Apply lt_le_trans with (sep__part_fun (S i) Hi'').
Assumption.
Apply sep__part_fun_bnd.
Apply mult_wd; Algebra.
Apply cg_minus_wd; Apply prf1; Auto.
ElimType False.
Apply le_not_lt with (sep__part_fun i Hi') j.
Assumption.
Cut (sep__part_fun i Hi')=(sep__part_fun i (lt_le_weak ?? Hi)); [Intro | Apply sep__part_fun_wd; Auto].
Rewrite H1; Assumption.
ElimType False.
Apply le_not_lt with (S j) (sep__part_fun (S i) Hi).
Cut (sep__part_fun (S i) Hi)=(sep__part_fun (S i) Hi''); [Intro | Apply sep__part_fun_wd; Auto].
Rewrite H1; Apply H0.
Rewrite (S_pred (sep__part_fun (S i) Hi) (sep__part_fun i (lt_le_weak ?? Hi))).
Auto with arith.
Apply sep__part_fun_mon; Apply lt_n_Sn.
Intros; Symmetry; Apply sep__part_fun_m.
Apply Sumx_wd; Intros.
Unfold part_tot_nat_fun.
Elim (le_lt_dec n i); Intro; Simpl.
ElimType False; Apply le_not_lt with n i; Auto.
Apply mult_wd; Algebra.
Apply cg_minus_wd; Apply prf1; Auto.
Qed.

Local sep__part_Sum3 : (AbsIR (Partition_Sum gP incF)[-]
  (Partition_Sum sep__part_pts_in_Partition incF))[=]
    (AbsIR (Sumx [i:nat][Hi:(lt i m)]
      (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
        ((Part F (g j (Hsep_S ??? Hj')) just1)[-](Part F (sep__part_pts i Hi) just2))[*]
        ((Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj')))))).
Apply AbsIR_wd.
Apply eq_transitive_unfolded with (Sumx [i:nat][Hi:(lt i m)]
    (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
      (Part F (g j (Hsep_S ??? Hj')) just1)[*]((Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj'))))[-]
    ((Part F (sep__part_pts i Hi) just2)[*]
    (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
        (Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj'))))).
EApply eq_transitive_unfolded.
2: Apply Sumx_minus_Sumx with
  f:=[i:nat][Hi:(lt i m)](Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
      (Part F (g j (Hsep_S ??? Hj')) just1)[*]((Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj'))))
  g:=[i:nat][Hi:(lt i m)]((Part F (sep__part_pts i Hi) just2)[*]
      (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
        (Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj')))).
Apply cg_minus_wd.
Apply sep__part_Sum2.
Unfold Partition_Sum; Apply Sumx_wd; Intros.
Apply mult_wd_rht.
Apply eq_symmetric_unfolded; Apply sep__part_sum1.
Apply Sumx_wd; Intros i Hi.
Apply eq_transitive_unfolded with
    (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
      (Part F (g j (Hsep_S ??? Hj')) just1)[*]((Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj'))))[-]
      (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
    ((Part F (sep__part_pts i Hi) just2)[*]((Pts P ? (Hsep_S ??? Hj'))[-](Pts P ? (Hsep ??? Hj'))))).
Apply cg_minus_wd.
Algebra.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply Sum2_comm_scal'.
Algebra.
Rewrite <- (S_pred (sep__part_fun (S i) Hi) (sep__part_fun i (lt_le_weak ?? Hi)) (sep__part_fun_mon ???? (lt_n_Sn i))).
Apply lt_le_weak; Apply sep__part_fun_mon; Apply lt_n_Sn.
EApply eq_transitive_unfolded.
Apply Sum2_minus_Sum2.
Rewrite <- (S_pred (sep__part_fun (S i) Hi) (sep__part_fun i (lt_le_weak ?? Hi)) (sep__part_fun_mon ???? (lt_n_Sn i))).
Apply lt_le_weak; Apply sep__part_fun_mon; Apply lt_n_Sn.
Apply Sum2_wd; Intros.
Rewrite <- (S_pred (sep__part_fun (S i) Hi) (sep__part_fun i (lt_le_weak ?? Hi)) (sep__part_fun_mon ???? (lt_n_Sn i))).
Apply lt_le_weak; Apply sep__part_fun_mon; Apply lt_n_Sn.
Algebra.
Qed.

Local sep__part_Sum4 : (Sumx [i:nat][Hi:(lt i m)]
  (Sum2 [j:nat][Hj:(le (sep__part_fun i (lt_le_weak ?? Hi)) j)][Hj':(le j (pred (sep__part_fun (S i) Hi)))]
    (M[+]M)[*](delta[/]TwoNZ)))[<=]alpha.
Unfold Sum2.
Apply leEq_wdl with (Sumx [j:nat][_:(lt j n)](part_tot_nat_fun ?? [i:nat][_:(lt i n)](M[+]M)[*](delta[/]TwoNZ) j)).
2: Apply eq_symmetric_unfolded; Apply str_Sumx_Sum_Sum' with
  g:=[i:nat][Hi:(lt i m)][i0:nat]
              (sumbool_rec (le (sep__part_fun i (lt_le_weak i m Hi)) i0)
           (lt i0 (sep__part_fun i (lt_le_weak i m Hi)))
           [_:(sumbool (le (sep__part_fun i (lt_le_weak i m Hi)) i0)
                (lt i0 (sep__part_fun i (lt_le_weak i m Hi))))]IR
           [_:(le (sep__part_fun i (lt_le_weak i m Hi)) i0)]
            (sumbool_rec (le i0 (pred (sep__part_fun (S i) Hi)))
              (lt (pred (sep__part_fun (S i) Hi)) i0)
              [_:(sumbool (le i0 (pred (sep__part_fun (S i) Hi)))
                   (lt (pred (sep__part_fun (S i) Hi)) i0))]IR
              [_:(le i0 (pred (sep__part_fun (S i) Hi)))]
               (M[+]M)[*]delta[/]TwoNZ
              [_:(lt (pred (sep__part_fun (S i) Hi)) i0)]Zero
              (le_lt_dec i0 (pred (sep__part_fun (S i) Hi))))
           [_:(lt i0 (sep__part_fun i (lt_le_weak i m Hi)))]Zero
           (le_lt_dec (sep__part_fun i (lt_le_weak i m Hi)) i0))
  h:=(part_tot_nat_fun ?? [i:nat][_:(lt i n)](M[+]M)[*](delta[/]TwoNZ)).
Apply leEq_wdr with (Sumx [i:nat][_:(lt i n)](alpha[/]?[//](nring_ap_zero ?? SPap_n))).
2: RStepr (nring n)[*](alpha[/]?[//](nring_ap_zero ?? SPap_n)); Apply sumx_const.
Apply Sumx_resp_leEq; Intros.
Unfold part_tot_nat_fun.
Elim (le_lt_dec n i); Intro; Simpl.
ElimType False; Exact (le_not_lt ?? a0 H).
Unfold delta.
Apply leEq_transitive with (M[+]M)[*]((alpha[/]?[//](mult_resp_ap_zero ??? (nring_ap_zero ?? SPap_n) (max_one_ap_zero M)))[/]TwoNZ).
Apply mult_resp_leEq_lft.
Apply div_resp_leEq.
Apply pos_two.
Apply Min_leEq_rht.
Step (Zero::IR)[+]Zero; Apply plus_resp_leEq_both; Unfold M; Apply positive_norm.
RStep alpha[*](M[/]?[//](max_one_ap_zero M))[*](One[/]?[//](nring_ap_zero ?? SPap_n)).
RStepr alpha[*]One[*](One[/]?[//](nring_ap_zero ?? SPap_n)).
Apply mult_resp_leEq_rht.
Apply mult_resp_leEq_lft.
Apply shift_div_leEq.
Apply pos_max_one.
Stepr (Max M One); Apply lft_leEq_Max.
Apply less_leEq; Assumption.
Apply less_leEq; Apply recip_resp_pos.
Step (!nring IR O); Apply nring_less; Apply pos_n.
Apply sep__part_fun_0.
Exact sep__part_fun_wd.
Exact sep__part_fun_mon.
Unfold part_tot_nat_fun.
Intros; Elim (le_lt_dec (sep__part_fun i (lt_le_weak ?? Hi)) j); Intro; Simpl.
Elim (le_lt_dec j (pred (sep__part_fun (S i) Hi))); Intro; Simpl.
Elim (le_lt_dec n j); Intro; Simpl.
ElimType False; Apply (le_not_lt n j).
Assumption.
EApply lt_le_trans.
Apply H0.
Apply sep__part_fun_bnd.
Algebra.
ElimType False; Apply (le_not_lt ?? H0).
Rewrite (S_pred (sep__part_fun (S i) Hi'') (sep__part_fun i Hi')).
Cut (sep__part_fun (S i) Hi'')=(sep__part_fun (S i) Hi); [Intro | Apply sep__part_fun_wd; Auto].
Rewrite H1; Auto with arith.
Apply sep__part_fun_mon.
Apply lt_n_Sn.
ElimType False; Apply (le_not_lt ?? H).
Rewrite sep__part_fun_i.
2: Assumption.
Rewrite sep__part_fun_i in b0; Assumption.
Intros; Symmetry; Apply sep__part_fun_m.
Qed.

Local sep__part_aux : (i:nat)(lt (pred (sep__part_h (S i))) n).
Intros.
Red.
Rewrite <- S_pred with (sep__part_h (S i)) (sep__part_h O).
Apply sep__part_h_bnd.
Apply sep__part_h_mon_3.
Rewrite <- sep__part_fun_i with H:=(le_O_n m).
2: Apply pos_m.
2: Apply lt_O_Sn.
Rewrite <- sep__part_fun_m with H:=(le_n m).
Apply sep__part_fun_mon.
Apply pos_m.
Qed.

Lemma sep__part_Sum : (AbsIR (Partition_Sum gP incF)[-](Partition_Sum sep__part_pts_in_Partition incF))[<=]alpha.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply sep__part_Sum3.
EApply leEq_transitive.
2: Apply sep__part_Sum4.
EApply leEq_transitive.
Apply triangle_SumxIR.
Apply Sumx_resp_leEq; Intros.
EApply leEq_transitive.
Apply triangle_Sum2IR.
Rewrite <- (S_pred (sep__part_fun (S i) H) (sep__part_fun i (lt_le_weak ?? H)) (sep__part_fun_mon ???? (lt_n_Sn i))).
Apply lt_le_weak; Apply sep__part_fun_mon; Apply lt_n_Sn.
Apply Sum2_resp_leEq.
Rewrite <- (S_pred (sep__part_fun (S i) H) (sep__part_fun i (lt_le_weak ?? H)) (sep__part_fun_mon ???? (lt_n_Sn i))).
Apply lt_le_weak; Apply sep__part_fun_mon; Apply lt_n_Sn.
Intros k Hk Hk'.
Elim (le_lt_dec m (S i)); Intro.
Cut (S i)=m; [Intro | Clear Hk Hk'; Omega].
Generalize H0.
Unfold 1 m; Elim delta2_delta4; Intro; Simpl; Intro.
Cut (lt i m); [Intro | Assumption].
Apply leEq_wdl with (AbsIR ((Part F (g k (Hsep_S ?? H Hk')) just1)[-](Part F (g ? (sep__part_aux m1)) just1))[*]
  ((Pts P (S k) (Hsep_S ?? H Hk'))[-](Pts P k (Hsep ?? H Hk')))).
2: Apply AbsIR_wd; Apply mult_wd_lft.
2: Apply cg_minus_wd; [Algebra | Idtac].
2: Cut i=m1; [Intro | Auto].
2: Generalize H; Rewrite H3; Intro.
2: Unfold sep__part_pts; Simpl; Algebra.
Elim (le_lt_dec (pred (sep__part_h (S m1))) k); Intro.
Cut (pred (sep__part_h (S m1)))=k; Intros.
Apply leEq_wdl with (Zero::IR).
Step (Zero[+]Zero)[*](Zero::IR).
Apply mult_resp_leEq_both.
Apply eq_imp_leEq; Algebra.
Apply leEq_reflexive.
Apply plus_resp_leEq_both; Unfold M; Apply positive_norm.
Apply less_leEq; Stepr delta[/]TwoNZ; Apply pos_div_two; Exact pos_delta.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply AbsIRz_isz.
Apply AbsIR_wd.
RStepr ((Part F (g ? (sep__part_aux m1)) just1)[-](Part F (g ? (sep__part_aux m1)) just1))[*]
  ((Pts P (S k) (Hsep_S ?? H Hk'))[-](Pts P k (Hsep ?? H Hk'))).
Algebra.
Cut (H:?)(sep__part_fun (S i) H)=n.
Intro.
Cut (sep__part_h (S m1))=n; Intros.
Rewrite H4 in a2.
Rewrite H3 in Hk'.
Rewrite H4.
Apply le_antisym; Auto.
Elim (proj2_sig ?? (sep__part_app_n)); Fold m1; Intros.
Auto.
Rewrite H0; Exact sep__part_fun_m.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both; Unfold M I; Apply norm_bnd_AbsIR; Apply Pts_part_lemma with n P; Apply gP.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (Pts P k (Hsep i k H Hk')); Apply prf2.
Apply sep__part_h_lemma3 with i.
Rewrite sep__part_fun_i in Hk; Assumption.
Rewrite H1; Assumption.
Apply leEq_wdl with (AbsIR ((Part F (g k (Hsep_S ?? H Hk')) just1)[-](Part F (g ? (sep__part_aux i)) just1))[*]
  ((Pts P (S k) (Hsep_S ?? H Hk'))[-](Pts P k (Hsep ?? H Hk')))).
2: Apply AbsIR_wd; Apply mult_wd.
2: Apply cg_minus_wd; Apply pfwdef; [Algebra | Unfold sep__part_pts; Apply gP']; Auto.
2: Apply cg_minus_wd; Apply prf1; Auto.
Elim (le_lt_dec (pred (sep__part_h m1)) k); Intro.
Elim (le_lt_eq_dec ?? a1); Intro.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both; Unfold M I; Apply norm_bnd_AbsIR; Apply Pts_part_lemma with n P; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (Pts P k (Hsep i k H Hk')); Apply prf2.
Apply less_leEq; EApply leEq_less_trans.
2: Apply b0.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply Partition_mon.
Rewrite (S_pred (sep__part_h (S m1)) (sep__part_h m1)).
Apply le_n_S.
Cut (H:?)(sep__part_h (S m1))=(sep__part_fun (S i) H); Intros.
Rewrite (H2 H); Assumption.
Generalize H2; Rewrite H0.
Intro; Rewrite sep__part_fun_m.
Elim (proj2_sig ?? (sep__part_app_n)); Fold m1; Auto.
Apply sep__part_h_mon_3.
Elim (proj2_sig ?? (sep__part_app_n)); Fold m1; Intros.
Apply H3; Apply le_n.
Apply lt_n_Sn.
Apply inv_resp_leEq; Apply Partition_mon.
EApply le_trans.
2: Apply a2.
Clear Hk Hk'; Omega.
Apply leEq_wdl with (Zero::IR).
Step (Zero[+]Zero)[*](Zero::IR).
Apply mult_resp_leEq_both.
Apply eq_imp_leEq; Algebra.
Apply leEq_reflexive.
Apply plus_resp_leEq_both; Unfold M; Apply positive_norm.
Apply less_leEq; Stepr delta[/]TwoNZ; Apply pos_div_two; Exact pos_delta.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply AbsIRz_isz.
Apply AbsIR_wd.
RStepr ((Part F (g ? (sep__part_aux i)) just1)[-](Part F (g ? (sep__part_aux i)) just1))[*]
  ((Pts P (S k) (Hsep_S ?? H Hk'))[-](Pts P k (Hsep ?? H Hk'))).
Apply mult_wd_lft.
Apply cg_minus_wd; Apply pfwdef; Apply gP'; Auto.
Rewrite H1; Auto.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both; Unfold M I; Apply norm_bnd_AbsIR; Apply Pts_part_lemma with n P; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (Pts P k (Hsep i k H Hk')); Apply prf2.
Apply sep__part_h_lemma3 with i.
Rewrite sep__part_fun_i in Hk; Assumption.
Rewrite H1; Assumption.
Elim (le_lt_eq_dec ?? Hk'); Intro.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both; Unfold M I; Apply norm_bnd_AbsIR.
Apply Pts_part_lemma with n P; Assumption.
Apply Pts_part_lemma with sep__part_length sep__part; Apply sep__part_pts_in_Partition.
Cut (le (pred (sep__part_fun (S i) H)) n); Intros.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (Pts P k (Hsep i k H Hk')); Apply prf2.
Apply sep__part_h_lemma3 with i.
Rewrite sep__part_fun_i in Hk; Assumption.
Rewrite sep__part_fun_i in a0; Assumption.
Apply le_trans with (sep__part_fun (S i) H).
Auto with arith.
Apply sep__part_fun_bnd.
Apply leEq_wdl with (Zero::IR).
Step (Zero[+]Zero)[*](Zero::IR).
Apply mult_resp_leEq_both.
Apply eq_imp_leEq; Algebra.
Apply leEq_reflexive.
Apply plus_resp_leEq_both; Unfold M; Apply positive_norm.
Apply less_leEq; Stepr delta[/]TwoNZ; Apply pos_div_two; Exact pos_delta.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply AbsIRz_isz.
Apply AbsIR_wd.
RStepr ((Part F (g ? (sep__part_aux i)) just1)[-](Part F (g ? (sep__part_aux i)) just1))[*]
  ((Pts P (S k) (Hsep_S ?? H Hk'))[-](Pts P k (Hsep ?? H Hk'))).
Apply mult_wd_lft.
Apply cg_minus_wd; Apply pfwdef; Unfold sep__part_pts; Apply gP'; Auto.
Rewrite sep__part_fun_i in b1; Assumption.
Qed.

End Separating_Partition.
