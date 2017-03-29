(* $Id: RefSepRef.v,v 1.7 2003/03/11 13:36:08 lcf Exp $ *)

Require Export IntegralLemmas.

Section Refining_Separated.

Variables a,b:IR.
Hypothesis Hab:(a[<=]b).
Local I:=(compact a b Hab).

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis incF:(included (compact a b Hab) (Pred F)).

Variables m,n:nat.
Variable P:(Partition Hab n).
Variable R:(Partition Hab m).

Hypothesis HPR:(Separated P R).

Local HP:(_Separated P).
Elim HPR; Intros; Assumption.
Qed.

Local HP':(a[=]b)->O=n.
Intro.
Apply _Separated_imp_length_zero with P:=P.
Exact HP.
Assumption.
Qed.

Local HR:(_Separated R).
Elim HPR; Intros.
Elim b0; Intros; Assumption.
Qed.

Local HR':(a[=]b)->O=m.
Intro.
Apply _Separated_imp_length_zero with P:=R.
Exact HR.
Assumption.
Qed.

Local mn0 : (O=m)->(O=n).
Intro; Apply HP'; Apply partition_length_zero with Hab.
Rewrite H; Apply R.
Qed.

Local nm0 : (O=n)->(O=m).
Intro; Apply HR'; Apply partition_length_zero with Hab.
Rewrite H; Apply P.
Qed.

Local H':(i,j:nat)(lt O i)->(lt O j)->(lt i n)->(lt j m)->(Hi:(le i n))(Hj:(le j m))(Pts P i Hi)[#](Pts R j Hj).
Elim HPR; Do 2 Intro.
Elim b0; Do 2 Intro; Assumption.
Qed.

Local f':=[i:nat][H:(lt i (pred n))](Pts P ? (lt_8 ?? H)).
Local g':=[j:nat][H:(lt j (pred m))](Pts R ? (lt_8 ?? H)).

Local f'_nlnf : (nat_less_n_fun ?? f').
Red; Intros; Unfold f'; Apply prf1; Auto.
Qed.

Local g'_nlnf : (nat_less_n_fun ?? g').
Red; Intros; Unfold g'; Apply prf1; Auto.
Qed.

Local f'_mon : ((i,i':nat)(Hi:?)(Hi':?)(lt i i')->((f' i Hi)[<](f' i' Hi'))).
Intros.
Apply local_mon_imp_mon_lt with n:=(pred n).
Intros; Unfold f'; Apply HP.
Assumption.
Qed.

Local g'_mon : ((j,j':nat)(Hj:?)(Hj':?)(lt j j')->((g' j Hj)[<](g' j' Hj'))).
Intros.
Apply local_mon_imp_mon_lt with n:=(pred m).
Intros; Unfold g'; Apply HR.
Assumption.
Qed.

Local f'_ap_g' : ((i,j:nat)(Hi:?)(Hj:?)(f' i Hi)[#](g' j Hj)).
Intros.
Unfold f' g'; Apply H'.
Apply lt_O_Sn.
Apply lt_O_Sn.
Apply pred_lt; Assumption.
Apply pred_lt; Assumption.
Qed.

Local h:=(ProjS1 (can_be_ordered ????? f'_nlnf g'_nlnf f'_mon g'_mon f'_ap_g')).
Local Hh:=(ProjS2 (can_be_ordered ????? f'_nlnf g'_nlnf f'_mon g'_mon f'_ap_g')).

Local h_nlnf : (nat_less_n_fun ?? h).
Inversion_clear Hh; Do 3 (Inversion_clear H; Inversion_clear H1); Assumption.
Qed.

Local h_mon : ((i,i':nat)(Hi:?)(Hi':?)(lt i i')->((h i Hi)[<](h i' Hi'))).
Inversion_clear Hh; Do 3 (Inversion_clear H; Inversion_clear H1); Assumption.
Qed.

Local h_mon' : ((i,i':nat)(Hi:?)(Hi':?)(le i i')->((h i Hi)[<=](h i' Hi'))).
ClearBody h Hh; Intros; Apply mon_imp_mon'_lt with n:=(plus (pred m) (pred n)).
Apply h_nlnf.
Apply h_mon.
Assumption.
Qed.

Local h_f' : (i:nat)(Hi:?){j:nat & {Hj:(Clt ??) | (f' i Hi)[=](h j (Clt_to ?? Hj))}}.
Inversion_clear Hh; Do 3 (Inversion_clear H; Inversion_clear H1); Assumption.
Qed.

Local h_g' : (j:nat)(Hj:?){i:nat & {Hi:(Clt ??) | (g' j Hj)[=](h i (Clt_to ?? Hi))}}.
Inversion_clear Hh; Do 3 (Inversion_clear H; Inversion_clear H1); Assumption.
Qed.

Local h_PropAll : (P:IR->Prop)(pred_well_def' IR P)->((i:nat)(Hi:?)(P (f' i Hi)))->((j:nat)(Hj:?)(P (g' j Hj)))->(k:nat)(Hk:?)(P (h k Hk)).
Inversion_clear Hh; Do 3 (Inversion_clear H; Inversion_clear H1); Assumption.
Qed.

Local h_PropEx : (P:IR->Prop)(pred_well_def' IR P)->
   ({i:nat & {Hi:(Clt ??) | (P (f' i (Clt_to ?? Hi)))}}+{j:nat & {Hj:(Clt ??) | (P (g' j (Clt_to ?? Hj)))}})->
     {k:nat & {Hk:(Clt ??) | (P (h k (Clt_to ?? Hk)))}}.
Inversion_clear Hh; Do 3 (Inversion_clear H; Inversion_clear H1); Assumption.
Qed.

Definition Separated_Refinement_fun : (i:nat)(le i (pred (plus m n)))->IR.
Intros.
Elim (le_lt_eq_dec ?? H); Intro.
Elim (le_lt_dec i O); Intro.
Apply a.
Apply (h (pred i) (lt_10 ??? b0 a0)).
Apply b.
Defined.

Lemma Separated_Refinement_lemma1 : (i,j:nat)i=j->(Hi:(le i (pred (plus m n))))(Hj:(le j (pred (plus m n))))
  (Separated_Refinement_fun i Hi)[=](Separated_Refinement_fun j Hj).
ClearBody h Hh.
Do 3 Intro.
Rewrite <- H; Intros; Unfold Separated_Refinement_fun; Simpl.
Elim (le_lt_eq_dec ?? Hi); Elim (le_lt_eq_dec ?? Hj); Elim (le_lt_dec i O); Intros; Simpl.
Algebra.
Apply h_nlnf; Reflexivity.
ElimType False; Rewrite <- b0 in a1; Apply (lt_n_n ? a1).
ElimType False; Rewrite <- b1 in a0; Apply (lt_n_n ? a0).
ElimType False; Rewrite <- b0 in a1; Apply (lt_n_n ? a1).
ElimType False; Rewrite <- b1 in a0; Apply (lt_n_n ? a0).
Algebra.
Algebra.
Qed.

Lemma Separated_Refinement_lemma3 : (H:(le (0) (pred (plus m n))))(Separated_Refinement_fun (0) H)[=]a.
Intros; Unfold Separated_Refinement_fun; Simpl.
Elim (le_lt_eq_dec ?? H); Elim (le_lt_dec O O); Intros; Simpl.
Algebra.
ElimType False; Inversion b0.
Apply eq_symmetric_unfolded; Apply partition_length_zero with Hab.
Cut (le (plus m n) (1)); [Intro | Omega].
Elim (plus_eq_one_imp_eq_zero ?? H0); Intro.
Rewrite <- a1; Apply R.
Rewrite <- b1; Apply P.
ElimType False; Inversion b0.
Qed.

Lemma Separated_Refinement_lemma4 : (H:(le (pred (plus m n)) (pred (plus m n))))(Separated_Refinement_fun (pred (plus m n)) H)[=]b.
Intros; Unfold Separated_Refinement_fun; Simpl.
Elim (le_lt_eq_dec ?? H); Elim (le_lt_dec O O); Intros; Simpl.
Algebra.
ElimType False; Apply (lt_n_n ? a1).
ElimType False; Apply (lt_n_n ? a0).
Algebra.
Algebra.
Qed.

Lemma Separated_Refinement_lemma2 : (i:nat)(H:(le i (pred (plus m n))))(H':(le (S i) (pred (plus m n))))
  (Separated_Refinement_fun i H)[<=](Separated_Refinement_fun (S i) H').
ClearBody h Hh.
Intros; Unfold Separated_Refinement_fun; Simpl.
Elim (le_lt_eq_dec ?? H); Elim (le_lt_eq_dec ?? H'0); Intros; Simpl.
Elim (le_lt_dec i O); Elim (le_lt_dec (S i) O); Intros; Simpl.
ElimType False; Inversion a2.
Apply h_PropAll with P:=[x:IR]a[<=]x.
Red; Intros.
Apply leEq_wdr with x; Assumption.
Intros; Unfold f'.
Apply leEq_wdl with (Pts P O (le_O_n ?)).
Apply Partition_mon; Apply le_O_n.
Apply start.
Intros; Unfold g'.
Apply leEq_wdl with (Pts R O (le_O_n ?)).
Apply Partition_mon; Apply le_O_n.
Apply start.
ElimType False; Inversion a2.
Apply less_leEq; Apply h_mon; Auto with arith.
Elim (le_lt_dec i O); Elim (le_lt_dec (S i) O); Intros; Simpl.
ElimType False; Inversion a1.
Assumption.
ElimType False; Inversion a1.
Apply h_PropAll with P:=[x:IR]x[<=]b.
Red; Intros.
Apply leEq_wdl with x; Assumption.
Intros; Unfold f'.
Apply leEq_wdr with (Pts P ? (le_n ?)).
Apply Partition_mon; Apply le_trans with (pred n); Auto with arith.
Apply finish.
Intros; Unfold g'.
Apply leEq_wdr with (Pts R ? (le_n ?)).
Apply Partition_mon; Apply le_trans with (pred m); Auto with arith.
Apply finish.
ElimType False; Rewrite <- b0 in H'0; Apply (le_Sn_n ? H'0).
Apply leEq_reflexive.
Qed.

Definition Separated_Refinement : (Partition Hab (pred (plus m n))).
Apply Build_Partition with Separated_Refinement_fun.
Exact Separated_Refinement_lemma1.
Exact Separated_Refinement_lemma2.
Exact Separated_Refinement_lemma3.
Exact Separated_Refinement_lemma4.
Defined.

Local auxP : nat->nat.
ClearBody h Hh.
Intro i.
Elim (le_lt_dec i O); Intro.
Apply O.
Elim (le_lt_dec n i); Intro.
Apply (plus (pred (plus m n)) (minus i n)).
Apply (S (ProjS1 (h_f' (pred i) (lt_pred' ?? b0 b1)))).
Defined.

Local auxR : nat->nat.
ClearBody h Hh.
Intro i.
Elim (le_lt_dec i O); Intro.
Apply O.
Elim (le_lt_dec m i); Intro.
Apply (plus (pred (plus m n)) (minus i m)).
Apply (S (ProjS1 (h_g' (pred i) (lt_pred' ?? b0 b1)))).
Defined.

Local not_not_lt : (i,j:nat)~~(lt i j)->(lt i j).
Intros; Omega.
Qed.

Local plus_pred_pred_plus : (i,j,k:nat)(le k (plus (pred i) (pred j)))->(le k (pred (plus i j))).
Intros; Omega.
Qed.

Local auxP_lemma0 : (auxP O)=O.
ClearBody h Hh; Unfold auxP.
Elim (le_lt_dec O O); Intro; Simpl.
Reflexivity.
ElimType False; Inversion b0.
Qed.

Local h_inj : (i,j:nat)(Hi:?)(Hj:?)(((h i Hi)[=](h j Hj))->i=j).
ClearBody h Hh; Intros.
EApply mon_imp_inj_lt with f:=h.
Exact h_mon.
Apply H.
Qed.

Local auxP_lemmai : (i:nat)(Hi:(lt O i))(Hi':(lt i n))(auxP i)=(S (ProjS1 (h_f' (pred i) (lt_pred' ?? Hi Hi')))).
ClearBody h Hh; Intros.
Unfold auxP.
Elim (le_lt_dec n i); Intro; Simpl.
ElimType False; Apply le_not_lt with n i; Auto.
Elim (le_lt_dec i O); Intro; Simpl.
ElimType False; Apply lt_n_n with O; Apply lt_le_trans with i; Auto.
LetTac x:=(ProjS1 (h_f' ? (lt_pred' ?? b1 b0))).
LetTac y:=(ProjS1 (h_f' ? (lt_pred' ?? Hi Hi'))).
Cut x=y.
Intro; Auto with arith.
Cut {Hj:(Clt ??) | (f' ? (lt_pred' ?? b1 b0))[=](h x (Clt_to ?? Hj))}; [Intro | Exact (ProjS2 (h_f' ? (lt_pred' ?? b1 b0)))].
Cut {Hj:(Clt ??) | (f' ? (lt_pred' ?? Hi Hi'))[=](h y (Clt_to ?? Hj))}; [Intro | Exact (ProjS2 (h_f' ? (lt_pred' ?? Hi Hi')))].
Elim H; Clear H; Intros Hx Hx'.
Elim H0; Clear H0; Intros Hy Hy'.
Apply h_inj with (Clt_to ?? Hx) (Clt_to ?? Hy).
EApply eq_transitive_unfolded.
2: Apply Hy'.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply Hx'.
Apply f'_nlnf; Reflexivity.
Qed.

Local auxP_lemman : (auxP n)=(pred (plus m n)).
ClearBody h Hh; Unfold auxP.
Elim (le_lt_dec n O); Intro; Simpl.
Cut n=O; [Intro | Auto with arith].
Transitivity (pred m).
2: Rewrite H; Auto.
Cut O=m; [Intro; Rewrite <- H0; Auto | Apply HR'].
Apply partition_length_zero with Hab; Rewrite <- H; Apply P.
Elim (le_lt_dec n n); Intro; Simpl.
Rewrite <- minus_n_n; Auto.
ElimType False; Apply lt_n_n with n; Auto.
Qed.

Local auxP_lemma1 : (i,j:nat)(lt i j)->(lt (auxP i) (auxP j)).
ClearBody h Hh.
Intros; Unfold auxP.
Elim (le_lt_dec i O); Intro.
Elim (le_lt_dec j O); Intros; Simpl.
Apply lt_le_trans with j; Try Apply le_lt_trans with i; Auto with arith.
Elim (le_lt_dec n j); Intros; Simpl.
Omega.
Apply lt_O_Sn.
Elim (le_lt_dec n i); Elim (le_lt_dec j O); Intros; Simpl.
Elim (lt_n_n O); Apply lt_le_trans with j; Try Apply le_lt_trans with i; Auto with arith.
Elim (le_lt_dec n j); Intro; Simpl.
Apply lt_reg_l.
Apply simpl_lt_plus_l with n.
Repeat Rewrite <- le_plus_minus; Auto.
Elim (le_not_lt n i); Auto; Apply lt_trans with j; Auto.
Elim (lt_n_n O); Apply lt_trans with i; Auto; Apply lt_le_trans with j; Auto.
Elim (le_lt_dec n j); Intro; Simpl.
Apply lt_le_trans with (S (plus (pred m) (pred n))).
Apply lt_n_S.
Apply Clt_to; Apply (proj1_sig ?? (ProjS2 (h_f' (pred i) (lt_pred' ?? b0 b2)))).
Rewrite plus_n_Sm.
Rewrite <- S_pred with n O.
2: Apply lt_trans with i; Auto.
Replace (plus (pred m) n) with (pred (plus m n)).
Auto with arith.
Cut (S (pred (plus m n)))=(S (plus (pred m) n)); Auto.
Rewrite <- plus_Sn_m.
Rewrite S_pred with m O; Auto with arith.
Apply neq_O_lt.
Intro.
Apply lt_n_n with O.
Apply lt_trans with i; Auto.
Rewrite mn0; Auto.
Apply lt_n_S.
Cut ~~(lt (ProjS1 (h_f' (pred i) (lt_pred' ?? b0 b2))) (ProjS1 (h_f' (pred j) (lt_pred' ?? b1 b3)))); Intro.
Apply not_not_lt; Assumption.
Cut (le (ProjS1 (h_f' (pred j) (lt_pred' ?? b1 b3))) (ProjS1 (h_f' (pred i) (lt_pred' ?? b0 b2)))); Intros.
2: Apply not_lt; Assumption.
Cut (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_f' (pred j) (lt_pred' ?? b1 b3))))))[<=]
  (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_f' (pred i) (lt_pred' ?? b0 b2)))))).
Intro.
2: Apply h_mon'; Assumption.
Cut (f' (pred j) (lt_pred' ?? b1 b3))[<=](f' (pred i) (lt_pred' ?? b0 b2)).
2: Apply leEq_wdl with (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_f' (pred j) (lt_pred' ?? b1 b3)))))).
2: Apply leEq_wdr with (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_f' (pred i) (lt_pred' ?? b0 b2)))))).
2: Assumption.
3: Apply eq_symmetric_unfolded; Exact (proj2_sig ?? (ProjS2 (h_f' (pred j) (lt_pred' ?? b1 b3)))).
2: Apply eq_symmetric_unfolded; Exact (proj2_sig ?? (ProjS2 (h_f' (pred i) (lt_pred' ?? b0 b2)))).
Clear H2 H1; Intro.
Cut (f' ? (lt_pred' ?? b0 b2))[<](f' ? (lt_pred' ?? b1 b3)).
2: Apply f'_mon.
2: Apply lt_pred'; Assumption.
Intro.
ElimType False.
Apply less_irreflexive_unfolded with x:=(f' ? (lt_pred' ?? b1 b3)).
EApply leEq_less_trans; [Apply H1 | Apply H2].
Qed.

Local auxP_lemma2 : (i:nat)(H:(le i n)){H':(Cle (auxP i) ?) | (Pts P i H)[=](Pts Separated_Refinement ? (Cle_to ?? H'))}.
ClearBody h Hh; Intros.
Unfold Separated_Refinement; Simpl.
Unfold Separated_Refinement_fun; Simpl.
Elim (le_lt_dec i O); Intro; Simpl.
Cut i=O; [Intro | Auto with arith].
Generalize H; Clear a0 H; Rewrite H0.
Rewrite auxP_lemma0.
Clear H0; Intros.
Exists (toCle ?? (le_O_n (pred (plus m n)))).
Elim (le_lt_eq_dec ?? (Cle_to ?? (toCle ?? (le_O_n (pred (plus m n)))))); Intro; Simpl.
Elim (le_lt_dec O O); Intro; Simpl.
Apply start.
ElimType False; Inversion b0.
Apply eq_transitive_unfolded with a.
Apply start.
Apply partition_length_zero with Hab.
Cut (le (plus m n) (1)).
Intro.
Elim (plus_eq_one_imp_eq_zero ?? H0); Intro.
Rewrite <- a0; Apply R.
Rewrite <- b1; Apply P.
Generalize b0; Clear b0.
Case (plus m n).
Auto.
Intros.
Simpl in b0; Rewrite <- b0; Auto.
Elim (le_lt_eq_dec ?? H); Intro.
Cut (lt (pred i) (pred n)); [Intro | Apply lt_pred; Rewrite <- S_pred with i O; Auto].
Cut (le (auxP i) (pred (plus m n))).
Intro; Exists (toCle ?? H1).
Elim (le_lt_eq_dec ?? (Cle_to ?? (toCle ?? H1))); Intro; Simpl.
Elim (le_lt_dec (auxP i) O); Intro; Simpl.
Cut (auxP i)=O; [Intro | Auto with arith].
Rewrite <- auxP_lemma0 in H2.
Cut (lt (auxP O) (auxP i)); [Intro | Apply auxP_lemma1; Assumption].
ElimType False; Rewrite H2 in H3; Apply (lt_n_n ? H3).
Generalize b1 a1; Clear b1 a1.
Rewrite (auxP_lemmai i b0 a0); Intros.
Simpl.
Elim (ProjS2 (h_f' ? (lt_pred' i n b0 a0))); Intros.
EApply eq_transitive_unfolded.
2: EApply eq_transitive_unfolded.
2: Apply p.
Unfold f'.
Apply prf1; Apply S_pred with O; Auto.
Apply h_nlnf; Reflexivity.
Rewrite <- auxP_lemman in b1.
Cut i=n.
Intro; ElimType False; Rewrite H2 in a0; Apply (lt_n_n ? a0).
Apply nat_mon_imp_inj with h:=auxP.
Apply auxP_lemma1.
Assumption.
Unfold auxP.
Elim (le_lt_dec i O); Intro; Simpl.
Apply le_O_n.
Elim (le_lt_dec n i); Intro; Simpl.
Elim (lt_n_n n); Apply le_lt_trans with i; Auto.
Apply plus_pred_pred_plus.
Elim (ProjS2 (h_f' ? (lt_pred' i n b1 b2))); Intros.
Change (lt (ProjS1 (h_f' ? (lt_pred' ?? b1 b2))) (plus (pred m) (pred n))).
Apply Clt_to; Assumption.
Generalize H; Clear H; Rewrite b1; Intro.
Rewrite auxP_lemman.
Exists (toCle ?? (le_n (pred (plus m n)))).
Elim (le_lt_eq_dec ?? (Cle_to ?? (toCle ?? (le_n (pred (plus m n)))))); Intro; Simpl.
ElimType False; Apply (lt_n_n ? a0).
Apply finish.
Qed.

Lemma Separated_Refinement_lft : (Refinement P Separated_Refinement).
ClearBody h Hh.
Clear auxR.
Exists auxP; Repeat Split.
Exact auxP_lemman.
Intros; Apply auxP_lemma1; Assumption.
Exact auxP_lemma2.
Qed.

Local auxR_lemma0 : (auxR O)=O.
ClearBody h Hh; Unfold auxR.
Elim (le_lt_dec O O); Intro; Simpl.
Reflexivity.
ElimType False; Inversion b0.
Qed.

Local auxR_lemmai : (i:nat)(Hi:(lt O i))(Hi':(lt i m))(auxR i)=(S (ProjS1 (h_g' (pred i) (lt_pred' ?? Hi Hi')))).
ClearBody h Hh; Intros.
Unfold auxR.
Elim (le_lt_dec m i); Intro; Simpl.
ElimType False; Apply le_not_lt with m i; Auto.
Elim (le_lt_dec i O); Intro; Simpl.
ElimType False; Apply lt_n_n with O; Apply lt_le_trans with i; Auto.
LetTac x:=(ProjS1 (h_g' ? (lt_pred' ?? b1 b0))).
LetTac y:=(ProjS1 (h_g' ? (lt_pred' ?? Hi Hi'))).
Cut x=y.
Intro; Auto with arith.
Cut {Hj:(Clt ??) | (g' ? (lt_pred' ?? b1 b0))[=](h x (Clt_to ?? Hj))}; [Intro | Exact (ProjS2 (h_g' ? (lt_pred' ?? b1 b0)))].
Cut {Hj:(Clt ??) | (g' ? (lt_pred' ?? Hi Hi'))[=](h y (Clt_to ?? Hj))}; [Intro | Exact (ProjS2 (h_g' ? (lt_pred' ?? Hi Hi')))].
Elim H; Clear H; Intros Hx Hx'.
Elim H0; Clear H0; Intros Hy Hy'.
Apply h_inj with (Clt_to ?? Hx) (Clt_to ?? Hy).
EApply eq_transitive_unfolded.
2: Apply Hy'.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply Hx'.
Apply g'_nlnf; Reflexivity.
Qed.

Local auxR_lemmam : (auxR m)=(pred (plus m n)).
ClearBody h Hh; Unfold auxR.
Elim (le_lt_dec m O); Intro; Simpl.
Cut m=O; [Intro | Auto with arith].
Transitivity (pred m).
Rewrite H; Auto.
Cut O=n; [Intro; Rewrite <- H0; Auto | Apply HP'].
Apply partition_length_zero with Hab; Rewrite <- H; Apply R.
Elim (le_lt_dec m m); Intro; Simpl.
Rewrite <- minus_n_n; Auto.
Elim (lt_n_n ? b1).
Qed.

Local auxR_lemma1 : (i,j:nat)(lt i j)->(lt (auxR i) (auxR j)).
ClearBody h Hh.
Intros; Unfold auxR.
Elim (le_lt_dec i O); Intro.
Elim (le_lt_dec j O); Intros; Simpl.
Apply le_lt_trans with i; Try Apply lt_le_trans with j; Auto with arith.
Elim (le_lt_dec m j); Intros; Simpl.
Omega.
Apply lt_O_Sn.
Elim (le_lt_dec m i); Elim (le_lt_dec j O); Intros; Simpl.
Elim (lt_n_n O); Apply le_lt_trans with i; Try Apply lt_le_trans with j; Auto with arith.
Elim (le_lt_dec m j); Intro; Simpl.
Apply lt_reg_l.
Apply simpl_lt_plus_l with m.
Repeat Rewrite <- le_plus_minus; Auto.
Elim (le_not_lt m i); Auto; Apply lt_trans with j; Auto.
Elim (lt_n_n O); Apply lt_trans with i; Auto; Apply lt_le_trans with j; Auto.
Elim (le_lt_dec m j); Intro; Simpl.
LetTac H0:=nm0; LetTac H1:=mn0; Apply lt_le_trans with (S (plus (pred m) (pred n))).
Apply lt_n_S.
Apply Clt_to; Apply (proj1_sig ?? (ProjS2 (h_g' (pred i) (lt_pred' ?? b0 b2)))).
Rewrite <- plus_Sn_m.
Rewrite <- S_pred with m O.
2: Apply lt_trans with i; Auto.
Replace (plus m (pred n)) with (pred (plus m n)).
Auto with arith.
Cut (S (pred (plus m n)))=(S (plus m (pred n))); Auto.
Rewrite plus_n_Sm.
Rewrite <- S_pred with n O; Auto with arith.
Symmetry; Apply S_pred with O.
Apply lt_le_trans with m; Auto with arith.
Apply lt_trans with i; Auto.
Apply neq_O_lt.
Intro.
Apply lt_n_n with O.
Apply lt_trans with i; Auto.
Rewrite nm0; Auto.
Apply lt_n_S.
Cut ~~(lt (ProjS1 (h_g' (pred i) (lt_pred' ?? b0 b2))) (ProjS1 (h_g' (pred j) (lt_pred' ?? b1 b3)))); Intro.
Apply not_not_lt; Assumption.
Cut (le (ProjS1 (h_g' (pred j) (lt_pred' ?? b1 b3))) (ProjS1 (h_g' (pred i) (lt_pred' ?? b0 b2)))); Intros.
2: Apply not_lt; Assumption.
Cut (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_g' (pred j) (lt_pred' ?? b1 b3))))))[<=]
  (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_g' (pred i) (lt_pred' ?? b0 b2)))))).
Intro.
2: Apply h_mon'; Assumption.
Cut (g' (pred j) (lt_pred' ?? b1 b3))[<=](g' (pred i) (lt_pred' ?? b0 b2)).
2: Apply leEq_wdl with (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_g' (pred j) (lt_pred' ?? b1 b3)))))).
2: Apply leEq_wdr with (h ? (Clt_to ?? (proj1_sig ?? (ProjS2 (h_g' (pred i) (lt_pred' ?? b0 b2)))))).
2: Assumption.
3: Apply eq_symmetric_unfolded; Exact (proj2_sig ?? (ProjS2 (h_g' (pred j) (lt_pred' ?? b1 b3)))).
2: Apply eq_symmetric_unfolded; Exact (proj2_sig ?? (ProjS2 (h_g' (pred i) (lt_pred' ?? b0 b2)))).
Clear H2 H1; Intro.
Cut (g' ? (lt_pred' ?? b0 b2))[<](g' ? (lt_pred' ?? b1 b3)).
2: Apply g'_mon.
2: Apply lt_pred'; Assumption.
Intro.
ElimType False.
Apply less_irreflexive_unfolded with x:=(g' ? (lt_pred' ?? b1 b3)).
EApply leEq_less_trans; [Apply H1 | Apply H2].
Qed.

Local auxR_lemma2 : (j:nat)(H:(le j m)){H':(Cle (auxR j) ?) | (Pts R j H)[=](Pts Separated_Refinement ? (Cle_to ?? H'))}.
ClearBody h Hh; Intros.
Unfold Separated_Refinement; Simpl.
Unfold Separated_Refinement_fun; Simpl.
Elim (le_lt_dec j O); Intro; Simpl.
Cut j=O; [Intro | Auto with arith].
Generalize H; Clear a0 H; Rewrite H0.
Rewrite auxR_lemma0.
Clear H0; Intros.
Exists (toCle ?? (le_O_n (pred (plus m n)))).
Elim (le_lt_eq_dec ?? (Cle_to ?? (toCle ?? (le_O_n (pred (plus m n)))))); Intro; Simpl.
Elim (le_lt_dec O O); Intro; Simpl.
Apply start.
ElimType False; Inversion b0.
Apply eq_transitive_unfolded with a.
Apply start.
Apply partition_length_zero with Hab.
Cut (le (plus m n) (1)).
Intros.
Elim (plus_eq_one_imp_eq_zero ?? H0); Intro.
Rewrite <- a0; Apply R.
Rewrite <- b1; Apply P.
Generalize b0; Clear b0.
Case (plus m n).
Auto.
Intros.
Simpl in b0; Rewrite <- b0; Auto.
Elim (le_lt_eq_dec ?? H); Intro.
Cut (lt (pred j) (pred m)); [Intro | Red; Rewrite <- S_pred with j O; Auto; Apply le_2; Auto].
Cut (le (auxR j) (pred (plus m n))).
Intro; Exists (toCle ?? H1).
Elim (le_lt_eq_dec ?? (Cle_to ?? (toCle ?? H1))); Intro; Simpl.
Elim (le_lt_dec (auxR j) O); Intro; Simpl.
Cut (auxR j)=O; [Intro | Auto with arith].
Rewrite <- auxR_lemma0 in H2.
Cut (lt (auxR O) (auxR j)); [Intro | Apply auxR_lemma1; Assumption].
ElimType False; Rewrite H2 in H3; Apply (lt_n_n ? H3).
Generalize b1 a1; Clear b1 a1.
Rewrite (auxR_lemmai j b0 a0); Intros.
Simpl.
Elim (ProjS2 (h_g' ? (lt_pred' ?? b0 a0))); Intros.
EApply eq_transitive_unfolded.
2: EApply eq_transitive_unfolded.
2: Apply p.
Unfold g'.
Apply prf1; Apply S_pred with O; Auto.
Apply h_nlnf; Reflexivity.
Rewrite <- auxR_lemmam in b1.
Cut j=m.
Intro; ElimType False; Rewrite H2 in a0; Apply (lt_n_n ? a0).
Apply nat_mon_imp_inj with h:=auxR.
Apply auxR_lemma1.
Assumption.
Unfold auxR.
Elim (le_lt_dec j O); Intro; Simpl.
Apply le_O_n.
Elim (le_lt_dec m j); Intro; Simpl.
Rewrite inj_minus_aux.
Rewrite <- plus_n_O; Auto with arith.
Apply lt_not_le; Auto.
Apply plus_pred_pred_plus.
Elim (ProjS2 (h_g' ? (lt_pred' ?? b1 b2))); Intros.
Change (lt (ProjS1 (h_g' ? (lt_pred' ?? b1 b2))) (plus (pred m) (pred n))).
Apply Clt_to; Assumption.
Generalize H; Clear H; Rewrite b1; Intro.
Rewrite auxR_lemmam.
Exists (toCle ?? (le_n (pred (plus m n)))).
Elim (le_lt_eq_dec ?? (Cle_to ?? (toCle ?? (le_n (pred (plus m n)))))); Intro; Simpl.
ElimType False; Apply (lt_n_n ? a0).
Apply finish.
Qed.

Lemma Separated_Refinement_rht : (Refinement R Separated_Refinement).
ClearBody h Hh.
Exists auxR; Repeat Split.
Exact auxR_lemmam.
Intros; Apply auxR_lemma1; Assumption.
Exact auxR_lemma2.
Qed.

End Refining_Separated.
