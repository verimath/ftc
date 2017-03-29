(* $Id: Taylor.v,v 1.16 2003/03/13 12:06:23 lcf Exp $ *)

Require Export TaylorLemma.

Opaque Min Max N_Deriv.

Section More_Taylor_Defs.

(* Tex_Prose
\chapter{Taylor's Theorem (continued)}

The generalization to arbitrary intervals just needs a few more definitions.

\begin{convention} Let \verb!I! be a proper interval, \verb!F:PartIR! and \verb!a,b:IR! be points of \verb!I!.
\end{convention}
*)

Variable I:interval.
Hypothesis pI:(proper I).

Variable F:PartIR.

(* Begin_Tex_Verb *)
Local deriv_Sn [b:IR][n:nat][Hf:(Diffble_n (S n) I pI F)] :=
  ((N_Deriv ???? Hf){*}
    ({-C-}(One[/]?[//](nring_fac_ap_zero ? n)))){*}
    ({-C-}b{-}FId){^}n.
(* End_Tex_Verb *)

Variables a,b:IR.
Hypothesis Ha:(iprop I a).
Hypothesis Hb:(iprop I b).

(* Begin_Tex_Verb *)
Local fi:=[n:nat][Hf:(Diffble_n n I pI F)]
  [i:nat][Hi:(lt i (S n))]
    (N_Deriv ???? (le_imp_Diffble_n ???? (lt_n_Sm_le ?? Hi) ? Hf)).

Local funct_i := [n:nat][Hf:(Diffble_n n I pI F)]
  [i:nat][Hi:(lt i (S n))]
  ({-C-}(((fi n Hf i Hi) a Ha)
    [/]?[//](nring_fac_ap_zero ? i)))
  {*}(FId{-}{-C-}a){^}i.

Definition Taylor_Seq' [n:nat][Hf:(Diffble_n n I pI F)] :=
  (FSumx ? (funct_i n Hf)).
(* End_Tex_Verb *)

Lemma TaylorB : (n,Hf:?)(Pred (Taylor_Seq' n Hf) b).
Repeat Split.
Apply FSumx_pred'; Repeat Split.
Qed.

(* Begin_Tex_Verb *)
Definition Taylor_Rem [n:nat][Hf:(Diffble_n n I pI F)] :=
  (F b (Diffble_n_imp_inc ???? Hf b Hb))[-]
    ((Taylor_Seq' n Hf) b (TaylorB n Hf)).
(* End_Tex_Verb *)

Local Taylor_Sumx_lemma : (n:nat)(x,z:IR)(y,y':?)((H:?)(y O H)[=]z)->((i:nat)(H,H':?)(y' i H')[=](y (S i) H))->
  (x[-](!Sumx IR (S n) y))[=](x[-]z)[-](!Sumx IR n y').
Intro; Induction n.
Intros; Simpl.
Step x[-](Zero[+]z).
Rational.
Intros.
Step x[-]((Sumx [i:nat][l:(lt i (S n))](y i (lt_S ?? l)))[+](y (S n) (lt_n_Sn (S n)))).
RStep (x[-](Sumx [i:nat][l:(lt i (S n))](y i (lt_S ?? l))))[-](y (S n) (lt_n_Sn (S n))).
Stepr (x[-]z)[-]((Sumx [i:nat][l:(lt i n)](y' i (lt_S ?? l)))[+](y' n (lt_n_Sn n))).
RStepr ((x[-]z)[-](Sumx [i:nat][l:(lt i n)](y' i (lt_S ?? l))))[-](y' n (lt_n_Sn n)).
Algebra.
Qed.

Local Taylor_lemma_ap : (n:nat)(Hf:(Diffble_n (S n) I pI F))(Hf':(Diffble_n n I pI F))
  (Ha':?)(((Taylor_Rem n Hf')[-]((deriv_Sn b ? Hf) a Ha')[*](b[-]a))[#]Zero)->a[#]b.
Intros.
LetTac Hpred := (Diffble_n_imp_inc ???? Hf').
Cut (Taylor_Rem n Hf')[-](pfpfun ? ? Ha')[*](b[-]a)[#]Zero[-]Zero.
2: Stepr (Zero::IR); Auto.
Clear H; Intros.
Elim (cg_minus_strext ????? H); Clear H; Intro H.
Unfold Taylor_Rem Taylor_Seq' funct_i in H.
Cut (Pred (FSumx n [i:nat][Hi:(lt i n)]
  ({-C-}(((fi n Hf' (S i) (lt_n_S ?? Hi)) a Ha)[/]?[//](nring_fac_ap_zero IR (S i)))){*}(FId{-}{-C-}a){^}(S i)) b).
2: Apply FSumx_pred'; Repeat Split.
Intro.
Cut (((F b (Hpred b Hb))[-](F a (Hpred a Ha)))[#]Zero)+((pfpfun ? ? H0)[#]Zero); Intros.
Elim H1; Clear H H1; Intro H.
Apply pfstrx with Hx:=(Hpred a Ha) Hy:=(Hpred b Hb).
Apply ap_symmetric_unfolded; Apply zero_minus_apart; Auto.
Cut (good_fun_seq' ? [i:nat][Hi:(lt i n)]
  ({-C-}(((fi n Hf' (S i) (lt_n_S ?? Hi)) a Ha)[/]?[//](nring_fac_ap_zero IR (S i)))){*}(FId{-}{-C-}a){^}(S i)).
2: Red; Repeat Split.
Intro.
Cut (Sumx [i:nat][Hi:(lt i n)](pfpfun ? ? (FSumx_pred n ? H1 ? H0 i Hi)))[#](Sumx [i:nat][Hi:(lt i n)]Zero); Intros.
2: EApply ap_well_def_lft_unfolded.
2: EApply ap_well_def_rht_unfolded.
2: Apply H.
2: Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded; [Apply sumx_const | Algebra].
2: Exact (FSumx_char ???? H1).
Simpl in H2.
Cut (nat_less_n_fun ?? [i:nat][Hi:(lt i n)](((fi n Hf' (S i) (lt_n_S ?? Hi)) a Ha)[/]?[//](nring_fac_ap_zero IR (S i)))[*](
  (nexp IR i (b[+][--]a))[*](b[+][--]a))); Intros.
Cut (nat_less_n_fun IR ? [i:nat][Hi:(lt i n)]Zero); Intros.
Elim (Sumx_strext ???? H3 H4 H2); Clear H H0 H1 H2 H3 H4; Intros N HN.
Elim HN; Clear HN; Intros HN H.
Cut (b[+][--]a)[#]Zero; Intros.
2: EApply cring_mult_ap_zero_op; EApply cring_mult_ap_zero_op; Apply H.
Apply ap_symmetric_unfolded; Apply zero_minus_apart; Auto.
Red; Algebra.
Red; Do 3 Intro.
Rewrite H3; Intros; Unfold fi.
Apply mult_wd_lft.
Apply div_wd.
2: Algebra.
Apply Feq_imp_eq with (iprop I).
Apply Derivative_n_unique with pI (S j) F; Apply N_Deriv_lemma.
Auto.
Apply cg_minus_strext.
Stepr (Zero::IR).
Apply ap_well_def_lft_unfolded with (pfpfun ? ? (Hpred b Hb))[-](pfpfun ? ? (TaylorB n Hf')); Auto.
Unfold Taylor_Seq' funct_i.
Cut (good_fun_seq' ? [i:nat][Hi:(lt i (S n))]{-C-}(((fi n Hf' i Hi) a Ha)[/]?[//](nring_fac_ap_zero IR i)){*}(FId{-}{-C-}a){^}i); Intros.
Apply eq_transitive_unfolded with ((pfpfun ? ? (Hpred b Hb))[-]
  (Sumx [i:nat][Hi:(lt i (S n))](pfpfun ? ? (FSumx_pred ?? H1 b (TaylorB n Hf') i Hi)))).
Apply cg_minus_wd.
Algebra.
Exact (FSumx_char ???? H1).
Cut (good_fun_seq' ? [i:nat][Hi:(lt i n)]
  {-C-}(((fi n Hf' (S i) (lt_n_S ?? Hi)) a Ha)[/]?[//](nring_fac_ap_zero IR (S i))){*}(FId{-}{-C-}a){^}(S i)); Intros.
Apply eq_transitive_unfolded with (((pfpfun ? ? (Hpred b Hb))[-](pfpfun ? ? (Hpred a Ha)))[-]
  (Sumx [i:nat][Hi:(lt i n)](pfpfun ? ? (FSumx_pred ?? H2 b H0 i Hi)))).
2: Apply cg_minus_wd.
2: Algebra.
2: Apply eq_symmetric_unfolded; Exact (FSumx_char ???? H2).
Apply Taylor_Sumx_lemma.
Intros; Simpl.
Unfold fi.
RStepr ((pfpfun ? ? (Hpred a Ha))[/](Zero[+]One)[//](nring_fac_ap_zero IR O))[*]One.
Apply mult_wd_lft; Apply div_wd.
2: Algebra.
Apply Feq_imp_eq with (iprop I).
Apply Derivative_n_unique with pI O F.
Apply N_Deriv_lemma.
Split; Auto.
Split; Auto.
Intros; Simpl.
Apply Feq_reflexive; Included.
Auto.
Intros; Simpl.
Apply mult_wd_lft; Apply div_wd.
2: Algebra.
Unfold fi.
Apply Feq_imp_eq with (iprop I).
Apply Derivative_n_unique with pI (S i) F; Apply N_Deriv_lemma; Auto.
Auto.
Repeat Split.
Repeat Split.
Apply ap_symmetric_unfolded; Apply zero_minus_apart.
EApply cring_mult_ap_zero_op; Apply H.
Qed.

(* Begin_Tex_Verb *)
Theorem Taylor' : (n:nat)(Hf:(Diffble_n (S n) I pI F))
  (Hf':(Diffble_n n I pI F))(e:IR)(Zero[<]e)->{c:IR &
    (Compact (Min_leEq_Max a b) c) | (Hc:?)
  (AbsIR (Taylor_Rem n Hf')[-]
         ((deriv_Sn b ? Hf) c Hc)[*](b[-]a))[<=]e}.
(* End_Tex_Verb *)
Intros.
Cut (Pred (deriv_Sn b n Hf) a); Intros.
2: Repeat Split.
2: Simpl; Auto.
Elim (cotrans_less_unfolded ??? H (AbsIR (Taylor_Rem n Hf')[-](pfpfun ? ? H0)[*](b[-]a))).
Intros.
Cut a[#]b; Intros.
Clear a0 H0.
Cut (Diffble_I_n (ap_imp_Min_less_Max ?? H1) (S n) F); Intros.
2: Apply included_imp_Diffble_n with I pI; Auto.
Cut (Diffble_I_n (ap_imp_Min_less_Max ?? H1) n F); Intros.
2: Apply le_imp_Diffble_I with (S n); Auto.
Elim (Taylor_lemma a b H1 F (Diffble_n_imp_inc ???? Hf b Hb) e H n H2 H0).
Intros c H3 H4.
Exists c; Auto.
Intro.
Cut (Pred ((n_deriv_I ????? H0){*}{-C-}(One[/]?[//](nring_fac_ap_zero ? n))){*}({-C-}b{-}FId){^}n c); Intros.
2: Repeat Split.
2: Apply n_deriv_inc; Auto.
EApply leEq_wdl.
Apply (H4 H5).
Unfold Taylor_rem Taylor_Rem.
Apply AbsIR_wd; Repeat Apply cg_minus_wd.
Algebra.
Simpl.
Repeat First [Apply bin_op_wd_unfolded | Apply mult_wd | Apply div_wd | Apply eq_reflexive_unfolded].
Apply FSumx_wd; Intros; Simpl.
Apply mult_wd_lft.
Apply div_wd.
2: Algebra.
Apply eq_transitive_unfolded with ((PartInt (ProjS1 (Diffble_I_n_imp_deriv_n ????? (le_imp_Diffble_I ????? (lt_n_Sm_le ?? (lt_S ?? Hi)) ? H2)))) a (compact_Min_lft ?? (less_leEq ??? (ap_imp_Min_less_Max ?? H1)))).
Simpl; Algebra.
Apply Feq_imp_eq with (Compact (less_leEq ??? (ap_imp_Min_less_Max ?? H1))).
Apply Derivative_I_n_unique with i F.
Apply projS2.
Unfold fi.
Elim (N_Deriv_lemma ???? (le_imp_Diffble_n I pI i n (lt_n_Sm_le ?? (lt_S ?? Hi)) ? Hf')); Intros incF0 H'.
Elim H'; Intros Hinc derivF; Clear H'.
Apply derivF.
Simpl; Included.
Apply compact_Min_lft.
Apply eq_transitive_unfolded with ((PartInt (ProjS1 (Diffble_I_n_imp_deriv_n ????? (le_imp_Diffble_I ????? (lt_n_Sm_le ?? (lt_n_Sn n)) ? H2)))) a (compact_Min_lft ?? (less_leEq ??? (ap_imp_Min_less_Max ?? H1)))).
Simpl; Algebra.
Apply Feq_imp_eq with (Compact (less_leEq ??? (ap_imp_Min_less_Max ?? H1))).
Apply Derivative_I_n_unique with n F.
Apply projS2.
Unfold fi.
Elim (N_Deriv_lemma ???? (le_imp_Diffble_n I pI n n (lt_n_Sm_le ?? (lt_n_Sn n)) ? Hf')); Intros incF0 H'.
Elim H'; Intros Hinc derivF; Clear H'.
Apply derivF.
Simpl; Included.
Apply compact_Min_lft.
Simpl.
Repeat Apply mult_wd_lft.
Apply Feq_imp_eq with (Compact (less_leEq ??? (ap_imp_Min_less_Max ?? H1))).
Apply Derivative_I_n_unique with (S n) F.
Apply Derivative_I_n_wdr with (n_deriv_I ????? H0).
Apply Derivative_I_n_unique with n (n_deriv_I ????? (le_imp_Diffble_I ????? (le_n_S ?? (le_O_n n)) ? H0)).
Cut (HS,HSn:?)(Derivative_I_n (ap_imp_Min_less_Max ?? H1) n (n_deriv_I ?? (ap_imp_Min_less_Max ?? H1) (1) F HS) (n_deriv_I ?? (ap_imp_Min_less_Max ?? H1) (S n) F HSn)); Auto.
Cut (S n)=(plus n (1)); [Intro | Rewrite plus_sym; Auto].
Rewrite H6.
Intros; Apply n_deriv_plus.
EApply Derivative_I_n_wdl.
2: Apply n_deriv_lemma.
Apply Derivative_I_unique with F.
Apply projS2.
Apply Derivative_I_wdl with (n_deriv_I ????? (le_imp_Diffble_I ????? (le_O_n ?) F H0)).
Simpl.
FEQ.
Apply included_trans with (iprop I); Included.
Apply n_Sn_deriv.
Apply n_deriv_lemma.
Elim (N_Deriv_lemma ???? Hf); Intros incF0 H'.
Elim H'; Intros Hinc derivF; Clear H'.
Apply derivF.
Simpl; Included.
Inversion_clear H5.
Inversion_clear H6.
Exact (n_deriv_inc' ???????? H5).
Included.
Cut ((Taylor_Rem n Hf')[-](pfpfun ? ? H0)[*](b[-]a))[#]Zero.
Intro; Exact (Taylor_lemma_ap ???? H1).
Stepr (Zero::IR); Apply AbsIR_cancel_ap_zero; Apply Greater_imp_ap; Auto.
Intro.
Exists a.
Apply compact_Min_lft.
Intro; EApply leEq_wdl.
Apply less_leEq; Apply b0.
Apply AbsIR_wd; Rational.
Qed.

End More_Taylor_Defs.

Section Taylor_Theorem.

(* Tex_Prose
And finally the ``nice'' version, when we know the expression of the derivatives of $F$.

\begin{convention} Let \verb!f! be the sequence of derivatives of \verb!F! of order up to $n$ and \verb!F'! be the $n$th-derivative of \verb!F!.
\end{convention}
*)

Variable I:interval.
Hypothesis pI:(proper I).

Variable F:PartIR.

Variable n:nat.
Variable f:(i:nat)(lt i (S n))->PartIR.

Hypothesis goodF : (good_fun_seq ? f).
Hypothesis goodF' : (good_fun_seq' ? f).

Hypothesis derF : (i:nat)(Hi:(lt i (S n)))
  (Derivative_n i I pI F (f i Hi)).

Variable F':PartIR.
Hypothesis derF' : (Derivative_n (S n) I pI F F').

Variables a,b:IR.
Hypothesis Ha:(iprop I a).
Hypothesis Hb:(iprop I b).

(* Begin_Tex_Verb *)
Local funct_i [i:nat][Hi:(lt i (S n))] :=
  {-C-}(((f i Hi) a (Derivative_n_imp_inc' ????? (derF i Hi) a Ha))
    [/]?[//](nring_fac_ap_zero IR i))
  {*}(FId{-}{-C-}a){^}i.

Definition Taylor_Seq := (FSumx ? funct_i).

Local deriv_Sn := (F'{*}
    {-C-}(One[/]?[//](nring_fac_ap_zero ? n))){*}
  ({-C-}b{-}FId){^}n.

Lemma Taylor_aux : (Pred Taylor_Seq b).
(* End_Tex_Verb *)
Repeat Split.
Apply FSumx_pred'; Repeat Split.
Qed.

(* Begin_Tex_Verb *)
Theorem Taylor : (e:IR)(Zero[<]e)->(Hb':?){c:IR &
  (Compact (Min_leEq_Max a b) c) | (Hc:?)
    (AbsIR ((F b Hb')[-](pfpfun ? ? Taylor_aux))[-]
           (deriv_Sn c Hc)[*](b[-]a))[<=]e}.
(* End_Tex_Verb *)
Intros.
Cut (Diffble_n (S n) I pI F).
Intro Hf.
Cut (Diffble_n n I pI F).
Intro Hf'.
Elim (Taylor' I pI F ?? Ha Hb n Hf Hf' e H); Intros c Hc' Hc.
Exists c.
Auto.
Intros.
Cut (Pred ((N_Deriv ???? Hf){*}{-C-}(One[/]?[//](nring_fac_ap_zero IR n))){*}({-C-}b{-}FId){^}n c); Intros.
EApply leEq_wdl.
Apply (Hc H0).
Apply AbsIR_wd; Simpl; Repeat Apply cg_minus_wd.
2: Repeat Apply mult_wd_lft.
Unfold Taylor_Rem; Simpl.
Apply cg_minus_wd.
Algebra.
Apply bin_op_wd_unfolded.
Apply Feq_imp_eq with (Compact (Min_leEq_Max a b)).
Apply FSumx_wd'.
Unfold funct_i; Intros; Simpl.
Apply Feq_mult.
FEQ.
Simpl.
Apply div_wd.
Apply Feq_imp_eq with (iprop I).
Apply Derivative_n_unique with pI i F.
Apply N_Deriv_lemma.
Apply derF.
Auto.
Algebra.
Apply Feq_reflexive; Repeat Split.
Apply compact_Min_rht.
Apply mult_wd_lft.
Apply div_wd.
2: Algebra.
Apply Feq_imp_eq with (iprop I).
Apply Derivative_n_unique with pI n F.
Apply N_Deriv_lemma.
Apply derF.
Auto.
Apply Feq_imp_eq with (iprop I).
Apply Derivative_n_unique with pI (S n) F.
Apply N_Deriv_lemma.
Assumption.
Cut (included (Compact (Min_leEq_Max a b)) (iprop I)); Included.
Repeat Split.
Transparent N_Deriv.
Simpl.
Cut (included (Compact (Min_leEq_Max a b)) (iprop I)); Included.
Apply Derivative_n_imp_Diffble_n with (f n (lt_n_Sn n)).
Apply derF.
Apply Derivative_n_imp_Diffble_n with F'.
Assumption.
Qed.

End Taylor_Theorem.
