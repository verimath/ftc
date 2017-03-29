(* $Id: Integral.v,v 1.19 2003/03/13 12:06:19 lcf Exp $ *)

Require Export RefLemma.

Section Lemmas.

Local Sumx_wd_weird : (n,m:nat)m=(S n)->(f:(i:nat)(lt i n)->IR)(g:(i:nat)(lt i m)->IR)
  ((H:?)(g O H)[=]Zero)->((i:nat)(H:?)(H':?)(f i H)[=](g (S i) H'))->(Sumx f)[=](Sumx g).
Intro; Induction n.
Do 2 Intro.
Rewrite H.
Intros; Simpl; Apply eq_symmetric_unfolded.
Stepr (g O (lt_n_Sn O)); Algebra.
Do 2 Intro; Rewrite H; Intros.
Step (Sumx [i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)))[+](f n (lt_n_Sn n)).
Step_final (Sumx [i:nat][Hi:(lt i (S n))](g i (lt_S ?? Hi)))[+](g (S n) (lt_n_Sn (S n))).
Qed.

Lemma Sumx_weird_lemma :
  (n,m,l:nat)l=(S (plus m n))->(f1:(i:nat)(lt i n)->IR)(f2:(i:nat)(lt i m)->IR)(f3:(i:nat)(lt i l)->IR)
    (nat_less_n_fun ?? f1)->(nat_less_n_fun ?? f2)->(nat_less_n_fun ?? f3)->
    ((i:nat)(Hi:?)(Hi':?)(f1 i Hi)[=](f3 i Hi'))->((i:nat)(Hi:?)(Hi':?)(f2 i Hi)[=](f3 (S (plus n i)) Hi'))->((Hi:?)(f3 n Hi)[=]Zero)->
  (Sumx f1)[+](Sumx f2)[=](Sumx f3).
Intros n m.
Induction m.
Intros l Hl.
Simpl in Hl; Rewrite Hl; Intros f1 f2 f3 Hf1 Hf2 Hf3 Hf1_f3 Hf2_f3 Hf3_f3.
Step (Sumx f1)[+]Zero.
Simpl; Apply bin_op_wd_unfolded.
Apply Sumx_wd; Intros; Apply Hf1_f3.
Apply eq_symmetric_unfolded; Apply Hf3_f3.
LetTac l':= (plus (S m) n).
Intros l Hl.
Rewrite Hl; Intros f1 f2 f3 Hf1 Hf2 Hf3 Hf1_f3 Hf2_f3 Hf3_f3.
Apply eq_transitive_unfolded with ((Sumx f1)[+](Sumx [i:nat][Hi:(lt i m)](f2 i (lt_S ?? Hi))))[+](f2 m (lt_n_Sn m)).
Simpl; Algebra.
Stepr (Sumx [i:nat][Hi:(lt i l')](f3 i (lt_S ?? Hi)))[+](f3 l' (lt_n_Sn l')).
Apply bin_op_wd_unfolded.
Apply Hrecm.
Unfold l'; Auto.
Assumption.
Red; Intros; Apply Hf2; Auto.
Red; Intros; Apply Hf3; Auto.
Red; Intros; Apply Hf1_f3.
Red; Intros; Apply Hf2_f3.
Red; Intros; Apply Hf3_f3.
Unfold 1 l'.
Cut (lt (S (plus n m)) (S l')); [Intro | Unfold l'; Simpl; Rewrite plus_sym; Auto].
Apply eq_transitive_unfolded with (f3 ? H).
Apply Hf2_f3.
Apply Hf3; Simpl; Auto with arith.
Qed.

End Lemmas.

Section Integral.

(* Tex_Prose
\chapter{Integral}

Having proved the main properties of partitions and refinements, we will define the integral of a continuous function $F$ in the interval $[a,b]$ as the limit of the sequence of Sums of $F$ for even partitions of increasing number of points.

\begin{convention} All throughout, \verb!a,b! will be real numbers, the interval $[a,b]$ will be denoted by \verb!I! and \verb!F,G! will be continuous functions in \verb!I!.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab:(a[<=]b).
Local I:=(Compact Hab).

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).

Local contF' := (contin_prop ???? contF).

Section Darboux_Sum.

(* Begin_Tex_Verb *)
Definition integral_seq : nat->IR.
(* End_Tex_Verb *)
Intro n.
Apply Even_Partition_Sum with a b Hab F (S n).
Assumption.
Auto.
Defined.

(* Begin_Tex_Verb *)
Lemma Cauchy_Darboux_Seq : (Cauchy_prop integral_seq).
(* End_Tex_Verb *)
Red; Intros e He.
LetTac e':=e[/]?[//](mult_resp_ap_zero ??? (two_ap_zero ?) (max_one_ap_zero b[-]a)).
Cut (Zero[<]e').
Intro He'.
LetTac d:=(proj1_sigS2P ??? (contF' e' He')).
Generalize (proj2b_sigS2P ??? (contF' e' He')); Generalize (proj2a_sigS2P ??? (contF' e' He')); Fold d; Intros H0 H1.
LetTac N:=(proj1_sig ?? (Archimedes (b[-]a)[/]?[//](pos_ap_zero ?? H0))).
Exists N; Intros.
Apply AbsIR_imp_AbsSmall.
Apply leEq_transitive with Two[*]e'[*](b[-]a).
RStepr e'[*](b[-]a)[+]e'[*](b[-]a).
Unfold integral_seq.
Elim (even_partition_refinement ?? Hab ?? (O_S m) (O_S N)).
Intros w Hw.
Elim Hw; Clear Hw; Intros Hw H2 H3.
Unfold Even_Partition_Sum.
Unfold I; Apply second_refinement_lemma with 
  a:=a b:=b F:=F contF:=contF
  Q:=(Even_Partition Hab w (not_to_CNot ? Hw)) 
  He:=He' He':=He'
  fQ:=[i:nat][Hi:(lt i w)]a[+](nring i)[*]((b[-]a)[/](nring w)[//](nring_ap_zero' ?? (not_to_CNot ? Hw))); Fold d.
Assumption.
Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply even_partition_Mesh.
Apply shift_div_leEq.
Apply pos_nring_S.
Apply shift_leEq_mult' with (pos_ap_zero ?? H0).
Assumption.
Apply leEq_transitive with (!nring IR N).
Exact (proj2_sig ?? (Archimedes (b[-]a)[/]d[//](pos_ap_zero ?? H0))).
Apply nring_leEq; Apply le_S; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply even_partition_Mesh.
Apply shift_div_leEq.
Apply pos_nring_S.
Apply shift_leEq_mult' with (pos_ap_zero ?? H0).
Assumption.
Apply leEq_transitive with (!nring IR N).
Exact (proj2_sig ?? (Archimedes (b[-]a)[/]d[//](pos_ap_zero ?? H0))).
Apply nring_leEq; Apply le_n_Sn.
Red; Intros.
Simpl; Split.
Apply leEq_reflexive.
Apply plus_resp_leEq_lft.
Apply mult_resp_leEq_rht.
Apply less_leEq; Apply less_plusOne.
Apply shift_leEq_div.
Step (!nring IR O); Apply nring_less; Apply le_lt_trans with i; Auto with arith.
Apply shift_leEq_minus; RStep a; Auto.
Red; Do 3 Intro; Simpl.
Rewrite H4; Intros.
Algebra.
Unfold e'.
RStep (e[*](b[-]a))[/]?[//](max_one_ap_zero b[-]a).
Apply shift_div_leEq.
Apply pos_max_one.
Apply mult_resp_leEq_lft.
Apply lft_leEq_Max.
Apply less_leEq; Assumption.
Unfold e'.
Apply div_resp_pos.
Apply mult_resp_pos.
Apply pos_two.
Apply pos_max_one.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition integral :=
  (Lim (Build_CauchySeq ?? Cauchy_Darboux_Seq)).
(* End_Tex_Verb *)

End Darboux_Sum.

Section Integral_Thm.

(* Tex_Prose
The following shows that in fact the integral of $F$ is the limit of \emph{any} sequence of partitions of mesh converging to 0.

\begin{convention} Let \verb!e! be a positive real number and \verb!P! be a partition of \verb!I! with \verb!n! points and mesh smaller than the modulus of continuity of \verb!F! for \verb!e!.  Let \verb!fP! be a choice of points respecting \verb!P!.
\end{convention}
*)

Variable n:nat.

Variable P:(Partition Hab n).

Variable e:IR.
Hypothesis He:Zero[<]e.

Local d:=(proj1_sigS2P ??? (contF' e He)).

Hypothesis HmeshP : (Mesh P)[<]d.

Variable fP:(i:nat)(lt i n)->IR.
Hypothesis HfP:(Points_in_Partition P fP).
Hypothesis HfP':(nat_less_n_fun ?? fP).

Hypothesis incF:(included (Compact Hab) (Pred F)).

(* Begin_Tex_Verb *)
Lemma partition_Sum_conv_integral :
  (AbsIR (Partition_Sum HfP incF)[-]integral)[<=]e[*](b[-]a).
(* End_Tex_Verb *)
Apply leEq_wdl with (AbsIR (Partition_Sum HfP (contin_imp_inc ???? contF))[-]integral).
Apply leEq_wdl with (AbsIR (Lim (Cauchy_const (Partition_Sum HfP (contin_imp_inc ???? contF))))[-]integral).
2: Apply AbsIR_wd; Apply cg_minus_wd; [Apply eq_symmetric_unfolded; Apply Lim_const | Algebra].
Unfold integral.
Apply leEq_wdl with (AbsIR (Lim 
  (Build_CauchySeq ?? (Cauchy_minus (Cauchy_const (Partition_Sum HfP (contin_imp_inc ???? contF))) (Build_CauchySeq ?? Cauchy_Darboux_Seq))))).
2: Apply AbsIR_wd; Apply Lim_minus.
EApply leEq_wdl.
2: Apply Lim_abs.
Stepr Zero[+]e[*](b[-]a); Apply shift_leEq_plus; Red; Apply approach_zero_weak.
Intros e' He'.
LetTac ee:=e'[/]?[//](max_one_ap_zero b[-]a).
Apply leEq_transitive with ee[*](b[-]a).
Cut Zero[<]ee.
Intro Hee.
LetTac d':=(proj1_sigS2P ??? (contF' ? Hee)).
Generalize (proj2b_sigS2P ??? (contF' ? Hee)); Generalize (proj2a_sigS2P ??? (contF' ? Hee)); Fold d'; Intros Hd' Hd'0.
Elim (Archimedes (b[-]a)[/]?[//](pos_ap_zero ?? Hd')); Intros k Hk.
Apply shift_minus_leEq.
EApply leEq_wdr.
2: Apply cm_commutes_unfolded.
Apply str_seq_leEq_so_Lim_leEq.
Exists k; Simpl; Intros.
Unfold integral_seq Even_Partition_Sum.
Apply refinement_lemma with contF He Hee.
Assumption.
Fold d'.
EApply less_wdl.
2: Apply eq_symmetric_unfolded; Apply even_partition_Mesh.
Apply shift_div_less.
Apply pos_nring_S.
Apply shift_less_mult' with (pos_ap_zero ?? Hd').
Assumption.
Apply leEq_less_trans with (!nring IR k).
Assumption.
Apply nring_less; Auto with arith.
Assumption.
Red; Do 3 Intro.
Rewrite H0; Intros; Simpl; Algebra.
Unfold ee; Apply div_resp_pos.
Apply pos_max_one.
Assumption.
Unfold ee.
RStep e'[*]((b[-]a)[/]?[//](max_one_ap_zero b[-]a)).
RStepr e'[*]One.
Apply mult_resp_leEq_lft.
Apply shift_div_leEq.
Apply pos_max_one.
Stepr (Max b[-]a One); Apply lft_leEq_Max.
Apply less_leEq; Assumption.
Apply AbsIR_wd; Apply cg_minus_wd.
Unfold Partition_Sum.
Apply Sumx_wd; Intros.
Algebra.
Algebra.
Qed.

End Integral_Thm.

End Integral.

Section Basic_Properties.

(* Tex_Prose
The usual welldefinedness and strong extensionality results hold.

\begin{convention} \verb!Integral! will denote the integral in \verb!I!.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab : a[<=]b.
Local I:=(Compact Hab).

Syntactic Definition Integral:=(integral ?? Hab ?).

Section Well_Definedness.

Variables F,G:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis contG:(Continuous_I Hab G).

(* Begin_Tex_Verb *)
Lemma integral_strext :
  ((Integral contF)[#](Integral contG))->
    {x:IR & (I x) & (Hx,Hx':?)(F x Hx)[#](G x Hx')}.
(* End_Tex_Verb *)
Intro.
Unfold integral in H.
Elim (Lim_ap_imp_seq_ap' ?? H); Intros N HN; Clear H.
Simpl in HN.
Unfold integral_seq Even_Partition_Sum Partition_Sum in HN.
LetTac f':=[i:nat][H:(lt i (S N))]
  (Part F ? (contin_imp_inc ???? contF ? (compact_partition_lemma ?? Hab ? (O_S N) ? (lt_le_weak ?? H))))[*]
  ((Pts (Even_Partition Hab ? (O_S N)) ? H)[-](Pts (Even_Partition Hab ? (O_S N)) i (lt_le_weak ?? H))).
LetTac g':=[i:nat][H:(lt i (S N))]
  (Part G ? (contin_imp_inc ???? contG ? (compact_partition_lemma ?? Hab ? (O_S N) ? (lt_le_weak ?? H))))[*]
  ((Pts (Even_Partition Hab ? (O_S N)) ? H)[-](Pts (Even_Partition Hab ? (O_S N)) i (lt_le_weak ?? H))).
Cut (nat_less_n_fun ?? f'); Intros.
Cut (nat_less_n_fun ?? g'); Intros.
Cut (Sumx f')[#](Sumx g'); Intros.
Elim (Sumx_strext ???? H H0 H1).
Intros n Hn.
Elim Hn; Clear Hn; Intros Hn H'.
Exists a[+](nring n)[*]((b[-]a)[/](nring ?)[//](nring_ap_zero' ?? (O_S N))).
Unfold I; Apply compact_partition_lemma; Auto.
Apply lt_le_weak; Apply Clt_to; Assumption.
Intros.
Elim (bin_op_strext_unfolded ?????? H'); Clear H'; Intro.
EApply ap_well_def_lft_unfolded.
EApply ap_well_def_rht_unfolded.
Apply a0.
Algebra.
Algebra.
ElimType False; Generalize b0; Exact (ap_irreflexive_unfolded ??).
EApply ap_well_def_lft_unfolded.
EApply ap_well_def_rht_unfolded.
Apply HN.
Unfold g' Partition_imp_points; Apply Sumx_wd; Intros; Simpl; Rational.
Unfold f' Partition_imp_points; Apply Sumx_wd; Intros; Simpl; Rational.
Do 3 Intro.
Rewrite H0; Unfold g'; Intros; Algebra.
Do 3 Intro.
Rewrite H; Unfold f'; Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_strext' : (c,d,Hcd,HF1,HF2:?)
  (((integral a b Hab F HF1)[#](integral c d Hcd F HF2))->
    (a[#]c)+(b[#]d)).
(* End_Tex_Verb *)
Intros.
Clear contF contG.
Unfold integral in H.
Elim (Lim_strext ?? H).
Clear H; Intros N HN.
Simpl in HN.
Unfold integral_seq Even_Partition_Sum Partition_Sum in HN.
LetTac f1:=[i:nat][Hi:(lt i (S N))]
  (pfpfun ? ? (contin_imp_inc ???? HF1 ? (Pts_part_lemma ?????? (Partition_imp_points_1 ???? (Even_Partition Hab ? (O_S N))) i Hi)))[*]
    ((Pts (Even_Partition Hab ? (O_S N)) ? Hi)[-](Pts (Even_Partition Hab ? (O_S N)) ? (lt_le_weak ?? Hi))).
LetTac f2:=[i:nat][Hi:(lt i (S N))]
  (pfpfun ? ? (contin_imp_inc ???? HF2 ? (Pts_part_lemma ?????? (Partition_imp_points_1 ???? (Even_Partition Hcd ? (O_S N))) i Hi)))[*]
    ((Pts (Even_Partition Hcd ? (O_S N)) ? Hi)[-](Pts (Even_Partition Hcd ? (O_S N)) ? (lt_le_weak ?? Hi))).
Cut (nat_less_n_fun ?? f1); Intros.
Cut (nat_less_n_fun ?? f2); Intros.
Elim (Sumx_strext ???? H H0 HN).
Clear H0 H HN; Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Unfold f1 f2 in Hi'; Clear f1 f2.
Elim (bin_op_strext_unfolded ?????? Hi'); Clear Hi'; Intro.
Cut (Partition_imp_points ???? (Even_Partition Hab ? (O_S N)) i (Clt_to ?? Hi))[#]
  (Partition_imp_points ???? (Even_Partition Hcd ? (O_S N)) i (Clt_to ?? Hi)); Intros.
2: Exact (pfstrx ?????? a0).
Clear a0; Simpl in H.
Elim (bin_op_strext_unfolded ?????? H); Clear H; Intro.
Left; Auto.
Elim (bin_op_strext_unfolded ?????? b0); Clear b0; Intro.
ElimType False; Generalize a0; Apply ap_irreflexive_unfolded.
Elim (div_strong_ext ??????? b0); Clear b0; Intro.
Elim (cg_minus_strext ????? a0); Clear a0; Intro.
Right; Auto.
Left; Auto.
ElimType False; Generalize b0; Apply ap_irreflexive_unfolded.
Elim (cg_minus_strext ????? b0); Clear b0; Intro.
Simpl in a0.
Elim (bin_op_strext_unfolded ?????? a0); Clear a0; Intro.
Left; Auto.
Elim (bin_op_strext_unfolded ?????? b0); Clear b0; Intro.
ElimType False; Generalize a0; Apply ap_irreflexive_unfolded.
Elim (div_strong_ext ??????? b0); Clear b0; Intro.
Elim (cg_minus_strext ????? a0); Clear a0; Intro.
Right; Auto.
Left; Auto.
ElimType False; Generalize b0; Apply ap_irreflexive_unfolded.
Elim (bin_op_strext_unfolded ?????? b0); Clear b0; Intro.
Left; Auto.
Elim (bin_op_strext_unfolded ?????? b0); Clear b0; Intro.
ElimType False; Generalize a0; Apply ap_irreflexive_unfolded.
Elim (div_strong_ext ??????? b0); Clear b0; Intro.
Elim (cg_minus_strext ????? a0); Clear a0; Intro.
Right; Auto.
Left; Auto.
Elim (bin_op_strext_unfolded ?????? b0); Clear b0; Intro.
ElimType False; Generalize a0; Apply ap_irreflexive_unfolded.
ElimType False; Generalize b0; Apply ap_irreflexive_unfolded.
Red.
Do 3 Intro.
Rewrite H0; Clear H0; Intros.
Unfold f2.
Algebra.
Red.
Do 3 Intro.
Rewrite H; Clear H; Intros.
Unfold f1.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_wd :
  (Feq (Compact Hab) F G)->((Integral contF)[=](Integral contG)).
(* End_Tex_Verb *)
Intro.
Apply not_ap_imp_eq.
Intro.
Elim (integral_strext H0).
Intros x H1 H2.
Inversion_clear H.
Inversion_clear H3.
Generalize (H2 (contin_imp_inc ???? contF x H1) (contin_imp_inc ???? contG x H1)).
Apply eq_imp_not_ap.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_wd' : (a',b',Hab',contF':?)(a[=]a')->(b[=]b')->
  (Integral contF)[=](integral a' b' Hab' F contF').
(* End_Tex_Verb *)
Intros.
Unfold integral.
Apply Lim_wd'.
Intro; Simpl.
Unfold integral_seq Even_Partition_Sum Partition_Sum.
Apply Sumx_wd; Intros; Apply mult_wd.
Apply pfwdef; Simpl; Algebra.
Simpl.
Repeat First [Apply cg_minus_wd | Apply bin_op_wd_unfolded | Apply mult_wd | Apply div_wd]; Algebra.
Qed.

End Well_Definedness.

Section Linearity_and_Monotonicity.

Opaque Even_Partition.

(* Tex_Prose
The integral is a linear and monotonous function; in order to prove these facts we also need the important equalities $\int_a^bdx=b-a$ and $\int_a^af(x)dx=0$.
*)

(* Begin_Tex_Verb *)
Lemma integral_one : (H:(Continuous_I Hab {-C-}One))
  (Integral H)[=](b[-]a).
(* End_Tex_Verb *)
Intro.
Unfold integral.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply Lim_const.
Apply Lim_wd'.
Intro; Simpl.
Unfold integral_seq Even_Partition_Sum Partition_Sum.
EApply eq_transitive_unfolded.
Apply Mengolli_Sum with f:=[i:nat][Hi:(le i (S n))](Pts (Even_Partition Hab ? (O_S n)) i Hi).
Red; Intros.
Apply prf1; Auto.
Intros; Simpl; Rational.
Apply cg_minus_wd; [Apply finish | Apply start].
Qed.

(* Begin_Tex_Verb *)
Lemma integral_comm_scal : (c:IR)(F:PartIR)
  (Hf:(Continuous_I Hab F))(Hf':(Continuous_I Hab c{**}F))
    (Integral Hf')[=]c[*](Integral Hf).
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with (Lim (Cauchy_const c))[*](Integral Hf); Unfold integral.
EApply eq_transitive_unfolded.
2: Apply Lim_mult.
Apply Lim_wd'; Intro; Simpl.
Unfold integral_seq Even_Partition_Sum Partition_Sum.
EApply eq_transitive_unfolded.
2: Apply Sumx_comm_scal'.
Apply Sumx_wd; Intros; Simpl; Rational.
Apply mult_wd_lft.
Apply eq_symmetric_unfolded; Apply Lim_const.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_plus : (F,G:PartIR)
  (Hf:(Continuous_I Hab F))(Hg:(Continuous_I Hab G))
  (Hfg:(Continuous_I Hab F{+}G))
    (Integral Hfg)[=](Integral Hf)[+](Integral Hg).
(* End_Tex_Verb *)
Intros.
Unfold integral.
EApply eq_transitive_unfolded.
2: Apply Lim_plus.
Apply Lim_wd'; Intro; Simpl.
Unfold integral_seq Even_Partition_Sum Partition_Sum.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply Sumx_plus_Sumx.
Apply Sumx_wd; Intros; Simpl; Rational.
Qed.

Variables F,G:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis contG:(Continuous_I Hab G).

Transparent Even_Partition.

(* Begin_Tex_Verb *)
Lemma integral_empty : (a[=]b)->(Integral contF)[=]Zero.
(* End_Tex_Verb *)
Intros.
Unfold integral.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply Lim_const.
Apply Lim_wd'.
Intros; Simpl.
Unfold integral_seq Even_Partition_Sum Partition_Sum.
Apply eq_transitive_unfolded with (Sumx [i:nat][H:(lt i (S n))](Zero::IR)).
Apply Sumx_wd; Intros; Simpl.
EApply eq_transitive_unfolded.
Apply dist_2a.
Apply x_minus_x.
Apply mult_wd_rht.
Apply bin_op_wd_unfolded.
Algebra.
Step (nring (S i))[*]((b[-]b)[/]?[//](nring_ap_zero' ?? (O_S n))).
Stepr (nring i)[*]((b[-]b)[/]?[//](nring_ap_zero' ?? (O_S n))).
Rational.
EApply eq_transitive_unfolded.
Apply sumx_const.
Algebra.
Qed.

(* Tex_Prose
\begin{convention} Let \verb!alpha,beta:IR! and asSume that \verb!h:=alpha{**}F{+}beta{**}G! is continuous.
\end{convention}
*)

Variables alpha,beta:IR.
Local h:=alpha{**}F{+}beta{**}G.
Hypothesis contH:(Continuous_I Hab h).

(* Begin_Tex_Verb *)
Lemma linear_integral : (Integral contH)[=]
  alpha[*](Integral contF)[+]beta[*](Integral contG).
(* End_Tex_Verb *)
Cut (Continuous_I Hab alpha{**}F); [Intro | Contin].
Cut (Continuous_I Hab beta{**}G); [Intro | Contin].
Apply eq_transitive_unfolded with (Integral H)[+](Integral H0).
Unfold h.
Apply integral_plus.
Apply bin_op_wd_unfolded; Apply integral_comm_scal.
Qed.

(* Begin_Tex_Verb *)
Lemma monotonous_integral :
  ((x:IR)(I x)->(Hx,Hx':?)(F x Hx)[<=](G x Hx'))->
    (Integral contF)[<=](Integral contG).
(* End_Tex_Verb *)
Intros.
Unfold integral.
Apply Lim_leEq_Lim.
Intro n; Simpl.
Unfold integral_seq Even_Partition_Sum Partition_Sum.
Apply Sumx_resp_leEq; Intros i Hi.
Apply mult_resp_leEq_rht.
Apply H.
Opaque nring.
Unfold I Partition_imp_points; Simpl.
Apply compact_partition_lemma; Auto with arith.
Apply leEq_transitive with (AntiMesh (Even_Partition Hab (S n) (O_S n))).
Apply AntiMesh_nonneg.
Apply AntiMesh_lemma.
Qed.

Transparent nring.

End Linearity_and_Monotonicity.

Section Corollaries.

Variables F,G:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis contG:(Continuous_I Hab G).

(* Tex_Prose
As corollaries we can calculate integrals of group operations applied to functions.
*)

(* Begin_Tex_Verb *)
Lemma integral_const : (c:IR)
  (H:(Continuous_I Hab {-C-}c))(Integral H)[=]c[*](b[-]a).
(* End_Tex_Verb *)
Intros.
Cut (Continuous_I Hab c{**}{-C-}One); [Intro | Contin].
Apply eq_transitive_unfolded with (Integral H0).
Apply integral_wd; FEQ.
EApply eq_transitive_unfolded.
Apply integral_comm_scal with Hf:=(Continuous_I_const a b Hab One).
Apply mult_wd_rht.
Apply integral_one.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_minus : (H:(Continuous_I Hab F{-}G))
  (Integral H)[=](Integral contF)[-](Integral contG).
(* End_Tex_Verb *)
Intro.
Cut (Continuous_I Hab (One{**}F){+}([--]One{**}G)); [Intro | Contin].
Apply eq_transitive_unfolded with (Integral H0).
Apply integral_wd; FEQ.
EApply eq_transitive_unfolded.
Apply linear_integral with contF:=contF contG:=contG.
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_inv : (H:(Continuous_I Hab {--}F))
  (Integral H)[=][--](Integral contF).
(* End_Tex_Verb *)
Intro.
Cut (Continuous_I Hab (Zero{**}F){+}([--]One{**}F)); [Intro | Contin].
Apply eq_transitive_unfolded with (Integral H0).
Apply integral_wd; FEQ.
EApply eq_transitive_unfolded.
Apply linear_integral with contF:=contF contG:=contF.
Rational.
Qed.

(* Tex_Prose
We can also bound integrals by bounding the integrated functions.
*)

(* Begin_Tex_Verb *)
Lemma lb_integral : (c:IR)
  ((x:IR)(I x)->(Hx:?)(c[<=](F x Hx)))->
    (c[*](b[-]a))[<=](Integral contF).
(* End_Tex_Verb *)
Intros.
Apply leEq_wdl with (Integral (Continuous_I_const a b Hab c)).
2: Apply integral_const.
Apply monotonous_integral.
Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma ub_integral : (c:IR)
  ((x:IR)(I x)->(Hx:?)(F x Hx)[<=]c)->
    (Integral contF)[<=](c[*](b[-]a)).
(* End_Tex_Verb *)
Intros.
Apply leEq_wdr with (Integral (Continuous_I_const a b Hab c)).
2: Apply integral_const.
Apply monotonous_integral.
Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_leEq_norm :
  (AbsIR (Integral contF))[<=](Norm_Funct contF)[*](b[-]a).
(* End_Tex_Verb *)
Simpl; Unfold ABSIR.
Apply Max_leEq.
Apply ub_integral.
Intros; EApply leEq_transitive.
Apply leEq_AbsIR.
Unfold I; Apply norm_bnd_AbsIR; Assumption.
Stepr [--][--]((Norm_Funct contF)[*](b[-]a)).
Stepr [--]([--](Norm_Funct contF)[*](b[-]a)).
Apply inv_resp_leEq.
Apply lb_integral.
Intros; Stepr [--][--](Part F x Hx).
Apply inv_resp_leEq.
EApply leEq_transitive.
Apply inv_leEq_AbsIR.
Unfold I; Apply norm_bnd_AbsIR; Assumption.
Qed.

End Corollaries.

Section Integral_Sum.

(* Tex_Prose
We now relate the Sum of integrals in adjoining intervals to the integral over the union of those intervals.

\begin{convention} Let \verb!c! be a real number such that $c\in[a,b]$.
\end{convention}
*)

Variable F:PartIR.

Variable c:IR.

Hypothesis Hac:a[<=]c.
Hypothesis Hcb:c[<=]b.

Hypothesis Hab':(Continuous_I Hab F).
Hypothesis Hac':(Continuous_I Hac F).
Hypothesis Hcb':(Continuous_I Hcb F).

Section Partition_Join.

(* Tex_Prose
We first prove that every pair of partitions, one of $[a,c]$ and another of $[c,b]$ defines a partition of $[a,b]$ the mesh of which is less or equal to the maximum of the mesh of the original partitions (actually it is equal, but we don't need the other inequality).

\begin{convention} Let \verb!P,Q! be partitions respectively of $[a,c]$ and $[c,b]$ with \verb!n! and \verb!m! points.
\end{convention}
*)

Variables n,m:nat.
Variable P:(Partition Hac n).
Variable Q:(Partition Hcb m).

(* Begin_Tex_Verb *)
Lemma partition_join_aux : (i,n,m:nat)(lt n i)->
  (le i (S (plus n m)))->(le (minus i (S n)) m).
(* End_Tex_Verb *)
Intros; Omega.
Qed.

(* Begin_Tex_Verb *)
Definition partition_join_fun :
  (i:nat)(le i (S (plus n m)))->IR.
(* End_Tex_Verb *)
Intros.
Elim (le_lt_dec i n); Intros.
Apply (Pts P i a0).
Cut (le (minus i (S n)) m); [Intro | Apply partition_join_aux; Assumption].
Apply (Pts Q ? H0).
Defined.

Lemma pjf_1 : (i:nat)(Hi:?)(Hi':?)(partition_join_fun i Hi)[=](Pts P i Hi').
Intros; Unfold partition_join_fun.
Elim le_lt_dec; Intro; Simpl.
Apply prf1; Auto.
ElimType False; Apply le_not_lt with i n; Auto.
Qed.

Lemma pjf_2 : (i:nat)(Hi:?)i=n->(partition_join_fun i Hi)[=]c.
Intros; Unfold partition_join_fun.
Generalize Hi; Clear Hi.
Rewrite H; Clear H; Intro.
Elim le_lt_dec; Intro; Simpl.
Apply finish.
ElimType False; Apply lt_n_n with n; Auto.
Qed.

Lemma pjf_2' : (i:nat)(Hi:?)i=(S n)->(partition_join_fun i Hi)[=]c.
Intros; Unfold partition_join_fun.
Generalize Hi; Clear Hi.
Rewrite H; Clear H; Intro.
Elim le_lt_dec; Intro; Simpl.
ElimType False; Apply (le_Sn_n ? a0).
Cut (H:?)(Pts Q (minus n n) H)[=]c; Auto.
Cut (minus n n)=O; [Intro | Auto with arith].
Rewrite H; Intros; Apply start.
Qed.

Lemma pjf_3 : (i,j:nat)(Hi:?)(Hj:?)(lt n i)->(j=(minus i (S n)))->(partition_join_fun i Hi)[=](Pts Q j Hj).
Intros; Unfold partition_join_fun.
Generalize Hj; Rewrite H0; Clear Hj; Intros.
Elim le_lt_dec; Intro; Simpl.
ElimType False; Apply le_not_lt with i n; Auto.
Apply prf1; Auto.
Qed.

Lemma partition_join_prf1 : (i,j:nat)i=j->(Hi:?)(Hj:?)(partition_join_fun i Hi)[=](partition_join_fun j Hj).
Intros.
Unfold partition_join_fun.
Elim (le_lt_dec i n); Elim (le_lt_dec j n); Intros; Simpl.
Apply prf1; Auto.
ElimType False; Apply le_not_lt with i n.
Assumption.
Rewrite H; Assumption.
ElimType False; Apply le_not_lt with j n.
Assumption.
Rewrite <- H; Assumption.
Apply prf1; Auto.
Qed.

Lemma partition_join_prf2 : (i:nat)(H:?)(H':?)(partition_join_fun i H)[<=](partition_join_fun (S i) H').
Intros.
Unfold partition_join_fun.
Elim (le_lt_dec i n); Elim (le_lt_dec (S i) n); Intros; Simpl.
Apply prf2.
Cut n=i; [Intro | Apply le_antisym; Auto with arith].
Change (Pts P i a0)[<=](Pts Q (minus (S i) (S n)) (partition_join_aux ??? b0 H')).
Generalize H' a0 b0; Clear H' a0 b0.
Rewrite <- H0; Intros.
Apply eq_imp_leEq.
Apply eq_transitive_unfolded with c.
Apply finish.
Apply eq_transitive_unfolded with (Pts Q O (le_O_n ?)).
Apply eq_symmetric_unfolded; Apply start.
Apply prf1; Auto with arith.
ElimType False; Apply le_not_lt with n i; Auto with arith.
Cut (minus i n)=(S (minus i (S n))); [Intro | Omega].
Cut (le (S (minus i (S n))) m); [Intro | Omega].
Apply leEq_wdr with (Pts Q ? H1).
Apply prf2.
Apply prf1; Auto.
Qed.

Lemma partition_join_start : (H:?)(partition_join_fun O H)[=]a.
Intro.
Unfold partition_join_fun.
Elim (le_lt_dec O n); Intro; Simpl.
Apply start.
ElimType False; Apply (lt_n_O ? b0).
Qed.

Lemma partition_join_finish : (H:?)(partition_join_fun (S (plus n m)) H)[=]b.
Intro.
Unfold partition_join_fun.
Elim le_lt_dec; Intro; Simpl.
ElimType False; Apply le_Sn_n with n; Apply le_trans with (S (plus n m)); Auto with arith.
Apply eq_transitive_unfolded with (Pts Q ? (le_n ?)).
Apply prf1; Auto with arith.
Apply finish.
Qed.

(* Begin_Tex_Verb *)
Definition partition_join : (Partition Hab (S (plus n m))).
(* End_Tex_Verb *)
Intros.
Apply Build_Partition with partition_join_fun.
Exact partition_join_prf1.
Exact partition_join_prf2.
Exact partition_join_start.
Exact partition_join_finish.
Defined.

(* Tex_Prose
\begin{convention} \verb!fP,fQ! are choices of points respecting \verb!P! and \verb!Q!.
\end{convention}
*)

Variable fP : (i:nat)(lt i n)->IR.
Hypothesis HfP : (Points_in_Partition P fP).
Hypothesis HfP' : (nat_less_n_fun ?? fP).

Variable fQ : (i:nat)(lt i m)->IR.
Hypothesis HfQ : (Points_in_Partition Q fQ).
Hypothesis HfQ' : (nat_less_n_fun ?? fQ).

Lemma partition_join_aux' : (i,n,m:nat)(lt n i)->(lt i (S (plus n m)))->(lt (minus i (S n)) m).
Intros; Omega.
Qed.

(* Begin_Tex_Verb *)
Definition partition_join_pts : (i:nat)(lt i (S (plus n m)))->IR.
(* End_Tex_Verb *)
Intros.
Elim (le_lt_dec i n); Intros.
Elim (le_lt_eq_dec ?? a0); Intro.
Apply (fP i a1).
Apply c.
Cut (lt (minus i (S n)) m); [Intro | Apply partition_join_aux'; Assumption].
Apply (fQ ? H0).
Defined.

Local pjp_1 : (i:nat)(Hi:?)(Hi':?)(partition_join_pts i Hi)[=](fP i Hi').
Intros; Unfold partition_join_pts.
Elim le_lt_dec; Intro; Simpl.
Elim le_lt_eq_dec; Intro; Simpl.
Algebra.
ElimType False; Rewrite b0 in Hi'; Apply (lt_n_n ? Hi').
ElimType False; Apply le_not_lt with i n; Auto with arith.
Qed.

Local pjp_2 : (i:nat)(Hi:?)i=n->(partition_join_pts i Hi)[=]c.
Intros; Unfold partition_join_pts.
Elim le_lt_dec; Intro; Simpl.
Elim le_lt_eq_dec; Intro; Simpl.
ElimType False; Rewrite H in a1; Apply (lt_n_n ? a1).
Algebra.
ElimType False; Rewrite H in b0; Apply (lt_n_n ? b0).
Qed.

Local pjp_3 : (i:nat)(Hi:?)(Hi':?)(lt n i)->(partition_join_pts i Hi)[=](fQ (minus i (S n)) Hi').
Intros; Unfold partition_join_pts.
Elim le_lt_dec; Intro; Simpl.
ElimType False; Apply le_not_lt with i n; Auto.
Cut (fQ ? (partition_join_aux' ??? b0 Hi))[=](fQ ? Hi').
2: Apply HfQ'; Auto.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma partition_join_Pts_in_partition :
  (Points_in_Partition partition_join partition_join_pts).
(* End_Tex_Verb *)
Red; Intros.
Cut (H':?)(compact (Pts partition_join i (lt_le_weak ?? H)) (Pts partition_join (S i) H) H' (partition_join_pts i H)); Auto.
Unfold partition_join; Simpl.
Unfold partition_join_fun.
Elim le_lt_dec; Elim le_lt_dec; Intros; Simpl.
Elim (le_lt_eq_dec ?? a1); Intro.
Elim (HfP ? a2); Intros.
Apply compact_wd with (fP i a2).
2: Apply eq_symmetric_unfolded; Apply pjp_1.
Split.
EApply leEq_wdl.
Apply a3.
Apply prf1; Auto.
EApply leEq_wdr.
Apply b0.
Apply prf1; Auto.
ElimType False; Clear H'; Rewrite b0 in a0; Apply (le_Sn_n ? a0).
Cut i=n; [Intro | Clear H'; Apply le_antisym; Auto with arith].
Generalize H a0 b0 H'; Clear H' a0 b0 H; Rewrite H0; Intros.
Apply compact_wd with c.
2: Apply eq_symmetric_unfolded; Apply pjp_2; Auto.
Split.
Apply eq_imp_leEq; Apply finish.
Apply eq_imp_leEq; Apply eq_symmetric_unfolded.
Cut (H:?)(Pts Q (minus n n) H)[=]c; Auto.
Cut (minus n n)=O; [Intro | Auto with arith].
Rewrite H1; Intros; Apply start.
ElimType False; Apply le_not_lt with n i; Auto with arith.
Elim (HfQ ? (partition_join_aux' ??? b1 H)); Intros.
Apply compact_wd with (fQ ? (partition_join_aux' ??? b1 H)).
2: Apply eq_symmetric_unfolded; Apply pjp_3; Assumption.
Split.
EApply leEq_wdl.
Apply a0.
Apply prf1; Auto.
EApply leEq_wdr.
Apply b2.
Apply prf1; Rewrite minus_Sn_m; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma partition_join_Pts_wd : (i,j:nat)i=j->(Hi,Hj:?)
  (partition_join_pts i Hi)[=](partition_join_pts j Hj).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_dec i n); Intro.
Elim (le_lt_eq_dec ?? a0); Intro.
Cut (lt j n); [Intro | Rewrite <- H; Assumption].
EApply eq_transitive_unfolded.
Apply pjp_1 with Hi':=a1.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply pjp_1 with Hi':=H0.
Apply HfP'; Auto.
Cut j=n; [Intro | Rewrite <- H; Assumption].
EApply eq_transitive_unfolded.
Apply pjp_2; Auto.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply pjp_2; Auto.
Algebra.
Cut (lt n j); [Intro | Rewrite <- H; Assumption].
Cut (lt (minus i (S n)) m); [Intro | Omega].
Cut (lt (minus j (S n)) m); [Intro | Omega].
EApply eq_transitive_unfolded.
Apply pjp_3 with Hi':=H1; Assumption.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply pjp_3 with Hi':=H2; Assumption.
Apply HfQ'; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma partition_join_Sum_lemma : 
  (Partition_Sum HfP (contin_imp_inc ???? Hac'))[+]
    (Partition_Sum HfQ (contin_imp_inc ???? Hcb'))[=]
  (Partition_Sum partition_join_Pts_in_partition
                 (contin_imp_inc ???? Hab')).
(* End_Tex_Verb *)
Unfold Partition_Sum; Apply Sumx_weird_lemma.
Auto with arith.
Opaque partition_join.
Red; Intros; Apply mult_wd; Algebra; Apply cg_minus_wd; Apply prf1; Auto.
Red; Intros; Apply mult_wd; Algebra; Apply cg_minus_wd; Apply prf1; Auto.
Red; Intros; Apply mult_wd; Try Apply cg_minus_wd; Try Apply pfwdef; Algebra.
Apply partition_join_Pts_wd; Auto.
Apply prf1; Auto.
Apply prf1; Auto.
Transparent partition_join.
Intros; Apply mult_wd.
Apply pfwdef; Apply eq_symmetric_unfolded; Apply pjp_1.
Apply cg_minus_wd; Simpl.
Unfold partition_join_fun; Elim le_lt_dec; Simpl; Intro; [Apply prf1; Auto | ElimType False; Apply le_not_lt with n i; Auto with arith].
Unfold partition_join_fun; Elim le_lt_dec; Simpl; Intro; [Apply prf1; Auto | ElimType False; Apply le_not_lt with i n; Auto with arith].
Intros; Apply mult_wd.
Apply pfwdef.
Cut i=(minus (S (plus n i)) (S n)); [Intro | Omega].
Generalize Hi; Clear Hi; Pattern 1 2 i; Rewrite H; Intro.
Apply eq_symmetric_unfolded; Apply pjp_3; Auto with arith.
Apply cg_minus_wd; Simpl.
Opaque minus.
Unfold partition_join partition_join_fun.
Elim le_lt_dec; Simpl; Intro.
ElimType False; Apply le_Sn_n with n; EApply le_trans.
2: Apply a0.
Auto with arith.
Transparent minus.
Apply prf1; Transitivity (minus (S (plus n i)) n); Auto with arith.
Opaque minus.
Unfold partition_join partition_join_fun.
Elim le_lt_dec; Simpl; Intro.
ElimType False; Apply le_Sn_n with n; EApply le_trans.
2: Apply a0.
Auto with arith.
Transparent minus.
Apply prf1; Transitivity (minus (plus n i) n); Auto with arith.
Intro; Apply x_mult_zero.
Stepr (Pts partition_join ? Hi)[-](Pts partition_join ? Hi).
Apply cg_minus_wd.
Algebra.
Unfold partition_join; Simpl.
Apply eq_transitive_unfolded with c; Unfold partition_join_fun; Elim le_lt_dec; Simpl.
Intro; Apply finish.
Intro; ElimType False; Apply (lt_n_n ? b0).
Intro; ElimType False; Apply (le_Sn_n ? a0).
Intro; Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with (Pts Q ? (le_O_n ?)).
Apply prf1; Auto with arith.
Apply start.
Qed.

(* Begin_Tex_Verb *)
Lemma partition_join_mesh :
  (Mesh partition_join)[<=](Max (Mesh P) (Mesh Q)).
(* End_Tex_Verb *)
Unfold 1 Mesh.
Apply maxlist_leEq.
Apply length_Part_Mesh_List.
Apply lt_O_Sn.
Intros.
Elim (Part_Mesh_List_lemma ?????? H); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Elim Hi'; Clear Hi'; Intros Hi' Hx.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply Hx.
Unfold partition_join; Simpl.
Unfold partition_join_fun.
Elim le_lt_dec; Intro; Simpl.
Elim le_lt_dec; Intro; Simpl.
EApply leEq_transitive.
Apply Mesh_lemma.
Apply lft_leEq_Max.
ElimType False; Apply le_not_lt with i n; Auto with arith.
Elim le_lt_dec; Intro; Simpl.
Cut i=n; [Intro | Apply le_antisym; Auto with arith].
Generalize a0 b0 Hi'; Clear Hx Hi Hi' a0 b0.
Rewrite H0; Intros.
Apply leEq_wdl with (Zero::IR).
EApply leEq_transitive.
2: Apply lft_leEq_Max.
Apply Mesh_nonneg.
Step c[-]c.
Apply eq_symmetric_unfolded; Apply cg_minus_wd.
Cut (H:?)(Pts Q (minus n n) H)[=]c; Auto.
Cut (minus n n)=O; [Intro | Auto with arith].
Rewrite H1; Intros; Apply start.
Apply finish.
Cut (minus i n)=(S (minus i (S n))); [Intro | Omega].
Cut (H:?)(Pts Q (minus i n) H)[-](Pts Q ? (partition_join_aux ??? b1 (Cle_to ?? Hi)))[<=](Max (Mesh P) (Mesh Q)); Auto.
Rewrite H0; Intros; EApply leEq_transitive.
Apply Mesh_lemma.
Apply rht_leEq_Max.
Qed.

End Partition_Join.

(* Tex_Prose
With these results in mind, the following is a trivial consequence:
*)

(* Begin_Tex_Verb *)
Lemma integral_plus_integral : 
  (integral ?? Hac ? Hac')[+](integral ?? Hcb ? Hcb')
    [=](integral ?? Hab ? Hab').
(* End_Tex_Verb *)
Unfold 1 2 integral.
EApply eq_transitive_unfolded.
Apply eq_symmetric_unfolded; Apply Lim_plus.
Apply cg_inv_unique_2.
Apply AbsIR_approach_zero.
Intros e' He'.
LetTac e:=e'[/]?[//](max_one_ap_zero b[-]a).
Cut Zero[<]e.
Intro He.
LetTac d:=(proj1_sigS2P ??? (contin_prop ???? Hab' e He)).
Generalize (proj2b_sigS2P ??? (contin_prop ???? Hab' e He)); Generalize (proj2a_sigS2P ??? (contin_prop ???? Hab' e He)).
Fold d; Intros Hd Haux.
Clear Haux.
Apply leEq_transitive with e[*](b[-]a).
Elim (Archimedes (b[-]c)[/]?[//](pos_ap_zero ?? Hd)); Intros n1 Hn1.
Elim (Archimedes (c[-]a)[/]?[//](pos_ap_zero ?? Hd)); Intros n2 Hn2.
Apply leEq_wdl with 
  (Lim (Build_CauchySeq ?? (Cauchy_abs 
    (Build_CauchySeq ?? (Cauchy_plus
      (Build_CauchySeq ?? (Cauchy_plus
        (Build_CauchySeq ?? (Cauchy_Darboux_Seq ?? Hac ? Hac'))
        (Build_CauchySeq ?? (Cauchy_Darboux_Seq ?? Hcb ? Hcb'))))
      (Cauchy_const [--](integral ?? Hab ? Hab'))))))).
Apply str_seq_leEq_so_Lim_leEq.
LetTac p:=(max n1 n2); Exists p; Intros.
Step (AbsIR ((integral_seq ?? Hac ? Hac' i)[+](integral_seq ?? Hcb ? Hcb' i))[-](integral ?? Hab ? Hab')).
Unfold integral_seq Even_Partition_Sum.
LetTac EP1:=(Even_Partition Hac (S i) (O_S i)).
LetTac EP2:=(Even_Partition Hcb (S i) (O_S i)).
LetTac P:=(partition_join ?? EP1 EP2).
Cut (nat_less_n_fun ?? (Partition_imp_points ???? EP1)); [Intro | Apply Partition_imp_points_2].
Cut (nat_less_n_fun ?? (Partition_imp_points ???? EP2)); [Intro | Apply Partition_imp_points_2].
Apply leEq_wdl with (AbsIR (Partition_Sum (partition_join_Pts_in_partition ????? 
  (Partition_imp_points_1 ???? EP1) H0 ? (Partition_imp_points_1 ???? EP2) H1) (contin_imp_inc ???? Hab'))[-](integral ?? Hab ? Hab')).
Apply partition_Sum_conv_integral with He; Fold d.
EApply leEq_less_trans.
Apply partition_join_mesh.
Apply Max_less.
Unfold EP1; EApply less_wdl.
2: Apply eq_symmetric_unfolded; Apply even_partition_Mesh.
Apply swap_div with (pos_ap_zero ?? Hd).
Apply pos_nring_S.
Assumption.
Apply leEq_less_trans with (!nring IR n2).
Assumption.
Apply nring_less.
Apply le_lt_trans with p.
Unfold p; Apply le_max_r.
Auto with arith.
Unfold EP2; EApply less_wdl.
2: Apply eq_symmetric_unfolded; Apply even_partition_Mesh.
Apply swap_div with (pos_ap_zero ?? Hd).
Apply pos_nring_S.
Assumption.
Apply leEq_less_trans with (!nring IR n1).
Assumption.
Apply nring_less.
Apply le_lt_trans with p.
Unfold p; Apply le_max_l.
Auto with arith.
Red; Do 3 Intro.
Rewrite H2; Clear H2; Intros.
Apply partition_join_Pts_wd; Auto.
Apply AbsIR_wd.
Apply cg_minus_wd.
2: Algebra.
Apply eq_symmetric_unfolded.
Unfold Partition_Sum; Apply Sumx_weird_lemma.
Auto.
Red; Do 3 Intro.
Rewrite H2; Clear H2; Intros; Algebra.
Red; Do 3 Intro.
Rewrite H2; Clear H2; Intros; Algebra.
Red; Do 3 Intro.
Rewrite H2; Clear H2; Intros; Algebra.
Opaque Even_Partition.
Intros; Apply mult_wd.
Apply pfwdef; Unfold partition_join_pts.
Elim le_lt_dec; Intro; Simpl.
Elim le_lt_eq_dec; Intro; Simpl.
Apply Partition_imp_points_2; Auto.
ElimType False; Rewrite b0 in Hi; Apply (lt_n_n ?  Hi).
ElimType False; Apply le_not_lt with i0 (S i); Auto with arith.
Apply cg_minus_wd; Simpl.
Apply eq_symmetric_unfolded; Apply pjf_1.
Apply eq_symmetric_unfolded; Apply pjf_1.
Intros; Apply mult_wd.
Apply pfwdef; Unfold Partition_imp_points.
Unfold partition_join_pts.
Elim le_lt_dec; Intro; Simpl.
Elim le_lt_eq_dec; Intro; Simpl.
ElimType False; Apply le_Sn_n with (S i); EApply le_trans.
2: Apply a0.
Auto with arith.
ElimType False; Apply lt_n_n with (S i); Pattern 2 (S i); Rewrite <- b0; Auto with arith.
Unfold Partition_imp_points; Apply prf1.
Auto with arith.
Apply cg_minus_wd; Simpl.
Apply eq_symmetric_unfolded; Apply pjf_3; [Auto with arith | Omega].
Apply eq_symmetric_unfolded; Apply pjf_3; Auto with arith.
Intro; Apply x_mult_zero.
Stepr c[-]c.
Apply cg_minus_wd.
Simpl; Apply pjf_2'; Auto.
Simpl; Apply pjf_2; Auto.
EApply eq_transitive_unfolded.
Apply Lim_abs.
Apply AbsIR_wd.
Unfold cg_minus.
EApply eq_transitive_unfolded.
Apply Lim_plus.
Apply bin_op_wd_unfolded.
Algebra.
Apply eq_symmetric_unfolded; Apply Lim_const.
Unfold e.
RStep (e'[*](b[-]a))[/]?[//](max_one_ap_zero b[-]a).
Apply shift_div_leEq.
Apply pos_max_one.
Apply mult_resp_leEq_lft.
Apply lft_leEq_Max.
Apply less_leEq; Assumption.
Unfold e.
Apply div_resp_pos.
Apply pos_max_one.
Assumption.
Qed.

End Integral_Sum.

Transparent Even_Partition.

End Basic_Properties.

(* Tex_Prose
The following are simple consequences of this result and of previous ones.
*)

(* Begin_Tex_Verb *)
Lemma integral_less_norm : (a,b,Hab,F,contF:?)
  [N:=(!Norm_Funct a b Hab F contF)](a[<]b)->
  (x:IR)(Compact Hab x)->(Hx:?)((AbsIR (F x Hx))[<]N)->
  (AbsIR (integral ???? contF))[<]N[*](b[-]a).
(* End_Tex_Verb *)
Intros.
Rename H into Hless.
Rename H0 into H.
Rename H1 into H0.
LetTac e:=(N[-](AbsIR (F x Hx)))[/]TwoNZ.
Cut Zero[<]e; Intros.
2: Unfold e; Apply pos_div_two; Apply shift_less_minus.
2: Step (AbsIR (F x Hx)); Auto.
Elim (contin_prop ???? contF e); Auto.
Intros d H2 H3.
LetTac mid1:=(Max a x[-]d).
LetTac mid2:=(Min b x[+]d).
Cut a[<=]mid1; [Intro leEq1 | Unfold mid1; Apply lft_leEq_Max].
Cut mid1[<=]mid2; [Intro leEq2 | Unfold mid1 mid2; Inversion_clear H; Apply leEq_transitive with x].
2: Apply Max_leEq; Auto.
2: Apply less_leEq; Apply shift_minus_less.
2: Apply shift_less_plus'; Step (Zero::IR); Auto.
2: Apply leEq_Min; Auto.
2: Apply less_leEq; Apply shift_less_plus'.
2: Step (Zero::IR); Auto.
Cut mid2[<=]b; [Intro leEq3 | Unfold mid2; Apply Min_leEq_lft].
Cut (Continuous_I leEq1 F).
Cut (Continuous_I leEq2 F).
Cut (Continuous_I leEq3 F).
Intros cont3 cont2 cont1.
Cut (Continuous_I (leEq_transitive ???? leEq1 leEq2) F); Intros.
Apply less_wdl with (AbsIR (integral ???? cont1)[+](integral ???? cont2)[+](integral ???? cont3)).
2: Apply AbsIR_wd.
2: Apply eq_transitive_unfolded with (integral ???? H4)[+](integral ???? cont3).
2: Apply bin_op_wd_unfolded.
2: Apply integral_plus_integral.
2: Algebra.
2: Apply integral_plus_integral.
RStepr N[*](mid1[-]a)[+]N[*](mid2[-]mid1)[+]N[*](b[-]mid2).
EApply leEq_less_trans.
Apply triangle_IR.
Apply plus_resp_less_leEq.
EApply leEq_less_trans.
Apply triangle_IR.
Apply plus_resp_leEq_less.
EApply leEq_transitive.
Apply integral_leEq_norm.
Unfold N; Apply mult_resp_leEq_rht.
2: Apply shift_leEq_minus; Step a; Auto.
Apply included_imp_norm_leEq.
Apply included_compact.
Apply compact_inc_lft.
Split.
Unfold mid1; Apply lft_leEq_Max.
Apply leEq_transitive with mid2; Auto.
2: EApply leEq_transitive.
2: Apply integral_leEq_norm.
2: Unfold N; Apply mult_resp_leEq_rht.
3: Apply shift_leEq_minus; Step mid2; Auto.
2: Apply included_imp_norm_leEq.
2: Apply included_compact.
2: Split.
2: Apply leEq_transitive with mid1; Auto.
2: Auto.
2: Apply compact_inc_rht.
EApply leEq_less_trans.
Apply integral_leEq_norm.
Apply mult_resp_less.
Apply leEq_less_trans with N[-]e.
2: Apply shift_minus_less; Apply shift_less_plus'.
2: Step (Zero::IR); Auto.
Apply leEq_Norm_Funct; Intros y Hy Hy'.
Apply leEq_wdr with (AbsIR (F x Hx))[+]e.
2: Unfold e; Rational.
Apply AbsIR_bnd_AbsIR.
Apply H3; Auto.
Cut (included (Compact leEq2) (Compact Hab)); Auto.
Apply included_compact.
Split; Auto.
Apply leEq_transitive with mid2; Auto.
Split; Auto.
Apply leEq_transitive with mid1; Auto.
Cut (x[-]d)[<=](x[+]d); Intros.
Apply compact_bnd_AbsIR with H5.
Cut (included (Compact leEq2) (Compact H5)); Auto.
Apply included_compact; Unfold mid1 mid2; Split.
Apply rht_leEq_Max.
Apply leEq_transitive with mid2; Auto.
Unfold mid2; Apply Min_leEq_rht.
Apply leEq_transitive with mid1; Auto.
Unfold mid1; Apply rht_leEq_Max.
Apply Min_leEq_rht.
Apply leEq_transitive with x.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Unfold mid2 mid1.
Step x[-]x.
Unfold 1 2 cg_minus.
Inversion_clear H.
Elim (cotrans_less_unfolded ??? Hless x); Intro.
Apply plus_resp_leEq_less.
Apply leEq_Min; Auto.
Apply shift_leEq_plus'; Step (Zero::IR); Apply less_leEq; Auto.
Apply inv_resp_less; Apply Max_less; Auto.
Apply shift_minus_less; Apply shift_less_plus'.
Step (Zero::IR); Auto.
Apply plus_resp_less_leEq.
Apply less_Min; Auto.
Apply shift_less_plus'; Step (Zero::IR); Auto.
Apply inv_resp_leEq; Apply Max_leEq; Auto.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Apply compact_inc_lft.
Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply compact_inc_rht.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Split; Auto.
Apply leEq_transitive with mid2; Auto.
Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Apply compact_inc_lft.
Split; Auto.
Apply leEq_transitive with mid2; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma integral_gt_zero : (a,b,Hab,F,contF:?)
  [N:=(!Norm_Funct a b Hab F contF)]
  (a[<]b)->
  (x:IR)(Compact Hab x)->(Hx:?)(Zero[<](F x Hx))->
  ((x:IR)(Compact Hab x)->(Hx:?)(Zero[<=](F x Hx)))->
  Zero[<](integral ???? contF).
(* End_Tex_Verb *)
Intros.
Rename H into Hless.
Rename H0 into H.
Rename H1 into H0.
LetTac e:=(F x Hx)[/]TwoNZ.
Cut Zero[<]e; Intros.
2: Unfold e; Apply pos_div_two; Auto.
Elim (contin_prop ???? contF e); Auto.
Intros d H3 H4.
LetTac mid1:=(Max a x[-]d).
LetTac mid2:=(Min b x[+]d).
Cut a[<=]mid1; [Intro leEq1 | Unfold mid1; Apply lft_leEq_Max].
Cut mid1[<=]mid2; [Intro leEq2 | Unfold mid1 mid2; Inversion_clear H; Apply leEq_transitive with x].
2: Apply Max_leEq; Auto.
2: Apply less_leEq; Apply shift_minus_less.
2: Apply shift_less_plus'; Step (Zero::IR); Auto.
2: Apply leEq_Min; Auto.
2: Apply less_leEq; Apply shift_less_plus'.
2: Step (Zero::IR); Auto.
Cut mid2[<=]b; [Intro leEq3 | Unfold mid2; Apply Min_leEq_lft].
Cut (Continuous_I leEq1 F).
Cut (Continuous_I leEq2 F).
Cut (Continuous_I leEq3 F).
Intros cont3 cont2 cont1.
Cut (Continuous_I (leEq_transitive ???? leEq1 leEq2) F); Intros.
Apply less_wdr with (integral ???? cont1)[+](integral ???? cont2)[+](integral ???? cont3).
2: Apply eq_transitive_unfolded with (integral ???? H5)[+](integral ???? cont3).
2: Apply bin_op_wd_unfolded.
2: Apply integral_plus_integral.
2: Algebra.
2: Apply integral_plus_integral.
RStep Zero[*](mid1[-]a)[+]Zero[*](mid2[-]mid1)[+]Zero[*](b[-]mid2).
Apply plus_resp_less_leEq.
Apply plus_resp_leEq_less.
Apply lb_integral.
Intros.
Apply H2.
Inversion_clear H6; Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply leEq_transitive with mid2; Auto.
Apply less_leEq_trans with ((F x Hx)[/]TwoNZ)[*](mid2[-]mid1).
Apply mult_resp_less.
Apply pos_div_two; Auto.
Apply shift_less_minus; Step mid1.
Elim (cotrans_less_unfolded ??? Hless x); Intro; Unfold mid1 mid2.
Apply less_leEq_trans with x.
Apply Max_less.
Auto.
Apply shift_minus_less; Apply shift_less_plus'.
Step (Zero::IR); Auto.
Apply leEq_Min.
Inversion_clear H; Auto.
Apply less_leEq; Apply shift_less_plus'.
Step (Zero::IR); Auto.
Apply leEq_less_trans with x.
Apply Max_leEq.
Inversion_clear H; Auto.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Apply less_Min.
Auto.
Apply shift_less_plus'.
Step (Zero::IR); Auto.
Apply lb_integral.
Intros.
RStep (F x Hx)[-](F x Hx)[/]TwoNZ.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Fold e; EApply leEq_transitive; [Apply leEq_AbsIR | Apply H4].
Auto.
Inversion_clear H6; Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply leEq_transitive with mid2; Auto.
Cut (x[-]d)[<=](x[+]d); Intros.
Apply compact_bnd_AbsIR with H7.
Cut (included (Compact leEq2) (Compact H7)); Auto.
Apply included_compact; Unfold mid1 mid2; Split.
Apply rht_leEq_Max.
Apply leEq_transitive with mid2; Auto.
Unfold mid2; Apply Min_leEq_rht.
Apply leEq_transitive with mid1; Auto.
Unfold mid1; Apply rht_leEq_Max.
Apply Min_leEq_rht.
Apply leEq_transitive with x.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Apply lb_integral.
Intros.
Apply H2.
Inversion_clear H6; Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply leEq_transitive with mid2; Auto.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Apply compact_inc_lft.
Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply compact_inc_rht.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Split; Auto.
Apply leEq_transitive with mid2; Auto.
Split; Auto.
Apply leEq_transitive with mid1; Auto.
Apply included_imp_contin with a b Hab; Auto.
Apply included_compact.
Apply compact_inc_lft.
Split; Auto.
Apply leEq_transitive with mid2; Auto.
Qed.
