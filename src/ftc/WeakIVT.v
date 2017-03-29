Require Export Continuity.

(* Tex_Prose
\chapter{IVT for Partial Functions}

In general, we cannot prove the classically valid Intermediate Value Theorem
for arbitrary partial functions, which states that in any interval $[a,b]$, for any
value $z$ between $f(a)$ and $f(b)$ there exists $x\in[a,b]$ such that $f(x)=z$.

However, as is usually the case, there are some good aproximation results.  We
will prove them here.
*)

Section Lemma1.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.

Local I:=(Compact Hab).

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).

(* Tex_Prose
\section{First Lemmas}

\begin{convention} Let \verb!a,b:IR! and \verb!Hab:a[<=]b! and denote by \verb!I! the interval
$[a,b]$.  Let \verb!F! be a continuous function on \verb!I!.
\end{convention}

We begin by proving that, if $f(a)<f(b)$, then for every $y$ in 
$[f(a),f(b)]$ there is an $x\in[a,b]$ such that $f(x)$ is close
enough to $z$.
*)

(* Begin_Tex_Verb *)
Lemma Weak_IVT_ap_lft : (Ha,Hb:?)(HFab:(F a Ha)[<](F b Hb))
  (e:IR)(Zero[<]e)->(z:IR)(Compact (less_leEq ??? HFab) z)->
  {x:IR & (Compact Hab x) | ((Hx:?)(AbsIR (F x Hx)[-]z)[<=]e)}.
(* End_Tex_Verb *)
Intros.
Cut a[<]b.
Intro Hab'.
LetTac G:=(FAbs (F{-}{-C-}z)).
Cut (Continuous_I Hab G); Intros.
2: Unfold G; Contin.
LetTac m:=(glb_funct ???? H1).
Elim (glb_is_glb ???? H1).
Fold m; Intros.
Simpl in a0; Simpl in b0.
Cut (x:IR)(Compact Hab x)->(Hx:?)(m[<=](AbsIR (F x Hx)[-]z)); [Clear a0; Intro a0 | Intros].
Elim (cotrans_less_unfolded ??? H m); Intros.
Elim H0; Clear H0; Intros H0 H0'.
Cut (F a Ha)[-]z[<=][--]m; Intros.
Cut m[<=](F b Hb)[-]z; Intros.
ElimType False.
Elim (contin_prop ???? contF m a1); Intros d H4 H5.
LetTac incF:=(contin_imp_inc ???? contF).
LetTac f:=[i,Hi:?](F (compact_part ?? Hab' d H4 i Hi) (incF ? (compact_part_hyp ?? Hab Hab' d H4 i Hi)))[-]z.
LetTac n:=(compact_nat a b d H4).
Cut (i,Hi:?)((f i Hi)[<=]Zero).
Intros.
Apply (less_irreflexive_unfolded ? (F b Hb)[-]z).
EApply less_leEq_trans.
2: Apply H3.
Apply leEq_less_trans with (Zero::IR).
2: Auto.
Apply leEq_wdl with (f ? (le_n n)); Auto.
Unfold f compact_part n; Simpl.
Apply cg_minus_wd; [Apply pfwdef; Rational | Algebra].
Induction i.
Intros; Unfold f compact_part.
RStep (F a Ha)[-]z.
Apply leEq_transitive with [--]m; Auto.
Stepr [--](Zero::IR); Apply less_leEq; Apply inv_resp_less; Auto.
Intros i' Hrec HSi'.
Stepr m[-]m.
Apply shift_leEq_minus'.
Cut (le i' n); [Intro Hi' | Auto with arith].
Apply leEq_transitive with [--](f ? Hi')[+](f ? HSi').
Apply plus_resp_leEq.
Cut {m[<=](f ? Hi')}+{(f ? Hi')[<=][--]m}.
Intro; Inversion_clear H6.
ElimType False.
Apply (less_irreflexive_unfolded ? m).
Apply leEq_less_trans with (Zero::IR).
EApply leEq_transitive; [Apply H7 | Apply (Hrec Hi')].
Auto.
Step [--][--]m; Apply inv_resp_leEq; Auto.
Apply leEq_distr_AbsIR.
Assumption.
Unfold f; Apply a0; Apply compact_part_hyp.
RStep (f ? HSi')[-](f ? Hi').
EApply leEq_transitive.
Apply leEq_AbsIR.
Unfold f; Simpl.
Apply leEq_wdl with 
  (AbsIR (F ? (incF ? (compact_part_hyp ?? Hab Hab' d H4 ? HSi')))[-](F ? (incF ? (compact_part_hyp ?? Hab Hab' d H4 ? Hi')))).
Apply H5; Try Apply compact_part_hyp.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply compact_leEq.
Apply less_leEq; Apply compact_less.
Apply AbsIR_wd; Rational.
EApply leEq_wdr.
2: Apply AbsIR_eq_x.
Apply a0; Apply compact_inc_rht.
Apply shift_leEq_minus; Step z; Auto.
Step [--][--]((F a Ha)[-]z); Apply inv_resp_leEq.
EApply leEq_wdr.
2: Apply AbsIR_eq_inv_x.
Apply a0; Apply compact_inc_lft.
Apply shift_minus_leEq; Stepr z; Auto.
Elim (b0 e[-]m); Intros.
Elim p; Clear p b0; Intros Hx Hx'.
Exists x; Auto.
Intros.
Apply less_leEq.
Apply plus_cancel_less with [--]m.
Unfold cg_minus in Hx'.
EApply less_wdl.
Apply Hx'.
Apply bin_op_wd_unfolded; [Apply AbsIR_wd; Rational | Algebra].
Apply shift_less_minus; Step m; Auto.
EApply leEq_wdr.
Apply (a0 x H2).
Apply AbsIR_wd; Rational.
LetTac H1:=(less_imp_ap ??? HFab).
LetTac H2:=(pfstrx ?????? H1).
Elim (ap_imp_less ??? H2); Intro.
Auto.
ElimType False.
Apply (less_irreflexive_unfolded ? a).
Apply leEq_less_trans with b; Auto.
Qed.

End Lemma1.

Section Lemma2.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.

Local I:=(Compact Hab).

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).

(* Tex_Prose
If $f(b)<f(a)$, a similar result holds:
*)

(* Begin_Tex_Verb *)
Lemma Weak_IVT_ap_rht : (Ha,Hb:?)(HFab:(F b Hb)[<](F a Ha))
  (e:IR)(Zero[<]e)->(z:IR)(Compact (less_leEq ??? HFab) z)->
  {x:IR & (Compact Hab x) | (Hx:?)(AbsIR (F x Hx)[-]z)[<=]e}.
(* End_Tex_Verb *)
Intros.
LetTac G:={--}F.
Cut (Continuous_I Hab G); [Intro contG | Unfold G; Contin].
Cut ((G a Ha)[<](G b Hb)).
Intro HGab.
2: Unfold G; Simpl; Apply inv_resp_less; Auto.
Cut (Compact (less_leEq ??? HGab) [--]z); Intros.
2: Inversion_clear H0; Split; Unfold G; Simpl; Apply inv_resp_leEq; Auto.
Elim (Weak_IVT_ap_lft ???? contG ?? HGab ? H ? H1); Intros x Hx.
Exists x; Auto.
Intro; EApply leEq_wdl.
Apply (q Hx0).
EApply eq_transitive_unfolded.
Apply AbsIR_minus.
Apply AbsIR_wd; Unfold G; Simpl; Rational.
Qed.

End Lemma2.

Section IVT.

(* Tex_Prose
\section{The IVT}

We will now assume that $a<b$ and that \verb!F! is not only
continuous, but also strictly increasing in \verb!I!.  Under
these assumptions, we can build two sequences of values which
converge to $x_0$ such that $f(x_0)=z$.
*)

Variables a,b:IR.
Hypothesis Hab' : a[<]b.
Hypothesis Hab : a[<=]b.

Local I := (Compact Hab).

Variable F:PartIR.
Hypothesis contF : (Continuous_I Hab F).
Local incF:=(contin_imp_inc ???? contF).

(* Begin_Tex_Verb *)
Hypothesis incrF : (x,y:IR)(I x)->(I y)->
  (x[<]y)->(Hx,Hy:?)(F x Hx)[<](F y Hy).
(* End_Tex_Verb *)

Local Ha:=(compact_inc_lft ?? Hab).
Local Hb:=(compact_inc_rht ?? Hab).

Local HFab' := (incrF ?? Ha Hb Hab' (incF ? Ha) (incF ? Hb)).

(* Begin_Tex_Verb *)
Variable z:IR.
Hypothesis Haz:(F a (incF ? Ha))[<=]z.
Hypothesis Hzb:z[<=](F b (incF ? Hb)).
(* End_Tex_Verb *)

(* Tex_Prose
Given any two points $x<y\in[a,b]$ such that $x\leq z\leq y$, we
can find $x'<y'$ such that $|x'-y'|=\frac23|x-y|$ and $x'\leq z\leq y'$.
*)

(* Begin_Tex_Verb *)
Lemma IVT_seq_lemma : (xy:IR*IR)[x:=(Fst xy)][y:=(Snd xy)]
  (Hxy:(I x)*(I y))[Hx:=(Fst Hxy)][Hy:=(Snd Hxy)](x[<]y)->
  ((F x (incF ? Hx))[<=]z)/\(z[<=](F y (incF ? Hy)))->
  {xy0:IR*IR & [x0:=(Fst xy0)][y0:=(Snd xy0)]{Hxy0:(I x0)*(I y0) &
    (x0[<]y0) |
    [Hx0:=(Fst Hxy0)][Hy0:=(Snd Hxy0)]
     ((F x0 (incF ? Hx0))[<=]z) /\ (z[<=](F y0 (incF ? Hy0))) /\
     ((y0[-]x0)[=](Two[/]ThreeNZ)[*](y[-]x)) /\ (x[<=]x0) /\ (y0[<=]y)}}.
(* End_Tex_Verb *)
Intros.
LetTac x1:=(Two[*]x[+]y)[/]ThreeNZ.
LetTac y1:=(x[+]Two[*]y)[/]ThreeNZ.
Cut x1[<]y1; Intros.
2: Unfold x1 y1; Apply lft_rht; Auto.
Cut (I x1); Intros.
Cut (I y1); Intros.
Cut (F x1 (incF ? H2))[<](F y1 (incF ? H3)); Intros; Auto.
Elim (cotrans_less_unfolded ??? H4 z); Intros.
Exists (x1,y); Exists (H2,Hy); Simpl; Repeat Split; Auto.
Apply less_transitive_unfolded with y1; Unfold x1 y1; [Apply lft_rht | Apply rht_b]; Auto.
Apply less_leEq; Auto.
Elim H0; Auto.
Unfold x1; Apply smaller_rht.
Unfold x1; Apply less_leEq; Apply a_lft; Auto.
Apply leEq_reflexive.
Exists (x,y1); Exists (Hx,H3); Simpl; Repeat Split; Auto.
Apply less_transitive_unfolded with x1; Unfold x1 y1; [Apply a_lft | Apply lft_rht]; Auto.
Elim H0; Auto.
Apply less_leEq; Auto.
Unfold y1; Apply smaller_lft; Auto.
Apply leEq_reflexive.
Apply less_leEq; Unfold y1; Apply rht_b; Auto.
Unfold y1; Inversion_clear Hx; Inversion_clear Hy; Split.
Apply leEq_transitive with x; Auto.
Apply less_leEq; Apply less_transitive_unfolded with x1; Unfold x1; [Apply a_lft | Apply lft_rht]; Auto.
Apply leEq_transitive with y; Auto.
Apply less_leEq; Apply rht_b; Auto.
Unfold x1; Inversion_clear Hx; Inversion_clear Hy; Split.
Apply leEq_transitive with x; Auto.
Apply less_leEq; Apply a_lft; Auto.
Apply leEq_transitive with y; Auto.
Apply less_leEq; Apply less_transitive_unfolded with y1; Unfold y1; [Apply lft_rht | Apply rht_b]; Auto.
Qed.

(* Tex_Prose
We now iterate this construction.
*)

(* Begin_Tex_Verb *)
Record IVT_aux_seq_type : Set :=
  {IVTseq1 : IR;
   IVTseq2 : IR;
   IVTH1   : (I IVTseq1);
   IVTH2   : (I IVTseq2);
   IVTprf  : IVTseq1[<]IVTseq2;
   IVTz1   : (F IVTseq1 (incF ? IVTH1))[<=]z;
   IVTz2   : z[<=](F IVTseq2 (incF ? IVTH2))}.

Definition IVT_iter : IVT_aux_seq_type->IVT_aux_seq_type.
(* End_Tex_Verb *)
Intro Haux; Elim Haux; Intros.
Elim (IVT_seq_lemma (IVTseq3,IVTseq4) (IVTH3,IVTH4) IVTprf0 (conj ?? IVTz3 IVTz4)).
Intro x; Elim x; Simpl; Clear x; Intros.
Elim p.
Intro x; Elim x; Simpl; Clear x; Intros.
Inversion_clear q.
Inversion_clear H0.
Inversion_clear H2.
Inversion_clear H3.
Apply Build_IVT_aux_seq_type with a0 b0 a1 b1; Auto.
Defined.

(* Begin_Tex_Verb *)
Definition IVT_seq : nat->IVT_aux_seq_type.
(* End_Tex_Verb *)
Intro n; Induction n.
Apply Build_IVT_aux_seq_type with a b Ha Hb; Auto.
Apply (IVT_iter Hrecn).
Defined.

(* Tex_Prose
We now define $a_n$ and $b_n$ to be the sequences built from this iteration,
starting with $a_0=a$ and $b_0=b$.
*)

(* Begin_Tex_Verb *)
Definition a_seq := [n:nat](IVTseq1 (IVT_seq n)).
Definition b_seq := [n:nat](IVTseq2 (IVT_seq n)).

Definition a_seq_I [n:nat] : (I (a_seq n)) := (IVTH1 (IVT_seq n)).
Definition b_seq_I [n:nat] : (I (b_seq n)) := (IVTH2 (IVT_seq n)).

Lemma a_seq_less_b_seq : (n:nat)(a_seq n)[<](b_seq n).
(* End_Tex_Verb *)
Exact [n:nat](IVTprf (IVT_seq n)).
Qed.

(* Begin_Tex_Verb *)
Lemma a_seq_leEq_z : (n:nat)(F ? (incF ? (a_seq_I n)))[<=]z.
(* End_Tex_Verb *)
Exact [n:nat](IVTz1 (IVT_seq n)).
Qed.

(* Begin_Tex_Verb *)
Lemma z_leEq_b_seq : (n:nat)z[<=](F ? (incF ? (b_seq_I n))).
(* End_Tex_Verb *)
Exact [n:nat](IVTz2 (IVT_seq n)).
Qed.

(* Begin_Tex_Verb *)
Lemma a_seq_mon : (i:nat)(a_seq i)[<=](a_seq (S i)).
(* End_Tex_Verb *)
Intro.
Unfold a_seq.
Simpl.
Elim IVT_seq; Simpl; Intros.
Elim IVT_seq_lemma; Simpl; Intro.
Elim x; Simpl; Clear x; Intros.
Elim p; Clear p; Intro.
Elim x; Simpl; Clear x; Intros.
Case q; Clear q; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Case a2; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma b_seq_mon : (i:nat)(b_seq (S i))[<=](b_seq i).
(* End_Tex_Verb *)
Intro.
Unfold b_seq.
Simpl.
Elim IVT_seq; Simpl; Intros.
Elim IVT_seq_lemma; Simpl; Intro.
Elim x; Simpl; Clear x; Intros.
Elim p; Clear p; Intro.
Elim x; Simpl; Clear x; Intros.
Case q; Clear q; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Case a2; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma a_seq_b_seq_dist_n : (n:nat)((b_seq (S n))[-](a_seq (S n)))[=](Two[/]ThreeNZ)[*]((b_seq n)[-](a_seq n)).
(* End_Tex_Verb *)
Intro.
Unfold a_seq b_seq.
Simpl.
Elim IVT_seq; Simpl; Intros.
Elim IVT_seq_lemma; Simpl; Intro.
Elim x; Simpl; Clear x; Intros.
Elim p; Clear p; Intro.
Elim x; Simpl; Clear x; Intros.
Case q; Clear q; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Case a2; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma a_seq_b_seq_dist : (n:nat)((b_seq n)[-](a_seq n))[=](Two[/]ThreeNZ)[^]n[*](b[-]a).
(* End_Tex_Verb *)
Induction n.
Simpl; Algebra.
Clear n; Intros.
Stepr (Two[/]ThreeNZ)[*](Two[/]ThreeNZ)[^]n[*](b[-]a).
Stepr (Two[/]ThreeNZ)[*]((Two[/]ThreeNZ)[^]n[*](b[-]a)).
Stepr (Two[/]ThreeNZ)[*]((b_seq n)[-](a_seq n)).
Apply a_seq_b_seq_dist_n.
Qed.

(* Begin_Tex_Verb *)
Lemma a_seq_Cauchy : (Cauchy_prop a_seq).
(* End_Tex_Verb *)
Red; Intros.
Elim (intervals_small' a b e H); Intros i Hi.
Exists i; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_transitive.
2: Apply Hi.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (a_seq i).
2: Apply local_mon'_imp_mon'; Auto; Exact a_seq_mon.
EApply leEq_wdr.
2: Apply a_seq_b_seq_dist.
Apply minus_resp_leEq.
Apply less_leEq; Apply a_b'.
Exact a_seq_mon.
Exact b_seq_mon.
Exact a_seq_less_b_seq.
Qed.

(* Begin_Tex_Verb *)
Lemma b_seq_Cauchy : (Cauchy_prop b_seq).
(* End_Tex_Verb *)
Red; Intros.
Elim (intervals_small' a b e H); Intros i Hi.
Exists i; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_transitive.
2: Apply Hi.
EApply leEq_wdl.
2: Apply AbsIR_minus.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (b_seq m).
2: Step [--][--](b_seq m); Stepr [--][--](b_seq i).
2: Apply inv_resp_leEq; Apply local_mon'_imp_mon' with f:=[n:nat][--](b_seq n); Auto.
2: Intro; Apply inv_resp_leEq; Apply b_seq_mon.
EApply leEq_wdr.
2: Apply a_seq_b_seq_dist.
Unfold cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq.
Apply less_leEq; Apply a_b'.
Exact a_seq_mon.
Exact b_seq_mon.
Exact a_seq_less_b_seq.
Qed.

Local xa:=(Lim (Build_CauchySeq ?? a_seq_Cauchy)).
Local xb:=(Lim (Build_CauchySeq ?? b_seq_Cauchy)).

(* Tex_Prose
\begin{notation} We denote by $x_a$ and $x_b$ the limits of $a_n$ and $b_n$, respectively.
\end{notation}
*)

(* Begin_Tex_Verb *)
Lemma a_seq_b_seq_lim : xa[=]xb.
(* End_Tex_Verb *)
Unfold xa xb; Clear xa xb.
Apply cg_inv_unique_2.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
2: Apply Lim_minus.
Simpl.
Apply Limits_unique.
Simpl.
Red; Intros.
Elim (intervals_small' a b eps H); Intros i Hi.
Exists i; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_transitive.
2: Apply Hi.
EApply leEq_wdl.
2: Apply AbsIR_minus.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (a_seq m)[-](b_seq m).
2: Apply shift_minus_leEq; Stepr (b_seq m).
2: Apply less_leEq; Apply a_seq_less_b_seq.
EApply leEq_wdr.
2: Apply a_seq_b_seq_dist.
RStep (b_seq m)[-](a_seq m).
Unfold cg_minus; Apply plus_resp_leEq_both.
Step [--][--](b_seq m); Stepr [--][--](b_seq i).
Apply inv_resp_leEq; Apply local_mon'_imp_mon' with f:=[n:nat][--](b_seq n); Auto.
Intro; Apply inv_resp_leEq; Apply b_seq_mon.
Apply inv_resp_leEq; Apply local_mon'_imp_mon'; Auto; Exact a_seq_mon.
Qed.

(* Begin_Tex_Verb *)
Lemma xa_in_interval : (I xa).
(* End_Tex_Verb *)
Split.
Unfold xa.
Apply leEq_seq_so_leEq_Lim.
Simpl.
Intro; Elim (a_seq_I i); Auto.
Unfold xa.
Apply seq_leEq_so_Lim_leEq.
Simpl.
Intro; Elim (a_seq_I i); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma IVT_I : {x:IR & (I x) | (Hx:?)(F x Hx)[=]z}.
(* End_Tex_Verb *)
Exists xa.
Apply xa_in_interval.
Intro.
Apply cg_inv_unique_2; Apply leEq_imp_eq.
Red; Apply approach_zero.
Intros.
Apply leEq_less_trans with e[/]TwoNZ.
2: Apply pos_div_two'; Auto.
Elim (contin_prop ???? contF ? (pos_div_two ?? H)); Intros d H0 H1.
Elim (Cauchy_complete (Build_CauchySeq ?? a_seq_Cauchy) ? H0); Fold xa; Simpl; Intros N HN.
Apply leEq_transitive with (F xa Hx)[-](F (a_seq N) (incF ? (a_seq_I N))).
Unfold cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq; Apply a_seq_leEq_z.
EApply leEq_wdl.
2: Apply AbsIR_eq_x.
Apply H1; Auto.
Apply xa_in_interval.
Apply a_seq_I.
Apply AbsSmall_imp_AbsIR.
Apply AbsSmall_minus.
Auto.
Apply shift_leEq_minus; Step (F  ? (incF ? (a_seq_I N))).
Apply part_mon_imp_mon' with I; Auto.
Apply a_seq_I.
Apply xa_in_interval.
Unfold xa.
Apply str_leEq_seq_so_leEq_Lim.
Exists N; Intros; Simpl.
Apply local_mon'_imp_mon'; Auto; Exact a_seq_mon.
Step [--](Zero::IR); RStepr [--](z[-](F xa Hx)).
Apply inv_resp_leEq.
Red; Apply approach_zero.
Intros.
Apply leEq_less_trans with e[/]TwoNZ.
2: Apply pos_div_two'; Auto.
Elim (contin_prop ???? contF ? (pos_div_two ?? H)); Intros d H0 H1.
Elim (Cauchy_complete (Build_CauchySeq ?? b_seq_Cauchy) ? H0); Fold xb; Simpl; Intros N HN.
Apply leEq_transitive with (F (b_seq N) (incF ? (b_seq_I N)))[-](F xa Hx).
Apply minus_resp_leEq; Apply z_leEq_b_seq.
EApply leEq_wdl.
2: Apply AbsIR_eq_x.
Apply H1; Auto.
Apply b_seq_I.
Apply xa_in_interval.
Apply leEq_wdl with (AbsIR (b_seq N)[-]xb).
2: Apply AbsIR_wd; Apply cg_minus_wd; [Algebra | Apply eq_symmetric_unfolded; Apply a_seq_b_seq_lim].
Apply AbsSmall_imp_AbsIR.
Auto.
Apply shift_leEq_minus; Step (F xa Hx).
Apply part_mon_imp_mon' with I; Auto.
Apply xa_in_interval.
Apply b_seq_I.
Apply leEq_wdl with xb.
2: Apply eq_symmetric_unfolded; Apply a_seq_b_seq_lim.
Unfold xb.
Apply str_seq_leEq_so_Lim_leEq.
Exists N; Intros; Simpl.
Step [--][--](b_seq i); Stepr [--][--](b_seq N).
Apply inv_resp_leEq.
Apply local_mon'_imp_mon' with f:=[n:nat][--](b_seq n); Auto.
Intro; Apply inv_resp_leEq; Apply b_seq_mon.
Qed.

End IVT.
