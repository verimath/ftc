Require Export WeakIVT.
Require Export CalculusTheorems.

Section IVT'.

(* Tex_Prose
\chapter{The Generalized IVT}

The IVT can be generalized to arbitrary partial functions; in the first
part, we will simply do that, repeating the previous construction.

The same notations and conventions apply as before.
*)

Variables a,b:IR.
Hypothesis Hab' : a[<]b.
Hypothesis Hab : a[<=]b.

Local I := (Compact Hab).
Local I' := (iprop (olor a b)).

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
Hypothesis Haz:(F a (incF ? Ha))[<]z.
Hypothesis Hzb:z[<](F b (incF ? Hb)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma IVT'_seq_lemma : (xy:IR*IR)[x:=(Fst xy)][y:=(Snd xy)]
  (Hxy:(I x)*(I y))[Hx:=(Fst Hxy)][Hy:=(Snd Hxy)](x[<]y)->
  ((F x (incF ? Hx))[<]z)*(z[<](F y (incF ? Hy)))->
  {xy0:IR*IR & [x0:=(Fst xy0)][y0:=(Snd xy0)]{Hxy0:(I x0)*(I y0) &
  [Hx0:=(Fst Hxy0)][Hy0:=(Snd Hxy0)]
    (x0[<]y0)*((F x0 (incF ? Hx0))[<]z)*(z[<](F y0 (incF ? Hy0))) | 
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
Auto.
Elim H0; Auto.
Unfold x1; Apply smaller_rht.
Unfold x1; Apply less_leEq; Apply a_lft; Auto.
Apply leEq_reflexive.
Exists (x,y1); Exists (Hx,H3); Simpl; Repeat Split; Auto.
Apply less_transitive_unfolded with x1; Unfold x1 y1; [Apply a_lft | Apply lft_rht]; Auto.
Elim H0; Auto.
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

(* Begin_Tex_Verb *)
Record IVT'_aux_seq_type : Set :=
  {IVT'seq1 : IR;
   IVT'seq2 : IR;
   IVT'H1   : (I IVT'seq1);
   IVT'H2   : (I IVT'seq2);
   IVT'prf  : IVT'seq1[<]IVT'seq2;
   IVT'z1   : (F IVT'seq1 (incF ? IVT'H1))[<]z;
   IVT'z2   : z[<](F IVT'seq2 (incF ? IVT'H2))}.

Definition IVT'_iter : IVT'_aux_seq_type->IVT'_aux_seq_type.
(* End_Tex_Verb *)
Intro Haux; Elim Haux; Intros.
Elim (IVT'_seq_lemma (IVT'seq3,IVT'seq4) (IVT'H3,IVT'H4) IVT'prf0 (IVT'z3,IVT'z4)).
Intro x; Elim x; Simpl; Clear x; Intros.
Elim p.
Intro x; Elim x; Simpl; Clear x; Intros.
Inversion_clear p0.
Inversion_clear H.
Inversion_clear q.
Inversion_clear H3.
Apply Build_IVT'_aux_seq_type with a0 b0 a1 b1; Auto.
Defined.

(* Begin_Tex_Verb *)
Definition IVT'_seq : nat->IVT'_aux_seq_type.
(* End_Tex_Verb *)
Intro n; Induction n.
Apply Build_IVT'_aux_seq_type with a b Ha Hb; Auto.
Apply (IVT'_iter Hrecn).
Defined.

(* Begin_Tex_Verb *)
Definition a'_seq := [n:nat](IVT'seq1 (IVT'_seq n)).
Definition b'_seq := [n:nat](IVT'seq2 (IVT'_seq n)).

Definition a'_seq_I [n:nat] : (I (a'_seq n)) := (IVT'H1 (IVT'_seq n)).
Definition b'_seq_I [n:nat] : (I (b'_seq n)) := (IVT'H2 (IVT'_seq n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma a'_seq_less_b'_seq : (n:nat)(a'_seq n)[<](b'_seq n).
(* End_Tex_Verb *)
Exact [n:nat](IVT'prf (IVT'_seq n)).
Qed.

(* Begin_Tex_Verb *)
Lemma a'_seq_less_z : (n:nat)(F ? (incF ? (a'_seq_I n)))[<]z.
(* End_Tex_Verb *)
Exact [n:nat](IVT'z1 (IVT'_seq n)).
Qed.

(* Begin_Tex_Verb *)
Lemma z_less_b'_seq : (n:nat)z[<](F ? (incF ? (b'_seq_I n))).
(* End_Tex_Verb *)
Exact [n:nat](IVT'z2 (IVT'_seq n)).
Qed.

(* Begin_Tex_Verb *)
Lemma a'_seq_mon : (i:nat)(a'_seq i)[<=](a'_seq (S i)).
(* End_Tex_Verb *)
Intro.
Unfold a'_seq.
Simpl.
Elim (IVT'_seq i); Simpl; Intros.
Elim IVT'_seq_lemma; Simpl; Intro.
Elim x; Simpl; Clear x; Intros.
Elim p; Clear p; Intro.
Elim x; Simpl; Clear x; Intros.
Case q; Clear q; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Elim p; Clear p; Simpl; Intros.
Elim a2; Clear a2; Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma b'_seq_mon : (i:nat)(b'_seq (S i))[<=](b'_seq i).
(* End_Tex_Verb *)
Intro.
Unfold b'_seq.
Simpl.
Elim (IVT'_seq i); Simpl; Intros.
Elim IVT'_seq_lemma; Simpl; Intro.
Elim x; Simpl; Clear x; Intros.
Elim p; Clear p; Intro.
Elim x; Simpl; Clear x; Intros.
Case q; Clear q; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Elim p; Clear p; Simpl; Intros.
Elim a2; Clear a2; Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma a'_seq_b'_seq_dist_n : (n:nat)((b'_seq (S n))[-](a'_seq (S n)))[=](Two[/]ThreeNZ)[*]((b'_seq n)[-](a'_seq n)).
(* End_Tex_Verb *)
Intro.
Unfold a'_seq b'_seq.
Simpl.
Elim (IVT'_seq n); Simpl; Intros.
Elim IVT'_seq_lemma; Simpl; Intro.
Elim x; Simpl; Clear x; Intros.
Elim p; Clear p; Intro.
Elim x; Simpl; Clear x; Intros.
Case q; Clear q; Simpl; Intros.
Case a2; Clear a2; Simpl; Intros.
Elim p; Clear p; Simpl; Intros.
Elim a2; Clear a2; Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma a'_seq_b'_seq_dist : (n:nat)((b'_seq n)[-](a'_seq n))[=](Two[/]ThreeNZ)[^]n[*](b[-]a).
(* End_Tex_Verb *)
Induction n.
Simpl; Algebra.
Clear n; Intros.
Stepr (Two[/]ThreeNZ)[*](Two[/]ThreeNZ)[^]n[*](b[-]a).
Stepr (Two[/]ThreeNZ)[*]((Two[/]ThreeNZ)[^]n[*](b[-]a)).
Stepr (Two[/]ThreeNZ)[*]((b'_seq n)[-](a'_seq n)).
Apply a'_seq_b'_seq_dist_n.
Qed.

(* Begin_Tex_Verb *)
Lemma a'_seq_Cauchy : (Cauchy_prop a'_seq).
(* End_Tex_Verb *)
Red; Intros.
Elim (intervals_small' a b e H); Intros i Hi.
Exists i; Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_transitive.
2: Apply Hi.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step (a'_seq i).
2: Apply local_mon'_imp_mon'; Auto; Exact a'_seq_mon.
EApply leEq_wdr.
2: Apply a'_seq_b'_seq_dist.
Apply minus_resp_leEq.
Apply less_leEq; Apply a_b'.
Exact a'_seq_mon.
Exact b'_seq_mon.
Exact a'_seq_less_b'_seq.
Qed.

(* Begin_Tex_Verb *)
Lemma b'_seq_Cauchy : (Cauchy_prop b'_seq).
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
2: Apply shift_leEq_minus; Step (b'_seq m).
2: Step [--][--](b'_seq m); Stepr [--][--](b'_seq i).
2: Apply inv_resp_leEq; Apply local_mon'_imp_mon' with f:=[n:nat][--](b'_seq n); Auto.
2: Intro; Apply inv_resp_leEq; Apply b'_seq_mon.
EApply leEq_wdr.
2: Apply a'_seq_b'_seq_dist.
Unfold cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq.
Apply less_leEq; Apply a_b'.
Exact a'_seq_mon.
Exact b'_seq_mon.
Exact a'_seq_less_b'_seq.
Qed.

Local xa:=(Lim (Build_CauchySeq ?? a'_seq_Cauchy)).
Local xb:=(Lim (Build_CauchySeq ?? b'_seq_Cauchy)).

(* Begin_Tex_Verb *)
Lemma a'_seq_b'_seq_lim : xa[=]xb.
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
2: Apply shift_leEq_minus; Step (a'_seq m)[-](b'_seq m).
2: Apply shift_minus_leEq; Stepr (b'_seq m).
2: Apply less_leEq; Apply a'_seq_less_b'_seq.
EApply leEq_wdr.
2: Apply a'_seq_b'_seq_dist.
RStep (b'_seq m)[-](a'_seq m).
Unfold cg_minus; Apply plus_resp_leEq_both.
Step [--][--](b'_seq m); Stepr [--][--](b'_seq i).
Apply inv_resp_leEq; Apply local_mon'_imp_mon' with f:=[n:nat][--](b'_seq n); Auto.
Intro; Apply inv_resp_leEq; Apply b'_seq_mon.
Apply inv_resp_leEq; Apply local_mon'_imp_mon'; Auto; Exact a'_seq_mon.
Qed.

(* Begin_Tex_Verb *)
Lemma xa'_in_interval : (I xa).
(* End_Tex_Verb *)
Split.
Unfold xa.
Apply leEq_seq_so_leEq_Lim.
Simpl.
Intro; Elim (a'_seq_I i); Auto.
Unfold xa.
Apply seq_leEq_so_Lim_leEq.
Simpl.
Intro; Elim (a'_seq_I i); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma IVT'_I : {x:IR & (I' x) | (Hx:?)(F x Hx)[=]z}.
(* End_Tex_Verb *)
Elim (IVT_I a b Hab' Hab F contF) with z; Try Apply less_leEq; Auto.
Intros x H H0.
Exists x; Auto.
Elim H; Intros; Split; Apply leEq_not_eq; Auto.
Apply pfstrx with F (incF ? Ha) (incF ? H).
Apply less_imp_ap; Stepr z; Auto.
Apply pfstrx with F (incF ? H) (incF ? Hb).
Apply less_imp_ap; Step z; Auto.
Qed.

End IVT'.

(* Tex_Prose
\section{Other formulations}

We now generalize the various statements of the intermediate value theorem to more widely applicable forms.
*)

(* Begin_Tex_Verb *)
Lemma Weak_IVT : (I,F:?)(Continuous I F)->
  (a,b,Ha,Hb:?)(HFab:(F a Ha)[<](F b Hb))
  (iprop I a)->(iprop I b)->
  (e:IR)(Zero[<]e)->(y:IR)(Compact (less_leEq ??? HFab) y)->
  {x:IR & (Compact (Min_leEq_Max a b) x) | (Hx:?)(AbsIR (F x Hx)[-]y)[<=]e}.
(* End_Tex_Verb *)
Intros.
LetTac H5:=(less_imp_ap ??? HFab).
LetTac H6:=(pfstrx ?????? H5).
Elim (ap_imp_less ??? H6); Clear H6 H5; Intro.
Cut (Continuous_I (Min_leEq_Max a b) F); Intros.
2: Apply included_imp_Continuous with I; Auto; Apply included_interval; Auto.
LetTac incF:=(contin_imp_inc ???? H4).
Cut (Min a b)[=]a.
Cut (Max a b)[=]b; Intros.
2: Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
2: Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
LetTac Ha':=(incF ? (compact_inc_lft ?? (Min_leEq_Max a b))).
LetTac Hb':=(incF ? (compact_inc_rht ?? (Min_leEq_Max a b))).
Cut (F ? Ha')[<](F ? Hb'); Intros.
Apply Weak_IVT_ap_lft with HFab:=H7; Auto.
Apply compact_wd' with Hab:=(less_leEq ??? HFab); Algebra.
Step (F a Ha); Stepr (F b Hb); Auto.
Cut (Continuous_I (Min_leEq_Max b a) F); Intros.
2: Apply included_imp_Continuous with I; Auto; Apply included_interval; Auto.
LetTac incF:=(contin_imp_inc ???? H4).
Cut (Min a b)[=]b.
Cut (Max a b)[=]a; Intros.
2: EApply eq_transitive_unfolded; [Apply Max_comm | Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto].
2: EApply eq_transitive_unfolded; [Apply Min_comm | Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto].
LetTac Ha':=(incF ? (compact_inc_lft ?? (Min_leEq_Max b a))).
LetTac Hb':=(incF ? (compact_inc_rht ?? (Min_leEq_Max b a))).
Cut (F ? Hb')[<](F ? Ha'); Intros.
Elim (Weak_IVT_ap_rht ???? H4 ?? H7 ? H2 y); Auto.
Intro x; Intros.
Exists x; Auto.
Apply compact_wd' with Hab:=(Min_leEq_Max b a); [Apply Min_comm | Apply Max_comm | Auto].
Apply compact_wd' with Hab:=(less_leEq ??? HFab); Algebra.
Apply pfwdef; Step (Max a b); Apply Max_comm.
Apply pfwdef; Step (Min a b); Apply Min_comm.
Apply less_wdl with (F a Ha).
Apply less_wdr with (F b Hb).
Auto.
Apply pfwdef; Step (Min a b); Apply Min_comm.
Apply pfwdef; Step (Max a b); Apply Max_comm.
Qed.

(* Begin_Tex_Verb *)
Lemma IVT_inc : (I,F:?)(Continuous I F)->
  (a,b,Ha,Hb:?)((F a Ha)[#](F b Hb))->
  (iprop I a)->(iprop I b)->
  ((x,y:IR)(iprop I x)->(iprop I y)->
    (x[<]y)->(Hx,Hy:?)(F x Hx)[<](F y Hy))->
  (y:IR)(Compact (Min_leEq_Max (F a Ha) (F b Hb)) y)->
  {x:IR & (Compact (Min_leEq_Max a b) x) | (Hx:?)(F x Hx)[=]y}.
(* End_Tex_Verb *)
Intros.
LetTac H5:=(pfstrx ?????? H0).
Elim (ap_imp_less ??? H5); Clear H5; Intro.
Cut (Continuous_I (Min_leEq_Max a b) F); Intros.
2: Apply included_imp_Continuous with I; Auto; Apply included_interval; Auto.
Cut (Min a b)[=]a; [Intro | Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto].
Cut (Max a b)[=]b; [Intro | Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto].
Cut (H,H':?)(F (Min a b) H)[<](F (Max a b) H'); Intros.
2: Apply H3; Auto.
2: Apply iprop_wd with a; Algebra.
2: Apply iprop_wd with b; Algebra.
2: Step a; Stepr b; Auto.
Elim H4; Intros.
Apply IVT_I with H5.
Apply ap_imp_Min_less_Max; Apply less_imp_ap; Auto.
Intros.
Apply H3; Auto.
Apply (included_interval ??? H1 H2 (Min_leEq_Max a b)); Auto.
Apply (included_interval ??? H1 H2 (Min_leEq_Max a b)); Auto.
EApply leEq_wdl.
Apply a1.
Stepr (F a Ha); Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
EApply leEq_wdr.
Apply b0.
Stepr (F b Hb); Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Cut (Continuous_I (Min_leEq_Max b a) F); Intros.
2: Apply included_imp_Continuous with I; Auto; Apply included_interval; Auto.
Cut (Min b a)[=]b; [Intro | Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto].
Cut (Max b a)[=]a; [Intro | Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto].
Cut (H,H':?)(F (Min b a) H)[<](F (Max b a) H'); Intros.
2: Apply H3; Auto.
2: Apply iprop_wd with b; Algebra.
2: Apply iprop_wd with a; Algebra.
2: Step b; Stepr a; Auto.
Elim H4; Intros.
Elim IVT_I with contF:=H5 z:=y; Intros; Auto.
Exists x; Auto.
Apply compact_wd' with Hab:=(Min_leEq_Max b a); Auto.
Apply Min_comm.
Apply Max_comm.
Step b; Stepr a; Auto.
Apply H3; Auto.
Apply (included_interval ??? H2 H1 (Min_leEq_Max b a)); Auto.
Apply (included_interval ??? H2 H1 (Min_leEq_Max b a)); Auto.
EApply leEq_wdl.
Apply a0.
Stepr (F b Hb); EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
EApply leEq_wdr.
Apply b1.
Stepr (F a Ha); EApply eq_transitive_unfolded.
Apply Max_comm.
Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Qed.

Transparent Min.

(* Begin_Tex_Verb *)
Lemma IVT_dec : (I,F:?)(Continuous I F)->
  (a,b,Ha,Hb:?)((F a Ha)[#](F b Hb))->
  (iprop I a)->(iprop I b)->
  ((x,y:IR)(iprop I x)->(iprop I y)->
    (x[<]y)->(Hx,Hy:?)(F y Hy)[<](F x Hx))->
  (y:IR)(Compact (Min_leEq_Max (F a Ha) (F b Hb)) y)->
  {x:IR & (Compact (Min_leEq_Max a b) x) | (Hx:?)(F x Hx)[=]y}.
(* End_Tex_Verb *)
Intros.
Elim IVT_inc with I:=I F:={--}F a:=a b:=b y:=[--]y Ha:=Ha Hb:=Hb; Auto.
Intros x H5 H6.
Exists x; Auto.
Intro.
Step [--][--](F x Hx); Stepr [--][--]y.
Apply un_op_wd_unfolded; Simpl in H6; Apply H6.
Contin.
Simpl; Apply un_op_strext_unfolded with (!cg_inv IR).
Step (F a Ha); Stepr (F b Hb); Auto.
Intros; Simpl; Apply inv_resp_less; Auto.
Inversion_clear H4; Split; Simpl.
Apply inv_resp_leEq.
EApply leEq_wdr.
Apply H6.
Apply max_wd_unfolded; Algebra.
Stepr [--][--](Max [--](F a Ha) [--](F b Hb)).
Apply inv_resp_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma IVT'_inc : (I,F:?)(Continuous I F)->
  (a,b,Ha,Hb:?)((F a Ha)[#](F b Hb))->
  (iprop I a)->(iprop I b)->
  ((x,y:IR)(iprop I x)->(iprop I y)->
    (x[<]y)->(Hx,Hy:?)(F x Hx)[<](F y Hy))->
  (y:IR)(iprop (olor (Min (F a Ha) (F b Hb)) (Max (F a Ha) (F b Hb))) y)->
  {x:IR & (iprop (olor (Min a b) (Max a b)) x) | (Hx:?)(F x Hx)[=]y}.
(* End_Tex_Verb *)
Intros.
LetTac H5:=(pfstrx ?????? H0).
Elim (ap_imp_less ??? H5); Clear H5; Intro.
Cut (Continuous_I (Min_leEq_Max a b) F); Intros.
2: Apply included_imp_Continuous with I; Auto; Apply included_interval; Auto.
Cut (Min a b)[=]a; [Intro | Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto].
Cut (Max a b)[=]b; [Intro | Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto].
Cut (H,H':?)(F (Min a b) H)[<](F (Max a b) H'); Intros.
2: Apply H3; Auto.
2: Apply iprop_wd with a; Algebra.
2: Apply iprop_wd with b; Algebra.
2: Step a; Stepr b; Auto.
Elim H4; Intros.
Apply IVT'_I with (Min_leEq_Max a b) H5.
Apply ap_imp_Min_less_Max; Apply less_imp_ap; Auto.
Intros.
Apply H3; Auto.
Apply (included_interval ??? H1 H2 (Min_leEq_Max a b)); Auto.
Apply (included_interval ??? H1 H2 (Min_leEq_Max a b)); Auto.
EApply less_wdl.
Apply a1.
Stepr (F a Ha); Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
EApply less_wdr.
Apply b0.
Stepr (F b Hb); Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Cut (Continuous_I (Min_leEq_Max b a) F); Intros.
2: Apply included_imp_Continuous with I; Auto; Apply included_interval; Auto.
Cut (Min b a)[=]b; [Intro | Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto].
Cut (Max b a)[=]a; [Intro | Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto].
Cut (H,H':?)(F (Min b a) H)[<](F (Max b a) H'); Intros.
2: Apply H3; Auto.
2: Apply iprop_wd with b; Algebra.
2: Apply iprop_wd with a; Algebra.
2: Step b; Stepr a; Auto.
Elim H4; Intros.
Elim IVT'_I with contF:=H5 z:=y; Auto.
Intros x H9 H10; Exists x; Auto.
Inversion_clear H9; Split.
EApply less_wdl; [Apply H11 | Apply Min_comm].
EApply less_wdr; [Apply H12 | Apply Max_comm].
Apply ap_imp_Min_less_Max; Apply less_imp_ap; Auto.
Intros; Apply H3; Auto.
Apply (included_interval ??? H2 H1 (Min_leEq_Max b a)); Auto.
Apply (included_interval ??? H2 H1 (Min_leEq_Max b a)); Auto.
EApply less_wdl.
Apply a0.
Stepr (F b Hb); EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
EApply less_wdr.
Apply b1.
Stepr (F a Ha); EApply eq_transitive_unfolded.
Apply Max_comm.
Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Qed.

Transparent Min.

(* Begin_Tex_Verb *)
Lemma IVT'_dec : (I,F:?)(Continuous I F)->
  (a,b,Ha,Hb:?)((F a Ha)[#](F b Hb))->
  (iprop I a)->(iprop I b)->
  ((x,y:IR)(iprop I x)->(iprop I y)->
    (x[<]y)->(Hx,Hy:?)(F y Hy)[<](F x Hx))->
  (y:IR)(iprop (olor (Min (F a Ha) (F b Hb)) (Max (F a Ha) (F b Hb))) y)->
  {x:IR & (iprop (olor (Min a b) (Max a b)) x) | (Hx:?)(F x Hx)[=]y}.
(* End_Tex_Verb *)
Intros.
Elim IVT'_inc with I:=I F:={--}F a:=a b:=b y:=[--]y Ha:=Ha Hb:=Hb; Auto.
Intros x H5 H6.
Exists x; Auto.
Intro.
Step [--][--](F x Hx); Stepr [--][--]y.
Apply un_op_wd_unfolded; Simpl in H6; Apply H6.
Contin.
Simpl; Apply un_op_strext_unfolded with (!cg_inv IR).
Step (F a Ha); Stepr (F b Hb); Auto.
Intros; Simpl; Apply inv_resp_less; Auto.
Inversion_clear H4; Split; Simpl.
Apply inv_resp_less.
EApply less_wdr.
Apply H6.
Apply max_wd_unfolded; Algebra.
Stepr [--][--](Max [--](F a Ha) [--](F b Hb)).
Apply inv_resp_less; Auto.
Qed.
