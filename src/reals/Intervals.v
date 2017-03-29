(* $Id: Intervals.v,v 1.21 2003/03/13 12:06:25 lcf Exp $ *)

Require Export RealLists.

Section Intervals.
(* Tex_Prose
\chapter{Intervals}
In this section we define (compact) intervals of the real line and some useful functions to work with them.

\section{Definitions}

We start by defining the compact interval $[a,b]$ as being the set of points less or equal than $b$ and greater or equal than $a$.  We require $a$ to be less or equal to $b$, as we want to work only in nonempty intervals.
*)

(* Begin_Tex_Verb *)
Definition compact [a,b:IR][Hab:a[<=]b] :=
  [x:IR]{a[<=]x}*{x[<=]b}.
(* End_Tex_Verb *)

(* Tex_Prose
\begin{convention} Let \verb!a,b:IR! and \verb!Hab:a[<=]b!.
\end{convention}

As expected, both $a$ and $b$ are members of $[a,b]$.  Also they are members of the interval $[\min(a,b),\max(a,b)]$.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.

(* Begin_Tex_Verb *)
Lemma compact_inc_lft : (compact a b Hab a).
(* End_Tex_Verb *)
Intros; Split; [Apply leEq_reflexive | Auto].
Qed.

(* Begin_Tex_Verb *)
Lemma compact_inc_rht : (compact a b Hab b).
(* End_Tex_Verb *)
Intros; Split; [Auto | Apply leEq_reflexive].
Qed.

(* Begin_Tex_Verb *)
Lemma compact_Min_lft :
  (Hab':?)(compact (Min a b) (Max a b) Hab' a).
(* End_Tex_Verb *)
Split; [Apply Min_leEq_lft | Apply lft_leEq_Max].
Qed.

(* Begin_Tex_Verb *)
Lemma compact_Min_rht :
  (Hab':?)(compact (Min a b) (Max a b) Hab' b).
(* End_Tex_Verb *)
Split; [Apply Min_leEq_rht | Apply rht_leEq_Max].
Qed.

(* Tex_Prose
As we will be interested in taking functions with domain in a compact interval, we want this predicate to be well defined.
*)

(* Begin_Tex_Verb *)
Lemma compact_wd : (pred_well_def IR (compact a b Hab)).
(* End_Tex_Verb *)
Intros; Red; Intros.
Inversion_clear H; Split.
Apply leEq_wdr with x; Assumption.
Apply leEq_wdl with x; Assumption.
Qed.

(* Tex_Prose
Also, it will sometimes be necessary to rewrite the endpoints of an interval.
*)

(* Begin_Tex_Verb *)
Lemma compact_wd' : (a',b':IR)(Hab':?)(x:IR)(a[=]a')->(b[=]b')->
  (compact a b Hab x)->(compact a' b' Hab' x).
(* End_Tex_Verb *)
Intros.
Inversion_clear H1; Split.
Apply leEq_wdl with a; Auto.
Apply leEq_wdr with b; Auto.
Qed.

(* Tex_Prose
As we identify subsets with predicates, inclusion is simply implication.
*)

(* Begin_Tex_Verb *)
Definition included [P,Q:IR->CProp] : CProp := (x:IR)(P x)->(Q x).
(* End_Tex_Verb *)

(* Tex_Prose
Finally, we define a restriction operator that takes a function $F$ and a well defined predicate $P$ included in the domain of $F$ and returns the restriction $F|_P$.
*)

(* Begin_Tex_Verb *)
Definition Frestr [F:PartIR][P:IR->CProp][HP:(pred_well_def IR P)]
  [H:(included P (Pred F))] : PartIR.
(* End_Tex_Verb *)
Intros.
Apply Build_PartFunct with P [x:IR][Hx:(P x)](Part F x (H x Hx)).
Assumption.
Intros; Exact (pfstrx ?????? H0).
Defined.

End Intervals.

(* Tex_Prose
\begin{notation}
\item the first two arguments of \verb!compact! are left implicit by writing {\tt\hypertarget{Syntactic_36}{Compact}};
\item {\tt\hypertarget{Syntactic_38}{FRestr}} stands for \verb!(Frestr ?? (compact_wd ???))!.
\end{notation}
*)

Syntactic Definition Compact := (compact ??).
Implicits Frestr [1 2].
Syntactic Definition FRestr := (Frestr (compact_wd ???)).

Section More_Intervals.

(* Tex_Prose
\section{Inclusion}

We now turn our attention to the properties of the inclusion relation.  We show it to be reflexive and transitive, and to work as expected with conjunction and extension.  The second property is a generalization of the reflexivity when the same compact interval is characterized in two different ways.
*)

(* Begin_Tex_Verb *)
Lemma included_refl : (P:IR->CProp)(included P P).
(* End_Tex_Verb *)
Intro.
Red; Intros.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_refl' : (a,b,Hab,Hab':?)
  (included (compact a b Hab) (compact a b Hab')).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Inversion_clear H; Split; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_trans : (P,Q,R:?)
  (included P Q)->(included Q R)->(included P R).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Apply H0; Apply H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_conj : (P,Q,R:IR->CProp)
  (included P Q)->(included P R)->(included P (Conj Q R)).
(* End_Tex_Verb *)
Intros.
Red; Red in H H0.
Intros; Red.
Split.
Apply H; Assumption.
Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_conj' : (P,Q:IR->CProp)
  (included (Conj P Q) P).
(* End_Tex_Verb *)
Intros.
Exact (prj1 ? P Q).
Qed.

(* Begin_Tex_Verb *)
Lemma included_conj'' : (P,Q:IR->CProp)
  (included (Conj P Q) Q).
(* End_Tex_Verb *)
Intros.
Exact (prj2 ? P Q).
Qed.

(* Begin_Tex_Verb *)
Lemma included_conj_lft : (P,Q,R:IR->CProp)
  (included R (Conj P Q))->(included R P).
(* End_Tex_Verb *)
Intros.
Red; Red in H.
Unfold conjP in H.
Intros.
Elim (H x).
Intros; Trivial.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_conj_rht : (P,Q,R:IR->CProp)
  (included R (Conj P Q))->(included R Q).
(* End_Tex_Verb *)
Intros.
Red; Red in H.
Unfold conjP in H.
Intros.
Elim (H x).
Intros; Trivial.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_extend : (P,R:IR->CProp;Q:(x:IR)(P x)->CProp)
  (included R (extend P Q))->(included R P).
(* End_Tex_Verb *)
Intros.
Red; Red in H.
Unfold extend in H.
Intros.
Elim (H x).
2: Assumption.
Intros.
Tauto.
Qed.

(* Tex_Prose
We also prove some inclusions of compact intervals.
*)

(* Begin_Tex_Verb *)
Lemma compact_map1 : (a,b:IR)(Hab,Hab':?)
  (included
    (compact (Min a b) (Max a b) Hab')
    (compact a b Hab)).
(* End_Tex_Verb *)
Intros.
Red; Intros x H.
Red; Red in H.
Inversion_clear H.
Split.
EApply leEq_wdl; [Apply H0 | Apply leEq_imp_Min_is_lft; Auto].
EApply leEq_wdr; [Apply H1 | Apply leEq_imp_Max_is_rht; Auto].
Defined.

(* Begin_Tex_Verb *)
Lemma compact_map2 : (a,b:IR)(Hab,Hab':?)
  (included
    (compact a b Hab)
    (compact (Min a b) (Max a b) Hab')).
(* End_Tex_Verb *)
Intros.
Red; Intros x H.
Red; Red in H.
Inversion_clear H.
Split.
EApply leEq_transitive; [Apply Min_leEq_lft | Apply H0].
EApply leEq_transitive; [Apply H1 | Apply rht_leEq_Max].
Defined.

(* Begin_Tex_Verb *)
Lemma compact_map3 : (a,b,e:IR)(Hab,Hab':?)(Zero[<]e)->
  (included (compact a b[-]e Hab') (compact a b Hab)).
(* End_Tex_Verb *)
Intros; Red.
Intros; Inversion_clear H0; Split.
Auto.
EApply leEq_transitive.
Apply H2.
Apply shift_minus_leEq.
Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Assumption.
Qed.

End More_Intervals.

Section Totally_Bounded.

(* Tex_Prose
\section{Totally Bounded}

Sets that are totally bounded will play an important role in what is to come.  The definition (equivalent to the classical one) states that $P$ is totally bounded iff \[\forall_{\varepsilon>0}\exists_{x_1,\ldots,x_n}\forall_{y\in P}\exists_{1\leq i\leq n}|y-x_i|<\varepsilon\]

Notice the use of lists for quantification.
*)

(* Begin_Tex_Verb *)
Definition totally_bounded [P:IR->CProp] : CProp :=
  {x:IR & (P x)}*
  (e:IR)(Zero[<]e)->
    {l:(list IR) & 
      ((x:IR)(member x l)->(P x)) & (x:IR)(P x)->
        {y:IR & (member y l) | (AbsSmall e x[-]y)}}.
(* End_Tex_Verb *)

(* Tex_Prose
This definition is classically, but not constructively, equivalent to the definition of compact; the next result, classically equivalent to the Heine-Borel theorem, justifies that we take the definition of totally bounded to be the relevant one and that we defined compacts as we did.
*)

(* Begin_Tex_Verb *)
Lemma compact_is_totally_bounded :
   (a,b,Hab:?)(totally_bounded (compact a b Hab)).
(* End_Tex_Verb *)
Intros; Split.
Exists a.
Apply compact_inc_lft.
Cut (n:nat)(a,b,e:IR)(Hab:a[<=]b)(He:Zero[<]e)
  ((b[-]a)[/]e[//](pos_ap_zero ?? He)[<=](nring n))->
    ((le (2) n)->(((nring n)[-]Two)[<=](b[-]a)[/]e[//](pos_ap_zero ?? He)))->
    {l:(list IR) & ((x:IR)(member x l)->(compact a b Hab x)) & (x:IR)(compact a b Hab x)->{y:IR & (member y l) | (AbsIR x[-]y)[<=]e}}.
Intros H e He.
Elim (str_Archimedes (b[-]a)[/]?[//](pos_ap_zero ?? (pos_div_two ?? He))).
Intros n Hn.
Inversion_clear Hn.
Elim (H n a b ? Hab (pos_div_two ?? He)).
Intros l Hl' Hl.
2: Assumption.
2: Assumption.
Exists l.
Assumption.
Intros x Hx; Elim (Hl x Hx).
Intros y Hy Hy'.
Exists y.
Assumption.
Apply AbsIR_imp_AbsSmall.
Apply leEq_transitive with e[/]TwoNZ.
Assumption.
Apply less_leEq; Apply pos_div_two'; Assumption.
Apply shift_leEq_div; [Apply pos_div_two; Assumption | Apply shift_leEq_minus].
RStep a; Assumption.
Clear Hab a b; Intro n; Induction n.
Intros.
Exists (cons a (nil ?)).
Intros.
Inversion H1.
Elim H2.
Apply compact_wd with a; Algebra.
Apply compact_inc_lft.
Intros.
Exists a.
Right; Algebra.
Apply leEq_wdl with (Zero::IR).
Apply less_leEq; Auto.
Step (AbsIR Zero).
Apply AbsIR_wd.
Apply leEq_imp_eq.
Apply shift_leEq_minus; Step a; Elim H1; Auto.
Apply shift_minus_leEq.
Apply leEq_transitive with b.
Elim H1; Auto.
Apply shift_leEq_plus.
Apply mult_cancel_leEq with One[/]?[//](pos_ap_zero ?? He).
Apply recip_resp_pos; Auto.
Stepr (Zero::IR).
RStep (b[-]a)[/]?[//](pos_ap_zero ?? He); Auto.
Clear Hrecn; Induction n.
Intros.
Exists (cons a (nil IR)).
Intros.
Inversion_clear H1.
Elim H2.
Apply compact_wd with a; [Apply compact_inc_lft | Algebra].
Intros x Hx; Inversion_clear Hx.
Exists a.
Simpl; Right; Algebra.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
Apply leEq_transitive with b[-]a.
Apply minus_resp_leEq; Assumption.
RStepr e[*](nring (1)); EApply shift_leEq_mult'; [Assumption | Apply H].
Apply shift_leEq_minus; Step a.
Assumption.
Clear Hrecn; Induction n.
Intros.
LetTac enz:=(pos_ap_zero ?? He).
Exists (cons (a[+]b)[/]TwoNZ (nil IR)).
Intros.
Inversion_clear H1.
Inversion_clear H2.
Apply compact_wd with (a[+]b)[/]TwoNZ; [Split | Algebra].
Step a[+]Zero; Apply shift_plus_leEq'.
Apply mult_cancel_leEq with (Two::IR).
Apply pos_two.
Step (Zero::IR).
RStepr b[-]a.
Apply shift_leEq_minus; Step a; Auto.
Stepr b[+]Zero; Apply shift_leEq_plus'.
Apply mult_cancel_leEq with (Two::IR).
Apply pos_two.
Stepr (Zero::IR).
RStep a[-]b.
Apply shift_minus_leEq; Stepr b; Auto.
Intros.
Exists (a[+]b)[/]TwoNZ.
Right; Algebra.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply Abs_Max.
Apply shift_minus_leEq; Apply Max_leEq; Apply shift_leEq_plus'; Apply leEq_Min.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.
Apply shift_minus_leEq.
Apply leEq_transitive with b.
Elim H1; Auto.
Apply shift_leEq_plus'.
Apply mult_cancel_leEq with (Two::IR).
Apply pos_two.
Apply shift_leEq_mult' with enz.
Auto.
RStep (b[-]a)[/]e[//]enz; Auto.
Apply leEq_transitive with a.
2: Elim H1; Auto.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Apply mult_cancel_leEq with (Two::IR).
Apply pos_two.
Apply shift_leEq_mult' with enz.
Auto.
RStep (b[-]a)[/]e[//]enz; Auto.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply less_leEq; Auto.

Intros.
LetTac b':=b[-]e.
Cut a[<=]b'; Intros.
Elim (Hrecn a b' e H1 He).
Intros l Hl' Hl.
Exists (cons b' l).
Intros.
Unfold b' in H1; Apply compact_map3 with e:=e Hab':=H1 b:=b.
Assumption.
Simpl in H2; Inversion_clear H2.
Apply Hl'; Assumption.
Apply compact_wd with b'; [Apply compact_inc_rht | Algebra].
Intros.
Cut (x[<]b')+((b'[-]e)[<]x); Intros.
Inversion_clear H3.
Cut (compact a b' H1 x); Intros.
Elim (Hl x H3).
Intros y Hy Hy'.
Exists y.
Left; Assumption.
Auto.
Inversion_clear H2; Split.
Assumption.
Apply less_leEq; Auto.
Exists b'.
Right; Algebra.
Simpl; Unfold ABSIR.
Apply Max_leEq.
Apply shift_minus_leEq; Unfold b'.
RStepr b.
Elim H2; Auto.
RStep b'[-]x; Apply shift_minus_leEq; Apply shift_leEq_plus'; Apply less_leEq; Assumption.
Cut ((b'[-]e)[<]x)+(x[<]b'); [Tauto | Apply cotrans_less_unfolded].
Apply shift_minus_less; Apply shift_less_plus'; Step (Zero::IR); Assumption.

Unfold b'.
RStep (b[-]a)[/]e[//](pos_ap_zero ?? He)[-]One.
Apply shift_minus_leEq.
Stepr (!nring IR (S (S (S n)))); Auto.

Intro.
Unfold b'.
RStepr (b[-]a)[/]e[//](pos_ap_zero ?? He)[-]One.
Apply shift_leEq_minus.
RStep ((!nring IR (S (S n)))[+]One)[-]Two.
Auto with arith.

Unfold b'.
Apply shift_leEq_minus; Apply shift_plus_leEq'.
Step One[*]e; Apply shift_mult_leEq with (pos_ap_zero ?? He).
Auto.
Apply leEq_transitive with (!nring IR (S (S (S n))))[-]Two.
Apply shift_leEq_minus; RStep (Three::IR); Apply nring_leEq; Auto with arith.
Auto with arith.
Qed.

(* Tex_Prose
Suprema and infima will be needed throughout; we define them here both for arbitrary subsets of \RR\ and for images of functions.
*)

(* Begin_Tex_Verb *)
Definition set_glb_IR [P:IR->CProp][a:IR] : CProp :=
  {(x:IR)(P x)->(a[<=]x)}*
  ((e:IR)((Zero[<]e)->{x:IR & (P x) & ((x[-]a)[<]e)})).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition set_lub_IR [P:IR->CProp][a:IR] : CProp :=
  {(x:IR)(P x)->(x[<=]a)}*
  ((e:IR)((Zero[<]e)->{x:IR & (P x) & ((a[-]x)[<]e)})).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition fun_glb_IR [F:PartIR][a:IR] : CProp :=
  {(x:IR)(Hx:(Pred F x))(a[<=](Part F x Hx))}*
  ((e:IR)((Zero[<]e)->{x:IR &
    {Hx:(Pred F x) & (Part F x Hx)[-]a[<]e}})).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition fun_lub_IR [F:PartIR][a:IR] : CProp :=
  {(x:IR)(Hx:(Pred F x))(Part F x Hx)[<=]a}*
  ((e:IR)((Zero[<]e)->{x:IR &
    {Hx:(Pred F x) & (a[-](Part F x Hx))[<]e}})).
(* End_Tex_Verb *)

Local aux_seq_lub [P:IR->CProp][H:(totally_bounded P)] : 
  (k:nat)(Build_SubCSetoid IR [x:IR](P x)*{(y:IR)(P y)->(y[-]x)[<=]Two[*](one_div_succ k)}).
Intros P H; Elim H; Clear H; Intros non_empty H k.
Elim (H (one_div_succ k) (one_div_succ_pos IR k)).
Intros l Hl' Hl; Clear H.
Cut {y:IR & (member y l) | (((maxlist l)[-](one_div_succ k))[<=]y)}.
Intro; Inversion_clear H.
2: Apply maxlist_leEq_eps.
2: Inversion_clear non_empty.
2: Elim (Hl x).
2: Intros.
2: Exists x0.
2: Tauto.
2: Assumption.
2: Apply one_div_succ_pos.
Exists x; Split.
Apply Hl'; Assumption.
Intros y Hy.
Elim (Hl y Hy).
Intros z Hz Hz'.
RStep (y[-]z)[+](z[-]x).
RStepr (!one_div_succ IR k)[+](one_div_succ k).
Apply plus_resp_leEq_both.
Apply leEq_transitive with (AbsIR y[-]z).
Apply leEq_AbsIR.
Apply AbsSmall_imp_AbsIR; Assumption.
Apply shift_minus_leEq.
Apply leEq_transitive with (maxlist l).
Apply maxlist_greater; Assumption.
Apply shift_leEq_plus'.
Assumption.
Qed.

Local aux_seq_lub_prop : (P:IR->CProp)(H:(totally_bounded P))((k:nat)(P (scs_elem ?? (aux_seq_lub P H k))))*{(k:nat)(y:IR)(P y)->(y[-](scs_elem ?? (aux_seq_lub P H k)))[<=]Two[*](one_div_succ k)}.
Intros; Cut (k:nat)(P (scs_elem ?? (aux_seq_lub P H k)))*{(y:IR)(P y)->(y[-](scs_elem ?? (aux_seq_lub P H k)))[<=]Two[*](one_div_succ k)}.
Intro.
Split; Intro; Elim (H0 k); Intros.
Assumption.
Apply b; Assumption.
Intro; Apply scs_prf.
Qed.

(* Tex_Prose
The following are probably the most important results in this section.
*)

(* Begin_Tex_Verb *)
Lemma totally_bounded_has_lub :
  (P:IR->CProp)(totally_bounded P)->{z:IR & set_lub_IR P z}.
(* End_Tex_Verb *)
Intros P tot_bnd.
Red in tot_bnd.
Elim tot_bnd; Intros non_empty H.
Cut {sequence : (nat->IR) & ((k:nat)(P (sequence k))) | (k:nat)(x:IR)(P x)->(x[-](sequence k))[<=]Two[*](one_div_succ k)}.
Intros.
Elim H0.
Intros seq Hseq Hseq'.
Cut (Cauchy_prop seq).
Intro.
LetTac seq1 := (Build_CauchySeq IR seq H1).
Exists (Lim seq1).
Split; Intros.
Apply shift_leEq_rht.
Step [--](Zero::IR); RStepr [--](x[-](Lim seq1)).
Apply inv_resp_leEq.
LetTac seq2 := (Cauchy_const x).
Apply leEq_wdl with (Lim seq2)[-](Lim seq1).
2: Apply cg_minus_wd; [Unfold seq2; Apply eq_symmetric_unfolded; Apply Lim_const | Algebra].
Apply leEq_wdl with (Lim (Build_CauchySeq IR [n:nat](seq2 n)[-](seq1 n) (Cauchy_minus seq2 seq1))).
Apply leEq_transitive with (Lim twice_inv_seq).
Apply Lim_leEq_Lim; Intro; Simpl.
Apply Hseq'; Assumption.
Apply eq_imp_leEq.
Apply eq_symmetric_unfolded; Apply Limits_unique.
Red; Fold (SeqLimit twice_inv_seq Zero).
Apply twice_inv_seq_Lim.
Apply Lim_minus.
Cut (Cauchy_Lim_prop2 seq (Lim seq1)).
Intro H4; Red in H4.
Elim (H4 e[/]TwoNZ (pos_div_two ?? H2)); Clear H4.
Intros n Hn.
Exists (seq n).
Apply Hseq.
Apply leEq_less_trans with (AbsIR (Lim seq1)[-](seq n)).
Apply leEq_AbsIR.
Apply leEq_less_trans with e[/]TwoNZ.
Apply AbsSmall_imp_AbsIR.
Apply AbsSmall_minus; Simpl; Apply Hn.
Apply le_n.
Apply pos_div_two'; Auto.
Cut (Cauchy_Lim_prop2 seq1 (Lim seq1)); Intros.
Red; Red in H3.
Intros eps Heps; Elim (H3 eps Heps); Clear H3; Intros.
Exists x.
Intros m Hm; Elim (p m Hm); Clear p.
Intros.
Stepr (seq1 m)[-](Lim seq1).
Apply AbsIR_eq_AbsSmall; Assumption.
Red; Fold (SeqLimit seq1 (Lim seq1)).
Apply ax_Lim.
Apply crl_proof.
Red; Intros.
Elim (Archimedes One[/]e[//](pos_ap_zero ?? H1)).
Intros n Hn.
Exists (S (mult (2) n)); Intros.
Cut Zero[<](!nring IR n); Intros.
Apply AbsIR_eq_AbsSmall.
Apply leEq_transitive with [--](One[/](nring n)[//](pos_ap_zero ?? H3)).
Apply inv_resp_leEq.
Apply shift_div_leEq.
Assumption.
EApply shift_leEq_mult'; [Assumption | Apply Hn].
RStepr [--]((seq (S (mult (2) n)))[-](seq m)); Apply inv_resp_leEq.
Apply leEq_transitive with Two[*](!one_div_succ IR m).
Auto.
Apply leEq_transitive with (!one_div_succ IR n).
Unfold one_div_succ.
Unfold Snring.
RStep One[/]((nring (S m))[/]TwoNZ)[//](div_resp_ap_zero_rev ???? (nring_ap_zero IR (S m) (sym_not_eq nat (0) (S m) (O_S m)))).
Apply recip_resp_leEq.
Apply pos_nring_S.
Apply shift_leEq_div.
Apply pos_two.
Simpl; Fold (Two::IR).
RStep (Two[*](!nring IR n))[+]One[+]One.
Apply plus_resp_leEq.
Apply leEq_wdl with (!nring IR (S (mult (2) n))).
Apply nring_leEq; Assumption.
Step_final (!nring IR (mult (2) n))[+]One.
Unfold one_div_succ; Unfold Snring; Apply recip_resp_leEq.
Assumption.
Simpl; Apply less_leEq; Apply less_plusOne.
Apply leEq_transitive with Two[*](!one_div_succ IR (S (mult (2) n))).
Auto.
Apply less_leEq.
Apply less_leEq_trans with One[/](nring n)[//](pos_ap_zero ?? H3).
Step (!one_div_succ IR (S (mult (2) n)))[*]Two.
Unfold one_div_succ; Unfold Snring.
Apply shift_mult_less with (two_ap_zero IR).
Apply pos_two.
RStepr One[/](Two[*](nring n))[//](mult_resp_ap_zero ??? (two_ap_zero IR) (pos_ap_zero ?? H3)).
Apply recip_resp_less.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive; [Apply pos_two | Assumption].
Apply less_wdr with (Two[*](!nring IR n))[+]One[+]One.
Apply less_transitive_unfolded with (Two[*](!nring IR n))[+]One; Apply less_plusOne.
Step_rht (!nring IR (S (mult (2) n)))[+]One.
Step_final (!nring IR (mult (2) n))[+]One[+]One.
RStepr One[/](One[/]e[//](pos_ap_zero ?? H1))[//](div_resp_ap_zero_rev ???? (one_ap_zero IR)).
Apply recip_resp_leEq; [Apply recip_resp_pos; Assumption | Assumption].
EApply less_leEq_trans.
2: Apply Hn.
Apply recip_resp_pos; Assumption.
Elim (aux_seq_lub_prop P tot_bnd).
Exists [k:nat](scs_elem ?? (aux_seq_lub P tot_bnd k)); Auto.
Qed.

Local aux_seq_glb [P:IR->CProp][H:(totally_bounded P)] : (k:nat)(Build_SubCSetoid IR [x:IR](P x)*{(y:IR)(P y)->(x[-]y)[<=]Two[*](one_div_succ k)}).
Intros P H; Elim H; Clear H; Intros non_empty H k.
Elim (H (one_div_succ k) (one_div_succ_pos IR k)).
Intros l Hl' Hl; Clear H.
Cut {y:IR & (member y l) | y[<=]((minlist l)[+](one_div_succ k))}.
Intro; Inversion_clear H.
2: Apply minlist_leEq_eps.
2: Inversion_clear non_empty.
2: Elim (Hl x).
2: Intros.
2: Exists x0.
2: Tauto.
2: Assumption.
2: Apply one_div_succ_pos.
Exists x; Split.
Apply Hl'; Assumption.
Intros y Hy.
Elim (Hl y Hy).
Intros z Hz Hz'.
RStep (x[-]z)[+](z[-]y).
RStepr (!one_div_succ IR k)[+](one_div_succ k).
Apply plus_resp_leEq_both.
Apply shift_minus_leEq.
Apply shift_leEq_plus'.
Apply leEq_transitive with (minlist l).
Apply shift_minus_leEq.
Assumption.
Apply minlist_smaller; Assumption.
Apply leEq_transitive with (AbsIR y[-]z).
RStep [--](y[-]z); Apply inv_leEq_AbsIR.
Apply AbsSmall_imp_AbsIR; Assumption.
Qed.

Local aux_seq_glb_prop : (P:IR->CProp)(H:(totally_bounded P))((k:nat)(P (scs_elem ?? (aux_seq_glb P H k))))*{(k:nat)(y:IR)(P y)->((scs_elem ?? (aux_seq_glb P H k))[-]y)[<=]Two[*](one_div_succ k)}.
Intros; Cut (k:nat)(P (scs_elem ?? (aux_seq_glb P H k)))*{(y:IR)(P y)->((scs_elem ?? (aux_seq_glb P H k))[-]y)[<=]Two[*](one_div_succ k)}.
Intro.
Split; Intro; Elim (H0 k); Intros.
Assumption.
Apply b; Assumption.
Intro; Apply scs_prf.
Qed.

(* Begin_Tex_Verb *)
Lemma totally_bounded_has_glb :
  (P:IR->CProp)(totally_bounded P)->{z:IR & set_glb_IR P z}.
(* End_Tex_Verb *)
Intros P tot_bnd.
Red in tot_bnd.
Elim tot_bnd; Intros non_empty H.
Cut {sequence : (nat->IR) & ((k:nat)(P (sequence k))) | (k:nat)(x:IR)(P x)->((sequence k)[-]x)[<=]Two[*](one_div_succ k)}.
Intros.
Elim H0.
Clear H0; Intros seq H0 H1.
Cut (Cauchy_prop seq).
Intro.
LetTac seq1 := (Build_CauchySeq IR seq H2).
Exists (Lim seq1).
Split; Intros.
Apply shift_leEq_rht.
Step [--](Zero::IR); RStepr [--]((Lim seq1)[-]x).
Apply inv_resp_leEq.
LetTac seq2 := (Cauchy_const x).
Apply leEq_wdl with (Lim seq1)[-](Lim seq2).
2: Apply cg_minus_wd; [Algebra | Unfold seq2; Apply eq_symmetric_unfolded; Apply Lim_const].
Apply leEq_wdl with (Lim (Build_CauchySeq IR [n:nat](seq1 n)[-](seq2 n) (Cauchy_minus seq1 seq2))).
Apply leEq_transitive with (Lim twice_inv_seq).
Apply Lim_leEq_Lim; Intro.
Simpl.
Apply H1; Assumption.
Apply eq_imp_leEq.
Apply eq_symmetric_unfolded; Apply Limits_unique.
Red; Fold (SeqLimit twice_inv_seq Zero).
Apply twice_inv_seq_Lim.
Apply Lim_minus.
Cut (Cauchy_Lim_prop2 seq (Lim seq1)).
Intro; Red in H4.
Elim (H4 e[/]TwoNZ (pos_div_two ?? H3)); Clear H4.
Intros n Hn.
Exists (seq n).
Apply H0.
Apply leEq_less_trans with (AbsIR (Lim seq1)[-](seq n)).
RStep [--]((Lim seq1)[-](seq n)).
Apply inv_leEq_AbsIR.
Apply leEq_less_trans with e[/]TwoNZ.
Apply AbsSmall_imp_AbsIR.
Apply AbsSmall_minus; Simpl; Apply Hn.
Apply le_n.
Apply pos_div_two'; Auto.
Cut (Cauchy_Lim_prop2 seq1 (Lim seq1)); Intros.
Red; Red in H4.
Intros eps Heps; Elim (H4 eps Heps); Clear H4; Intros.
Exists x.
Intros m Hm; Elim (p m Hm); Clear p.
Intros.
Stepr (seq1 m)[-](Lim seq1).
Apply AbsIR_eq_AbsSmall; Assumption.
Red; Fold (SeqLimit seq1 (Lim seq1)).
Apply ax_Lim.
Apply crl_proof.
Red; Intros.
Elim (Archimedes One[/]e[//](pos_ap_zero ?? H2)).
Intros n Hn.
Exists (S (mult (2) n)); Intros.
Cut Zero[<](!nring IR n); Intros.
Apply AbsIR_eq_AbsSmall.
Apply leEq_transitive with [--](One[/](nring n)[//](pos_ap_zero ?? H4)).
Apply inv_resp_leEq.
Apply shift_div_leEq.
Assumption.
EApply shift_leEq_mult'; [Assumption | Apply Hn].
Apply less_leEq.
RStepr [--]((seq (S (mult (2) n)))[-](seq m)); Apply inv_resp_less.
Apply leEq_less_trans with Two[*](!one_div_succ IR (S (mult (2) n))).
Apply H1; Apply H0.
Step (!one_div_succ IR (S (mult (2) n)))[*]Two.
Unfold one_div_succ; Unfold Snring.
Apply shift_mult_less with (two_ap_zero IR).
Apply pos_two.
RStepr One[/](Two[*](nring n))[//](mult_resp_ap_zero ??? (two_ap_zero IR) (pos_ap_zero ?? H4)).
Apply recip_resp_less.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive; [Apply pos_two | Assumption].
Apply less_wdr with (Two[*](!nring IR n))[+]One[+]One.
Apply less_transitive_unfolded with (Two[*](!nring IR n))[+]One; Apply less_plusOne.
Step_rht (!nring IR (S (mult (2) n)))[+]One.
Step_final (!nring IR (mult (2) n))[+]One[+]One.
Apply leEq_transitive with Two[*](!one_div_succ IR m).
Apply H1; Apply H0.
Apply leEq_transitive with (!one_div_succ IR n).
Unfold one_div_succ.
Unfold Snring.
RStep One[/]((!nring IR (S m))[/]TwoNZ)[//](div_resp_ap_zero_rev ???? (nring_ap_zero IR (S m) (sym_not_eq nat (0) (S m) (O_S m)))).
Apply recip_resp_leEq.
Apply pos_nring_S.
Apply shift_leEq_div.
Apply pos_two.
Simpl; Fold (Two::IR).
RStep (Two[*](!nring IR n))[+]One[+]One.
Apply plus_resp_leEq.
Apply leEq_wdl with (!nring IR (S (mult (2) n))).
Apply nring_leEq; Assumption.
Step_final (!nring IR (mult (2) n))[+]One.
Unfold one_div_succ; Unfold Snring.
RStepr One[/](One[/]e[//](pos_ap_zero ?? H2))[//](div_resp_ap_zero_rev ???? (one_ap_zero IR)).
Apply recip_resp_leEq.
Apply recip_resp_pos; Assumption.
Apply leEq_transitive with (!nring IR n); [Assumption | Simpl; Apply less_leEq; Apply less_plusOne].
EApply less_leEq_trans.
2: Apply Hn.
Apply recip_resp_pos; Assumption.
Elim (aux_seq_glb_prop P tot_bnd).
Exists [k:nat](scs_elem ?? (aux_seq_glb P tot_bnd k)); Auto.
Qed.

End Totally_Bounded.

Section Compact.

(* Tex_Prose
\section{Compact}

In this section we dwell a bit farther into the definition of compact and explore some of its properties.

The following characterization of inclusion can be very useful:
*)

(* Begin_Tex_Verb *)
Lemma included_compact : (a,b,c,d:IR)(Hab,Hcd:?)
  (compact a b Hab c)->(compact a b Hab d)->
  (included (compact c d Hcd) (compact a b Hab)).
(* End_Tex_Verb *)
Repeat Intro.
Inversion_clear H.
Inversion_clear H0.
Inversion_clear H1.
Split.
Apply leEq_transitive with c; Auto.
Apply leEq_transitive with d; Auto.
Qed.

(* Tex_Prose
At several points in our future development of a theory we will need to partition a compact interval in subintervals of length smaller than some predefined value $\varepsilon$\footnote{Although this seems a consequence of every compact interval being totally bounded, it is in fact a stronger property.}.  In this section we perform that construction (requiring the endpoints of the interval to be distinct) and prove some of its good properties.

\begin{convention} Let \verb!a,b:IR!, \verb!Hab:a[<=]b! and denote by \verb!I! the compact interval $[a,b]$.  Also assume that $a<b$, and let \verb!e! be a positive real number.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(compact a b Hab).

Hypothesis Hab':a[<]b.

Variable e:IR.
Hypothesis He:(Zero[<]e).

(* Tex_Prose
We start by finding a natural number $n$ such that \[\frac{b-a}n<\varepsilon\]
*)

(* Begin_Tex_Verb *)
Definition compact_nat :=
  (proj1_sig ?? (Archimedes (b[-]a)[/]?[//](pos_ap_zero ?? He))).
(* End_Tex_Verb *)

(* Tex_Prose
Obviously such an $n$ must be greater than zero.
*)

(* Begin_Tex_Verb *)
Lemma pos_compact_nat : (Zero[<](!nring IR compact_nat)).
(* End_Tex_Verb *)
Apply less_leEq_trans with ((b[-]a)[/]e[//](pos_ap_zero ?? He)).
RStepr (b[-]a)[*](One[/]e[//](pos_ap_zero ?? He)).
Apply mult_resp_pos.
Apply shift_less_minus; Step a; Assumption.
Apply recip_resp_pos; Assumption.
Unfold compact_nat; Apply proj2_sig.
Qed.

(* Tex_Prose
We now define a sequence on $n$ points in $[a,b]$ by \[x_i=\min(a,b)+i\times\frac{b-a}n\] and prove that all of its points are really in that interval.
*)

(* Begin_Tex_Verb *)
Definition compact_part [i:nat] : (le i compact_nat)->IR.
(* End_Tex_Verb *)
Intros.
Apply a[+](nring i)[*]((b[-]a)[/]?[//](pos_ap_zero ?? pos_compact_nat)).
Defined.

(* Begin_Tex_Verb *)
Lemma compact_part_hyp : (i:nat)(Hi:(le i compact_nat))
  (compact a b Hab (compact_part i Hi)).
(* End_Tex_Verb *)
Intros; Unfold compact_part.
Split.
Step a[+]Zero; Apply plus_resp_leEq_lft.
Step (Zero::IR)[*]Zero; Apply mult_resp_leEq_both; Try Apply leEq_reflexive.
Apply nring_nonneg.
Apply shift_leEq_div.
Apply pos_compact_nat.
Apply shift_leEq_minus; RStep a; Apply less_leEq; Assumption.
RStepr a[+](nring compact_nat)[*]((b[-]a)[/]?[//](pos_ap_zero ?? pos_compact_nat)).
Apply plus_resp_leEq_lft.
Apply mult_resp_leEq_rht; Try Apply nring_nonneg.
Apply nring_leEq; Assumption.
Apply shift_leEq_div.
Apply pos_compact_nat.
Apply shift_leEq_minus; RStep a; Apply less_leEq; Assumption.
Qed.

(* Tex_Prose
This sequence is strictly increasing and each two consecutive points are apart by less than $\varepsilon$.
*)

(* Begin_Tex_Verb *)
Lemma compact_less : (i:nat)
  (H1:(le i compact_nat))(H2:(le (S i) compact_nat))
  (Zero[<](compact_part ? H2)[-](compact_part ? H1)).
(* End_Tex_Verb *)
Intros.
Apply shift_less_minus; Step (compact_part ? H1).
Unfold compact_part.
Apply plus_resp_less_lft.
Apply mult_resp_less.
Simpl; Apply less_plusOne.
Apply div_resp_pos.
Apply pos_compact_nat.
Apply shift_less_minus; Step a; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma compact_leEq : (i:nat)
  (H1:(le i compact_nat))(H2:(le (S i) compact_nat))
  (compact_part ? H2)[-](compact_part ? H1)[<=]e.
(* End_Tex_Verb *)
Intros.
Unfold compact_part; Simpl.
RStep (b[-]a)[/]?[//](pos_ap_zero ?? pos_compact_nat).
Apply shift_div_leEq.
Apply pos_compact_nat.
Apply shift_leEq_mult' with (pos_ap_zero ?? He).
Assumption.
Exact (proj2_sig ?? (Archimedes ?)).
Qed.

(* Tex_Prose
When we proceed to integration, this lemma will also be useful:
*)

(* Begin_Tex_Verb *)
Lemma compact_partition_lemma : (n:nat)(Hn:~(O=n))
  (i:nat)(H:(le i n))(Compact Hab
    a[+](nring i)[*]((b[-]a)[/]?[//](nring_ap_zero' ? n Hn))).
(* End_Tex_Verb *)
Intros; Split.
Apply shift_leEq_plus'.
Step (Zero::IR).
Apply mult_resp_nonneg.
Apply nring_nonneg.
Apply shift_leEq_div.
Apply nring_pos; Apply neq_O_lt; Auto.
Apply shift_leEq_minus.
RStep a; Assumption.
Apply shift_plus_leEq'.
RStepr (nring n)[*]((b[-]a)[/]?[//](nring_ap_zero' ?? Hn)).
Step Zero[+](nring i)[*]((b[-]a)[/]?[//](nring_ap_zero' ?? Hn)).
Apply shift_plus_leEq.
RStepr ((nring n)[-](nring i))[*]((b[-]a)[/]?[//](nring_ap_zero' ?? Hn)).
Apply mult_resp_nonneg.
Apply shift_leEq_minus.
Step (!nring IR i).
Apply nring_leEq; Assumption.
Apply shift_leEq_div.
Apply nring_pos; Apply neq_O_lt; Auto.
Apply shift_leEq_minus.
RStep a; Assumption.
Qed.

(* Tex_Prose
The next lemma provides an upper bound for the distance between two points in an interval:
*)

(* Begin_Tex_Verb *)
Lemma compact_elements :
  (x,y:IR)(Compact Hab x)->(Compact Hab y)->
  (AbsIR x[-]y)[<=](AbsIR b[-]a).
(* End_Tex_Verb *)
Clear Hab' He e.
Do 2 Intro; Intros Hx Hy.
Apply leEq_wdr with b[-]a.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step a; Auto.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply Abs_Max.
Inversion_clear Hx.
Inversion_clear Hy.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply Max_leEq; Auto.
Apply inv_resp_leEq.
Apply leEq_Min; Auto.
Qed.

Opaque Min Max.

(* Tex_Prose
The following is a variation on the previous lemma:
*)

(* Begin_Tex_Verb *)
Lemma compact_elements' : (c,d,Hcd:?)(x,y:IR)
  (Compact Hab x)->(compact c d Hcd y)->
  (AbsIR x[-]y)[<=](AbsIR (Max b d)[-](Min a c)).
(* End_Tex_Verb *)
Do 5 Intro; Intros Hx Hy.
EApply leEq_transitive.
2: Apply leEq_AbsIR.
Inversion_clear Hx.
Inversion_clear Hy.
Simpl; Unfold ABSIR; Apply Max_leEq.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply leEq_transitive with b; Auto; Apply lft_leEq_Max.
Apply inv_resp_leEq; Apply leEq_transitive with c; Auto; Apply Min_leEq_rht.
RStep y[-]x.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply leEq_transitive with d; Auto; Apply rht_leEq_Max.
Apply inv_resp_leEq; Apply leEq_transitive with a; Auto; Apply Min_leEq_lft.
Qed.

(* Tex_Prose
The following lemma is a bit more specific: it shows that we can also estimate the distance from the \emph{center} of a compact interval to any of its points.
*)

(* Begin_Tex_Verb *)
Lemma compact_bnd_AbsIR : (x,y,d,H:?)
  (compact x[-]d x[+]d H y)->
  (AbsIR x[-]y)[<=]d.
(* End_Tex_Verb *)
Intros.
Inversion_clear H0.
Simpl; Unfold ABSIR.
Apply Max_leEq.
Apply shift_minus_leEq; Apply shift_leEq_plus'; Auto.
RStep y[-]x.
Apply shift_minus_leEq.
Stepr x[+]d; Auto.
Qed.

(* Tex_Prose
Finally, two more useful lemmas to prove inclusion of compact intervals.  They will be necessary for the definition and proof of the elementary properties of the integral.
*)

(* Begin_Tex_Verb *)
Lemma included2_compact : (x,y:IR)(Hxy:?)
  (Compact Hab x)->(Compact Hab y)->
  (included (compact (Min x y) (Max x y) Hxy) (Compact Hab)).
(* End_Tex_Verb *)
Intros.
Inversion_clear H.
Inversion_clear H0.
Apply included_compact; Split.
Apply leEq_Min; Auto.
Apply leEq_transitive with y.
Apply Min_leEq_rht.
Auto.
Apply leEq_transitive with y.
Auto.
Apply rht_leEq_Max.
Apply Max_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included3_compact : (x,y,z:IR)(Hxyz:?)
  (Compact Hab x)->(Compact Hab y)->(Compact Hab z)->
  (included
    (compact (Min (Min x y) z) (Max (Max x y) z) Hxyz)
    (Compact Hab)).
(* End_Tex_Verb *)
Intros.
Inversion_clear H.
Inversion_clear H0.
Inversion_clear H1.
Apply included_compact; Split.
Repeat Apply leEq_Min; Auto.
Apply leEq_transitive with z.
Apply Min_leEq_rht.
Auto.
Apply leEq_transitive with z.
Auto.
Apply rht_leEq_Max.
Repeat Apply Max_leEq; Auto.
Qed.

End Compact.
