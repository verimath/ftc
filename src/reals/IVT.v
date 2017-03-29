(* $Id: IVT.v,v 1.17 2003/03/11 13:36:16 lcf Exp $ *)

Require Export CPoly_Contin.
Require Export CPoly_ApZero.

(* Tex_Prose
\chapter{Intermediate Value Theorem}
*)

Section Nested_Intervals.
(* Tex_Prose
\section{Nested intervals}

\begin{convention} Let \verb!a,b:nat->IR! be sequences such that:
\begin{itemize}
\item \verb!a! is increasing;
\item \verb!b! is decreasing;
\item \verb!(i:nat)((a i) [<] (b i))!;
\item for every positive real number \verb!eps!, there is an $i$ such that \verb!(b i) [<] (a i)[+]eps!.
\end{itemize}
\end{convention}
*)

Variables a,b : nat->IR.
Hypothesis a_mon : (i:nat)((a i) [<=] (a (S i))).
Hypothesis b_mon : (i:nat)((b (S i)) [<=] (b i)).
Hypothesis a_b : (i:nat)((a i) [<] (b i)).
Hypothesis b_a : (eps:IR)(Zero [<] eps) -> {i:nat | (b i) [<=] (a i)[+]eps}.

(* Begin_Tex_Verb *)
Lemma a_mon' : (i,j:nat)(le i j) -> ((a i) [<=] (a j)).
(* End_Tex_Verb *)
Intros.
Apply local_mon'_imp_mon'; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma b_mon' : (i,j:nat)(le i j) -> ((b j) [<=] (b i)).
(* End_Tex_Verb *)
Intros.
LetTac b':=[i:nat][--](b i).
Step [--][--](b j).
Stepr [--][--](b i).
Fold (b' i) (b' j).
Apply inv_resp_leEq.
Apply local_mon'_imp_mon'.
Unfold b'; Intro; Apply inv_resp_leEq; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma a_b' : (i,j:nat)((a i) [<] (b j)).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_dec i j); Intro.
Apply leEq_less_trans with (a j).
Apply a_mon'. Auto.
Auto.
Apply less_leEq_trans with (b i).
Auto.
Apply b_mon'. Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma intervals_cauchy : (Cauchy_prop a).
(* End_Tex_Verb *)
Unfold Cauchy_prop.
Unfold AbsSmall.
Intro eps. Intros.
Elim (b_a eps H). Intro n. Intros. Exists n.
Intro i. Intros.
Split; Apply less_leEq.
Apply less_leEq_trans with (Zero::IR).
Stepr [--](Zero::IR).
Apply inv_resp_less. Auto.
Step (a n)[-](a n).
Apply minus_resp_leEq.
Apply a_mon'. Auto.
Apply shift_minus_less'.
Apply less_leEq_trans with (b n).
Apply a_b'.
Auto.
Qed.

(* Begin_Tex_Verb *)
Local a' := (Build_CauchySeq ? a intervals_cauchy).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Cnested_intervals_limit :
  {z:IR | ((i:nat)((a i) [<=] z)) | ((i:nat)(z [<=] (b i)))}.
(* End_Tex_Verb *)
Exists (Lim a').
Intros.
Unfold leEq. Unfold Not. Intros.
Elim (Lim_less_so_seq_less a' (a i)). Intro n. Intros H0.
Elim (le_lt_dec n i); Intro H1.
Cut (Not ((a i) [<] (a i))). Intro H2.
Unfold Not in H1. Elim H2. Apply H0. Auto.
Apply less_irreflexive_unfolded.
Cut (i,j:nat)(le i j) -> ((a i) [<=] (a j)). Intro a_mon''.
Unfold leEq in a_mon''. Unfold Not in a_mon''.
Elim a_mon'' with i n. Auto with arith.
Apply H0.
Auto.
Intros. Apply a_mon'; Auto.
Auto.
Unfold leEq. Unfold Not. Intros.
Elim (less_Lim_so_less_seq a' (b i) H). Intro n. Intros H0.
Elim (le_lt_dec n i); Intro H1.
Cut (Not ((a i) [<] (b i))). Unfold Not. Intro.
Elim H2. Auto. Apply less_antisymmetric_unfolded.
Apply H0.
Auto.
Cut (Not ((a n) [<] (b n))). Unfold Not. Intro H2.
Apply H2. Auto. Apply less_antisymmetric_unfolded.
Apply leEq_less_trans with (b i).
Apply b_mon'. Auto with arith.
Apply H0. Auto.
Qed.

(* Tex_Prose
\begin{convention} Let \verb!f! be a continuous real function.
\end{convention}
*)

Variable f : (CSetoid_un_op IR).
Hypothesis f_contin : (contin f).

(* Begin_Tex_Verb *)
Lemma f_contin_pos :
  (z:IR)(Zero [<] (f z)) ->
    {eps:IR & (Zero [<] eps) &
      ((x:IR)(x [<=] z[+]eps) -> (z [<=] x[+]eps) -> (Zero [<] (f x)))}.
(* End_Tex_Verb *)
Intros.
Unfold contin in f_contin.
Unfold continAt in f_contin.
Unfold funLim in f_contin.
Unfold AbsSmall in f_contin.
Elim (f_contin z (f z)[/]TwoNZ (pos_div_two ?? H)). Intro eps. Intros H1 H2.
Exists eps.
Auto. Intros.
Elim (H2 x). Intros H5 H6.
Step (f z)[-](f z).
Apply shift_minus_less.
Apply shift_less_plus'. 
Apply leEq_less_trans with (f z)[/]TwoNZ. Auto. Apply pos_div_two'. Auto.
Split.
Apply shift_leEq_minus.
RStep x[-]eps.
Apply shift_minus_leEq. Auto.
Apply shift_minus_leEq. Stepr x[+]eps. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma f_contin_neg :
  (z:IR)((f z) [<] Zero) ->
    {eps:IR & (Zero [<] eps) &
      ((x:IR)(x [<=] z[+]eps) -> (z [<=] x[+]eps) -> ((f x) [<] Zero))}.
(* End_Tex_Verb *)
Intros.
Unfold contin in f_contin.
Unfold continAt in f_contin.
Unfold funLim in f_contin.
Unfold AbsSmall in f_contin.
Cut Zero [<] [--](f z). Intro.
Elim (f_contin z ([--](f z))[/]TwoNZ (pos_div_two ?? H0)). Intro eps. Intros H2 H3.
Exists eps.
Auto. Intros.
Elim (H3 x). Intros H6 H7.
RStepr (f z)[-][--][--](f z).
Apply shift_less_minus'.
Apply shift_plus_less. 
Apply less_leEq_trans with (f z)[/]TwoNZ. 
Step (f z). Apply inv_cancel_less. RStep ([--](f z))[/]TwoNZ. Apply pos_div_two'. Auto.
RStep [--]([--](f z))[/]TwoNZ. Auto.
Split.
Apply shift_leEq_minus.
RStep x[-]eps.
Apply shift_minus_leEq. Auto.
Apply shift_minus_leEq. Stepr x[+]eps. Auto.
Step [--](Zero::IR).
Apply inv_resp_less. Auto.
Qed.

(* Begin_Tex_Verb *)
Hypothesis f_a : (i:nat)((f (a i)) [<=] Zero).
Hypothesis f_b : (i:nat)(Zero [<=] (f (b i))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Cnested_intervals_zero :
  {z : IR | ((a (0)) [<=] z) /\ ((z [<=] (b (0))) /\ ((f z) [=] Zero))}.
(* End_Tex_Verb *)
Elim Cnested_intervals_limit. Intro z. Intros H0 H1. Exists z.
Split. Auto. Split. Auto.
Apply not_ap_imp_eq.
Unfold Not.
Intros H2.
Elim (ap_imp_less ? ? ? H2); Intros H3.
Elim (f_contin_neg z H3). Intro eps. Intros H5 H6.
Elim (b_a eps). Intro i. Intros H7.
Cut (b i) [<=] z[+]eps. Intro.
Cut z [<=] (b i)[+]eps. Intro.
Unfold leEq in f_b. Unfold Not in f_b.
Apply f_b with i. Apply H6. Auto. Auto.
Apply leEq_transitive with (b i). Auto.
Step (b i)[+]Zero. Apply plus_resp_leEq_lft. Apply less_leEq. Auto.
Apply leEq_transitive with (a i)[+]eps. Auto.
Apply plus_resp_leEq. Auto. Auto.
Elim (f_contin_pos z H3). Intro eps. Intros H5 H6.
Elim (b_a eps). Intro i. Intros H7.
Cut (a i) [<=] z[+]eps. Intro.
Cut z [<=] (a i)[+]eps. Intro.
Unfold leEq in f_a. Unfold Not in f_a.
Apply f_a with i. Apply H6. Auto. Auto.
Apply leEq_transitive with (b i). Auto.
Auto. Apply leEq_transitive with z. Auto.
Step z[+]Zero. Apply less_leEq. Apply plus_resp_less_lft. Auto.
Auto.
Qed.

End Nested_Intervals.

Section Bisection.
(* Tex_Prose
\section{Bisections}
*)

(* Begin_Tex_Verb *)
Variable f : (CSetoid_un_op IR).
Hypothesis f_apzero_interval : (a,b:IR)(a [<] b) ->
  {c:IR | (a [<=] c) /\ (c [<=] b) & ((f c) [#] Zero)}.
Variable a,b : IR.
Hypothesis a_b : a [<] b.
Hypothesis f_a : (f a) [<=] Zero.
Hypothesis f_b : Zero [<=] (f b).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Local Small : IR := Two[/]ThreeNZ.
Local lft := (Two[*]a[+]b)[/]ThreeNZ.
Local rht := (a[+]Two[*]b)[/]ThreeNZ.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma a_lft : a [<] lft.
(* End_Tex_Verb *)
Unfold lft.
Apply shift_less_div.
Apply pos_three.
RStep Two[*]a[+]a.
Apply plus_resp_less_lft.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma rht_b : rht [<] b.
(* End_Tex_Verb *)
Unfold rht.
Apply shift_div_less.
Apply pos_three.
RStepr b[+]Two[*]b.
Apply plus_resp_less_rht.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma lft_rht : lft [<] rht.
(* End_Tex_Verb *)
Unfold lft. Unfold rht.
Apply div_resp_less_rht.
RStep (a[+]b)[+]a.
RStepr (a[+]b)[+]b.
Apply plus_resp_less_lft.
Auto.
Apply pos_three.
Qed.

(* Begin_Tex_Verb *)
Lemma smaller_lft : rht[-]a [=] Small[*](b[-]a).
(* End_Tex_Verb *)
Unfold Small. Unfold rht.
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma smaller_rht : b[-]lft [=] Small[*](b[-]a).
(* End_Tex_Verb *)
Unfold Small. Unfold lft.
Rational.
Qed.

Hints Resolve smaller_lft smaller_rht : algebra.

(* Begin_Tex_Verb *)
Lemma Cbisect' :
  {a':IR & { b':IR &
      (a' [<] b') |
      (a [<=] a') /\ (b' [<=] b) /\
      (b'[-]a' [<=] Small[*](b[-]a)) /\
      ((f a') [<=] Zero) /\ 
      (Zero [<=] (f b'))}}.
(* End_Tex_Verb *)
Elim (f_apzero_interval lft rht lft_rht). Intro c. Intro H.
Elim H. Intros H0 H2 H3.
Cut ({(f c) [<=] Zero} + {Zero [<=] (f c)}).
Intro H4; Inversion_clear H4.
Exists c. Exists b.
Apply leEq_less_trans with rht. Auto. Apply rht_b.
Split. Apply leEq_transitive with lft. Apply less_leEq. Apply a_lft. Auto.
Split. Apply leEq_reflexive.
Split. Stepr b[-]lft. Apply minus_resp_leEq_rht. Auto.
Split. Auto. Auto.
Exists a. Exists c.
Apply less_leEq_trans with lft. Apply a_lft. Auto.
Split. Apply leEq_reflexive.
Split. Apply less_leEq. Apply leEq_less_trans with rht. Auto. Apply rht_b.
Split. 
Stepr rht[-]a. Apply minus_resp_leEq. Auto. 
Split. Auto. Auto.
Elim (ap_imp_less ? ? ? H3); Intros.
Left. Apply less_leEq. Auto.
Right. Apply less_leEq. Auto.
Qed.

End Bisection.

Section Bisect_Interval.

(* Tex_Prose
\section{Bisection gives an interval}
*)

(* Begin_Tex_Verb *)
Variable f : (CSetoid_un_op IR).
Hypothesis C_f_apzero_interval : (a,b:IR)(a [<] b) ->
  {c:IR | (a [<=] c) /\ (c [<=] b) & ((f c) [#] Zero)}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Local Small : IR := Two[/]ThreeNZ.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record bisect_interval : Set :=
  { interval_lft     : IR;
    interval_rht     : IR;
    interval_lft_rht : interval_lft [<] interval_rht;
    interval_f_lft   : (f interval_lft) [<=] Zero;
    interval_f_rht   : Zero [<=] (f interval_rht)
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Cbisect_exists : (I:bisect_interval)
  {I':bisect_interval |
    ((interval_rht I')[-](interval_lft I') [<=]
      Small[*]((interval_rht I)[-](interval_lft I))) /\
    (((interval_lft I) [<=] (interval_lft I')) /\
    ((interval_rht I') [<=] (interval_rht I)))}.
(* End_Tex_Verb *)
Intros.
Elim (Cbisect' f C_f_apzero_interval
  ? ? (interval_lft_rht I) (interval_f_lft I) (interval_f_rht I)).
Intro lft. Intro H.
Elim H. Intro rht. Intros H1 H2. Elim H2. Intros H3 H4. Elim H4. Intros H5 H6.
Elim H6. Intros H7 H8.
Elim H8. Intros H9 H10.
Exists (Build_bisect_interval lft rht H1 H9 H10).
Simpl.
Unfold Small.
Split. Auto. Split. Auto. Auto.
Qed.

(* Begin_Tex_Verb *)
Definition bisect : bisect_interval -> bisect_interval :=
  [I:bisect_interval]
    (proj1_sig ? ? (Cbisect_exists I)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma bisect_prop : (I:bisect_interval)
  (((interval_rht (bisect I))[-](interval_lft (bisect I)) [<=]
    Small[*]((interval_rht I)[-](interval_lft I)))) /\
  (((interval_lft I) [<=] (interval_lft (bisect I))) /\
  ((interval_rht (bisect I)) [<=] (interval_rht I))).
(* End_Tex_Verb *)
Intros.
Unfold bisect.
Apply proj2_sig. 
Qed.

End Bisect_Interval.

Section IVT_Op.
(* Tex_Prose
\section{IVT for operations}
*)

(* Begin_Tex_Verb *)
Variable f : (CSetoid_un_op IR).
Hypothesis f_contin : (contin f).
Hypothesis f_apzero_interval : (a,b:IR)(a [<] b) ->
  { c:IR | (a [<=] c) /\ (c [<=] b) & ((f c) [#] Zero)}.
Variable a,b : IR.
Hypothesis a_b : a [<] b.
Hypothesis f_a : (f a) [<=] Zero.
Hypothesis f_b : Zero [<=] (f b).

Local Small : IR := Two[/]ThreeNZ.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint interval_sequence [n:nat] : (bisect_interval f) :=
  Cases n of
    O => (Build_bisect_interval f a b a_b f_a f_b)
  | (S m) => (bisect f f_apzero_interval (interval_sequence m))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Local a_ := [i:nat](interval_lft ? (interval_sequence i)).
Local b_ := [i:nat](interval_rht ? (interval_sequence i)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma intervals_smaller :
  (i:nat)((b_ i)[-](a_ i) [<=] Small[^]i[*](b[-]a)).
(* End_Tex_Verb *)
Intros.
Induction i; Intros.
Unfold a_. Unfold b_. Simpl.
RStepr b[-]a.
Apply leEq_reflexive.
Apply leEq_transitive with Small[*]((b_ i)[-](a_ i)).
Elim (bisect_prop f f_apzero_interval (interval_sequence i)).
Intros H H0.
Elim H0; Intros H1 H2.
Auto.
Simpl.
Replace (nexp ? i Small) with Small[^]i. 2: Auto.
RStepr Small[*](Small[^]i[*](b[-]a)).
Apply mult_resp_leEq_lft.
Auto.
Apply less_leEq.
Unfold Small. Apply div_resp_pos. Apply pos_three. Apply pos_two.
Qed.

(* Begin_Tex_Verb *)
Lemma intervals_small'' : (i:nat)(Small[^]i[*](nring i) [<=] One).
(* End_Tex_Verb *)
Intros.
Apply mult_cancel_leEq with ((Three[^]i)::IR).
Apply nexp_resp_pos. Apply pos_three.
Stepr ((Three[^]i)::IR).
Apply leEq_wdl with (((nring i)[*]Two[^]i)::IR).
2: RStepr (nring i)[*](Small[^]i[*]Three[^]i).
2: Stepr (nring i)[*]((Small[*]Three)[^]i).
2: Cut Small[*]Three [=] Two; Algebra.
2: Unfold Small; Rational.
Induction i.
Simpl. Step (Zero::IR). Apply less_leEq. Apply pos_one.
Elim (zerop i); Intro y.
Rewrite y. Simpl.
RStep (Two::IR). RStepr (Three::IR).
Apply less_leEq. Apply two_less_three.
Elim (le_lt_eq_dec ? ? (lt_le_S ? ? y)); Intros H0.
Apply mult_cancel_leEq with ((nring i)::IR).
Step ((nring (0))::IR). Apply nring_less. Auto.
Apply leEq_wdl with ((nring (S i))[*]Two)[*](((nring i)[*]Two[^]i)::IR).
2: Simpl; Rational.
Apply leEq_wdr with ((((nring i)[*]Three)[*]Three[^]i)::IR).
2: Simpl; Rational.
Apply leEq_transitive with ((nring i)[*]Three)[*](((nring i)[*]Two[^]i)::IR).
Apply mult_resp_leEq_rht.
Simpl.
RStep (nring i)[*]Two[+](Two::IR).
RStepr (nring i)[*]Two[+]((nring i)::IR).
Apply plus_resp_leEq_lft.
Elim (le_lt_eq_dec ? ? (lt_le_S ? ? H0)); Intros H1.
Apply less_leEq. Apply nring_less. Auto.
Rewrite <- H1. Apply leEq_reflexive.
Apply less_leEq. Apply mult_resp_pos.
Step ((nring (0))::IR). Apply nring_less. Auto.
Apply nexp_resp_pos. Apply pos_two.
Apply mult_resp_leEq_lft. Auto.
Apply less_leEq. Apply mult_resp_pos.
Step ((nring (0))::IR). Apply nring_less. Auto.
Apply pos_three.
Rewrite <- H0.
RStep (!nring IR (8)).
RStepr (!nring IR (9)).
Apply nring_leEq. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma intervals_small' :
  (eps:IR)(Zero [<] eps) -> {i:nat | Small[^]i[*](b[-]a) [<=] eps}.
(* End_Tex_Verb *)
Intros.
Cut eps [#] Zero. Intro.
Elim (Archimedes (b[-]a)[/]eps[//]H0). Intro i. Intros H1. Exists i.
Stepr eps[*]One.
Apply shift_leEq_mult' with H0. Auto.
Apply leEq_transitive with Small[^]i[*](nring i).
Step Small[^]i[*]((b[-]a)[/]eps[//]H0).
Apply mult_resp_leEq_lft.
Auto.
Apply nexp_resp_nonneg.
Apply less_leEq.
Step (Zero::IR)[/]ThreeNZ. Unfold Small.
Apply div_resp_less_rht. Apply pos_two. Apply pos_three.
Apply intervals_small''.
Apply Greater_imp_ap. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma intervals_small :
  (eps:IR)(Zero [<] eps) -> {i:nat | (b_ i) [<=] (a_ i)[+]eps}.
(* End_Tex_Verb *)
Intros.
Elim (intervals_small' eps H). Intro i. Intros. Exists i.
Apply shift_leEq_plus'.
Apply leEq_transitive with Small[^]i[*](b[-]a).
Apply intervals_smaller.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Civt_op :
  {z:IR | (a [<=] z) /\ ((z [<=] b) /\ ((f z) [=] Zero))}.
(* End_Tex_Verb *)
Cut (i:nat)((a_ i) [<=] (a_ (S i))). Intro.
Cut (i:nat)((b_ (S i)) [<=] (b_ i)). Intro.
Cut (i:nat)((a_ i) [<] (b_ i)). Intro.
Cut (i:nat)((f (a_ i)) [<=] Zero). Intro.
Cut (i:nat)(Zero [<=] (f (b_ i))). Intro.
Elim (Cnested_intervals_zero a_ b_ H H0 H1 intervals_small f f_contin H2 H3).
Intro z. Intro H4. Exists z.
Exact H4.
Intros. Exact (interval_f_rht ? (interval_sequence i)).
Intros. Exact (interval_f_lft ? (interval_sequence i)).
Intros. Exact (interval_lft_rht ? (interval_sequence i)).
Intros. Elim (bisect_prop f f_apzero_interval (interval_sequence i)).
Intros H0 H1. Elim H1. Intros H2 H3.
Unfold b_. Simpl. 
Assumption.
Intros. Elim (bisect_prop f f_apzero_interval (interval_sequence i)).
Intros H H0. Elim H0. Intros H1 H2.
Unfold a_. Simpl. Auto.
Qed.

End IVT_Op.

Section IVT_Poly.

(* Tex_Prose
\section{IVT for polynomials}
*)

(* Begin_Tex_Verb *)
Lemma Civt_poly :
  (f:(cpoly_cring IR))(f [#] Zero) ->
  (a,b:IR)(a [<] b) -> (f!a [<=] Zero) -> (Zero [<=] f!b) ->
    { x:IR | (a [<=] x) /\ ((x [<=] b) /\ (f!x [=] Zero))}.
(* End_Tex_Verb *)
Intros.
Cut { x:IR |
  (a [<=] x) /\ ((x [<=] b) /\ (((cpoly_csetoid_op ? f) x) [=] Zero))}.
Intro. Auto.
Apply Civt_op; Auto.
Apply cpoly_op_contin.
Intros.
Change { c:IR | (a0 [<=] c) /\ (c [<=] b0) & ((f!c) [#] Zero)}.
Apply Cpoly_apzero_interval. Auto. Auto.
Qed.

End IVT_Poly.
