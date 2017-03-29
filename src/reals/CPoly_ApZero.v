(* $Id: CPoly_ApZero.v,v 1.14 2003/03/11 13:36:15 lcf Exp $ *)

Require Export CReals1.
Require Export CPoly_Degree.

(* Tex_Prose
\chapter{Polynomials apart from zero}
*)

(* Begin_Tex_Verb *)
Definition distinct1 :=
  [A:CSetoid; f:nat->A](i,j:nat)(~i=j) -> ((f i) [#] (f j)).
(* End_Tex_Verb *)

Implicits distinct1 [1].

Section Poly_Representation.
(* Tex_Prose
\section{Representation of polynomials}
\begin{convention}
Let \verb!R! be a field, \verb!a_ : nat->R! with
\verb!(distinct1 a_)! and \verb!f : (cpoly_cring R)! and
\verb!n : nat! with \verb!(degree_le n f)!.
\end{convention}
*)

Variable R : CField.
Variable a_ : nat->R.
Hypothesis distinct_a_ : (distinct1 a_).
Variable f : (cpoly_cring R).
Variable n : nat.
Hypothesis degree_f : (degree_le n f).

Load Transparent_algebra.

(* Begin_Tex_Verb *)
Lemma poly_linear_shifted :
  (a:R)(f:(cpoly_cring R))
    {f':(cpoly_cring R) & {f'':R | f [=] (_X_[-](_C_ a))[*]f'[+](_C_ f'')}}.
(* End_Tex_Verb *)
Intros.
Induction f0; Intros.
Exists (cpoly_zero R).
Exists (Zero::R).
Simpl.
Algebra.
Elim Hrecf0. Intro g'. Intros H.
Elim H. Intro g''. Intros H0.
Exists _X_[*]g'[+](_C_ g'').
Exists a[*]g''[+]s.
Step _X_[*]f0[+](_C_ s).
Step _X_[*]((_X_[-](_C_ a))[*]g'[+](_C_ g''))[+](_C_ s).
Apply eq_symmetric_unfolded.
Cut (_C_ a[*]g''[+]s) [=] (_C_ a)[*](_C_ g'')[+](_C_ s). Intro.
Step (_X_[-](_C_ a))[*](_X_[*]g'[+](_C_ g''))[+]
  ((_C_ a)[*](_C_ g'')[+](_C_ s)).
Rational.
Step_final (_C_ a[*]g'')[+](_C_ s).
Qed.
Load Opaque_algebra.

(* Begin_Tex_Verb *)
Lemma poly_linear_factor :
  (f:(cpoly_cring R))(a:R)(f!a [=] Zero) ->
    {f':(cpoly_cring R) | f [=] (_X_[-](_C_ a))[*]f'}.
(* End_Tex_Verb *)
Intros.
Elim (poly_linear_shifted a f0). Intro f'. Intros H0.
Elim H0. Intro f''. Intros H1.
Exists f'.
Cut (_C_ f'') [=] Zero. Intro.
Step (_X_[-](_C_ a))[*]f'[+](_C_ f'').
Step_final (_X_[-](_C_ a))[*]f'[+]Zero.
Step_rht (_C_ (Zero::R)).
Apply cpoly_const_eq.
Step Zero[+]f''.
Step Zero[*]f'!a[+]f''.
Step (a[-]a)[*]f'!a[+]f''.
Step (_X_!a[-](_C_ a)!a)[*]f'!a[+]f''.
Step (_X_[-](_C_ a))!a[*]f'!a[+]f''.
Step ((_X_[-](_C_ a))[*]f')!a[+]f''.
Step ((_X_[-](_C_ a))[*]f')!a[+](_C_ f'')!a.
Step ((_X_[-](_C_ a))[*]f'[+](_C_ f''))!a.
Step_final f0!a.
Qed.

(* Begin_Tex_Verb *)
Lemma zero_poly :
  (n:nat)
  (f:(cpoly_cring R))(degree_le n f) ->
  ((i:nat)(le i n) -> (f!(a_ i) [=] Zero)) ->
    (f [=] Zero).
(* End_Tex_Verb *)
Intro.
Induction n0; Intros.
Elim (degree_le_zero ? ? H). Intros.
Step (_C_ x).
Step_rht (_C_ (Zero::R)).
Apply cpoly_const_eq.
Apply eq_transitive_unfolded with f0!(a_ (0)).
Step_final (_C_ x)!(a_ (0)).
Apply H0.
Auto.
Cut f0!(a_ (S n0)) [=] Zero. Intro.
Elim (poly_linear_factor f0 (a_ (S n0)) H1). Intro f'. Intros.
Step (_X_[-](_C_ (a_ (S n0))))[*]f'.
Cut f' [=] Zero. Intro.
Step_final (_X_[-](_C_ (a_ (S n0))))[*]Zero.
Apply Hrecn0.
Apply degree_le_mult_imp with (1) (_X_[-](_C_ (a_ (S n0)))).
Apply degree_invus_lft with (0).
Apply degree_le_c_.
Apply degree_x_.
Auto.
Apply degree_le_wd with f0.
Auto.
Auto.
Intros.
Apply mult_cancel_lft with ((a_ i)[-](a_ (S n0))).
Apply minus_ap_zero.
Apply distinct_a_.
Intro; Rewrite H3 in H2; Exact (le_Sn_n ? H2).
Step_rht (Zero::R).
Cut (a_ i)[-](a_ (S n0)) [=] (_X_[-](_C_ (a_ (S n0))))!(a_ i). Intro.
Step (_X_[-](_C_ (a_ (S n0))))!(a_ i)[*]f'!(a_ i).
Step ((_X_[-](_C_ (a_ (S n0))))[*]f')!(a_ i).
Step f0!(a_ i).
Apply H0.
Auto with arith.
Step_final (_X_!(a_ i))[-]((_C_ (a_ (S n0)))!(a_ i)).
Apply H0.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma identical_poly :
  (f,g:(cpoly_cring R))(degree_le n f) -> (degree_le n g) ->
  ((i:nat)(le i n) -> (f!(a_ i) [=] g!(a_ i))) ->
    (f [=] g).
(* End_Tex_Verb *)
Intros.
Apply cg_inv_unique_2.
Apply zero_poly with n.
Apply degree_le_invus; Auto.
Intros.
Step f0!(a_ i)[-]g!(a_ i).
Step_final f0!(a_ i)[-]f0!(a_ i).
Qed.

(* Begin_Tex_Verb *)
Definition poly_01_factor' := [n:nat](_X_[-](_C_ (a_ n))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma poly_01_factor'_degree :
  (n:nat)(degree_le (1) (poly_01_factor' n)).
(* End_Tex_Verb *)
Intros.
Unfold poly_01_factor'.
Apply degree_imp_degree_le.
Apply degree_invus_lft with (0).
Apply degree_le_c_.
Apply degree_x_.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_01_factor'_zero :
  (n:nat)((poly_01_factor' n)!(a_ n) [=] Zero).
(* End_Tex_Verb *)
Intros.
Unfold poly_01_factor'.
Step (_X_!(a_ n0))[-]((_C_ (a_ n0))!(a_ n0)).
Step_final (a_ n0)[-](a_ n0).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_01_factor'_apzero :
  (n,i:nat)(~i = n) -> ((poly_01_factor' n)!(a_ i) [#] Zero).
(* End_Tex_Verb *)
Intros.
Unfold poly_01_factor'.
Step (_X_!(a_ i))[-]((_C_ (a_ n0))!(a_ i)).
Step (a_ i)[-](a_ n0).
Qed.

Hints Resolve poly_01_factor'_zero.

(* Begin_Tex_Verb *)
Definition poly_01_factor :=
  [n,i:nat; H:(~i = n)]
    (poly_01_factor' n)[*](_C_ One[/]((poly_01_factor' n)!(a_ i))[//]
      (poly_01_factor'_apzero n i H)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma poly_01_factor_degree :
  (n,i:nat; H:(~i = n))(degree_le (1) (poly_01_factor n i H)).
(* End_Tex_Verb *)
Intros.
Unfold poly_01_factor.
Replace (1) with (plus (1) (0)).
Apply degree_le_mult.
Apply poly_01_factor'_degree.
Apply degree_le_c_.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_01_factor_zero :
  (n,i:nat; H:(~i = n))((poly_01_factor n i H)!(a_ n) [=] Zero).
(* End_Tex_Verb *)
Intros.
Unfold poly_01_factor.
Step ((poly_01_factor' n0)!(a_ n0))[*]
  ((_C_ One[/](poly_01_factor' n0)!(a_ i)[//]
    (poly_01_factor'_apzero n0 i H))!(a_ n0)).
Step_final Zero[*]((_C_ One[/](poly_01_factor' n0)!(a_ i)[//]
  (poly_01_factor'_apzero n0 i H))!(a_ n0)).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_01_factor_one :
  (n,i:nat; H:(~i = n))((poly_01_factor n i H)!(a_ i) [=] One).
(* End_Tex_Verb *)
Intros.
Unfold poly_01_factor.
Step ((poly_01_factor' n0)!(a_ i))[*]
  ((_C_ One[/](poly_01_factor' n0)!(a_ i)[//]
    (poly_01_factor'_apzero n0 i H))!(a_ i)).
Step ((poly_01_factor' n0)!(a_ i))[*]
  (One[/](poly_01_factor' n0)!(a_ i)[//](poly_01_factor'_apzero n0 i H)).
Rational.
Qed.

Hints Resolve poly_01_factor_zero poly_01_factor_one : algebra.

(* Begin_Tex_Verb *)
Fixpoint poly_01 [i,n:nat] : (cpoly_cring R) :=
    Cases (eq_nat_dec i n) of
      (left _) => One
    | (right ne) => (poly_01_factor n i ne)
    end
  [*]
    Cases n of
      O => One
    | (S m) => (poly_01 i m)
    end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma poly_01_degree' :
  (n,i:nat)(degree_le (S n) (poly_01 i n)).
(* End_Tex_Verb *)
Intros.
Induction n0. Intros.
Simpl.
Elim (eq_nat_dec i (0)); Intro y.
Apply degree_le_wd with (_C_ (One::R)).
Step_final (One::(cpoly_cring R)).
Apply degree_le_mon with (0).
Auto with arith.
Apply degree_le_c_.
Apply degree_le_wd with (poly_01_factor (0) i y).
Algebra.
Apply poly_01_factor_degree.
Simpl.
Elim (eq_nat_dec i (S n0)); Intro.
Apply degree_le_mon with (S n0).
Auto.
Apply degree_le_wd with (poly_01 i n0).
Algebra.
Auto.
Replace (S (S n0)) with (plus (1) (S n0)).
Apply degree_le_mult.
Apply poly_01_factor_degree.
Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_01_degree :
  (n,i:nat)(le i n) -> (degree_le n (poly_01 i n)).
(* End_Tex_Verb *)
Intros.
Induction n0; Intros.
Simpl.
Elim (eq_nat_dec i (0)); Intro y.
Apply degree_le_wd with (_C_ (One::R)).
Step_final (One::(cpoly_cring R)).
Apply degree_le_c_.
Cut i=(0). Intro.
Elim (y H0).
Auto with arith.
Simpl.
Elim (eq_nat_dec i (S n0)); Intro.
Apply degree_le_wd with (poly_01 i n0).
Algebra.
Apply poly_01_degree'.
Pattern 1 (S n0).
Replace (S n0) with (plus (1) n0).
Apply degree_le_mult.
Apply poly_01_factor_degree.
Apply Hrecn0.
Elim (le_lt_eq_dec ?? H); Auto with arith.
Intro; Elim (b b0).
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_01_zero :
  (n,i,j:nat)(le j n) -> (~j = i) -> ((poly_01 i n)!(a_ j) [=] Zero).
(* End_Tex_Verb *)
Intros.
Induction n0; Intros.
Rewrite <- (le_n_O_eq j H).
Rewrite <- (le_n_O_eq j H) in H0.
Simpl.
Elim (eq_nat_dec i (0)); Intro y.
Rewrite y in H0.
Elim (H0 (refl_equal ? (0))).
Step ((poly_01_factor (0) i y)!(a_ (0)))[*](One!(a_ (0))).
Step ((poly_01_factor (0) i y)!(a_ (0)))[*]One.
Step ((poly_01_factor (0) i y)!(a_ (0))).
Apply poly_01_factor_zero.
Elim (eq_nat_dec j (S n0)); Intro y.
Simpl.
Rewrite <- y.
Elim (eq_nat_dec i j); Intro y0.
Rewrite y0 in H0.
Elim (H0 (refl_equal ? j)).
Step ((poly_01_factor j i y0)!(a_ j))[*]((poly_01 i n0)!(a_ j)).
Step_final Zero[*]((poly_01 i n0)!(a_ j)).
Cut (le j n0). Intro.
Simpl.
Elim (eq_nat_dec i (S n0)); Intro y0.
Step (One!(a_ j))[*]((poly_01 i n0)!(a_ j)).
Step_final (One!(a_ j))[*]Zero.
Step ((poly_01_factor (S n0) i y0)!(a_ j))[*]((poly_01 i n0)!(a_ j)).
Step_final ((poly_01_factor (S n0) i y0)!(a_ j))[*]Zero.
Elim (le_lt_eq_dec ?? H); Auto with arith.
Intro; Elim (y b).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_01_one :
  (n,i:nat)(poly_01 i n)!(a_ i) [=] One.
(* End_Tex_Verb *)
Intros.
Induction n0; Intros.
Simpl.
Elim (eq_nat_dec i (0)); Intro y.
Step (One!(a_ i))[*](One!(a_ i)).
Step_final One[*](One::R).
Step ((poly_01_factor (0) i y)!(a_ i))[*](One!(a_ i)).
Step ((poly_01_factor (0) i y)!(a_ i))[*]One.
Step (poly_01_factor (0) i y)!(a_ i).
Apply poly_01_factor_one.
Simpl.
Elim (eq_nat_dec i (S n0)); Intro y.
Step (One!(a_ i))[*]((poly_01 i n0)!(a_ i)).
Step One[*]((poly_01 i n0)!(a_ i)).
Step_final One[*](One::R).
Step ((poly_01_factor (S n0) i y)!(a_ i))[*]((poly_01 i n0)!(a_ i)).
Step ((poly_01_factor (S n0) i y)!(a_ i))[*]One.
Step (poly_01_factor (S n0) i y)!(a_ i).
Apply poly_01_factor_one.
Qed.

Hints Resolve poly_01_zero poly_01_one : algebra.

(* Begin_Tex_Verb *)
Lemma poly_representation'' :
  (a:nat->R)(i:nat)(le i n) ->
  ((j:nat)(~j = i) -> (a j) [=] Zero) ->
    (Sum (0) n a) [=] (a i).
(* End_Tex_Verb *)
Intro. Intro.
Elim i.
Intros.
Step (a (0))[+](Sum (1) n a).
Step_rht (a (0))[+]Zero.
Apply bin_op_wd_unfolded.
Algebra.
Apply Sum_zero.
Auto with arith.
Intros.
Apply H0.
Intro; Rewrite H3 in H1; Inversion H1.
Intro i'.
Intros.
Step (Sum (0) i' a)[+](Sum (S i') n a).
Step_rht Zero[+](a (S i')).
Apply bin_op_wd_unfolded.
Apply Sum_zero.
Auto with arith.
Intros.
Apply H1.
Intro; Rewrite H4 in H3; Exact (le_Sn_n ? H3).
Step (a (S i'))[+](Sum (S (S i')) n a).
Step_rht (a (S i'))[+]Zero.
Apply bin_op_wd_unfolded.
Algebra.
Apply Sum_zero.
Auto with arith.
Intros.
Apply H1.
Intro; Rewrite H4 in H2; Exact (le_Sn_n ? H2).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_representation' :
  (f_:nat->(cpoly_cring R))(k:nat)(le k n) ->
    (Sum (0) n [i:nat]((f_ i)[*](poly_01 i n)))!(a_ k) [=] (f_ k)!(a_ k).
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with
  (Sum (0) n [i:nat]((f_ i)[*](poly_01 i n))!(a_ k)).
Apply Sum_cpoly_ap with f := [i:nat](f_ i)[*](poly_01 i n).
Step (Sum (0) n [i:nat](f_ i)!(a_ k)[*](poly_01 i n)!(a_ k)).
Step_rht (f_ k)!(a_ k)[*]One.
Step_rht (f_ k)!(a_ k)[*](poly_01 k n)!(a_ k).
Apply poly_representation'' with
  a := [i:nat](f_ i)!(a_ k)[*](poly_01 i n)!(a_ k).
Auto.
Intros.
Step_final (f_ j)!(a_ k)[*]Zero.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_representation :
  f [=] (Sum (0) n [i:nat](_C_ f!(a_ i))[*](poly_01 i n)).
(* End_Tex_Verb *)
Apply identical_poly.
Auto.
Apply Sum_degree_le. Auto with arith. Intros.
Replace n with (plus (0) n).
Apply degree_le_mult.
Apply degree_le_c_.
Apply poly_01_degree.
Auto.
Auto with arith.
Intros.
Apply eq_symmetric_unfolded.
Step_rht (_C_ f!(a_ i))!(a_ i).
Apply poly_representation' with f_ := [i:nat](_C_ f!(a_ i)).
Auto.
Qed.

Hints Resolve poly_representation : algebra.

(* Begin_Tex_Verb *)
Lemma Cpoly_choose_apzero :
  (f [#] Zero) -> { i:nat | (le i n) & (f!(a_ i) [#] Zero)}.
(* End_Tex_Verb *)
Intros.
Cut (Sum (0) n [i:nat](_C_ f!(a_ i))[*](poly_01 i n)) [#] Zero. Intros.
Elim (Sum_apzero ? [i:nat](_C_ f!(a_ i))[*](poly_01 i n) (0) n (le_O_n n) H0).
Intro i. Intro H1.
Elim H1. Intros H2 H3. Intro H4.
Exists i.
Auto.
Apply poly_c_apzero.
Apply cring_mult_ap_zero with (poly_01 i n).
Auto.
Step f.
Qed.

End Poly_Representation.

(* Tex_Prose
\section{Polynomials are nonzero on any interval}
*)
Section Poly_ApZero_Interval.

Variable R: COrdField.

(* Begin_Tex_Verb *)
Lemma Cpoly_apzero_interval :
  (f:(cpoly_cring R))(f [#] Zero) ->
  (a,b:R)(a [<] b) ->
    { c:R | (a [<=] c) /\ (c [<=] b) & (f!c [#] Zero)}.
(* End_Tex_Verb *)
Intros.
Elim (Cpoly_ex_degree ? f). Intro n. Intro H1.
Cut Zero [<] ((nring (plus n (2)))::R). Intros.
Cut (nring (plus n (2))) [#] (Zero::R). Intros.
Cut (distinct1
  [i:nat](((nring (plus i (1)))[*]a[+]
    ((nring (plus n (2)))[-](nring (plus i (1))))[*]b)[/]
    (nring (plus n (2)))[//]H3)).
Intro.
Elim (Cpoly_choose_apzero ?
  [i:nat](((nring (plus i (1)))[*]a[+]
    ((nring (plus n (2)))[-](nring (plus i (1))))[*]b)[/]
    (nring (plus n (2)))[//]H3)
  H4 f n H1 H).
Intro i. Intros H6 H7.
Exists (((nring (plus i (1)))[*]a[+]
  ((nring (plus n (2)))[-](nring (plus i (1))))[*]b)[/]
    (nring (plus n (2)))[//]H3).
Split.
Apply less_leEq.
Apply shift_less_div.
Auto.
Apply less_wdl with (nring (plus i (1)))[*]a[+]
  ((nring (plus n (2)))[-](nring (plus i (1))))[*]a.
Apply plus_resp_less_lft.
Apply mult_resp_less_lft.
Auto.
Apply shift_zero_less_minus.
Apply nring_less.
Omega.
Rational.
Apply less_leEq.
Apply shift_div_less.
Auto.
Apply less_wdr with (nring (plus i (1)))[*]b[+]
  ((nring (plus n (2)))[-](nring (plus i (1))))[*]b.
Apply plus_resp_less_rht.
Apply mult_resp_less_lft.
Auto.
Step ((nring (0))::R).
Apply nring_less.
Auto with arith.
Rational.
Auto.
Unfold distinct1.
Intros.
Apply zero_minus_apart.
RStep (((nring (plus i (1)))[-](nring (plus j (1))))[*](a[-]b))[/]
  (nring (plus n (2)))[//]H3.
Apply div_resp_ap_zero_rev.
Apply mult_resp_ap_zero.
Apply minus_ap_zero.
Apply nring_apart.
Repeat Rewrite <- plus_n_Sm; Repeat Rewrite <- plus_n_O.
Apply not_eq_S; Auto.
Apply minus_ap_zero.
Apply less_imp_ap.
Auto.
Apply ap_symmetric_unfolded.
Apply less_imp_ap.
Auto.
Step ((nring (0))::R).
Apply nring_less.
Auto with arith.
Qed.

End Poly_ApZero_Interval.


