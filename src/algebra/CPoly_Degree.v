(* $Id: CPoly_Degree.v,v 1.12 2003/03/11 13:35:52 lcf Exp $ *)

Require Export CPoly_NthCoeff.
Require Export CFields.

(* Tex_Prose
\chapter{Polynomials: Degree}
\begin{convention}
Let \verb!R! be a ring and write \verb!RX! for the ring of polynomials
over \verb!R!.
\end{convention}
*)

Section Degree_def.

Variable R: CRing.

Syntactic Definition RX := (cpoly_cring R).

(* Tex_Prose
The length of a polynomial is the number of its coefficients. This is a
syntactical property, as the highest coefficient may be $0$. Note that the
`zero' polynomial \verb!cpoly_zero! has length $0$, a constant
polynomial has length $1$ and so forth. So the length is always $1$ higher
than the `degree' (assuming that the highest coefficient is $\noto 0$)!
*)
(* Begin_Tex_Verb *)
Fixpoint lth_of_poly [p: RX] : nat :=
  Cases p of
     	cpoly_zero => O
	| (cpoly_linear d q) => (S(lth_of_poly q))
  end.
(* End_Tex_Verb *)

(* Tex_Prose
   When dealing with constructive polynomials, notably
   over the reals or complex numbers, the degree may be unknown, as we can not
   decide whether the highest coeffiecient is $\noto 0$.
   Hence, degree is a {\em relation\/} between polynomials and natural numbers;
   if the degree is unknown for polynomial $p$, degree$(n,p)$ doesn't hold for
   any $n$.
   If we don't know the degree of $p$, we may still know it to be below or
   above a certain number. E.g.\ for the polynomial
   $p_0 +p_1 X +\cdots + p_{n-1} X^{n-1}$,
   if $p_i \noto 0$, we can say that the `degree is
   at least $i$' and if $p_{j+1} = \ldots =p_n =0$ (with $n$ the length of the
   polynomial), we can say that the `degree is
   at most $j$'.
*)

(* Begin_Tex_Verb *)
Definition degree_le : nat -> RX -> Prop :=
  [n:nat][p:RX] (m:nat)((lt n m)-> ((nth_coeff m p) [=] Zero)).

Definition degree : nat -> RX -> CProp :=
  [n:nat][p:RX] ((nth_coeff n p) [#] Zero) * {degree_le n p}.

Definition monic : nat -> RX -> Prop :=
  [n:nat][p:RX] ((nth_coeff n p) [=] One) /\ (degree_le n p).

Definition odd_cpoly : RX -> CProp :=
  [p:RX]{ n:nat & (Codd n) & (degree n p)}.

Definition even_cpoly : RX -> CProp :=
  [p:RX]{ n:nat & (Ceven n) & (degree n p)}.

Definition regular :RX-> CProp :=
  [p:RX]{ n:nat & degree n p}.
(* End_Tex_Verb *)

End Degree_def.

Implicits degree_le [1].
Implicits degree [1].
Implicits monic [1].
Implicits lth_of_poly [1].

Section Degree_props.

Variable R: CRing.

Syntactic Definition RX := (cpoly_cring R).

(* Begin_Tex_Verb *)
Lemma degree_le_wd : (p,p':RX)(n:nat)
  (p [=] p')->(degree_le n p)->(degree_le n p').
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Step_final (nth_coeff m p).
Qed.

(* Begin_Tex_Verb *)
Lemma degree_wd : (p,p':RX)(n:nat)
  (p [=] p')->(degree n p)->(degree n p').
(* End_Tex_Verb *)
Unfold degree. Intros.
Elim H0. Clear H0. Intros. Split.
Step (nth_coeff n p).
Apply degree_le_wd with p; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_wd : (p,p':RX)(n:nat)
  (p [=] p')->(monic n p)->(monic n p').
(* End_Tex_Verb *)
Unfold monic. Intros.
Elim H0. Clear H0. Intros. Split.
Step_final (nth_coeff n p).
Apply degree_le_wd with p; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_imp_degree_le : (p:RX)(n:nat)(degree n p)->(degree_le n p).
(* End_Tex_Verb *)
Unfold degree. Intros. Elim H. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_c_ : (c:R)(degree_le O (_C_ c)).
(* End_Tex_Verb *)
Unfold degree_le. Intros c m. Elim m; Intros.
Elim (lt_n_n ? H).
Simpl. Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_c_ : (c:R)(c [#] Zero)->(degree O (_C_ c)).
(* End_Tex_Verb *)
Unfold degree. Intros. Split. Simpl. Auto. Apply degree_le_c_.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_c_one : (monic O (_C_ One::R)).
(* End_Tex_Verb *)
Unfold monic. Intros. Split. Simpl. Algebra. Apply degree_le_c_.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_x_ : (degree_le (1) _X_::RX).
(* End_Tex_Verb *)
Unfold degree_le.
Intro. Elim m. Intros. Elim (lt_n_O ? H).
Intro. Elim n. Intros. Elim (lt_n_n ? H0).
Intros. Simpl. Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_x_ : (degree (1) _X_::RX).
(* End_Tex_Verb *)
Unfold degree. Split. Simpl. Algebra. Exact degree_le_x_.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_x_ : (monic (1) _X_::RX).
(* End_Tex_Verb *)
Unfold monic. Split. Simpl. Algebra. Exact degree_le_x_.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_mon : (p:RX)(m,n:nat)
  (le m n) -> (degree_le m p) -> (degree_le n p).
(* End_Tex_Verb *)
Unfold degree_le. Intros. Apply H0. 
Apply le_lt_trans with n; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_inv : (p:RX)(n:nat)(degree_le n p)->(degree_le n [--]p).
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Step [--](nth_coeff m p).
Step_final [--](Zero::R).
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_plus : (p,q:RX)(n:nat)
  (degree_le n p) -> (degree_le n q) -> (degree_le n p[+]q).
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Step (nth_coeff m p)[+](nth_coeff m q).
Step_final Zero[+](Zero::R).
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_invus : (p,q:RX)(n:nat)
  (degree_le n p) -> (degree_le n q) -> (degree_le n p[-]q).
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Step (nth_coeff m p)[-](nth_coeff m q).
Step_final Zero[-](Zero::R).
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_degree_le : (f:nat->RX)(n,k,l:nat)(le k (S l)) ->
  ((i:nat)(le k i) -> (le i l) -> (degree_le n (f i))) ->
    (degree_le n (Sum k l f)).
(* End_Tex_Verb *)
Unfold degree_le. Intros. Induction l; Intros.
Generalize (toCle ?? H); Clear H; Intro H.
Inversion H.
Unfold Sum. Unfold Sum1. Simpl.
Apply eq_transitive_unfolded with (nth_coeff m (Zero::RX)).
Apply nth_coeff_wd. Algebra. Algebra.
Inversion H3. Unfold Sum. Unfold Sum1. Simpl.
Apply eq_transitive_unfolded with (nth_coeff m (f (0))).
Apply nth_coeff_wd. Cut (f (0))[-]Zero [=] (f (0)). Auto. Algebra.
Apply H0; Try Auto. Rewrite H4. Auto.
Elim (le_lt_eq_dec ? ? H); Intro y.
Apply eq_transitive_unfolded with (nth_coeff m (Sum k l f)[+](f (S l))).
Apply nth_coeff_wd. Algebra.
Step (nth_coeff m (Sum k l f))[+](nth_coeff m (f (S l))).
Stepr Zero[+](Zero::R). Apply bin_op_wd_unfolded.
Apply Hrecl. Auto with arith. Intros.
Apply H0. Auto. Auto. Auto.
Apply H0. Auto with arith. Auto. Auto.
Rewrite y. Unfold Sum. Unfold Sum1. Simpl.
Apply eq_transitive_unfolded with (nth_coeff m (Zero::RX)).
Apply nth_coeff_wd. Algebra. Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_inv : (p:RX)(n:nat)(degree n p)->(degree n [--]p).
(* End_Tex_Verb *)
Unfold degree. Intros.
Elim H. Clear H. Intros. Split.
Step [--](nth_coeff n p).
Apply degree_le_inv; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_plus_rht : (p,q:RX)(m,n:nat)
             (degree_le m p)->(degree n q)->(lt m n)->(degree n (p [+] q)).
(* End_Tex_Verb *)
Unfold degree. Unfold degree_le. Intros.
Elim H0. Clear H0. Intros.
Split.
Step (nth_coeff n p)[+](nth_coeff n q).
Step Zero[+](nth_coeff n q).
Step (nth_coeff n q).
Intros.
Step (nth_coeff m0 p)[+](nth_coeff m0 q).
Cut (lt m m0). Intro.
Step_final Zero[+](Zero::R).
Apply lt_trans with n; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_invus_lft : (p,q:RX)(m,n:nat)
             (degree_le m p)->(degree n q)->(lt m n)->(degree n (q [-] p)).
(* End_Tex_Verb *)
Intros.
Apply degree_wd with ([--]p)[+]q.
Step_final q[+][--]p.
Apply degree_plus_rht with m.
Apply degree_le_inv. Auto. Auto. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_plus : (p,q:RX)(m,n:nat)
  (degree_le m p) -> (monic n q) -> (lt m n) -> (monic n p[+]q).
(* End_Tex_Verb *)
Unfold monic. Unfold degree_le. Intros.
Elim H0. Clear H0. Intros.
Split.
Step (nth_coeff n p)[+](nth_coeff n q).
Step Zero[+](nth_coeff n q).
Step_final (nth_coeff n q).
Intros.
Step (nth_coeff m0 p)[+](nth_coeff m0 q).
Cut (lt m m0). Intro.
Step_final Zero[+](Zero::R).
Apply lt_trans with n; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_minus : (p,q:RX)(m,n:nat)
  (degree_le m p) -> (monic n q) -> (lt m n) -> (monic n q[-]p).
(* End_Tex_Verb *)
Intros.
Apply monic_wd with ([--]p)[+]q.
Step_final q[+][--]p.
Apply monic_plus with m.
Apply degree_le_inv. Auto. Auto. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_mult : (p,q:RX)(m,n:nat)
             (degree_le m p)->(degree_le n q)->(degree_le (plus m n) p[*]q).
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Step (Sum (0) m0 [i:nat](nth_coeff i p)[*](nth_coeff (minus m0 i) q)).
Apply Sum_zero. Auto with arith.
Intros.
Cut {lt m i} + {lt n (minus m0 i)}. Intro.
Elim H4; Clear H4; Intros.
Step_final Zero[*](nth_coeff (minus m0 i) q).
Step_final (nth_coeff i p)[*]Zero.
Elim (lt_eq_lt_dec m i); Intro.
Elim a; Intro.
Auto.
Right.
Omega.
Right.
Omega.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_mult_aux : (p,q:RX)(m,n:nat)
 (degree_le m p)->(degree_le n q)->
             (nth_coeff (plus m n) p[*]q) [=]
               (nth_coeff m p)[*](nth_coeff n q).
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Step (Sum (0) (plus m n)
  [i:nat](nth_coeff i p)[*](nth_coeff (minus (plus m n) i) q)).
Step (Sum (0) m [i:nat](nth_coeff i p)[*](nth_coeff (minus (plus m n) i) q))[+]
  (Sum (S m) (plus m n)
    [i:nat](nth_coeff i p)[*](nth_coeff (minus (plus m n) i) q)).
Stepr (nth_coeff m p)[*](nth_coeff n q)[+]Zero.
Apply bin_op_wd_unfolded.
Elim (O_or_S m); Intro y.
Elim y. Clear y. Intros x y. Rewrite <- y in H. Rewrite <- y.
Apply eq_transitive_unfolded with (Sum (0) x
  [i:nat](nth_coeff i p)[*](nth_coeff (minus (plus (S x) n) i) q))[+]
    (nth_coeff (S x) p)[*](nth_coeff (minus (plus (S x) n) (S x)) q).
Apply Sum_last with f :=
  [i:nat](nth_coeff i p)[*](nth_coeff (minus (plus (S x) n) i) q).
Stepr Zero[+](nth_coeff (S x) p)[*](nth_coeff n q).
Apply bin_op_wd_unfolded.
Apply Sum_zero. Auto with arith. Intros.
Cut (lt n (minus (plus (S x) n) i)). Intro.
Step_final (nth_coeff i p)[*]Zero.
Omega.
Replace (minus (plus (S x) n) (S x)) with n. Algebra. Auto with arith.
Rewrite <- y in H. Rewrite <- y.
Pattern 2 n. Replace n with (minus (plus (0) n) (0)).
Apply Sum_one with f :=
  [i:nat](nth_coeff i p)[*](nth_coeff (minus (plus (0) n) i) q).
Auto with arith.
Apply Sum_zero. Auto with arith. Intros.
Cut (lt m i). Intro.
Step_final Zero[*](nth_coeff (minus (plus m n) i) q).
Auto.
Qed.

Hints Resolve degree_mult_aux : algebra.

(* Begin_Tex_Verb *)
Lemma monic_mult : (p,q:RX)(m,n:nat)
             (monic m p)->(monic n q)->(monic (plus m n) p[*]q).
(* End_Tex_Verb *)
Unfold monic. Intros.
Elim H. Clear H. Intros. Elim H0. Clear H0. Intros. Split.
Step (nth_coeff m p)[*](nth_coeff n q).
Step_final One[*](One::R).
Apply degree_le_mult; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_nexp : (p:RX)(m,n:nat)
             (degree_le m p)->(degree_le (mult m n) p[^]n).
(* End_Tex_Verb *)
Intros. Induction n; Intros.
Replace (mult m (0)) with (0).
Apply degree_le_wd with (_C_ (One::R)). Algebra.
Apply degree_le_c_.
Auto.
Replace (mult m (S n)) with (plus (mult m n) m).
Apply degree_le_wd with p[^]n[*]p. Algebra.
Apply degree_le_mult; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_nexp : (p:RX)(m,n:nat)(monic m p)->(monic (mult m n) p[^]n).
(* End_Tex_Verb *)
Intros. Induction n; Intros.
Replace (mult m (0)) with (0).
Apply monic_wd with (_C_ (One::R)). Algebra.
Apply monic_c_one.
Auto.
Replace (mult m (S n)) with (plus (mult m n) m).
Apply monic_wd with p[^]n[*]p. Algebra.
Apply monic_mult; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_i_lth_of_poly : (i:nat)(p:RX)
  ((nth_coeff i p) [#] Zero) -> (lt i (lth_of_poly p)).
(* End_Tex_Verb *)
Intros i. Induction i; Intros.
Induction p; Intros.
Simpl in H. Elim (ap_irreflexive_unfolded ? ? H).
Simpl. Auto with arith.
Induction p; Intros.
Simpl in H. Elim (ap_irreflexive_unfolded ? ? H).
Simpl. Simpl in H. Apply lt_n_S. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_degree_lth : (p:RX)
  (degree_le (lth_of_poly p) p).
(* End_Tex_Verb *)
Unfold degree_le. Intros. Apply not_ap_imp_eq. Intro.
Elim (lt_not_le ? ? H). Apply lt_le_weak.
Apply lt_i_lth_of_poly. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cpoly_ex_degree : (p:RX){n:nat | (degree_le n p)}.
(* End_Tex_Verb *)
Intros. Exists (lth_of_poly p). Apply poly_degree_lth.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_as_sum'' : (p:RX)(n:nat)(degree_le n p)->
  p [=] (Sum (0) n [i:nat](_C_ (nth_coeff i p))[*]_X_[^]i).
(* End_Tex_Verb *)
Unfold degree_le. Intros. Apply all_nth_coeff_eq_imp. Intros.
Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with
  (Sum (0) n [i0:nat](nth_coeff i (_C_ (nth_coeff i0 p))[*]_X_[^]i0)).
Apply nth_coeff_sum with p_ := [i:nat](_C_ (nth_coeff i p))[*]_X_[^]i.
Apply eq_transitive_unfolded with
  (Sum (0) n [i0:nat](nth_coeff i0 p)[*](nth_coeff i _X_[^]i0)).
Apply Sum_wd. Intros. Algebra.
Elim (le_lt_dec i n); Intros.
Stepr (nth_coeff i p)[*]One.
Stepr (nth_coeff i p)[*](nth_coeff i _X_[^]i).
Apply Sum_term with i := i
  f := [i0:nat](nth_coeff i0 p)[*](nth_coeff i _X_[^]i0).
Auto with arith. Auto.
Intros.
Step_final (nth_coeff j p)[*]Zero.
Stepr (Zero::R).
Apply Sum_zero. Auto with arith. Intros.
Cut (~i=i0). Intro.
Step_final (nth_coeff i0 p)[*]Zero.
Intro; Rewrite <- H2 in H1.
Apply (le_not_lt i n); Auto.
Qed.

Hints Resolve poly_as_sum'' : algebra.

(* Begin_Tex_Verb *)
Lemma poly_as_sum' : (p:RX)
  p [=] (Sum (0) (lth_of_poly p) [i:nat](_C_ (nth_coeff i p))[*]_X_[^]i).
(* End_Tex_Verb *)
Intros. Apply poly_as_sum''. Apply poly_degree_lth.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_as_sum : (p:RX)(n:nat)(degree_le n p)->
  (x:R)(p!x [=] (Sum (0) n [i:nat](nth_coeff i p)[*]x[^]i)).
(* End_Tex_Verb *)
Intros.
Step (Sum (0) n [i:nat](_C_ (nth_coeff i p))[*]_X_[^]i)!x.
Apply eq_transitive_unfolded with
  (Sum (0) n [i:nat]((_C_ (nth_coeff i p))[*]_X_[^]i)!x).
Apply Sum_cpoly_ap with f := [i:nat](_C_ (nth_coeff i p))[*]_X_[^]i.
Apply Sum_wd. Intros.
Step (_C_ (nth_coeff i p))!x[*](_X_[^]i)!x.
Step_final (nth_coeff i p)[*](_X_!x)[^]i.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_zero : (p:RX)
  (degree_le (0) p) -> {a:R | p [=] (_C_ a)}.
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Exists (nth_coeff (0) p).
Apply all_nth_coeff_eq_imp. Intros.
Elim (O_or_S i); Intro y.
Elim y. Clear y. Intros x y. Rewrite <- y.
Cut (lt (0) (S x)). Intro. Step_final (Zero::R). Auto with arith.
Rewrite <- y. Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_1_imp : (p:RX)
  (degree_le (1) p) -> {a:R & {b:R | p [=] (_C_ a)[*]_X_[+](_C_ b)}}.
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Exists (nth_coeff (1) p). Exists (nth_coeff (0) p).
Apply all_nth_coeff_eq_imp. Intros.
Elim i; Intros.
Simpl. Rational.
Elim n; Intros.
Simpl. Algebra.
Simpl. Apply H. Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_cpoly_linear :
  (p:(cpoly R))(c:R)(n:nat)
    (degree_le (S n) (cpoly_linear ? c p)) -> (degree_le n p).
(* End_Tex_Verb *)
Unfold degree_le. Intros.
Change (nth_coeff (S m) (cpoly_linear ? c p)) [=] Zero.
Apply H. Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_cpoly_linear :
  (p:(cpoly R))(c:R)(n:nat)
    (monic (S n) (cpoly_linear ? c p)) -> (monic n p).
(* End_Tex_Verb *)
Unfold monic. Intros. Elim H. Clear H. Intros. Split. Auto.
Apply degree_le_cpoly_linear with c. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_one :
  (p:(cpoly R))(c:R)
    (monic (1) (cpoly_linear ? c p)) -> (x:R)(p!x [=] One).
(* End_Tex_Verb *)
Intros. Cut (monic (0) p). Unfold monic. Intros. Elim H0. Clear H0.
Intros H0 H1.
Elim (degree_le_zero ? H1). Intro d. Intros.
Step (_C_ d)!x.
Step d.
Step (nth_coeff (0) (_C_ d)).
Step_final (nth_coeff (0) p).
Apply monic_cpoly_linear with c. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma monic_apzero :
  (p:RX)(n:nat)(monic n p) -> (p [#] Zero).
(* End_Tex_Verb *)
Unfold monic. Intros.
Elim H. Clear H. Intros.
Apply nth_coeff_ap_zero_imp with n.
Step (One::R).
Qed.

End Degree_props.

Hints Resolve poly_as_sum'' poly_as_sum' poly_as_sum : algebra.
Hints Resolve degree_mult_aux : algebra.


Section degree_props_Field.

Variable F: CField.

Syntactic Definition FX := (cpoly_cring F).

(* Begin_Tex_Verb *)
Lemma degree_mult : (p,q:FX)(m,n:nat)
             (degree m p)->(degree n q)->(degree (plus m n) p[*]q).
(* End_Tex_Verb *)
Unfold degree. Intros.
Elim H. Clear H. Intros H1 H2. Elim H0. Clear H0. Intros H3 H4. 
Split.
Step (nth_coeff m p)[*](nth_coeff n q).
Apply degree_le_mult; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_nexp : (p:FX)(m,n:nat)(degree m p)->(degree (mult m n) p[^]n).
(* End_Tex_Verb *)
Intros. Induction n; Intros.
Replace (mult m (0)) with (0).
Apply degree_wd with (_C_ (One::F)). Algebra.
Apply degree_c_. Algebra.
Auto.
Replace (mult m (S n)) with (plus (mult m n) m).
Apply degree_wd with p[^]n[*]p. Algebra.
Apply degree_mult; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma degree_le_mult_imp : (m,n:nat)(p,q:FX)
  (degree m p) -> (degree_le (plus m n) p[*]q) -> (degree_le n q).
(* End_Tex_Verb *)
Unfold degree. Unfold degree_le. Intros. Elim H. Clear H. Intros H2 H3.
Elim (Cpoly_ex_degree ? q). Unfold degree_le. Intro N. Intro H4. 
     (* Set_ not necessary *)
Cut (k,i:nat)(lt n i) -> (lt (minus N k) i) -> (nth_coeff i q) [=] Zero. Intro H5.
Elim (le_lt_dec m0 N); Intros H6.
Replace m0 with (minus N (minus N m0)). Apply H5 with (minus N n).
Omega. Omega. Omega.
Apply H4; Auto.
Intro. Induction k; Intros.
Apply H4. Rewrite <- minus_n_O in H5; Auto.
Elim (le_lt_eq_dec (minus N k) i); Try Intro y. Auto. Rewrite y in Hreck.
Apply mult_cancel_lft with (nth_coeff m p). Auto. Stepr (Zero::F).
Apply eq_transitive_unfolded with (Sum (0) (plus m i)
  [j:nat](nth_coeff j p)[*](nth_coeff (minus (plus m i) j) q)).
Pattern 1 i. Replace i with (minus (plus m i) m).
Apply eq_symmetric_unfolded.
Apply Sum_term with f :=
 [j:nat](nth_coeff j p)[*](nth_coeff (minus (plus m i) j) q).
Auto with arith. Auto with arith.
Intros. Elim (le_lt_dec j m); Intros.
Cut (lt i (minus (plus m i) j)). Intro.
Cut (lt n (minus (plus m i) j)). Intro.
Step_final (nth_coeff j p)[*]Zero.
Omega. Omega.
Step_final Zero[*](nth_coeff (minus (plus m i) j) q).
Auto with arith.
Step (nth_coeff (plus m i) p[*]q).
Cut (lt (plus m n) (plus m i)). Intro.
Auto.
Auto with arith.
Omega. 
Qed.

(* Begin_Tex_Verb *)
Lemma degree_mult_imp : (p,q:FX)(m,n:nat)
  (degree m p) -> (degree (plus m n) p[*]q) -> (degree n q).
(* End_Tex_Verb *)
Unfold degree. Intros.
Elim H. Clear H. Intros H H1. 
Elim H0. Clear H0. Intros H0 H2. 
Cut (degree_le n q). Intro H3. Split.
Apply mult_cancel_ap_zero_rht with (nth_coeff m p).
Step (nth_coeff (plus m n) p[*]q). 
Assumption.
Apply degree_le_mult_imp with m p; Auto.
Unfold degree. Split. Auto.
Assumption.
Qed.

End degree_props_Field.
