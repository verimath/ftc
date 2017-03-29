(* $Id: CPoly_NthCoeff.v,v 1.9 2003/03/11 13:35:52 lcf Exp $ *)

Require Export CPolynomials.

(* Tex_Prose
\chapter{Polynomials: NthCoeff}
\begin{convention}
Let \verb!R! be a ring and write \verb!RX! for the ring of polynomials
over \verb!R!.
\end{convention}
*)

Section NthCoeff_def.

Variable R: CRing.

Syntactic Definition RX := (cpoly_cring R).

(* Tex_Prose
The $n$-th coefficient of a polynomial. The default value is \verb!Zero::CR!
e.g.\ if the $n$ is higher than the length. For the polynomial
$a_0 +a_1 X +a_2 X^2 + \cdots + a_n X^n$, the $0$-th coefficient is $a_0$,
the $1$-th is $a_1$ etcetera.
*)

(* Begin_Tex_Verb *)
Fixpoint nth_coeff [n:nat; p:RX] : R :=
  Cases p of
    cpoly_zero => Zero
  | (cpoly_linear c q) =>
      Cases n of
        O => c
      | (S m) => (nth_coeff m q)
      end
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma nth_coeff_strext : (n:nat)(p,p':RX)
               ((nth_coeff n p)[#](nth_coeff n p')) -> p[#]p'.
(* End_Tex_Verb *)
Do 3 Intro.
Generalize n.
Clear n.
Pattern p p'.
Apply Ccpoly_double_sym_ind.
Unfold Csymmetric.
Intros.
Apply ap_symmetric_unfolded.
Apply H with n.
Apply ap_symmetric_unfolded.
Assumption.
Intro.
Pattern p0.
Apply Ccpoly_induc.
Simpl.
Intros.
Elim (ap_irreflexive_unfolded ? ? H).
Do 4 Intro.
Elim n.
Simpl.
Auto.
Intros.
Cut (c[#]Zero)+(p1[#]Zero).
Intro; Apply _linear_ap_zero.
Auto.
Right.
Apply H with n0.
Stepr (Zero::R).
Intros.
Induction n.
Simpl in H0.
Cut (c[#]d)+(p0[#]q).
Auto.
Auto.
Cut (c[#]d)+(p0[#]q).
Auto.
Right.
Apply H with n.
Exact H0.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_wd : (n:nat)(p,p':RX)
  (p [=] p') -> ((nth_coeff n p) [=] (nth_coeff n p')).
(* End_Tex_Verb *)
Intros.
Generalize (fun_strong_ext_imp_well_def ? ? (nth_coeff n)); Intro.
Unfold fun_well_def in H0.
Apply H0.
Unfold fun_strong_ext.
Intros.
Apply nth_coeff_strext with n.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition nth_coeff_fun[n:nat] :=
  (Build_CSetoid_fun ? ? ? (nth_coeff_strext n)).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{shortcoming}
We would like to use \verb!nth_coeff_fun n! all the time.
However, Coq's coercion mechanism doesn't support this properly:
the term
\verb!(nth_coeff_fun n p)! won't get parsed, and has to be written as
\verb!((nth_coeff_fun n) p)! instead.

So, in the names of lemmas, we write \verb!(nth_coeff n p)!,
which always (e.g.\ in proofs) can be converted
to \verb!((nth_coeff_fun n) p)!.
\end{shortcoming}
*)

(* Begin_Tex_Verb *)
Definition nonConst [p:RX]: CProp :=
   {n:nat | (lt O n) & ((nth_coeff n p) [#] Zero)}.
(* End_Tex_Verb *)

(* Tex_Prose
The following is probably NOT needed.  These functions are NOT extensional, that is, they are not SETOID functions.
*)

(* Begin_Tex_Verb *)
Fixpoint nth_coeff_ok [n:nat; p:RX] : bool :=
  Cases n p of
     O cpoly_zero => false
  |  O (cpoly_linear c q) => true
  | (S m) cpoly_zero => false
  | (S m) (cpoly_linear c q) => (nth_coeff_ok m q)
  end.
(* End_Tex_Verb *)

(* The in_coeff predicate*)
(* Begin_Tex_Verb *)
Fixpoint in_coeff  [c:R;p:RX] : Prop :=
      Cases p of
	  cpoly_zero => False
	| (cpoly_linear d q) => (c [=] d) \/ (in_coeff c q)
      end.
(* End_Tex_Verb *)

(* Tex_Prose
The \verb!cpoly_zero! case should be (c [=] Zero) in order to be extensional.
*)

(* Begin_Tex_Verb *)
Lemma nth_coeff_S :
 (m:nat)(p:RX)(c:R)(in_coeff (nth_coeff m p) p)
   ->(in_coeff (nth_coeff (S m) (c [+X*] p)) (c [+X*] p)).
(* End_Tex_Verb *)
Simpl; Auto.
Qed.

End NthCoeff_def.

(* Tex_Prose
\begin{notation}
\verb!(nth_coeff ?)! is denoted as \hypertarget{Syntactic_25}{}\verb!Nth_coeff!, 
and \verb!(nth_coeff_fun ?)! as \hypertarget{Syntactic_26}{}\verb!Nth_coeff_fun!.
\end{notation}
*)

Implicits nth_coeff [1].
Implicits nth_coeff_fun [1].

Hints Resolve nth_coeff_wd : algebra_c.

Section NthCoeff_props.

Variable R: CRing.

Syntactic Definition RX := (cpoly_cring R).

(* Begin_Tex_Verb *)
Lemma nth_coeff_zero : (n:nat)(nth_coeff n (Zero::RX))[=]Zero.
(* End_Tex_Verb *)
Intros.
Simpl.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma coeff_O_lin : (p:RX)(c:R)(nth_coeff (0) (c[+X*]p)) [=]c.
(* End_Tex_Verb *)
Intros.
Simpl.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma coeff_Sm_lin : (p:RX)(c:R)(m:nat)
                     (nth_coeff (S m) (c[+X*]p)) [=] (nth_coeff m p).
(* End_Tex_Verb *)
Intros.
Simpl.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma coeff_O_c_ : (c:R)(nth_coeff (0) (_C_ c))[=]c.
(* End_Tex_Verb *)
Intros.
Simpl.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma coeff_O_x_mult : (p:RX)(nth_coeff (0) (_X_ [*] p)) [=] Zero.
(* End_Tex_Verb *)
Intros.
Step (nth_coeff (0) (Zero [+] _X_ [*] p)).
Step (nth_coeff (0) ((_C_ Zero) [+] _X_ [*] p)).
Step (nth_coeff (0) (Zero [+X*] p)).
Simpl.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma coeff_Sm_x_mult : (p:RX)(m:nat)
             (nth_coeff (S m) (_X_ [*] p)) [=] (nth_coeff m p).
(* End_Tex_Verb *)
Intros.
Step (nth_coeff (S m) (Zero [+] _X_ [*] p)).
Step (nth_coeff (S m) ((_C_ Zero) [+] _X_ [*] p)).
Step (nth_coeff (S m) (Zero [+X*] p)).
Simpl.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma coeff_Sm_mult_x_ : (p:RX)(m:nat)
             (nth_coeff (S m) (p [*] _X_)) [=] (nth_coeff m p).
(* End_Tex_Verb *)
Intros.
Step (nth_coeff (S m) (_X_ [*] p)).
Apply coeff_Sm_x_mult.
Qed.

Hints Resolve nth_coeff_zero coeff_O_lin coeff_Sm_lin
   coeff_O_c_ coeff_O_x_mult coeff_Sm_x_mult coeff_Sm_mult_x_ : algebra.

(* Begin_Tex_Verb *)
Lemma nth_coeff_ap_zero_imp : (p:RX)(n:nat)
                             ((nth_coeff n p) [#] Zero) -> (p [#] Zero).
(* End_Tex_Verb *)
Intros.
Cut (nth_coeff n p)[#](nth_coeff n Zero).
Intro.
Apply (nth_coeff_strext ? ? ? ? H0).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_plus : (p,q:RX)(n:nat)
  (nth_coeff n (p[+]q)) [=] (nth_coeff n p)[+](nth_coeff n q).
(* End_Tex_Verb *)
Do 2 Intro.
Pattern p q.
Apply poly_double_comp_ind.
Intros.
Step (nth_coeff n (p1[+]q1)).
Stepr (nth_coeff n p1)[+](nth_coeff n q1).
Apply H1.
Intros.
Simpl.
Algebra.
Intros.
Elim n.
Simpl.
Algebra.
Intros.
Step (nth_coeff n0 (p0[+]q0)).
Generalize (H n0); Intro.
Step (nth_coeff n0 p0)[+](nth_coeff n0 q0).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_inv : (p:RX)(n:nat)
  (nth_coeff n ([--]p)) [=] [--](nth_coeff n p).
(* End_Tex_Verb *)
Intro.
Pattern p.
Apply cpoly_induc.
Intros.
Simpl.
Algebra.
Intros.
Elim n.
Simpl.
Algebra.
Intros. Simpl.
Apply H.
Qed.

Hints Resolve nth_coeff_inv : algebra.

(* Begin_Tex_Verb *)
Lemma nth_coeff_c_mult_p : (p:RX)(c:R)(n:nat)
  ((nth_coeff n (_C_ c)[*]p) [=] c[*](nth_coeff n p)).
(* End_Tex_Verb *)
Do 2 Intro.
Pattern p.
Apply cpoly_induc.
Intros.
Step (nth_coeff n (Zero::RX)).
Stepr c[*]Zero.
Step (Zero::R).
Algebra.
Intros.
Elim n.
Simpl.
Algebra.
Intros.
Step (nth_coeff (S n0) (c[*]c0 [+X*] ((_C_ c)[*]p0))).
Step (nth_coeff n0 ((_C_ c)[*]p0)).
Step c[*](nth_coeff n0 p0).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_p_mult_c_ : (p:RX)(c:R)(n:nat)
  ((nth_coeff n p[*](_C_ c)) [=] (nth_coeff n p)[*]c).
(* End_Tex_Verb *)
Intros.
Step (nth_coeff n (_C_ c)[*]p).
Stepr c[*](nth_coeff n p).
Apply nth_coeff_c_mult_p.
Qed.

Hints Resolve nth_coeff_c_mult_p nth_coeff_p_mult_c_ nth_coeff_plus : algebra.

(* Begin_Tex_Verb *)
Lemma nth_coeff_complicated : (a,b:R)(p:RX)(n:nat)
  (nth_coeff (S n) ((_C_ a)[*]_X_[+](_C_ b))[*]p) [=]
    a[*](nth_coeff n p)[+]b[*](nth_coeff (S n) p).
(* End_Tex_Verb *)
Intros.
Step (nth_coeff (S n) (((_C_ a)[*]_X_)[*]p [+](_C_ b)[*]p)).
Step (nth_coeff (S n) ((_C_ a)[*]_X_[*]p)) [+]
         (nth_coeff (S n) (_C_ b)[*]p).
Step (nth_coeff (S n) ((_C_ a)[*](_X_[*]p))) [+]
         b[*](nth_coeff (S n) p).
Step a[*](nth_coeff (S n) (_X_[*]p)) [+]
         b[*](nth_coeff (S n) p).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma all_nth_coeff_eq_imp : (p,p':RX)
  ((i:nat)((nth_coeff i p) [=] (nth_coeff i p'))) -> (p [=] p').
(* End_Tex_Verb *)
Intro. Induction p; Intros; Induction p'; Intros.
Algebra.
Simpl. Simpl in H. Simpl in Hrecp'. Split.
Apply eq_symmetric_unfolded. Apply (H (0)). Apply Hrecp'.
Intros. Apply (H (S i)).
Simpl. Simpl in H. Simpl in Hrecp. Split.
Apply (H (0)).
Change Zero [=] (p::RX). Apply eq_symmetric_unfolded. Simpl. Apply Hrecp.
Intros. Apply (H (S i)).
Simpl. Simpl in H. Split.
Apply (H (0)).
Change (p::RX) [=] (p'::RX). Apply Hrecp. Intros. Apply (H (S i)).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_at_zero : (p:RX)(p!Zero [=] (nth_coeff O p)).
(* End_Tex_Verb *)
Intros. Induction p; Intros.
Simpl. Algebra.
Simpl. Step_final s[+]Zero.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_inv' :
  (p:(cpoly R))(i:nat)(nth_coeff i (cpoly_inv ? p)) [=] [--](nth_coeff i p).
(* End_Tex_Verb *)
Intros. Change (nth_coeff i [--](p::RX)) [=] [--](nth_coeff i p). Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_minus :
  (p,q:RX)(i:nat)(nth_coeff i p[-]q) [=] (nth_coeff i p)[-](nth_coeff i q).
(* End_Tex_Verb *)
Intros.
Step (nth_coeff i p[+][--]q).
Step (nth_coeff i p)[+](nth_coeff i [--]q).
Step_final (nth_coeff i p)[+][--](nth_coeff i q).
Qed.

Hints Resolve nth_coeff_minus : algebra.

(* Begin_Tex_Verb *)
Lemma nth_coeff_sum0 :
  (p_:nat->RX)(k,n:nat)
    (nth_coeff k (Sum0 n p_)) [=] (Sum0 n [i:nat](nth_coeff k (p_ i))).
(* End_Tex_Verb *)
Intros. Induction n; Intros.
Simpl. Algebra.
Change (nth_coeff k (Sum0 n p_)[+](p_ n)) [=]
  (Sum0 n [i:nat](nth_coeff k (p_ i)))[+](nth_coeff k (p_ n)).
Step_final (nth_coeff k (Sum0 n p_))[+](nth_coeff k (p_ n)).
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_sum :
  (p_:nat->RX)(k,m,n:nat)
    (nth_coeff k (Sum m n p_)) [=] (Sum m n [i:nat](nth_coeff k (p_ i))).
(* End_Tex_Verb *)
Unfold Sum. Unfold Sum1. Intros.
Step (nth_coeff k (Sum0 (S n) p_))[-](nth_coeff k (Sum0 m p_)).
Apply cg_minus_wd; Apply nth_coeff_sum0.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_nexp_eq :
   (i:nat)(nth_coeff i (_X_ [^]i)) [=] (One::R).
(* End_Tex_Verb *)
Intros. Induction i; Intros.
Simpl. Algebra.
Change (nth_coeff (S i) _X_[^]i[*]_X_) [=] (One::R).
Step_final ((nth_coeff i _X_[^]i)::R).
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_nexp_neq :
   (i,j:nat)~(i=j)->(nth_coeff i (_X_[^]j)) [=] (Zero::R).
(* End_Tex_Verb *)
Intro; Induction i; Intros; Induction j; Intros.
Elim (H (refl_equal ? ?)).
Step_final ((nth_coeff (0) _X_[*]_X_[^]j)::R).
Simpl. Algebra.
Change (nth_coeff (S i) _X_[^]j[*]_X_) [=] (Zero::R).
Step ((nth_coeff i _X_[^]j)::R).
Apply Hreci. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nth_coeff_mult :
  (p,q:RX)(n:nat)(nth_coeff n p[*]q) [=]
    (Sum (0) n [i:nat](nth_coeff i p)[*](nth_coeff (minus n i) q)).
(* End_Tex_Verb *)
Intro; Induction p. Intros.
Simpl. Apply eq_symmetric_unfolded.
Apply Sum_zero. Auto with arith. Intros. Algebra.
Intros.
Apply eq_transitive_unfolded with
  (nth_coeff n (_C_ s)[*]q[+]_X_[*]((p::RX)[*]q)).
Apply nth_coeff_wd.
Change (s[+X*]p)[*]q [=] (_C_ s)[*]q[+]_X_[*]((p::RX)[*]q).
Step ((_C_ s)[+]_X_[*]p)[*]q.
Step_final (_C_ s)[*]q[+]_X_[*]p[*]q.
Step (nth_coeff n (_C_ s)[*]q)[+](nth_coeff n _X_[*]((p::RX)[*]q)).
Step s[*](nth_coeff n q)[+](nth_coeff n _X_[*]((p::RX)[*]q)).
Induction n; Intros.
Step s[*](nth_coeff (0) q)[+]Zero.
Step s[*](nth_coeff (0) q).
Step (nth_coeff (0) (cpoly_linear ? s p))[*](nth_coeff (0) q).
Pattern 2 (0). Replace (0) with (minus (0) (0)).
Apply eq_symmetric_unfolded.
Apply Sum_one with f :=
  [i:nat](nth_coeff i (cpoly_linear ? s p))[*](nth_coeff (minus (0) i) q).
Auto.
Step s[*](nth_coeff (S n) q)[+](nth_coeff n (p::RX)[*]q).
Apply eq_transitive_unfolded with
  (nth_coeff (0) (cpoly_linear ? s p))[*](nth_coeff (minus (S n) (0)) q)[+]
  (Sum (1) (S n)
    [i:nat](nth_coeff i (cpoly_linear ? s p))[*](nth_coeff (minus (S n) i) q)).
Apply bin_op_wd_unfolded. Algebra.
Step (Sum (0) n [i:nat](nth_coeff i p)[*](nth_coeff (minus n i) q)).
Apply Sum_shift. Intros. Simpl. Algebra.
Apply eq_symmetric_unfolded.
Apply Sum_first with f :=
  [i:nat](nth_coeff i (cpoly_linear ? s p))[*](nth_coeff (minus (S n) i) q).
Qed.

End NthCoeff_props.

Hints Resolve nth_coeff_wd : algebra_c.
Hints Resolve nth_coeff_complicated poly_at_zero nth_coeff_inv : algebra.
Hints Resolve nth_coeff_inv' nth_coeff_c_mult_p nth_coeff_mult : algebra.
Hints Resolve nth_coeff_zero nth_coeff_plus nth_coeff_minus : algebra.
Hints Resolve nth_coeff_nexp_eq nth_coeff_nexp_neq : algebra.
