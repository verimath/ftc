(* $Id: OddPolyRootIR.v,v 1.8 2003/03/11 13:36:18 lcf Exp $ *)

Require Export IVT.

(* Tex_Prose
\chapter{Roots of polynomials of odd degree}
*)

Section CPoly_Big.

(* Tex_Prose
\section{Monic polys are positive near infinity}
\begin{convention}
Let \verb!R! be an ordered field.
\end{convention}
*)

Variable R : COrdField.

(* Begin_Tex_Verb *)
Lemma Cbigger : (x,y:R) { z:R & (x[<]z) & (y [<] z) }.
(* End_Tex_Verb *)
Intros.
Elim (cotrans_less_unfolded ? x x[+]One (less_plusOne ? ?) y); Intro.
Exists y[+]One. 
Apply less_leEq_trans with y. Auto. Apply less_leEq; Apply less_plusOne.
Apply less_plusOne.
Exists x[+]One.
Apply less_plusOne.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_big :
  (p:(cpoly R))(n:nat)(lt (0) n) -> (monic n p) ->
    (Y:R){X:R & (x:R)(X [<] x) -> (Y [<] p!x)}.
(* End_Tex_Verb *)
Intro. Elim p.
Unfold monic. Simpl. Intros. Elim H0. Intros H1 H2.
Cut (Zero [~=] (One::R)). Intro. Elim (H3 H1).
Apply ap_imp_neq. Apply ap_symmetric_unfolded. Apply ring_non_triv.
Intros c q. Intros.
Elim (O_or_S n); Intro y. Elim y. Intro m. Intro y0.
Rewrite <- y0 in H1.
Elim (zerop m); Intro y1. Simpl.
Exists Y[-]c. Intros.
Rewrite y1 in H1.
Apply shift_less_plus'.
Cut q!x [=] One. Intro.
Stepr x[*]One. Stepr x. Auto.
Apply monic_one with c. Auto.
Cut (monic m q). Intro.
Elim (Cbigger Zero Y[-]c). Intro Y'. Intros H3 H4.
Elim (H m y1 H2 Y'). Intro X'. Intro H5.
Simpl.
Elim (Cbigger One X'). Intro X. Intros H6 H7.
Exists X. Intros.
Apply shift_less_plus'.
Apply less_leEq_trans with One[*]Y'.
Stepr Y'. Auto.
Apply less_leEq; Apply mult_resp_less_both; Auto.
Apply less_leEq. Apply pos_one.
Apply less_transitive_unfolded with X; Auto.
Apply less_leEq. Auto.
Change Y' [<] q!x.
Apply H5.
Apply less_transitive_unfolded with X; Auto.
Apply monic_cpoly_linear with c; Auto.
Rewrite <- y in H0.
Elim (lt_n_n ? H0).
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_pos :
  (p:(cpoly R))(n:nat)(lt (0) n) -> (monic n p) -> { x:R & Zero [<] p!x}.
(* End_Tex_Verb *)
Intros.
Elim (Ccpoly_big ? ? H H0 Zero). Intros x H1.
Exists x[+]One.
Apply H1. Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_pos' : 
 (p:(cpoly R))(a:R)(n:nat)(lt (0) n) -> (monic n p) ->
    {x:R & (a [<] x) & (Zero [<] p!x)}.
(* End_Tex_Verb *)
Intros.
Elim (Ccpoly_big ? ? H H0 Zero). Intro x'. Intro H1.
Elim (Cbigger a x'). Intro x. Intros.
Exists x; Auto.
Qed.


End CPoly_Big.


Section Flip_Poly.
(* Tex_Prose
\section{Flipping a polynomial}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)

Variable R : CRing.

(* Begin_Tex_Verb *)
Fixpoint flip [p:(cpoly R)] : (cpoly R) :=
  Cases p of
    cpoly_zero => (cpoly_zero ?)
  | (cpoly_linear c q) => (cpoly_inv ? (cpoly_linear ? c (flip q)))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma flip_poly : (p:(cpoly R))(x:R)((flip p)!x [=] [--](p!([--]x))).
(* End_Tex_Verb *)
Intro p. Elim p.
Intros. Simpl. Algebra.
Intros c q. Intros.
Change  [--]c[+]x[*]((cpoly_inv ? (flip q)) ! x)
    [=] [--](c[+][--]x[*](q !([--]x))).
Step [--]c[+]x[*][--]((flip q)!x).
Step [--]c[+]x[*]([--][--](q!([--]x))).
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma flip_coefficient :
  (p:(cpoly R))(i:nat)
    ((nth_coeff i (flip p)) [=] [--](([--]One)[^]i)[*](nth_coeff i p)).
(* End_Tex_Verb *)
Intro p. Elim p.
Simpl. Algebra.
Intros c q. Intros.
Elim i. Simpl. Rational.
Intros. Simpl.
Step [--](nth_coeff n (flip q)).
Step [--]([--](([--]One)[^]n)[*](nth_coeff n q)).
Simpl. Rational.
Qed.

Hints Resolve flip_coefficient : algebra.

(* Begin_Tex_Verb *)
Lemma flip_odd :
  (p:(cpoly R))(n:nat)(odd n) -> (monic n p) -> (monic n (flip p)).
(* End_Tex_Verb *)
Unfold monic. Unfold degree_le.
Intros.
Elim H0. Clear H0. Intros.
Split.
Step [--](([--]One)[^]n)[*](nth_coeff n p).
Step ([--][--]One[^]n)[*](nth_coeff n p).
Step One[^]n[*](nth_coeff n p).
Step One[*](nth_coeff n p).
Step_final One[*](One::R).
Intros.
Step [--](([--]One)[^]m)[*](nth_coeff m p).
Step_final [--](([--]One)[^]m)[*](Zero::R).
Qed.

End Flip_Poly.

Hints Resolve flip_poly : algebra.


Section OddPoly_Signs.
(* Tex_Prose
\section{Sign of a polynomial of odd degree}
\begin{convention}
Let \verb!R! be an ordered field.
\end{convention}
*)

Variable R : COrdField.

(* Begin_Tex_Verb *)
Lemma oddpoly_pos :
  (p:(cpoly R))(n:nat)(odd n) -> (monic n p) -> {x:R & Zero [<] p!x}.
(* End_Tex_Verb *)
Intros.
Apply cpoly_pos with n; Auto.
Elim H. Intros. Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma oddpoly_pos' :
  (p:(cpoly R))(a:R)(n:nat)(odd n) -> (monic n p) ->
    {x:R & (a [<] x) & (Zero [<] p!x)}.
(* End_Tex_Verb *)
Intros.
Elim (Ccpoly_pos' ? p a n). Intros x H1 H2.
Exists x; Assumption.
Elim H; Auto with arith.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma oddpoly_neg :
  (p:(cpoly R))(n:nat)(odd n) -> (monic n p) -> {x:R & p!x [<] Zero}.
(* End_Tex_Verb *)
Intros.
Elim (oddpoly_pos ? ? H (flip_odd ? ? ? H H0)). Intro x. Intros.
Exists [--]x.
Step [--][--](p!([--]x)). Stepr [--](Zero::R).
Apply inv_resp_less.
Stepr (flip ? p)!x. Auto.
Qed.

End OddPoly_Signs.


Section Poly_Norm.

(* Tex_Prose
\section{The norm of a polynomial}
\begin{convention}
Let \verb!R! be a field, and \verb!RX! the polynomials over this field.
\end{convention}
*)

Variable R : CField.
Local RX := (cpoly_cring R).

(* Begin_Tex_Verb *)
Lemma poly_norm_aux :
  (p:RX; n:nat; H:(degree n p))
    (nth_coeff n p) [#] Zero.
(* End_Tex_Verb *)
Unfold degree. Intros.
Elim H. Auto.
Qed.

(* Begin_Tex_Verb *)
Definition poly_norm :=
  [p:RX; n:nat; H:(degree n p)]
    (_C_ (One[/](nth_coeff n p)[//](poly_norm_aux p n H)))[*]p.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma poly_norm_monic :
  (p:RX; n:nat; H:(degree n p))
    (monic n (poly_norm p n H)).
(* End_Tex_Verb *)
Unfold poly_norm. Unfold monic. Unfold degree. Unfold degree_le. Intros.
Elim H. Intros H0 H1. 
Split.
Step_final (One[/](nth_coeff n p)[//](poly_norm_aux p n (conjl ?? H0 H1)))[*](nth_coeff n p).
Intros.
Step (One[/](nth_coeff n p)[//](poly_norm_aux p n (conjl ?? H0 H1)))[*](nth_coeff m p).
Step_final (One[/](nth_coeff n p)[//](poly_norm_aux p n H))[*]Zero.
Qed.

(* Begin_Tex_Verb *)
Lemma poly_norm_apply :
  (p:RX; n:nat; H:(degree n p))
    (x:R)((poly_norm p n H)!x [=] Zero) -> (p!x [=] Zero).
(* End_Tex_Verb *)
Unfold poly_norm. Intros.
Apply mult_cancel_lft with (One[/](nth_coeff n p)[//](poly_norm_aux p n H)).
Apply div_resp_ap_zero_rev. Apply ring_non_triv.
Step (_C_ One[/](nth_coeff n p)[//](poly_norm_aux p n H))!x[*]p!x.
Step ((_C_ (One[/](nth_coeff n p)[//](poly_norm_aux p n H)))[*]p)!x.
Step_final (Zero::R).
Qed.

End Poly_Norm.


Section OddPoly_Root.
(* Tex_Prose
\section{Roots of polynomials of odd degree}
*)

(* Begin_Tex_Verb *)
Lemma oddpoly_root' :
  (f:(cpoly IR))(n:nat)(odd n) -> (monic n f) -> {x:IR | f!x [=] Zero}.
(* End_Tex_Verb *)
Intros.
Elim (oddpoly_neg ? f n); Auto. Intro a. Intro H1.
Elim (oddpoly_pos' ? f a n); Auto. Intro b. Intros H2 H3.
Cut {x:IR | (a [<=] x) /\ ((x [<=] b) /\ (f!x [=] Zero))}.
Intro H4.
Elim H4. Clear H4. Intros x H4.
Elim H4. Clear H4. Intros H4 H5. 
Elim H5. Clear H5. Intros.
Exists x. Auto.
Apply Civt_poly; Auto. 
Apply monic_apzero with n; Auto.
Simpl. Apply less_leEq. Auto.
Simpl. Apply less_leEq. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma oddpoly_root :
  (f:(cpoly IR))(n: nat)(odd n) -> (degree n f) -> {x:IR | f!x [=] Zero}.
(* End_Tex_Verb *)
Intros.
Elim (oddpoly_root' (poly_norm ? f n H0) n); Auto.
Intros. Exists x.
Apply poly_norm_apply with n H0; Auto.
Apply poly_norm_monic; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma realpolyn_oddhaszero :
  (f:(cpoly_cring IR))(odd_cpoly ? f) -> {x:IR | f!x [=] Zero}.
(* End_Tex_Verb *)
Unfold odd_cpoly.
Intros.
Elim H. Clear H. Intro n. Intros H H0.
Cut (odd n).
Intro.
Elim (oddpoly_root f n H1 H0). Intros. Exists x. Auto.
Apply Codd_to.
Assumption.
Qed.

End OddPoly_Root.
