(* $Id: CRings.v,v 1.15 2003/03/13 12:06:15 lcf Exp $ *)

Require Export CSums.

Transparent sym_eq.
Transparent f_equal.

(* Begin_SpecReals *)

(* Constructive RINGS *)

(* Tex_Prose
\chapter{Rings}
We actually define commutative rings with 1.
*)

(* Tex_Prose
\section{Definition of the notion of Ring}
*)
(* Begin_Tex_Verb *)
Definition distributive :=
  [S:CSetoid; mult,plus:(CSetoid_bin_op S)]
  (x,y,z:S) (mult x (plus y z)) [=] (plus (mult x y) (mult x z)).
(* End_Tex_Verb *)

Implicits distributive [1].

(* Begin_Tex_Verb *)
Record is_CRing [G : CGroup; one : G; mult : (CSetoid_bin_op G)] : CProp :=
  { ax_mult_assoc : (associative mult);
    ax_mult_mon : (is_CMonoid (Build_CSemi_grp G one mult ax_mult_assoc));
    ax_dist : (distributive mult csg_op);
    ax_non_triv : (one [#] Zero)
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record CRing : Type :=
  { cr_crr   :> CGroup;
    cr_one   :  cr_crr;
    cr_mult  :  (CSetoid_bin_op cr_crr);
    cr_proof :  (is_CRing cr_crr cr_one cr_mult)
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition cr_plus  :=  !csg_op.
Definition cr_inv   :=  !cg_inv.
Definition cr_minus :=  !cg_minus.
(* End_Tex_Verb *)


(* Tex_Prose
\begin{notation}
The term \verb!cr_one! with its first argument left implicit is denoted by
{\tt\hypertarget{Syntactic_10}{One}}.
\end{notation}
*)
Syntactic Definition One    := (cr_one ?).
Syntax constr level 1:
  cr_one_constant [(cr_one $e0)] -> ["One"].

(* End_SpecReals *)

(* Begin_SpecReals *)

(* Tex_Prose
\begin{notation}
The multiplication \verb!(cr_mult x y)! is denoted by {\tt\hypertarget{Operator_15}{x [*] y}}.
\end{notation}

\begin{nameconvention}
In the {\em names} of lemmas, we will denote \verb!One! with \verb!one!,
and \verb![*]! with \verb!mult!.
\end{nameconvention}
*)

Implicits cr_mult [1].
Infix 6 "[*]" cr_mult.

Section CRing_axioms.
(* Tex_Prose
\section{Ring axioms}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Variable R : CRing.

(* Begin_Tex_Verb *)
Lemma CRing_is_CRing : (is_CRing R One cr_mult).
(* End_Tex_Verb *)
Elim R; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_assoc : (associative (!cr_mult R)).
(* End_Tex_Verb *)
Elim CRing_is_CRing; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_mon : (is_CMonoid (Build_CSemi_grp R One cr_mult mult_assoc)).
(* End_Tex_Verb *)
Elim (cr_proof R).
Intros H1 H2 H3 H4.
Apply is_CMonoid_proof_irr with H1.
Assumption.
Qed.

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma dist : (!distributive R cr_mult (cr_plus R)).
(* End_Tex_Verb *)
Elim (cr_proof R); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma ring_non_triv : ((One::R) [#] Zero).
(* End_Tex_Verb *)
Elim (cr_proof R); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_wd : (x1,x2,y1,y2:R)(x1[=]x2)-> (y1[=]y2)-> (x1[*]y1) [=] (x2[*]y2).
(* End_Tex_Verb *)
Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_wd_lft : (x1,x2,y:R)(x1[=]x2)-> (x1[*]y) [=] (x2[*]y).
(* End_Tex_Verb *)
Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_wd_rht : (x,y1,y2:R)(y1[=]y2)-> (x[*]y1) [=] (x[*]y2).
(* End_Tex_Verb *)
Intros; Algebra.
Qed.

(* Begin_SpecReals *)

End CRing_axioms.

Section Ring_constructions.
(* Tex_Prose
\section{Ring constructions}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Variable R : CRing.

(* Tex_Prose
The multiplicative monoid of a ring is defined as follows.
*)
(* Begin_Tex_Verb *)
Definition Build_multCMonoid : CMonoid := (Build_CMonoid ? (mult_mon R)).
(* End_Tex_Verb *)

End Ring_constructions.

(* End_SpecReals *)

(* Begin_SpecReals *)

(* End_SpecReals *)

Section Ring_unfolded.
(* Tex_Prose
\section{Ring unfolded}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Variable R : CRing.
Local mmR := (Build_multCMonoid R).

(* Begin_Tex_Verb *)
Lemma mult_assoc_unfolded : (x,y,z:R)
                            (x [*] (y [*] z)) [=] ((x [*] y) [*] z).
(* End_Tex_Verb *)
Proof (mult_assoc R).

(* Begin_Tex_Verb *)
Lemma mult_commutes: (x,y:R) (x[*]y) [=] (y[*]x).
(* End_Tex_Verb *)
Proof (cm_commutes mmR).
Hints Resolve mult_commutes : algebra.

(* Begin_Tex_Verb *)
Lemma mult_one: (x:R)(x [*] One) [=] x.
(* End_Tex_Verb *)
Proof (cm_rht_unit mmR).

(* Begin_Tex_Verb *)
Lemma one_mult: (x:R)(One [*] x) [=] x.
(* End_Tex_Verb *)
Proof (cm_lft_unit mmR).

(* Begin_Tex_Verb *)
Lemma ring_dist_unfolded:
  (x,y,z:R) x [*] (y [+] z) [=] (x [*] y) [+] (x [*] z).
(* End_Tex_Verb *)
Proof (dist R).
Hints Resolve ring_dist_unfolded : algebra.

(* Begin_Tex_Verb *)
Lemma ring_distl_unfolded:
  (x,y,z:R) (y [+] z) [*] x [=] (y [*] x) [+] (z [*] x).
(* End_Tex_Verb *)
Intros x y z.
Step x [*] (y [+] z).
Step (x [*] y) [+] (x [*] z).
Step (y [*] x) [+] (x [*] z).
Step_final (y [*] x) [+] (z [*] x).
Qed.

End Ring_unfolded.
Hints Resolve mult_assoc_unfolded : algebra.
Hints Resolve ring_non_triv mult_one one_mult mult_commutes : algebra.
Hints Resolve ring_dist_unfolded ring_distl_unfolded : algebra.


Section Ring_basics.
(* Tex_Prose
\section{Ring basics}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Variable R : CRing.

(* Begin_Tex_Verb *)
Lemma one_ap_zero : ((One::R) [#] Zero).
(* End_Tex_Verb *)
Proof (ring_non_triv R).

(* Begin_Tex_Verb *)
Definition is_zero_rht [S:CSetoid; op:(CSetoid_bin_op S); zero:S]: Prop :=
    (x:S)((op x zero) [=] zero).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition is_zero_lft [S:CSetoid; op:(CSetoid_bin_op S); zero:S]: Prop :=
    (x:S)((op zero x) [=] zero).
(* End_Tex_Verb *)

Implicits is_zero_rht [1].
Implicits is_zero_lft [1].

(* Begin_Tex_Verb *)
Lemma cring_mult_zero: (x:R) (x [*] Zero) [=] Zero.
(* End_Tex_Verb *)
Intro x.
Apply cg_cancel_lft with (x [*] Zero).
Stepr x[*]Zero.
Step_final x[*](Zero[+]Zero).
Qed.
Hints Resolve cring_mult_zero : algebra.

(* Begin_Tex_Verb *)
Lemma x_mult_zero : (x,y:R)(y[=]Zero)->(x[*]y)[=]Zero.
(* End_Tex_Verb *)
Intros x y H; Step_final x[*]Zero.
Qed.

(* Begin_Tex_Verb *)
Lemma cring_mult_zero_op: (x:R) Zero[*]x [=] Zero.
(* End_Tex_Verb *)
Intro x; Step_final x[*]Zero.
Qed.
Hints Resolve cring_mult_zero_op : algebra.

(* Begin_Tex_Verb *)
Lemma cring_inv_mult_lft: (x,y:R) x [*] ([--]y) [=] [--](x [*] y).
(* End_Tex_Verb *)
Intros x y.
Apply cg_inv_unique.
Step x[*](y[+]([--]y)).
Step_final x[*]Zero.
Qed.
Hints Resolve cring_inv_mult_lft : algebra.

(* Begin_Tex_Verb *)
Lemma cring_inv_mult_rht: (x,y:R) ([--]x) [*] y [=] [--](x [*] y).
(* End_Tex_Verb *)
Intros x y.
Step y[*]([--]x).
Step_final [--](y[*]x).
Qed.
Hints Resolve cring_inv_mult_rht : algebra.

(* Begin_Tex_Verb *)
Lemma cring_mult_ap_zero: (x,y:R)((x [*] y) [#] Zero) -> (x [#] Zero).
(* End_Tex_Verb *)
Intros x y H.
Elim (bin_op_strext ? cr_mult x Zero y y).
  Auto.
 Intro contra; Elim (ap_irreflexive ? ? contra).
Stepr (Zero::R).
Qed.

(* Begin_Tex_Verb *)
Lemma cring_mult_ap_zero_op: (x,y:R)((x [*] y) [#] Zero) -> (y [#] Zero).
(* End_Tex_Verb *)
Intros x y H.
Apply cring_mult_ap_zero with x.
Step x[*]y.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_mult_invol: (x,y:R)([--]x[*][--]y [=] x[*]y).
(* End_Tex_Verb *)
Intros x y.
Step [--](x[*][--]y).
Step_final [--][--](x[*]y).
Qed.

(* Begin_Tex_Verb *)
Lemma ring_dist_minus :
  (x,y,z:R) x [*] (y [-] z) [=] (x [*] y) [-] (x [*] z).
(* End_Tex_Verb *)
Intros x y z.
Unfold cg_minus.
Step_final x[*]y [+] x[*][--]z.
Qed.

Hints Resolve ring_dist_minus : algebra.

(* Begin_Tex_Verb *)
Lemma ring_distl_minus:
  (x,y,z:R) (y [-] z) [*] x [=] (y [*] x) [-] (z [*] x).
(* End_Tex_Verb *)
Intros x y z.
Unfold cg_minus.
Step_final y[*]x [+] [--]z[*]x.
Qed.

Hints Resolve ring_distl_minus : algebra.

End Ring_basics.
Hints Resolve cring_mult_zero cring_mult_zero_op : algebra.
Hints Resolve inv_mult_invol : algebra.
Hints Resolve cring_inv_mult_lft cring_inv_mult_rht : algebra.
Hints Resolve ring_dist_minus : algebra.
Hints Resolve ring_distl_minus : algebra.

(* Begin_SpecReals *)

(* Tex_Prose
\section{Ring Auxiliary}
Some auxiliary functions and operations over a ring;
especially geared towards CReals.
*)

Section exponentiation.
(* Tex_Prose
\subsection{Exponentiation}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Variable R: CRing.

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Fixpoint nexp [m:nat]: R->R :=
  Cases m of O => [_:R] One | (S n) => [x:R]((nexp n x) [*] x)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma nexp_well_def: (n:nat)(fun_well_def (nexp n)).
(* End_Tex_Verb *)
Intro n; Induction n; Red; Intros; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_strong_ext: (n:nat)(fun_strong_ext (nexp n)).
(* End_Tex_Verb *)
Intro n; Red; Induction n; Simpl; Intros x y H.
 Elim (ap_irreflexive ? ? H).
Elim (bin_op_strext ? cr_mult ? ? ? ? H); Auto.
Qed.

(* Begin_Tex_Verb *)
Definition nexp_op :=
  [n:nat](Build_CSetoid_un_op R (nexp n)
    (nexp_strong_ext n)).
(* End_Tex_Verb *)

(* Begin_SpecReals *)

End exponentiation.

(* End_SpecReals *)

(* Tex_Prose
\begin{notation}
\hypertarget{Operator_14}{}\verb!a [^] b! stands for \verb!(nexp_op ? b a)!.
\end{notation}
*)

Notation "x [^] n" := (nexp_op ? n x).
Implicits nexp_op [1].
Syntax constr level 2:
  nexp_op_infix [((nexp_op $e1) $e2)] ->
    [[<hov 1> $e2:E [0 1] "[^]" $e1:L]].

(* Begin_SpecReals *)

Section nat_injection.
(* Tex_Prose
\subsection{The injection of natural numbers into a ring}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Variable R: CRing.

(* Tex_Prose
The injection of Coq natural numbers into a ring is called \verb!nring!.
*)
(* Begin_Tex_Verb *)
Fixpoint nring [m:nat]: R :=
  Cases m of O => Zero | (S n) => ((nring n) [+] One)
  end.
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma nring_comm_plus:
  (n,m:nat)(nring (plus n m)) [=] ((nring n) [+] (nring m)).
(* End_Tex_Verb *)
Intros n m; Induction n; Simpl.
 Algebra.
Stepr (nring n)[+](One[+](nring m)).
Stepr (nring n)[+]((nring m)[+]One).
Step_final ((nring n)[+](nring m))[+]One.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_comm_mult :
  (n,m:nat)(nring (mult n m)) [=] ((nring n) [*] (nring m)).
(* End_Tex_Verb *)
Intros n m; Induction n; Simpl.
 Algebra.
Apply eq_transitive_unfolded with (nring m)[+](nring (mult n m)). Apply (nring_comm_plus m (mult n m)).
Stepr ((nring n)[*](nring m)) [+] (One[*](nring m)).
Stepr ((nring n)[*](nring m)) [+] (nring m).
Step_final (nring m) [+] ((nring n)[*](nring m)).
Qed.

(* Begin_SpecReals *)

End nat_injection.

(* End_SpecReals *)

Hints Resolve nring_comm_plus nring_comm_mult : algebra.

(* Tex_Prose
\begin{notation}
{\tt\hypertarget{Syntactic_12}{Two}} denotes \verb!nring (S (S O))!,
{\tt\hypertarget{Syntactic_13}{Three}} denotes \verb!nring (S (S (S O)))! and
{\tt\hypertarget{Syntactic_14}{Four}} denotes \verb!nring (S (S (S (S O))))!.
\end{notation}
*)
(* Begin_SpecReals *)

Implicits nring [1].

(* End_SpecReals *)

Syntactic Definition Two    := (nring (S (S O))).
Syntax constr level 1:
  cr_two_constant [(nring (S (S O)))] -> ["Two"].


Syntactic Definition Three    := (nring (S (S (S O)))).
Syntax constr level 1:
  cr_three_constant [(nring (S (S (S O))))] -> ["Three"].

Syntactic Definition Four    := (nring (S (S (S (S O))))).
Syntax constr level 1:
  cr_four_constant [(nring (S (S (S (S O)))))] -> ["Four"].

(* Begin_Tex_Verb *)
Lemma one_plus_one : (R:CRing)(One [+] One) [=] (Two :: R).
(* End_Tex_Verb *)
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma x_plus_x : (R:CRing)(x:R)(x[+]x) [=] Two[*]x.
(* End_Tex_Verb *)
Intros R x.
Step (One[*]x)[+](One[*]x).
Step (One[+]One)[*]x.
Simpl; Algebra.
Qed.

Hints Resolve one_plus_one x_plus_x : algebra.

Section int_injection.

(* Tex_Prose
\subsection{The injection of integers into a ring}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)

Variable R: CRing.

(* Tex_Prose
The injection of Coq integers into a ring is called \verb!zring!.
*)
(* Begin_Tex_Verb *)
Definition zring [k:Z] : R := (caseZ_diff k [m,n:nat](nring m) [-] (nring n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma zring_zero : (zring `0`) [=] Zero.
(* End_Tex_Verb *)
Simpl; Algebra.
Qed.
Hints Resolve zring_zero : algebra.

(* Begin_Tex_Verb *)
Lemma zring_diff : (m,n:nat)(zring `m-n`) [=] (nring m) [-] (nring n).
(* End_Tex_Verb *)
Unfold zring.
Intros m n.
(* Rewrite with [=] *)
Apply proper_caseZ_diff_CS with f:=[m0,n0:nat](!nring R m0)[-](nring n0).
Clear m n.
Intros m n p q H.
Apply cg_cancel_lft with ((nring n)::R).
Unfold cg_minus.
Step (!nring R n)[+]([--](nring n)[+](nring m)).
Step ((!nring R n)[+][--](nring n))[+](nring m).
Step Zero[+](!nring R m).
Step (!nring R m).
Apply cg_cancel_rht with ((nring q)::R).
Stepr (!nring R n)[+](((nring p)[+][--](nring q))[+](nring q)).
Stepr (!nring R n)[+]((nring p)[+]([--](nring q)[+](nring q))).
Stepr (!nring R n)[+]((nring p)[+]Zero).
Stepr (!nring R n)[+](nring p).
Stepr (!nring R (plus n p)).
Step (!nring R (plus m q)).
Rewrite H.
Algebra.
Qed.

Hints Resolve zring_diff.

(* Begin_Tex_Verb *)
Lemma zring_plus_nat : (n:nat)(zring `n`) [=] (nring n).
(* End_Tex_Verb *)
Intro n.
Replace (`n`::Z) with `n-O`.
 Step (!nring R n) [-] (nring O).
 Simpl; Algebra.
Simpl; Auto with zarith.
Qed.

Hints Resolve zring_plus_nat : algebra.

(* Begin_Tex_Verb *)
Lemma zring_inv_nat : (n:nat)(zring `-n`) [=] [--](nring n).
(* End_Tex_Verb *)
Intro n.
Replace `-n` with `O-n`.
 Step (nring O) [-] (!nring R n).
 Simpl; Algebra.
Simpl; Auto.
Qed.

Hints Resolve zring_inv_nat : algebra.

(* Begin_Tex_Verb *)
Lemma zring_plus : (i,j:Z)(zring `i+j`) [=] (zring i)[+](zring j).
(* End_Tex_Verb *)
Intros i j.
Pattern i.
Apply diff_Z_ind.
Intros m n.
Pattern j.
Apply diff_Z_ind.
Intros m0 n0.
Hints Resolve zring_diff : algebra.
Replace `(m-n)+(m0-n0)` with `(plus m m0)-(plus n n0)`.
(* Rewrite using [=] would be great. *)
Step ((nring (plus m m0)) [-] (nring (plus n n0)) ::R).
Step (((nring m) [+] (nring m0)) [-] ((nring n) [+] (nring n0)) :: R).
Stepr (((nring m) [-] (nring n)) [+] ((nring m0) [-] (nring n0)) :: R).
Unfold cg_minus.
Step ((nring m) [+] ((nring m0) [+][--] ((nring n) [+] (nring n0))) :: R).
Stepr
  ((nring m) [+] ([--](nring n) [+] ((nring m0) [+][--] (nring n0))) ::R).
Apply bin_op_wd_unfolded.
 Algebra.
Step ((nring m0) [+]([--] (nring n) [+][--] (nring n0)) :: R).
Step (((nring m0) [+] [--] (nring n)) [+][--] (nring n0) :: R).
Step_final (([--](nring n) [+] (nring m0)) [+] [--](nring n0) :: R).

Repeat Rewrite inj_plus.
Auto with zarith.
Qed.

Hints Resolve zring_plus : algebra.

(* Begin_Tex_Verb *)
Lemma zring_inv : (i:Z)(zring `-i`) [=] [--](zring i).
(* End_Tex_Verb *)
Intro i.
Pattern i.
Apply diff_Z_ind.
Intros m n.
Replace `-(m-n)` with `n-m`.
Step (!nring R n) [-] (nring m).
Stepr [--]((!nring R m) [-] (nring n)).
Unfold cg_minus.
Stepr [--](nring m)[+][--][--](!nring R n).
Step_final [--](!nring R m)[+](nring n).

Auto with zarith.
Qed.

Hints Resolve zring_inv : algebra.

(* Begin_Tex_Verb *)
Lemma zring_minus : (i,j:Z)(zring `i-j`) [=] (zring i)[-](zring j).
(* End_Tex_Verb *)
Intros i j.
Unfold cg_minus.
Replace `i-j` with `i+(-j)`.
Step_final (zring `i`) [+] (zring `-j`).

Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma zring_mult : (i,j:Z)(zring `i*j`) [=] (zring i)[*](zring j).
(* End_Tex_Verb *)
Intros i j.
Pattern i.
Apply diff_Z_ind.
Intros m n.
Pattern j.
Apply diff_Z_ind.
Intros m0 n0.
Stepr ((!nring R m) [-] (nring n))[*]((nring m0) [-] (nring n0)).
Replace `(m-n)*(m0-n0)` with
        `(plus (mult m m0) (mult n n0)) - (plus (mult n m0) (mult m n0))`.
 2: Repeat Rewrite inj_plus.
 2: Repeat Rewrite inj_mult.
 2: Repeat Rewrite Zmult_minus_distr.
 2: Repeat Rewrite Zmult_minus_distr_r.
 2: Auto with zarith.
Step (!nring R (plus (mult m m0) (mult n n0))) [-]
         (nring (plus (mult n m0) (mult m n0))).
Step ((!nring R (mult m m0)) [+] (nring (mult n n0))) [-]
         ((nring (mult n m0)) [+] (nring (mult m n0))).
Step ((!nring R m) [*] (nring m0) [+] (nring n) [*] (nring n0)) [-]
         ((nring n) [*] (nring m0) [+] (nring m) [*] (nring n0)).
Stepr (!nring R m) [*] ((nring m0)[-](nring n0)) [-]
         (nring n) [*] ((nring m0)[-](nring n0)).
Stepr ((!nring R m) [*] (nring m0) [-] (nring m) [*] (nring n0)) [-]
         ((nring n) [*] (nring m0) [-] (nring n) [*] (nring n0)).
Unfold cg_minus.
Stepr (!nring R m)[*](nring m0)[+](([--]((nring m)[*](nring n0)))
            [+][--]((nring n)[*](nring m0)
                      [+][--]((nring n)[*](nring n0)))).
Step
 (!nring R m)[*](nring m0)[+](((nring n)[*](nring n0))
     [+][--]((nring n)[*](nring m0)[+](nring m)[*](nring n0))).
Apply bin_op_wd_unfolded.
 Algebra.
Step
 ((!nring R n)[*](nring n0))
   [+]([--]((nring n)[*](nring m0))[+]([--]((nring m)[*](nring n0)))).
Stepr ([--]((!nring R m)[*](nring n0)))
            [+]([--]((nring n)[*](nring m0))
                      [+][--][--]((nring n)[*](nring n0))).
Stepr ([--]((!nring R m)[*](nring n0)))
            [+]([--]((nring n)[*](nring m0))
                      [+]((nring n)[*](nring n0))).
Stepr ([--]((!nring R m)[*](nring n0)))
            [+](   ((nring n)[*](nring n0))
                [+]  [--]((nring n)[*](nring m0))   ).
Stepr ([--]((!nring R m)[*](nring n0)))
            [+]   ((nring n)[*](nring n0))
                [+]  [--]((nring n)[*](nring m0))   .
Stepr  ((!nring R n)[*](nring n0))
            [+]   ([--]((nring m)[*](nring n0)))
                [+]  [--]((nring n)[*](nring m0))   .
Step_final  ((!nring R n)[*](nring n0))
            [+] (  ([--]((nring m)[*](nring n0)))
                [+]  [--]((nring n)[*](nring m0))   ).
Qed.

Hints Resolve zring_mult : algebra.

(* Begin_Tex_Verb *)
Lemma zring_one : (zring `1`) [=] One.
(* End_Tex_Verb *)
Simpl.
Step_final (One[-]Zero :: R).
Qed.

Hints Resolve zring_one : algebra.

(* Begin_Tex_Verb *)
Lemma zring_inv_one : (x:R)((zring `-1`)[*]x [=] [--]x).
(* End_Tex_Verb *)
Intro x.
Simpl.
Step [--](Zero[+]One)[*]x.
Step ([--]One)[*]x.
Step_final [--](One[*]x).
Qed.

End int_injection.

Implicits zring [1].

Hints Resolve zring_zero zring_diff zring_plus_nat zring_inv_nat
              zring_plus zring_inv zring_minus zring_mult
              zring_one zring_inv_one : algebra.


Section Ring_sums.

(* Tex_Prose
\section{Ring sums}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Variable R : CRing.

(* Tex_Prose
\subsection{Infinite Ring sums}
*)
Section infinite_ring_sums.

(* Begin_Tex_Verb *)
Fixpoint Sum_upto [f:nat->R; n:nat] : R :=
  Cases n of O     => Zero
	   | (S x) => (f x) [+] (Sum_upto f x)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma sum_upto_O : (f:nat->R)(Sum_upto f O) [=] Zero.
(* End_Tex_Verb *)
Algebra.
Qed.

(* Begin_Tex_Verb *)
Definition Sum_from_upto [f:nat->R; m,n:nat] : R :=
  (Sum_upto f n) [-] (Sum_upto f m).
(* End_Tex_Verb *)

(* Tex_Prose
Here's an alternative def of \verb!Sum_from_upto!, with lemma that
it's equivalent to the original.
*)
(* Begin_Tex_Verb *)
Definition seq_from [f:nat->R; n:nat] : nat->R := [i:nat](f (plus n i)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Sum_from_upto_alt [f:nat->R; m,n:nat] : R :=
  (Sum_upto (seq_from f m) (minus n m)).
(* End_Tex_Verb *)

End infinite_ring_sums.

Section ring_sums_over_lists.
(* Tex_Prose
\section{Ring Sums over Lists}
*)

(* Begin_Tex_Verb *)
Fixpoint RList_Mem [l:(list R); n:nat] : R :=
  Cases l n of nil _       => Zero
             | (cons a _) O => a
             | (cons _ k) (S y) => (RList_Mem k y)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint List_Sum_upto [l:(list R); n:nat] : R :=
  Cases n of O     => Zero
	   | (S x) => (RList_Mem l x) [+] (List_Sum_upto l x)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma list_sum_upto_O : (l:(list R))(List_Sum_upto l O) [=] Zero.
(* End_Tex_Verb *)
Algebra.
Qed.

(* Begin_Tex_Verb *)
Definition List_Sum_from_upto [l:(list R); m,n:nat] : R :=
   (List_Sum_upto l n) [-] (List_Sum_upto l m).
(* End_Tex_Verb *)

(* Tex_Prose
Here's an alternative def of \verb!List_Sum_from_upto!, with lemma
 that it's equivalent to the original.
*)
(* Begin_Tex_Verb *)
Fixpoint List_End [l:(list R); n:nat] : (list R) :=
   Cases n of O     => l
            | (S p) => (List_End (tail l) p)
   end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition List_Sum_from_upto_alt [l:(list R); m,n:nat] : R :=
   (List_Sum_upto (List_End l m) (minus n m)).
(* End_Tex_Verb *)

End ring_sums_over_lists.
End Ring_sums.

(* Tex_Prose
\section{Distribution properties}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Section Dist_properties.
Variable R : CRing.

(* Begin_Tex_Verb *)
Lemma dist_1b : (x,y,z:R)((x[+]y)[*]z [=] x[*]z[+]y[*]z).
(* End_Tex_Verb *)
Intros x y z.
Step z[*](x[+]y).
Step_final z[*]x[+]z[*]y.
Qed.
Hints Resolve dist_1b : algebra.

(* Begin_Tex_Verb *)
Lemma dist_2a : (x,y,z:R)(z[*](x[-]y) [=] z[*]x[-]z[*]y).
(* End_Tex_Verb *)
Intros x y z.
Step z[*](x[+][--]y).
Step z[*]x[+]z[*][--]y.
Step_final z[*]x[+][--](z[*]y).
Qed.
Hints Resolve dist_2a : algebra.

(* Begin_Tex_Verb *)
Lemma dist_2b : (x,y,z:R)((x[-]y)[*]z [=] x[*]z[-]y[*]z).
(* End_Tex_Verb *)
Intros x y z.
Step z[*](x[-]y).
Step_final z[*]x[-]z[*]y.
Qed.
Hints Resolve dist_2b : algebra.

(* Begin_Tex_Verb *)
Lemma mult_distr_sum0_lft : (f:nat->R)(x:R)(n:nat)
                            (Sum0 n [i:nat](x [*] (f i))) [=]
                            (x [*] (Sum0 n f)).
(* End_Tex_Verb *)
Intros f x n.
Induction n.
 Simpl; Algebra.
Simpl.
Step_final x[*](Sum0 n f) [+] x[*](f n).
Qed.
Hints Resolve mult_distr_sum0_lft.

(* Begin_Tex_Verb *)
Lemma mult_distr_sum_lft : (f:nat->R)(x:R)(m,n:nat)
                           (Sum m n [i:nat](x [*] (f i))) [=]
                           (x [*] (Sum m n f)).
(* End_Tex_Verb *)
Intros f x m n.
Unfold Sum.
Unfold Sum1.
Step_final  x[*](Sum0 (S n) f) [-] x[*] (Sum0 m f).
Qed.
Hints Resolve mult_distr_sum_lft : algebra.

(* Begin_Tex_Verb *)
Lemma mult_distr_sum_rht : (f:nat->R)(x:R)(m,n:nat)
                           (Sum m n [i:nat]((f i) [*] x)) [=]
                           ((Sum m n f) [*] x).
(* End_Tex_Verb *)
Intros f x m n.
Step (Sum m n [i:nat]x[*](f i)).
Step_final x[*] (Sum m n f).
Qed.

(* Begin_Tex_Verb *)
Lemma sumx_const : (n:nat)(x:R)(Sumx [i:nat][_:(lt i n)]x)[=](nring n)[*]x.
(* End_Tex_Verb *)
Intros n x; Induction n.
 Simpl; Algebra.
Simpl.
Stepr (nring n)[*]x[+]One[*]x.
Step_final (nring n)[*]x[+]x.
Qed.

End Dist_properties.

Hints Resolve dist_1b dist_2a dist_2b mult_distr_sum_lft mult_distr_sum_rht sumx_const
              : algebra.


(* Tex_Prose
\section{Properties of exponentiation over N}
\begin{convention}
Let \verb!R! be a ring.
\end{convention}
*)
Section NExp_properties.
Variable R : CRing.

(* Begin_Tex_Verb *)
Lemma nexp_wd :(x,y:R)(n:nat)(x[=]y)->(x[^]n [=] y[^]n).
(* End_Tex_Verb *)
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_strext : (x,y:R)(n:nat)((x[^]n)[#](y[^]n))->(x[#]y).
(* End_Tex_Verb *)
Intros x y n H.
Exact (un_op_strext_unfolded ???? H).
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_Sn : (x:R)(n:nat)(x[*]x[^]n [=] x[^](S n)).
(* End_Tex_Verb *)
Intros x n.
Step_final x[^]n[*]x.
Qed.

Hints Resolve nexp_wd nexp_Sn : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_plus : (x:R)(m,n:nat)(x[^]m[*]x[^]n [=] x[^](plus m n)).
(* End_Tex_Verb *)
Intros x m n.
Induction m.
 Rewrite plus_O_n.
 Step_final One[*]x[^]n.
Rewrite plus_Sn_m.
Step (x[^]m[*]x)[*]x[^]n.
Step (x[*]x[^]m)[*]x[^]n.
Step x[*](x[^]m[*]x[^]n).
Step_final x[*]x[^](plus m n).
Qed.
Hints Resolve nexp_plus : algebra.

(* Begin_Tex_Verb *)
Lemma one_nexp : (n:nat)((One::R)[^]n [=] One).
(* End_Tex_Verb *)
Intro n.
Induction n.
 Algebra.
Step (One::R)[*]One[^]n.
Step_final (One::R)[*]One.
Qed.
Hints Resolve one_nexp : algebra.

(* Begin_Tex_Verb *)
Lemma mult_nexp : (x,y:R)(n:nat)((x[*]y)[^]n [=] x[^]n[*]y[^]n).
(* End_Tex_Verb *)
Intros x y n.
Induction n.
 Step (One::R).
 Step_final (One::R)[*]One.
Step (x[*]y)[*](x[*]y)[^]n.
Step (x[*]y)[*](x[^]n[*]y[^]n).
Step x[*](y[*](x[^]n[*]y[^]n)).
Step x[*]((y[*]x[^]n)[*]y[^]n).
Step x[*]((x[^]n[*]y)[*]y[^]n).
Step x[*](x[^]n[*](y[*]y[^]n)).
Step_final (x[*]x[^]n)[*](y[*]y[^]n).
Qed.
Hints Resolve mult_nexp : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_mult : (x:R)(m,n:nat)((x[^]m)[^]n [=] x[^](mult m n)).
(* End_Tex_Verb *)
Intros x m n.
Induction m.
 Simpl.
 Step_final (One::R)[^]n.
Step (x[*]x[^]m)[^]n.
Step x[^]n[*](x[^]m)[^]n.
Step x[^]n[*]x[^](mult m n).
Step x[^](plus n (mult m n)).
Replace (plus n (mult m n)) with (mult (S m) n); Algebra.
Qed.
Hints Resolve nexp_mult : algebra.

(* Begin_Tex_Verb *)
Lemma zero_nexp : (x:R)(n:nat)(lt O n)->((Zero::R)[^]n [=] Zero).
(* End_Tex_Verb *)
Intros x n H.
Induction n.
 Inversion H.
Step_final (Zero::R)[*]Zero[^]n.
Qed.
Hints Resolve zero_nexp : algebra.

(* Begin_Tex_Verb *)
Lemma inv_nexp_even : (x:R)(n:nat)(even n)->(([--]x)[^]n [=] x[^]n).
(* End_Tex_Verb *)
Intros x n H.
Elim (even_2n n); Try Assumption.
Intros m H0.
Rewrite H0. Unfold double.
Step ([--]x)[^]m[*]([--]x)[^]m.
Step ([--]x[*][--]x)[^]m.
Step (x[*]x)[^]m.
Step_final x[^]m[*]x[^]m.
Qed.
Hints Resolve inv_nexp_even : algebra.

(* Begin_Tex_Verb *)
Lemma inv_nexp_two : (x:R)(([--]x)[^](2) [=] x[^](2)).
(* End_Tex_Verb *)
Intro x.
Apply inv_nexp_even.
Auto with arith.
Qed.
Hints Resolve inv_nexp_two : algebra.

(* Begin_Tex_Verb *)
Lemma inv_nexp_odd : (x:R)(n:nat)(odd n)->(([--]x)[^]n [=] [--](x[^]n)).
(* End_Tex_Verb *)
Intros x n H.
Inversion H; Clear H1 H n.
Step ([--]x)[*]([--]x)[^]n0.
Step [--]x[*]x[^]n0.
Step_final [--](x[*]x[^]n0).
Qed.
Hints Resolve inv_nexp_odd : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_one : (x:R)(x[^](1) [=] x).
(* End_Tex_Verb *)
Intro x.
Step_final One[*]x.
Qed.
Hints Resolve nexp_one : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_two : (x:R)(x[^](2) [=] x[*]x).
(* End_Tex_Verb *)
Intro x.
Replace (2) with (plus (1) (1)).
 Step_final x[^](1)[*]x[^](1).
Auto with arith.
Qed.
Hints Resolve nexp_two : algebra.

(* Begin_Tex_Verb *)
Lemma inv_one_even_nexp : (n:nat)(even n)->([--]One)[^]n[=](One::R).
(* End_Tex_Verb *)
Intros n H.
Step_final (One::R)[^]n.
Qed.
Hints Resolve inv_one_even_nexp : algebra.

(* Begin_Tex_Verb *)
Lemma inv_one_odd_nexp : (n:nat)(odd n)->([--]One)[^]n[=][--](One::R).
(* End_Tex_Verb *)
Intros n H.
Step_final [--]((One::R)[^]n).
Qed.
Hints Resolve inv_one_odd_nexp : algebra.

(* Begin_Tex_Verb *)
Lemma square_plus : (x,y:R)(x[+]y)[^](2)[=]x[^](2)[+]y[^](2)[+]Two[*]x[*]y.
(* End_Tex_Verb *)
Intros x y.
Step (x[+]y)[*](x[+]y).
Step x[*](x[+]y)[+]y[*](x[+]y).
Step x[*]x[+]x[*]y[+](y[*]x[+]y[*]y).
Step x[^](2)[+]x[*]y[+](x[*]y[+]y[^](2)).
Step x[^](2)[+]x[*]y[+]x[*]y[+]y[^](2).
Step x[^](2)[+](x[*]y[+]x[*]y)[+]y[^](2).
Step x[^](2)[+](Two[*](x[*]y))[+]y[^](2).
Step x[^](2)[+](Two[*]x[*]y)[+]y[^](2).
Step x[^](2)[+]((Two[*]x[*]y)[+]y[^](2)).
Step_final x[^](2)[+](y[^](2)[+]Two[*]x[*]y).
Qed.

(* Begin_Tex_Verb *)
Lemma square_minus : (x,y:R)(x[-]y)[^](2)[=](x[^](2)[+]y[^](2))[-]Two[*]x[*]y.
(* End_Tex_Verb *)
Intros x y.
Unfold cg_minus.
EApply eq_transitive_unfolded.
 Apply square_plus.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_funny : (x,y:R)((x[+]y)[*](x[-]y) [=] x[^](2)[-]y[^](2)).
(* End_Tex_Verb *)
Intros x y.
Step x[*](x[-]y)[+]y[*](x[-]y).
Step (x[*]x[-]x[*]y)[+](y[*]x[-]y[*]y).
Step (x[*]x[+][--](x[*]y))[+](y[*]x[+][--](y[*]y)).
Step ((x[*]x[+][--](x[*]y))[+]y[*]x)[+][--](y[*]y).
Step (x[*]x[+]([--](x[*]y)[+]y[*]x))[+][--](y[*]y).
Step (x[*]x[+]([--](x[*]y)[+]x[*]y))[+][--](y[*]y).
Step (x[*]x[+]Zero)[+][--](y[*]y).
Step x[*]x[+][--](y[*]y).
Step_final x[*]x[-]y[*]y.
Qed.
Hints Resolve nexp_funny : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_funny' : (x,y:R)((x[-]y)[*](x[+]y) [=] x[^](2)[-]y[^](2)).
(* End_Tex_Verb *)
Intros x y.
Step_final (x[+]y)[*](x[-]y).
Qed.
Hints Resolve nexp_funny' : algebra.

End NExp_properties.

Hints Resolve nexp_wd nexp_Sn nexp_plus one_nexp mult_nexp nexp_mult zero_nexp
  inv_nexp_even inv_nexp_two inv_nexp_odd nexp_one nexp_two nexp_funny
  inv_one_even_nexp inv_one_odd_nexp nexp_funny' one_nexp square_plus square_minus : algebra.

Section CRing_Ops.

(* Tex_Prose
\section{Functional Operations}

Now for partial functions.

\begin{convention} As usual, let \verb!R:CRing! and \verb!F,G:(PartFunct R)! with predicates respectively \verb!P! and \verb!Q!.
\end{convention}
*)

Variable R:CRing.

Variables F,G:(PartFunct R).

Local P := (pfpred R F).
Local Q := (pfpred R G).

Section Part_Function_Mult.

(* Begin_Tex_Verb *)
Lemma part_function_mult_strext :
  (x,y:R)(Hx:(Conj P Q x))(Hy:(Conj P Q y))
  ((((F x (prj1 R ??? Hx))[*](G x (prj2 R ??? Hx)))[#]
    ((F y (prj1 R ??? Hy))[*](G y (prj2 R ??? Hy))))->(x[#]y)).
(* End_Tex_Verb *)
Intros x y Hx Hy H.
Elim (bin_op_strext_unfolded ?????? H); Intro H1; Exact (pfstrx ?????? H1).
Qed.

(* Begin_Tex_Verb *)
Definition Fmult := (Build_PartFunct R ? 
  (conj_wd ??? (pfprwd ? F) (pfprwd ? G))
  [x:R][Hx:(Conj P Q x)]((F x (prj1 R ??? Hx))[*](G x (prj2 R ??? Hx))) 
  part_function_mult_strext).
(* End_Tex_Verb *)

End Part_Function_Mult.

Section Part_Function_Nth_Power.

(* Begin_Tex_Verb *)
Variable n:nat.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma part_function_nth_strext : (x,y:R)(Hx:(P x))(Hy:(P y))
  ((((F x Hx)[^]n)[#]((F y Hy)[^]n))->(x[#]y)).
(* End_Tex_Verb *)
Intros x y Hx Hy H.
Apply pfstrx with F Hx Hy.
Apply nexp_strext with n; Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Fnth := (Build_PartFunct R ?
  (pfprwd R F)
  [x:R][Hx:(P x)](F x Hx)[^]n 
  part_function_nth_strext).
(* End_Tex_Verb *)

End Part_Function_Nth_Power.

End CRing_Ops.

(* Begin_Tex_Verb *)
Definition Fscalmult [R:CRing][alpha:R][F:(PartFunct R)] :=
  (Fmult R {-C-}alpha F).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\begin{itemize}
\item \verb!(Fmult ? F G)! will be denoted by {\tt\hypertarget{Operator_16}{F\{*\}G}}.
\item \verb!(Fnth ? F n)! will be denoted by \hypertarget{Operator_17}{}\verb!F{^}n!.
\item \verb!(Fscalmult ? c F)! will be denoted by {\tt\hypertarget{Operator_18}{c\{**\}F}}.
\end{itemize}
\end{notation}
*)

Implicits Fmult [1].
Infix 6 "{*}" Fmult.

Implicits Fscalmult [1].
Infix LEFTA 2 "{**}" Fscalmult.

Implicits Fnth [1].
Infix LEFTA 2 "{^}" Fnth.
