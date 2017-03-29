(* $Id: COrdFields.v,v 1.21 2003/03/13 12:06:14 lcf Exp $ *)

Require Export Refl_corr.

(* ORDERED FIELDS *)

(* Tex_Prose
\chapter{Ordered Fields}
\section{Definition of the notion of ordered field}
*)

(* Begin_SpecReals *)

Implicit Arguments On.

(* Begin_Tex_Verb *)
Record strictorder [A:Set; R: A->A->CProp] : CProp :=
  { so_trans : (Ctransitive R);
    so_asym  : (antisymmetric R)
  }.
(* End_Tex_Verb *)

Implicit Arguments Off.

(* Begin_Tex_Verb *)
Record is_COrdField [F: CField; less : (CCSetoid_relation F)] : CProp :=
 {ax_less_strorder : (strictorder less);
  ax_plus_resp_less: (x,y:F)(less x y) -> (z:F)(less (x[+]z) (y[+]z));
  ax_mult_resp_pos : (x,y:F)(less Zero x)->(less Zero y)->(less Zero (x[*]y));
  ax_less_conf_ap  : (x,y:F)(Iff (x [#] y) ((less x y) + (less y x)))
 }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record COrdField : Type :=
  {cof_crr   :> CField;
   cof_less  :  (CCSetoid_relation cof_crr);
   cof_proof :  (is_COrdField cof_crr cof_less)
  }.
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\verb!cof_less! is denoted infix by {\tt\hypertarget{Operator_22}{[<]}}.
The first argument is left implicit.
In the names of lemmas, {\tt [<]} is written as \verb!less! and
 {\tt Zero [<]} is written as \verb!pos!.
\end{notation}
*)

Implicits cof_less [1].
Infix NONA 8 "[<]" cof_less.

(* Begin_Tex_Verb *)
Definition greater := [F:COrdField; x,y : F] y[<]x.
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
{\tt\hypertarget{Operator_23}{a [>] b}} denotes \verb!(greater ? a b)!.
\end{notation}
*)

Implicits greater [1].
Infix NONA 8 "[>]" greater.

(* End_SpecReals *)

(* Tex_Prose
Less or equal is defined as ``not greater than''.
*)

(* Begin_Tex_Verb *)
Definition leEq [F:COrdField; x,y:F]: Prop := (Not (y[<]x)).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
{\tt LeEq} is denoted infix by {\tt\hypertarget{Operator_24}{[<=]}}.
In lemmas, {\tt [<=]} is written as {\tt leEq}, and
{\tt Zero [<=]} is written as \verb!nonneg!.
\end{notation}
*)

Implicits leEq [1].
Infix NONA 8 "[<=]" leEq.

Section COrdField_axioms.
(* Tex_Prose
\section{COrdField axioms}
\begin{convention}
Let \verb!F! be a field.
\end{convention}
*)

Variable F : COrdField.

(* Begin_Tex_Verb *)
Lemma COrdField_is_COrdField : (is_COrdField F cof_less).
(* End_Tex_Verb *)
Elim F; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_strorder : (strictorder (!cof_less F)).
(* End_Tex_Verb *)
Elim COrdField_is_COrdField; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_transitive_unfolded : (x,y,z:F)(x[<]y) -> (y[<]z) -> (x[<]z).
(* End_Tex_Verb *)
Elim less_strorder; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_antisymmetric_unfolded : (x,y:F)((x[<]y) -> (Not (y[<]x))).
(* End_Tex_Verb *)
Elim less_strorder.
Intros H1 H2 x y H.
Intro H0.
Elim (H2 ?? H).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma less_irreflexive : (irreflexive (!cof_less F)).
(* End_Tex_Verb *)
Red.
Intro x; Intro H.
Elim (less_antisymmetric_unfolded ? ? H H).
Qed.

(* Begin_Tex_Verb *)
Lemma less_irreflexive_unfolded : (x:F)(Not (x[<]x)).
(* End_Tex_Verb *)
Proof less_irreflexive.

(* Begin_Tex_Verb *)
Lemma plus_resp_less_rht : (x,y,z:F)(x [<] y) -> (x[+]z [<] y[+]z).
(* End_Tex_Verb *)
Elim COrdField_is_COrdField; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_resp_pos :
                (x,y:F)(Zero [<] x)->(Zero [<] y)->(Zero [<] (x[*]y)).
(* End_Tex_Verb *)
Elim COrdField_is_COrdField; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_conf_ap : (x,y:F)(Iff (x [#] y) 
                                              ((x [<] y) + (y [<] x))).
(* End_Tex_Verb *)
Elim COrdField_is_COrdField; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_wdr : (x,y,z:F)(x[<]y) -> (y [=] z) -> (x[<]z).
(* End_Tex_Verb *)
Proof (Ccsr_wdr F cof_less).

(* Begin_Tex_Verb *)
Lemma less_wdl : (x,y,z:F)(x[<]y) -> (x [=] z) -> (z[<]y).
(* End_Tex_Verb *)
Proof (Ccsr_wdl F cof_less).

End COrdField_axioms.

Section OrdField_basics.

(* Tex_Prose
\section{Basics}
*)

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}.
\end{convention}
*)
Variable R : COrdField.


(* Begin_Tex_Verb *)
Lemma less_imp_ap : (x,y:R)((x [<] y) -> (x [#] y)).
(* End_Tex_Verb *)
Intros x y H.
Elim (less_conf_ap ? x y); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Greater_imp_ap : (x,y:R)((y [<] x) -> (x [#] y)).
(* End_Tex_Verb *)
Intros x y H.
Elim (less_conf_ap ? x y); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_imp_less : (x,y:R)((x [#] y) -> ((x [<] y)+(y [<] x))).
(* End_Tex_Verb *)
Intros x y.
Elim (less_conf_ap ? x y); Auto.
Qed.


(* Tex_Prose
Now properties which can be derived.
*)

(* Begin_Tex_Verb *)
Lemma cotrans_less : (cotransitive (!cof_less R)).
(* End_Tex_Verb *)
Red.
Intros x y H z.
Generalize (less_imp_ap ? ? H); Intro H0.
Elim (ap_cotransitive_unfolded ? ? ? H0 z); Intro H1.
 Elim (ap_imp_less ? ? H1).
  Auto.
 Intro H2.
 Right.
 Apply (less_transitive_unfolded ? ? ? ? H2 H).
Elim (ap_imp_less ? ? H1).
 Auto.
Intro H2.
Left.
Apply (less_transitive_unfolded ? ? ? ? H H2).
Qed.

(* Begin_Tex_Verb *)
Lemma cotrans_less_unfolded : (x,y:R)(x [<] y)->(z:R)(x[<]z)+(z[<]y).
(* End_Tex_Verb *)
Proof cotrans_less.

(* Begin_Tex_Verb *)
Lemma pos_ap_zero : (x:R)(Zero [<] x)-> x [#] Zero.
(* End_Tex_Verb *)
Intros x H.
Apply Greater_imp_ap.
Assumption.
Defined.

(* Main characterization of less *)

(* Begin_Tex_Verb *)
Lemma leEq_not_eq : (x,y:R)(x[<=]y)->(x[#]y)->(x[<]y).
(* End_Tex_Verb *)
Intros x y H H0.
Elim (ap_imp_less ?? H0); Intro H1; Auto.
Elim (H H1).
Qed.

End OrdField_basics.

Section infinity_of_cordfields.
(* Tex_Prose
\section{Infinity of ordered fields}

In an ordered field we have that \verb!One [+] One! and
\verb!One [+] One [+] One! and so on are all apart from zero.
We first show this, so that we can define \verb!TwoNZ!, \verb!ThreeNZ!
and so on. These are elements of \verb!NonZeros!, so that we can write
e.g.\ \verb!x[/]TwoNZ!.
*)

(* Tex_Prose
\begin{convention}
Let \verb!R! be a field.
\end{convention}
*)

Variable R : COrdField.

(* Begin_Tex_Verb *)
Lemma pos_one : ((Zero::R) [<] One).
(* End_Tex_Verb *)
 (* 0[#]1, so 0<1 (and we are done) or 1<0; so asSume 1<0. *)
Elim (ap_imp_less ? ? ? (ring_non_triv R)).
 2: Auto.
Intro H.
ElimType False.
Apply (less_irreflexive_unfolded R One).
Apply less_transitive_unfolded with (Zero::R).
Auto.
 (* By plus_resp_less, 0=(1-1)<(0-1)=-1. *)
Cut (Zero::R) [<] [--]One.
 2: Step (One::R)[+][--]One.
 2: Stepr (Zero::R)[+][--]One.
 2: Apply plus_resp_less_rht; Auto.
Intro H0.
 (* By mult_resp_pos, 0<(-1).(-1)=1. *)
RStepr [--](One::R)[*][--]One.
Apply (mult_resp_pos ? ? ? H0 H0).
Qed.

(* Begin_Tex_Verb *)
Lemma nring_less_succ : (m:nat)((nring m)::R) [<] (nring (S m)).
(* End_Tex_Verb *)
Intro m.
Simpl.
Stepr (One [+] (!nring R m)).
Step (Zero [+] (!nring R m)).
Apply plus_resp_less_rht.
Apply pos_one.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_less : (m,n:nat)(lt m n) -> (((nring m)::R) [<] (nring n)).
(* End_Tex_Verb *)
Intros m n H.
Generalize (toCProp_lt ?? H); Intro H0.
Elim H0.
 Apply nring_less_succ.
Clear H0 H n; Intros n H H0.
Apply less_transitive_unfolded with (!nring R n).
 Assumption.
Apply nring_less_succ.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_leEq : (m,n:nat)(le m n) -> (((nring m)::R) [<=] (nring n)).
(* End_Tex_Verb *)
Intros m n H.
Elim (le_lt_eq_dec ? ? H); Intro H1.
 Unfold leEq. Apply less_antisymmetric_unfolded.
 Apply nring_less. Auto.
Rewrite H1.
Unfold leEq. Apply less_irreflexive_unfolded.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_apart : (m,n:nat)(~(m=n) -> (((nring m)::R) [#] (nring n))).
(* End_Tex_Verb *)
Intros m n H.
Elim (lt_eq_lt_dec m n); Intro H0.
 Elim H0; Intro H1.
  Apply less_imp_ap.
  Apply nring_less.
 Assumption.
 Elim (H H1).
Apply Greater_imp_ap.
Apply nring_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_ap_zero :(n:nat)(~(n=O) ->((!nring R n)[#]Zero)).
(* End_Tex_Verb *)
Intros n H.
Exact (nring_apart ? ? H).
Qed.

(* Begin_Tex_Verb *)
Lemma nring_ap_zero' :(n:nat)(~(O=n) ->((!nring R n)[#]Zero)).
(* End_Tex_Verb *)
Intros.
Apply nring_ap_zero; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nringS_ap_zero:(m:nat)((!nring R (S m))[#]Zero).
(* End_Tex_Verb *)
Intros.
Apply nring_ap_zero.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_ap_zero_imp:(n:nat)((!nring R n)[#]Zero)->(~(O=n)).
(* End_Tex_Verb *)
Intros n H.
Induction n.
Simpl in H.
Elim (ap_irreflexive_unfolded ?? H).
Apply O_S.
Qed.

(* Begin_Tex_Verb *)
Definition Snring [n:nat] := (!nring R (S n)).
(* End_Tex_Verb *)

Load Transparent_algebra.

(* Begin_Tex_Verb *)
Lemma pos_Snring : (n:nat)((Zero::R) [<] (Snring n)).
(* End_Tex_Verb *)
Intro n.
Change (!nring R O) [<] (nring (S n)).
Apply nring_less.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_fac_ap_zero:(n:nat)((!nring R (fac n))[#]Zero).
(* End_Tex_Verb *)
Intro n; Apply nring_ap_zero. Cut (lt O (fac n)).
 Omega.
Apply nat_fac_gtzero.
Qed.

Load Opaque_algebra.

(***********************************)
Section Basic_Properties_of_leEq.
(***********************************)

(* Tex_Prose
\section{Properties of $\leq$ ({\tt leEq})}
*)

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}.
\end{convention}
*)

(* Begin_Tex_Verb *)
Lemma leEq_wdr : (x,y,z:R)(x[<=]y) -> (y [=] z) -> (x[<=]z).
(* End_Tex_Verb *)
Unfold leEq.
Intros x y z H H0.
Intro H1.
Apply H.
Step z.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_wdl : (x,y,z:R)(x[<=]y) -> (x [=] z) -> (z[<=]y).
(* End_Tex_Verb *)
Unfold leEq.
Intros x y z H H0.
Intro H1.
Apply H.
Stepr z.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_reflexive : (x:R)(x[<=]x).
(* End_Tex_Verb *)
Intro x.
Unfold leEq.
Apply less_irreflexive_unfolded.
Qed.

(* Begin_Tex_Verb *)
Lemma eq_imp_leEq : (x,y:R)(x[=]y)->(x[<=]y).
(* End_Tex_Verb *)
Intros x y H.
Stepr x.
Exact (leEq_reflexive ?).
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_imp_eq : (x,y:R)(x [<=] y) -> (y [<=] x) -> (x [=] y).
(* End_Tex_Verb *)
Unfold leEq. Intros x y H H0.
Apply not_ap_imp_eq. Intro H1. Apply H0.
Elim (ap_imp_less ??? H1); Intro H2. Auto.
Elim (H H2).
Qed.

(* Begin_Tex_Verb *)
Lemma lt_equiv_imp_eq : (x,x':R)
  ((y:R)(x [<] y) -> (x' [<] y)) ->
  ((y:R)(x' [<] y) -> (x [<] y)) ->
    x [=] x'.
(* End_Tex_Verb *)
Intros x x' H H0.
Apply leEq_imp_eq; Unfold leEq; Intro H1.
Apply (less_irreflexive_unfolded ? x); Auto.
Apply (less_irreflexive_unfolded ? x'); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_leEq_trans : (x,y,z:R)(x [<] y) -> (y [<=] z) -> (x [<] z).
(* End_Tex_Verb *)
Intros x y z.
Unfold leEq.
Intros H H0.
Elim (cotrans_less_unfolded ? ? ? H z); Intro H1.
Assumption.
Elim (H0 H1).
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_less_trans : (x,y,z:R)(x [<=] y) -> (y [<] z) -> (x [<] z).
(* End_Tex_Verb *)
Intros x y z.
Unfold leEq.
Intros H H0.
Elim (cotrans_less_unfolded ? ? ? H0 x); Intro H1.
Elim (H H1).
Assumption.
Qed.


(* Begin_Tex_Verb *)
Lemma leEq_transitive:(x,y,z:R)(x[<=]y)->(y[<=]z)->(x[<=]z).
(* End_Tex_Verb *)
Intros x y z H H0 H1.
Apply H.
Apply leEq_less_trans with y:=z; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_leEq : (x,y:R)(x [<] y) -> (x [<=] y).
(* End_Tex_Verb *)
Intros.
Unfold leEq.
Apply less_antisymmetric_unfolded.
Assumption.
Qed.

End Basic_Properties_of_leEq.

Section up_to_four.

(* Tex_Prose
\subsection{Properties of one up to four}
\begin{nameconvention}
In the names of lemmas, we denote the numbers 0,1,2,3,4 and so on, by
\verb!zero!, \verb!one!, \verb!two! etc.
\end{nameconvention}
*)

(* Begin_Tex_Verb *)
Lemma less_plusOne: (x:R) x [<] x[+]One.
(* End_Tex_Verb *)
 (* by plus_resp_less_rht and pos_one *)
Intros x.
Step Zero[+]x; Stepr One[+]x.
Apply plus_resp_less_rht.
Exact pos_one.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_one_ext_less: (x,y:R)(x [<] y) -> x [<] y[+]One.
(* End_Tex_Verb *)
 (* By transitivity of less and less_plusOne *)
Intros x y H.
Apply less_leEq_trans with y.
Assumption.
Apply less_leEq; Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma one_less_two : ((One::R) [<] Two).
(* End_Tex_Verb *)
Simpl.
Stepr (One::R)[+]One.
Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma two_less_three : ((Two::R) [<] Three).
(* End_Tex_Verb *)
Simpl.
Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma three_less_four : ((Three::R) [<] Four).
(* End_Tex_Verb *)
Simpl.
Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_two : ((Zero::R) [<] Two).
(* End_Tex_Verb *)
Apply less_leEq_trans with (One::R).
Exact pos_one.
Apply less_leEq; Exact one_less_two.
Qed.

(* Begin_Tex_Verb *)
Lemma one_less_three : ((One::R) [<] Three).
(* End_Tex_Verb *)
Apply less_leEq_trans with (Two::R).
Exact one_less_two.
Apply less_leEq; Exact two_less_three.
Qed.

(* Begin_Tex_Verb *)
Lemma two_less_four : ((Two::R) [<] Four).
(* End_Tex_Verb *)
Apply less_leEq_trans with (Three::R).
Exact two_less_three.
Apply less_leEq; Exact three_less_four.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_three : ((Zero::R) [<] Three).
(* End_Tex_Verb *)
Apply less_leEq_trans with (Two::R).
Exact pos_two.
Apply less_leEq; Exact two_less_three.
Qed.


(* Begin_Tex_Verb *)
Lemma one_less_four : ((One::R) [<] Four).
(* End_Tex_Verb *)
Apply less_leEq_trans with (Three::R).
Exact one_less_three.
Apply less_leEq; Exact three_less_four.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_four : ((Zero::R) [<] Four).
(* End_Tex_Verb *)
Apply less_leEq_trans with (Three::R).
Exact pos_three.
Apply less_leEq; Exact three_less_four.
Qed.

(* Begin_Tex_Verb *)
Lemma two_ap_zero : Two [#] (Zero::R).
(* End_Tex_Verb *)
Apply pos_ap_zero.
Apply pos_two.
Qed.

(* Begin_Tex_Verb *)
Lemma three_ap_zero : Three [#] (Zero::R).
(* End_Tex_Verb *)
Apply pos_ap_zero.
Apply pos_three.
Qed.

(* Begin_Tex_Verb *)
Lemma four_ap_zero : Four [#] (Zero::R).
(* End_Tex_Verb *)
Apply pos_ap_zero.
Apply pos_four.
Qed.

End up_to_four.

End infinity_of_cordfields.

(* Tex_Prose
\begin{convention}
{\tt\hypertarget{Syntactic_16}{OneNZ}}, {\tt\hypertarget{Syntactic_17}{TwoNZ}}, {\tt\hypertarget{Syntactic_18}{ThreeNZ}} and {\tt\hypertarget{Syntactic_19}{FourNZ}} are 1,
2, 3 and 4 as elements of \verb!NonZeros!.
\end{convention}
*)

Notation " x [/]OneNZ" := (x [/] One [//] (ring_non_triv ?)).
Notation " x [/]TwoNZ" := (x [/] Two [//] (two_ap_zero ?)).
Notation " x [/]ThreeNZ" := (x [/] Three [//] (three_ap_zero ?)).
Notation " x [/]FourNZ" := (x [/] Four [//] (four_ap_zero ?)).

Section consequences_of_infinity.

(* Tex_Prose
\subsection{Consequences of infinity}
*)

Variable F:COrdField.

(* Begin_Tex_Verb *)
Lemma square_eq : (x,a:F)(a [#] Zero)->
  (x[^](2) [=] a[^](2))->{x[=]a} + {x[=][--]a}.
(* End_Tex_Verb *)
Intros x a a_ H.
Elim (Cconditional_square_eq F x a); Auto.
Apply two_ap_zero.
Qed.

End consequences_of_infinity.

(***********************************)
Section Properties_of_Ordering.
(***********************************)

(* Tex_Prose
\section{Properties of $<$ ({\tt less})}
*)

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}.
\end{convention}
*)
Variable R : COrdField.


(* Tex_Prose
\begin{convention}
We do not use a special predicate for positivity,
(e.g. {\tt PosP}), but just write {\tt Zero [<] x}.
Reasons: it is more natural; in ordinary mathematics we also write $0<x$
(or $x>0$).
\end{convention}
*)

Section addition.
(* Tex_Prose
\subsection{Addition and subtraction}\label{section:less_plus_minus}
\subsection*{$+$ and $-$ respect $<$}
*)

(* Begin_Tex_Verb *)
Lemma plus_resp_less_lft : (x,y,z:R)(x [<] y) -> (z[+]x) [<] (z[+]y).
(* End_Tex_Verb *)
Intros x y z H.
Step x[+]z.
Stepr y[+]z.
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_resp_less : (x,y:R)(x [<] y) -> ([--]y) [<] ([--]x).
(* End_Tex_Verb *)
Intros x y H.
RStep x [+] ([--]x [+] [--]y).
RStepr y [+] ([--]x [+] [--]y).
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_less : (x,y,z:R)(x [<] y) -> ((x[-]z) [<] (y[-]z)).
(* End_Tex_Verb *)
Transparent cg_minus.
Unfold cg_minus.
Intros x y z H.
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_less_rht :(x,y,z:R)(y [<] x) -> ((z[-]x) [<] (z[-]y)).
(* End_Tex_Verb *)
Intros.
Transparent cg_minus.
Unfold cg_minus.
Apply plus_resp_less_lft.
Apply inv_resp_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_less_both : (a,b,c,d:R)(a [<] b) -> (c [<] d) ->
                                       ((a[+]c) [<] (b[+]d)).
(* End_Tex_Verb *)
Intros.
Apply less_leEq_trans with a[+]d.
Apply plus_resp_less_lft.
Assumption.
Apply less_leEq.
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Tex_Prose
For versions of \verb!plus_resp_less_both! where one \verb![<]! in the
asSumption is replaced by \verb![<=]! see
Section~\ref{section:leEq-plus-minus}.
*)

(* Tex_Prose
\subsection*{Cancellation laws}
*)

(* Begin_Tex_Verb *)
Lemma plus_cancel_less : (x,y,z:R)((x[+]z) [<] (y[+]z)) -> (x [<] y).
(* End_Tex_Verb *)
Intros.
(* Step (x [+] Zero).
   Step (x [+] (z [+] ([--] z))). *)
RStep ((x [+] z) [+] ([--] z)).
(* Stepr (y [+] Zero).
   Stepr (y [+] (z [+] ([--] z))). *)
RStepr ((y [+] z) [+] ([--] z)).
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_cancel_less : (x,y:R)(([--]x) [<] ([--]y)) -> (y [<] x).
(* End_Tex_Verb *)
Intros.
Apply plus_cancel_less with ([--]x)[-]y.
RStep [--]x.
RStepr [--]y.
Assumption.
Qed.

(* Tex_Prose
\subsection*{Laws for shifting}
Lemmas where an operation is transformed into the inverse operation on
the other side of an inequality are called laws for shifting.
\begin{nameconvention}
The names of laws for shifting start with ``\verb!shift_!'', and then come
the operation and the inequality, in the order in which they occur in the
conclusion.
If the shifted operand changes sides w.r.t. the operation and its inverse,
the name gets a prime.
\end{nameconvention}

It would be nicer to write the laws for shifting as bi-implications,
However, it is impractical to use these in Coq
(see the Coq shortcoming in Section~\ref{section:setoid-basics}).
*)

(* Begin_Tex_Verb *)
Lemma shift_less_plus :   (x,y,z:R)(x[-]z [<] y) -> x [<] y[+]z.
(* End_Tex_Verb *)
Intros.
RStep x[-]z[+]z.
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_less_plus' :  (x,y,z:R)(x[-]y [<] z) -> x [<] y[+]z.
(* End_Tex_Verb *)
Intros.
Stepr z[+]y.
Apply shift_less_plus.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_less_minus :  (x,y,z:R)(x[+]z [<] y)-> (x [<] y [-] z).
(* End_Tex_Verb *)
Intros.
RStep (x[+]z)[-]z.
Apply minus_resp_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_less_minus' : (x,y,z:R)(z[+]x [<] y)-> (x [<] y [-] z).
(* End_Tex_Verb *)
Intros.
Apply shift_less_minus.
Step z[+]x.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_plus_less :   (x,y,z:R)(x [<] z [-] y) -> (x[+]y [<] z).
(* End_Tex_Verb *)
Intros.
RStepr (z[-]y)[+]y.
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_plus_less' :  (x,y,z:R)(y [<] z [-] x) -> (x[+]y [<] z).
(* End_Tex_Verb *)
Intros.
Step y[+]x.
Apply shift_plus_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_minus_less :  (x,y,z:R)(x [<] z[+]y) -> (x[-]y [<] z).
(* End_Tex_Verb *)
Intros.
Stepr (z[+]y)[-]y.
Apply minus_resp_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_minus_less' : (x,y,z:R)(x [<] y[+]z) -> (x[-]y [<] z).
(* End_Tex_Verb *)
Intros.
Apply shift_minus_less.
Stepr y[+]z.
Assumption.
Qed.

(* Tex_Prose
Some special cases of laws for shifting.
*)

(* Begin_Tex_Verb *)
Lemma shift_zero_less_minus : (x,y:R)(x[<]y) -> (Zero[<](y[-]x)).
(* End_Tex_Verb *)
Intros.
RStep x[-]x.
Apply minus_resp_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma qltone: (q:R) (q [<] One) ->(q[-]One [#]Zero).
(* End_Tex_Verb *)
Intros.
Apply less_imp_ap.
Apply shift_minus_less.
Stepr (One::R).
Auto.
Qed.

End addition.

Section multiplication.
(* Tex_Prose
\subsection{Multiplication and division}
*)

(* Tex_Prose
   By convention~\ref{convention:div-form}
   in CFields (Section~\ref{section:fields}), we often have redundant premises
   in lemmas. E.g. the informal statement
     \[\text{for all }x, y \text{ in } R \text{ with } 0<x \text{ and } 0<y
       \text{ we have } 0 < y / x
     \]
   is formalized as follows.
\begin{verbatim}
        (x,y:R)(H: (x [#] Zero))(Zero [<] x) -> (Zero [<] y)->
        (Zero [<] y[/]x[//]H)
\end{verbatim}
   We do this to keep it easy to use such lemmas.

\subsection*{Multiplication and division respect $<$}
*)

(* Begin_Tex_Verb *)
Lemma mult_resp_less :
 (x,y,z:R)(x [<] y) -> (Zero [<] z) -> ((x [*] z) [<] (y [*] z)).
(* End_Tex_Verb *)
Intros.
Apply plus_cancel_less with ([--] (x[*]z)).
Step (Zero::R).
(* Stepr ((y[*]z) [-] (x[*]z)). *)
RStepr ((y[-]x)[*]z).
Apply mult_resp_pos.
Step (x[-]x).
Apply minus_resp_less.
Assumption.

Assumption.
Qed.


(* Begin_Tex_Verb *)
Lemma recip_resp_pos :
 (y:R)(y_:y[#]Zero)(Zero [<] y) -> Zero [<] (One [/] y[//]y_).
(* End_Tex_Verb *)
Intros.
Cut (Zero [<] One[/]y[//]y_) + (One[/]y[//]y_ [<] Zero).
Intros. Elim H0; Clear H0; Intros H0.
Auto.
ElimType False.
Apply (less_irreflexive_unfolded R Zero).
EApply less_transitive_unfolded.
2: Apply H0.
Cut One [<] (Zero::R). Intro H1.
Elim (less_antisymmetric_unfolded ? ? ? (pos_one ?) H1).
Step [--]([--]One::R). Stepr [--](Zero::R).
Apply inv_resp_less.
RStepr y[*]([--](One[/]y[//]y_)).
Apply mult_resp_pos. Auto.
Step [--](Zero::R).
Apply inv_resp_less. Auto.
Apply ap_imp_less.
Apply ap_symmetric_unfolded. Apply div_resp_ap_zero_rev.
Apply ring_non_triv.
Qed.


(* Begin_Tex_Verb *)
Lemma div_resp_less_rht :
 (x,y,z:R)(z_:z[#]Zero)(x [<] y) -> (Zero [<] z) ->
         ((x [/] z[//]z_) [<] (y [/] z[//]z_)).
(* End_Tex_Verb *)
Intros.
RStep x[*](One[/]z[//]z_).
RStepr y[*](One[/]z[//]z_).
Apply mult_resp_less. Auto.
Apply recip_resp_pos.
Auto.
Qed.


(* Begin_Tex_Verb *)
Lemma div_resp_pos :
        (x,y:R)(x_: (x [#] Zero))(Zero [<] x) -> (Zero [<] y)->
        (Zero [<] y[/]x[//]x_).
(* End_Tex_Verb *)
Intros.
Step Zero[/]x[//]x_.
Apply div_resp_less_rht; Auto.
Qed.


(* Begin_Tex_Verb *)
Lemma mult_resp_less_lft :
 (x,y,z:R)(x [<] y) -> (Zero [<] z) -> ((z [*] x) [<] (z [*] y)).
(* End_Tex_Verb *)
Intros.
Step (x [*] z).
Stepr (y [*] z).
Apply mult_resp_less.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_resp_less_both :
 (x,y,u,v:R)(Zero [<=] x) -> (x [<] y) -> (Zero [<=] u) -> (u [<] v) ->
 x[*]u [<] y[*]v.
(* End_Tex_Verb *)
Cut (x,y,z:R)(x [<=] y) -> (Zero [<=] z) -> (x[*]z) [<=] (y[*]z).
Intro resp_leEq.
Intros.
Apply leEq_less_trans with y[*]u.
Apply resp_leEq; Auto.
Apply less_leEq; Auto.
Apply mult_resp_less_lft; Auto.
Apply leEq_less_trans with x; Auto.

(* Cut *)
Unfold leEq.
Intros x y z H H0 H1.
Generalize (shift_zero_less_minus ? ? H1); Intro H2.
Cut Zero [<] (x[-]y)[*]z.
Intro H3.
 2: RStepr x[*]z[-]y[*]z; Auto.
Cut (a,b:R)(Zero [<] a[*] b) ->
    ((Zero [<] a) * (Zero [<] b)) + ((a [<] Zero) * (b [<] Zero)).
Intro H4.
Generalize (H4 ? ? H3); Intro H5.
Elim H5; Intro H6; Elim H6; Intros H7 H8.
 Apply H.
 Step Zero[+]y.
 Apply shift_plus_less.
 Assumption.
Apply H0.
Assumption.

Intros.
Generalize (Greater_imp_ap ? ? ? H4); Intro H5.
Generalize (mult_cancel_ap_zero_lft ? ? ? H5); Intro H6.
Generalize (mult_cancel_ap_zero_rht ? ? ? H5); Intro H7.
Elim (ap_imp_less ? ? ? H6); Intro H8.
 Right.
 Split; Auto.
 Elim (ap_imp_less ? ? ? H7); Auto.
 Intro H9.
 ElimType False.
 Apply (less_irreflexive_unfolded R Zero).
 Apply less_leEq_trans with a[*]b; Auto.
 Apply less_leEq.
 Apply inv_cancel_less.
 Step (Zero::R).
 Stepr ([--]a)[*]b.
 Apply mult_resp_pos; Auto.
 Step [--](Zero::R).
 Apply inv_resp_less; Auto.
Left.
Split; Auto.
Elim (ap_imp_less ? ? ? H7); Auto.
Intro H9.
ElimType False.
Apply (less_irreflexive_unfolded R Zero).
Apply less_leEq_trans with a[*]b; Auto.
Apply less_leEq.
Apply inv_cancel_less.
Step (Zero::R).
Stepr a[*][--]b.
Apply mult_resp_pos; Auto.
Step [--](Zero::R).
Apply inv_resp_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma recip_resp_less :
 (x,y:R)(x_:x[#]Zero)(y_:y[#]Zero)(Zero [<] x) -> (x [<] y) ->
            (One [/] y[//]y_) [<] (One [/] x[//]x_).
(* End_Tex_Verb *)
Intros.
Cut Zero [<] x[*]y. Intro.
Cut x[*]y [#] Zero. Intro.
RStep x[*](One[/](x[*]y)[//]H2).
RStepr y[*](One[/](x[*]y)[//]H2).
Apply mult_resp_less. Auto.
Apply recip_resp_pos. Auto.
Apply Greater_imp_ap. Auto.
Apply mult_resp_pos. Auto.
Apply less_leEq_trans with x; Try Apply less_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma div_resp_less : (x,y,z:R)(z_:z[#]Zero)
  (Zero[<]z)->(x[<]y)->((x[/]z[//]z_)[<](y[/]z[//]z_)).
(* End_Tex_Verb *)
Intros.
RStep (x[*](One[/]z[//]z_)).
RStepr (y[*](One[/]z[//]z_)).
Apply mult_resp_less.
Assumption.
Apply recip_resp_pos.
Auto.
Qed.


(* Tex_Prose
\subsection*{Cancellation laws}
*)
(* Begin_Tex_Verb *)
Lemma mult_cancel_less : (x,y,z:R)(Zero [<] z) ->
                         ((x[*]z) [<] (y[*]z)) -> (x [<] y).
(* End_Tex_Verb *)
Intros.
Generalize (Greater_imp_ap ? ? ? H); Intro.
RStep ((x[*]z)[*](One[/]z[//]H1)).
RStepr ((y[*]z)[*](One[/]z[//]H1)).
Apply mult_resp_less.
Assumption.
RStep (Zero[/]z[//]H1).
Apply div_resp_less_rht.
Apply pos_one.
Assumption.
Qed.

(* Tex_Prose
\subsection*{Laws for shifting}
For namegiving, see the Section~\ref{section:less_plus_minus}
on plus and minus.
*)
(* Begin_Tex_Verb *)
Lemma shift_div_less : (x,y,z:R)(y_:y[#]Zero)(Zero [<] y) ->
                       (x [<] (z[*]y)) -> ((x[/]y[//]y_) [<] z).
(* End_Tex_Verb *)
Intros.
Apply mult_cancel_less with y. Auto.
Step x. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_div_less' : (x,y,z:R)(y_:y[#]Zero)(Zero [<] y) ->
                        (x [<] (y [*]z)) -> ((x[/]y[//]y_) [<] z).
(* End_Tex_Verb *)
Intros.
Apply shift_div_less; Auto.
Stepr y[*]z. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_less_div : (x,y,z:R)(y_:y[#]Zero)(Zero [<] y) ->
                    ((x[*]y) [<] z) -> (x [<] z[/]y[//]y_).
(* End_Tex_Verb *)
Intros.
Apply mult_cancel_less with y. Auto.
Stepr z. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_less_mult : (x,y,z:R)(Zero[<]z)->
  (z_:z[#]Zero)((x[/]z[//]z_)[<]y)->(x[<](y[*]z)).
(* End_Tex_Verb *)
Intros.
Step (x[/]z[//]z_)[*]z.
Apply mult_resp_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_less_mult' : (x,y,z:R)(y_:y[#]Zero)(Zero [<] y) ->
                         ((x[/]y[//]y_) [<] z) -> (x [<] (y [*]z)).
(* End_Tex_Verb *)
Intros.
Step y[*](x[/]y[//]y_).
Apply mult_resp_less_lft; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_mult_less : (x,y,z:R)(y_:y[#]Zero)(Zero [<] y) ->
                        (x [<] z[/]y[//]y_) -> ((x[*]y) [<] z).
(* End_Tex_Verb *)
Intros.
Stepr (z[/]y[//]y_)[*]y.
Apply mult_resp_less; Auto.
Qed.

(* Tex_Prose
\subsection*{Other properties of multiplication and division}
*)
(* Begin_Tex_Verb *)
Lemma minusOne_less : (x:R) x[-]One [<] x.
(* End_Tex_Verb *)
Intros; Apply shift_minus_less; Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma swap_div : (x,y,z:R)(y_:y[#]Zero)(z_:z[#]Zero)
                 (Zero [<] y) -> (Zero [<] z) ->
                 ((x[/]z[//]z_)[<] y) -> ((x[/]y[//]y_) [<] z).
(* End_Tex_Verb *)
Intros.
RStep (x[/]z[//]z_)[*](z[/]y[//]y_).
Stepr y[*](z[/]y[//]y_).
Apply mult_resp_less. Auto.
Apply div_resp_pos; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma eps_div_less_eps : (eps,d:R)(d_:d [#] Zero)
                         (Zero[<]eps) -> (One [<] d) ->
                         ((eps[/]d[//]d_)[<]eps).
(* End_Tex_Verb *)
Intros.
Apply shift_div_less'.
Apply leEq_less_trans with (One::R).
Apply less_leEq; Apply pos_one.

Assumption.

Step One[*]eps.
Apply mult_resp_less.
Assumption.

Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_div_two : (eps:R)(Zero [<] eps) -> (Zero [<] (eps[/]TwoNZ)).
(* End_Tex_Verb *)
Intros.
Apply shift_less_div.
Apply pos_two.

Step (Zero::R).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_div_two' : (eps:R)(Zero[<]eps)->(eps[/]TwoNZ)[<]eps.
(* End_Tex_Verb *)
Intros.
Apply plus_cancel_less with [--](eps[/]TwoNZ).
Step (Zero::R).
RStepr eps[/]TwoNZ.
Apply pos_div_two; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_div_three : (eps:R)(Zero[<]eps)->Zero[<](eps[/]ThreeNZ).
(* End_Tex_Verb *)
Intros.
Apply mult_cancel_less with (Three::R).
Apply pos_three.
Step (Zero::R); RStepr eps.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_div_three' : (eps:R)(Zero[<]eps)->(eps[/]ThreeNZ)[<]eps.
(* End_Tex_Verb *)
Intros.
Apply plus_cancel_less with [--](eps[/]ThreeNZ).
Step (Zero::R).
RStepr Two[*](eps[/]ThreeNZ).
Apply shift_less_mult' with (ap_symmetric_unfolded ? ? ? (less_imp_ap ? ? ? (pos_two R))).
Apply pos_two.
RStep (Zero::R).
Apply pos_div_three; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_div_four : (eps:R)(Zero[<]eps)->(Zero[<]eps[/]FourNZ).
(* End_Tex_Verb *)
Intros.
RStepr (eps[/]TwoNZ)[/]TwoNZ.
Apply pos_div_two; Apply pos_div_two; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_div_four' : (eps:R)(Zero[<]eps)->(eps[/]FourNZ[<]eps).
(* End_Tex_Verb *)
Intros.
RStep (eps[/]TwoNZ)[/]TwoNZ.
Apply leEq_less_trans with eps[/]TwoNZ.
2: Apply pos_div_two'; Assumption.
Apply less_leEq.
Apply pos_div_two'.
Apply pos_div_two.
Assumption.
Qed.

End multiplication.

Section misc.

(* Tex_Prose
\subsection{Miscellaneous}
*)

(* Begin_Tex_Verb *)
Lemma nring_pos : (m:nat)((lt O m) -> (Zero [<] (!nring R m))).
(* End_Tex_Verb *)
Intro m. Elim m.
Intro; Elim (lt_n_n (0) H).
Clear m; Intros.
Apply leEq_less_trans with (!nring R n).
Step (!nring R O).
Apply nring_leEq; Auto with arith.
Simpl; Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma less_nring : (n,m:nat)((!nring R n)[<](nring m))->(lt n m).
(* End_Tex_Verb *)
Intro n; Induction n.
Intros.
Induction m.
ElimType False; Generalize H; Apply less_irreflexive_unfolded.
Auto with arith.
Intros.
Induction m.
ElimType False.
Cut (!nring R (0))[<](nring (S n)).
Apply less_antisymmetric_unfolded; Assumption.
Apply nring_less; Auto with arith.
Cut (lt n m).
Auto with arith.
Apply Hrecn.
RStepr ((!nring R m)[+]One)[-]One.
Apply shift_less_minus.
Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_nring_fac : (n:nat)Zero[<](!nring R (fac n)).
(* End_Tex_Verb *)
Intro.
Step (!nring R O).
Apply nring_less.
Apply nat_fac_gtzero.
Qed.

(* Begin_Tex_Verb *)
Lemma Smallest_less_Average : (a,b:R)(a[<]b)->(a[<]((a[+]b) [/]TwoNZ)).
(* End_Tex_Verb *)
Intros.
Apply shift_less_div.
Apply pos_two.
RStep a[+]a.
Apply plus_resp_less_lft.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Average_less_Greatest : (a,b:R)(a[<]b)->((a[+]b) [/]TwoNZ) [<] b.
(* End_Tex_Verb *)
Intros.
Apply shift_div_less'.
Apply pos_two.
RStepr b[+]b.
Apply plus_resp_less_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_resp_less : (f,g:nat->R)(a,b:nat)(le a b)->
                      ((i:nat)(le a i) -> (le i b) -> (f i) [<] (g i)) ->
                      (Sum a b f) [<] (Sum a b g).
(* End_Tex_Verb *)
Intros.
Induction b; Intros.
Replace a with O.
Step (f (0)). Stepr (g (0)).
Auto.
Inversion H. Auto.
Elim (le_lt_eq_dec ? ? H); Intro H1.
Apply less_wdl with (Sum a b f)[+](f (S b)).
Apply less_wdr with (Sum a b g)[+](g (S b)).
Apply plus_resp_less_both.
Apply Hrecb. Auto with arith. Auto.
Apply H0; Auto.
Apply eq_symmetric_unfolded. Apply Sum_last.
Apply eq_symmetric_unfolded. Apply Sum_last.
Rewrite H1.
Step (f (S b)).
Stepr (g (S b)).
Apply H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_resp_less : (n:nat)(lt O n)->(f,g:(i:nat)(lt i n)->R)
  ((i:nat)(H:(lt i n))(f i H)[<](g i H))->(Sumx f)[<](Sumx g).
(* End_Tex_Verb *)
Induction n.
Intros; Simpl; ElimType False; Inversion H.
Induction n0.
Intros.
Clear H.
Simpl; Apply plus_resp_less_lft.
Apply H1.
Intros.
Simpl.
Apply plus_resp_less_both.
Step (Sumx [i:nat][l:(lt i (S n1))](f i (lt_S ?? l))).
Stepr (Sumx [i:nat][l:(lt i (S n1))](g i (lt_S ?? l))).
Apply H0.
Auto with arith.
Intros; Apply H2.
Apply H2.
Qed.

(* Begin_Tex_Verb *)
Lemma positive_Sum_two : (x,y:R)(Zero[<]x[+]y)->(Zero[<]x)+(Zero[<]y).
(* End_Tex_Verb *)
Intros.
Cut ([--]x[<]Zero)+(Zero[<]y).
Intro; Inversion_clear H0.
Left; Step [--](Zero::R); Stepr [--][--]x; Apply inv_resp_less; Assumption.
Right; Assumption.
Apply cotrans_less_unfolded.
Step Zero[-]x; Apply shift_minus_less'; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma positive_Sumx : (n:nat)(f:?)(nat_less_n_fun R n f)->
  (Zero[<](Sumx f))->
  {i:nat & {H:(Clt i n) & Zero[<](f i (Clt_to ?? H))}}.
(* End_Tex_Verb *)
Induction n.
Simpl.
Intros; ElimType False; Generalize H0; Apply less_irreflexive_unfolded.
Induction n0.
Simpl.
Intros.
Exists O.
Cut (Clt (0) (1)).
Intro.
Exists H2.
2: Apply toCProp_lt; Auto.
EApply less_wdr.
Apply H1.
Step_lft (f ? (lt_n_Sn (0))).
Apply H0; Auto.
Simpl; Intros.
Clear H.
Cut (Zero[<](f ? (lt_n_Sn (S n1))))+(Zero[<](Sumx [i:nat][l:(lt i n1)](f i (lt_S i (S n1) (lt_S i n1 l))))[+](f n1 (lt_S n1 (S n1) (lt_n_Sn n1)))).
Intro; Inversion_clear H.
Exists (S n1).
Exists (toCProp_lt ?? (lt_n_Sn (S n1))).
EApply less_wdr.
Apply H3.
Apply H1; Auto.
LetTac f':=[i:nat][H:(lt i (S n1))](f i (lt_S ?? H)).
Cut {i:nat & {H:(Clt i (S n1)) & Zero[<](f' i (Clt_to i (S n1) H))}}; Intros.
Elim H; Intros i Hi; Elim Hi; Clear H3 Hi; Intros Hi Hi'.
Exists i.
Cut (Clt i (S (S n1))); Intros.
Exists H3.
EApply less_wdr.
Apply Hi'.
Unfold f'; Simpl.
Apply H1; Auto.
Apply toCProp_lt; Apply lt_S; Apply Clt_to; Assumption.
Apply H0.
Red; Intros; Simpl; Unfold f'.
Apply H1; Auto.
Apply H3; Assumption.
Apply positive_Sum_two.
EApply less_wdr.
2: Apply cm_commutes_unfolded.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma negative_Sumx : (n:nat)(f:?)(nat_less_n_fun R n f)->
  ((Sumx f)[<]Zero)->
  {i:nat & {H:(Clt i n) & (f i (Clt_to ?? H))[<]Zero}}.
(* End_Tex_Verb *)
Intros.
Cut {i:nat & {H:(Clt i n) & Zero[<][--](f i (Clt_to i n H))}}.
Intro.
Elim H1; Intros i Hi; Elim Hi; Clear H0 Hi; Intros Hi Hi'.
Exists i; Exists Hi.
Step [--][--](f i (Clt_to ?? Hi)); Stepr [--](Zero::R); Apply inv_resp_less; Assumption.
Apply positive_Sumx with f:=[i:nat][H:(lt i n)]([--](f i H)).
Red; Intros.
Apply un_op_wd_unfolded; Apply H; Assumption.
Step [--](Zero::R); Apply less_wdr with [--](Sumx f).
Apply inv_resp_less; Assumption.
Generalize f H; Clear H0 H f.
Induction n.
Simpl.
Intros; Algebra.
Intros.
Simpl.
RStep ([--](Sumx [i:nat][l:(lt i n)](f i (lt_S i n l)))[+][--](f n (lt_n_Sn n))).
Apply bin_op_wd_unfolded.
2: Algebra.
Apply Hrecn with f:=[i:nat][l:(lt i n)](f i (lt_S i n l)).
Red; Intros; Apply H; Auto.
Qed.

End misc.

End Properties_of_Ordering.


(***********************************)
Section Properties_of_leEq.
(***********************************)

(* Tex_Prose
\section{Properties of $\leq$ ({\tt leEq})}
*)

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}.
\end{convention}
*)

Variable R : COrdField.

Section addition.
(* Tex_Prose
\subsection{Addition and subtraction}\label{section:leEq-plus-minus}
\subsection*{+ and - respect $\leq$}
*)

(* Begin_Tex_Verb *)
Lemma plus_resp_leEq : (x,y,z:R)(x [<=] y) -> (x[+]z) [<=] (y[+]z).
(* End_Tex_Verb *)
Unfold leEq.
Intros.
Intro.
Apply H.
Apply (plus_cancel_less ? ? ? ? H0).
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_leEq_lft : (x,y,z:R)(x [<=] y) -> (z[+]x) [<=] (z[+]y).
(* End_Tex_Verb *)
Intros.
Step x[+]z.
Stepr y[+]z.
Apply plus_resp_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_leEq : (x,y,z:R)(x [<=] y) -> (x[-]z) [<=] (y[-]z).
(* End_Tex_Verb *)
Intros.
Step x[+][--]z.
Stepr y[+][--]z.
Apply plus_resp_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_resp_leEq :  (x,y:R)(x [<=] y) -> ([--]y) [<=] ([--]x).
(* End_Tex_Verb *)
Unfold leEq.
Intros.
Intro.
Apply H.
Apply inv_cancel_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_leEq_rht :(x,y,z:R)(y [<=] x) -> ((z[-]x) [<=] (z[-]y)).
(* End_Tex_Verb *)
Intros.
Transparent cg_minus.
Unfold cg_minus.
Apply plus_resp_leEq_lft.
Apply inv_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_leEq_both : (x,y,a,b:R)(x [<=] y)->(a [<=] b)
	->(x [+] a [<=] y [+] b).
(* End_Tex_Verb *)
 Intros.
 Apply leEq_transitive with y:=x [+] b.
 RStep a[+]x.
 RStepr b[+]x.
 Apply plus_resp_leEq.
 Assumption.
 Apply plus_resp_leEq.
 Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_less_leEq : (a,b,c,d:R)(a [<] b) -> (c [<=] d) ->
                                       ((a[+]c) [<] (b[+]d)).
(* End_Tex_Verb *)
Intros.
Apply leEq_less_trans with a[+]d.
Apply plus_resp_leEq_lft. Auto.
Apply plus_resp_less_rht. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_leEq_less : (a,b,c,d:R)(a [<=] b) -> (c [<] d) ->
                                       ((a[+]c) [<] (b[+]d)).
(* End_Tex_Verb *)
Intros.
Step c[+]a.
Stepr d[+]b.
Apply plus_resp_less_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_less_leEq :
  (x,y,x',y':R)(x [<=] y) -> (y' [<] x') -> (x[-]x' [<] y[-]y').
(* End_Tex_Verb *)
Intros.
Step x[+][--]x'.
Stepr y[+][--]y'.
Apply plus_resp_leEq_less.
Auto.
Apply inv_resp_less. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_leEq_both :
  (x,y,x',y':R)(x [<=] y) -> (y' [<=] x') -> (x[-]x' [<=] y[-]y').
(* End_Tex_Verb *)
Intros.
Step x[+][--]x'.
Stepr y[+][--]y'.
Apply plus_resp_leEq_both. Auto.
Apply inv_resp_leEq. Auto.
Qed.

(* Tex_Prose
\subsection*{Cancellation properties}
*)
(* Begin_Tex_Verb *)
Lemma plus_cancel_leEq_rht: (x,y,z:R)( (x[+]z) [<=] (y[+]z) )->
	(x[<=]y).
(* End_Tex_Verb *)
 Intros.
 RStep x[+]z[+]([--]z).
 RStepr y[+]z[+]([--]z).
 Apply plus_resp_leEq.
 Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_cancel_leEq:(x,y:R)([--]y[<=][--]x)->(x[<=]y).
(* End_Tex_Verb *)
 Intros.
 RStep [--][--]x.
 RStepr [--][--]y.
 Apply inv_resp_leEq.
 Assumption.
Qed.

(* Tex_Prose
\subsection*{Laws for shifting}
*)

(* Begin_Tex_Verb *)
Lemma shift_plus_leEq : (a,b,c:R)(a[<=]c[-]b)->(a[+]b[<=]c).
(* End_Tex_Verb *)
Intros.
RStepr c[-]b[+]b.
Apply plus_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_plus : (a,b,c:R)(a[-]b[<=]c)->(a[<=]c[+]b).
(* End_Tex_Verb *)
Intros.
RStep a[-]b[+]b.
Apply plus_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_plus_leEq' : (a,b,c:R)(b[<=]c[-]a)->(a[+]b[<=]c).
(* End_Tex_Verb *)
Intros.
RStepr a[+](c[-]a).
Apply plus_resp_leEq_lft.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_plus' : (a,b,c:R)(a[-]b [<=] c) -> (a[<=] b[+]c).
(* End_Tex_Verb *)
Intros.
RStep b[+](a[-]b).
Apply plus_resp_leEq_lft. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_rht: (a,b:R)(Zero [<=] b[-]a) -> (a [<=] b).
(* End_Tex_Verb *)
Intros.
Step Zero[+]a.
RStepr (b[-]a)[+]a.
Apply plus_resp_leEq. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_lft : (a,b:R)(a [<=] b) -> (Zero [<=] b[-]a).
(* End_Tex_Verb *)
Intros.
Step a[-]a.
Apply minus_resp_leEq. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_minus_leEq : (a,b,c:R)(a[<=]c[+]b)->(a[-]b[<=]c).
(* End_Tex_Verb *)
Intros.
RStepr (c[+]b)[-]b.
Apply minus_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_minus : (a,b,c:R)((a[+]c)[<=]b)->(a[<=](b[-]c)).
(* End_Tex_Verb *)
Intros.
RStep ((a[+]c)[-]c).
Apply minus_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_minus' : (a,b,c:R)((c[+]a)[<=]b)->(a[<=](b[-]c)).
(* End_Tex_Verb *)
Intros.
RStep ((c[+]a)[-]c).
Apply minus_resp_leEq.
Assumption.
Qed.

End addition.

Section multiplication.
(* Tex_Prose
\subsection{Multiplication and division}
*)

(* Tex_Prose
\subsection*{Multiplication and division respect $\leq$}
*)

(* Begin_Tex_Verb *)
Lemma mult_resp_leEq_rht:
            (x,y,z:R)(x [<=] y) -> (Zero [<=] z) -> (x[*]z) [<=] (y[*]z).
(* End_Tex_Verb *)
Unfold leEq.
Intros.
Intro.
Generalize (shift_zero_less_minus ? ? ? H1); Intro.
Cut Zero [<] (x[-]y)[*]z.
Intro.
2: RStepr x[*]z[-]y[*]z.
2: Assumption.
Cut (a,b:R)(Zero [<] a[*] b) ->
    ((Zero [<] a) * (Zero [<] b)) + ((a [<] Zero) * (b [<] Zero)).
Intros.
Generalize (H4 ? ? H3); Intro.
Elim H5; Intro H6.
Elim H6; Intros.
Elim H.
Step Zero[+]y.
Apply shift_plus_less.
Assumption.
Elim H6; Intros.
Elim H0.
Assumption.

Intros.
Generalize (Greater_imp_ap ? ? ? H4); Intro.
Generalize (mult_cancel_ap_zero_lft ? ? ? H5); Intro.
Generalize (mult_cancel_ap_zero_rht ? ? ? H5); Intro.
Elim (ap_imp_less ? ? ? H6); Intro.
Right.
Split.
Assumption.
Elim (ap_imp_less ? ? ? H7); Intro.
Assumption.
ElimType False.
Elim (less_irreflexive_unfolded R Zero).
Apply less_leEq_trans with a[*]b.
Assumption.
Apply less_leEq.
Apply inv_cancel_less.
Step (Zero::R).
Stepr ([--]a)[*]b.
Apply mult_resp_pos.
Step [--](Zero::R).
Apply inv_resp_less.
Assumption.
Assumption.
Left.
Split.
Assumption.
Elim (ap_imp_less ? ? ? H7); Intro.
ElimType False.
Elim (less_irreflexive_unfolded R Zero).
Apply less_leEq_trans with a[*]b.
Assumption.
Apply less_leEq.
Apply inv_cancel_less.
Step (Zero::R).
Stepr a[*][--]b.
Apply mult_resp_pos.
Assumption.
Step [--](Zero::R).
Apply inv_resp_less.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_resp_leEq_lft:
            (x,y,z:R)(x[<=]y)->(Zero[<=]z)-> (z[*]x[<=]z[*]y).
(* End_Tex_Verb *)
Intros.
Step x[*]z.
Stepr y[*]z.
Apply mult_resp_leEq_rht.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_resp_leEq_both : (x,x',y,y':R)(Zero[<=]x)->
  (Zero[<=]y)->(x[<=]x')->(y[<=]y')->(x[*]y[<=]x'[*]y').
(* End_Tex_Verb *)
Intros.
Apply leEq_transitive with x[*]y'.
Apply mult_resp_leEq_lft; Assumption.
Apply mult_resp_leEq_rht.
Assumption.
Apply leEq_transitive with y; Assumption.
Qed.


(* Begin_Tex_Verb *)
Lemma recip_resp_leEq : (x,y:R)(x_:x[#]Zero)(y_:y[#]Zero)
                        (Zero[<]y) -> (y[<=]x) ->
                        (One[/]x[//]x_ [<=] One[/]y[//]y_).
(* End_Tex_Verb *)
Unfold leEq.
Intros. Intro. Apply H0.
Cut One[/]x[//]x_ [#] Zero. Intro x'_.
Cut One[/]y[//]y_ [#] Zero. Intro y'_.
RStep One[/](One[/]x[//]x_)[//]x'_.
RStepr One[/](One[/]y[//]y_)[//]y'_.
Apply recip_resp_less.
Apply recip_resp_pos; Auto.
Auto.
Apply div_resp_ap_zero_rev. Apply ring_non_triv.
Apply div_resp_ap_zero_rev. Apply ring_non_triv.
Qed.

(* Begin_Tex_Verb *)
Lemma div_resp_leEq : (x,y,z:R)(z_:z[#]Zero)
  (Zero[<]z)->(x[<=]y)->((x[/]z[//]z_)[<=](y[/]z[//]z_)).
(* End_Tex_Verb *)
Intros.
RStep (x[*](One[/]z[//]z_)).
RStepr (y[*](One[/]z[//]z_)).
Apply mult_resp_leEq_rht.
Assumption.
Apply less_leEq.
Apply recip_resp_pos.
Auto.
Qed.

Hints Resolve recip_resp_leEq : algebra.

(* Tex_Prose
\subsection*{Cancellation properties}
*)

(* Begin_Tex_Verb *)
Lemma mult_cancel_leEq : (x,y,z:R)(Zero [<] z) ->
                         ((x[*]z) [<=] (y[*]z)) -> (x [<=] y).
(* End_Tex_Verb *)
Unfold leEq.
Intros.
Intro.
Apply H0.
Apply mult_resp_less.
Assumption.
Assumption.
Qed.

(* Tex_Prose
\subsection*{Laws for shifting}
*)

(* Begin_Tex_Verb *)
Lemma shift_mult_leEq : (x,y,z:R)(Zero[<]z)->
  (z_:z[#]Zero)(x[<=]y[/]z[//]z_)->(x[*]z)[<=]y.
(* End_Tex_Verb *)
Intros.
RStepr (y[/]z[//]z_)[*]z.
Apply mult_resp_leEq_rht; [Assumption | Apply less_leEq; Assumption].
Qed.

(* Begin_Tex_Verb *)
Lemma shift_mult_leEq' : (x,y,z:R)(Zero[<]z)->
  (z_:z[#]Zero)(x[<=]y[/]z[//]z_)->(z[*]x)[<=]y.
(* End_Tex_Verb *)
Intros.
RStepr z[*](y[/]z[//]z_).
Apply mult_resp_leEq_lft; [Assumption | Apply less_leEq; Assumption].
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_mult' :
                 (x,y,z:R)(H:y[#]Zero)(Zero[<]y) ->
                 (x[/]y[//]H [<=] z) -> (x [<=] y[*]z).
(* End_Tex_Verb *)
Unfold leEq. Intros. Intro. Apply H1.
Apply shift_less_div. Auto.
Step y[*]z. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_div_leEq : (x,y,z:R)(Zero[<]z)->
  (z_:z[#]Zero)(x[<=]y[*]z)->(x[/]z[//]z_)[<=]y.
(* End_Tex_Verb *)
Intros.
RStepr (y[*]z)[/]z[//]z_.
Apply div_resp_leEq.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_div_leEq' : (x,y,z:R)(Zero[<]z)->
  (z_:z[#]Zero)(x[<=]z[*]y)->(x[/]z[//]z_)[<=]y.
(* End_Tex_Verb *)
Intros.
RStepr (z[*]y)[/]z[//]z_.
Apply div_resp_leEq.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma shift_leEq_div :
                 (x,y,z:R)(H:y[#]Zero)(Zero[<]y) ->
                 (x[*]y [<=] z) -> (x [<=] z[/]y[//]H).
(* End_Tex_Verb *)
Unfold leEq. Intros. Intro. Apply H1.
Stepr y[*]x.
Apply shift_less_mult' with H; Auto.
Qed.

Hints Resolve shift_leEq_div : algebra.

(* Begin_Tex_Verb *)
Lemma eps_div_leEq_eps : (eps,d:R)(d_:d [#] Zero)
                         (Zero[<=]eps) -> (One [<=] d) ->
                         ((eps[/]d[//]d_)[<=]eps).
(* End_Tex_Verb *)
Intros.
Apply shift_div_leEq'.
Apply less_leEq_trans with (One::R).
Apply pos_one.

Assumption.

Step One[*]eps.
Apply mult_resp_leEq_rht.
Assumption.

Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma nonneg_div_two : (eps:R)(Zero [<=] eps) -> (Zero [<=] (eps[/]TwoNZ)).
(* End_Tex_Verb *)
Intros.
Apply shift_leEq_div.
Apply pos_two.

Step (Zero::R).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma nonneg_div_two' : (eps:R)(Zero[<=]eps)->(eps[/]TwoNZ)[<=]eps.
(* End_Tex_Verb *)
Intros.
Apply shift_div_leEq.
Apply pos_two.
Step eps[+]Zero; RStepr eps[+]eps.
Apply plus_resp_leEq_lft; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nonneg_div_three : (eps:R)(Zero[<=]eps)->Zero[<=](eps[/]ThreeNZ).
(* End_Tex_Verb *)
Intros.
Apply mult_cancel_leEq with (Three::R).
Apply pos_three.
Step (Zero::R); RStepr eps.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma nonneg_div_three' : (eps:R)(Zero[<=]eps)->(eps[/]ThreeNZ)[<=]eps.
(* End_Tex_Verb *)
Intros.
Apply shift_div_leEq.
Apply pos_three.
RStep eps[+]Zero[+]Zero; RStepr eps[+]eps[+]eps.
Repeat Apply plus_resp_leEq_both; Auto.
Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma nonneg_div_four : (eps:R)(Zero[<=]eps)->(Zero[<=]eps[/]FourNZ).
(* End_Tex_Verb *)
Intros.
RStepr (eps[/]TwoNZ)[/]TwoNZ.
Apply nonneg_div_two; Apply nonneg_div_two; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma nonneg_div_four' : (eps:R)(Zero[<=]eps)->(eps[/]FourNZ[<=]eps).
(* End_Tex_Verb *)
Intros.
RStep (eps[/]TwoNZ)[/]TwoNZ.
Apply leEq_transitive with eps[/]TwoNZ.
2: Apply nonneg_div_two'; Assumption.
Apply nonneg_div_two'.
Apply nonneg_div_two.
Assumption.
Qed.

End multiplication.

Section misc.
(* Tex_Prose
\subsection{Miscellaneous}
*)

(* Begin_Tex_Verb *)
Lemma sqr_nonneg: (x:R) Zero [<=] (x[^](2)).
(* End_Tex_Verb *)
Unfold leEq. Intros. Intro.
Cut Zero [<] x[^](2). Intro.
Elim (less_antisymmetric_unfolded ? ? ? H H0).
Cut (x [<] Zero) + (Zero [<] x). Intro. Elim H0; Clear H0; Intros H0.
RStepr ([--]x)[*]([--]x).
Cut Zero [<] [--]x. Intro.
Apply mult_resp_pos; Auto.
Step [--](Zero::R). Apply inv_resp_less. Auto.
RStepr x[*]x.
Apply mult_resp_pos; Auto.
Apply ap_imp_less.
Apply cring_mult_ap_zero with x.
Step x[^](2).
Apply less_imp_ap. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nring_nonneg : (n:nat)(Zero[<=](!nring R n)).
(* End_Tex_Verb *)
Intro; Induction n.
Apply leEq_reflexive.
Apply leEq_transitive with (!nring R n); [Assumption | Apply less_leEq; Simpl; Apply less_plusOne].
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_nring : (n,m:nat)((!nring R n)[<=](nring m))->(le n m).
(* End_Tex_Verb *)
Intro n; Induction n.
Intros.
Auto with arith.
Intros.
Induction m.
ElimType False.
Cut (!nring R n)[<]Zero.
Change (nring O)[<=](!nring R n).
Apply nring_leEq.
Auto with arith.
Change (nring n)[<](!nring R O).
Apply nring_less.
Apply lt_le_trans with (S n).
Auto with arith.
ElimType False; Apply H.
Apply nring_less; Auto with arith.
Cut (le n m).
Auto with arith.
Apply Hrecn.
RStepr ((!nring R m)[+]One)[-]One.
Apply shift_leEq_minus.
Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma cc_abs_aid: (x,y:R)(Zero [<=] ((x[^](2)) [+] (y[^](2)))).
(* End_Tex_Verb *)
Intros.
Step Zero[+](Zero::R).
Apply plus_resp_leEq_both; Apply sqr_nonneg.
Qed.

Load Transparent_algebra.

(* Begin_Tex_Verb *)
Lemma nexp_resp_pos : (x:R)(k:nat)(Zero [<] x)->(Zero [<] x[^]k).
(* End_Tex_Verb *)
Intros.
Elim k.
Simpl.
Apply pos_one.
Intros.
Simpl.
Apply mult_resp_pos.
Assumption.
Assumption.
Qed.

Load Opaque_algebra.

(* Begin_Tex_Verb *)
Lemma mult_resp_nonneg : (x,y:R)(Zero[<=]x) -> (Zero[<=]y) ->
                                (Zero[<=] x[*]y).
(* End_Tex_Verb *)
Unfold leEq. Intros. Intro. Apply H0.
Cut x[*]y [#] Zero. Intro.
Cut x [#] Zero. Intro.
Cut y [#] Zero. Intro.
Elim (ap_imp_less ? ? ? H4); Intro H5. Auto.
Elim (ap_imp_less ? ? ? H3); Intro H6. Elim (H H6).
Elim (less_antisymmetric_unfolded ? ? ? H1 (mult_resp_pos ? ? ? H6 H5)).
Apply cring_mult_ap_zero_op with x. Auto.
Apply cring_mult_ap_zero with y. Auto.
Apply less_imp_ap. Auto.
Qed.

Load Transparent_algebra.

(* Begin_Tex_Verb *)
Lemma nexp_resp_nonneg : (x:R)(k:nat)(Zero [<=] x)->(Zero [<=] x[^]k).
(* End_Tex_Verb *)
Intros. Induction k. Intros.
Stepr (One::R). Apply less_leEq. Apply pos_one.
Stepr x[^]k[*]x.
Apply mult_resp_nonneg; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma power_resp_leEq : (x,y:R)(k:nat)
  (Zero [<=] x)->(x [<=] y)->(x[^]k [<=] y[^]k).
(* End_Tex_Verb *)
Intros. Induction k; Intros.
Step (One::R).
Stepr (One::R).
Apply leEq_reflexive.
Step x[^]k[*]x.
Stepr y[^]k[*]y.
Apply leEq_transitive with x[^]k[*]y.
Apply mult_resp_leEq_lft. Auto.
Apply nexp_resp_nonneg; Auto.
Apply mult_resp_leEq_rht. Auto.
Apply leEq_transitive with x; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_resp_less : (x,y:R)(n:nat)(le (1) n) -> (Zero [<=] x) ->
                             (x [<] y) -> x[^]n [<] y[^]n.
(* End_Tex_Verb *)
Intros.
Induction n.
ElimType False.
Inversion H.
Elim n.
Simpl.
Step x.
Stepr y.
Assumption.
Intros.
Change x[^](S n0) [*] x [<] y[^](S n0) [*] y.
Apply mult_resp_less_both.
Apply nexp_resp_nonneg.
Assumption.
Assumption.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma power_cancel_leEq : (x,y:R)(k:nat)(lt O k) ->
  (Zero [<=] y)->(x[^]k [<=] y[^]k)->(x [<=] y).
(* End_Tex_Verb *)
Unfold leEq. Intros. Intro. Apply H1.
Apply nexp_resp_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma power_cancel_less : (x,y:R)(k:nat)
  (Zero [<=] y)->(x[^]k [<] y[^]k)->(x [<] y).
(* End_Tex_Verb *)
Intros.
Elim (zerop k); Intro y0.
Rewrite y0 in H0.
Cut One [<] (One::R). Intro.
Elim (less_irreflexive_unfolded ? ? H1).
Step x[^](0). Stepr y[^](0). Auto.
Cut (x [<] y) + (y [<] x). Intro.
Elim H1; Clear H1; Intros H1. Auto.
Cut (x [<=] y). Intro. Elim (H2 H1).
Apply power_cancel_leEq with k; Auto.
Apply less_leEq. Auto.
Apply ap_imp_less. Apply un_op_strext_unfolded with (!nexp_op R k).
Apply less_imp_ap. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_resp_leEq : (f,g:nat->R)(a,b:nat)(le a (S b)) ->
                      ((i:nat)(le a i) -> (le i b) -> (f i) [<=] (g i)) ->
                      (Sum a b f) [<=] (Sum a b g).
(* End_Tex_Verb *)
Intros. Induction b; Intros.
Unfold Sum. Unfold Sum1.
Generalize (toCle ?? H); Clear H; Intro H.
Inversion H.
Step (Zero::R).
Stepr (Zero::R).
Apply leEq_reflexive.
Inversion H2.
Simpl.
RStep (f (0)).
RStepr (g (0)).
Apply H0; Auto. Rewrite H3. Auto.
Elim (le_lt_eq_dec ? ? H); Intro H1.
Apply leEq_wdl with (Sum a b f)[+](f (S b)).
Apply leEq_wdr with (Sum a b g)[+](g (S b)).
Apply plus_resp_leEq_both.
Apply Hrecb. Auto with arith. Auto.
Apply H0. Auto with arith. Auto.
Apply eq_symmetric_unfolded. Apply Sum_last.
Apply eq_symmetric_unfolded. Apply Sum_last.
Unfold Sum. Unfold Sum1.
Rewrite H1.
Simpl.
Step (Zero::R).
Stepr (Zero::R).
Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_resp_leEq : (n:nat)(f,g:(i:nat)(lt i n)->R)
  ((i:nat)(H:(lt i n))(f i H)[<=](g i H))->((Sumx f)[<=](Sumx g)).
(* End_Tex_Verb *)
Induction n.
Intros; Simpl; Apply leEq_reflexive.
Clear n; Intros; Simpl.
Apply plus_resp_leEq_both.
Apply H; Intros; Apply H0.
Apply H0.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum2_resp_leEq : (m,n:nat)(le m (S n))->
  (f,g:(i:nat)(le m i)->(le i n)->R)
  ((i:nat)(Hm:(le m i))(Hn:(le i n))(f i Hm Hn)[<=](g i Hm Hn))->
  (Sum2 f)[<=](Sum2 g).
(* End_Tex_Verb *)
Intros.
Unfold Sum2.
Apply Sum_resp_leEq.
Assumption.
Intros.
Elim (le_lt_dec m i); Intro; [Simpl | ElimType False; Apply (le_not_lt m i); Auto with arith].
Elim (le_lt_dec i n); Intro; [Simpl | ElimType False; Apply (le_not_lt i n); Auto with arith].
Apply H0.
Qed.

(* Begin_Tex_Verb *)
Lemma approach_zero:(x:R)((e:R)(Zero[<]e)->(x[<]e))->
			(Not (Zero[<]x)).
(* End_Tex_Verb *)
 Intros.
 Intro.
 Cut (x[<](x[/]TwoNZ)).
 Change (Not (x [<] x[/]TwoNZ)).
 Apply less_antisymmetric_unfolded.
 Apply plus_cancel_less with z:=[--]x[/]TwoNZ.
 Apply mult_cancel_less with z:=(Two::R).
 Apply pos_two.
 RStep (Zero::R).
 RStepr x.
 Assumption.
 Apply H.
 Apply pos_div_two.
 Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma approach_zero_weak:(x:R)((e:R)(Zero [<] e)-> x [<=] e)->
                              (Not (Zero [<] x)).
(* End_Tex_Verb *)
 Intros.
 Intro.
 Cut (x[<=](x[/]TwoNZ)).
 Change ~(Not (x[/]TwoNZ [<] x)).
 Intro.
 Apply H1.
 Apply plus_cancel_less with z:=[--]x[/]TwoNZ.
 Apply mult_cancel_less with z:=(Two::R).
 Apply pos_two.
 RStep (Zero::R).
 RStepr x.
 Assumption.
 Apply H.
 Apply pos_div_two.
 Assumption.
Qed.
End misc.

(* Begin_Tex_Verb *)
Lemma equal_less_leEq : (a,b,x,y:R)
  ((a[<]b)->(x[<=]y))->((a[=]b)->(x[<=]y))->
  (a[<=]b)->(x[<=]y).
(* End_Tex_Verb *)
Intros.
Red.
Apply CNot_not_or with a[<]b a[=]b; Auto.
Intro.
Cut a[=]b; Intros.
2: Apply leEq_imp_eq; Auto.
Auto.
Intro; Auto.
Qed.

End Properties_of_leEq.

(***********************************)
Section PosP_properties.
(***********************************)

(* Tex_Prose
\section{Properties of positive numbers}
*)

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}.
\end{convention}
*)
Variable R : COrdField.

(* Begin_Tex_Verb *)
Syntactic Definition ZeroR := (Zero::R).
Syntactic Definition OneR := (One::R).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma mult_pos_imp : (a,b:R)(Zero [<] a[*] b) ->
    ((Zero [<] a) * (Zero [<] b)) + ((a [<] Zero) * (b [<] Zero)).
(* End_Tex_Verb *)
Generalize I; Intro.
Generalize I; Intro.
Generalize I; Intro.
Generalize I; Intro.
Generalize I; Intro.
Intros.
Generalize (Greater_imp_ap ? ? ? H4); Intro.
Generalize (mult_cancel_ap_zero_lft ? ? ? H5); Intro.
Generalize (mult_cancel_ap_zero_rht ? ? ? H5); Intro.
Elim (ap_imp_less ? ? ? H6); Intro.
Right.
Split.
Assumption.
Elim (ap_imp_less ? ? ? H7); Intro.
Assumption.
ElimType False.
Elim (less_irreflexive_unfolded R Zero).
Apply less_leEq_trans with a[*]b.
Assumption.
Apply less_leEq.
Apply inv_cancel_less.
Step (Zero::R).
Stepr ([--]a)[*]b.
Apply mult_resp_pos.
Step [--](Zero::R).
Apply inv_resp_less.
Assumption.
Assumption.
Left.
Split.
Assumption.
Elim (ap_imp_less ? ? ? H7); Intro.
ElimType False.
Elim (less_irreflexive_unfolded R Zero).
Apply less_leEq_trans with a[*]b.
Assumption.
Apply less_leEq.
Apply inv_cancel_less.
Step (Zero::R).
Stepr a[*][--]b.
Apply mult_resp_pos.
Assumption.
Step [--](Zero::R).
Apply inv_resp_less.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_pos_nonneg :
       (x,y:R)(Zero [<] x) -> (Zero [<=] y) -> (Zero [<] x[+]y).
(* End_Tex_Verb *)
Intros.
Apply less_leEq_trans with x. Auto.
Step x[+]Zero.
Apply plus_resp_leEq_lft. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_nonneg_pos :
       (x,y:R)(Zero [<=] x) -> (Zero [<] y) -> (Zero [<] x[+]y).
(* End_Tex_Verb *)
Intros.
Stepr y[+]x.
Apply plus_resp_pos_nonneg; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_square : (x:R)(x [#] Zero)->(Zero [<] x[^](2)).
(* End_Tex_Verb *)
Intros.
Elim (ap_imp_less ??? H); Intro H1.
RStepr ([--]x)[*]([--]x).
Cut Zero [<] [--]x. Intro.
Apply mult_resp_pos; Auto.
Step [--](Zero::R).
Apply inv_resp_less. Auto.
RStepr x[*]x.
Apply mult_resp_pos; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_cancel_pos_rht : (x,y:R)
  (Zero [<] x[*]y)->(Zero [<=] x)->(Zero [<] y).
(* End_Tex_Verb *)
Intros.
Elim (mult_pos_imp ?? H); Intro H1.
Elim H1; Auto.
Elim H1; Intros.
Elim (H0 a).
Qed.

(* Begin_Tex_Verb *)
Lemma mult_cancel_pos_lft : (x,y:R)
  (Zero [<] x[*]y)->(Zero [<=] y)->(Zero [<] x).
(* End_Tex_Verb *)
Intros.
Apply mult_cancel_pos_rht with y.
Stepr x[*]y.
Auto. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_wd : (x,y:R)(x [=] y)->(Zero [<] y)->(Zero [<] x).
(* End_Tex_Verb *)
Intros.
Stepr y.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma even_power_pos : (n:nat)(even n) -> 
  (x:R)(x [#] Zero) -> (Zero [<] x[^]n).
(* End_Tex_Verb *)
Intros.
Elim (even_2n n H). Intros m y.
Replace n with (mult (2) m).
Stepr (x[^](2))[^]m.
Apply nexp_resp_pos.
Apply pos_square. Auto.
Rewrite y. Unfold double. Omega.
Qed.


(* Begin_Tex_Verb *)
Lemma odd_power_cancel_pos : (n:nat)(odd n)->
  (x:R)(Zero [<] x[^]n)->(Zero [<] x).
(* End_Tex_Verb *)
Intros.
Induction n.
Generalize (to_Codd ? H); Intro.
Inversion H1.
Apply mult_cancel_pos_rht with x[^]n.
Stepr x[^](S n). Auto.
Apply less_leEq; Apply even_power_pos.
Inversion H. Auto.
Apply un_op_strext_unfolded with (!nexp_op R (S n)).
Cut (lt (0) (S n)). Intro.
Stepr (Zero::R).
Apply Greater_imp_ap. Auto.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_pos : (x,y:R)(Zero [<] x)->(Zero [<] y)->(Zero [<] x[+]y).
(* End_Tex_Verb *)
Intros.
Apply plus_resp_pos_nonneg.
Auto.
Apply less_leEq. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_nring_S: (n:nat)((Zero::R) [<] (nring (S n))).
(* End_Tex_Verb *)
Induction n; Simpl; Intros.
(* base *)
Stepr (One::R); Apply pos_one.
(* step *)
Apply less_leEq_trans with (!nring R n0)[+]One.
Assumption.
Apply less_leEq.
Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma square_eq_pos : (x,a:R)(Zero[<]a)->
  (Zero[<]x)->(x[^](2)[=]a[^](2))->(x[=]a).
(* End_Tex_Verb *)
Intros.
Elim (square_eq ? x a); Intros; Auto.
ElimType False.
Apply less_irreflexive_unfolded with x:=(Zero::R).
Apply less_leEq_trans with x.
Auto.
Apply less_leEq.
Step [--]a; Apply inv_cancel_less.
Step (Zero::R); Stepr a; Auto.
Apply Greater_imp_ap; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma square_eq_neg : (x,a:R)(Zero[<]a)->
  (x[<]Zero)->(x[^](2)[=]a[^](2))->(x[=][--]a).
(* End_Tex_Verb *)
Intros.
Elim (square_eq ? x a); Intros; Auto.
ElimType False.
Apply less_irreflexive_unfolded with x:=(Zero::R).
Apply leEq_less_trans with x.
Stepr a; Apply less_leEq; Auto.
Auto.
Apply Greater_imp_ap; Auto.
Qed.

End PosP_properties.

Hints Resolve mult_resp_nonneg.

(* Tex_Prose
\section{Properties of {\tt AbsSmall}}
*)

(* Begin_SpecReals *)

(* Begin_Tex_Verb *)
Definition AbsSmall [R:COrdField;e,x:R]: Prop := ([--]e [<=] x) /\ (x [<=] e).
(* End_Tex_Verb *)

Implicits AbsSmall [1].

(* End_SpecReals *)

(***********************************)
Section AbsSmall_properties.
(***********************************)

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}.
\end{convention}
*)
Variable R : COrdField.

(* Begin_Tex_Verb *)
Lemma AbsSmall_wd_rht : (rel_well_def_rht R (!AbsSmall R)).
(* End_Tex_Verb *)
Unfold rel_well_def_rht.
Unfold AbsSmall.
Intros.
(Elim H; Intros).
Split.
Stepr y.
Assumption.

Step y.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_wd_rht_unfolded : (x,y,z:R)(AbsSmall x y)->(y[=]z)->
                                 (AbsSmall x z).
(* End_Tex_Verb *)
Proof AbsSmall_wd_rht.

(* Begin_Tex_Verb *)
Lemma AbsSmall_wd_lft : (rel_well_def_lft R (!AbsSmall R)).
(* End_Tex_Verb *)
Unfold rel_well_def_lft.
Unfold AbsSmall.
Intros.
(Elim H; Intros).
Split.
Step ([--]x).
Assumption.

Stepr x.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_wd_lft_unfolded : (x,y,z:R)(AbsSmall x y)->(x[=]z)->
                                 (AbsSmall z y).
(* End_Tex_Verb *)
Proof AbsSmall_wd_lft.

(* Begin_Tex_Verb *)
Syntactic Definition ZeroR := (Zero::R).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma AbsSmall_leEq_trans :  (e1,e2,d:R)(e1 [<=] e2) ->
                             (AbsSmall e1 d) -> (AbsSmall e2 d).
(* End_Tex_Verb *)
Unfold AbsSmall.
Intros.
(Elim H0; Intros).
Split.
Apply leEq_transitive with ([--]e1).
Apply inv_resp_leEq.
Assumption.

Assumption.

Apply leEq_transitive with e1.
Assumption.

Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma zero_AbsSmall: (e:R)(Zero[<=]e)->(AbsSmall e Zero).
(* End_Tex_Verb *)
Intros.
Unfold AbsSmall.
Split.
Stepr ([--](Zero::R)).
Apply inv_resp_leEq.
Assumption.
Assumption.
Qed.

Lemma AbsSmall_trans :  (e1,e2,d:R)(e1 [<] e2) ->
                        (AbsSmall e1 d) -> (AbsSmall e2 d).
Intros.
Apply AbsSmall_leEq_trans with e1.
Apply less_leEq.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_imp_AbsSmall : (e,d:R)(Zero [<=] e) -> (e [<=] d) ->
                           (AbsSmall d e).
(* End_Tex_Verb *)
Intros.
Unfold AbsSmall.
Split; Try Assumption.
Apply leEq_transitive with ZeroR; Try Assumption.
Stepr [--]ZeroR.
Apply inv_resp_leEq.
Apply leEq_transitive with e; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_resp_AbsSmall: (x,y:R)(AbsSmall x y) -> (AbsSmall x [--]y).
(* End_Tex_Verb *)
Unfold AbsSmall.
Intros.
Elim H; Intros.
Split.
Apply inv_resp_leEq.
Assumption.
Stepr [--]([--]x).
Apply inv_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_minus : (e,x1,x2:R)
                       (AbsSmall e (x1[-]x2)) -> (AbsSmall e (x2[-]x1)).
(* End_Tex_Verb *)
Intros.
RStepr [--](x1[-]x2).
Apply inv_resp_AbsSmall.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_plus : (e1,e2,x1,x2:R)
                      (AbsSmall e1 x1) -> (AbsSmall e2 x2) ->
                      (AbsSmall (e1[+]e2) (x1[+]x2)).
(* End_Tex_Verb *)
Unfold AbsSmall.
Intros.
Elim H; Intros.
Elim H0; Intros.
Split.
RStep ([--]e1) [+] ([--]e2).
Apply plus_resp_leEq_both; Assumption.
Apply plus_resp_leEq_both; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_eps_div_two : (e,x1,x2:R)
                             (AbsSmall (e[/]TwoNZ) x1) ->
                             (AbsSmall (e[/]TwoNZ) x2) ->
                             (AbsSmall e (x1[+]x2)).
(* End_Tex_Verb *)
Intros.
RStep (e[/]TwoNZ [+] e[/]TwoNZ).
Apply AbsSmall_plus.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_x_plus_delta : (x,eps,delta:R)
               (Zero [<=] eps) -> (Zero [<=] delta) -> (delta[<=]eps) ->
               (AbsSmall eps (x[-](x[+]delta))).
(* End_Tex_Verb *)
Intros.
(* Stepr ((x[-]x)[-]delta).
Stepr (Zero [-] delta). *)
RStepr ([--] delta).
Apply inv_resp_AbsSmall.
Apply leEq_imp_AbsSmall.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_x_minus_delta : (x,eps,delta:R)
                  (Zero [<=] eps) -> (Zero[<=] delta) -> (delta[<=]eps) ->
                  (AbsSmall eps (x[-](x[-]delta))).
(* End_Tex_Verb *)
Intros.
(* Stepr ((x[-]x)[+]delta).
   Stepr (Zero [+] delta). *)
RStepr delta.
Apply leEq_imp_AbsSmall.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_x_plus_eps_div2 : (x,eps:R)(Zero [<=] eps)->
                    (AbsSmall eps (x[-](x[+]eps[/]TwoNZ))).
(* End_Tex_Verb *)
Intros.
Apply AbsSmall_x_plus_delta.
Assumption.

Apply nonneg_div_two.
Assumption.

Apply nonneg_div_two'.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_x_minus_eps_div2 : (x,eps:R)(Zero [<=] eps)->
                     (AbsSmall eps (x[-](x[-]eps[/]TwoNZ))).
(* End_Tex_Verb *)
Intros.
Apply AbsSmall_x_minus_delta.
Assumption.

Apply nonneg_div_two.
Assumption.

Apply eps_div_leEq_eps.
Assumption.

Apply less_leEq.
Apply one_less_two.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_intermediate : (x,y,z,eps:R)(x [<=] y)->(y[<=]z)->
                              (AbsSmall eps (z[-]x)) -> (AbsSmall eps (z[-]y)).
(* End_Tex_Verb *)
Intros.
Apply leEq_imp_AbsSmall.
Apply shift_leEq_minus; Step y.
Assumption.
Unfold AbsSmall in H1.
Elim H1; Intros.
Apply leEq_transitive with z[-]x; Try Assumption.
Apply minus_resp_leEq_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_eps_div2 : (eps:R)(Zero [<=] eps)->
                          (AbsSmall eps (eps[/]TwoNZ)).
(* End_Tex_Verb *)
Intros.
Apply leEq_imp_AbsSmall.
Apply nonneg_div_two.
Assumption.

Apply eps_div_leEq_eps.
Assumption.

Apply less_leEq.
Apply one_less_two.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_nonneg: (e,x:R)(AbsSmall e x)->(Zero[<=]e).
(* End_Tex_Verb *)
 Unfold AbsSmall.
 Intros.
 Elim H.
 Intros.
 Cut ([--]e [<=] e).
 Intros.
 Apply mult_cancel_leEq with z:=(Two::R).
 Apply pos_two.
 Apply plus_cancel_leEq_rht with z:=[--]e.
 RStep [--]e.
 RStepr e.
 Assumption.
 Apply leEq_transitive with y:=x.
 Assumption.
 Assumption.
Qed.


(* Begin_Tex_Verb *)
Lemma AbsSmall_mult :(e1,e2,x1,x2: R)(AbsSmall e1 x1)->
	(AbsSmall e2 x2)->(AbsSmall Three[*](e1[*]e2) x1[*]x2).
(* End_Tex_Verb *)
 Unfold AbsSmall.
 Intros.
 Elim H.
 Intros.
 Elim H0.
 Intros.
 Cut (Zero[<=]e1).
 Intro.
 Cut (Zero[<=]e2).
 Intro.
 Split.

 Apply plus_cancel_leEq_rht with z:=(Three[*](e1[*]e2)).
 RStep (Zero::R).
 RStepr x1[*]x2[+](e1[*]e2)[+](e1[*]e2)[+](e1[*]e2).
 Apply leEq_transitive with
   	 y:= x1[*]x2[+](e1[*]e2)[+](x1[*]e2)[+](e1[*]x2).
 RStepr (e1[+]x1)[*](e2[+]x2).
 Apply mult_resp_nonneg.
 Apply plus_cancel_leEq_rht with z:=[--]x1.
 RStep [--]x1.
 RStepr [--]([--]e1).
 Apply inv_resp_leEq.
 Assumption.

 Apply plus_cancel_leEq_rht with z:=[--]x2.
 RStep [--]x2.
 RStepr [--]([--]e2).
 Apply inv_resp_leEq.
 Assumption.

 RStep (x1[*]x2[+]e1[*]e2)[+](x1[*]e2[+]e1[*]x2).
 RStepr (x1[*]x2[+]e1[*]e2)[+](e1[*]e2[+]e1[*]e2).
 Apply plus_resp_leEq_lft.
 Apply plus_resp_leEq_both.
 Apply mult_resp_leEq_rht.
 Assumption.
 Assumption.
 Apply mult_resp_leEq_lft.
 Assumption.
 Assumption.

 Apply plus_cancel_leEq_rht with z:=[--](x1[*]x2).
 RStep (Zero::R).
 RStepr [--](x1[*]x2)[+](e1[*]e2)[+]((e1[*]e2)[+](e1[*]e2)).
 Apply leEq_transitive with
   	 y:= [--](x1[*]x2)[+](e1[*]e2)[+]((x1[*]e2)[-](e1[*]x2)).
 RStepr (e1[+]x1)[*](e2[-]x2).
 Apply mult_resp_nonneg.
 Apply plus_cancel_leEq_rht with z:=[--]x1.
 RStep [--]x1.
 RStepr [--]([--]e1).
 Apply inv_resp_leEq.
 Assumption.

 Apply plus_cancel_leEq_rht with z:=x2.
 RStep x2.
 RStepr e2.
 Assumption.

 Apply plus_resp_leEq_lft.
 RStep  x1[*]e2[+]([--]e1[*]x2).
 Apply plus_resp_leEq_both.
 Apply mult_resp_leEq_rht.
 Assumption.
 Assumption.
 RStep e1[*]([--]x2).
 Apply mult_resp_leEq_lft.
 RStepr [--]([--]e2).
 Apply inv_resp_leEq.
 Assumption.
 Assumption.

 Apply AbsSmall_nonneg with e:=e2 x:=x2.
 Assumption.
 Apply AbsSmall_nonneg with e:=e1 x:=x1.
 Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_cancel_mult:(e,x,z:R)(Zero[<]z)->
			(AbsSmall e[*]z x[*]z)->(AbsSmall e x).
(* End_Tex_Verb *)
 Unfold AbsSmall.
 Intros.
 Elim H0.
 Intros.
 Split.
 Apply mult_cancel_leEq with z:=z.
 Assumption.
 RStep [--](e[*]z).
 Assumption.
 Apply mult_cancel_leEq with z:=z.
 Assumption.
 Assumption.
Qed.

End AbsSmall_properties.

(* Tex_Prose
\section{Properties of one over successor}
\begin{convention}
Let \verb!R! be an ordered field.
\end{convention}
*)

(* Begin_Tex_Verb *)
Definition one_div_succ := [R:COrdField][i:nat](One [/] (Snring R i) [//] (nringS_ap_zero ? i))
                        :  (R:COrdField)(nat->R).
(* End_Tex_Verb *)

Implicits one_div_succ [1].

Section One_div_succ_properties.

Variable R:COrdField.

(* Begin_Tex_Verb *)
Lemma one_div_succ_resp_leEq :
      (m,n:nat)(le m n)->((!one_div_succ R n) [<=] (one_div_succ m)).
(* End_Tex_Verb *)
Unfold one_div_succ. Unfold Snring. Intros.
Apply recip_resp_leEq.
Apply pos_nring_S.
Apply nring_leEq.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma one_div_succ_pos : (i:nat)((Zero::R) [<] (one_div_succ i)).
(* End_Tex_Verb *)
Intro.
Unfold one_div_succ.
Unfold Snring.
Apply recip_resp_pos.
Apply nring_pos.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma one_div_succ_resp_less : (i,j:nat)(lt i j)->
                              ((one_div_succ j)[<](!one_div_succ R i)).
(* End_Tex_Verb *)
Intros.
Unfold one_div_succ. Unfold Snring. Intros.
Apply recip_resp_less.
Apply pos_nring_S.
Apply nring_less.
Auto with arith.
Qed.

End One_div_succ_properties.

(* Tex_Prose
\section{Properties of {\tt Half}}
*)

(* Begin_Tex_Verb *)
Definition Half := [R:COrdField](One::R)[/]TwoNZ.
(* End_Tex_Verb *)

Implicits Half [1].

Section Half_properties.

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}
\end{convention}
*)

Variable R : COrdField.

(* Begin_Tex_Verb *)
Lemma half_1 : (Half::R)[*]Two [=] One.
(* End_Tex_Verb *)
Unfold Half.
Apply div_1.
Qed.
Hints Resolve half_1 : algebra.

(* Begin_Tex_Verb *)
Lemma pos_half : ((Zero::R) [<] Half).
(* End_Tex_Verb *)
Apply mult_cancel_pos_lft with (Two::R).
Apply (pos_wd R Half[*]Two One).
Exact half_1.
Apply pos_one.
Apply less_leEq; Apply pos_two.
Qed.

(* Begin_Tex_Verb *)
Lemma half_1' : (x:R)((x[*]Half)[*]Two [=] x).
(* End_Tex_Verb *)
Intros.
Unfold Half.
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma half_2 : (Half::R)[+]Half [=] One.
(* End_Tex_Verb *)
Unfold Half.
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma half_lt1 : (Half::R)[<] One.
(* End_Tex_Verb *)
Stepr Half[+](Half::R).
RStep (Half::R)[+]Zero.
Apply plus_resp_less_lft.
Exact pos_half.
Exact half_2.
Qed.

(* Begin_Tex_Verb *)
Lemma half_3 : (x:R)(Zero [<] x) -> (Half[*]x [<] x).
(* End_Tex_Verb *)
Intros.
Stepr One[*]x.
Apply mult_resp_less; Auto.
Exact half_lt1.
Qed.

End Half_properties.
Hints Resolve half_1 half_1' half_2 : algebra.

(* Begin_SpecReals *)

Section OrdField_Cauchy.

(* Tex_Prose
\section{Cauchy}
*)

(* Tex_Prose
\begin{convention} Let {\tt R} be a {\tt COrdField}.
\end{convention}
*)
Variable R : COrdField.

Implicit Arguments On.

(* Begin_Tex_Verb *)
Definition Cauchy_prop [g:nat -> R]: CProp :=
   (e:R)(Zero [<] e) -> { N:nat | (m:nat)(le N m)
			   -> (AbsSmall e ((g m)[-](g N)))}.
(* End_Tex_Verb *)
Implicit Arguments Off.

(* Def. CauchyP, Build_CauchyP *)
(* Should be defined in terms of CauchyP *)
(* Implicit arguments turned off, because Coq makes a mess of it in combination
   with the coercions *)

(* Begin_Tex_Verb *)
Record CauchySeq : Set :=
  {CS_seq  :> nat -> R;
   CS_proof: (Cauchy_prop CS_seq)
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition SeqLimit [seq:nat->R; lim:R]: CProp :=
   (e:R)(Zero [<] e) -> { N:nat | (m:nat)(le N m)
			   -> (AbsSmall e ((seq m)[-]lim))}.
(* End_Tex_Verb *)

End OrdField_Cauchy.

Implicits SeqLimit [1].

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma CS_seq_plus:(R:COrdField; f,g:nat->R)(Cauchy_prop f)->(Cauchy_prop g)->
	(Cauchy_prop [m:nat]((f m)[+](g m))).
(* End_Tex_Verb *)
 Intros.
 Unfold Cauchy_prop.
 Intros.
 Unfold Cauchy_prop in H.
 Unfold Cauchy_prop in H0.
 Cut { N:nat | (m:nat)(le N m)->(AbsSmall e[/]FourNZ (f m)[-](f N))}.
 Intro.
 Cut { N:nat | (m:nat)(le N m)->(AbsSmall e[/]FourNZ (g m)[-](g N))}.
 Intro.
 Case H2.
 Intros N1 H21.
 Case H3.
 Intros N2 H31.
 Exists (plus N1 N2).
 Intros.
 RStep (e[/]TwoNZ)[+](e[/]TwoNZ).
 RStepr  (f m)[-](f (plus N1 N2))[+]((g m)[-](g (plus N1 N2))).
 Apply AbsSmall_plus.

  RStepr ((f m)[-](f N1))[+]((f N1)[-](f (plus N1 N2))).
  RStep (e[/]FourNZ)[+](e[/]FourNZ).
  Apply AbsSmall_plus.
  Apply H21.
  Apply le_trans with m:=(plus N1 N2).
  Apply le_plus_l.
  Assumption.
  Apply AbsSmall_minus.
  Apply H21.
  Apply le_plus_l.


  RStepr ((g m)[-](g N2))[+]((g N2)[-](g (plus N1 N2))).
  RStep (e[/]FourNZ)[+](e[/]FourNZ).
  Apply AbsSmall_plus.
  Apply H31.
  Apply le_trans with m:=(plus N1 N2).
  Apply le_plus_r.
  Assumption.
  Apply AbsSmall_minus.
  Apply H31.
  Apply le_plus_r.

 Apply H0.
  Apply mult_cancel_less with z:=(Four::R).
  Apply nring_pos.
  Apply lt_O_Sn.
  RStep (Zero::R).
  RStepr e.
  Assumption.

 Apply H.
  Apply mult_cancel_less with z:=(Four::R).
  Apply nring_pos.
  Apply lt_O_Sn.
  RStep (Zero::R).
  RStepr e.
  Assumption.
Qed.

Section Mult_AbsSmall.

Variable R : COrdField.

(* Begin_Tex_Verb *)
Lemma mult_AbsSmall'_rht :
  (x,y,C:R)(Zero [<=] C) ->
  ([--]C [<=] x) -> (x [<=] C) -> ([--]C [<=] y) -> (y [<=] C) ->
    (x[*]y [<=] Three[*]C[^](2)).
(* End_Tex_Verb *)
Intros.
Step Zero[+]x[*]y. Apply shift_plus_leEq.
Apply leEq_transitive with (C[+]x)[*](C[-]y).
Apply mult_resp_nonneg.
Apply shift_leEq_plus. Step [--]x. Stepr [--][--]C.
Apply inv_resp_leEq. Auto.
Apply shift_leEq_minus. Step y. Auto.
RStep C[^](2)[-]x[*]y[+]C[*](x[-]y).
RStepr C[^](2)[-]x[*]y[+]C[*](C[-][--]C).
Apply plus_resp_leEq_lft.
Apply mult_resp_leEq_lft.
Apply minus_resp_leEq_both.
Auto. Auto. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_AbsSmall_rht :
  (x,y,X,Y:R)(Zero [<=] X) -> (Zero [<=] Y) ->
  ([--]X [<=] x) -> (x [<=] X) -> ([--]Y [<=] y) -> (y [<=] Y) ->
    (x[*]y [<=] X[*]Y).
(* End_Tex_Verb *)
Intros.
Intro.
Cut Zero[<]x[*]y; Intros.
2: Apply leEq_less_trans with X[*]Y; Auto.
Cut x[*]y[#]Zero; Intros.
2: Apply pos_ap_zero; Auto.
Cut x[#]Zero; Intros.
2: Apply mult_cancel_ap_zero_lft with y; Auto.
Elim (ap_imp_less ??? H8); Intro.
Cut y[<]Zero; Intros.
2: Step [--][--]y; Stepr [--](Zero::R); Apply inv_resp_less.
2: Apply mult_cancel_pos_rht with [--]x.
2: Stepr x[*]y; Auto.
2: Step [--](Zero::R); Apply less_leEq; Apply inv_resp_less; Auto.
Apply (less_irreflexive_unfolded R One).
Apply leEq_less_trans with (X[*]Y)[/]?[//]H7.
RStepr (X[/]([--]x)[//](inv_resp_ap_zero ?? H8))[*](Y[/]([--]y)[//](inv_resp_ap_zero ?? (less_imp_ap ??? H9))).
Step One[*](One::R).
Apply mult_resp_leEq_both.
Apply less_leEq; Apply pos_one.
Apply less_leEq; Apply pos_one.
Apply shift_leEq_div.
Step [--](Zero::R); Apply inv_resp_less; Auto.
Step [--]x; Stepr [--][--]X; Apply inv_resp_leEq; Auto.
Apply shift_leEq_div.
Step [--](Zero::R); Apply inv_resp_less; Auto.
Step [--]y; Stepr [--][--]Y; Apply inv_resp_leEq; Auto.
Apply shift_div_less; Auto.
Stepr x[*]y; Auto.
Cut Zero[<]y; Intros.
2: Apply mult_cancel_pos_rht with x; Try Apply less_leEq; Auto.
Apply (less_irreflexive_unfolded R One).
Apply leEq_less_trans with (X[*]Y)[/]?[//]H7.
RStepr (X[/]x[//]H8)[*](Y[/]y[//](pos_ap_zero ?? H9)).
Step One[*](One::R).
Apply mult_resp_leEq_both.
Apply less_leEq; Apply pos_one.
Apply less_leEq; Apply pos_one.
Apply shift_leEq_div; Auto.
Step x; Auto.
Apply shift_leEq_div; Auto.
Step y; Auto.
Apply shift_div_less; Auto.
Stepr x[*]y; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_AbsSmall_lft :
  (x,y,X,Y:R)(Zero [<=] X) -> (Zero [<=] Y) ->
  ([--]X [<=] x) -> (x [<=] X) -> ([--]Y [<=] y) -> (y [<=] Y) ->
    ([--](X[*]Y) [<=] x[*]y).
(* End_Tex_Verb *)
Intros.
RStepr [--]([--]x[*]y).
Apply inv_resp_leEq.
Apply mult_AbsSmall_rht; Auto.
Apply inv_resp_leEq. Auto.
RStepr [--][--]X.
Apply inv_resp_leEq. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_AbsSmall :
  (x,y,X,Y:R)(AbsSmall X x) -> (AbsSmall Y y) -> (AbsSmall X[*]Y x[*]y).
(* End_Tex_Verb *)
Unfold AbsSmall.
Intros.
Elim H. Intros. Elim H0. Intros.
Cut Zero [<=] X. Intro. Cut Zero [<=] Y. Intro.
Split.
Apply mult_AbsSmall_lft; Auto.
Apply mult_AbsSmall_rht; Auto.
Apply AbsSmall_nonneg with y; Auto.
Apply AbsSmall_nonneg with x; Auto.
Qed.

End Mult_AbsSmall.

Section Mult_Continuous.

Variable R : COrdField.

(* Begin_Tex_Verb *)
Lemma smaller :
  (x,y:R)(Zero [<] x) -> (Zero [<] y) ->
    {z:R & (Zero [<] z) | (z [<=] x) /\ (z [<=] y)}.
(* End_Tex_Verb *)
Intros.
Elim (cotrans_less_unfolded ? ? ? (half_3 ? ? H) y); Intro.
Exists Half[*]x.
Apply mult_resp_pos. Apply pos_half. Auto.
Split; Apply less_leEq. Apply half_3. Auto. Auto.
Cut Half[*]y [<] y. Intro. Exists Half[*]y.
Apply mult_resp_pos. Apply pos_half. Auto.
Split; Apply less_leEq. Apply less_transitive_unfolded with y. Auto. Auto.
Auto.
Apply half_3. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma estimate_abs : (x:R){X:R & (Zero[<]X) | AbsSmall X x}.
(* End_Tex_Verb *)
Intros.
Unfold AbsSmall.
Cut x [<] x[+]One. Intro.
Elim (cotrans_less_unfolded ? x x[+]One H [--]x); Intro.
Exists [--]x[+]One.
Apply leEq_less_trans with [--]x.
2: Apply less_plusOne.
Apply less_leEq; Apply mult_cancel_less with (Two::R).
Apply pos_two.
Step (Zero::R); RStepr [--]x[-]x.
Apply shift_less_minus.
Step x; Auto.
Split; Apply less_leEq.
Stepr [--][--]x. Apply inv_resp_less. Apply less_plusOne.
Apply less_transitive_unfolded with [--]x. Auto. Apply less_plusOne.
Exists x[+]One.
Apply less_leEq_trans with (One::R)[/]TwoNZ.
Apply pos_div_two; Apply pos_one.
Apply shift_leEq_plus; RStep ([--]One::R)[/]TwoNZ.
Apply shift_div_leEq.
Apply pos_two.
RStepr x[+]x; Apply shift_leEq_plus.
Unfold cg_minus; Apply shift_plus_leEq'.
RStepr x[+]One; Apply less_leEq; Auto.
Split; Apply less_leEq.
Stepr [--][--]x. Apply inv_resp_less. Auto. Auto.
Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_contin :
  (x,y,e:R)(Zero [<] e) ->
    {c:R & (Zero [<] c) & {d:R & (Zero [<] d) |
      (x',y':R)(AbsSmall c x[-]x') -> (AbsSmall d y[-]y') ->
        (AbsSmall e x[*]y[-]x'[*]y')}}.
(* End_Tex_Verb *)
Intros.
Cut Zero [<] e[/]TwoNZ. Intro.
Elim (estimate_abs x). Intro X. Intros H1a H1b.
Elim (estimate_abs y). Intro Y. Intros H2 H3.
Cut Y [#] Zero. Intro H4.
Exists (e[/]TwoNZ)[/]Y[//]H4.
Apply div_resp_pos. Auto. Auto.
Cut Zero [<] X[+](e[/]TwoNZ)[/]Y[//]H4. Intro H5.
Cut X[+](e[/]TwoNZ)[/]Y[//]H4 [#] Zero. Intro H6.
Exists (e[/]TwoNZ)[/](X[+](e[/]TwoNZ)[/]Y[//]H4)[//]H6.
Apply div_resp_pos. Auto. Auto.
Intros.
Apply AbsSmall_wd_rht_unfolded with (x[-]x')[*]y[+]x'[*](y[-]y').
Apply AbsSmall_eps_div_two.
Apply AbsSmall_wd_lft_unfolded with ((e[/]TwoNZ)[/]Y[//]H4)[*]Y.
Apply mult_AbsSmall; Auto.
Rational.
Apply AbsSmall_wd_lft_unfolded with
  (X[+](e[/]TwoNZ)[/]Y[//]H4)[*]
    ((e[/]TwoNZ)[/](X[+](e[/]TwoNZ)[/]Y[//]H4)[//]H6).
Apply mult_AbsSmall; Auto.
Apply AbsSmall_wd_rht_unfolded with x[+](x'[-]x).
Apply AbsSmall_plus; Auto. Apply AbsSmall_minus. Auto.
Rational.
Rational.
Rational.
Apply Greater_imp_ap. Auto.
Apply plus_resp_pos; Auto.
Apply div_resp_pos; Auto.
Apply Greater_imp_ap. Auto.
Apply pos_div_two. Auto.
Qed.

End Mult_Continuous.

Section Monotonous_functions.

(* Tex_Prose
\section{Monotonous Functions}

Finally, we study several properties of monotonous functions and characterize them in some way.

\begin{convention} Let \verb!R:COrdField!.
\end{convention}
*)
Variable R:COrdField.

(* Tex_Prose
We begin by characterizing the preservation of less (less or equal) in terms of preservation of less or equal (less).
*)

(* Begin_Tex_Verb *)
Lemma resp_less_char' : (P:R->CProp)
  (f:(x:R)(P x)->R)(x,y,Hx,Hy:?)
  ((x[#]y) -> ((f x Hx) [#] (f y Hy)))->
  ((x[<=]y) -> (f x Hx) [<=] (f y Hy))->
    (x[<]y) -> (f x Hx) [<] (f y Hy).
(* End_Tex_Verb *)
Intros.
Elim (ap_imp_less ??? (H (less_imp_ap ??? H1))); Intros.
Auto.
ElimType False.
Apply less_irreflexive_unfolded with x:=(f x Hx).
Apply leEq_less_trans with (f y Hy); Auto.
Apply H0; Apply less_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma resp_less_char : (f:R->R)(x,y:R)
  ((x[#]y) -> ((f x) [#] (f y)))->
  ((x[<=]y) -> (f x) [<=] (f y))->
    (x[<]y) -> (f x) [<] (f y).
(* End_Tex_Verb *)
Intros.
LetTac f':=[x:R][H:CTrue](f x).
Change ((f' x CI)[<](f' y CI)).
Apply resp_less_char' with P:=[x:R]CTrue; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma resp_leEq_char' : (P:R->CProp)
  (f:(x:R)(P x)->R)(x,y,Hx,Hy:?)
  ((x[=]y) -> (f x Hx) [=] (f y Hy))->
  ((x[<]y) -> (f x Hx) [<] (f y Hy))->
    (x[<=]y) -> (f x Hx) [<=] (f y Hy).
(* End_Tex_Verb *)
Intros.
Intro.
Cut (Not x[<]y)/\~(x[=]y); Intros.
Inversion_clear H3.
Apply H5.
Apply leEq_imp_eq; Auto.
Split; Intro.
Apply less_irreflexive_unfolded with x:=(f y Hy).
Apply less_transitive_unfolded with (f x Hx); Auto.
Apply less_irreflexive_unfolded with x:=(f y Hy).
Apply less_leEq_trans with (f x Hx); Auto.
Apply eq_imp_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma resp_leEq_char : (f:R->R)(x,y:R)
  ((x[=]y) -> (f x) [=] (f y))->
  ((x[<]y) -> (f x) [<] (f y))->
    (x[<=]y) -> (f x) [<=] (f y).
(* End_Tex_Verb *)
Intros.
LetTac f':=[x:R][H:CTrue](f x).
Change ((f' x CI)[<=](f' y CI)).
Apply resp_leEq_char' with P:=[x:R]CTrue; Auto.
Qed.

(* Tex_Prose
Next, we see different characterizations of monotonous functions from some subset of the natural numbers into \verb!R!.  Mainly, these amount (for different types of functions) to proving that a function is monotonous iff $f(i)<f(i+1)$ for every $i$.

Also, strictly monotonous functions are injective.
*)

(* Begin_Tex_Verb *)
Lemma local_mon_imp_mon : (f:nat->R)((i:nat)(f i)[<](f (S i)))->
  (i,j:nat)(lt i j)->(f i)[<](f j).
(* End_Tex_Verb *)
Induction j.
Intros; ElimType False; Inversion H0.
Clear j; Intro j; Intros.
Elim (le_lt_eq_dec ?? H1); Intro.
Apply leEq_less_trans with (f j).
Apply less_leEq; Apply H0; Auto with arith.
Auto.
Rewrite <- b; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon_imp_mon' : (f:nat->R)((i:nat)(f i)[<](f (S i)))->
  (i,j:nat)(le i j)->(f i)[<=](f j).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_eq_dec ?? H0); Intro.
Apply less_leEq; Apply local_mon_imp_mon with f:=f; Assumption.
Apply eq_imp_leEq; Rewrite b; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon'_imp_mon' : (f:nat->R)((i:nat)(f i)[<=](f (S i)))->
  (i,j:nat)(le i j)->(f i)[<=](f j).
(* End_Tex_Verb *)
Intros; Induction j.
Cut i=O; [Intro | Auto with arith].
Rewrite H1; Apply leEq_reflexive.
Elim (le_lt_eq_dec ?? H0); Intro.
Apply leEq_transitive with (f j).
Apply Hrecj; Auto with arith.
Apply H.
Rewrite b; Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma mon_imp_mon' : (f:nat->R)((i,j:nat)(lt i j)->((f i)[<](f j)))->
  (i,j:nat)(le i j)->(f i)[<=](f j).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_eq_dec ?? H0); Intro.
Apply less_leEq; Apply H; Assumption.
Rewrite b; Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma mon_imp_inj : (f:nat->R)((i,j:nat)(lt i j)->((f i)[<](f j)))->
  (i,j:nat)((f i)[=](f j))->i=j.
(* End_Tex_Verb *)
Intros.
Cut ~~i=j; [Omega | Intro].
Cut (lt i j)\/(lt j i); [Intro | Apply not_eq; Auto].
Inversion_clear H2; (ElimType False; Cut (f i)[#](f j); [Apply eq_imp_not_ap; Assumption | Idtac]).
Apply less_imp_ap; Apply H; Assumption.
Apply Greater_imp_ap; Apply H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon_imp_mon_lt : (n:nat)(f:(i:nat)(lt i n)->R)
  ((i:nat)(H,H':?)(f i H)[<](f (S i) H'))->
  (i,j:nat)(Hi,Hj:?)(lt i j)->(f i Hi)[<](f j Hj).
(* End_Tex_Verb *)
Induction j.
Intros; ElimType False; Inversion H0.
Clear j; Intro j; Intros.
Elim (le_lt_eq_dec ?? H1); Intro.
Cut (lt j n); [Intro | Auto with arith].
Apply leEq_less_trans with (f j H2).
Apply less_leEq; Apply H0; Auto with arith.
Apply H.
Generalize Hj; Rewrite <- b.
Intro; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon_imp_mon'_lt : (n:nat)(f:(i:nat)(lt i n)->R)
  ((i:nat)(H,H':?)(f i H)[<](f (S i) H'))->(nat_less_n_fun ?? f)->
  (i,j:nat)(Hi,Hj:?)(le i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_eq_dec ?? H1); Intros.
Apply less_leEq; Apply local_mon_imp_mon_lt with n; Auto.
Apply eq_imp_leEq; Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon'_imp_mon'_lt : (n:nat)(f:(i:nat)(lt i n)->R)
  ((i:nat)(H,H':?)(f i H)[<=](f (S i) H'))->(nat_less_n_fun ?? f)->
  (i,j:nat)(Hi,Hj:?)(le i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Induction j.
Intros.
Cut i=O; [Intro | Auto with arith].
Apply eq_imp_leEq; Apply H0; Auto.
Intro m; Intros.
Elim (le_lt_eq_dec ?? H2); Intro.
Cut (lt m n); [Intro | Auto with arith].
Apply leEq_transitive with (f m H3); Auto.
Apply H1; Auto with arith.
Apply eq_imp_leEq; Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon'_imp_mon'2_lt : (n:nat)(f:(i:nat)(lt i n)->R)
  ((i:nat)(H,H':?)(f i H)[<=](f (S i) H'))->
  (i,j:nat)(Hi,Hj:?)(lt i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Intros; Induction j.
ElimType False; Inversion H0.
Elim (le_lt_eq_dec ?? H0); Intro.
Cut (lt j n); [Intro | Auto with arith].
Apply leEq_transitive with (f j H1).
Apply Hrecj; Auto with arith.
Apply H.
Generalize Hj; Rewrite <- b.
Intro; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma mon_imp_mon'_lt : (n:nat)(f:(i:nat)(lt i n)->R)(nat_less_n_fun ?? f)->
  ((i,j:nat)(Hi,Hj:?)(lt i j)->((f i Hi)[<](f j Hj)))->
  (i,j:nat)(Hi,Hj:?)(le i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_eq_dec ?? H1); Intro.
Apply less_leEq; Apply H0; Assumption.
Apply eq_imp_leEq; Apply H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mon_imp_inj_lt : (n:nat)(f:(i:nat)(lt i n)->R)
  ((i,j:nat)(Hi,Hj:?)(lt i j)->((f i Hi)[<](f j Hj)))->
  (i,j:nat)(Hi,Hj:?)((f i Hi)[=](f j Hj))->i=j.
(* End_Tex_Verb *)
Intros.
Cut ~~i=j; Intro.
Clear H H0 Hj Hi; Omega.
Cut (lt i j)\/(lt j i); [Intro | Apply not_eq; Auto].
Inversion_clear H2; (ElimType False; Cut (f i Hi)[#](f j Hj); [Apply eq_imp_not_ap; Assumption | Idtac]).
Apply less_imp_ap; Apply H; Assumption.
Apply Greater_imp_ap; Apply H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon_imp_mon_le : (n:nat)(f:(i:nat)(le i n)->R)
  ((i:nat)(H,H':?)(f i H)[<](f (S i) H'))->
  (i,j:nat)(Hi,Hj:?)(lt i j)->(f i Hi)[<](f j Hj).
(* End_Tex_Verb *)
Induction j.
Intros; ElimType False; Inversion H0.
Clear j; Intro j; Intros.
Elim (le_lt_eq_dec ?? H1); Intro.
Cut (le j n); [Intro | Auto with arith].
Apply leEq_less_trans with (f j H2).
Apply less_leEq; Apply H0; Auto with arith.
Apply H.
Generalize Hj; Rewrite <- b.
Intro; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon_imp_mon'_le : (n:nat)(f:(i:nat)(le i n)->R)
  ((i:nat)(H,H':?)(f i H)[<](f (S i) H'))->(nat_less_n_fun' ?? f)->
  (i,j:nat)(Hi,Hj:?)(le i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_eq_dec ?? H1); Intros.
Apply less_leEq; Apply local_mon_imp_mon_le with n; Auto.
Apply eq_imp_leEq; Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon'_imp_mon'_le : (n:nat)(f:(i:nat)(le i n)->R)
  ((i:nat)(H,H':?)(f i H)[<=](f (S i) H'))->(nat_less_n_fun' ?? f)->
  (i,j:nat)(Hi,Hj:?)(le i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Induction j.
Intros.
Cut i=O; [Intro | Auto with arith].
Apply eq_imp_leEq; Apply H0; Auto.
Intro m; Intros.
Elim (le_lt_eq_dec ?? H2); Intro.
Cut (le m n); [Intro | Auto with arith].
Apply leEq_transitive with (f m H3); Auto.
Apply H1; Auto with arith.
Apply eq_imp_leEq; Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma local_mon'_imp_mon'2_le : (n:nat)(f:(i:nat)(le i n)->R)
  ((i:nat)(H,H':?)(f i H)[<=](f (S i) H'))->
  (i,j:nat)(Hi,Hj:?)(lt i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Intros; Induction j.
ElimType False; Inversion H0.
Elim (le_lt_eq_dec ?? H0); Intro.
Cut (le j n); [Intro | Auto with arith].
Apply leEq_transitive with (f j H1).
Apply Hrecj; Auto with arith.
Apply H.
Generalize Hj; Rewrite <- b.
Intro; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma mon_imp_mon'_le : (n:nat)(f:(i:nat)(le i n)->R)(nat_less_n_fun' ?? f)->
  ((i,j:nat)(Hi,Hj:?)(lt i j)->((f i Hi)[<](f j Hj)))->
  (i,j:nat)(Hi,Hj:?)(le i j)->(f i Hi)[<=](f j Hj).
(* End_Tex_Verb *)
Intros.
Elim (le_lt_eq_dec ?? H1); Intro.
Apply less_leEq; Apply H0; Assumption.
Apply eq_imp_leEq; Apply H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mon_imp_inj_le : (n:nat)(f:(i:nat)(le i n)->R)
  ((i,j:nat)(Hi,Hj:?)(lt i j)->((f i Hi)[<](f j Hj)))->
  (i,j:nat)(Hi,Hj:?)((f i Hi)[=](f j Hj))->i=j.
(* End_Tex_Verb *)
Intros.
Cut ~~i=j; Intro.
Clear H H0 Hj Hi; Omega.
Cut (lt i j)\/(lt j i); [Intro | Apply not_eq; Auto].
Inversion_clear H2; (ElimType False; Cut (f i Hi)[#](f j Hj); [Apply eq_imp_not_ap; Assumption | Idtac]).
Apply less_imp_ap; Apply H; Assumption.
Apply Greater_imp_ap; Apply H; Assumption.
Qed.

(* Tex_Prose
A similar result for {\em partial} functions.
*)

(* Begin_Tex_Verb *)
Lemma part_mon_imp_mon' : (F:(PartFunct R))(I:R->CProp)
  ((x:R)(I x)->(Pred F x))->
  ((x,y:R)(I x)->(I y)->(x[<]y)->(Hx,Hy:?)(F x Hx)[<](F y Hy))
  ->(x,y:R)(I x)->(I y)->(x[<=]y)->(Hx,Hy:?)(F x Hx)[<=](F y Hy).
(* End_Tex_Verb *)
Intros.
Intro.
Cut x[=]y; Intros.
Apply (less_irreflexive_unfolded ? (F x Hx)).
Step (F y Hy); Auto.
Apply leEq_imp_eq; Auto.
Intro.
Apply (less_irreflexive_unfolded ? (F x Hx)).
Apply less_transitive_unfolded with (F y Hy); Auto.
Qed.

End Monotonous_functions.
