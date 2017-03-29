(* $Id: RealLists.v,v 1.17 2003/03/13 12:06:26 lcf Exp $ *)

Require Export CReals1.

Opaque IR.

Section Lists.

(* Tex_Prose
\chapter{Lists of Real Numbers}

In some contexts we will need to work with nested existential quantified formulas of the form \[\exists_{n\in\NN}\exists_{x_1,\ldots,x_n}P(x_1,\ldots,x_n).\]  One way of formalizing this kind of statement is through quantifying over lists.  In this file we provide some tools for manipulating lists.

Notice that some of the properties listed below only make sense in the context within which we are working.  Unlike in the other lemma files, no care has been taken here to state the lemmas in their most general form, as that would make them very unpractical to use.

\section{Lists}

We start by defining maximum and minimum of lists of reals\footnote{The value of these functions for the empty list is arbitrarily set to 0, but it will be irrelevant, as we will never work with empty lists.}, and two membership predicates.
*)

(* Begin_Tex_Verb *)
Fixpoint maxlist [l:(list IR)] : IR :=
  Cases l of
    nil => Zero
  | (cons x nil) => x
  | (cons x m) => (Max x (maxlist m))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint minlist [l:(list IR)] : IR :=
  Cases l of
    nil => Zero
  | (cons x nil) => x
  | (cons x m) => (Min x (minlist m))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint member [x:IR][l:(list IR)] : CProp :=
  Cases l of
    nil => CFalse
  | (cons y m) => (member x m)+{x[=]y}
  end.
(* End_Tex_Verb *)

(* Tex_Prose
Sometimes the length of the list has to be restricted; the next definition provides an easy way to do that.
*)

(* Begin_Tex_Verb *)
Definition length_leEq [A:Set][l:(list A)][n:nat] :=
  (le (length l) n).
(* End_Tex_Verb *)

(* Tex_Prose
Length is preserved by mapping.
*)

(* Begin_Tex_Verb *)
Lemma map_pres_length : (A,B:Set)(l:(list A))(f:A->B)
  (length l)=(length (map f l)).
(* End_Tex_Verb *)
Intros.
Induction l.
Auto.
Simpl; Auto.
Qed.

(* Tex_Prose
Often we want to map \emph{partial} functions through a list; this next operator provides a way to do that, and is proved to be correct.
*)

(* Begin_Tex_Verb *)
Definition map2 [F:PartIR][l:(list IR)]
  [H:(y:IR)(member y l)->(Pred F y)] : (list IR).
(* End_Tex_Verb *)
Intros.
Induction l.
Apply nil.
Apply cons.
Cut (member a (cons a l)); [Intro | Right ; Algebra].
Apply (Part F a (H a H0)).
Cut (y:IR)(member y l)->(Pred F y); Intros.
2: Apply H; Left; Assumption.
Apply (Hrecl H0).
Defined.

(* Begin_Tex_Verb *)
Lemma map2_wd : (F:PartIR)(l:(list IR))(H,H':?)(x:IR)
  (member x (map2 F l H))->(member x (map2 F l H')).
(* End_Tex_Verb *)
Intros.
Induction l.
Simpl; Simpl in H0; Assumption.
Simpl in H0; Inversion_clear H0.
Simpl; Left.
Apply Hrecl with [y:IR][H0:(member y l)](H y (inleft (member y l) y[=]a H0)).
Assumption.
Right.
EApply eq_transitive_unfolded.
Apply H1.
Simpl; Apply pfwdef; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma map2_pres_member : (F:PartIR)(x:IR)(Hx,l,H:?)
  (member x l)->(member (F x Hx) (map2 F l H)).
(* End_Tex_Verb *)
Intros.
Induction l.
Simpl; Simpl in H; Assumption.
Simpl.
Elim H0.
Intro; Left; Apply Hrecl; Assumption.
Intro; Right.
Apply pfwdef; Assumption.
Qed.

(* Tex_Prose
As \verb!maxlist! and \verb!minlist! are generalizations of \verb!Max! and \verb!Min! to finite sets of real numbers, they have the expected properties:
*)

(* Begin_Tex_Verb *)
Lemma maxlist_greater :
  (l:(list IR))(x:IR)(member x l)->(x[<=](maxlist l)).
(* End_Tex_Verb *)
Intros.
Induction l.
ElimType CFalse; Assumption.
Simpl.
Induction l.
Simpl in H; Elim H.
Intro; Tauto.
Intro; Apply eq_imp_leEq.
Auto.
Simpl in H.
Elim H.
Intro.
Apply leEq_transitive with (maxlist (cons a0 l)).
Apply Hrecl; Assumption.
Apply rht_leEq_Max.
Intro; Step a; Apply lft_leEq_Max.
Qed.

Local maxlist_aux : (a,b:IR)(l:(list IR))(maxlist (cons a (cons b l)))[=](maxlist (cons b (cons a l))).
Intros.
Case l.
Simpl; Apply Max_comm.
Intros c m.
Step (Max a (Max b (maxlist (cons c m)))).
Stepr (Max b (Max a (maxlist (cons c m)))).
Apply leEq_imp_eq; Apply Max_leEq.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Apply lft_leEq_Max.
Apply Max_leEq.
Apply lft_leEq_Max.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Apply rht_leEq_Max.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Apply lft_leEq_Max.
Apply Max_leEq.
Apply lft_leEq_Max.
EApply leEq_transitive.
2: Apply rht_leEq_Max.
Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma maxlist_leEq_eps :
  (l:(list IR)){x:IR & (member x l)}->(e:IR)(Zero[<]e)->
  {x:IR & (member x l) | ((maxlist l)[-]e)[<=]x}.
(* End_Tex_Verb *)
Intro l; Induction l.
 Intro H; Simpl in H; Inversion H; Inversion H0.
Clear Hrecl.
Intro H; Induction l; Intros e H0.
 Simpl; Exists a.
  Right; Algebra.
 Apply less_leEq; Apply shift_minus_less; Apply shift_less_plus'.
 Step (Zero::IR); Assumption.
Cut {((Max a0 (maxlist (cons a l)))[-](e[/]TwoNZ))[<=]a0}+{((Max a0 (maxlist (cons a l)))[-](e[/]TwoNZ))[<=](maxlist (cons a l))}.
 2: Apply Max_minus_eps_leEq; Apply pos_div_two; Assumption.
Intro H1.
Elim H1; Intro H2.
 Exists a0.
  Simpl; Left; Right; Algebra.
 Apply leEq_transitive with (Max a (maxlist (cons a0 l)))[-](e[/]TwoNZ).
  Step (Max a (maxlist (cons a0 l)))[-]e.
  Apply shift_leEq_minus; Apply shift_plus_leEq'.
  RStepr e.
  Apply less_leEq; Apply pos_div_two'; Assumption.
 Apply shift_minus_leEq.
 Step (maxlist (cons a (cons a0 l))).
 EApply leEq_wdl.
  2: Apply maxlist_aux.
 Step (Max a0 (maxlist (cons a l))).
 Apply shift_leEq_plus; Assumption.
Elim Hrecl with (e[/]TwoNZ).
  Intros x p q.
  Exists x.
   Elim p; Intro H3.
    Left; Left; Assumption.
   Right; Assumption.
  Apply shift_minus_leEq; EApply leEq_wdl.
   2: Apply maxlist_aux.
  Apply shift_leEq_plus.
  Step ((Max a0 (maxlist (cons a l)))[-]e).
  RStep ((Max a0 (maxlist (cons a l)))[-](e[/]TwoNZ))[-](e[/]TwoNZ).
  Apply leEq_transitive with (maxlist (cons a l))[-](e[/]TwoNZ).
   Apply minus_resp_leEq; Assumption.
  Assumption.
 Exists a; Right; Algebra.
Apply pos_div_two; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma maxlist_less :
  (x:IR)(l:(list IR))(lt O (length l))->
  ((y:IR)(member y l)->y[<]x)->(maxlist l)[<]x.
(* End_Tex_Verb *)
Induction l.
Simpl; Intros; ElimType False; Inversion H.
Clear l.
Do 3 Intro.
Clear H; Induction l.
Simpl; Intros.
Apply H0; Right; Algebra.
Generalize l a0 Hrecl; Clear Hrecl l a0.
Intros l b; Intros.
EApply less_wdl.
2: Apply maxlist_aux.
Step (Max b (maxlist (cons a l))).
Apply Max_less.
Apply H0; Left; Right; Algebra.
Apply Hrecl.
Simpl; Apply lt_O_Sn.
Intros; Apply H0.
Inversion_clear H1.
Left; Left; Assumption.
Right; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma maxlist_leEq :
  (y:IR)(l:(list IR))(lt O (length l))->
  ((x:IR)(member x l)->x[<=]y)->(maxlist l)[<=]y.
(* End_Tex_Verb *)
Induction l.
Simpl; Intros; ElimType False; Inversion H.
Clear l.
Do 3 Intro.
Clear H; Induction l.
Simpl; Intros.
Apply H0; Right; Algebra.
Generalize l a0 Hrecl; Clear Hrecl l a0.
Intros l b; Intros.
EApply leEq_wdl.
2: Apply maxlist_aux.
Step (Max b (maxlist (cons a l))).
Apply Max_leEq.
Apply H0; Left; Right; Algebra.
Apply Hrecl.
Simpl; Auto with arith.
Intros; Apply H0.
Inversion_clear H1.
Left; Left; Assumption.
Right; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma minlist_smaller :
  (l:(list IR))(x:IR)(member x l)->((minlist l)[<=]x).
(* End_Tex_Verb *)
Intros.
Induction l.
ElimType CFalse; Assumption.
Simpl.
Step (Cases l of nil => a | (cons _ _) => (Min a (minlist l))end).
Induction l.
Simpl in H; Elim H.
Intro; Tauto.
Intro; Cut a[=]x; [Apply eq_imp_leEq | Apply eq_symmetric_unfolded; Assumption].
Simpl in H.
Elim H.
Intro.
Apply leEq_transitive with (minlist (cons a0 l)).
Apply Min_leEq_rht.
Apply Hrecl; Assumption.
Intro; Stepr a; Apply Min_leEq_lft.
Qed.

Local minlist_aux : (a,b:IR)(l:(list IR))(minlist (cons a (cons b l)))[=](minlist (cons b (cons a l))).
Intros.
Case l.
Step (Min a b); Stepr (Min b a); Apply Min_comm.
Intros c m.
Step (Min a (Min b (minlist (cons c m)))).
Stepr (Min b (Min a (minlist (cons c m)))).
Apply leEq_imp_eq; Apply leEq_Min.
EApply leEq_transitive.
Apply Min_leEq_rht.
Apply Min_leEq_lft.
Apply leEq_Min.
Apply Min_leEq_lft.
EApply leEq_transitive.
Apply Min_leEq_rht.
Apply Min_leEq_rht.
EApply leEq_transitive.
Apply Min_leEq_rht.
Apply Min_leEq_lft.
Apply leEq_Min.
Apply Min_leEq_lft.
EApply leEq_transitive.
Apply Min_leEq_rht.
Apply Min_leEq_rht.
Qed.

(* Begin_Tex_Verb *)
Lemma minlist_leEq_eps :
  (l:(list IR)){x:IR & (member x l)}->(e:IR)(Zero[<]e)->
  {x:IR & (member x l) | x[<=]((minlist l)[+]e)}.
(* End_Tex_Verb *)
Intro l; Induction l.
 Intro H; Simpl in H; Inversion H; Inversion H0.
Clear Hrecl.
Intro H; Induction l; Intros e He.
 Simpl; Exists a.
  Right; Algebra.
 Apply less_leEq; Apply shift_less_plus'.
 Step (Zero::IR); Assumption.
Cut {a0[<=](Min a0 (minlist (cons a l)))[+]e[/]TwoNZ}+{(minlist (cons a l))[<=](Min a0 (minlist (cons a l)))[+]e[/]TwoNZ}.
 2: Apply leEq_Min_plus_eps; Apply pos_div_two; Assumption.
Intro H1.
Elim H1; Intro H2.
 Exists a0.
  Simpl; Left; Right; Algebra.
 Apply leEq_transitive with (Min a (minlist (cons a0 l)))[+](e[/]TwoNZ).
 Apply shift_leEq_plus.
 Stepr (minlist (cons a (cons a0 l))).
 EApply leEq_wdr.
  2: Apply minlist_aux.
 Stepr (Min a0 (minlist (cons a l))).
 Apply shift_minus_leEq; Assumption.
 Stepr (Min a (minlist (cons a0 l)))[+]e.
 Apply plus_resp_leEq_lft.
 Apply less_leEq; Apply pos_div_two'; Assumption.
Elim Hrecl with (e[/]TwoNZ).
  Intros x p q.
  Exists x.
   Elim p; Intro H3.
    Left; Left; Assumption.
   Right; Assumption.
  Apply shift_leEq_plus; EApply leEq_wdr.
   2: Apply minlist_aux.
  Apply shift_minus_leEq.
  Stepr ((Min a0 (minlist (cons a l)))[+]e).
  RStepr ((Min a0 (minlist (cons a l)))[+](e[/]TwoNZ))[+](e[/]TwoNZ).
  Apply leEq_transitive with (minlist (cons a l))[+](e[/]TwoNZ).
   Assumption.
  Apply plus_resp_leEq; Assumption.
 Exists a; Right; Algebra.
Apply pos_div_two; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma less_minlist :
  (x:IR)(l:(list IR))(lt O (length l))->
  ((y:IR)(member y l)->x[<]y)->x[<](minlist l).
(* End_Tex_Verb *)
Induction l.
Simpl; Intros; ElimType False; Inversion H.
Clear l.
Do 3 Intro.
Clear H; Induction l.
Simpl; Intros.
Apply H0; Right; Algebra.
Generalize l a0 Hrecl; Clear Hrecl l a0.
Intros l b; Intros.
EApply less_wdr.
2: Apply minlist_aux.
Stepr (Min b (minlist (cons a l))).
Apply less_Min.
Apply H0; Left; Right; Algebra.
Apply Hrecl.
Simpl; Auto with arith.
Intros; Apply H0.
Inversion_clear H1.
Left; Left; Assumption.
Right; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_minlist :
  (x:IR)(l:(list IR))(lt O (length l))->
  ((y:IR)(member y l)->x[<=]y)->x[<=](minlist l).
(* End_Tex_Verb *)
Induction l.
Simpl; Intros; ElimType False; Inversion H.
Clear l.
Do 3 Intro.
Clear H; Induction l.
Simpl; Intros.
Apply H0; Right; Algebra.
Generalize l a0 Hrecl; Clear Hrecl l a0.
Intros l b; Intros.
EApply leEq_wdr.
2: Apply minlist_aux.
Stepr (Min b (minlist (cons a l))).
Apply leEq_Min.
Apply H0; Left; Right; Algebra.
Apply Hrecl.
Simpl; Auto with arith.
Intros; Apply H0.
Inversion_clear H1.
Left; Left; Assumption.
Right; Assumption.
Qed.

End Lists.
