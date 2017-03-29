(* $Id: IntervalFunct.v,v 1.10 2003/03/13 12:06:20 lcf Exp $ *)

Require Export PartFunEquality.

Section Operations.

(* Tex_Prose
\chapter{Functions with compact domain}

In this section we concern ourselves with defining operations on the set of functions from an arbitrary interval $[a,b]$ to $\RR$.  Although these are a particular kind of partial function, they have the advantage that, given $a$ and $b$, they have type \verb!Set! and can thus be quantified over and extracted from existential hypothesis.  This will be important when we want to define concepts like differentiability, which involve the existence of an object satisfying some given properties.

Throughout this section we will focus on a compact interval and define operators analogous to those we already have for arbitrary partial functions.

\begin{convention} Let \verb!a,b! be real numbers and denote by \verb!I! the compact interval $[a,b]$.  Let \verb!f,g! be setoid functions of type \verb!I->IR!.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables f,g:(CSetoid_fun (subset I) IR).

Section Const.

(* Tex_Prose
Constant and identity functions are defined.

\begin{convention} Let \verb!c:IR!.
\end{convention}
*)

Variable c:IR.

(* Begin_Tex_Verb *)
Lemma ifunct_const_strext : (x,y:(subset I))((c[#]c)->(x[#]y)).
(* End_Tex_Verb *)
Intros.
ElimType False; Generalize H.
Exact (ap_irreflexive_unfolded ? c).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_const := (Build_CSetoid_fun ??
  [x:(subset I)]c ifunct_const_strext).
(* End_Tex_Verb *)

End Const.

Section Id.

(* Begin_Tex_Verb *)
Lemma ifunct_id_strext : (x,y:(subset I))
  (((scs_elem ?? x)[#](scs_elem ?? y))->(x[#]y)).
(* End_Tex_Verb *)
Intros x y; Case x; Case y; Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_id := (Build_CSetoid_fun ??
  [x:(subset I)](scs_elem ?? x) ifunct_id_strext).
(* End_Tex_Verb *)

End Id.

(* Tex_Prose
Next, we define addition, algebraic inverse, subtraction and product of functions.
*)

Section Sum.

(* Begin_Tex_Verb *)
Lemma ifunct_plus_strext :
  (x,y:(subset I))(((f x)[+](g x)[#](f y)[+](g y))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Cut ((f x)[#](f y))+((g x)[#](g y)).
Intro.
Elim H0; Intro.
Exact (csetoid_fun_strext_unfolded ????? a0).
Exact (csetoid_fun_strext_unfolded ????? b0).
Exact (bin_op_strext_unfolded ?????? H).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_plus := (Build_CSetoid_fun ??
  [x:(subset I)](f x)[+](g x) ifunct_plus_strext).
(* End_Tex_Verb *)

End Sum.

Section Inv.

(* Begin_Tex_Verb *)
Lemma ifunct_inv_strext :
  (x,y:(subset I))(([--](f x)[#][--](f y))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Cut (f x)[#](f y).
Intro.
Exact (csetoid_fun_strext_unfolded ????? H0).
Exact (un_op_strext_unfolded ???? H).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_inv := (Build_CSetoid_fun ??
  [x:(subset I)][--](f x) ifunct_inv_strext).
(* End_Tex_Verb *)

End Inv.

Section Minus.

(* Begin_Tex_Verb *)
Lemma ifunct_minus_strext :
  (x,y:(subset I))(((f x)[-](g x)[#](f y)[-](g y))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Cut ((f x)[#](f y))+((g x)[#](g y)).
Intro.
Elim H0; Intro.
Exact (csetoid_fun_strext_unfolded ????? a0).
Exact (csetoid_fun_strext_unfolded ????? b0).
Exact (cg_minus_strext ????? H).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_minus := (Build_CSetoid_fun ??
  [x:(subset I)](f x)[-](g x) ifunct_minus_strext).
(* End_Tex_Verb *)

End Minus.

Section Mult.

(* Begin_Tex_Verb *)
Lemma ifunct_mult_strext :
  (x,y:(subset I))(((f x)[*](g x)[#](f y)[*](g y))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Cut ((f x)[#](f y))+((g x)[#](g y)).
Intro.
Elim H0; Intro.
Exact (csetoid_fun_strext_unfolded ????? a0).
Exact (csetoid_fun_strext_unfolded ????? b0).
Exact (bin_op_strext_unfolded ?????? H).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_mult := (Build_CSetoid_fun ??
  [x:(subset I)](f x)[*](g x) ifunct_mult_strext).
(* End_Tex_Verb *)

End Mult.

Section Nth_Power.

(* Tex_Prose
Exponentiation to a natural power \verb!n! is also useful.
*)

Variable n:nat.

(* Begin_Tex_Verb *)
Lemma ifunct_nth_strext :
  (x,y:(subset I))((((f x)[^]n)[#]((f y)[^]n))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Apply csetoid_fun_strext_unfolded with (IR::CSetoid) f.
Apply nexp_strext with n; Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_nth := (Build_CSetoid_fun ??
  [x:(subset I)](f x)[^]n ifunct_nth_strext).
(* End_Tex_Verb *)

End Nth_Power.

(* Tex_Prose
If a function is non-zero in all the interval then we can define its multiplicative inverse.
*)

Section Recip.

(* Begin_Tex_Verb *)
Hypothesis Hg:(x:(subset I))(g x)[#]Zero.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma ifunct_recip_strext : (x,y:(subset I))
  ((One[/](g x)[//](Hg x))[#](One[/](g y)[//](Hg y)))->(x[#]y).
(* End_Tex_Verb *)
Intros.
Elim (div_strong_ext ??????? H); Intro H0.
ElimType False; Generalize H0; Apply ap_irreflexive_unfolded.
Exact (csetoid_fun_strext_unfolded ????? H0).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_recip := (Build_CSetoid_fun ??
  [x:(subset I)](One[/](g x)[//](Hg x)) ifunct_recip_strext).
(* End_Tex_Verb *)

End Recip.

Section Div.

Hypothesis Hg:(x:(subset I))(g x)[#]Zero.

(* Begin_Tex_Verb *)
Lemma ifunct_div_strext : (x,y:(subset I))
  (((f x)[/](g x)[//](Hg x))[#]((f y)[/](g y)[//](Hg y)))->(x[#]y).
(* End_Tex_Verb *)
Intros.
Elim (div_strong_ext ??????? H); Intro H0; Exact (csetoid_fun_strext_unfolded ????? H0).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_div := (Build_CSetoid_fun ??
  [x:(subset I)]((f x)[/](g x)[//](Hg x)) ifunct_div_strext).
(* End_Tex_Verb *)

End Div.

Section Absolute_Value.

(* Tex_Prose
Absolute value will also be needed at some point.
*)

(* Begin_Tex_Verb *)
Lemma ifunct_AbsIR_strext :
  (x,y:(subset I))((AbsIR (f x))[#](AbsIR (f y)))->(x[#]y).
(* End_Tex_Verb *)
Intros.
Apply csetoid_fun_strext_unfolded with (IR::CSetoid) f.
Cut ((f x)[#](f y))+(([--](f x))[#]([--](f y))).
Intro.
Inversion_clear H0.
Assumption.
Apply un_op_strext_unfolded with (!cg_inv IR); Assumption.
Apply bin_op_strext_unfolded with Max.
Apply H.
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_abs := (Build_CSetoid_fun ??
  [x:(subset I)](AbsIR (f x)) ifunct_AbsIR_strext).
(* End_Tex_Verb *)

End Absolute_Value.

End Operations.

(* Tex_Prose 
The set of these functions form a ring with relation to the operations of sum and multiplication.  As they actually
form a set, this fact can be proved in Coq for this class of functions; unfortunately, due to a problem with the
coercions, we are not able to use it (Coq will not recognize the elements of that ring as functions which can be
applied to elements of $[a,b]$), so we merely state this fact here as a curiosity.

Finally, we define composition; for this we need two functions with different domains.

\begin{convention} Let \verb!a',b'! be real numbers and denote by \verb!I'! the compact interval $[a',b']$, and let \verb!g! be a setoid function of type \verb!I'->IR!.
\end{convention}
*)
Section IFunct_Composition.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables a',b':IR.
Hypothesis Hab':a'[<=]b'.
Local I':=(Compact Hab').

Variable f:(CSetoid_fun (subset I) IR).
Variable g:(CSetoid_fun (subset I') IR).

Hypothesis Hfg:(x:(subset I))(I' (f x)).

(* Begin_Tex_Verb *)
Lemma ifunct_comp_strext : (x,y:(subset I))
  ((g (Build_subcsetoid_crr ??? (Hfg x)))[#]
    (g (Build_subcsetoid_crr ??? (Hfg y))))->(x[#]y).
(* End_Tex_Verb *)
Intros.
Apply csetoid_fun_strext_unfolded with (IR::CSetoid) f.
Exact (csetoid_fun_strext_unfolded ????? H).
Qed.

(* Begin_Tex_Verb *)
Definition ifunct_comp := (Build_CSetoid_fun ??
  [x:(subset I)](g (Build_subcsetoid_crr ??? (Hfg x)))
  ifunct_comp_strext).
(* End_Tex_Verb *)

End IFunct_Composition.

(* Tex_Prose
\begin{notation} A lot of syntactic sugar:
\begin{itemize}
\item {\tt\hypertarget{Syntactic_41}{IConst}} stands for \verb!(ifunct_const ???)!;
\item {\tt\hypertarget{Syntactic_42}{IId}} stands for \verb!(ifunct_id ???)!;
\item {\tt\hypertarget{Syntactic_43}{IPlus}} stands for \verb!(ifunct_plus ???)!;
\item {\tt\hypertarget{Syntactic_44}{IInv}} stands for \verb!(ifunct_inv ???)!;
\item {\tt\hypertarget{Syntactic_45}{IMinus}} stands for \verb!(ifunct_minus ???)!;
\item {\tt\hypertarget{Syntactic_46}{IMult}} stands for \verb!(ifunct_mult ???)!;
\item {\tt\hypertarget{Syntactic_47}{INth}} stands for \verb!(ifunct_nth ???)!;
\item {\tt\hypertarget{Syntactic_48}{IRecip}} stands for \verb!(ifunct_recip ???)!;
\item {\tt\hypertarget{Syntactic_49}{IDiv}} stands for \verb!(ifunct_div ???)!;
\item {\tt\hypertarget{Syntactic_50}{IAbs}} stands for \verb!(ifunct_abs ???)!;
\item {\tt\hypertarget{Syntactic_51}{IComp}} stands for \verb!(ifunct_comp ??????)!.
\end{itemize}
\end{notation}
*)

Syntactic Definition IConst := (ifunct_const ???).
Syntactic Definition IId := (ifunct_id ???).
Syntactic Definition IPlus := (ifunct_plus ???).
Syntactic Definition IInv := (ifunct_inv ???).
Syntactic Definition IMinus := (ifunct_minus ???).
Syntactic Definition IMult := (ifunct_mult ???).
Syntactic Definition INth := (ifunct_nth ???).
Syntactic Definition IRecip := (ifunct_recip ???).
Syntactic Definition IDiv := (ifunct_div ???).
Syntactic Definition IAbs := (ifunct_abs ???).
Syntactic Definition IComp := (ifunct_comp ??????).
