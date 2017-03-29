(* $Id: NthDerivative.v,v 1.12 2003/03/13 12:06:21 lcf Exp $ *)

Require Export Differentiability.

Section Nth_Derivative.

(* Tex_Prose
\chapter{Nth Derivative}

We now study higher order differentiability.

\begin{convention} Throughout this section:
\begin{itemize}
\item \verb!a,b! will be real numbers with $a<b$;
\item \verb!I! will denote the compact interval $[a,b]$;
\item \verb!F,G,H! will denote partial functions.
\end{itemize}
\end{convention}

\section{Definitions}

We first define what we mean by the derivative of order $n$ of a function.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Fixpoint Derivative_I_n [n:nat] : PartIR->PartIR->CProp :=
  [F,Fn:PartIR]
    Cases n of
      O => (Feq I F Fn)
    | (S p) => {f':(CSetoid_fun (subset (Compact Hab)) IR) & 
        (Derivative_I Hab' F (PartInt f')) &
          (Derivative_I_n p (PartInt f') Fn)}
    end.
(* End_Tex_Verb *)

(* Tex_Prose
Unlike first order differentiability, for our definition to be workable it is better to define directly what it means for a function to be $n$ times differentiable instead of quantifying over the \verb!Derivative_I_n! relation.
*)

(* Begin_Tex_Verb *)
Fixpoint Diffble_I_n [n:nat] : PartIR->CProp := [F:PartIR] 
  Cases n of 
    O => (included I (Pred F))
  | (S p) => {H:(Diffble_I Hab' F) &
               (Diffble_I_n p (PartInt (ProjS1 H)))}
  end.
(* End_Tex_Verb *)

End Nth_Derivative.

Implicits Derivative_I_n [1 2].
Implicits Diffble_I_n [1 2].

Section Trivia.

(* Tex_Prose
\section{Trivia}

These are the expected welldefinedness and uniqueness results.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Lemma Diffble_I_n_wd : (n:nat)(F,G:PartIR)(Feq I F G)->
  (Diffble_I_n Hab' n F)->(Diffble_I_n Hab' n G).
(* End_Tex_Verb *)
Intro.
Induction n.
Simpl; Unfold Feq; Tauto.
Intros.
Elim H0; Intros H1 H2; Clear H0.
Cut (Diffble_I Hab' G).
2: Apply Diffble_I_wd with F; Assumption.
Intro.
Exists H0.
EApply Hrecn.
2: Apply H2.
Unfold I Hab; Apply Derivative_I_unique with F.
Apply projS2.
Apply Derivative_I_wdl with G.
Apply Feq_symmetric; Assumption.
Apply projS2.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_n_wdr : (n:nat)(F,G,H:PartIR)(Feq I G H)->
  (Derivative_I_n Hab' n F G)->(Derivative_I_n Hab' n F H).
(* End_Tex_Verb *)
Intro.
Induction n; Intros.
Simpl; Simpl in H1.
Apply Feq_transitive with G; Assumption.
Elim H1; Intros f' H2 H3.
Exists f'; Auto.
Apply Hrecn with G; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_n_wdl : (n:nat)(F,G,H:PartIR)(Feq I F G)->
  (Derivative_I_n Hab' n F H)->(Derivative_I_n Hab' n G H).
(* End_Tex_Verb *)
Intro.
Induction n; Intros.
Simpl; Simpl in H1.
Apply Feq_transitive with F.
Apply Feq_symmetric; Assumption.
Auto.
Elim H1; Intros f' H2 H3.
Exists f'; Auto.
Apply Derivative_I_wdl with F; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_n_unique : (n:nat)(F,G,H:PartIR)
  (Derivative_I_n Hab' n F G)->(Derivative_I_n Hab' n F H)->
  (Feq I G H).
(* End_Tex_Verb *)
Intro.
Induction n; Intros.
Simpl in H0 H1.
Unfold I; Apply Feq_transitive with F.
Apply Feq_symmetric; Assumption.
Auto.
Elim H0; Intros g' H2 H3.
Elim H1; Intros h' H4 H5.
Apply Hrecn with (PartInt g').
Assumption.
Apply Derivative_I_n_wdl with (PartInt h').
2: Assumption.
Unfold I Hab; Apply Derivative_I_unique with F; Assumption.
Qed.

End Trivia.

Section Basic_Results.

(* Tex_Prose
\section{Basic Results}

We now explore the concept of $n$ times differentiability.  Notice that, unlike the first order case, we do not pay so much attention to the relation of $n$ times derivative, but focus rather on the definition of \verb!Diffble_I_n!.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

(* Tex_Prose
We begin by showing that having a higher order derivative implies being differentiable.
*)

(* Begin_Tex_Verb *)
Lemma Diffble_I_n_imp_diffble : (n:nat)(lt O n)->
  (F:PartIR)(Diffble_I_n Hab' n F)->(Diffble_I Hab' F).
(* End_Tex_Verb *)
Intros.
Rewrite S_pred with n O in H0; Auto.
Simpl in H0.
Inversion_clear H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma deriv_n_imp_diffble : (n:nat)(lt O n)->(F,F':PartIR)
  (Derivative_I_n Hab' n F F')->(Diffble_I Hab' F).
(* End_Tex_Verb *)
Destruct n.
Intros; ElimType False; Inversion H.
Clear n; Intros.
Elim H0; Clear H0; Intros f'' H0 H1.
Exists f''; Assumption.
Qed.

(* Tex_Prose
If a function is $n$ times differentiable then it is also $m$ times differentiable for every $m$ less or equal than $n$.
*)

(* Begin_Tex_Verb *)
Lemma le_imp_Diffble_I : (m,n:nat)(le m n)->(F:PartIR)
  (Diffble_I_n Hab' n F)->(Diffble_I_n Hab' m F).
(* End_Tex_Verb *)
Intros.
Induction n.
Cut m=O; [Intro | Auto with arith].
Rewrite H1; Simpl; Tauto.
Elim (le_lt_eq_dec ?? H); Intro H2.
2: Rewrite H2; Assumption.
Apply Hrecn.
Auto with arith.
Elim H0; Intros Hf Hf'.
Clear Hf' Hf H2 Hrecn H.
Generalize H0.
Generalize F.
Clear H0 F; Induction n; Intros.
Simpl; Apply diffble_imp_inc.
Exact (Diffble_I_n_imp_diffble ? (lt_n_Sn O) F H0).
Simpl.
Elim H0; Intros Hf Hf'.
Exists Hf.
Apply Hrecn.
Assumption.
Qed.

(* Tex_Prose
The next result consolidates our intuition that a function is $n$ times differentiable if we can build from it a chain of $n$ derivatives.
*)

(* Begin_Tex_Verb *)
Lemma Diffble_I_imp_le : (n:nat)(lt O n)->(F,F':PartIR)
  (Diffble_I_n Hab' n F)->(Derivative_I Hab' F F')->
  (Diffble_I_n Hab' (pred n) F').
(* End_Tex_Verb *)
Destruct n.
Intros; ElimType False; Inversion H.
Clear n; Intros.
Elim H0; Intros f'' Hf''.
Simpl.
EApply Diffble_I_n_wd.
2: Apply Hf''.
Apply Derivative_I_unique with F.
Apply projS2.
Assumption.
Qed.

(* Tex_Prose
As expected, an $n$ times differentiable in $[a,b]$ function must be defined in that interval.
*)

(* Begin_Tex_Verb *)
Lemma Diffble_I_n_imp_inc : (n:nat)(F:PartIR)
  (Diffble_I_n Hab' n F)->(included (Compact Hab) (Pred F)).
(* End_Tex_Verb *)
Intros; Induction n.
Simpl in H; Included.
Apply Hrecn.
Exact (le_imp_Diffble_I ?? (le_n_Sn n) ? H).
Qed.

(* Tex_Prose
Also, the notions of derivative and differentiability are related as expected.
*)

(* Begin_Tex_Verb *)
Lemma Diffble_I_n_imp_deriv_n :
  (n:nat)(F:PartIR)(Diffble_I_n Hab' n F)->
  {f':(CSetoid_fun (subset (Compact Hab)) IR) &
     (Derivative_I_n Hab' n F (PartInt f'))}.
(* End_Tex_Verb *)
Intro; Induction n.
Intros.
Exists (IntPartIR (Diffble_I_n_imp_inc ?? H)).
Simpl; Simpl in H.
FEQ.
Intros.
Elim H; Intros H1 H2.
Elim (Hrecn ? H2); Intros f' Hf'.
Exists f'.
Simpl.
Exists (ProjS1 H1).
Apply projS2.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma deriv_n_imp_Diffble_I_n : (n:nat)(F,F':PartIR)
  (Derivative_I_n Hab' n F F')->(Diffble_I_n Hab' n F).
(* End_Tex_Verb *)
Intro; Induction n; Intros.
Simpl; Simpl in H.
Elim H; Intros.
Elim a0; Auto.
Simpl.
Elim H; Intros f' H0 H1.
Cut (Diffble_I Hab' F); [Intro | Exists f'; Assumption].
Exists H2.
Apply Hrecn with F'.
EApply Derivative_I_n_wdl.
2: Apply H1.
Apply Derivative_I_unique with F.
Assumption.
Apply projS2.
Qed.

(* Tex_Prose
From this we can prove that if $F$ has an $n$-th order derivative in $[a,b]$ then both $F$ and its derivative are defined in that interval.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_I_n_imp_inc : (n:nat)(F,F':PartIR)
  (Derivative_I_n Hab' n F F')->(included I (Pred F)).
(* End_Tex_Verb *)
Intros; Apply Diffble_I_n_imp_inc with n.
Apply deriv_n_imp_Diffble_I_n with F'; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_n_imp_inc' : (n:nat)(F,F':PartIR)
  (Derivative_I_n Hab' n F F')->(included I (Pred F')).
(* End_Tex_Verb *)
Intro; Induction n; Intros.
Simpl; Simpl in H.
Elim H; Intros H0 H1; Elim H0; Auto.
Elim H; Intros f' H0 H1.
Apply Hrecn with (PartInt f').
Assumption.
Qed.

(* Tex_Prose
First order differentiability is just a special case.
*)

(* Begin_Tex_Verb *)
Lemma deriv_1_deriv :
  (F:?)(diffF:(Diffble_I Hab' F))(diffFn:(Diffble_I_n Hab' (1) F))
  (Feq I (PartInt (ProjS1 diffF))
         (PartInt (ProjS1 (Diffble_I_n_imp_deriv_n ?? diffFn)))).
(* End_Tex_Verb *)
Intros.
Simpl.
Unfold I Hab; Apply Derivative_I_unique with F.
Apply projS2.
Cut (Derivative_I_n Hab' (1) F (PartInt (ProjS1 (Diffble_I_n_imp_deriv_n (1) F diffFn)))).
2: Apply projS2.
Intro.
Elim H; Intros f' H0 H1.
Apply Derivative_I_wdr with (PartInt f'); Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma deriv_1_deriv' :
  (F:?)(diffF:(Diffble_I Hab' F))(diffFn:(Diffble_I_n Hab' (1) F))
  (x:(subset I))(ProjS1 diffF x)[=]
    (ProjS1 (Diffble_I_n_imp_deriv_n ?? diffFn) x).
(* End_Tex_Verb *)
Intros.
Elim (deriv_1_deriv F diffF diffFn); Intros H H2.
Simpl in H2.
Generalize (H2 (scs_elem ?? x) (scs_prf ?? x) (scs_prf ?? x) (scs_prf ?? x)).
Intro.
EApply eq_transitive_unfolded.
EApply eq_transitive_unfolded.
2: Apply H0.
Apply csetoid_fun_wd_unfolded.
Cut (scs_elem ?? x)[=](scs_elem ?? x).
Case x; Simpl; Auto.
Algebra.
Apply csetoid_fun_wd_unfolded.
Cut (scs_elem ?? x)[=](scs_elem ?? x).
Case x; Simpl; Auto.
Algebra.
Qed.

(* Tex_Prose
As usual, nth order derivability is preserved by shrinking the interval.
*)

(* Begin_Tex_Verb *)
Lemma included_imp_deriv_n : (n,c,d,Hcd,F,F':?)
  (included (Compact (less_leEq ? c d Hcd))
            (Compact (less_leEq ? a b Hab')))->
  (Derivative_I_n Hab' n F F')->(Derivative_I_n Hcd n F F').
(* End_Tex_Verb *)
Intro; Induction n; Simpl; Intros.
Apply included_Feq with (Compact (less_leEq ??? Hab')); Auto.
Elim H0; Intros f' H1 H2.
Exists (int_partIR (!Frestr (PartInt f') ? (compact_wd ???) H) ??? (included_refl ?)).
Apply Derivative_I_wdr with (PartInt f').
FEQ.
Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply included_imp_deriv with Hab:=Hab'; Auto.
Apply Derivative_I_n_wdl with (PartInt f').
FEQ.
Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_imp_diffble_n : (n,c,d,Hcd,F:?)
  (included (Compact (less_leEq ? c d Hcd))
            (Compact (less_leEq ? a b Hab')))->
  (Diffble_I_n Hab' n F)->(Diffble_I_n Hcd n F).
(* End_Tex_Verb *)
Intro; Induction n; Simpl; Intros.
Apply included_trans with (Compact (less_leEq ??? Hab')); Included.
Elim H0; Intros f' HF.
Exists (included_imp_diffble ??????? H f').
Apply Diffble_I_n_wd with (PartInt (ProjS1 f')).
Apply Derivative_I_unique with F.
Apply included_imp_deriv with Hab:=Hab'.
Auto.
Apply projS2.
Apply projS2.
Auto.
Qed.

(* Tex_Prose
And finally we have an addition rule for the order of the derivative.
*)

(* Begin_Tex_Verb *)
Lemma Derivative_I_n_plus : (n,m,k,F,G,H:?)
  (Derivative_I_n Hab' m F G)->(Derivative_I_n Hab' n G H)->
  k=(plus m n)->(Derivative_I_n Hab' k F H).
(* End_Tex_Verb *)
Do 2 Intro.
Induction m; Intros; Rewrite H2.
Simpl.
Apply Derivative_I_n_wdl with G.
Inversion_clear H0.
Inversion_clear H3.
Apply Derivative_I_n_unique with (O) G.
Simpl; Apply Feq_reflexive; Auto.
Simpl; FEQ; Algebra.
Auto.
Elim H0; Intros F' H3 H4.
Exists F'; Auto.
Apply Hrecm with G; Auto.
Qed.

End Basic_Results.

Section More_Results.

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

(* Tex_Prose
\section{The $n^{\mathrm{th}}$ Derivative}

We now define an operator that returns an $n^{\mathrm{th}}$ order derivative of an $n$-times differentiable function.  This is analogous to the quantifier elimination which we would get if we had defined nth differentiability as an existential quantification of the nth derivative relation.
*)

(* Begin_Tex_Verb *)
Definition n_deriv_I [n,F:?][H:(Diffble_I_n Hab' n F)] : PartIR.
(* End_Tex_Verb *)
Intro; Induction n.
Intros.
Simpl in H.
Apply (FRestr H).
Intros.
Cut (Diffble_I Hab' F); Intros.
LetTac f':=(ProjS1 H0).
Cut (Diffble_I_n Hab' n (PartInt f')).
Intro.
Apply (Hrecn ? H1).
Cut n=(pred (S n)); [Intro | Simpl; Reflexivity].
Rewrite H1.
Apply Diffble_I_imp_le with F.
Apply lt_O_Sn.
Assumption.
Unfold f'; Apply projS2.
Apply Diffble_I_n_imp_diffble with (S n).
Apply lt_O_Sn.
Assumption.
Defined.

(* Tex_Prose
This operator is well defined and works as expected.
*)

(* Begin_Tex_Verb *)
Lemma n_deriv_I_wd : (n:nat)(F,G:PartIR)
  (Hf:(Diffble_I_n Hab' n F))(Hg:(Diffble_I_n Hab' n G))
  (Feq I F G)->(Feq I (n_deriv_I ?? Hf) (n_deriv_I ?? Hg)).
(* End_Tex_Verb *)
Intro; Induction n; Intros.
Inversion_clear H.
Inversion_clear H0.
Unfold I; Simpl; FEQ.
Simpl; Apply H1; Auto.
Simpl.
Apply Hrecn.
Unfold I Hab; Apply Derivative_I_unique with F.
Apply projS2.
Apply Derivative_I_wdl with G.
Apply Feq_symmetric; Assumption.
Apply projS2.
Qed.

(* Begin_Tex_Verb *)
Lemma n_deriv_lemma : (n:nat)(F:PartIR)(H:(Diffble_I_n Hab' n F))
  (Derivative_I_n Hab' n F (n_deriv_I ?? H)).
(* End_Tex_Verb *)
Intro; Induction n; Intros.
Simpl; Simpl in H; FEQ.
Elim H; Intros Hf Hf'.
Exists (ProjS1 Hf).
Apply projS2.
Simpl.
Cut (Diffble_I_n Hab' n (PartInt (ProjS1 Hf))); Intros.
Apply Derivative_I_n_wdr with (n_deriv_I ?? H0).
2: Apply Hrecn.
Apply n_deriv_I_wd.
Unfold I Hab; Apply Derivative_I_unique with F.
Apply projS2.
Apply projS2.
Elim H; Intros.
EApply Diffble_I_n_wd.
2: Apply p.
Apply Derivative_I_unique with F; Apply projS2.
Qed.

(* Begin_Tex_Verb *)
Lemma n_deriv_inc : (n:nat)(F:PartIR)(H:(Diffble_I_n Hab' n F))
  (included (Compact Hab) (Pred (n_deriv_I ?? H))).
(* End_Tex_Verb *)
Intros; Simpl.
Unfold I Hab; Apply Derivative_I_n_imp_inc' with n F.
Apply n_deriv_lemma.
Qed.

(* Begin_Tex_Verb *)
Lemma n_deriv_inc' : (n,Hab,F,H:?)
  (included (Pred (n_deriv_I n F H)) (compact a b Hab)).
(* End_Tex_Verb *)
Intro; Induction n; Intros; Simpl; Included.
Qed.

(* Tex_Prose
Some basic properties of this operation.
*)

(* Begin_Tex_Verb *)
Lemma n_Sn_deriv : (n:nat)(F:PartIR)
  (H:(Diffble_I_n Hab' n F))(H':(Diffble_I_n Hab' (S n) F))
  (Derivative_I Hab' (n_deriv_I ?? H) (n_deriv_I ?? H')).
(* End_Tex_Verb *)
Intro; Induction n.
Intros.
Apply Derivative_I_wdl with F.
FEQ.
Apply Derivative_I_wdr with (PartInt (ProjS1 (Diffble_I_n_imp_diffble ???? (lt_O_Sn O) ? H'))).
Apply eq_imp_Feq.
Included.
Included.
Intros; Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply projS2.
Intro.
Cut {p:nat | p=(S n)}.
Intro; Elim H; Intros p H0.
Pattern 2 4 (S n); Rewrite <- H0.
Intros.
Elim H1; Intros H0' H0''; Clear H1.
Elim H'; Intros H1' H1''; Clear H'.
Cut (Diffble_I_n Hab' n (PartInt (ProjS1 H1'))).
Intro H1'''.
Apply Derivative_I_wdl with (n_deriv_I ?? H1''').
2: Apply Derivative_I_wdr with (n_deriv_I ?? H1'').
Simpl; Apply n_deriv_I_wd.
Unfold I Hab; Apply Derivative_I_unique with F.
Apply projS2.
Apply projS2.
Simpl; Apply n_deriv_I_wd.
Unfold I Hab; Apply Derivative_I_unique with F.
Apply projS2.
Apply projS2.
Generalize H1''.
Rewrite H0.
Intro.
Apply Hrecn.
Generalize H1''; Clear H1''.
Rewrite H0; Intro.
Apply le_imp_Diffble_I with (S n); [Auto with arith | Assumption].
Exists (S n); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma n_deriv_plus : (m,n:nat)(F:PartIR)
  (H:(Diffble_I_n Hab' n F))(H':(Diffble_I_n Hab' (plus m n) F))
  (Derivative_I_n Hab' m (n_deriv_I ?? H) (n_deriv_I ?? H')).
(* End_Tex_Verb *)
Intro; Induction m.
Simpl.
Intros.
Apply n_deriv_I_wd.
Unfold I; Apply Feq_reflexive.
Exact (Diffble_I_n_imp_inc ????? H).
Intros.
Simpl.
Cut (Diffble_I_n Hab' (S n) F).
Intro.
Exists (IntPartIR (n_deriv_inc ?? H0)).
EApply Derivative_I_wdr.
2: Apply n_Sn_deriv with H':=H0.
FEQ.
Apply n_deriv_inc.
Cut (Diffble_I_n Hab' (plus m n) (PartInt (ProjS1 (Diffble_I_n_imp_diffble ??? (S n) (lt_O_Sn n) F H0)))).
Intro.
EApply Derivative_I_n_wdr.
2: EApply Derivative_I_n_wdl.
3: Apply Hrecm with H':=H1.
Apply n_deriv_I_wd.
Unfold I Hab; Apply Derivative_I_unique with F.
Apply projS2.
Apply projS2.
FEQ.
Apply n_deriv_inc.
Simpl; Algebra.
Elim H'; Intros.
EApply Diffble_I_n_wd.
2: Apply p.
Apply Derivative_I_unique with F.
Apply projS2.
Apply projS2.
Apply le_imp_Diffble_I with (plus (S m) n).
Simpl; Rewrite plus_sym; Auto with arith.
Assumption.
Qed.

End More_Results.

Section More_on_n_deriv.

(* Tex_Prose
Some not so basic properties of this operation (needed in rather specific situations).
*)

(* Begin_Tex_Verb *)
Lemma n_deriv_I_wd' : (n:nat)(a,b,Hab,a',b',Hab':?)(F:PartIR)
  (H,H':?)(x,y:IR)(x[=]y)->(Compact (less_leEq ??? Hab) x)->
                           (Compact (less_leEq ??? Hab') y)->
  (Diffble_I_n (Min_less_Max ?? a' b' Hab) n F)->
  (Hx,Hy:?)((n_deriv_I a b Hab n F H) x Hx)[=]
    ((n_deriv_I a' b' Hab' n F H') y Hy).
(* End_Tex_Verb *)
Intros.
Cut (included (Compact (less_leEq ??? Hab)) (Pred (n_deriv_I ????? H3))); Intros.
Cut (included (Compact (less_leEq ??? Hab')) (Pred (n_deriv_I ????? H3))); Intros.
Apply eq_transitive_unfolded with (Part (FRestr H5) y H2).
Apply eq_transitive_unfolded with (Part (FRestr H4) x H1).
Apply Feq_imp_eq with (Compact (less_leEq ??? Hab)).
Apply Derivative_I_n_unique with n F.
Apply n_deriv_lemma.
Apply Derivative_I_n_wdr with (n_deriv_I ????? H3).
FEQ.
Apply included_imp_deriv_n with Hab':=(Min_less_Max a b a' b' Hab).
Red; Intros.
Inversion_clear H6; Split.
Apply leEq_transitive with a.
Apply Min_leEq_lft.
Auto.
Apply leEq_transitive with b.
Auto.
Apply lft_leEq_Max.
Apply n_deriv_lemma.
Auto.
Simpl; Algebra.
Apply eq_symmetric_unfolded.
Apply Feq_imp_eq with (Compact (less_leEq ??? Hab')).
Apply Derivative_I_n_unique with n F.
Apply n_deriv_lemma.
Apply Derivative_I_n_wdr with (n_deriv_I ????? H3).
FEQ.
Apply included_imp_deriv_n with Hab':=(Min_less_Max a b a' b' Hab).
Red; Intros.
Inversion_clear H6; Split.
Apply leEq_transitive with a'.
Apply Min_leEq_rht.
Auto.
Apply leEq_transitive with b'.
Auto.
Apply rht_leEq_Max.
Apply n_deriv_lemma.
Auto.
Red; Intros.
Apply n_deriv_inc.
Inversion_clear H5; Split.
Apply leEq_transitive with a'.
Apply Min_leEq_rht.
Auto.
Apply leEq_transitive with b'.
Auto.
Apply rht_leEq_Max.
Red; Intros.
Apply n_deriv_inc.
Inversion_clear H4; Split.
Apply leEq_transitive with a.
Apply Min_leEq_lft.
Auto.
Apply leEq_transitive with b.
Auto.
Apply lft_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma n_deriv_I_wd'' : (n:nat)(a,b,Hab,Hab':?)(F:PartIR)(H,H':?)
  (x,y:IR)(x[=]y)->(Compact (less_leEq ??? Hab) x)->
                   (Compact (less_leEq ??? Hab) y)->
  (Hx,Hy:?)((n_deriv_I a b Hab n F H) x Hx)[=]
    ((n_deriv_I a b Hab' n F H') y Hy).
(* End_Tex_Verb *)
Intros.
Apply n_deriv_I_wd'.
Algebra.
Auto.
Auto.
Apply included_imp_diffble_n with Hab':=Hab.
2: Auto.
Red; Intros.
Inversion_clear H3; Split.
EApply leEq_wdl.
Apply H4.
Apply Min_id.
EApply leEq_wdr.
Apply H5.
Apply Max_id.
Qed.

(* Begin_Tex_Verb *)
Lemma n_deriv_I_strext' : (n:nat)(a,b,Hab,a',b',Hab':?)(F:PartIR)
  (H,H':?)(x,y:IR)(Compact (less_leEq ??? Hab) x)->
                  (Compact (less_leEq ??? Hab') y)->
  (Diffble_I_n (Min_less_Max ?? a' b' Hab) n F)->
  ((Hx,Hy:?)((n_deriv_I a b Hab n F H) x Hx)[#]
    ((n_deriv_I a' b' Hab' n F H') y Hy))->(x[#]y).
(* End_Tex_Verb *)
Intros.
Cut (Compact (less_leEq ??? (Min_less_Max a b a' b' Hab)) x); Intros.
Cut (Compact (less_leEq ??? (Min_less_Max a b a' b' Hab)) y); Intros.
Apply pfstrx with (n_deriv_I ????? H2) (n_deriv_inc ????? H2 ? H4) (n_deriv_inc ????? H2 ? H5).
Apply ap_well_def_rht_unfolded with (Part (n_deriv_I ????? H') y (n_deriv_inc ????? H' y H1)).
Apply ap_well_def_lft_unfolded with (Part (n_deriv_I ????? H) x (n_deriv_inc ????? H x H0)).
Auto.
Apply Feq_imp_eq with (Compact (less_leEq ??? Hab)).
Apply Derivative_I_n_unique with n F.
Apply n_deriv_lemma.
Apply included_imp_deriv_n with Hab':=(Min_less_Max a b a' b' Hab).
Red; Intros.
Inversion_clear H6; Split.
Apply leEq_transitive with a.
Apply Min_leEq_lft.
Auto.
Apply leEq_transitive with b.
Auto.
Apply lft_leEq_Max.
Apply n_deriv_lemma.
Auto.
Apply Feq_imp_eq with (Compact (less_leEq ??? Hab')).
Apply Derivative_I_n_unique with n F.
Apply n_deriv_lemma.
Apply included_imp_deriv_n with Hab':=(Min_less_Max a b a' b' Hab).
Red; Intros.
Inversion_clear H6; Split.
Apply leEq_transitive with a'.
Apply Min_leEq_rht.
Auto.
Apply leEq_transitive with b'.
Auto.
Apply rht_leEq_Max.
Apply n_deriv_lemma.
Auto.
Red; Intros.
Inversion_clear H1; Split.
Apply leEq_transitive with a'.
Apply Min_leEq_rht.
Auto.
Apply leEq_transitive with b'.
Auto.
Apply rht_leEq_Max.
Red; Intros.
Inversion_clear H0; Split.
Apply leEq_transitive with a.
Apply Min_leEq_lft.
Auto.
Apply leEq_transitive with b.
Auto.
Apply lft_leEq_Max.
Qed.

End More_on_n_deriv.
