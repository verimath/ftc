(* $Id: CPolynomials.v,v 1.12 2003/03/11 13:35:52 lcf Exp $ *)

Require Export CRings.

(* Tex_Prose
\chapter{Polynomials}
The first section only proves the polynomials form a ring, and nothing more
interesting.
Section~\ref{section:poly-equality} gives some basic properties of
equality and induction of polynomials.
\section{Definition of polynomials; they form a ring}
\label{section:poly-ring}
*)

Section CPoly_CRing.
(* Tex_Prose
\begin{convention}
Let \verb!CR! be a ring.
\end{convention}
*)

Variable CR:CRing.

(* Tex_Prose
\begin{itemize}
\item \verb!(cpoly CR)! is $R[X]$;
\item \verb!cpoly_zero! is the `empty' polynomial with no coefficients;
\item \verb!(cpoly_linear c p)! is $c + X * p$
\end{itemize}
*)

(* Begin_Tex_Verb *)
Inductive cpoly : Set :=
    cpoly_zero : cpoly
  | cpoly_linear : (s:CR)(c:cpoly)cpoly.

Definition cpoly_constant [c:CR]: cpoly := (cpoly_linear c cpoly_zero).
Definition cpoly_one: cpoly := (cpoly_constant One).
(* End_Tex_Verb *)

(* Tex_Prose
Some useful induction lemmas for doubly quantified propositions.
*)

(* Begin_Tex_Verb *)
Lemma Ccpoly_double_ind0 : (P:cpoly->cpoly->CProp)
   ((p:cpoly)(P p cpoly_zero)) ->
   ((p:cpoly)(P cpoly_zero p)) ->
   ((p,q:cpoly)(c,d:CR)(P p q)->(P (cpoly_linear c p) (cpoly_linear d q))) ->
   (p,q:cpoly)(P p q).
(* End_Tex_Verb *)
Induction p; Auto.
Induction q; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_double_sym_ind0 : (P:cpoly->cpoly->CProp)
   (Csymmetric P) ->
   ((p:cpoly)(P p cpoly_zero)) ->
   ((p,q:cpoly)(c,d:CR)(P p q)->(P (cpoly_linear c p) (cpoly_linear d q))) ->
   (p,q:cpoly)(P p q).
(* End_Tex_Verb *)
Intros.
Apply Ccpoly_double_ind0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_double_ind0' : (P:cpoly->cpoly->CProp)
   ((p:cpoly)(P cpoly_zero p)) ->
   ((p:cpoly)(c:CR)(P (cpoly_linear c p) cpoly_zero)) ->
   ((p,q:cpoly)(c,d:CR)(P p q)->(P (cpoly_linear c p) (cpoly_linear d q))) ->
   (p,q:cpoly)(P p q).
(* End_Tex_Verb *)
Induction p; Auto.
Induction q; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_double_ind0 : (P:cpoly->cpoly->Prop)
   ((p:cpoly)(P p cpoly_zero)) ->
   ((p:cpoly)(P cpoly_zero p)) ->
   ((p,q:cpoly)(c,d:CR)(P p q)->(P (cpoly_linear c p) (cpoly_linear d q))) ->
   (p,q:cpoly)(P p q).
(* End_Tex_Verb *)
Induction p; Auto.
Induction q; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_double_sym_ind0 : (P:cpoly->cpoly->Prop)
   (symmetric P) ->
   ((p:cpoly)(P p cpoly_zero)) ->
   ((p,q:cpoly)(c,d:CR)(P p q)->(P (cpoly_linear c p) (cpoly_linear d q))) ->
   (p,q:cpoly)(P p q).
(* End_Tex_Verb *)
Intros.
Apply cpoly_double_ind0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_double_ind0' : (P:cpoly->cpoly->Prop)
   ((p:cpoly)(P cpoly_zero p)) ->
   ((p:cpoly)(c:CR)(P (cpoly_linear c p) cpoly_zero)) ->
   ((p,q:cpoly)(c,d:CR)(P p q)->(P (cpoly_linear c p) (cpoly_linear d q))) ->
   (p,q:cpoly)(P p q).
(* End_Tex_Verb *)
Induction p; Auto.
Induction q; Auto.
Qed.

(* Tex_Prose
\subsection{The polynomials form a setoid}
*)
(* Begin_Tex_Verb *)
Fixpoint cpoly_eq_zero [p:cpoly] : Prop :=
  Cases p of
    cpoly_zero => True
  | (cpoly_linear c p1) => (c [=] Zero) /\ (cpoly_eq_zero p1)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint cpoly_eq [p:cpoly] : cpoly->Prop := [q:cpoly]
  Cases p of
    cpoly_zero => (cpoly_eq_zero q)
  | (cpoly_linear c p1) =>
      Cases q of
        cpoly_zero => (cpoly_eq_zero p)
      | (cpoly_linear d q1) => (c [=] d) /\ (cpoly_eq p1 q1)
      end
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_eq_p_zero : (p:cpoly)(cpoly_eq p cpoly_zero) == (cpoly_eq_zero p).
(* End_Tex_Verb *)
Induction p; Auto.
Qed.

(* Tex_Prose
The annoying thing about \verb!cpoly_eq_p_zero! is that this lemma cannot be
used with the \verb!Rewrite! tactic when the goal lives in \verb!CProp!
(instead of \verb!Prop!). This is because \verb!==! gives a \verb!Prop!, and
Coq's type system does not allow \verb!Prop! elimination over a \verb!CProp!.

The remedy would be to introduce a \verb!CProp!-valued equality, say\
\verb!CProp_eq!.
Unfortunately, the \verb!Rewrite!-tactic does not work for \verb!CProp_eq!.
Therefore we are forced to introduce two lemmas stating the implications
back and forth.
*)

(* Begin_Tex_Verb *)
Lemma cpoly_eq_p_zero_ : (p:cpoly)(cpoly_eq p cpoly_zero) -> (cpoly_eq_zero p).
(* End_Tex_Verb *)
Induction p; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma _cpoly_eq_p_zero : (p:cpoly)(cpoly_eq_zero p) -> (cpoly_eq p cpoly_zero).
(* End_Tex_Verb *)
Induction p; Auto.
Qed.


(* Begin_Tex_Verb *)
Fixpoint cpoly_ap_zero [p:cpoly] : CProp :=
  Cases p of
    cpoly_zero => CFalse
  | (cpoly_linear c p1) => (c [#] Zero) + (cpoly_ap_zero p1)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint cpoly_ap [p:cpoly] : cpoly->CProp := [q:cpoly]
  Cases p of
    cpoly_zero => (cpoly_ap_zero q)
  | (cpoly_linear c p1) =>
      Cases q of
        cpoly_zero => (cpoly_ap_zero p)
      | (cpoly_linear d q1) => (c [#] d) + (cpoly_ap p1 q1)
      end
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_ap_p_zero : 
        (p:cpoly)(cpoly_ap_zero p) == (cpoly_ap p cpoly_zero).
(* End_Tex_Verb *)
Induction p; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma _cpoly_ap_p_zero : 
        (p:cpoly)(cpoly_ap_zero p) -> (cpoly_ap p cpoly_zero).
(* End_Tex_Verb *)
Induction p; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_ap_p_zero_ : 
        (p:cpoly)(cpoly_ap p cpoly_zero) -> (cpoly_ap_zero p).
(* End_Tex_Verb *)
Induction p; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma irreflexive_cpoly_ap : (irreflexive cpoly_ap).
(* End_Tex_Verb *)
Red.
Intro p; Induction p.
Intro H; Elim H.
Intro H.
Elim H.
 Apply ap_irreflexive_unfolded.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma symmetric_cpoly_ap : (Csymmetric cpoly_ap).
(* End_Tex_Verb *)
Red.
Intros x y.
Pattern x y.
Apply Ccpoly_double_ind0'.
  Simpl; Induction p; Auto.
 Simpl; Auto.
Simpl.
Intros p q c d H H0.
Elim H0; Intro H1.
 Left.
 Apply ap_symmetric_unfolded.
 Assumption.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cotransitive_cpoly_ap : (cotransitive cpoly_ap).
(* End_Tex_Verb *)
Red.
Intros x y.
Pattern x y.
Apply Ccpoly_double_sym_ind0.
  Red; Intros p q H H0 r.
  Generalize (symmetric_cpoly_ap ? ? H0); Intro H1.
  Elim (H H1 r); Intro H2; [Right | Left]; Apply symmetric_cpoly_ap; Assumption.
 Simpl; Intros p H z.
 Generalize H.
 Pattern p z.
 Apply Ccpoly_double_ind0'.
   Simpl; Intros q H0; Elim H0.
  Simpl; Auto.
 Simpl; Intros r q c d H0 H1.
 Elim H1; Intro H2.
  Generalize (ap_cotransitive_unfolded ? ? ? H2 d); Intro H3.
  Elim H3; Auto.
 Generalize (_cpoly_ap_p_zero ? H2); Clear H2; Intro H2.
 Elim (H0 H2); Auto.
 Right; Right; Apply cpoly_ap_p_zero_; Assumption.
Intros p q c d H H0 r.
Simpl in H0.
Elim H0; Intro H1.
 Induction r.
  Simpl.
  Generalize (ap_cotransitive_unfolded ? ? ? H1 Zero); Intro H2.
  Elim H2; Auto.
  Intro H3.
  Right; Left; Apply ap_symmetric_unfolded; Assumption.
 Simpl.
 Generalize (ap_cotransitive_unfolded ? ? ? H1 s); Intro H2.
 Elim H2; Auto.
Induction r.
 Simpl.
 Cut (cpoly_ap_zero p)+(cpoly_ap_zero q).
  Intro H2; Elim H2; Auto.
 Generalize H1; Pattern p q; Apply Ccpoly_double_ind0.
   Simpl.
   Intros r H2.
   Left; Apply cpoly_ap_p_zero_; Assumption.
  Auto.
 Simpl.
 Intros p0 q0 c0 d0 H2 H3.
 Elim H3; Intro H4.
  Elim (ap_cotransitive_unfolded ? ? ? H4 Zero); Intro H5.
   Auto.
  Right; Left; Apply ap_symmetric_unfolded; Assumption.
 Elim (H2 H4); Auto.
Simpl.
Elim (H H1 r); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma tight_apart_cpoly_ap : (tight_apart cpoly_eq cpoly_ap).
(* End_Tex_Verb *)
Red.
Intros x y.
Pattern x y.
Apply cpoly_double_ind0'.
  Induction p.
   Simpl.
   Unfold iff.
   Unfold Not.
   Split.
    Auto.
   Intros H H0; Inversion H0.
  Simpl.
  Intros s c H.
  Cut (Not (s[#]Zero))<->(s[=]Zero).
   Unfold Not.
   Intro H0.
   Elim H0; Intros H1 H2.
   Split.
    Intro H3.
    Split; Auto.
    Elim H; Intros H4 H5.
    Apply H4.
    Intro H6.
    Auto.
   Intros H3 H4.
   Elim H3; Intros H5 H6.
   Elim H4; Intros H7.
    Auto.
   Elim H; Intros H8 H9.
   Unfold Not in H8.
   Elim H9; Assumption.
  Apply (ap_tight CR).
 Induction p.
  Simpl.
  Intro c.
  Cut (Not (c[#]Zero))<->(c[=]Zero).
   Unfold Not.
   Intro H.
   Elim H; Intros H0 H1.
   Split.
    Auto.
   Intros H2 H3.
   Elim H3; Intro H4.
    Tauto.
   Elim H4.
  Apply (ap_tight CR).
 Simpl.
 Intros s c H d.
 Generalize (H d).
 Generalize (ap_tight CR d Zero).
 Generalize (ap_tight CR s Zero).
 Unfold Not.
 Intros H0 H1 H2.
 Elim H0; Clear H0; Intros H3 H4.
 Elim H1; Clear H1; Intros H0 H5.
 Elim H2; Clear H2; Intros H1 H6.
 Tauto.
Simpl.
Unfold Not.
Intros p q c d H.
Elim H; Intros H0 H1.
Split.
 Intro H2.
 Split.
  Generalize (ap_tight CR c d).
  Unfold Not; Tauto.
 Tauto.
Intros H2 H3.
Elim H3.
 Elim H2.
 Intros H4 H5 H6.
 Generalize (ap_tight CR c d).
 Unfold Not.
 Tauto.
Elim H2.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_is_CSetoid : (is_CSetoid ? cpoly_eq cpoly_ap).
(* End_Tex_Verb *)
Apply Build_is_CSetoid.
Exact irreflexive_cpoly_ap.
Exact symmetric_cpoly_ap.
Exact cotransitive_cpoly_ap.
Exact tight_apart_cpoly_ap.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_csetoid :=
                    (Build_CSetoid cpoly cpoly_eq cpoly_ap cpoly_is_CSetoid).
(* End_Tex_Verb *)

(* Tex_Prose
Now that we know that the polynomials form a setoid, we can use the
notation with \verb![#]! and \verb![=]!. In order to use this notation,
we introduce \verb!cpoly_zero_cs! and \verb!cpoly_linear_cs!, so that Coq
recognizes we are talking about a setoid.
We formulate the induction properties and
the most basic properties of equality and apartness
in terms of these generators.
*)

(* Begin_Tex_Verb *)
Local cpoly_zero_cs := cpoly_zero : cpoly_csetoid.

Local cpoly_linear_cs [c:CR; p:cpoly_csetoid] : cpoly_csetoid :=
                      (cpoly_linear c p).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Ccpoly_ind_cs : (P:cpoly_csetoid->CProp)
   (P cpoly_zero_cs) ->
   ((p:cpoly_csetoid)(c:CR)(P p)->(P (cpoly_linear_cs c p))) ->
   (p:cpoly_csetoid)(P p).
(* End_Tex_Verb *)
Induction p; Auto.
Unfold cpoly_linear_cs in H0.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_double_ind0_cs : (P:cpoly_csetoid->cpoly_csetoid->CProp)
   ((p:cpoly_csetoid)(P p cpoly_zero_cs)) ->
   ((p:cpoly_csetoid)(P cpoly_zero_cs p)) ->
   ((p,q:cpoly_csetoid)(c,d:CR)
                 (P p q)->(P (cpoly_linear_cs c p) (cpoly_linear_cs d q))) ->
   (p,q:cpoly_csetoid)(P p q).
(* End_Tex_Verb *)
Induction p.
Auto.
Induction q.
Auto.
Simpl in H1.
Unfold cpoly_linear_cs in H1.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_double_sym_ind0_cs : (P:cpoly_csetoid->cpoly_csetoid->CProp)
   (Csymmetric P) ->
   ((p:cpoly_csetoid)(P p cpoly_zero_cs)) ->
   ((p,q:cpoly_csetoid)(c,d:CR)(P p q)->
                       (P (cpoly_linear_cs c p) (cpoly_linear_cs d q))) ->
   (p,q:cpoly_csetoid)(P p q).
(* End_Tex_Verb *)
Intros.
Apply Ccpoly_double_ind0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_ind_cs : (P:cpoly_csetoid->Prop)
   (P cpoly_zero_cs) ->
   ((p:cpoly_csetoid)(c:CR)(P p)->(P (cpoly_linear_cs c p))) ->
   (p:cpoly_csetoid)(P p).
(* End_Tex_Verb *)
Induction p; Auto.
Unfold cpoly_linear_cs in H0.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_double_ind0_cs : (P:cpoly_csetoid->cpoly_csetoid->Prop)
   ((p:cpoly_csetoid)(P p cpoly_zero_cs)) ->
   ((p:cpoly_csetoid)(P cpoly_zero_cs p)) ->
   ((p,q:cpoly_csetoid)(c,d:CR)
                 (P p q)->(P (cpoly_linear_cs c p) (cpoly_linear_cs d q))) ->
   (p,q:cpoly_csetoid)(P p q).
(* End_Tex_Verb *)
Induction p.
Auto.
Induction q.
Auto.
Simpl in H1.
Unfold cpoly_linear_cs in H1.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_double_sym_ind0_cs : (P:cpoly_csetoid->cpoly_csetoid->Prop)
   (symmetric P) ->
   ((p:cpoly_csetoid)(P p cpoly_zero_cs)) ->
   ((p,q:cpoly_csetoid)(c,d:CR)(P p q)->
                       (P (cpoly_linear_cs c p) (cpoly_linear_cs d q))) ->
   (p,q:cpoly_csetoid)(P p q).
(* End_Tex_Verb *)
Intros.
Apply cpoly_double_ind0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_eq_zero_ : (p:cpoly_csetoid)(c:CR)
     ((cpoly_linear_cs c p) [=] cpoly_zero_cs) ->
     ((c [=] Zero) /\ (p [=] (cpoly_zero_cs))).
(* End_Tex_Verb *)
Unfold cpoly_linear_cs.
Unfold cpoly_zero_cs.
Simpl.
Intros p c H.
Elim H; Intros.
Split; Auto.
Apply _cpoly_eq_p_zero.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma _cpoly_lin_eq_zero : (p:cpoly_csetoid)(c:CR)
     ((c [=] Zero) /\ (p [=] (cpoly_zero_cs))) ->
     ((cpoly_linear_cs c p) [=] cpoly_zero_cs).
(* End_Tex_Verb *)
Unfold cpoly_linear_cs.
Unfold cpoly_zero_cs.
Simpl.
Intros p c H.
Elim H; Intros.
Split; Auto.
Apply cpoly_eq_p_zero_.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_zero_eq_lin_ : (p:cpoly_csetoid)(c:CR)
     (cpoly_zero_cs [=] (cpoly_linear_cs c p)) ->
     ((c [=] Zero) /\ ((cpoly_zero_cs) [=] p)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma _cpoly_zero_eq_lin : (p:cpoly_csetoid)(c:CR)
     ((c [=] Zero) /\ ((cpoly_zero_cs) [=] p)) ->
     (cpoly_zero_cs [=] (cpoly_linear_cs c p)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_eq_lin_ : (p,q:cpoly_csetoid)(c,d:CR)
     ((cpoly_linear_cs c p) [=] (cpoly_linear_cs d q)) ->
     ((c [=] d) /\ (p [=] q)).
(* End_Tex_Verb *)
Auto.
Qed.


(* Begin_Tex_Verb *)
Lemma _cpoly_lin_eq_lin : (p,q:cpoly_csetoid)(c,d:CR)
     ((c [=] d) /\ (p [=] q)) ->
     ((cpoly_linear_cs c p) [=] (cpoly_linear_cs d q)).
(* End_Tex_Verb *)
Auto.
Qed.


(* Begin_Tex_Verb *)
Lemma cpoly_lin_ap_zero_ : (p:cpoly_csetoid)(c:CR)
     ((cpoly_linear_cs c p) [#] cpoly_zero_cs) ->
     ((c [#] Zero) + (p [#] (cpoly_zero_cs))).
(* End_Tex_Verb *)
Unfold cpoly_zero_cs.
Intros p c H.
Cut (cpoly_ap (cpoly_linear c p) cpoly_zero); Auto.
Intro H0.
Simpl in H0.
Elim H0; Auto.
Right.
Apply _cpoly_ap_p_zero.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma _cpoly_lin_ap_zero : (p:cpoly_csetoid)(c:CR)
     ((c [#] Zero) + (p [#] cpoly_zero_cs)) ->
     ((cpoly_linear_cs c p) [#] cpoly_zero_cs).
(* End_Tex_Verb *)
Unfold cpoly_zero_cs.
Intros.
Simpl.
Elim H; Try Auto.
Intros.
Right.
Apply cpoly_ap_p_zero_.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_ap_zero : (p:cpoly_csetoid)(c:CR)
     ((cpoly_linear_cs c p) [#] cpoly_zero_cs) ==
     ((c [#] Zero) + (p [#] (cpoly_zero_cs))).
(* End_Tex_Verb *)
Intros.
Simpl.
Unfold cpoly_zero_cs.
Rewrite cpoly_ap_p_zero.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_zero_ap_lin_ : (p:cpoly_csetoid)(c:CR)
               (cpoly_zero_cs [#] (cpoly_linear_cs c p)) ->
               ((c [#] Zero) + ((cpoly_zero_cs) [#] p)).
(* End_Tex_Verb *)
Intros.
Simpl.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma _cpoly_zero_ap_lin : (p:cpoly_csetoid)(c:CR)
               ((c [#] Zero) + ((cpoly_zero_cs) [#] p)) ->
               (cpoly_zero_cs [#] (cpoly_linear_cs c p)).
(* End_Tex_Verb *)
Intros.
Simpl.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_zero_ap_lin : (p:cpoly_csetoid)(c:CR)
     (cpoly_zero_cs [#] (cpoly_linear_cs c p)) ==
     ((c [#] Zero) + ((cpoly_zero_cs) [#] p)).
(* End_Tex_Verb *)
Intros.
Simpl.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_ap_lin_ : (p,q:cpoly_csetoid)(c,d:CR)
     ((cpoly_linear_cs c p) [#] (cpoly_linear_cs d q)) ->
     ((c [#] d) + (p [#] q)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma _cpoly_lin_ap_lin : (p,q:cpoly_csetoid)(c,d:CR)
     ((c [#] d) + (p [#] q)) ->
     ((cpoly_linear_cs c p) [#] (cpoly_linear_cs d q)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_ap_lin : (p,q:cpoly_csetoid)(c,d:CR)
     ((cpoly_linear_cs c p) [#] (cpoly_linear_cs d q)) ==
     ((c [#] d) + (p [#] q)).
(* End_Tex_Verb *)
Intros.
Simpl.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_linear_strext : (bin_fun_strong_ext ? ? ? cpoly_linear_cs).
(* End_Tex_Verb *)
Unfold bin_fun_strong_ext.
Intros.
Apply cpoly_lin_ap_lin_.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_linear_wd : (bin_fun_well_def ? ? ? cpoly_linear_cs).
(* End_Tex_Verb *)
Apply bin_fun_strong_ext_imp_well_def.
Exact cpoly_linear_strext.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_linear_fun :=
  (Build_CSetoid_bin_fun ? ? ? ? cpoly_linear_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Ccpoly_double_comp_ind : (P : cpoly_csetoid -> cpoly_csetoid -> CProp)
 ((p1,p2,q1,q2:cpoly_csetoid)((p1[=]p2)->(q1[=]q2)->(P p1 q1)->(P p2 q2))) ->
 (P cpoly_zero_cs cpoly_zero_cs) ->
 ((p,q:cpoly_csetoid)(c,d:CR)(P p q)->
                           (P (cpoly_linear_cs c p) (cpoly_linear_cs d q))) ->
 (p,q:cpoly_csetoid)(P p q).
(* End_Tex_Verb *)
Intros.
Apply Ccpoly_double_ind0_cs.
Intro p0; Pattern p0; Apply Ccpoly_ind_cs.
Assumption.
Intros.
Apply H with (cpoly_linear_cs c p1) (cpoly_linear_cs Zero cpoly_zero_cs).
Algebra.
Apply _cpoly_lin_eq_zero.
Split; Algebra.
Apply H1.
Assumption.

Intro p0; Pattern p0; Apply Ccpoly_ind_cs.
Assumption.
Intros.
Apply H with (cpoly_linear_cs Zero cpoly_zero_cs) (cpoly_linear_cs c p1).
Apply _cpoly_lin_eq_zero.
Split; Algebra.
Algebra.
Apply H1.
Assumption.
Intros.
Apply H1.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_triple_comp_ind :
 (P : cpoly_csetoid -> cpoly_csetoid -> cpoly_csetoid -> CProp)
 ((p1,p2,q1,q2,r1,r2:cpoly_csetoid)((p1[=]p2)->(q1[=]q2)->(r1[=]r2)->
                    (P p1 q1 r1)->(P p2 q2 r2))) ->
 (P cpoly_zero_cs cpoly_zero_cs cpoly_zero_cs) ->
 ((p,q,r:cpoly_csetoid)(c,d,e:CR)(P p q r)->
     (P (cpoly_linear_cs c p) (cpoly_linear_cs d q) (cpoly_linear_cs e r))) ->
 (p,q,r:cpoly_csetoid)(P p q r).
(* End_Tex_Verb *)
Do 6 Intro.
Pattern p q.
Apply Ccpoly_double_comp_ind.
Intros.
Apply H with p1 q1 r.
Assumption.
Assumption.
Algebra.
Apply H4.

Intro r; Pattern r; Apply Ccpoly_ind_cs.
Assumption.
Intros.
Apply H with (cpoly_linear_cs Zero cpoly_zero_cs)
             (cpoly_linear_cs Zero cpoly_zero_cs)
             (cpoly_linear_cs c p0).
Apply _cpoly_lin_eq_zero; Split; Algebra.
Apply _cpoly_lin_eq_zero; Split; Algebra.
Algebra.
Apply H1.
Assumption.

Do 6 Intro.
Pattern r; Apply Ccpoly_ind_cs.
Apply H with (cpoly_linear_cs c p0)
             (cpoly_linear_cs d q0)
             (cpoly_linear_cs Zero cpoly_zero_cs).
Algebra.
Algebra.
Apply _cpoly_lin_eq_zero; Split; Algebra.
Apply H1.
Apply H2.
Intros.
Apply H1.
Apply H2.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_double_comp_ind : (P : cpoly_csetoid -> cpoly_csetoid -> Prop)
 ((p1,p2,q1,q2:cpoly_csetoid)((p1[=]p2)->(q1[=]q2)->(P p1 q1)->(P p2 q2))) ->
 (P cpoly_zero_cs cpoly_zero_cs) ->
 ((p,q:cpoly_csetoid)(c,d:CR)(P p q)->
                           (P (cpoly_linear_cs c p) (cpoly_linear_cs d q))) ->
 (p,q:cpoly_csetoid)(P p q).
(* End_Tex_Verb *)
Intros.
Apply cpoly_double_ind0_cs.
Intro p0; Pattern p0; Apply cpoly_ind_cs.
Assumption.
Intros.
Apply H with (cpoly_linear_cs c p1) (cpoly_linear_cs Zero cpoly_zero_cs).
Algebra.
Apply _cpoly_lin_eq_zero.
Split; Algebra.
Apply H1.
Assumption.

Intro p0; Pattern p0; Apply cpoly_ind_cs.
Assumption.
Intros.
Apply H with (cpoly_linear_cs Zero cpoly_zero_cs) (cpoly_linear_cs c p1).
Apply _cpoly_lin_eq_zero.
Split; Algebra.
Algebra.
Apply H1.
Assumption.
Intros.
Apply H1.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_triple_comp_ind :
 (P : cpoly_csetoid -> cpoly_csetoid -> cpoly_csetoid -> Prop)
 ((p1,p2,q1,q2,r1,r2:cpoly_csetoid)((p1[=]p2)->(q1[=]q2)->(r1[=]r2)->
                    (P p1 q1 r1)->(P p2 q2 r2))) ->
 (P cpoly_zero_cs cpoly_zero_cs cpoly_zero_cs) ->
 ((p,q,r:cpoly_csetoid)(c,d,e:CR)(P p q r)->
     (P (cpoly_linear_cs c p) (cpoly_linear_cs d q) (cpoly_linear_cs e r))) ->
 (p,q,r:cpoly_csetoid)(P p q r).
(* End_Tex_Verb *)
Do 6 Intro.
Pattern p q.
Apply cpoly_double_comp_ind.
Intros.
Apply H with p1 q1 r.
Assumption.
Assumption.
Algebra.
Apply H4.

Intro r; Pattern r; Apply cpoly_ind_cs.
Assumption.
Intros.
Apply H with (cpoly_linear_cs Zero cpoly_zero_cs)
             (cpoly_linear_cs Zero cpoly_zero_cs)
             (cpoly_linear_cs c p0).
Apply _cpoly_lin_eq_zero; Split; Algebra.
Apply _cpoly_lin_eq_zero; Split; Algebra.
Algebra.
Apply H1.
Assumption.

Do 6 Intro.
Pattern r; Apply cpoly_ind_cs.
Apply H with (cpoly_linear_cs c p0)
             (cpoly_linear_cs d q0)
             (cpoly_linear_cs Zero cpoly_zero_cs).
Algebra.
Algebra.
Apply _cpoly_lin_eq_zero; Split; Algebra.
Apply H1.
Apply H2.
Intros.
Apply H1.
Apply H2.
Qed.

(* Tex_Prose
\subsection{The polynomials form a semi-group and a monoid}
*)
(* Begin_Tex_Verb *)
Fixpoint cpoly_plus [p:cpoly] : cpoly -> cpoly := [q:cpoly]
  Cases p of
    cpoly_zero => q
  | (cpoly_linear c p1) =>
      Cases q of
        cpoly_zero => p
      | (cpoly_linear d q1) => (cpoly_linear c[+]d (cpoly_plus p1 q1))
      end
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition cpoly_plus_cs [p,q:cpoly_csetoid] : cpoly_csetoid
                                             := (cpoly_plus p q).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_zero_plus : (p:cpoly_csetoid)(cpoly_plus_cs cpoly_zero_cs p) = p.
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_plus_zero : (p:cpoly_csetoid)(cpoly_plus_cs p cpoly_zero_cs) = p.
(* End_Tex_Verb *)
Induction p.
Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_plus_lin : (p,q:cpoly_csetoid)(c,d:CR)
             (cpoly_plus_cs (cpoly_linear_cs c p) (cpoly_linear_cs d q)) =
             (cpoly_linear_cs (c[+]d) (cpoly_plus_cs p q)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_plus_commutative :
               (p,q:cpoly_csetoid)(cpoly_plus_cs p q) [=] (cpoly_plus_cs q p).
(* End_Tex_Verb *)
Intros.
Pattern p q.
Apply cpoly_double_sym_ind0_cs.
Unfold symmetric.
Intros.
Algebra.
Intro p0.
Rewrite cpoly_zero_plus.
Rewrite cpoly_plus_zero.
Algebra.
Intros.
Repeat Rewrite cpoly_lin_plus_lin.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_plus_q_ap_q : (p,q:cpoly_csetoid)
              ((cpoly_plus_cs p q) [#] q) ->
              (p [#] cpoly_zero_cs).
(* End_Tex_Verb *)
Intro p; Pattern p; Apply Ccpoly_ind_cs.
Intro.
Rewrite cpoly_zero_plus.
Intro.
ElimType False.
Apply (ap_irreflexive ? ? H).
Do 4 Intro.
Pattern q; Apply Ccpoly_ind_cs.
Rewrite cpoly_plus_zero.
Auto.
Do 3 Intro.
Rewrite cpoly_lin_plus_lin.
Intros.
Cut ((c [+] c0) [#] c0) + ((cpoly_plus_cs p0 p1) [#] p1).
Intros.
2: Apply cpoly_lin_ap_lin_.
2: Assumption.
Cut (c[#]Zero) + (p0[#]cpoly_zero_cs).
Intro. Apply _cpoly_lin_ap_zero. Assumption.
Elim H2; Intro.
Left.
Apply cg_ap_cancel_rht with c0.
Stepr c0.
Right.
Generalize (H ? b); Intro.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_p_plus_ap_p : (p,q:cpoly_csetoid)
              ((cpoly_plus_cs p q) [#] p) -> (q [#] cpoly_zero).
(* End_Tex_Verb *)
Intros.
Apply cpoly_plus_q_ap_q with p.
Apply ap_well_def_lft_unfolded  with (cpoly_plus_cs p q).
Assumption.
Apply cpoly_plus_commutative.
Qed.


(* Begin_Tex_Verb *)
Lemma cpoly_ap_zero_plus : (p,q:cpoly_csetoid)
              ((cpoly_plus_cs p q) [#] cpoly_zero_cs) ->
              (p [#] cpoly_zero_cs) + (q [#] cpoly_zero_cs).
(* End_Tex_Verb *)
Intros p q; Pattern p q; Apply Ccpoly_double_sym_ind0_cs.
Unfold Csymmetric.
Intros.
Elim H.
Auto. Auto.
Step (cpoly_plus_cs y x).
Apply cpoly_plus_commutative.
Intros.
Left.
Rewrite cpoly_plus_zero in H.
Assumption.
Intros p0 q0 c d.
Rewrite cpoly_lin_plus_lin.
Intros.
Cut (c[+]d [#] Zero) + ((cpoly_plus_cs p0 q0) [#] cpoly_zero_cs).
2: Apply cpoly_lin_ap_zero_.
2: Assumption.
Clear H0.
Intros.
Elim H0; Intro H1.
Cut c[+]d [#] Zero[+]Zero.
Intro H2.
Elim (bin_op_strext ? ? ? ? ? ? H2); Intro H3.
Left.
Simpl.
Left.
Assumption.
Right.
Cut (d[#]Zero) + (q0[#]cpoly_zero_cs).
Intro.
Apply _cpoly_lin_ap_zero.
Auto.
Left.
Assumption.
Stepr (Zero::CR).
Elim (H H1); Intro.
Left.
Cut (c[#]Zero) + (p0[#]cpoly_zero_cs).
Intro; Apply _cpoly_lin_ap_zero.
Auto.
Right.
Assumption.
Right.
Cut (d[#]Zero) + (q0[#]cpoly_zero_cs).
Intro.
Apply _cpoly_lin_ap_zero.
Auto.
Right.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_plus_op_strext : (bin_op_strong_ext cpoly_csetoid cpoly_plus_cs).
(* End_Tex_Verb *)
Unfold bin_op_strong_ext.
Unfold bin_fun_strong_ext.
Intros x1 x2.
Pattern x1 x2.
Apply Ccpoly_double_sym_ind0_cs.
Unfold Csymmetric.
Intros.
Generalize (ap_symmetric_unfolded ? ? ? H0); Intro.
Generalize (H ? ? H1); Intro.
Elim H2; Intro H3; Generalize (ap_symmetric_unfolded ? ? ? H3); Auto.
Intro p; Pattern p; Apply Ccpoly_ind_cs.
Intro; Intro.
Simpl; Auto.
Intros s c H y1 y2.
Pattern y1 y2.
Apply Ccpoly_double_ind0_cs.
Intros.
Apply cpoly_ap_zero_plus.
Apply H0.
Intro.
Intro.
Elim (ap_cotransitive ? ? ? H0 cpoly_zero_cs); Auto.
Do 4 Intro.
Intros.
Cut ((c[+]c0) [#] d) + ((cpoly_plus_cs s p0) [#] q).
2: Apply cpoly_lin_ap_lin_; Assumption.
Clear H1; Intro H1.
Elim H1; Intro H2.
Cut c[+]c0 [#] Zero[+]d.
Intro.
Elim (bin_op_strext ? ? ? ? ? ? H3).
Intro H4.
Left.
Apply _cpoly_lin_ap_zero.
Auto.
Intro.
Right.
Apply _cpoly_lin_ap_lin.
Auto.
Stepr d.
Elim (H ? ? H2); Auto.
Intro.
Left.
Apply _cpoly_lin_ap_zero.
Auto.
Right.
Apply _cpoly_lin_ap_lin.
Auto.

Do 7 Intro.
Pattern y1 y2.
Apply Ccpoly_double_ind0_cs.
Intro p0; Pattern p0; Apply Ccpoly_ind_cs.
Auto.
Intros.
Cut ((c[+]c0) [#] d) + ((cpoly_plus_cs p p1) [#]q).
Intro.
2:Apply cpoly_lin_ap_lin_.
2: Auto.
Elim H2; Intro H3.
Cut c[+]c0 [#] d [+] Zero.
Intro.
Elim (bin_op_strext ? ? ? ? ? ? H4).
Intro.
Left.
Apply _cpoly_lin_ap_lin.
Auto.
Intro.
Right.
Apply _cpoly_lin_ap_zero.
Auto.
Stepr d.
Elim H with p1 cpoly_zero_cs.
Intro.
Left.
Apply _cpoly_lin_ap_lin.
Auto.
Right.
Apply _cpoly_lin_ap_zero.
Auto.
Rewrite cpoly_plus_zero.
Assumption.
Intro p0; Pattern p0; Apply Ccpoly_ind_cs.
Auto.
Intros.
Cut (c[#](d[+]c0)) + (p[#](cpoly_plus_cs q p1)).
2: Apply cpoly_lin_ap_lin_.
2: Assumption.
Clear H1; Intro H1.
Elim H1; Intro H2.
Cut c[+]Zero [#] d [+] c0.
Intro.
Elim (bin_op_strext ? ? ? ? ? ? H3).
Intro.
Left.
Unfold cpoly_linear_cs; Simpl; Auto.
Intro.
Right.
Left.
Apply ap_symmetric_unfolded.
Assumption.
Step c.
Elim H with cpoly_zero_cs p1.
Intro.
Left.
Unfold cpoly_linear_cs; Simpl; Auto.
Intro.
Right.
Right; Auto.
Rewrite cpoly_plus_zero.
Assumption.
Intros.
Elim H1; Intro H2.
Elim (bin_op_strext ? ? ? ? ? ? H2); Auto.
Intro.
Left.
Left; Auto.
Intro. Right.
Left; Auto.
Simpl in H2.
Elim (H ?? H2).
Intro.
Left; Right; Auto.
Right; Right; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_plus_op_proof : (bin_op_well_def cpoly_csetoid cpoly_plus_cs).
(* End_Tex_Verb *)
Unfold bin_op_well_def.
Apply bin_fun_strong_ext_imp_well_def.
Exact cpoly_plus_op_strext.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_plus_op :=
  (Build_CSetoid_bin_op ? ? cpoly_plus_op_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_plus_associative : (associative cpoly_plus_op).
(* End_Tex_Verb *)
Unfold associative.
Intros p q r.
Change (cpoly_plus_cs p (cpoly_plus_cs q r)) [=]
       (cpoly_plus_cs (cpoly_plus_cs p q) r).
Pattern p q r; Apply cpoly_triple_comp_ind.
Intros.
Apply eq_transitive_unfolded with (cpoly_plus_cs p1 (cpoly_plus_cs q1 r1)).
Apply eq_symmetric_unfolded.
Apply cpoly_plus_op_proof.
Assumption.
Apply cpoly_plus_op_proof.
Assumption.
Assumption.
Step_lft (cpoly_plus_cs (cpoly_plus_cs p1 q1) r1).
Apply cpoly_plus_op_proof.
Apply cpoly_plus_op_proof.
Assumption.
Assumption.
Assumption.
Simpl.
Auto.
Intros.
Repeat Rewrite cpoly_lin_plus_lin.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_csemi_grp :=
       (Build_CSemi_grp cpoly_csetoid cpoly_zero cpoly_plus_op
                        cpoly_plus_associative).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_cm_proof : (is_CMonoid cpoly_csemi_grp).
(* End_Tex_Verb *)
Apply Build_is_CMonoid.
Unfold is_rht_unit.
Intro.
Rewrite cpoly_plus_zero.
Algebra.
Unfold commutes.
Intros.
Apply cpoly_plus_commutative.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_cmonoid := (Build_CMonoid ? cpoly_cm_proof).
(* End_Tex_Verb *)

(* Tex_Prose
\subsection{The polynomials form a group}
*)

(* Begin_Tex_Verb *)
Fixpoint cpoly_inv [p:cpoly] : cpoly :=
  Cases p of
    cpoly_zero => cpoly_zero
  | (cpoly_linear c p1) => (cpoly_linear [--]c (cpoly_inv p1))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition cpoly_inv_cs [p:cpoly_csetoid] : cpoly_csetoid := (cpoly_inv p).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_inv_zero : (cpoly_inv_cs cpoly_zero_cs) = cpoly_zero_cs.
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_inv_lin : (p:cpoly_csetoid)(c:CR)
    (cpoly_inv_cs (cpoly_linear_cs c p)) =
    (cpoly_linear_cs ([--]c) (cpoly_inv_cs p)).
(* End_Tex_Verb *)
Induction p.
Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_inv_op_strext : (un_op_strong_ext cpoly_csetoid cpoly_inv_cs).
(* End_Tex_Verb *)
Unfold un_op_strong_ext.
Unfold fun_strong_ext.
Intros x y.
Pattern x y.
Apply Ccpoly_double_sym_ind0_cs.
Unfold Csymmetric.
Intros.
Apply ap_symmetric_unfolded.
Apply H.
Apply ap_symmetric_unfolded.
Assumption.
Intro p; Pattern p; Apply Ccpoly_ind_cs.
Auto.
Intros.
Cut ([--]c [#] Zero)+((cpoly_inv_cs p0) [#] cpoly_zero_cs).
2: Apply cpoly_lin_ap_zero_.
2: Auto.
Clear H0; Intro H0.
Apply _cpoly_lin_ap_zero.
Auto.
Elim H0.
Left.
Step [--][--]c.
Right.
Apply H.
Assumption.
Intros.
Cut ([--]c[#][--]d) + ((cpoly_inv_cs p)[#](cpoly_inv_cs q)).
2: Apply cpoly_lin_ap_lin_.
2: Auto.
Clear H0; Intro H0.
Auto.
Elim H0; Intro.
Left.
Step [--][--]c.
Stepr [--][--]d.
Apply inv_resp_ap.
Assumption.
Right.
Apply H.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_inv_op_proof : (un_op_well_def cpoly_csetoid cpoly_inv_cs).
(* End_Tex_Verb *)
Unfold un_op_well_def.
Apply fun_strong_ext_imp_well_def.
Exact cpoly_inv_op_strext.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_inv_op :=
  (Build_CSetoid_un_op ? ? cpoly_inv_op_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_cg_proof : (is_CGroup cpoly_cmonoid cpoly_inv_op).
(* End_Tex_Verb *)
Unfold is_CGroup.
Intro.
Unfold is_inverse.
Change x[+](cpoly_inv_cs x) [=] Zero.
Pattern x; Apply cpoly_ind_cs.
Rewrite cpoly_inv_zero.
Rewrite cpoly_plus_zero.
Simpl.
Auto.
Intros.
Rewrite cpoly_inv_lin.
Rewrite cpoly_lin_plus_lin.
Apply _cpoly_lin_eq_zero.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_cgroup := (Build_CGroup ? ? cpoly_cg_proof).
(* End_Tex_Verb *)

(* Tex_Prose
\subsection{The polynomials form a ring}
*)
(* Begin_Tex_Verb *)
Fixpoint cpoly_mult_cr [q:cpoly] : CR -> cpoly := [c:CR]
  Cases q of
    cpoly_zero => cpoly_zero
  | (cpoly_linear d q1) => (cpoly_linear c[*]d (cpoly_mult_cr q1 c))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint cpoly_mult [p:cpoly] : cpoly -> cpoly := [q:cpoly]
  Cases p of
    cpoly_zero => cpoly_zero
  | (cpoly_linear c p1) =>
      (cpoly_plus (cpoly_mult_cr q c)
                  (cpoly_linear Zero (cpoly_mult p1 q)))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition cpoly_mult_cr_cs [p:cpoly_csetoid; c:CR] : cpoly_csetoid
                                                    := (cpoly_mult_cr p c).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_zero_mult_cr : (c:CR)
                            (cpoly_mult_cr_cs cpoly_zero_cs c)=cpoly_zero_cs.
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_mult_cr : (c,d:CR)(q:cpoly_csetoid)
                              (cpoly_mult_cr_cs (cpoly_linear_cs d q) c) =
                              (cpoly_linear_cs c[*]d (cpoly_mult_cr_cs q c)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_cr_zero : (p:cpoly_csetoid)
                           (cpoly_mult_cr_cs p Zero) [=] cpoly_zero_cs.
(* End_Tex_Verb *)
Intro; Pattern p; Apply cpoly_ind_cs.
Rewrite cpoly_zero_mult_cr.
Algebra.
Intros.
Rewrite cpoly_lin_mult_cr.
Apply _cpoly_lin_eq_zero.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_cr_strext :
          (bin_fun_strong_ext cpoly_cgroup CR cpoly_cgroup cpoly_mult_cr_cs).
(* End_Tex_Verb *)
Unfold bin_fun_strong_ext.
Do 4 Intro.
Pattern x1 x2.
Apply Ccpoly_double_ind0_cs.
Intro.
Rewrite cpoly_zero_mult_cr.
Intro.
Left.
Generalize H.
Pattern p.
Apply Ccpoly_ind_cs.
Rewrite cpoly_zero_mult_cr.
Auto.
Do 2 Intro.
Rewrite cpoly_lin_mult_cr.
Intros.
Cut (y1[*]c[#]Zero)+((cpoly_mult_cr_cs p0 y1)[#]cpoly_zero_cs).
2: Apply cpoly_lin_ap_zero_.
2: Auto.
Clear H1; Intro H1.
Cut (c[#]Zero)+(p0[#]cpoly_zero_cs).
Intro; Apply _cpoly_lin_ap_zero.
Auto.
Elim H1; Intro H2.
Generalize (cring_mult_ap_zero_op ? ? ? H2); Intro.
Auto.
Right.
Auto.

Rewrite cpoly_zero_mult_cr.
Intros.
Left.
Generalize H.
Pattern p; Apply Ccpoly_ind_cs.
Rewrite cpoly_zero_mult_cr.
Auto.
Do 2 Intro.
Rewrite cpoly_lin_mult_cr.
Intros.
Cut (y2[*]c[#]Zero)+(cpoly_zero_cs[#](cpoly_mult_cr_cs p0 y2)).
2: Apply cpoly_zero_ap_lin_.
2: Auto.
Clear H1; Intro H1.
Cut (c[#]Zero) + (cpoly_zero_cs[#] p0).
Intro. 
Apply _cpoly_zero_ap_lin. Auto.
Elim H1; Intro H2.
Generalize (cring_mult_ap_zero_op ? ? ? H2); Auto.
Right.
Auto.

Do 4 Intro.
Repeat Rewrite cpoly_lin_mult_cr.
Intros.
Cut (y1[*]c[#]y2[*]d)+((cpoly_mult_cr_cs p y1)[#](cpoly_mult_cr_cs q y2)).
2: Apply cpoly_lin_ap_lin_.
2: Auto.
Clear H0; Intro H0.
Cut ((c[#]d)+(p[#]q))+(y1 [#] y2).
Intro. 
Elim H1; Try Auto.
Elim H0; Intro H1.
Generalize (bin_op_strext ? ? ? ? ? ? H1); Tauto.
Elim H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_cr_wd :
           (bin_fun_well_def cpoly_cgroup CR cpoly_cgroup cpoly_mult_cr_cs).
(* End_Tex_Verb *)
Apply bin_fun_strong_ext_imp_well_def.
Exact cpoly_mult_cr_strext.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_mult_cs [p,q:cpoly_csetoid] : cpoly_csetoid
                                             := (cpoly_mult p q).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_zero_mult : (q:cpoly_csetoid)
                        (cpoly_mult_cs cpoly_zero_cs q)=cpoly_zero_cs.
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_lin_mult : (c:CR)(p,q:cpoly_csetoid)
                         (cpoly_mult_cs (cpoly_linear_cs c p) q) =
                         (cpoly_plus_cs (cpoly_mult_cr_cs q c)
                             (cpoly_linear_cs Zero (cpoly_mult_cs p q))).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_op_strext : (bin_op_strong_ext cpoly_csetoid cpoly_mult_cs).
(* End_Tex_Verb *)
Do 4 Intro.
Pattern x1 x2.
Apply Ccpoly_double_ind0_cs.
Rewrite cpoly_zero_mult.
Intro; Pattern p; Apply Ccpoly_ind_cs.
Rewrite cpoly_zero_mult.
Auto.
Do 2 Intro.
Rewrite cpoly_lin_mult.
Intros.
Cut ((c[#]Zero)+(p0[#]cpoly_zero_cs))+(y1[#]y2).
Intro. Elim H1.  Intro; Left; Apply _cpoly_lin_ap_zero; Assumption.
Auto.
Cut (cpoly_plus_cs (cpoly_mult_cr_cs y1 c)
         (cpoly_linear_cs Zero (cpoly_mult_cs p0 y1))) [#]
    (cpoly_plus_cs (cpoly_mult_cr_cs y2 Zero)
         (cpoly_linear_cs Zero (cpoly_mult_cs cpoly_zero_cs y2))).
Intro.
Elim (cpoly_plus_op_strext ? ? ? ? H1); Intro H2.
Elim (cpoly_mult_cr_strext ? ? ? ? H2); Auto.
Elim H2; Intro H3.
Elim (ap_irreflexive ? ? H3).
Rewrite cpoly_zero_mult in H3.
Elim H; Auto.
Rewrite cpoly_zero_mult.
Apply ap_well_def_rht_unfolded with cpoly_zero_cs.
Assumption.
Step (cpoly_plus_cs cpoly_zero_cs cpoly_zero_cs).
Apply cpoly_plus_op_proof.
Apply eq_symmetric_unfolded.
Apply cpoly_mult_cr_zero.
Apply _cpoly_zero_eq_lin.
Split; Algebra.

Intro; Pattern p; Apply Ccpoly_ind_cs.
Auto.
Intros.
Cut ((c[#]Zero)+(cpoly_zero_cs[#]p0))+(y1[#]y2).
Intro. 
Elim H1; Try Auto.
Cut (cpoly_plus_cs (cpoly_mult_cr_cs y1 Zero)
         (cpoly_linear_cs Zero (cpoly_mult_cs cpoly_zero_cs y1))) [#]
    (cpoly_plus_cs (cpoly_mult_cr_cs y2 c)
         (cpoly_linear_cs Zero (cpoly_mult_cs p0 y2))).
Intro.
Elim (cpoly_plus_op_strext ? ? ? ? H1); Intro H2.
Elim (cpoly_mult_cr_strext ? ? ? ? H2); Auto.
Intro.
Left. Left.
Apply ap_symmetric_unfolded.
Assumption.
Cut ((Zero::CR)[#]Zero)+((cpoly_mult_cs cpoly_zero_cs y1) [#] 
                         (cpoly_mult_cs p0 y2)).
2: Apply cpoly_lin_ap_lin_; Auto.
Clear H2; Intro H2.
Elim H2; Intro H3.
Elim (ap_irreflexive ? ? H3).
Rewrite cpoly_zero_mult in H3.
Elim H; Auto.
Rewrite cpoly_zero_mult.
Apply ap_well_def_lft_unfolded with cpoly_zero_cs.
Assumption.
Step (cpoly_plus_cs cpoly_zero_cs cpoly_zero_cs).
Apply cpoly_plus_op_proof.
Apply eq_symmetric_unfolded.
Apply cpoly_mult_cr_zero.
Apply _cpoly_zero_eq_lin.
Split; Algebra.

Intros.
Cut ((c[#]d)+(p[#]q))+(y1[#]y2).
Intro.
Auto.
Elim (cpoly_plus_op_strext ? ? ? ? H0); Intro H1.
Elim (cpoly_mult_cr_strext ? ? ? ? H1); Auto.
Elim H1; Intro H2.
Elim (ap_irreflexive ? ? H2).
Elim H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_op_proof : (bin_op_well_def cpoly_csetoid cpoly_mult).
(* End_Tex_Verb *)
Unfold bin_op_well_def.
Apply bin_fun_strong_ext_imp_well_def.
Exact cpoly_mult_op_strext.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_mult_op :=
  (Build_CSetoid_bin_op ? ? cpoly_mult_op_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_mult_cr_dist : (p,q:cpoly_csetoid)(c:CR)
               (cpoly_mult_cr_cs (cpoly_plus_cs p q) c) [=]
               (cpoly_plus_cs (cpoly_mult_cr_cs p c) (cpoly_mult_cr_cs q c)).
(* End_Tex_Verb *)
Intros.
Pattern p q.
Apply cpoly_double_comp_ind.
Intros.
Apply eq_transitive_unfolded  with (cpoly_mult_cr_cs (cpoly_plus_cs p1 q1) c).
Apply eq_symmetric_unfolded.
Apply cpoly_mult_cr_wd.
Apply cpoly_plus_op_proof.
Assumption.
Assumption.
Algebra.
Step_lft  (cpoly_plus_cs (cpoly_mult_cr_cs p1 c) (cpoly_mult_cr_cs q1 c)).
Apply cpoly_plus_op_proof.
Apply cpoly_mult_cr_wd; Algebra.
Apply cpoly_mult_cr_wd; Algebra.
Repeat Rewrite cpoly_zero_plus.
Algebra.
Intros.
Repeat Rewrite cpoly_lin_mult_cr.
Repeat Rewrite cpoly_lin_plus_lin.
Rewrite cpoly_lin_mult_cr.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_cr_dist : (distributive cpoly_mult_op cpoly_plus_op).
(* End_Tex_Verb *)
Unfold distributive.
Intros p q r.
Change (cpoly_mult_cs p (cpoly_plus_cs q r)) [=]
       (cpoly_plus_cs (cpoly_mult_cs p q) (cpoly_mult_cs p r)).
Pattern p. Apply cpoly_ind_cs.
Repeat Rewrite cpoly_zero_mult.
Rewrite cpoly_zero_plus.
Algebra.
Intros.
Repeat Rewrite cpoly_lin_mult.
Apply eq_transitive_unfolded with
 (cpoly_plus_cs
            (cpoly_plus_cs (cpoly_mult_cr_cs q c)
              (cpoly_mult_cr_cs r c))
            (cpoly_plus_cs (cpoly_linear_cs Zero (cpoly_mult_cs p0 q))
              (cpoly_linear_cs Zero (cpoly_mult_cs p0 r)))).
Apply cpoly_plus_op_proof.
Apply cpoly_mult_cr_dist.
Rewrite cpoly_lin_plus_lin.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Assumption.
Clear H.
Apply eq_transitive_unfolded with
 (cpoly_plus_cs (cpoly_mult_cr_cs q c)
     (cpoly_plus_cs (cpoly_mult_cr_cs r c)
     (cpoly_plus_cs (cpoly_linear_cs Zero (cpoly_mult_cs p0 q))
       (cpoly_linear_cs Zero (cpoly_mult_cs p0 r))))).
Apply eq_symmetric_unfolded.
Apply cpoly_plus_associative.
Apply eq_transitive_unfolded with
(cpoly_plus_cs (cpoly_mult_cr_cs q c)
            (cpoly_plus_cs
              (cpoly_linear_cs Zero (cpoly_mult_cs p0 q))
            (cpoly_plus_cs (cpoly_mult_cr_cs r c)
              (cpoly_linear_cs Zero (cpoly_mult_cs p0 r))))).
Apply cpoly_plus_op_proof.
Algebra.
Apply eq_transitive_unfolded with
 (cpoly_plus_cs (cpoly_plus_cs (cpoly_mult_cr_cs r c)
     (cpoly_linear_cs Zero (cpoly_mult_cs p0 q)))
       (cpoly_linear_cs Zero (cpoly_mult_cs p0 r))).
Apply cpoly_plus_associative.
Apply eq_transitive_unfolded with
(cpoly_plus_cs (cpoly_plus_cs (cpoly_linear_cs Zero (cpoly_mult_cs p0 q))
             (cpoly_mult_cr_cs r c))
              (cpoly_linear_cs Zero (cpoly_mult_cs p0 r))).
Apply cpoly_plus_op_proof.
Apply cpoly_plus_commutative.
Algebra.
Apply eq_symmetric_unfolded.
Apply cpoly_plus_associative.
Apply cpoly_plus_associative.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_cr_assoc_mult_cr : (p:cpoly_csetoid)(c,d:CR)
   (cpoly_mult_cr_cs (cpoly_mult_cr_cs p c) d)
      [=] (cpoly_mult_cr_cs p d[*]c).
(* End_Tex_Verb *)
Intros.
Pattern p; Apply cpoly_ind_cs.
Repeat Rewrite cpoly_zero_mult_cr.
Algebra.
Intros.
Repeat Rewrite cpoly_lin_mult_cr.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_cr_assoc_mult : (p,q:cpoly_csetoid)(c:CR)
          (cpoly_mult_cr_cs (cpoly_mult_cs p q) c)
      [=] (cpoly_mult_cs (cpoly_mult_cr_cs p c) q).
(* End_Tex_Verb *)
Intros.
Pattern p; Apply cpoly_ind_cs.
Rewrite cpoly_zero_mult.
Repeat Rewrite cpoly_zero_mult_cr.
Rewrite cpoly_zero_mult.
Algebra.
Intros.
Rewrite cpoly_lin_mult.
Repeat Rewrite cpoly_lin_mult_cr.
Rewrite cpoly_lin_mult.
Apply eq_transitive_unfolded with
(cpoly_plus_cs (cpoly_mult_cr_cs (cpoly_mult_cr_cs q c0) c)
            (cpoly_mult_cr_cs (cpoly_linear_cs Zero (cpoly_mult_cs p0 q)) c)).
Apply cpoly_mult_cr_dist.
Apply cpoly_plus_op_proof.
Apply cpoly_mult_cr_assoc_mult_cr.
Rewrite cpoly_lin_mult_cr.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_zero :
   (p:cpoly_csetoid)(cpoly_mult_cs p cpoly_zero_cs) [=] (cpoly_zero_cs).
(* End_Tex_Verb *)
Intros.
Pattern p; Apply cpoly_ind_cs.
Algebra.
Intros.
Rewrite cpoly_lin_mult.
Rewrite cpoly_zero_mult_cr.
Rewrite cpoly_zero_plus.
Apply _cpoly_lin_eq_zero.
Split.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_lin : (c:CR)(p,q:cpoly_csetoid)
                         (cpoly_mult_cs p (cpoly_linear_cs c q)) [=]
                         (cpoly_plus_cs (cpoly_mult_cr_cs p c)
                             (cpoly_linear_cs Zero (cpoly_mult_cs p q))).
(* End_Tex_Verb *)
Intros.
Pattern p; Apply cpoly_ind_cs.
Repeat Rewrite cpoly_zero_mult.
Rewrite cpoly_zero_mult_cr.
Rewrite cpoly_zero_plus.
Apply _cpoly_zero_eq_lin.
Algebra.
Intros.
Repeat Rewrite cpoly_lin_mult.
Repeat Rewrite cpoly_lin_mult_cr.
Repeat Rewrite cpoly_lin_plus_lin.
Apply _cpoly_lin_eq_lin. Split.
Algebra.
Apply eq_transitive_unfolded with
 (cpoly_plus_cs (cpoly_plus_cs (cpoly_mult_cr_cs p0 c)
            (cpoly_mult_cr_cs q c0))
              (cpoly_linear_cs Zero (cpoly_mult_cs p0 q))).
2: Apply eq_symmetric_unfolded.
2: Apply cpoly_plus_associative.
Apply eq_transitive_unfolded with
 (cpoly_plus_cs (cpoly_plus_cs (cpoly_mult_cr_cs q c0)
            (cpoly_mult_cr_cs p0 c))
              (cpoly_linear_cs Zero (cpoly_mult_cs p0 q))).
2: Apply cpoly_plus_op_proof.
3: Algebra.
2: Apply cpoly_plus_commutative.
Apply eq_transitive_unfolded with
 (cpoly_plus_cs (cpoly_mult_cr_cs q c0)
            (cpoly_plus_cs (cpoly_mult_cr_cs p0 c)
              (cpoly_linear_cs Zero (cpoly_mult_cs p0 q)))).
2: Apply cpoly_plus_associative.
Apply cpoly_plus_op_proof.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_commutative :
   (p,q:cpoly_csetoid)(cpoly_mult_cs p q) [=] (cpoly_mult_cs q p).
(* End_Tex_Verb *)
Intros.
Pattern p.
Apply cpoly_ind_cs.
Rewrite cpoly_zero_mult.
Apply eq_symmetric_unfolded.
Apply cpoly_mult_zero.
Intros.
Rewrite cpoly_lin_mult.
Apply eq_transitive_unfolded with
                         (cpoly_plus_cs (cpoly_mult_cr_cs q c)
                             (cpoly_linear_cs Zero (cpoly_mult_cs q p0))).
2: Apply eq_symmetric_unfolded; Apply cpoly_mult_lin.
Apply cpoly_plus_op_proof.
Algebra.
Apply cpoly_linear_wd.
Algebra.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_dist_rht :
   (p,q,r:cpoly_csetoid)
   (cpoly_mult_cs (cpoly_plus_cs p q) r) [=]
   (cpoly_plus_cs (cpoly_mult_cs p r) (cpoly_mult_cs q r)).
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with
 (cpoly_mult_cs r (cpoly_plus_cs p q)).
Apply cpoly_mult_commutative.
Apply eq_transitive_unfolded with
 (cpoly_plus_cs (cpoly_mult_cs r p) (cpoly_mult_cs r q)).
Generalize cpoly_cr_dist; Intro.
Unfold distributive in H.
Simpl in H.
Simpl.
Apply H.
Apply cpoly_plus_op_proof.
Apply cpoly_mult_commutative.
Apply cpoly_mult_commutative.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_assoc : (associative cpoly_mult_op).
(* End_Tex_Verb *)
Unfold associative.
Intros p q r.
Change (cpoly_mult_cs p (cpoly_mult_cs q r)) [=]
       (cpoly_mult_cs (cpoly_mult_cs p q) r).
Pattern p; Apply cpoly_ind_cs.
Repeat Rewrite cpoly_zero_mult.
Algebra.
Intros.
Repeat Rewrite cpoly_lin_mult.
Apply eq_transitive_unfolded with
(cpoly_plus_cs (cpoly_mult_cs (cpoly_mult_cr_cs q c) r)
               (cpoly_mult_cs (cpoly_linear_cs Zero (cpoly_mult_cs p0 q)) r)).
Apply cpoly_plus_op_proof.
Apply cpoly_mult_cr_assoc_mult.
Rewrite cpoly_lin_mult.
Apply eq_transitive_unfolded with
(cpoly_plus_cs cpoly_zero_cs
            (cpoly_linear_cs Zero
              (cpoly_mult_cs (cpoly_mult_cs p0 q) r))).
Rewrite cpoly_zero_plus.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Assumption.
Apply cpoly_plus_op_proof.
Apply eq_symmetric_unfolded.
Apply cpoly_mult_cr_zero.
Apply _cpoly_lin_eq_lin.
Split.
Algebra.
Algebra.
Apply eq_symmetric_unfolded.
Apply cpoly_mult_dist_rht.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_cr_one : (p:cpoly_csetoid)(cpoly_mult_cr_cs p One)[=]p.
(* End_Tex_Verb *)
Intro.
Pattern p; Apply cpoly_ind_cs.
Algebra.
Intros.
Rewrite cpoly_lin_mult_cr.
Apply _cpoly_lin_eq_lin.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_one_mult : (p:cpoly_csetoid)(cpoly_mult_cs cpoly_one p)[=]p.
(* End_Tex_Verb *)
Intro.
Unfold cpoly_one.
Unfold cpoly_constant.
Replace (cpoly_linear One cpoly_zero) with (cpoly_linear_cs One cpoly_zero).
2: Reflexivity.
Rewrite cpoly_lin_mult.
Rewrite cpoly_zero_mult.
Apply eq_transitive_unfolded with (cpoly_plus_cs p cpoly_zero_cs).
Apply cpoly_plus_op_proof.
Apply cpoly_mult_cr_one.
Apply _cpoly_lin_eq_zero; Algebra.
Rewrite cpoly_plus_zero; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_one : (p:cpoly_csetoid)(cpoly_mult_cs p cpoly_one)[=]p.
(* End_Tex_Verb *)
Intro.
Apply eq_transitive_unfolded with (cpoly_mult_cs cpoly_one p).
Apply cpoly_mult_commutative.
Apply cpoly_one_mult.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_mult_monoid: (is_CMonoid
   (Build_CSemi_grp cpoly_csetoid cpoly_one cpoly_mult_op cpoly_mult_assoc)).
(* End_Tex_Verb *)
Apply Build_is_CMonoid.
Exact cpoly_mult_one.
Exact cpoly_mult_commutative.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_cr_non_triv : (cpoly_ap cpoly_one cpoly_zero).
(* End_Tex_Verb *)
Change ((cpoly_linear_cs One cpoly_zero_cs)[#]cpoly_zero_cs).
Cut ((One::CR)[#]Zero)+(cpoly_zero_cs [#] cpoly_zero_cs).
Auto.
Left.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_is_CRing : (is_CRing cpoly_cgroup cpoly_one cpoly_mult_op).
(* End_Tex_Verb *)
Apply Build_is_CRing with cpoly_mult_assoc.
Exact cpoly_mult_monoid.
Exact cpoly_cr_dist.
Exact cpoly_cr_non_triv.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_cring :=
  (Build_CRing cpoly_cgroup cpoly_one cpoly_mult_op cpoly_is_CRing) : CRing.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_constant_strext : (!fun_strong_ext CR cpoly_cring cpoly_constant).
(* End_Tex_Verb *)
Unfold fun_strong_ext.
Unfold cpoly_constant.
Simpl.
Intros.
Elim H.
Auto.
Intro.
Elim b.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_constant_wd : (!fun_well_def CR cpoly_cring cpoly_constant).
(* End_Tex_Verb *)
Apply fun_strong_ext_imp_well_def.
Exact cpoly_constant_strext.
Qed.

(* Begin_Tex_Verb *)
Definition _C_ :=
  (Build_CSetoid_fun CR cpoly_cring cpoly_constant
                        cpoly_constant_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition _X_ : cpoly_cring := (cpoly_linear_cs Zero (One::cpoly_cring)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition cpoly_x_minus_c : CR -> cpoly_cring
                         := [c:CR](cpoly_linear_cs ([--]c) (One::cpoly_cring)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_x_minus_c_strext : (!fun_strong_ext CR cpoly_cring cpoly_x_minus_c).
(* End_Tex_Verb *)
Unfold fun_strong_ext.
Unfold cpoly_x_minus_c.
Simpl.
Intros.
Elim H; Intro H0.
Apply (un_op_strext ? ? ? ? H0).
Elim H0; Intro H1.
Elim (ap_irreflexive_unfolded ? ? H1).
Elim H1.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_x_minus_c_wd : (!fun_well_def CR cpoly_cring cpoly_x_minus_c).
(* End_Tex_Verb *)
Apply fun_strong_ext_imp_well_def.
Exact cpoly_x_minus_c_strext.
Qed.

End CPoly_CRing.

Implicits _C_ [1].
Implicits _X_ [1].

(* Begin_Tex_Verb *)
Definition cpoly_linear_fun'[CR:CRing]
           :  (CSetoid_bin_fun CR (cpoly_cring CR) (cpoly_cring CR))
           := (cpoly_linear_fun CR).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\verb!cpoly_linear_fun ? c p! is denoted with {\tt\hypertarget{Operator_25}{c [+X*] p}}.
\end{notation}
*)

Implicits cpoly_linear_fun' [1].
Infix 7 "[+X*]" cpoly_linear_fun'.

(* Tex_Prose
\section{Apartness, equality, and induction}
\label{section:poly-equality}
*)

Section CPoly_CRing_ctd.

Variable CR: CRing.

Syntactic Definition Cpoly_cring := (cpoly_cring CR).

(* Begin_Tex_Verb *)
Lemma linear_eq_zero_ : (p:Cpoly_cring)(c:CR)
     ((c [+X*] p) [=] Zero) -> ((c [=] Zero) /\ (p [=] Zero)).
(* End_Tex_Verb *)
Exact (cpoly_lin_eq_zero_ CR).
Qed.

(* Begin_Tex_Verb *)
Lemma _linear_eq_zero : (p:Cpoly_cring)(c:CR)
     ((c [=] Zero) /\ (p [=] Zero)) -> ((c [+X*] p) [=] Zero).
(* End_Tex_Verb *)
Exact (_cpoly_lin_eq_zero CR).
Qed.

(* Begin_Tex_Verb *)
Lemma zero_eq_linear_ : (p:Cpoly_cring)(c:CR)
     (Zero [=] c [+X*] p) -> ((c [=] Zero) /\ (Zero [=] p)).
(* End_Tex_Verb *)
Exact (cpoly_zero_eq_lin_ CR).
Qed.

(* Begin_Tex_Verb *)
Lemma _zero_eq_linear : (p:Cpoly_cring)(c:CR)
     ((c [=] Zero) /\ (Zero [=] p)) -> (Zero [=] c [+X*] p).
(* End_Tex_Verb *)
Exact (_cpoly_zero_eq_lin CR).
Qed.

(* Begin_Tex_Verb *)
Lemma linear_eq_linear_ : (p,q:Cpoly_cring)(c,d:CR)
     (c [+X*] p [=] d [+X*] q) -> ((c [=] d) /\ (p [=] q)).
(* End_Tex_Verb *)
Exact (cpoly_lin_eq_lin_ CR).
Qed.

(* Begin_Tex_Verb *)
Lemma _linear_eq_linear : (p,q:Cpoly_cring)(c,d:CR)
     ((c [=] d) /\ (p [=] q)) ->
     (c [+X*] p [=] d [+X*] q).
(* End_Tex_Verb *)
Exact (_cpoly_lin_eq_lin CR).
Qed.

(* Begin_Tex_Verb *)
Lemma linear_ap_zero_ : (p:Cpoly_cring)(c:CR)
     (c [+X*] p [#] Zero)  -> ((c [#] Zero) + (p [#] Zero)).
(* End_Tex_Verb *)
Exact (cpoly_lin_ap_zero_ CR).
Qed.

(* Begin_Tex_Verb *)
Lemma _linear_ap_zero : (p:Cpoly_cring)(c:CR)
    ((c [#] Zero) + (p [#] Zero)) -> (c [+X*] p [#] Zero). 
(* End_Tex_Verb *)
Exact (_cpoly_lin_ap_zero CR).
Qed.

(* Begin_Tex_Verb *)
Lemma linear_ap_zero : (p:Cpoly_cring)(c:CR)
     (c [+X*] p [#] Zero) == ((c [#] Zero) + (p [#] Zero)).
(* End_Tex_Verb *)
Exact (cpoly_lin_ap_zero CR).
Qed.

(* Begin_Tex_Verb *)
Lemma zero_ap_linear_ : (p:Cpoly_cring)(c:CR)
     (Zero [#] c [+X*] p) -> ((c [#] Zero) + (Zero [#] p)).
(* End_Tex_Verb *)
Exact (cpoly_zero_ap_lin_ CR).
Qed.

(* Begin_Tex_Verb *)
Lemma _zero_ap_linear : (p:Cpoly_cring)(c:CR)
        ((c [#] Zero) + (Zero [#] p)) -> (Zero [#] c [+X*] p). 
(* End_Tex_Verb *)
Exact (_cpoly_zero_ap_lin CR).
Qed.

(* Begin_Tex_Verb *)
Lemma zero_ap_linear : (p:Cpoly_cring)(c:CR)
     (Zero [#] c [+X*] p) == ((c [#] Zero) + (Zero [#] p)).
(* End_Tex_Verb *)
Exact (cpoly_zero_ap_lin CR).
Qed.

(* Begin_Tex_Verb *)
Lemma linear_ap_linear_ : (p,q:Cpoly_cring)(c,d:CR)
     (c [+X*] p [#] d [+X*] q) -> ((c [#] d) + (p [#] q)).
(* End_Tex_Verb *)
Exact (cpoly_lin_ap_lin_ CR).
Qed.

(* Begin_Tex_Verb *)
Lemma _linear_ap_linear : (p,q:Cpoly_cring)(c,d:CR)
   ((c [#] d) + (p [#] q)) -> (c [+X*] p [#] d [+X*] q).
(* End_Tex_Verb *)
Exact (_cpoly_lin_ap_lin CR).
Qed.

(* Begin_Tex_Verb *)
Lemma linear_ap_linear : (p,q:Cpoly_cring)(c,d:CR)
     (c [+X*] p [#] d [+X*] q) == ((c [#] d) + (p [#] q)).
(* End_Tex_Verb *)
Exact (cpoly_lin_ap_lin CR).
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_induc : (P:Cpoly_cring->CProp)
   (P Zero) ->
   ((p:Cpoly_cring)(c:CR)(P p)->(P (c [+X*] p))) ->
   (p:Cpoly_cring)(P p).
(* End_Tex_Verb *)
Exact (Ccpoly_ind_cs CR).
Qed.

(* Begin_Tex_Verb *)
Lemma Ccpoly_double_sym_ind : (P:Cpoly_cring->Cpoly_cring->CProp)
   (Csymmetric P) ->
   ((p:Cpoly_cring)(P p Zero)) ->
   ((p,q:Cpoly_cring)(c,d:CR)(P p q)->(P (c [+X*] p) (d [+X*] q))) ->
   (p,q:Cpoly_cring)(P p q).
(* End_Tex_Verb *)
Exact (Ccpoly_double_sym_ind0_cs CR).
Qed.

(* Begin_Tex_Verb *)
Lemma Cpoly_double_comp_ind : (P : Cpoly_cring -> Cpoly_cring -> CProp)
 ((p1,p2,q1,q2:Cpoly_cring)((p1[=]p2)->(q1[=]q2)->(P p1 q1)->(P p2 q2))) ->
 (P Zero Zero) ->
 ((p,q:Cpoly_cring)(c,d:CR)(P p q)->(P (c [+X*] p) (d [+X*] q))) ->
 (p,q:Cpoly_cring)(P p q).
(* End_Tex_Verb *)
Exact (Ccpoly_double_comp_ind CR).
Qed.

(* Begin_Tex_Verb *)
Lemma Cpoly_triple_comp_ind :
 (P : Cpoly_cring -> Cpoly_cring -> Cpoly_cring -> CProp)
 ((p1,p2,q1,q2,r1,r2:Cpoly_cring)((p1[=]p2)->(q1[=]q2)->(r1[=]r2)->
                    (P p1 q1 r1)->(P p2 q2 r2))) ->
 (P Zero Zero Zero) ->
 ((p,q,r:Cpoly_cring)(c,d,e:CR)(P p q r)->
         (P (c [+X*] p) (d [+X*] q) (e [+X*] r))) ->
 (p,q,r:Cpoly_cring)(P p q r).
(* End_Tex_Verb *)
Exact (Ccpoly_triple_comp_ind CR).
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_induc : (P:Cpoly_cring->Prop)
   (P Zero) ->
   ((p:Cpoly_cring)(c:CR)(P p)->(P (c [+X*] p))) ->
   (p:Cpoly_cring)(P p).
(* End_Tex_Verb *)
Exact (cpoly_ind_cs CR).
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_double_sym_ind : (P:Cpoly_cring->Cpoly_cring->Prop)
   (symmetric P) ->
   ((p:Cpoly_cring)(P p Zero)) ->
   ((p,q:Cpoly_cring)(c,d:CR)(P p q)->(P (c [+X*] p) (d [+X*] q))) ->
   (p,q:Cpoly_cring)(P p q).
(* End_Tex_Verb *)
Exact (cpoly_double_sym_ind0_cs CR).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_double_comp_ind : (P : Cpoly_cring -> Cpoly_cring -> Prop)
 ((p1,p2,q1,q2:Cpoly_cring)((p1[=]p2)->(q1[=]q2)->(P p1 q1)->(P p2 q2))) ->
 (P Zero Zero) ->
 ((p,q:Cpoly_cring)(c,d:CR)(P p q)->(P (c [+X*] p) (d [+X*] q))) ->
 (p,q:Cpoly_cring)(P p q).
(* End_Tex_Verb *)
Exact (cpoly_double_comp_ind CR).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_triple_comp_ind :
 (P : Cpoly_cring -> Cpoly_cring -> Cpoly_cring -> Prop)
 ((p1,p2,q1,q2,r1,r2:Cpoly_cring)((p1[=]p2)->(q1[=]q2)->(r1[=]r2)->
                    (P p1 q1 r1)->(P p2 q2 r2))) ->
 (P Zero Zero Zero) ->
 ((p,q,r:Cpoly_cring)(c,d,e:CR)(P p q r)->
         (P (c [+X*] p) (d [+X*] q) (e [+X*] r))) ->
 (p,q,r:Cpoly_cring)(P p q r).
(* End_Tex_Verb *)
Exact (cpoly_triple_comp_ind CR).
Qed.

Transparent cpoly_cring.
Transparent cpoly_cgroup.
Transparent cpoly_csetoid.

(* Begin_Tex_Verb *)
Fixpoint cpoly_apply [p:Cpoly_cring] : CR -> CR := [x:CR]
  Cases p of
    cpoly_zero => Zero
  | (cpoly_linear c p1) =>
      (c [+](x [*] (cpoly_apply p1 x)))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma cpoly_apply_strext : (bin_fun_strong_ext ??? cpoly_apply).
(* End_Tex_Verb *)
Unfold bin_fun_strong_ext.
Do 2 Intro.
Pattern x1 x2.
Apply Ccpoly_double_sym_ind.
Unfold Csymmetric.
Intros.
Generalize (ap_symmetric ? ? ? H0); Intro.
Elim (H ? ? H1); Intro.
Left.
Apply ap_symmetric_unfolded.
Assumption.
Right.
Apply ap_symmetric_unfolded.
Assumption.
Do 3 Intro.
Pattern p.
Apply Ccpoly_induc.
Simpl.
Intro.
Elim (ap_irreflexive ? ? H).
Intros.
Simpl in H0.
Simpl in H.
Cut c[+]y1[*](cpoly_apply p0 y1) [#] Zero[+]y1[*]Zero.
Intro.
Elim (bin_op_strext ? ? ? ? ? ? H1); Intro H2.
Left.
Cut (c[#]Zero) + (p0[#]Zero).
Intro.
Apply _linear_ap_zero.
Auto.
Left.
Assumption.
Elim (bin_op_strext ? ? ? ? ? ? H2); Intro H3.
Elim (ap_irreflexive ? ? H3).
Elim (H H3); Intro H4.
Left.
Cut (c[#]Zero) + (p0[#]Zero).
Intro; Apply _linear_ap_zero.
Auto.
Right.
Exact H4.
Auto.
Stepr Zero[+](Zero::CR).
Stepr (Zero::CR).
Simpl.
Intros.
Elim (bin_op_strext ? ? ? ? ? ? H0); Intro H1.
Auto.
Elim (bin_op_strext ? ? ? ? ? ? H1); Intro H2.
Auto.
Elim (H ? ? H2); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_apply_wd : (bin_fun_well_def ??? cpoly_apply).
(* End_Tex_Verb *)
Apply bin_fun_strong_ext_imp_well_def.
Exact cpoly_apply_strext.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_apply_fun := (Build_CSetoid_bin_fun ? ? ? ? cpoly_apply_strext).
(* End_Tex_Verb *)


End CPoly_CRing_ctd.

(* Tex_Prose
\begin{notation}
\verb!cpoly_apply_fun! is denoted infix by {\tt\hypertarget{Operator_26}{!}}.
The first argument is left implicit.
In the names of lemmas, we write \verb!apply!.
\end{notation}
*)

Implicits cpoly_apply_fun [1].
Infix NONA 1 "!" cpoly_apply_fun.

(* Tex_Prose
\section{Basic properties of polynomials}
\begin{convention}
Let \verb!R! be a ring and write \verb!RX! for the ring of polynomials
over \verb!R!.
\end{convention}
*)

Section Poly_properties.
Variable R : CRing.

Syntactic Definition RX := (cpoly_cring R).

(* Tex_Prose
\subsection{Constant and identity}
*)

(* Begin_Tex_Verb *)
Lemma cpoly_X_ : (_X_ [=] ((Zero::RX) [+X*] One)).
(* End_Tex_Verb *)
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_C_ : (c:RX)((_C_ c) [=] (c [+X*] Zero)).
(* End_Tex_Verb *)
Algebra.
Qed.

Hints Resolve cpoly_X_ cpoly_C_ : algebra.

(* Begin_Tex_Verb *)
Lemma cpoly_const_eq : (c,d:R)(c[=]d)->(_C_ c)[=](_C_ d).
(* End_Tex_Verb *)
Intros.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma _c_zero : Zero [=] (_C_ (Zero::R)).
(* End_Tex_Verb *)
Simpl.
Split; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma _c_one : One [=] (_C_ (One::R)).
(* End_Tex_Verb *)
Simpl; Split; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma _c_mult : (a,b:R)((_C_ a[*]b) [=] (_C_ a)[*](_C_ b)).
(* End_Tex_Verb *)
Simpl; Split; Algebra.
Qed.

(* !!! INSTEAD OF Step_rht *)
Tactic Definition Step_right y :=
  Apply eq_transitive_unfolded with y; [Idtac | Algebra].
(* FIXME *)
Grammar tactic simple_tactic : tactic :=
  Step_right [ "Step_right" constrarg($c) ] -> [ (Step_right $c) ].

(* Begin_Tex_Verb *)
Lemma cpoly_lin : (p:RX)(c:R)
                  (c [+X*] p) [=] ((_C_ c) [+] (_X_ [*] p)).
(* End_Tex_Verb *)
Intros.
Step_right (c [+X*] Zero) [+] (((cpoly_mult_cr_cs ? p Zero)::RX) [+]
 ((cpoly_linear ? (Zero :: R) (cpoly_mult_cs ? (cpoly_one R) p::(cpoly_csetoid R))):: (cpoly_csetoid R))).
Cut (cpoly_mult_cr_cs R p Zero) [=] ((Zero)::RX).
Intro.
Step_right (c [+X*] Zero) [+] (((Zero)::RX) [+]
 ((cpoly_linear ? (Zero :: R) (cpoly_mult_cs ? (cpoly_one R) p::(cpoly_csetoid R))):: (cpoly_csetoid R))).
2: Apply (cpoly_mult_cr_zero R p).
Cut ((cpoly_mult_cs ? (cpoly_one R) p::(cpoly_csetoid R)):: (cpoly_csetoid R)) [=] p.
Intro.
Apply eq_transitive_unfolded with
 (c [+X*] Zero) [+] (((Zero)::RX) [+]
 ((cpoly_linear ? (Zero :: R) (p::(cpoly_csetoid R))))).
2: Apply bin_op_wd_unfolded.
2: Algebra.
2: Apply bin_op_wd_unfolded.
2: Algebra.
2: Apply (cpoly_linear_wd R).
2: Algebra.
2: Apply eq_symmetric_unfolded.
2: Apply cpoly_one_mult.
Step_right (c [+X*] Zero) [+]
        (((cpoly_linear ? (Zero :: R) (p::(cpoly_csetoid R))))).
Step_right ((c[+]Zero) [+X*] (Zero[+]p)).
Step_right c [+X*] p.
Algebra.
Apply cpoly_one_mult.
Qed.

Hints Resolve cpoly_lin : algebra.

(* Begin_Tex_Verb *)
(* SUPERFLUOUS *)
Lemma poly_linear : (c:R)(f:RX)
  (((cpoly_linear ? c f)::RX) [=] _X_[*]f[+](_C_ c)).
(* End_Tex_Verb *)
Intros.
Step_rht (_C_ c)[+] _X_ [*] f.
Exact (cpoly_lin f c).
Qed.

(* Begin_Tex_Verb *)
Lemma poly_c_apzero : (a:R)((_C_ a) [#] Zero) -> (a [#] Zero).
(* End_Tex_Verb *)
Intros.
Cut (_C_ a) [#] (_C_ Zero).
Intro.
Generalize (csf_strext ? ? ? ? ? H0); Auto.
Hints Resolve _c_zero : algebra.
Stepr (Zero::RX).
Qed.

(* Begin_Tex_Verb *)
Lemma _c_mult_lin : (p:RX)(c,d:R)
                      (_C_ c) [*] (d [+X*] p) [=] c[*]d [+X*] ((_C_ c) [*] p).
(* End_Tex_Verb *)
Intros.
Pattern p.
Apply cpoly_induc.
Simpl.
Repeat Split; Algebra.
Intros. Simpl.
Repeat Split; Algebra.
Change ((cpoly_mult_cr R p0 c)::RX) [=] ((cpoly_mult_cr R p0 c)::RX) [+] Zero.
Algebra.
Qed.


(* Begin_Tex_Verb *)
(* SUPERFLUOUS ? *)
Lemma lin_mult : (p,q:RX)(c:R)
 ((c [+X*] p) [*] q) [=] (_C_ c) [*] q [+] _X_ [*] (p [*] q).
(* End_Tex_Verb *)
Intros.
Step_lft ((_C_ c) [+] (_X_ [*] p)) [*] q.
Step_lft ((_C_ c) [*] q) [+] ((_X_ [*] p) [*] q).
Algebra.
Qed.

Hints Resolve lin_mult : algebra.

(* Tex_Prose
\subsection{Application}
*)

(* Begin_Tex_Verb *)
Lemma poly_eq_zero :(p:RX)(p[=](cpoly_zero R)) -> (x:R)(p!x [=] Zero).
(* End_Tex_Verb *)
Intros.
Step_lft (cpoly_zero R)!x.
Change Zero!x [=] Zero.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma apply_wd : (p,p':RX)(x,x':R)(p [=] p')->(x [=] x')->(p!x [=] p'!x').
(* End_Tex_Verb *)
Intros.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cpolyap_pres_eq :(f:RX;x,y:R)(x[=]y)->(f!x)[=](f!y).
(* End_Tex_Verb *)
Intros.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cpolyap_strext :(f:RX;x,y:R)((f!x)[#](f!y))->(x[#]y).
(* End_Tex_Verb *)
Intros.
Elim (csbf_strext ? ? ? ? ? ? ? ? H); Intro H0.
Elim (ap_irreflexive_unfolded ? ? H0).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition cpoly_csetoid_op : RX -> (CSetoid_un_op R) :=
[f:RX](Build_CSetoid_fun ? ?[x:R](f!x) (cpolyap_strext f)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma _c_apply : (c,x:R)((_C_ c)!x [=] c).
(* End_Tex_Verb *)
Intros.
Simpl.
Step_lft c[+]Zero.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma _x_apply : (x:R)(_X_!x [=] x).
(* End_Tex_Verb *)
Intros.
Simpl.
Step_lft x[*](One[+]x[*]Zero).
Step_lft x[*](One[+]Zero).
Step_lft x[*]One.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_apply : (p,q:RX)(x:R)((p [+] q)!x [=] p!x [+] q!x).
(* End_Tex_Verb *)
Intros.
Pattern p q; Apply poly_double_comp_ind.
Intros.
Step_lft (p1[+]q1)!x.
Step_rht p1!x [+] q1!x.
Algebra.
Simpl.
Algebra.
Intros.
Step_lft c[+]d[+]x[*]((p0[+]q0)!x).
Step_rht (c[+] x [*] (p0!x)) [+] (d [+] x [*] (q0!x)).
Step_lft  c[+]d[+]x[*] (p0!x[+]q0!x).
Step_lft  c[+]d[+] (x[*] (p0!x) [+] x[*](q0!x)).
Step_lft  c[+] (d[+] (x[*] (p0!x) [+] x[*](q0!x))).
Step_rht c[+](x[*]p0!x[+](d[+]x[*]q0!x)).
Step_lft  c[+] (d[+] x[*] (p0!x) [+] x[*](q0!x)).
Step_rht c[+](x[*]p0!x[+]d[+]x[*]q0!x).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_apply : (p:RX)(x:R)(([--]p)!x [=] [--](p!x)).
(* End_Tex_Verb *)
Intros.
Pattern p.
Apply cpoly_induc.
Simpl.
Algebra.
Intros.
Step_lft ([--]c) [+] x [*] ([--]p0)!x.
Step_rht [--](c [+] x [*] (p0!x)).
Step_rht [--]c [+] [--](x [*] (p0!x)).
Step_rht [--]c [+] x[*][--](p0!x).
Algebra.
Qed.

Hints Resolve plus_apply inv_apply : algebra.

(* Begin_Tex_Verb *)
Lemma minus_apply : (p,q:RX)(x:R)((p [-] q)!x [=] p!x [-] q!x).
(* End_Tex_Verb *)
Intros.
Step_lft (p[+][--]q)!x.
Step_rht (p!x)[+][--](q!x).
Step_lft (p!x)[+]([--]q)!x.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma _c_mult_apply : (q:RX)(c,x:R)(((_C_ c) [*] q)!x [=] c [*] q!x).
(* End_Tex_Verb *)
Intros.
Step_lft (((cpoly_mult_cr R q c)::RX) [+] ((Zero [+X*] Zero)))!x.
Step_lft (cpoly_mult_cr R q c)!x [+] (Zero [+X*] Zero)!x.
Step_lft (cpoly_mult_cr R q c)!x [+] (Zero [+] x [*]Zero).
Step_lft (cpoly_mult_cr R q c)!x [+] (Zero [+] Zero).
Step_lft (cpoly_mult_cr R q c)!x [+] Zero.
Step_lft (cpoly_mult_cr R q c)!x.
Pattern q.
Apply cpoly_induc.
Simpl.
Algebra.
Intros.
Step_lft  ((c[*]c0) [+X*] (cpoly_mult_cr R p c))!x.
Step_lft (c[*]c0) [+] x [*] (cpoly_mult_cr R p c)!x.
Step_lft (c[*]c0) [+] x [*] (c[*]p!x).
Step_rht c[*](c0[+] x[*] (p!x)).
Step_rht c[*]c0 [+] c[*](x[*] (p!x)).
Apply bin_op_wd_unfolded.
Algebra.
Step_lft  x[*]c[*]p!x.
Step_rht c[*]x[*]p!x.
Algebra.
Qed.

Hints Resolve _c_mult_apply : algebra.

(* Begin_Tex_Verb *)
Lemma mult_apply : (p,q:RX)(x:R)((p [*] q)!x [=] p!x [*] q!x).
(* End_Tex_Verb *)
Intros.
Pattern p.
Apply cpoly_induc.
Simpl.
Algebra.
Intros.
Step_lft ((_C_ c)[*]q [+] _X_ [*] (p0[*]q))!x.
Step_lft ((_C_ c)[*]q)!x [+] (_X_ [*] (p0[*]q))!x.
Step_lft ((_C_ c)[*]q)!x [+] (Zero [+] _X_ [*] (p0[*]q))!x.
Step_lft ((_C_ c)[*]q)!x [+] ((_C_ Zero) [+] _X_ [*] (p0[*]q))!x.
Step_lft ((_C_ c)[*]q)!x [+] (Zero [+X*] (p0[*]q))!x.
Step_lft ((_C_ c)[*]q)!x [+] (Zero [+] x[*] (p0[*]q)!x).
Step_lft c[*](q!x) [+] (x[*] (p0[*]q)!x).
Step_lft c[*](q!x) [+] (x[*] ((p0!x)[*](q!x))).
Step_rht (c[+]x[*]p0!x)[*]q!x.
Step_rht c[*]q!x [+] (x[*]p0!x)[*]q!x.
Algebra.
Qed.

Hints Resolve mult_apply : algebra.

(* Begin_Tex_Verb *)
Lemma one_apply : (x:R)(One!x [=] One).
(* End_Tex_Verb *)
Intro.
Step_lft (_C_ One)!x.
Apply _c_apply.
Qed.

Hints Resolve one_apply : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_apply : (p:RX)(n:nat)(x:R)((p[^]n)!x [=] (p!x)[^]n).
(* End_Tex_Verb *)
Intros.
Induction n.
Step_lft (One::RX)!x.
Step_lft (One::R).
Algebra.
Step_lft (p[*](p[^]n))!x.
Step_lft p!x [*] (p[^]n)!x.
Step_lft  p!x [*] (p!x)[^]n.
Algebra.
Qed.

(* Begin_Tex_Verb *)
(* SUPERFLUOUS *)
Lemma poly_inv_apply :
  (p:RX)(x:R)((cpoly_inv ? p)!x [=] [--](p!x)).
(* End_Tex_Verb *)
Exact inv_apply.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_cpoly_ap : (f:nat->RX)(a:R)(k:nat)
  ((Sum0 k f)!a [=] (Sum0 k [i:nat](f i)!a)).
(* End_Tex_Verb *)
Intros.
Induction k.
Simpl.
Algebra.
Step_lft ((Sum0 k f) [+] (f k))!a.
Step_lft (Sum0 k f)!a [+] (f k)!a.
Step_lft (Sum0 k [i:nat](f i)!a) [+] (f k)!a.
Simpl.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_cpoly_ap : (f:nat->RX)(a:R)(k,l:nat)
  ((Sum k l f)!a [=] (Sum k l [i:nat](f i)!a)).
(* End_Tex_Verb *)
Unfold Sum.
Unfold Sum1.
Intros.
Unfold cg_minus.
Step_lft  ((Sum0 (S l) f)!a) [+] ([--](Sum0 k f))!a.
Step_lft  ((Sum0 (S l) f)!a) [+] [--]((Sum0 k f)!a).
Apply bin_op_wd_unfolded.
Apply Sum0_cpoly_ap.
Apply un_op_wd_unfolded.
Apply Sum0_cpoly_ap.
Qed.

End Poly_properties.

(* Tex_Prose
\section{Induction properties of polynomials for {\tt Prop}}
*)
Section Poly_Prop_Induction.

Variable CR:CRing.

Syntactic Definition Cpoly := (cpoly CR).

Syntactic Definition Cpoly_zero := (cpoly_zero CR).

Syntactic Definition Cpoly_linear := (cpoly_linear CR).

Syntactic Definition Cpoly_cring := (cpoly_cring CR).

(* Begin_Tex_Verb *)
Lemma cpoly_double_ind : (P:Cpoly_cring->Cpoly_cring->Prop)
   ((p:Cpoly_cring)(P p Zero)) ->
   ((p:Cpoly_cring)(P Zero p)) ->
   ((p,q:Cpoly_cring)(c,d:CR)(P p q)->(P (c [+X*] p) (d [+X*] q))) ->
   (p,q:Cpoly_cring)(P p q).
(* End_Tex_Verb *)
Exact (cpoly_double_ind0_cs CR).
Qed.

End Poly_Prop_Induction.

Hints Resolve poly_linear cpoly_lin : algebra.
Hints Resolve apply_wd cpoly_const_eq : algebra_c.
Hints Resolve _c_apply _x_apply inv_apply plus_apply minus_apply mult_apply nexp_apply : algebra.
Hints Resolve one_apply _c_zero _c_one _c_mult : algebra.
Hints Resolve poly_inv_apply : algebra.
Hints Resolve _c_mult_lin : algebra.
