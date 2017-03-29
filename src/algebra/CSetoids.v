(* $Id.v,v 1.18 2002/11/25 14:43:42 lcf Exp $ *)

(* Begin_SpecReals *)

(* Tex_Prose
\chapter{Setoids}
Definition of a constructive setoid with apartness,
i.e. a set with an equivalence relation and an apartness relation compatible with it.
*)

Require Export Relations.
Require Export CLogic.

Definition Relation:=Relation_Definitions.relation.

(* End_SpecReals *)

Implicits reflexive   [1].
Implicits Creflexive  [1].

(* Begin_SpecReals *)

Implicits symmetric   [1].
Implicits Csymmetric  [1].
Implicits transitive  [1].
Implicits Ctransitive [1].

Implicit Arguments On.

(* Tex_Prose
\section{Relations necessary for Setoids}
\begin{convention}
Let \verb!A : Set!.
\end{convention}

Notice that their type depends on the main logical connective.
*)
Section Properties_of_relations.
Variable A: Set.

(* Begin_Tex_Verb *)
Definition irreflexive [R:(Crelation A)] : Prop :=
        (x:A)(Not (R x x)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition cotransitive [R:(Crelation A)] : CProp :=
        (x,y:A)(R x y) -> (z:A)(R x z) + (R z y).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition tight_apart [eq:(Relation A); ap:(Crelation A)] : Prop :=
    (x,y:A)(Not (ap x y))<->(eq x y).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition antisymmetric [R:(Crelation A)] : Prop :=
        (x,y: A)(R x y) -> (Not (R y x)).
(* End_Tex_Verb *)

End Properties_of_relations.
Implicit Arguments Off.

(* Tex_Prose
\section{Definition of Setoid}

Apartness, being the main relation, needs to be \verb!Set!-valued.  Equality,
as it is characterized by a negative statement, lives in \verb!Prop!.
*)
(* Begin_Tex_Verb *)
Record is_CSetoid [A:Set; eq:(Relation A); ap:(Crelation A)] : CProp :=
  { ax_ap_irreflexive  : (irreflexive ap);
    ax_ap_symmetric    : (Csymmetric ap);
    ax_ap_cotransitive : (cotransitive ap);
    ax_ap_tight        : (tight_apart eq ap)
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record CSetoid : Type :=
  { cs_crr   :> Set;
    cs_eq    :  (Relation cs_crr);
    cs_ap    :  (Crelation cs_crr);
    cs_proof :  (is_CSetoid cs_crr cs_eq cs_ap)
  }.
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\begin{itemize}
\item \hypertarget{Operator_2}{}\verb!(cs_ap ? x y)! is denoted by \verb!x [#] y!.
\item \hypertarget{Operator_1}{}\verb!(cs_eq ? x y)! is denoted by \verb!x [=] y!.
\end{itemize}
\end{notation}
*)

Implicits cs_eq [1].

Infix NONA 8 "[=]" cs_eq.
Syntax constr level 8:
  cs_eq_infix [ (cs_eq $_ $e1 $e2) ] ->
    [[<hov 1> $e1:L [0 1] " [=] " $e2:L]].

Implicits cs_ap [1].

Infix NONA 8 "[#]" cs_ap.
Syntax constr level 8:
  cs_ap_infix [(cs_ap $_ $e1 $e2)] ->
    [[<hov 1> $e1:L [0 1] " [#] " $e2:L]].
(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition cs_neq [S: CSetoid] : (Relation S)
                               := [x,y:S]~(x [=] y).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\hypertarget{Operator_3}{}\verb!(cs_neq ? x y)! is denoted by \verb!x [~=] y!.
\end{notation}
*)

Implicits cs_neq [1].

Infix NONA 8 "[~=]" cs_neq.
Syntax constr level 8:
  s_neq_infix [(cs_neq $_ $e1 $e2)] ->
    [[<hov 1> $e1:L [0 1] " [~=] " $e2:L]].

(* Tex_Prose
\begin{nameconvention}
In the names of lemmas, we refer to \verb! [=]! by \verb!eq!, \verb![~=]! by
\verb!neq!, and \verb![#]! by \verb!ap!.
\end{nameconvention}
*)

(* Tex_Prose
\section{Setoid axioms}
We want concrete lemmas that state the axiomatic properties of a setoid.
\begin{convention}
Let \verb!S! be a setoid.
\end{convention}
*)

(* Begin_SpecReals *)

Section CSetoid_axioms.
Variable S : CSetoid.

(* Begin_Tex_Verb *)
Lemma CSetoid_is_CSetoid : (is_CSetoid S (!cs_eq S) (!cs_ap S)).
(* End_Tex_Verb *)
Proof (cs_proof S).

(* Begin_Tex_Verb *)
Lemma ap_irreflexive : (irreflexive (!cs_ap S)).
(* End_Tex_Verb *)
Elim CSetoid_is_CSetoid; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_symmetric : (Csymmetric (!cs_ap S)).
(* End_Tex_Verb *)
Elim CSetoid_is_CSetoid; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_cotransitive : (cotransitive (!cs_ap S)).
(* End_Tex_Verb *)
Elim CSetoid_is_CSetoid; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_tight : (tight_apart (!cs_eq S) (!cs_ap S)).
(* End_Tex_Verb *)
Elim CSetoid_is_CSetoid; Auto.
Qed.

End CSetoid_axioms.

(* End_SpecReals *)

(* Tex_Prose
\section{Setoid basics}\label{section:setoid-basics}
\begin{convention}
Let \verb!S! be a setoid.
\end{convention}
*)

(* Begin_SpecReals *)

Section CSetoid_basics.
Variable S : CSetoid.

(* End_SpecReals *)

(* Tex_Prose
In `there exists a {\em unique\/}
$a:S$ such that \ldots ', we now mean unique with respect to the
setoid equality. We use \verb!ex_unq! to denote unique existence
*)

(* Begin_Tex_Verb *)
Definition ex_unq := [P:S->CProp]
	{x:S | (y:S)(P y)-> (x [=] y) & (P x)}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma eq_reflexive: (reflexive (!cs_eq S)).
(* End_Tex_Verb *)
Intro x.
Generalize (ap_tight S x x); Intro H.
Generalize (ap_irreflexive S x); Intro H0.
Inversion_clear H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma eq_symmetric: (symmetric (!cs_eq S)).
(* End_Tex_Verb *)
Intro x; Intros y H.
Generalize (ap_tight S x y); Intro H0.
Generalize (ap_tight S y x); Intro H1.
Generalize (ap_symmetric S y x); Intro H2.
Elim H0; Clear H0; Intros H3 H4.
Elim H1; Clear H1; Intros H0 H5.
Apply H0; Intro H6.
Apply H4; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma eq_transitive: (transitive (!cs_eq S)).
(* End_Tex_Verb *)
Intro x; Intros y z H H0.
Generalize (ap_tight S x y); Intro H1.
Generalize (ap_tight S y z); Intro H2.
Generalize (ap_tight S x z); Intro H3.
Elim H3; Intros H4 H5.
Apply H4.
Intro H6.
Generalize (ap_cotransitive ? ? ? H6 y); Intro H7.
Elim H1; Clear H1; Intros H1' H1''.
Elim H2; Clear H2; Intros H2' H2''.
Elim H3; Clear H3; Intros H3' H3''.
Elim H7; Clear H7; Intro H1.
Generalize H1; Apply H1''; Auto.
Generalize H1; Apply H2''; Auto.
Qed.

(* Tex_Prose
\begin{shortcoming}
The lemma \verb!eq_reflexive! above is convertible to
\verb!eq_reflexive_unfolded! below. We need the second version too,
because the first cannot be applied when an instance of reflexivity is needed.
(``I have complained bitterly about this.'' RP)
\end{shortcoming}

\begin{nameconvention}
If lemma $a$ is just an unfolding of lemma $b$, the name of $a$ is the name
$b$ with the suffix ``\verb!_unfolded!''.
\end{nameconvention}
*)

(* Begin_Tex_Verb *)
Lemma eq_reflexive_unfolded : (x:S)(x [=] x).
(* End_Tex_Verb *)
Proof eq_reflexive.

(* Begin_Tex_Verb *)
Lemma eq_symmetric_unfolded : (x,y:S)(x [=] y)->(y [=] x).
(* End_Tex_Verb *)
Proof eq_symmetric.

(* Begin_Tex_Verb *)
Lemma eq_transitive_unfolded : (x,y,z:S)(x [=] y)->(y [=] z)->(x [=] z).
(* End_Tex_Verb *)
Proof eq_transitive.

(* Begin_SpecReals *)

(* Begin_Tex_Verb *)
Lemma ap_irreflexive_unfolded : (x:S)(Not (x[#]x)).
(* End_Tex_Verb *)
Proof (ap_irreflexive S).

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma ap_cotransitive_unfolded
     : (a,b:S)(a [#] b)->
              (c:S)(a [#] c)+(c [#] b).
(* End_Tex_Verb *)
Intros a b H c.
Exact (ap_cotransitive ? ? ? H c).
Qed.

(* Begin_Tex_Verb *)
Lemma ap_symmetric_unfolded : (x,y:S)((x[#]y) -> (y[#]x)).
(* End_Tex_Verb *)
Proof (ap_symmetric S).

(* Tex_Prose
\begin{shortcoming}
We would like to write
\[\verb!Lemma eq_equiv_not_ap : (x,y:S)(x [=] y) <-> ~(x [#] y).!\]
In Coq, however, this lemma cannot be easily applied.
Therefore we have to split the lemma into the following two lemmas
\verb!eq_imp_not_ap! and \verb!not_ap_imp_eq!.
\end{shortcoming}
*)

(* Begin_Tex_Verb *)
Lemma eq_imp_not_ap : (x,y:S)(x [=] y) -> (Not (x [#] y)).
(* End_Tex_Verb *)
Intros x y.
Elim (ap_tight S x y).
Intros H1 H2.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma not_ap_imp_eq : (x,y:S)(Not (x [#] y)) -> (x [=] y).
(* End_Tex_Verb *)
Intros x y.
Elim (ap_tight S x y).
Intros H1 H2.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma neq_imp_notnot_ap : (x,y:S)(x [~=] y) -> 
                                 ~(Not (x [#] y)).
(* End_Tex_Verb *)
Intros x y H.
Intro H0.
Unfold cs_neq in H.
Apply H.
Apply not_ap_imp_eq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma notnot_ap_imp_neq :  (x,y:S)~(Not (x [#] y)) -> 
                                  (x [~=] y).
(* End_Tex_Verb *)
Intros x y H.
Intro H0.
Apply H.
Apply eq_imp_not_ap.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_imp_neq: (x,y:S)(x [#] y)->(x [~=] y).
(* End_Tex_Verb *)
Intros x y H; Intro H1.
Apply (eq_imp_not_ap ?? H1).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma not_neq_imp_eq : (x,y:S)~(x[~=]y) -> (x [=] y).
(* End_Tex_Verb *)
Intros x y H.
Apply not_ap_imp_eq.
Intro H0.
Elim H.
Apply ap_imp_neq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma eq_imp_not_neq : (x,y:S)(x [=] y) -> ~(x[~=]y).
(* End_Tex_Verb *)
Intros x y H.
Intro H0.
Auto.
Qed.

(* Begin_SpecReals *)

End CSetoid_basics.

(* End_SpecReals *)

Implicits ex_unq [1].

Hints Resolve eq_reflexive_unfolded : algebra_r.
Hints Resolve eq_symmetric_unfolded : algebra_s.


(* Begin_SpecReals *)

(* Tex_Prose
\section{Relations and predicates}
Here we define the notions of well-definedness and strong extensionality
on predicates and relations.

\begin{convention}
Let \verb!S! be a setoid.
\end{convention}

\begin{nameconvention}
\begin{itemize}
\item ``well-defined'' is abbreviated to \verb!well_def! (or \verb!wd!?).
\item ``strongly extensional'' is abbreviated to \verb!strong_ext!
(or \verb!strext!?).
\end{itemize}
\end{nameconvention}
*)
Section CSetoid_relations_and_predicates.
Variable S : CSetoid.

(* End_SpecReals *)

(* Tex_Prose
\subsection{Predicates}

At this stage, we should really consider \verb!CProp!- and \verb!Prop!-valued predicates
on setoids; however, for our applications, we will only need to consider the first type,
so that is all we introduce.

\begin{convention}
Let \verb!P! be a predicate on (the carrier of) \verb!S!.
\end{convention}

*)
Section CSetoidPredicates.
Variable P: S -> CProp.

(* Begin_Tex_Verb *)
Definition pred_strong_ext: CProp := (x,y: S)(P x) -> (P y) + (x [#] y).
Definition pred_well_def: CProp :=   (x,y: S)(P x) -> (x [=] y) -> (P y).
(* End_Tex_Verb *)

End CSetoidPredicates.

(* Tex_Prose
\subsection{Definition of a setoid predicate}
*)
(* Begin_Tex_Verb *)
Record CSetoid_predicate : Type :=
  { csp_pred   :> S -> CProp;
    csp_strext :  (pred_strong_ext csp_pred)
  }.

Lemma csp_wd : (P:CSetoid_predicate)(pred_well_def P).
(* End_Tex_Verb *)
Intro P.
Intro x; Intros y H H0.
Elim (csp_strext P x y H).

Auto.

Intro H1.
ElimType False.
Generalize H1.
Exact (eq_imp_not_ap ??? H0).
Qed.


(* Begin_SpecReals *)

(* Tex_Prose
\subsection{Relation}
\begin{convention}
Let \verb!R! be a relation on (the carrier of) \verb!S!.
\end{convention}
*)
Section CsetoidRelations.
Variable R: S -> S -> Prop.

(* Begin_Tex_Verb *)
Definition rel_well_def_rht: Prop :=
  (x,y,z: S)(R x y) -> (y [=] z) -> (R x z).
Definition rel_well_def_lft: Prop :=
  (x,y,z: S)(R x y) -> (x [=] z) -> (R z y).
Definition rel_strong_ext : CProp :=
  (x1,x2,y1,y2 : S)(R x1 y1) -> 
                 ((x1 [#] x2)+(y1 [#] y2))+{R x2 y2}.
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition rel_strong_ext_lft : CProp :=
  (x1,x2,y : S)(R x1 y) -> (x1 [#] x2)+{R x2 y}.
Definition rel_strong_ext_rht : CProp :=
  (x,y1,y2 : S)(R x y1) -> (y1 [#] y2)+{R x y2}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma rel_strext_imp_lftarg: rel_strong_ext -> rel_strong_ext_lft.
(* End_Tex_Verb *)
Proof.
Unfold rel_strong_ext rel_strong_ext_lft; Intros H x1 x2 y H0.
Generalize (H x1 x2 y y).
Intros H1.
Elim (H1 H0).

Intro H3.
Elim H3.

Auto.

Intro H4.
Elim (ap_irreflexive S ? H4).

Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma rel_strext_imp_rhtarg: rel_strong_ext -> rel_strong_ext_rht.
(* End_Tex_Verb *)
Unfold rel_strong_ext rel_strong_ext_rht; Intros H x y1 y2 H0.
Generalize (H x x y1 y2 H0); Intro H1.
Elim H1; Intro H2.

Elim H2; Intro H3.
Elim (ap_irreflexive ? ? H3).

Auto.

Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma rel_strextarg_imp_strext:
   rel_strong_ext_rht -> rel_strong_ext_lft -> rel_strong_ext.
(* End_Tex_Verb *)
Unfold rel_strong_ext rel_strong_ext_lft rel_strong_ext_rht; Intros H H0 x1 x2 y1 y2 H1.
Elim (H x1 y1 y2 H1); Intro H2.

Auto.

Elim (H0 x1 x2 y2 H2); Auto.
Qed.

(* Begin_SpecReals *)

End CsetoidRelations.

(* Tex_Prose
\subsection{Definition of a setoid relation}
*)

(* Tex_Prose
The type of relations over a setoid.
*)
(* Begin_Tex_Verb *)
Record CSetoid_relation : Type :=
  { csr_rel    :> S -> S -> Prop;
    csr_wdr    : (rel_well_def_rht csr_rel);
    csr_wdl    : (rel_well_def_lft csr_rel);
    csr_strext : (rel_strong_ext csr_rel)
  }.
(* End_Tex_Verb *)

(* Tex_Prose
\subsection{CProp Relation}
\begin{convention}
Let \verb!R! be a relation on (the carrier of) \verb!S!.
\end{convention}
*)
Section CCsetoidRelations.

Variable R: S -> S -> CProp.

(* Begin_Tex_Verb *)
Definition Crel_well_def_rht: CProp :=
  (x,y,z: S)(R x y) -> (y [=] z) -> (R x z).
Definition Crel_well_def_lft: CProp :=
  (x,y,z: S)(R x y) -> (x [=] z) -> (R z y).
Definition Crel_strong_ext : CProp :=
  (x1,x2,y1,y2 : S)(R x1 y1) -> 
                (R x2 y2) + ((x1 [#] x2) + (y1 [#] y2)).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition Crel_strong_ext_lft : CProp :=
  (x1,x2,y : S)(R x1 y) -> (R x2 y) + (x1 [#] x2).
Definition Crel_strong_ext_rht : CProp :=
  (x,y1,y2 : S)(R x y1) -> (R x y2) + (y1 [#] y2).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Crel_strext_imp_lftarg: 
                        Crel_strong_ext -> Crel_strong_ext_lft.
(* End_Tex_Verb *)
Proof.
Unfold Crel_strong_ext Crel_strong_ext_lft; Intros H x1 x2 y H0.
Generalize (H x1 x2 y y).
Intro H1.
Elim (H1 H0).

Auto.

Intro H3.
Elim H3; Intro H4.

Auto.
Elim (ap_irreflexive ?? H4).
Qed.

(* Begin_Tex_Verb *)
Lemma Crel_strext_imp_rhtarg:
                          Crel_strong_ext -> Crel_strong_ext_rht.
(* End_Tex_Verb *)
Unfold Crel_strong_ext Crel_strong_ext_rht; Intros H x y1 y2 H0.
Generalize (H x x y1 y2 H0); Intro H1.
Elim H1; Intro H2.

Auto.

Elim H2; Intro H3.

Elim (ap_irreflexive ? ? H3).

Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Crel_strextarg_imp_strext:
   Crel_strong_ext_rht -> Crel_strong_ext_lft -> 
   Crel_strong_ext.
(* End_Tex_Verb *)
Unfold Crel_strong_ext Crel_strong_ext_lft Crel_strong_ext_rht; Intros H H0 x1 x2 y1 y2 H1.
Elim (H x1 y1 y2 H1); Auto.
Intro H2.
Elim (H0 x1 x2 y2 H2); Auto.
Qed.

(* Begin_SpecReals *)

End CCsetoidRelations.

(* Tex_Prose
\subsection{Definition of a CProp setoid relation}
*)

(* Tex_Prose
The type of relations over a setoid.
*)
(* Begin_Tex_Verb *)
Record CCSetoid_relation : Type :=
  { Ccsr_rel    :> S -> S -> CProp;
    Ccsr_strext : (Crel_strong_ext Ccsr_rel)
  }.

Lemma Ccsr_wdr : (R:(CCSetoid_relation))(Crel_well_def_rht R).
(* End_Tex_Verb *)
Intro R.
Red; Intros x y z H H0.
Elim (Ccsr_strext R x x y z H).

Auto.

Intro H1; ElimType False.
Elim H1; Intro H2.

Exact (ap_irreflexive_unfolded ?? H2).

Generalize H2.
Exact (eq_imp_not_ap ??? H0).
Qed.

(* Begin_Tex_Verb *)
Lemma Ccsr_wdl : (R:(CCSetoid_relation))(Crel_well_def_lft R).
(* End_Tex_Verb *)
Intro R.
Red; Intros x y z H H0.
Elim (Ccsr_strext R x z y y H).

Auto.

Intro H1; ElimType False.
Elim H1; Intro H2.

Generalize H2.
Exact (eq_imp_not_ap ??? H0).

Exact (ap_irreflexive_unfolded ?? H2).
Qed.

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma ap_well_def_rht: (Crel_well_def_rht (!cs_ap S)).
(* End_Tex_Verb *)
Red; Intros x y z H H0.
Generalize (eq_imp_not_ap ? ? ? H0); Intro H1.
Elim (ap_cotransitive_unfolded ? ? ? H z); Intro H2.

Assumption.

Elim H1.
Apply ap_symmetric_unfolded.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_well_def_lft: (Crel_well_def_lft (!cs_ap S)).
(* End_Tex_Verb *)
Red; Intros x y z H H0.
Generalize (ap_well_def_rht y x z); Intro H1.
Apply ap_symmetric_unfolded.
Apply H1.

Apply ap_symmetric_unfolded.
Assumption.

Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_well_def_rht_unfolded:
   (x,y,z:S)(x [#] y) -> (y [=] z) -> (x [#] z).
(* End_Tex_Verb *)
Proof ap_well_def_rht.

(* Begin_Tex_Verb *)
Lemma ap_well_def_lft_unfolded:
   (x,y,z:S)(x [#] y) -> (x [=] z) -> (z [#] y).
(* End_Tex_Verb *)
Proof ap_well_def_lft.

(* Begin_Tex_Verb *)
Lemma ap_strong_ext: (Crel_strong_ext (!cs_ap S)).
(* End_Tex_Verb *)
Red; Intros x1 x2 y1 y2 H.
Case (ap_cotransitive_unfolded ? ? ? H x2); Intro H0.

Auto.

Case (ap_cotransitive_unfolded ? ? ? H0 y2); Intro H1.

Auto.

Right; Right.
Apply ap_symmetric_unfolded.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition predS_well_def [P:S->CProp]: CProp := (x,y:S)(P x) -> (x [=] y) -> (P y).
(* End_Tex_Verb *)

(* Begin_SpecReals *)

End CSetoid_relations_and_predicates.

(* End_SpecReals *)

(* Tex_Prose
\section{Functions between setoids}
Such functions must preserve the setoid equality
and be strongly extensional w.r.t. the apartness, i.e. e.g.
if \verb!f(x,y) apart f(x1,y1)!, then  \verb!x apart x1 \/ y apart y1!.
For every arity this has to be defined separately.
\begin{convention}
Let \verb!S1!, \verb!S2! and \verb!S3! be setoids.
\end{convention}

First we consider unary functions.
*)

(* Begin_SpecReals *)

Section CSetoid_functions.
Variables S1, S2, S3 : CSetoid.


Section unary_functions.

(* Tex_Prose
In the following two definitions,
\verb!f! is a function from (the carrier of) \verb!S1! to
(the carrier of) \verb!S2!.
*)
Variable  f : S1 -> S2.

(* Begin_Tex_Verb *)
Definition fun_well_def : Prop := (x, y: S1)(x [=] y) -> ((f x) [=] (f y)).
Definition fun_strong_ext : CProp := (x, y: S1)((f x) [#] (f y)) -> (x [#] y).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma fun_strong_ext_imp_well_def : fun_strong_ext -> fun_well_def.
(* End_Tex_Verb *)
Unfold fun_strong_ext.
Unfold fun_well_def.
Intros H x y H0.
Apply not_ap_imp_eq.
Intro H1.
Generalize (H ? ? H1); Intro H2.
Generalize (eq_imp_not_ap ? ? ? H0); Intro H3.
Elim H3; Assumption.
Qed.

(* Begin_SpecReals *)

End unary_functions.

(* Begin_Tex_Verb *)
Record CSetoid_fun : Set :=
  { csf_fun    :> S1 -> S2;
    csf_strext :  (fun_strong_ext csf_fun)
  }.

Lemma csf_wd : (f:CSetoid_fun)(fun_well_def f).
(* End_Tex_Verb *)
Intro f.
Apply fun_strong_ext_imp_well_def.
Apply csf_strext.
Qed.

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition Const_CSetoid_fun : S2 -> CSetoid_fun.
(* End_Tex_Verb *)
Intro c; Apply (Build_CSetoid_fun [x:S1]c); Red; Intros x y H.
(* str ext *)
Elim (ap_irreflexive ? ? H).
Defined.

(* Begin_SpecReals *)

Section binary_functions.

(* Tex_Prose
Now we consider binary functions.
In the following two definitions,
\verb!f! is a function from \verb!S1! and \verb!S2! to \verb!S3!.
*)
Variable f : S1 -> S2 -> S3.

(* Begin_Tex_Verb *)
Definition bin_fun_well_def : Prop :=
  (x1, x2: S1)(y1, y2: S2)
   (x1 [=] x2) -> (y1 [=] y2) -> ((f x1 y1) [=] (f x2 y2)).

Definition bin_fun_strong_ext : CProp :=
  (x1, x2: S1)(y1, y2: S2)
   ((f x1 y1) [#] (f x2 y2)) -> (x1 [#] x2) + (y1 [#] y2).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma bin_fun_strong_ext_imp_well_def : bin_fun_strong_ext -> bin_fun_well_def.
(* End_Tex_Verb *)
Unfold bin_fun_strong_ext.
Unfold bin_fun_well_def.
Intros H x1 x2 y1 y2 H0 H1.
Apply not_ap_imp_eq.
Intro H2.
Generalize (H ? ? ? ? H2); Intro H3.
Elim H3; Intro H4.

Generalize (eq_imp_not_ap ? ? ? H0); Intro H5.
Elim H5; Assumption.

Generalize (eq_imp_not_ap ? ? ? H1); Intro H5.
Elim H5; Assumption.
Qed.

(* Begin_SpecReals *)

End binary_functions.

(* Begin_Tex_Verb *)
Record CSetoid_bin_fun : Set :=
  { csbf_fun    :> S1 -> S2 -> S3;
    csbf_strext :  (bin_fun_strong_ext csbf_fun)
  }.

Lemma csbf_wd : (f:CSetoid_bin_fun)(bin_fun_well_def f).
(* End_Tex_Verb *)
Intro f.
Apply bin_fun_strong_ext_imp_well_def.
Apply csbf_strext.
Qed.

(* Begin_Tex_Verb *)
Lemma csetoid_fun_wd_unfolded : 
  (f:CSetoid_fun)(x,x':S1)(x[=]x')->((f x)[=](f x')).
(* End_Tex_Verb *)
Intros f x x' H.
Apply (csf_wd f x x').
Assumption.
Qed.

Lemma csetoid_fun_strext_unfolded : (f:CSetoid_fun)(x,y:S1)((f x)[#](f y))->(x[#]y).
Intros f x y H.
Apply (csf_strext f x y).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma csetoid_bin_fun_wd_unfolded :
  (f:CSetoid_bin_fun)(x,x':S1;y,y':S2)(x[=]x')->(y[=]y')->(f x y)[=](f x' y').
(* End_Tex_Verb *)
Intros f x x' y y' H H0.
Apply (csbf_wd f x x' y y'); Assumption.
Qed.

End CSetoid_functions.

(* End_SpecReals *)

Hints Resolve csetoid_fun_wd_unfolded csetoid_bin_fun_wd_unfolded : algebra_c.

Implicits fun_well_def [1 2].
Implicits fun_strong_ext [1 2].

Section unary_function_composition.

(* Tex_Prose
Let \verb!S1!,  \verb!S2! and \verb!S3! be setoids, \verb!f! a
setoid function from \verb!S1! to \verb!S2!, and \verb!g! from \verb!S2!
to \verb!S3! in the following definition of composition.
*)
Variables S1, S2, S3 : CSetoid.
Variable  f : (CSetoid_fun S1 S2).
Variable  g : (CSetoid_fun S2 S3).

(* Begin_Tex_Verb *)
Definition compose_CSetoid_fun: (CSetoid_fun S1 S3).
(* End_Tex_Verb *)
Apply (Build_CSetoid_fun ? ? [x:S1](g (f x))).
(* str_ext *)
Unfold fun_strong_ext; Intros x y H.
Apply (csf_strext ? ? f). Apply (csf_strext ? ? g). Assumption.
Defined.

End unary_function_composition.


(* Begin_SpecReals *)

(* Tex_Prose
\section{The unary and binary (inner) operations on a csetoid.}
An operation is a function with domain(s) and co-domain equal.

\begin{nameconvention}
The word ``unary operation'' is abbreviated to \verb!un_op!;
``binary operation'' is abbreviated to \verb!bin_op!.
\end{nameconvention}

\begin{convention}
Let \verb!S! be a setoid.
\end{convention}
 *)
Section csetoid_inner_ops.
Variable S : CSetoid.

(* Tex_Prose
Properties of binary operations
*)
(* Begin_Tex_Verb *)
Definition commutes [f:S->S->S] : Prop := (x,y: S)(f x y) [=] (f y x).
Definition associative [f:S->S->S]: Prop :=
    (x,y,z:S)(f x (f y z)) [=] (f (f x y) z).
(* End_Tex_Verb *)

(* Tex_Prose
Well-defined unary operations on a setoid.
*)
(* Begin_Tex_Verb *)
Definition un_op_well_def := (!fun_well_def S S).
Definition un_op_strong_ext := (!fun_strong_ext S S).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition CSetoid_un_op : Set := (CSetoid_fun S S).
Definition Build_CSetoid_un_op := (Build_CSetoid_fun S S).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma id_strext : (un_op_strong_ext [x:S]x).
(* End_Tex_Verb *)
Unfold un_op_strong_ext.
Unfold fun_strong_ext.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma id_pres_eq : (un_op_well_def [x:S]x).
(* End_Tex_Verb *)
Unfold un_op_well_def.
Unfold fun_well_def.
Auto.
Qed.

(* Begin_Tex_Verb *)
Definition id_un_op := (Build_CSetoid_un_op [x:S]x id_strext).
(* End_Tex_Verb *)
Identity Coercion un_op_fun: CSetoid_un_op >-> CSetoid_fun.

(* Begin_SpecReals *)

(* Begin_Tex_Verb *)
Definition un_op_strext := (csf_strext S S).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma un_op_wd_unfolded:
  (op:CSetoid_un_op)(x,y:S)(x [=] y) -> (op x) [=] (op y).
(* End_Tex_Verb *)
Proof (csf_wd S S).

(* Begin_Tex_Verb *)
Lemma un_op_strext_unfolded:
  (op:CSetoid_un_op)(x,y:S)((op x) [#] (op y)) -> x [#] y.
(* End_Tex_Verb *)
Exact un_op_strext.
Qed.

(* Tex_Prose
Well-defined binary operations on a setoid.
*)
(* Begin_Tex_Verb *)
Definition bin_op_well_def := (bin_fun_well_def S S S).
Definition bin_op_strong_ext := (bin_fun_strong_ext S S S).
(* End_Tex_Verb *)

(* Begin_SpecReals *)

(* Begin_Tex_Verb *)
Definition CSetoid_bin_op : Set := (CSetoid_bin_fun S S S).
Definition Build_CSetoid_bin_op := (Build_CSetoid_bin_fun S S S).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition bin_op_wd := (csbf_wd S S S).
Definition bin_op_strext := (csbf_strext S S S).
(* End_Tex_Verb *)

(* Begin_SpecReals *)

Identity Coercion bin_op_bin_fun: CSetoid_bin_op >-> CSetoid_bin_fun.

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma bin_op_wd_unfolded:
    (op:CSetoid_bin_op)(x1, x2, y1, y2: S)
      (x1 [=] x2) -> (y1 [=] y2) -> (op x1 y1) [=] (op x2 y2).
(* End_Tex_Verb *)
Exact bin_op_wd.
Qed.

(* Begin_Tex_Verb *)
Lemma bin_op_strext_unfolded:
    (op:CSetoid_bin_op)(x1, x2, y1, y2: S)
      ((op x1 y1) [#] (op x2 y2)) -> (x1 [#] x2) + (y1 [#] y2).
(* End_Tex_Verb *)
Exact bin_op_strext.
Qed.

(* Begin_Tex_Verb *)
Lemma bin_op_is_wd_un_op_lft:
    (op:CSetoid_bin_op)(c: S)(un_op_well_def [x:S](op x c)).
(* End_Tex_Verb *)
Proof.
Intros op c. Unfold un_op_well_def. Unfold fun_well_def.
Intros x y H. Apply bin_op_wd_unfolded. Trivial. Apply eq_reflexive_unfolded.
Qed.

(* Begin_Tex_Verb *)
Lemma bin_op_is_wd_un_op_rht:
    (op:CSetoid_bin_op)(c: S)(un_op_well_def [x:S](op c x)).
(* End_Tex_Verb *)
Proof.
Intros op c. Unfold un_op_well_def. Unfold fun_well_def.
Intros x y H. Apply bin_op_wd_unfolded. Apply eq_reflexive_unfolded. Trivial.
Qed.

(* Begin_Tex_Verb *)
Lemma bin_op_is_strext_un_op_lft:
    (op:CSetoid_bin_op)(c: S)(un_op_strong_ext [x:S](op x c)).
(* End_Tex_Verb *)
Proof.
Intros op c. Unfold un_op_strong_ext. Unfold fun_strong_ext.
Intros x y H. Cut (x[#]y)+(c[#]c). Intro Hv. Elim Hv. Trivial. Intro Hf. 
Generalize (ap_irreflexive_unfolded ? c Hf). Intro. Elim H0.
Apply bin_op_strext_unfolded with op. Trivial.
Qed.

(* Begin_Tex_Verb *)
Lemma bin_op_is_strext_un_op_rht:
    (op:CSetoid_bin_op)(c: S)(un_op_strong_ext [x:S](op c x)).
(* End_Tex_Verb *)
Proof.
Intros op c. Unfold un_op_strong_ext. Unfold fun_strong_ext.
Intros x y H. Cut (c[#]c)+(x[#]y). Intro Hv. Elim Hv. Intro Hf.
Generalize (ap_irreflexive_unfolded ? c Hf). Tauto. Auto.
Apply bin_op_strext_unfolded with op. Trivial.
Qed.

(* Begin_Tex_Verb *)
Definition bin_op2un_op_rht : CSetoid_bin_op->(S)->CSetoid_un_op :=
[op:CSetoid_bin_op; c:(S)]
 (Build_CSetoid_un_op [x:(S)](op c x)
  (bin_op_is_strext_un_op_rht op c)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition bin_op2un_op_lft : CSetoid_bin_op->(S)->CSetoid_un_op :=
[op:CSetoid_bin_op; c:(S)]
 (Build_CSetoid_un_op [x:(S)](op x c)
   (bin_op_is_strext_un_op_lft op c)).
(* End_Tex_Verb *)

(* Begin_SpecReals *)

End csetoid_inner_ops.

(* End_SpecReals *)

Implicits commutes [1].

(* Begin_SpecReals *)

Implicits associative [1].

(* End_SpecReals *)

Hints Resolve bin_op_wd_unfolded un_op_wd_unfolded : algebra_c.

(* Tex_Prose
\section{The binary outer operations on a csetoid.}
\begin{convention}
Let \verb!S1! and \verb!S2! be setoids.
\end{convention}
 *)

Section csetoid_outer_ops.
Variable S1, S2 : CSetoid.

(* Tex_Prose
Well-defined outer operations on a setoid.
*)
(* Begin_Tex_Verb *)
Definition outer_op_well_def := (bin_fun_well_def S1 S2 S2).
Definition outer_op_strong_ext := (bin_fun_strong_ext S1 S2 S2).

Definition CSetoid_outer_op : Set := (CSetoid_bin_fun S1 S2 S2).
Definition Build_CSetoid_outer_op := (Build_CSetoid_bin_fun S1 S2 S2).
Definition csoo_wd := (csbf_wd S1 S2 S2).
Definition csoo_strext := (csbf_strext S1 S2 S2).
(* End_Tex_Verb *)
Identity Coercion outer_op_bin_fun: CSetoid_outer_op >-> CSetoid_bin_fun.

(* Begin_Tex_Verb *)
Lemma csoo_wd_unfolded:
    (op:CSetoid_outer_op)(x1, x2: S1)(y1, y2: S2)
      (x1 [=] x2) -> (y1 [=] y2) -> (op x1 y1) [=] (op x2 y2).
(* End_Tex_Verb *)
Exact csoo_wd.
Qed.

End csetoid_outer_ops.
Hints Resolve csoo_wd_unfolded : algebra_c.


(* Tex_Prose
\section{Combining operations}
\begin{convention}
Let \verb!S1!, \verb!S2! and \verb!S3! be setoids.
\end{convention}
*)
Section CombiningOperations.
Variables S1, S2, S3 : CSetoid.

(* Tex_Prose
In the following definition, we assume \verb!f! is a setoid function from
\verb!S1! to \verb!S2!, and \verb!op! is an unary operation on \verb!S2!.
*)
Section CombiningUnaryOperations.
Variable f : (CSetoid_fun S1 S2).
Variable op : (CSetoid_un_op S2).

(* Tex_Prose
\verb!opOnFun! is the composition \verb!op! after \verb!f!.
*)
(* Begin_Tex_Verb *)
Definition opOnFun: (CSetoid_fun S1 S2).
(* End_Tex_Verb *)
Apply (Build_CSetoid_fun S1 S2 [x:S1](op (f x))).
(* str_ext *)
Unfold fun_strong_ext; Intros.
Apply (csf_strext ? ? f x y).
Apply (csf_strext ? ? op ? ? H).
Defined.

End CombiningUnaryOperations.

End CombiningOperations.

(* Tex_Prose
\section{Partial Functions}

In this section we define a concept of partial function for an arbitrary setoid.  Essentially, a partial function is what would be expected---a predicate on the setoid in question and a total function from the set of points satisfying that predicate to the setoid.  There is one important limitations to this approach: first, the record we obtain has type \verb!Type!, meaning that we can't use, for instance, elimination of existential quantifiers.

Furthermore, for reasons we will explain ahead, partial functions will not be defined via the \verb!CSetoid_fun! record, but the whole structure will be incorporated in a new record.

Finally, notice that to be completely general the domains of the functions have to be characterized by a \verb!CProp!-valued predicate; otherwise, the use you can make of a function will be {\em a priori} restricted at the moment it is defined.

Before we state our definitions we need to do some work on domains.
*)

Section SubSets_of_G.

(* Tex_Prose
\subsection*{Subsets of Setoids}

Subsets of a setoid will be identified with predicates from the carrier set of the setoid into \verb!CProp!.  At this stage, we do not make any assumptions about these predicates.

We will begin by defining elementary operations on predicates, along with their basic properties.  In particular, we will work with well defined predicates, so we will prove that these operations preserve welldefinedness.

\begin{convention} Let \verb!S:CSetoid! and \verb!P,Q:S->CProp!.
\end{convention}
*)

Variable S:CSetoid.

Section Conjunction.

Variables P,Q:S->CProp.

(* Begin_Tex_Verb *)
Definition conjP [x:S] : CProp := (P x)*(Q x).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma prj1 : (x:S)(conjP x)->(P x).
(* End_Tex_Verb *)
Intros; Inversion_clear H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma prj2 : (x:S)(conjP x)->(Q x).
(* End_Tex_Verb *)
Intros; Inversion_clear H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma conj_wd : (pred_well_def ? P)->(pred_well_def ? Q)->
  (pred_well_def ? conjP).
(* End_Tex_Verb *)
Intros H H0.
Red; Intros x y H1 H2.
Inversion_clear H1; Split.

Apply H with x; Assumption.

Apply H0 with x; Assumption.
Qed.

End Conjunction.

Section Disjunction.

Variables P,Q:S->CProp.

(* Tex_Prose
Although at this stage we never use it, for completeness' sake we also treat disjunction (corresponding to union of subsets).
*)

(* Begin_Tex_Verb *)
Definition disj [x:S] : CProp := (P x)+(Q x).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma inj1 : (x:S)(P x)->(disj x).
(* End_Tex_Verb *)
Intros; Left; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma inj2 : (x:S)(Q x)->(disj x).
(* End_Tex_Verb *)
Intros; Right; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma disj_wd : (pred_well_def ? P)->(pred_well_def ? Q)->
  (pred_well_def ? disj).
(* End_Tex_Verb *)
Intros H H0.
Red; Intros x y H1 H2.
Inversion_clear H1.

Left; Apply H with x; Assumption.

Right; Apply H0 with x; Assumption.
Qed.

End Disjunction.

Section Extension.

(* Tex_Prose
The next definition is a bit tricky, and is useful for choosing among the elements that satisfy a predicate $P$ those that also satisfy $R$ in the case where $R$ is only defined for elements satisfying $P$---consider $R$ to be a condition on the image of an object via a function with domain $P$.  We chose to call this operation \emph{extension}.
*)

Variable P : S->CProp.
Variable R : (x:S)(P x)->CProp.

(* Begin_Tex_Verb *)
Definition extend : S->CProp := [x:S](P x)*(H:(P x))(R x H).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma ext1 : (x:S)(extend x)->(P x).
(* End_Tex_Verb *)
Intros x H; Inversion_clear H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma ext2_a : (x:S)(extend x)->{H:(P x) & (R x H)}.
(* End_Tex_Verb *)
Intros x H; Inversion_clear H.
Exists H0; Apply H1.
Qed.

(* Begin_Tex_Verb *)
Lemma ext2 : (x:S)(Hx:(extend x))(R x (ProjS1 (ext2_a x Hx))).
(* End_Tex_Verb *)
Intros; Apply projS2.
Qed.

(* Begin_Tex_Verb *)
Lemma extension_wd : (pred_well_def ? P)->
  ((x,y:S)(Hx,Hy:?)(x[=]y)->(R x Hx)->(R y Hy))->
  (pred_well_def ? extend).
(* End_Tex_Verb *)
Intros H H0.
Red; Intros x y H1 H2.
Elim H1; Intros H3 H4; Split.

Apply H with x; Assumption.

Intro H5; Apply H0 with x H3; [Apply H2 | Apply H4].
Qed.

End Extension.

End SubSets_of_G.

Notation Conj := (conjP ?).
Implicits disj [1].

Implicits extend [1].
Implicits ext1 [1 2 3 4].
Implicits ext2 [1 2 3 4].

(* Tex_Prose
\subsection*{Operations}

We are now ready to define the concept of partial function between arbitrary setoids.
*)

(* Begin_Tex_Verb *)
Record BinPartFunct [S1,S2:CSetoid] : Type :=
  {bpfpred :  S1->CProp;
   bpfprwd :  (pred_well_def S1 bpfpred);
   bpfpfun :> (x:S1)(bpfpred x)->S2;
   bpfstrx :  (x,y:S1)(Hx:(bpfpred x))(Hy:(bpfpred y))
                (((bpfpfun x Hx)[#](bpfpfun y Hy))->(x[#]y))}.
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\begin{itemize}
\item The predicate of a partial function \verb!F! will be denoted simply by {\tt\hypertarget{Syntactic_2a}{(BPred F)}}.
\end{itemize}
\end{notation}
*)

Notation BPred := (bpfpred ??).
Implicits bpfpfun [1 2].

(* Tex_Prose
The next lemma states that every partial function is well defined.
*)

(* Begin_Tex_Verb *)
Lemma bpfwdef : (S1,S2:CSetoid)(F:(BinPartFunct S1 S2))
  ((x,y:S1)(Hx:(BPred F x))(Hy:(BPred F y))
    (x[=]y)->(F x Hx)[=](F y Hy)).
(* End_Tex_Verb *)
Intros.
Apply not_ap_imp_eq; Intro.
Generalize (bpfstrx ??????? H0).
Exact (eq_imp_not_ap ??? H).
Qed.

(* Similar for automorphisms. *)

(* Begin_Tex_Verb *)
Record PartFunct [S:CSetoid] : Type :=
  {pfpred :  S->CProp;
   pfprwd :  (pred_well_def S pfpred);
   pfpfun :> (x:S)(pfpred x)->S;
   pfstrx :  (x,y:S)(Hx:(pfpred x))(Hy:(pfpred y))
               (((pfpfun x Hx)[#](pfpfun y Hy))->(x[#]y))}.
(* End_Tex_Verb *)

Notation Pred := (pfpred ?).
Syntactic Definition Part := (pfpfun ?).
Implicits pfpfun [1].

(* Tex_Prose
\begin{notation}
\begin{itemize}
\item The predicate of a partial function \verb!F! will be denoted simply by {\tt\hypertarget{Syntactic_2}{(Pred F)}}.
\end{itemize}
\end{notation}
*)

(* Tex_Prose
The next lemma states that every partial function is well defined.
*)

(* Begin_Tex_Verb *)
Lemma pfwdef : (S:CSetoid)(F:(PartFunct S))
  ((x,y:S)(Hx:(Pred F x))(Hy:(Pred F y))
    (x[=]y)->(F x Hx)[=](F y Hy)).
(* End_Tex_Verb *)
Intros.
Apply not_ap_imp_eq; Intro.
Generalize (pfstrx ?????? H0).
Exact (eq_imp_not_ap ??? H).
Qed.

(* Tex_Prose
A few characteristics of this definition should be explained:
\begin{itemize}
\item The domain of the partial function is characterized by a predicate that is required to be well defined but not strongly extensional.  The motivation for this choice comes from two facts: first, one very important subset of real numbers is the compact interval $[a,b]$---characterized by the predicate \verb![x:IR](a[<=]x)*(x[<=]b)!, which is not strongly extensional; on the other hand, if we can apply a function to an element $s$ of a setoid $S$ it seems reasonable (and at some point we do have to do it) to apply that same function to any element $s'$ which is equal to $s$ from the point of view of the setoid equality.
\item The last two conditions state that \verb!partG! is really a subsetoid function.  The reason why we do not write it that way is the following: when applying a partial function $f$ to an element $s$ of $S$ we also need a proof object $H$; with this definition the object we get is $f(s,H)$, \emph{where the proof is kept separate from the object}.  Using subsetoid notation, we would get $f(\langle s,H\rangle)$; from this we need to apply two projections to get either the original object or the proof, and we need to apply an extra constructor to get $f(\langle s,H\rangle)$ from $s$ and $H$.  This amounts to spending more resources when actually working with these objects.
\item This record has type \verb!Type!, which is very unfortunate, because it means in particular that we cannot use the well behaved set existential quantification over partial functions; however, later on we will manage to avoid this problem in a way that also justifies that we don't really need to use that kind of quantification.

Another approach to this definition that completely avoid this complication would be to make \verb!PartFunct! a dependent type, receiving the predicate as an argument.  This does work in that it allows us to give \verb!PartFunct! type \verb!Set! and do some useful stuff with it; however, we are not able to define something as simple as an operator that gets a function and returns its domain (because of the restrictions in the type elimination rules).  This sounds very unnatural, and soon gets us into strange problems that yield very unlikely definitions, which is why we chose to altogether do away with this approach.
\end{itemize}

\begin{convention} All partial functions will henceforth be denoted by capital letters.
\end{convention}

We now present some methods for defining partial functions.
*)

Hints Resolve CI : core.

Section CSetoid_Ops.

Variable S:CSetoid.

(* Tex_Prose
To begin with, we want to be able to ``see'' each total function as a partial function.
*)

(* Begin_Tex_Verb *)
Definition total_eq_part : (CSetoid_un_op S)->(PartFunct S).
(* End_Tex_Verb *)
Intros f.
Apply Build_PartFunct with [x:S]CTrue [x:S][H:CTrue](f x); Intros.
Red; Intros; Auto.
Exact (csetoid_fun_strext_unfolded ?? f ?? H).
Defined.

Section Part_Function_Const.

(* Tex_Prose
In any setoid we can also define constant functions (one for each element of the setoid) and an identity function:

\begin{convention} Let \verb!c:S!.
\end{convention}
*)

Variable c:S.

(* Begin_Tex_Verb *)
Definition Fconst := (total_eq_part (Const_CSetoid_fun ?? c)).
(* End_Tex_Verb *)

End Part_Function_Const.

Section Part_Function_Id.

(* Begin_Tex_Verb *)
Definition Fid := (total_eq_part (id_un_op S)).
(* End_Tex_Verb *)

End Part_Function_Id.

(* Tex_Prose
(These happen to be always total functions, but that is more or less obvious, as we have no information on the setoid; however, we will be able to define partial functions just applying other operators to these ones.)

If we have two setoid functions $F$ and $G$ we can always compose them.  The domain of our new function will be the set of points $s$ in the domain of $F$ for which $F(s)$ is in the domain of $G$\footnote{Notice that the use of extension here is essential.}.  The inversion in the order of the variables is done to maintain uniformity with the usual mathematical notation.

\begin{convention} Let \verb!G,F:(PartFunct S)! and denote by \verb!Q! and \verb!P!, respectively, the predicates characterizing their domains.
\end{convention}
*)

Section Part_Function_Composition.

Variables G,F : (PartFunct S).

Local P := (Pred F).
Local Q := (Pred G).

(* Begin_Tex_Verb *)
Local R:=[x:S]{Hx:(P x) & (Q (F x Hx))}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma part_function_comp_strext : (x,y:S)(Hx:(R x))(Hy:(R y))
  (((G (F x (ProjS1 Hx)) (ProjS2 Hx))[#]
    (G (F  y (ProjS1 Hy)) (ProjS2 Hy)))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Exact (pfstrx ?????? (pfstrx ?????? H)).
Qed.

(* Begin_Tex_Verb *)
Lemma part_function_comp_pred_wd : (pred_well_def S R).
(* End_Tex_Verb *)
Red; Intros.
Unfold R; Inversion_clear H.
Exists (pfprwd ? F x y x0 H0).
Apply (pfprwd ? G) with (F x x0).
Assumption.
Apply pfwdef; Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Fcomp := (Build_PartFunct ? R
  part_function_comp_pred_wd
  [x:S][Hx:(R x)](G (F x (ProjS1 Hx)) (ProjS2 Hx))
  part_function_comp_strext).
(* End_Tex_Verb *)

End Part_Function_Composition.

End CSetoid_Ops.

(* Tex_Prose
\begin{convention} Let \verb!F:(BinPartFunct S1 S2)! and \verb!G:(PartFunct S2 S3)!, and denote by \verb!Q! and \verb!P!, respectively, the predicates characterizing their domains.
\end{convention}
*)

Section BinPart_Function_Composition.

Variables S1,S2,S3:CSetoid.

Variable G : (BinPartFunct S2 S3).
Variable F : (BinPartFunct S1 S2).

Local P := (BPred F).
Local Q := (BPred G).

(* Begin_Tex_Verb *)
Local R:=[x:S1]{Hx:(P x) & (Q (F x Hx))}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma bin_part_function_comp_strext : (x,y:S1)(Hx:(R x))(Hy:(R y))
  (((G (F x (ProjS1 Hx)) (ProjS2 Hx))[#]
    (G (F y (ProjS1 Hy)) (ProjS2 Hy)))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Exact (bpfstrx ??????? (bpfstrx ??????? H)).
Qed.

(* Begin_Tex_Verb *)
Lemma bin_part_function_comp_pred_wd : (pred_well_def S1 R).
(* End_Tex_Verb *)
Red; Intros.
Unfold R; Inversion_clear H.
Exists (bpfprwd ?? F x y x0 H0).
Apply (bpfprwd ?? G) with (F x x0).
Assumption.
Apply bpfwdef; Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition BinFcomp := (Build_BinPartFunct ?? R
  bin_part_function_comp_pred_wd
  [x:S1][Hx:(R x)](G (F x (ProjS1 Hx)) (ProjS2 Hx))
  bin_part_function_comp_strext).
(* End_Tex_Verb *)

End BinPart_Function_Composition.

Implicits Fconst [1].
Distfix RIGHTA 1 "{-C-} _" Fconst.

Notation FId    := (Fid ?).

Implicits Fcomp [1].
Infix NONA 7 "{o}" Fcomp.

(* Tex_Prose
\begin{notation}
\begin{itemize}
\item Constant funtions with value \verb!c! will be denoted by {\tt\hypertarget{Operator_5}{\{-C-\}}c}.
\item The composition of \verb!F! and \verb!G! will be denoted by {\tt G \hypertarget{Operator_6}{\{o\}} F}.
\item When the underlying setoid is clear from the context, the identity function on it can be written down simply as {\tt\hypertarget{Syntactic_3}{FId}}.
\end{itemize}
\end{notation}
*)

(* Begin_SpecReals *)

(* Tex_Prose
\section{Subsetoids}
\begin{convention}
Let \verb!S! be a setoid, and \verb!P! a predicate on the carrier of \verb!S!.
\end{convention}
*)

Section SubCSetoids.
Variable S : CSetoid.
Variable P : S -> CProp.

(* Begin_Tex_Verb *)
Record subcsetoid_crr : Set :=
  { scs_elem :> S;
    scs_prf : (P scs_elem)
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition restrict_relation [R:(Relation S)] : 
                             (Relation subcsetoid_crr) :=
  [a, b: subcsetoid_crr]
  Cases a b of
   (Build_subcsetoid_crr x _) (Build_subcsetoid_crr y _) => (R x y)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Crestrict_relation [R:(Crelation S)] :
                                   (Crelation subcsetoid_crr) :=
  [a, b: subcsetoid_crr]
  Cases a b of
   (Build_subcsetoid_crr x _) (Build_subcsetoid_crr y _) => (R x y)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition subcsetoid_eq: (Relation subcsetoid_crr) :=
  (restrict_relation (!cs_eq S)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition subcsetoid_ap: (Crelation subcsetoid_crr) :=
  (Crestrict_relation (!cs_ap S)).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Remark subcsetoid_equiv : (equiv ? subcsetoid_eq).
(* End_Tex_Verb *)
Unfold subcsetoid_eq; Split.
(* reflexive *)
Red; Intros a; Case a.
Intros x s; Red.
Apply (eq_reflexive S).
(* transitive *)
Split.
Red; Intros a b c; Case a.
Intros x s; Case b.
Intros y t; Case c.
Intros z u; Simpl.
Exact (eq_transitive ? x y z).
(* symmetric *)
Red.
Intros a b; Case a.
Intros x s; Case b.
Intros y t; Simpl.
Exact (eq_symmetric ? x y).
Qed.

(* Begin_SpecReals *)

(* Begin_Tex_Verb *)
Lemma subcsetoid_is_CSetoid : (is_CSetoid ? subcsetoid_eq subcsetoid_ap).
(* End_Tex_Verb *)
Apply (Build_is_CSetoid ? subcsetoid_eq subcsetoid_ap).
(* irreflexive *)
Red; Intros. Case x. Unfold Not; Intros.
Exact (ap_irreflexive_unfolded S ? H).
(* symmetric *)
Red; Intros x y. Case x. Case y. Intros.
Exact (ap_symmetric S ? ? H).
(* cotransitive *)
Red; Intros x y. Case x. Case y. Intros; Case z. Intros.
Exact (ap_cotransitive S ? ? H scs_elem2).
(* tight *)
Red; Intros. Case x. Case y. Intros.
Exact (ap_tight S scs_elem1 scs_elem0).
Qed.

(* Begin_Tex_Verb *)
Definition Build_SubCSetoid : CSetoid :=
  (Build_CSetoid subcsetoid_crr subcsetoid_eq subcsetoid_ap
            subcsetoid_is_CSetoid).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Tex_Prose
\subsection{Subsetoid unary operations}
\begin{convention}
Let \verb!f! be a unary setoid operation on \verb!S!.
\end{convention}
*)

Section SubCSetoid_unary_operations.
Variable f : (CSetoid_un_op S).
(* Begin_Tex_Verb *)
Definition un_op_pres_pred : CProp := (x:S)(P x) -> (P (f x)).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{convention}
Assume \verb!pr : un_op_pres_pred!.
\end{convention}
*)
Variable pr : un_op_pres_pred.

(* Begin_Tex_Verb *)
Definition restr_un_op : subcsetoid_crr -> subcsetoid_crr :=
  [a: subcsetoid_crr]
  Cases a of (Build_subcsetoid_crr x p) =>
              (Build_subcsetoid_crr (f x) (pr x p))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma restr_un_op_well_def: (un_op_well_def Build_SubCSetoid restr_un_op).
(* End_Tex_Verb *)
Red. Red. Intros x y. Case y. Case x. Intros.
  Exact (un_op_wd_unfolded ? f ? ? H).
Qed.

(* Begin_Tex_Verb *)
Lemma restr_un_op_strong_ext: (un_op_strong_ext Build_SubCSetoid restr_un_op).
(* End_Tex_Verb *)
Red. Red. Intros x y. Case y. Case x. Intros.
  Exact (un_op_strext ? f ? ? H).
Qed.

(* Begin_Tex_Verb *)
Definition Build_SubCSetoid_un_op: (CSetoid_un_op Build_SubCSetoid) :=
  (Build_CSetoid_un_op Build_SubCSetoid restr_un_op restr_un_op_strong_ext).
(* End_Tex_Verb *)

End SubCSetoid_unary_operations.


(* Tex_Prose
\subsection{Subsetoid binary operations}
\begin{convention}
Let \verb!f! be a binary setoid operation on \verb!S!.
\end{convention}
*)

Section SubCSetoid_binary_operations.

Variable f : (CSetoid_bin_op S).

(* Begin_Tex_Verb *)
Definition bin_op_pres_pred : CProp := (x,y:S)(P x) -> (P y) -> (P (f x y)).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{convention}
Assume \verb!un_op_pres_pred!.
\end{convention}
*)

Variable pr : bin_op_pres_pred.

(* Begin_Tex_Verb *)
Definition restr_bin_op [a,b:subcsetoid_crr]: subcsetoid_crr :=
  Cases a b of (Build_subcsetoid_crr x p) (Build_subcsetoid_crr y q) =>
                   (Build_subcsetoid_crr (f x y) (pr x y p q))
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma restr_bin_op_well_def: (bin_op_well_def Build_SubCSetoid restr_bin_op).
(* End_Tex_Verb *)
Red. Red. Intros x1 x2 y1 y2. Case y2. Case y1. Case x2. Case x1. Intros.
  Exact (bin_op_wd ? f ? ? ? ? H H0).
Qed.

(* Begin_Tex_Verb *)
Lemma restr_bin_op_strong_ext:
                         (bin_op_strong_ext Build_SubCSetoid restr_bin_op).
(* End_Tex_Verb *)
Red. Red. Intros x1 x2 y1 y2. Case y2. Case y1. Case x2. Case x1. Intros.
  Exact (bin_op_strext ? f ? ? ? ? H).
Qed.

(* Begin_Tex_Verb *)
Definition Build_SubCSetoid_bin_op : (CSetoid_bin_op Build_SubCSetoid) :=
  (Build_CSetoid_bin_op Build_SubCSetoid restr_bin_op restr_bin_op_strong_ext).
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Lemma restr_f_assoc: (associative f) ->
                     (associative (Build_SubCSetoid_bin_op)).
(* End_Tex_Verb *)
Intro. Red. Intros x y z. Case z. Case y. Case x. Intros.
Simpl.
Apply H.
Qed.


End SubCSetoid_binary_operations.


(* Begin_SpecReals *)

End SubCSetoids.

(* End_SpecReals *)

(* Tex_Prose
\subsection{Miscellaneous}
*)


(* Begin_Tex_Verb *)
Lemma proper_caseZ_diff_CS : (S:CSetoid)(f:nat->nat->S)
              ((m,n,p,q:nat)(plus m q) = (plus n p) -> (f m n) [=] (f p q)) ->
              (m,n:nat)(caseZ_diff `m-n` f) [=] (f m n).
(* End_Tex_Verb *)
Intro CS.
Intros.
Pattern m n.
Apply nat_double_ind.
Intro.
Replace `O-n0` with `-n0`.
Rewrite caseZ_diff_Neg.
Apply eq_reflexive_unfolded.
Simpl.
Reflexivity.
Intros.
Replace `(S n0)-O` with (`(S n0)` :: Z).
Rewrite caseZ_diff_Pos.
Apply eq_reflexive_unfolded.
Simpl.
Reflexivity.
Intros.
Generalize (H (S n0) (S m0) n0 m0); Intro.
Cut (plus (S n0) m0)=(plus (S m0) n0).
Intro.
Generalize (H1 H2); Intro.
Apply eq_transitive_unfolded with (f n0 m0).
Apply eq_transitive_unfolded with (caseZ_diff `n0-m0` f).
Replace `(S n0)-(S m0)` with `n0-m0`.
Apply eq_reflexive_unfolded.
Repeat Rewrite inj_S.
Clear H1; Auto with zarith.
Assumption.
Apply eq_symmetric_unfolded.
Assumption.
Clear H1; Auto with zarith.
Qed.

(* Tex_Prose
Finally, we characterize functions defined on the natural numbers also as setoid functions, similarly to what we already did for predicates.
*)

(* Begin_Tex_Verb *)
Definition nat_less_n_fun [S:CSetoid][n:nat]
  [f:(i:nat)(lt i n)->S] := (i,j:nat)(i=j)->
  (H:(lt i n))(H':(lt j n))(f i H)[=](f j H').
Definition nat_less_n_fun' [S:CSetoid][n:nat]
  [f:(i:nat)(le i n)->S] := (i,j:nat)(i=j)->
  (H:(le i n))(H':(le j n))(f i H)[=](f j H').
(* End_Tex_Verb *)
