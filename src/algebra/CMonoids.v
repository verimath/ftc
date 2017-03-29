(* $Id: CMonoids.v,v 1.8 2003/03/11 13:35:51 lcf Exp $ *)

Require Export CSemiGroups.

(* Begin_SpecReals *)

(* Tex_Prose
\chapter{Monoids}\label{section:monoids}
We deal only with commutative algebraic structures.
*)

(* Tex_Prose
\section{Definition of monoids}
*)

(* Begin_Tex_Verb *)
Definition is_rht_unit
 [S: CSetoid; op: (CSetoid_bin_op S); one: S] : Prop :=
    (x: S)((op x one) [=] x).
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition is_lft_unit
 [S: CSetoid; op: (CSetoid_bin_op S); one: S] : Prop :=
    (x: S)((op one x) [=] x).
(* End_Tex_Verb *)

Implicits is_lft_unit [1].

(* Begin_SpecReals *)

Implicits is_rht_unit [1].

(* Begin_Tex_Verb *)
Record is_CMonoid [M: CSemi_grp]: CProp :=
  { runit : (is_rht_unit (!csg_op M) Zero);
    commut: (commutes (!csg_op M))
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record CMonoid : Type :=
  { cm_crr   :> CSemi_grp;
    cm_proof :  (is_CMonoid cm_crr)
  }.
(* End_Tex_Verb *)
(* End_SpecReals *)

(* Tex_Prose
\section{Monoid axioms}
\begin{convention}
Let \verb!M! be a monoid.
\end{convention}
*)
Section CMonoid_axioms.
Variable M : CMonoid.

(* Begin_Tex_Verb *)
Lemma CMonoid_is_CMonoid : (is_CMonoid M).
(* End_Tex_Verb *)
Elim M; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cm_rht_unit: (is_rht_unit csg_op Zero::M).
(* End_Tex_Verb *)
Elim CMonoid_is_CMonoid; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma cm_commutes: (commutes (!csg_op M)).
(* End_Tex_Verb *)
Elim CMonoid_is_CMonoid; Auto.
Qed.

End CMonoid_axioms.

(* Tex_Prose
\section{Monoid basics}
\begin{convention}
Let \verb!M! be a monoid.
\end{convention}
*)
Section CMonoid_basics.
Variable M : CMonoid.

(* Begin_Tex_Verb *)
Lemma cm_commutes_unfolded: (x, y: M)((x [+] y) [=] (y [+] x)).
(* End_Tex_Verb *)
Proof (cm_commutes M).
Hints Resolve cm_commutes_unfolded : algebra.

(* Begin_Tex_Verb *)
Lemma cm_rht_unit_unfolded : (x:M)((x [+] Zero) [=] x).
(* End_Tex_Verb *)
Intro.
Apply (cm_rht_unit M).
Qed.

(* Begin_Tex_Verb *)
Lemma lftUnit_iff_rhtUnit:
  (x:M)(is_lft_unit csg_op x)<->(is_rht_unit csg_op x).
(* End_Tex_Verb *)
Proof.
Intro x; Split; Red; Intros H x0.
Step_final (x [+] x0).
Step_final (x0 [+] x).
Qed.

(* Begin_Tex_Verb *)
Lemma cm_lft_unit: (is_lft_unit csg_op Zero::M).
(* End_Tex_Verb *)
Generalize (lftUnit_iff_rhtUnit Zero); Intro H.
Elim H; Intros H0 H1.
Apply H1.
Apply cm_rht_unit.
Qed.

(* Begin_Tex_Verb *)
Lemma cm_lft_unit_unfolded: (x:M)((Zero [+] x) [=] x).
(* End_Tex_Verb *)
  Proof cm_lft_unit.

Hints Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded : algebra.

(* Begin_Tex_Verb *)
Lemma cm_unit_unique_lft:
    (x:M)(is_lft_unit csg_op x)->(x [=] Zero).
(* End_Tex_Verb *)
Intros x h. Red in h.
Step_final (x [+] Zero).
Qed.

(* Begin_Tex_Verb *)
Lemma cm_unit_unique_rht:
    (x:M)(is_rht_unit csg_op x)->(x [=] Zero).
(* End_Tex_Verb *)
Intros x h. Red in h.
Step_final (Zero [+] x).
Qed.

(* Begin_SpecReals *)

(* Tex_Prose
The proof component of the monoid is irrelevant.
*)
(* Begin_Tex_Verb *)
Lemma is_CMonoid_proof_irr :
  (S:CSetoid)(one:S)(mult:(CSetoid_bin_op S))(p,q:(associative mult))
                 (is_CMonoid (Build_CSemi_grp S one mult p)) ->
                 (is_CMonoid (Build_CSemi_grp S one mult q)).
(* End_Tex_Verb *)
Intros S one mult p q H.
Elim H; Intros runit0 commut0.
Simpl in runit0.
Simpl in commut0.
Apply Build_is_CMonoid; Simpl; Assumption.
Qed.

(* End_SpecReals *)

(* Tex_Prose
\section{Submonoids}
\begin{convention}
Let \verb!P! a predicate on \verb!M! with
\verb!P Zero! and which is preserved by \verb![+]!.
\end{convention}
*)

Section SubCMonoids.
Variable P         : M -> CProp.
Variable Punit     : (P Zero).
Variable op_pres_P : (bin_op_pres_pred ? P csg_op).

(* Begin_Tex_Verb *)
Local subcrr : CSemi_grp := (Build_SubCSemi_grp ? ? Punit op_pres_P).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma ismon_scrr: (is_CMonoid subcrr).
(* End_Tex_Verb *)
Split; Red.

(* unit *)
Intro x. Case x. Intros scs_elem scs_prf.
Apply (cm_rht_unit_unfolded scs_elem).

(* commutes *)
Intros x y. Case y. Case x. Intros scs_elem scs_prf scs_elem0 scs_prf0.
Exact (cm_commutes_unfolded scs_elem scs_elem0).
Qed.

(* Begin_Tex_Verb *)
Definition Build_SubCMonoid : CMonoid := (Build_CMonoid subcrr ismon_scrr).
(* End_Tex_Verb *)

End SubCMonoids.


End CMonoid_basics.

Hints Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded : algebra.
Hints Resolve cm_commutes_unfolded : algebra.
