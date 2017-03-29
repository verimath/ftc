(* $Id: CGroups.v,v 1.16 2003/03/13 12:06:13 lcf Exp $ *)

Require Export CMonoids.

(* Begin_SpecReals *)

(* Tex_Prose
\chapter{Groups}
*)

(* Tex_Prose
\section{Definition of the notion of Group}
*)
(* Begin_Tex_Verb *)
Definition is_inverse
 [S:CSetoid; op:(CSetoid_bin_op S); one:S; x:S; x_inv:S] : Prop :=
  ((op x x_inv) [=] one).
(* End_Tex_Verb *)

Implicits is_inverse [1].

(* Begin_Tex_Verb *)
Definition is_CGroup [G: CMonoid; inv: (CSetoid_un_op G)] :=
     (x: G)(is_inverse csg_op Zero x (inv x)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record CGroup : Type :=
  { cg_crr   :> CMonoid;
    cg_inv   :  (CSetoid_un_op cg_crr);
    cg_proof :  (is_CGroup cg_crr cg_inv)
  }.
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_SpecReals *)

(* Tex_Prose
\begin{notation}
\hypertarget{Operator_9}{}\verb!(cg_inv ? a)! is denoted by \verb![--]a!.
\end{notation}
*)

Implicits cg_inv [1].
Distfix RIGHTA 1 "[--] _" cg_inv.

(* Begin_Tex_Verb *)
Definition cg_minus := [G: CGroup][x, y: G](x [+] [--]y).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\hypertarget{Operator_10}{}\verb!(cg_minus ? a b)! is denoted by \verb!a[-]b!.
\end{notation}

\begin{nameconvention}
In the {\em names} of lemmas, we will denote \verb![--]! with \verb!min!,
and \verb![-]! with \verb!minus!.
\end{nameconvention}
*)

Implicits cg_minus [1].
Infix NONA 7 "[-]" cg_minus.

(* End_SpecReals *)

(* Tex_Prose
\section{Group axioms}
\begin{convention}
Let \verb!G! be a group.
\end{convention}
*)
Section CGroup_axioms.
Variable G : CGroup.

(* Begin_Tex_Verb *)
Lemma cg_rht_inv: (x: G)(is_inverse csg_op Zero x [--]x).
(* End_Tex_Verb *)
Proof (cg_proof G).

End CGroup_axioms.

(* Tex_Prose
\section{Group basics}
General properties of groups.
\begin{convention}
Let \verb!G! be a group.
\end{convention}
*)
Section CGroup_basics.
Variable G : CGroup.

(* Begin_Tex_Verb *)
Lemma cg_rht_inv_unfolded: (x:G)((x [+] [--]x) [=] Zero).
(* End_Tex_Verb *)
Exact (cg_rht_inv G).
Qed.

(* Begin_Tex_Verb *)
Lemma cg_minus_correct: (x: G)(x [-] x) [=] Zero.
(* End_Tex_Verb *)
Intro x.
Unfold cg_minus.
Apply cg_rht_inv_unfolded.
Qed.
Hints Resolve cg_rht_inv_unfolded cg_minus_correct : algebra.

(* Begin_Tex_Verb *)
Lemma cg_lft_inv: (x: G)(is_inverse csg_op Zero ([--]x) x).
(* End_Tex_Verb *)
Intro x.
Red.
Step_final (x [+] [--]x).
Qed.

(* Begin_Tex_Verb *)
Lemma cg_lft_inv_unfolded: (x:G) ([--]x [+] x) [=] Zero.
(* End_Tex_Verb *)
Proof cg_lft_inv.
Hints Resolve cg_lft_inv_unfolded : algebra.

(* Hints for Auto *)
(* Begin_Tex_Verb *)
Lemma cg_minus_unfolded: (x,y:G) (x [-] y) [=] (x [+] [--]y).
(* End_Tex_Verb *)
Algebra.
Qed.
Hints Resolve cg_minus_unfolded : algebra.

(* Begin_Tex_Verb *)
Lemma cg_minus_wd: (x,x',y,y':G)
  (x [=] x')->(y [=] y')->(x[-]y [=] x'[-]y').
(* End_Tex_Verb *)
Intros x x' y y' H H0.
Unfold cg_minus.
Step_final x[+][--]y'.
Qed.
Hints Resolve cg_minus_wd : algebra_c.

(* Begin_Tex_Verb *)
Lemma cg_minus_strext: (x,x',y,y':G)
  (x[-]y [#] x'[-]y') -> (x [#] x')+(y [#] y').
(* End_Tex_Verb *)
Intros x x' y y' H. Cut (x [#] x')+([--]y [#] [--]y').
Intro H0. Elim H0.
 Left; Trivial.
Intro H1.
Right; Exact (un_op_strext G cg_inv y y' H1).

Apply bin_op_strext_unfolded with (!csg_op G). Trivial.
Qed.

(* Begin_Tex_Verb *)
Definition cg_minus_is_csetoid_bin_op : (CSetoid_bin_op G):=
  (Build_CSetoid_bin_op G (!cg_minus G) cg_minus_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma grp_inv_assoc: (x,y:G) (x[+]y)[-]y [=] x.
(* End_Tex_Verb *)
Intros x y; Unfold cg_minus.
Step x [+] (y [+] ([--]y)).
Step_final x [+] Zero.
Qed.
Hints Resolve grp_inv_assoc : algebra.

(* Begin_Tex_Verb *)
Lemma cg_inv_unique: (x,y:G) ((x [+] y) [=] Zero) -> y [=] [--]x.
(* End_Tex_Verb *)
Proof.
Intros x y H.
Step (Zero [+] y).
Step (([--]x [+] x) [+] y).
Step ([--]x [+] (x [+] y)).
Step_final ([--]x [+] Zero).
Qed.

(* Begin_Tex_Verb *)
Lemma cg_inv_inv: (x:G) [--][--]x [=] x.
(* End_Tex_Verb *)
Proof.
Intro x.
Step (Zero [+] [--][--]x).
Step (x[+][--]x)[+][--][--]x.
Step (x [+] ([--]x [+] [--][--]x)).
Step_final (x [+] Zero).
Qed.
Hints Resolve cg_inv_inv : algebra.

(* Begin_Tex_Verb *)
Lemma cg_cancel_lft: (x, y, z:G)((x [+] y) [=] (x [+] z)) -> y [=] z.
(* End_Tex_Verb *)
Proof.
Intros x y z H.
Step (Zero [+] y).
Step (([--]x [+] x) [+] y).
Step ([--]x [+] (x [+] y)).
Step ([--]x [+] (x [+] z)).
Step (([--]x [+] x) [+] z).
Step_final (Zero [+] z).
Qed.

(* Begin_Tex_Verb *)
Lemma cg_cancel_rht: (x, y, z: G)((y [+] x) [=] (z [+] x)) -> y [=] z.
(* End_Tex_Verb *)
Proof.
Intros x y z H.
Apply (cg_cancel_lft x y z).
Step (y [+] x).
Step_final (z [+] x).
Qed.

(* Begin_Tex_Verb *)
Lemma cg_inv_unique': (x,y:G) ((x [+] y) [=] Zero) -> x [=] [--]y.
(* End_Tex_Verb *)
Proof.
Intros x y H.
Step (x [+] Zero).
Step (x [+] (y [+] [--]y)).
Step ((x [+] y) [+] [--]y).
Step_final (Zero [+] [--]y).
Qed.

(* Begin_Tex_Verb *)
Lemma cg_inv_unique_2 : (x,y:G)(x[-]y [=] Zero)->(x [=] y).
(* End_Tex_Verb *)
Intros x y H.
Generalize (cg_inv_unique ? ? H); Intro H0.
Step [--][--]x.
Step_final [--][--]y.
Qed.

(* Begin_Tex_Verb *)
Lemma cg_zero_inv: [--](Zero::G) [=] Zero.
(* End_Tex_Verb *)
Apply eq_symmetric_unfolded; Apply cg_inv_unique; Algebra.
Qed.

Hints Resolve cg_zero_inv : algebra.

(* Begin_Tex_Verb *)
Lemma cg_inv_zero : (x:G)x[-]Zero [=] x.
(* End_Tex_Verb *)
Intro x.
Unfold cg_minus.
Step_final x[+]Zero.
Qed.

(* Begin_Tex_Verb *)
Lemma cg_inv_op: (x,y:G) [--](x[+]y) [=] [--]y [+] [--]x.
(* End_Tex_Verb *)
Intros x y.
Apply (eq_symmetric G).
Apply cg_inv_unique.
Step ((x [+] y) [+] [--]y) [+] [--]x.
Step (x [+] (y [+] [--]y)) [+] [--]x.
Step (x [+] Zero) [+] [--]x.
Step_final (x [+] [--]x).
Qed.

(* Begin_Tex_Verb *)
Lemma csg_op_inv: (x,y:G) [--](x[+]y) [=] [--]x [+] [--]y.
(* End_Tex_Verb *)
Intros x y.
Stepr [--]y [+] [--]x.
Apply cg_inv_op.
Qed.

(* Tex_Prose
Useful for interactive proof development.
*)

(* Begin_Tex_Verb *)
Lemma x_minus_x : (x,y:G)(x[=]y)->(x[-]y[=]Zero).
(* End_Tex_Verb *)
Intros x y H; Step_final x[-]x.
Qed.

(* Tex_Prose
\section{Sub-groups}
\begin{convention}
Let \verb!P! a predicate on \verb!G! with
\verb!(P Zero)! and which is preserved by \verb![+]! and \verb![--]!.
\end{convention}
*)
Section SubCGroups.
Variable P         : G -> CProp.
Variable Punit     : (P Zero).
Variable op_pres_P : (bin_op_pres_pred ? P csg_op).
Variable inv_pres_P : (un_op_pres_pred ? P cg_inv).

(* Begin_Tex_Verb *)
Local subcrr : CMonoid := (Build_SubCMonoid ? ? Punit op_pres_P).
Local subinv : (CSetoid_un_op subcrr) :=
  (Build_SubCSetoid_un_op ? ? ? inv_pres_P).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma isgrp_scrr: (is_CGroup subcrr subinv).
(* End_Tex_Verb *)
Red. Intro x. Case x. Intros. Simpl. Apply cg_rht_inv_unfolded.
Qed.

(* Begin_Tex_Verb *)
Definition Build_SubCGroup : CGroup := (Build_CGroup subcrr ? isgrp_scrr).
(* End_Tex_Verb *)

End SubCGroups.

End CGroup_basics.

Hints Resolve cg_rht_inv_unfolded cg_lft_inv_unfolded : algebra.
Hints Resolve cg_inv_inv cg_minus_correct cg_zero_inv cg_inv_zero : algebra.
Hints Resolve cg_minus_unfolded grp_inv_assoc cg_inv_op csg_op_inv : algebra.
Hints Resolve cg_minus_wd : algebra_c.

(* Tex_Prose
\section{Associative properties of groups}
\begin{convention}
Let \verb!G! be a group.
\end{convention}
*)
Section Assoc_properties.
Variable G : CGroup.

(* Begin_Tex_Verb *)
Lemma assoc_1 : (x,y,z:G)(x[-](y[-]z) [=] (x[-]y)[+]z).
(* End_Tex_Verb *)
Intros x y z; Unfold cg_minus.
Stepr x[+]([--]y[+]z).
Step_final x[+]([--]y[+][--][--]z).
Qed.

(* Begin_Tex_Verb *)
Lemma assoc_2 : (x,y,z:G)(x[+](y[-]z) [=] (x[+]y)[-]z).
(* End_Tex_Verb *)
Intros x y z; Unfold cg_minus; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_plus : (x,y,z:G)((x[-](y[+]z)) [=] ((x[-]y)[-]z)).
(* End_Tex_Verb *)
Intros x y z.
Unfold cg_minus.
Step_final x[+]([--]y[+][--]z).
Qed.

(* Begin_Tex_Verb *)
Lemma zero_minus : (x:G)((Zero [-] x) [=] ([--] x)).
(* End_Tex_Verb *)
Intro x.
Unfold cg_minus.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cg_cancel_mixed:(x,y:G)(x[=]x[-]y[+]y).
(* End_Tex_Verb *)
 Intros x y.
 Unfold cg_minus.
 Stepr x[+]([--]y[+]y).
 Step_final x[+]Zero.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_resp_eq:(x,y,z:G)(y[=]z)->(x[+]y[=]x[+]z).
(* End_Tex_Verb *)
Algebra.
Qed.

End Assoc_properties.

Hints Resolve assoc_1 assoc_2 minus_plus zero_minus: algebra.


(* Tex_Prose
\section{Apartness in Constructive Groups}
Specific properties of {\em constructive} groups.
\begin{convention}
Let \verb!G! be a group.
\end{convention}
*)
Section cgroups_apartness.
Variable G : CGroup.

(* Begin_Tex_Verb *)
Lemma cg_add_ap_zero :
  (x,y:G)((x [+] y) [#] Zero) -> (x [#] Zero) + (y [#] Zero).
(* End_Tex_Verb *)
Intros x y H.
Apply (bin_op_strext ? csg_op x Zero y Zero).
Stepr (Zero::G).
Qed.

(* Begin_Tex_Verb *)
Lemma op_rht_resp_ap: (x,y,z:G)(x [#] y) -> (x [+] z) [#] (y [+] z).
(* End_Tex_Verb *)
Intros x y z H.
Cut (x [+] z) [-] z [#] (y [+] z) [-] z.
Intros h.
Case (bin_op_strext ? ? ? ? ? ? h).
 Auto.
Intro contra; Elim (ap_irreflexive ? ? contra).

Step x; Stepr y.
Qed.

(* Begin_Tex_Verb *)
Lemma op_lft_resp_ap: (x,y,z:G)(y [#] z) -> (x [+] y) [#] (x [+] z).
(* End_Tex_Verb *)
Proof.
Intros x y z H.
Step y[+]x.
Stepr z[+]x.
Apply op_rht_resp_ap; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cg_ap_cancel_rht: (x,y,z:G) ((x [+] z) [#] (y [+] z)) -> x [#] y.
(* End_Tex_Verb *)
Intros x y z H.
Apply ap_well_def_rht_unfolded with (y[+]z)[-]z.
 Apply ap_well_def_lft_unfolded with (x[+]z)[-]z.
  Apply (op_rht_resp_ap ? ? ([--]z) H).
 Stepr x [+] Zero.
 Step_final x [+] (z[-]z).
Stepr y [+] Zero.
Step_final y [+] (z[-]z).
Qed.

(* Begin_Tex_Verb *)
Lemma plus_cancel_ap_rht : (x,y,z:G)((x[+]z) [#] (y[+]z)) -> x[#]y.
(* End_Tex_Verb *)
Proof cg_ap_cancel_rht.

(* Begin_Tex_Verb *)
Lemma cg_ap_cancel_lft: (x,y,z:G) ((x [+] y) [#] (x [+] z)) -> y [#] z.
(* End_Tex_Verb *)
Intros x y z H.
Apply ap_symmetric_unfolded.
Apply cg_ap_cancel_rht with x.
Apply ap_symmetric_unfolded.
Step x[+]y.
Stepr x[+]z.
Qed.


(* Begin_Tex_Verb *)
Lemma plus_cancel_ap_lft : (x,y,z:G)((z[+]x) [#] (z[+]y)) -> x[#]y.
(* End_Tex_Verb *)
Intros x y z H.
Apply cg_ap_cancel_lft with z.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_ap_zero: (x,y:G)(x [#] y) -> (x[-]y) [#] Zero.
(* End_Tex_Verb *)
Intros x y H.
Stepr y[-]y.
Unfold cg_minus.
Apply op_rht_resp_ap; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma zero_minus_apart: (x,y:G)((x[-]y) [#] Zero) -> x [#] y.
(* End_Tex_Verb *)
Unfold cg_minus. Intros x y H.
Cut x[+][--]y [#] y[+][--]y. Intros h.
Apply (cg_ap_cancel_rht ? ? ? h).

Stepr (Zero::G).
Qed.

(* Begin_Tex_Verb *)
Lemma inv_resp_ap_zero: (x:G)(x [#] Zero) -> [--]x [#] Zero.
(* End_Tex_Verb *)
Intros x H.
Step Zero[+][--]x.
Step Zero[-]x.
Apply minus_ap_zero.
Apply (ap_symmetric G).
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_resp_ap : (x,y:G)(x[#]y) -> ([--]x) [#] ([--]y).
(* End_Tex_Verb *)
Intros x y H.
Apply cg_ap_cancel_lft with x[+]y.
Apply ap_well_def_lft with y.
 Apply ap_well_def_rht with x.
  Apply ap_symmetric_unfolded; Assumption.
 Stepr x[+](y[+][--]y).
 Step_final x[+]Zero.
Stepr (y[+]x)[+][--]x.
Stepr y[+](x[+][--]x).
Step_final y[+]Zero.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_ap_lft : (x,y,z:G)(x[#]y) -> (z[-]x) [#] (z[-]y).
(* End_Tex_Verb *)
Intros x y z H.
Unfold cg_minus.
Apply op_lft_resp_ap.
Apply inv_resp_ap.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_resp_ap_rht : (x,y,z:G)(x[#]y) -> (x[-]z) [#] (y[-]z).
(* End_Tex_Verb *)
Intros x y z H.
Unfold cg_minus.
Apply op_rht_resp_ap.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma minus_cancel_ap_rht : (x,y,z:G)((x[-]z) [#] (y[-]z)) -> x[#]y.
(* End_Tex_Verb *)
Unfold cg_minus.
Intros x y z H.
Exact (plus_cancel_ap_rht ? ? ? H).
Qed.

End cgroups_apartness.
Hints Resolve op_rht_resp_ap op_lft_resp_ap : algebra.
Hints Resolve minus_ap_zero zero_minus_apart inv_resp_ap_zero : algebra.

Section CGroup_Ops.

(* Tex_Prose
\section{Functional operations}

As before, we lift our group operations to the function space of the group.

\begin{convention} Let \verb!G:CGroup! and \verb!F,F':(PartFunct G)! with domains characterized respectively by \verb!P! and \verb!G!.
\end{convention}
*)

Variable G:CGroup.

Variables F,F' : (PartFunct G).

Local P := (Pred F).
Local Q := (Pred F').

Section Part_Function_Inv.

(* Begin_Tex_Verb *)
Lemma part_function_inv_strext :
  (x,y:G)(Hx:(P x))(Hy:(P y))
  (([--](F x Hx)[#][--](F y Hy))->(x[#]y)).
(* End_Tex_Verb *)
Intros x y Hx Hy H.
Apply pfstrx with F Hx Hy.
Apply un_op_strext_unfolded with (!cg_inv G); Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Finv := (Build_PartFunct G ? 
  (pfprwd ? F)
  [x:G][Hx:(P x)][--](F x Hx) 
  part_function_inv_strext).
(* End_Tex_Verb *)

End Part_Function_Inv.

Section Part_Function_Minus.

(* Begin_Tex_Verb *)
Lemma part_function_minus_strext :
  (x,y:G)(Hx:(Conj P Q x))(Hy:(Conj P Q y))
  ((((F x (prj1 G ??? Hx))[-](F' x (prj2 G ??? Hx)))[#]
    ((F y (prj1 G ??? Hy))[-](F' y (prj2 G ??? Hy))))->(x[#]y)).
(* End_Tex_Verb *)
Intros x y Hx Hy H.
Cut ((F x (prj1 G ??? Hx))[#](F y (prj1 G ??? Hy)))+((F' x (prj2 G ??? Hx))[#](F' y (prj2 G ??? Hy))).
Intro H0.
Elim H0; Intro H1; Exact (pfstrx ?????? H1).

Apply cg_minus_strext; Auto.
Qed.

(* Begin_Tex_Verb *)
Definition Fminus := (Build_PartFunct G ? 
  (conj_wd ??? (pfprwd ? F) (pfprwd ? F'))
  [x:G][Hx:(Conj P Q x)]((F x (prj1 G ??? Hx))[-](F' x (prj2 G ??? Hx))) 
  part_function_minus_strext).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\begin{itemize}
\item \verb!(Finv ? F)! is denoted by {\tt\hypertarget{Operator_11}{\{--\}F}}.
\item \verb!(Fminus ? F G)! is denoted by {\tt\hypertarget{Operator_12}{F{-}G}}.
\end{itemize}
\end{notation}
*)

End Part_Function_Minus.

End CGroup_Ops.

Implicits Finv [1].
Distfix RIGHTA 1 "{--} _" Finv.

Implicits Fminus [1].
Infix NONA 7 "{-}" Fminus.

Hints Resolve pfwdef : algebra.
