(* $Id: CSemiGroups.v,v 1.15 2003/03/13 12:06:15 lcf Exp $ *)

Require Export CSetoids.
Require Export CTactics.

(* Begin_SpecReals *)

(* Tex_Prose
\chapter{Semigroups}
*)

(* Tex_Prose
\section{Definition of the notion of semigroup}
*)

(* Begin_Tex_Verb *)
Definition is_CSemi_grp [A:CSetoid; unit: A; op:(CSetoid_bin_op A)] :=
  (associative op).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record CSemi_grp : Type :=
  { csg_crr   :> CSetoid;
    csg_unit  :  csg_crr;                      (* non-empty *)
    csg_op    :  (CSetoid_bin_op csg_crr);
    csg_proof :  (is_CSemi_grp csg_crr csg_unit csg_op)
  }.
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\verb!csg_unit ?! is denoted with {\tt\hypertarget{Syntactic_4}{Zero}}.
\end{notation}
*)

Syntactic Definition Zero := (csg_unit ?).
Syntax constr level 1:
  csg_unit_constant [(csg_unit $e0)] -> ["Zero"].

(* Tex_Prose
\begin{notation}
\hypertarget{Operator_7}{}\verb!(csg_op ? x y)! is denoted with \verb!x [+] y!.
\end{notation}

\begin{nameconvention}
In the {\em names} of lemmas, we will denote \verb!Zero! with \verb!zero!,
and \verb![+]! with \verb!plus!.
We denote \verb![#] Zero! in the names of lemmas by \verb!ap_zero!
(and not, e.g.\ \verb!nonzero!).
\end{nameconvention}
*)

Implicits csg_op [1].
Infix 7 "[+]" csg_op.
(* End_SpecReals *)

(* Tex_Prose
\section{Semi group axioms}
The axiomatic properties of a semi group.
\begin{convention}
Let \verb!G! be a semi-group.
\end{convention}
*)
Section CSemi_grp_axioms.
Variable G : CSemi_grp.

(* Begin_Tex_Verb *)
Lemma CSemi_grp_is_CSemi_grp : (is_CSemi_grp G Zero csg_op).
(* End_Tex_Verb *)
Elim G; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_assoc : (associative (!csg_op G)).
(* End_Tex_Verb *)
Exact CSemi_grp_is_CSemi_grp.
Qed.

End CSemi_grp_axioms.

(* Begin_SpecReals *)

(* Tex_Prose
\section{Semi group basics}
\begin{convention}
Let \verb!G! be a semi-group.
\end{convention}
*)
Section CSemi_grp_basics.
Variable G : CSemi_grp.

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Lemma plus_assoc_unfolded : (G:CSemi_grp)(x,y,z:G)
                            (x [+] (y [+] z)) [=] ((x [+] y) [+] z).
(* End_Tex_Verb *)
Exact plus_assoc.
Qed.

(* Begin_SpecReals *)

(* Tex_Prose
The predicate "non-zero" is defined as follows.
In lemmas we will continue to write \verb!x [#] Zero!, rather than
\verb!nonZeroP x!, but the predicate is useful for some high-level definitions,
e.g. for the setoid of non-zeros.
*)

(* Begin_Tex_Verb *)
Definition nonZeroP [x:G] : CProp := (x [#] Zero).
(* End_Tex_Verb *)

End CSemi_grp_basics.

Implicits nonZeroP [1].
(* End_SpecReals *)

Hints Resolve plus_assoc_unfolded : algebra.

(* Tex_Prose
\section{Functional operations}
We can also define a similar addition operator, which will be denoted by {\tt\hypertarget{Operator_8}{\{+\}}}, on partial functions.

\begin{convention} Whenever possible, we will denote the functional construction corresponding to an algebraic operation by the same symbol enclosed in curly braces.
\end{convention}

At this stage, we will always consider automorphisms; we {\em could} treat this in a more general setting, but we feel that it wouldn't really be a useful effort.

\begin{convention} Let \verb!G:CSemi_grp! and \verb!F,F':(PartFunct G)! and denote by \verb!P! and \verb!Q!, respectively, the predicates characterizing their domains.
\end{convention}
*)

Section Part_Function_Plus.

Variable G:CSemi_grp.

Variables F,F' : (PartFunct G).

Local P := (Pred F).
Local Q := (Pred F').

(* Begin_Tex_Verb *)
Lemma part_function_plus_strext :
  (x,y:G)(Hx:(Conj P Q x))(Hy:(Conj P Q y))
  ((((F x (prj1 G ??? Hx))[+](F' x (prj2 G ??? Hx)))[#]
    ((F y (prj1 G ??? Hy))[+](F' y (prj2 G ??? Hy))))->(x[#]y)).
(* End_Tex_Verb *)
Intros x y Hx Hy H.
Elim (bin_op_strext_unfolded ?????? H); Intro H1; Exact (pfstrx ?????? H1).
Qed.

(* Begin_Tex_Verb *)
Definition Fplus := (Build_PartFunct G ? 
  (conj_wd ??? (pfprwd ? F) (pfprwd ? F'))
  [x:G][Hx:(Conj P Q x)]((F x (prj1 G ??? Hx))[+](F' x (prj2 G ??? Hx))) 
  part_function_plus_strext).
(* End_Tex_Verb *)

End Part_Function_Plus.

Implicits Fplus [1].
Infix 7 "{+}" Fplus.

(* Tex_Prose
\section{Sub-semi-groups}
\begin{convention}
Let \verb!csg! a semi-group and \verb!P! a predicate on the semi-group with
\verb!P Zero! and which is preserved by \verb![+]!.
\end{convention}
*)
Section SubCSemi_grps.
Variable csg       : CSemi_grp.
Variable P         : csg -> CProp.
Variable Punit     : (P Zero).
Variable op_pres_P : (bin_op_pres_pred ? P csg_op).

(* Begin_Tex_Verb *)
Local subcrr : CSetoid := (Build_SubCSetoid ? P).
Definition Build_SubCSemi_grp : CSemi_grp :=
  (Build_CSemi_grp subcrr
                   (Build_subcsetoid_crr ? ? ? Punit)
                   (Build_SubCSetoid_bin_op ? ? ? op_pres_P)
                   (restr_f_assoc ? ? ? op_pres_P (plus_assoc csg))).
(* End_Tex_Verb *)
End SubCSemi_grps.
