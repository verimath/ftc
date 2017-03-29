(* $Id: CFields.v,v 1.16 2003/03/13 12:06:13 lcf Exp $ *)

Require Export RRefl_corr.

Transparent sym_eq.
Transparent f_equal.


Transparent cs_crr.
Transparent csg_crr.
Transparent cm_crr.
Transparent cg_crr.
Transparent cr_crr.

Transparent csf_fun.
Transparent csbf_fun.
Transparent csr_rel.

Transparent cs_eq.
Transparent cs_neq.
Transparent cs_ap.
Transparent csg_unit.
Transparent csg_op.
Transparent cg_inv.
Transparent cg_minus.
Transparent cr_one.
Transparent cr_mult.

Transparent nexp_op.

(* Begin_SpecReals *)

(* FIELDS *)

(* Tex_Prose
\chapter{Fields}\label{section:fields}
\section{Definition of the notion Field}
*)

(* Begin_Tex_Verb *)
Definition is_CField
  [R: CRing; cf_rcpcl: (x:R)(x[#]Zero)->R] : Prop :=
  (x:R)(Hx:(x[#]Zero))(is_inverse cr_mult One x (cf_rcpcl x Hx)).

Record CField : Type :=
  { cf_crr   :> CRing;
    cf_rcpcl :  (x:cf_crr)(x[#]Zero)->cf_crr;
    cf_proof :  (is_CField cf_crr cf_rcpcl);
    cf_rcpsx :  (x,y:cf_crr)(x_,y_:?)
       (((cf_rcpcl x x_)[#](cf_rcpcl y y_))->(x[#]y))
  }.
(* End_Tex_Verb *)
(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition f_rcpcl' [F:CField] : (PartFunct F).
(* End_Tex_Verb *)
Intro F.
Apply Build_PartFunct with [x:F]x[#]Zero (cf_rcpcl F).
 Red; Intros; Step x.
Exact (cf_rcpsx F).
Defined.

(* Begin_Tex_Verb *)
Definition f_rcpcl [F:CField][x:F][x_:x[#]Zero] := ((f_rcpcl' F) x x_).
(* End_Tex_Verb *)

Implicits f_rcpcl [1].

(* Tex_Prose
\verb!cf_div! is the division in a field.
*)
(* Begin_Tex_Verb *)
Definition cf_div [F:CField; x,y: F; y_:y[#]Zero]: F := (x [*] (f_rcpcl y y_)).
(* End_Tex_Verb *)


(* Tex_Prose
\begin{notation}
The division \verb!(cf_div x y Hy)! is denoted infix by {\tt\hypertarget{Operator_19}{x [/] y [//] Hy}}.
\end{notation}
*)

Implicits cf_div [1].
Notation "x [/] y [//] Hy" := (cf_div x y Hy) (at level 6).

Syntax constr level 6:
  cf_div_infix [(cf_div $e1 $e2 $e3)] ->
    [[<hov 1> $e1:E [0 1] "[/]" $e2:L "[//]" $e3:L]].

(* Tex_Prose
\begin{numconvention}\label{convention:div-form}\em
\begin{enumerate}
\item
 We do not use \verb!NonZeros!,
 but write the condition \verb![#]Zero! separately.
\item
 In each lemma, we use only variables for proof objects, and these variables
 are universally quantified.

 E.g. the informal lemma
\begin{verbatim}
(1/x).(1/y) = 1/(x.y) for all x and y
\end{verbatim}
   is formalized as
\begin{verbatim}
(x,y:F)(H1:x#0)(H2:y#0)(H3:(x.y)#0) (1/x//H1).(1/y//H2) = 1/(x.y)//H3
\end{verbatim}
and {\em not} as
\begin{verbatim}
(x,y:F)(H1:x#0)(H2:y#0)(1/x//H1).(1/y//H2) = 1/(x.y)//(prod_nz x y H1 H2)
\end{verbatim}

   We have made this choice to make it easier to apply lemmas; this can be
   quite awkward if we would use the last formulation.

\item
   So every division occurring in the formulation of a lemma is of the form
   \verb!e[/]e'[//]H! where \verb!H! is a variable.
   Only exceptions: we may write \verb!e[/](Snring n)! and
   \verb!e[/]TwoNZ!,  \verb!e[/]ThreeNZ! and so on.
   (Constants like \verb!TwoNZ! will be defined later on.)
\end{enumerate}
\end{numconvention}
*)

(* Tex_Prose
\section{Field axioms}
\begin{convention}
Let \verb!F! be a field.
\end{convention}
*)
Section Field_axioms.
Variable F : CField.

(* Begin_Tex_Verb *)
Lemma CField_is_CField : (is_CField F (cf_rcpcl F)).
(* End_Tex_Verb *)
Elim F; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma rcpcl_is_inverse :
 (x:F)(x_:x[#]Zero)(is_inverse cr_mult One x (cf_rcpcl F x x_)).
(* End_Tex_Verb *)
Apply CField_is_CField.
Qed.

End Field_axioms.

Section Field_basics.
(* Tex_Prose
\section{Field basics}
\begin{convention}
Let \verb!F! be a field.
\end{convention}
*)
Variable F : CField.

(* Begin_Tex_Verb *)
Lemma rcpcl_is_inverse_unfolded :
              (x:F)(x_:x[#]Zero) x[*] (cf_rcpcl F x x_) [=] One.
(* End_Tex_Verb *)
Proof (rcpcl_is_inverse F).

(* Begin_Tex_Verb *)
Lemma field_mult_inv: (x:F)(x_:x[#]Zero)(x [*] (f_rcpcl x x_)) [=] One.
(* End_Tex_Verb *)
Intros x H.
Unfold f_rcpcl.
Apply (cf_proof F x H).
Qed.
Hints Resolve field_mult_inv : algebra.

(* Begin_Tex_Verb *)
Lemma field_mult_inv_op : (x:F)(x_:x[#]Zero)((f_rcpcl x x_) [*] x) [=] One.
(* End_Tex_Verb *)
Intros x H.
Step x [*] (f_rcpcl x H).
Apply field_mult_inv.
Qed.

End Field_basics.

Hints Resolve field_mult_inv field_mult_inv_op : algebra.

Section Field_multiplication.
(* Tex_Prose
\section{Properties of multiplication}
\begin{convention}
Let \verb!F! be a field.
\end{convention}
*)
Variable F : CField.

(* Begin_Tex_Verb *)
Lemma mult_resp_ap_zero:
  (x,y:F)(x [#] Zero) -> (y [#] Zero) -> (x[*]y [#] Zero).
(* End_Tex_Verb *)
Intros x y Hx Hy.
Cut ((x[*]y) [*] (f_rcpcl y Hy)) [#] (Zero [*] (f_rcpcl y Hy)).
Intro H.
Case (bin_op_strext ? ? ? ? ? ? H).
 Auto.
Intro contra; Elim (ap_irreflexive ? ? contra).

Stepr (Zero::F).
Step x.
Stepr x[*](y[*](f_rcpcl y Hy)).
Step_final x[*]One.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_lft_resp_ap :
   (x,y,z:F)(x [#] y) -> (z [#] Zero) -> (z [*] x) [#] (z [*] y).
(* End_Tex_Verb *)
Intros x y z H Hz.
Apply zero_minus_apart.
Unfold cg_minus.
Step z[*]x[+](z[*][--]y).
Step z[*](x[+][--]y).
Step z[*](x[-]y).
Apply mult_resp_ap_zero; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_rht_resp_ap :
   (x,y,z:F)(x [#] y) -> (z [#] Zero) -> (x [*] z) [#] (y [*] z).
(* End_Tex_Verb *)
Intros x y z H Hz.
Step z [*] x.
Stepr z [*] y.
Apply mult_lft_resp_ap; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_resp_neq_zero :
   (x,y:F)(x [~=] Zero)->(y [~=] Zero)->((x [*] y) [~=] Zero).
(* End_Tex_Verb *)
Intros x y Hx Hy.
Cut ~(Not (x [#] Zero)).
Intro H.
Cut ~(Not (y [#] Zero)).
Intro H0.
Apply notnot_ap_imp_neq.
Cut (x [#] Zero)->(y [#] Zero)->((x[*]y) [#] Zero).
Intro H1.
Intro.
Apply H0; Intro H3.
Apply H; Intro H4.
Apply H2; Auto.

Intros; Apply mult_resp_ap_zero; Auto.

Apply neq_imp_notnot_ap; Auto.

Apply neq_imp_notnot_ap; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_resp_neq :
   (x,y,z:F)(x [~=] y)->(z [~=] Zero)->((x [*] z) [~=] (y [*] z)).
(* End_Tex_Verb *)
Intros x y z H Hz.
Generalize (neq_imp_notnot_ap ? ? ? H).
Generalize (neq_imp_notnot_ap ? ? ? Hz).
Generalize (mult_rht_resp_ap x y z).
Intros H1 H2 H3.
Apply notnot_ap_imp_neq.
Intro H4.
Apply H2; Intro.
Apply H3; Intro.
Apply H4.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_eq_zero :
   (x,y:F)(x [~=] Zero)->((x [*] y) [=] Zero)->(y [=] Zero).
(* End_Tex_Verb *)
Intros x y Hx Hxy.
Apply not_ap_imp_eq.

Intro H.
Elim (eq_imp_not_neq ? ? ? Hxy).
Apply mult_resp_neq_zero.
 Assumption.
Apply ap_imp_neq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_cancel_lft : (x,y,z:F)(z [#] Zero)->(z[*]x [=] z[*]y)->(x [=] y).
(* End_Tex_Verb *)
Intros x y z Hz H.
Apply not_ap_imp_eq.
Intro H2.
Elim (eq_imp_not_ap ? ? ? H).
Apply mult_lft_resp_ap; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_cancel_rht : (x,y,z:F)(z [#] Zero)->(x[*]z [=] y[*]z)->(x [=] y).
(* End_Tex_Verb *)
Intros x y z Hz H.
Apply (mult_cancel_lft x y z).
 Assumption.
Stepr (y[*]z).
Step_final (x[*]z).
Qed.

(* Begin_Tex_Verb *)
Lemma square_eq_aux :
      (x,a:F)(x[^](2) [=] a[^](2))-> (x[+]a)[*](x[-]a) [=] Zero.
(* End_Tex_Verb *)
Intros x a H.
RStep (x[^](2) [-] a[^](2)).
Step_final a[^](2) [-] a[^](2).
Qed.

(* Begin_Tex_Verb *)
Lemma square_eq_weak :
      (x,a:F)(x[^](2) [=] a[^](2))-> 
      (Not ((x [#] a)*(x [#] [--]a))).
(* End_Tex_Verb *)
Intros x a H.
Intro H0.
Elim H0; Intros H1 H2.
Generalize (square_eq_aux ? ? H); Intro H3.
Generalize (eq_imp_not_ap ? ? ? H3); Intro H4.
Apply H4.
Apply mult_resp_ap_zero.
 Stepr [--]a [+] a.
Stepr a [-] a.
Apply minus_resp_ap_rht.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cconditional_square_eq :
   (x,a:F)((Two::F) [#] Zero)->(a [#] Zero)->
   (x[^](2) [=] a[^](2))->{x [=] a} + {x [=] [--]a}.
(* End_Tex_Verb *)
Intros x a H Ha H0.
Cut a [#] [--]a.
Intro H1.
Elim (ap_cotransitive_unfolded ? ? ? H1 x); Intro H2.
 Right.
 Apply not_ap_imp_eq.
 Intro H3.
 Elim (square_eq_weak ? ? H0).
 Split; Auto.
 Apply ap_symmetric_unfolded; Auto.
Left.
Apply not_ap_imp_eq.
Intro H3.
Elim (square_eq_weak ? ? H0); Auto.

Apply plus_cancel_ap_lft with a.
Stepr (Zero::F).
Step Two[*]a.
Apply mult_resp_ap_zero; Auto.
Qed.

End Field_multiplication.

Hints Resolve mult_resp_ap_zero : algebra.


Section Rcpcl_properties.
(* Tex_Prose
\section{Properties of reciprocal}
\begin{convention}
Let \verb!F! be a field.
\end{convention}
*)
Variable F : CField.

(* Begin_Tex_Verb *)
Lemma inv_one : (f_rcpcl One (ring_non_triv F)) [=] One.
(* End_Tex_Verb *)
Step One [*] (f_rcpcl One (ring_non_triv F)).
Apply field_mult_inv.
Qed.

(* Begin_Tex_Verb *)
Lemma f_rcpcl_wd : (x,y:F)(x_,y_:?) (x [=] y) ->
                                                (f_rcpcl x x_) [=] (f_rcpcl y y_).
(* End_Tex_Verb *)
Intros x y H.
Unfold f_rcpcl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma f_rcpcl_mult : (y,z:F)(y_:y [#] Zero)(z_:z[#]Zero)(yz_:y[*]z[#]Zero)
 (f_rcpcl (y[*]z) yz_) [=] (f_rcpcl y y_) [*](f_rcpcl z z_).
(* End_Tex_Verb *)
Intros y z nzy nzz nzyz.
Apply mult_cancel_lft with y[*]z.
 Assumption.
Step (One::F).
Stepr (y[*]z)[*]((f_rcpcl z nzz)[*](f_rcpcl y nzy)).
Stepr y[*](z[*]((f_rcpcl z nzz)[*](f_rcpcl y nzy))).
Stepr y[*]((z[*](f_rcpcl z nzz))[*](f_rcpcl y nzy)).
Stepr y[*](One[*](f_rcpcl y nzy)).
Stepr y[*](f_rcpcl y nzy).
Step_final (One::F).
Qed.

(* Begin_Tex_Verb *)
Lemma f_rcpcl_resp_ap_zero : (y:F)(y_:(y [#] Zero))
                                  ((f_rcpcl y y_) [#] Zero).
(* End_Tex_Verb *)
Intros y nzy.
Apply cring_mult_ap_zero_op with y.
Step (One::F).
Qed.

(* Begin_Tex_Verb *)
Lemma f_rcpcl_f_rcpcl : (x:F)(x_:x [#] Zero)(r_:(f_rcpcl x x_)[#]Zero)
                        (f_rcpcl (f_rcpcl x x_) r_) [=] x.
(* End_Tex_Verb *)
Intros x nzx nzr.
Apply mult_cancel_rht with (f_rcpcl x nzx).
 Assumption.
Stepr (One::F).
Step_final (f_rcpcl x nzx)[*](f_rcpcl (f_rcpcl x nzx) nzr).
Qed.

End Rcpcl_properties.

Section MultipGroup.

Variable F: CField.

(* Tex_Prose
The multiplicative group of nonzeros of a field.
*)
(* Tex_Prose
The multiplicative monoid of NonZeros.
*)
(* Begin_Tex_Verb *)
Definition NonZeroMonoid : CMonoid :=
  (Build_SubCMonoid (Build_multCMonoid F)
                    (!nonZeroP F) (one_ap_zero F)
                    (mult_resp_ap_zero F)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition fmg_cs_inv: (CSetoid_un_op NonZeroMonoid).
(* End_Tex_Verb *)
Red.
Cut (x:NonZeroMonoid)(nonZeroP (cf_rcpcl F (scs_elem ?? x) (scs_prf ?? x))).
Intro.
Apply Build_CSetoid_fun with [x:NonZeroMonoid](Build_subcsetoid_crr ?? (cf_rcpcl F (scs_elem ?? x) (scs_prf ?? x)) (H x)).
Red.
Simpl.
Destruct x; Destruct y; Intros.
Apply (cf_rcpsx ????? H0).
Intro; Simpl.
Red.
Step (f_rcpcl (scs_elem ?? x) (scs_prf ?? x)).
Apply f_rcpcl_resp_ap_zero.
Defined.

(* Begin_Tex_Verb *)
Lemma plus_nonzeros_eq_mult_dom : (x,y:NonZeroMonoid)
            (scs_elem ?? (x [+] y)) [=] ((scs_elem ?? x) [*] (scs_elem ?? y)).
(* End_Tex_Verb *)
Destruct x; Destruct y; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma cfield_to_mult_cgroup : CGroup.
(* End_Tex_Verb *)
Apply (Build_CGroup NonZeroMonoid fmg_cs_inv).
Intro x.
Red.
Elim x; Intros x_ Hx.
Simpl; Apply cf_proof.
Qed.

End MultipGroup.

Section Div_properties.
(* Tex_Prose
\section{Properties of division}
\begin{convention}
Let \verb!F! be a field.
\end{convention}

\begin{nameconvention}
In the names of lemmas, we denote \verb![/]! by \verb!div!, and
\verb!One[/]! by \verb!recip!.
\end{nameconvention}
*)
Variable F : CField.

(* Begin_Tex_Verb *)
Lemma div_prop : (x:F)(x_:x[#]Zero)(Zero[/]x[//]x_ [=] Zero).
(* End_Tex_Verb *)
Unfold cf_div; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma div_1 : (x,y:F)(y_:y [#] Zero)((x[/]y[//]y_)[*]y [=] x).
(* End_Tex_Verb *)
Intros x y y_.
Step (x[*](f_rcpcl y y_))[*]y.
Step x[*]((f_rcpcl y y_)[*]y).
Step_final x[*]One.
Qed.

(* Begin_Tex_Verb *)
Lemma div_1' : (x,y:F)(y_:y [#] Zero)(y[*](x[/]y[//]y_) [=] x).
(* End_Tex_Verb *)
Intros x y y_.
Step (x[/]y[//]y_)[*]y.
Apply div_1.
Qed.

(* Begin_Tex_Verb *)
Lemma div_1'' : (x,y:F)(y_:y [#] Zero)((x[*]y)[/]y[//]y_ [=] x).
(* End_Tex_Verb *)
Intros x y y_.
Unfold cf_div.
Step y[*]x[*](f_rcpcl y y_).
Step y[*](x[*](f_rcpcl y y_)).
Change y[*](x[/]y[//]y_) [=] x.
Apply div_1'.
Qed.

Hints Resolve div_1 : algebra.

(* Begin_Tex_Verb *)
Lemma x_div_x : (x:F)(x_: x [#] Zero)((x[/]x[//]x_) [=] One).
(* End_Tex_Verb *)
Intros x x_.
Unfold cf_div.
Apply field_mult_inv.
Qed.

Hints Resolve x_div_x : algebra.

(* Begin_Tex_Verb *)
Lemma x_div_one : (x:F)((x[/]One[//](ring_non_triv (F))) [=] x).
(* End_Tex_Verb *)
Intro x.
Unfold cf_div.
Generalize inv_one; Intro H.
Step x[*]One.
Apply mult_one.
Qed.

(* Tex_Prose
The next lemma says \verb!x.(y/z) = (x.y)/z!.
*)
(* Begin_Tex_Verb *)
Lemma x_mult_y_div_z : (x,y,z:F)(z_: z [#] Zero)
                       ((x[*](y[/]z[//]z_)) [=] ((x[*]y)[/]z[//]z_)).
(* End_Tex_Verb *)
Unfold cf_div; Algebra.
Qed.

Hints Resolve x_mult_y_div_z : algebra.


(* Begin_Tex_Verb *)
Lemma div_wd : (x,x',y,y':F)(y_:y [#] Zero)(y'_:y'[#]Zero)
  (x [=] x')->(y [=] y')->(x[/]y[//]y_ [=] x'[/]y'[//]y'_).
(* End_Tex_Verb *)
Intros x x' y y' nzy nzy' H H0.
Unfold cf_div.
Cut (f_rcpcl y nzy) [=] (f_rcpcl y' nzy').
Intro H1.
Algebra.

Apply f_rcpcl_wd.
Assumption.
Qed.

Hints Resolve div_wd : algebra_c.

(* Tex_Prose
The next lemma says \verb!(x/y)/z = x/(y.z)!
*)
(* Begin_Tex_Verb *)
Lemma div_div : (x,y,z:F)(y_:y [#] Zero)(z_:z[#]Zero)
  (yz_:y[*]z[#]Zero)
    (((x[/]y[//]y_)[/]z[//]z_) [=] (x[/](y[*]z)[//]yz_)).
(* End_Tex_Verb *)
Intros x y z nzy nzz nzyz.
Unfold cf_div.
Step x[*]((f_rcpcl y nzy)[*](f_rcpcl z nzz)).
Apply mult_wd_rht.
Apply eq_symmetric_unfolded.
Apply f_rcpcl_mult.
Qed.


(* Begin_Tex_Verb *)
Lemma div_resp_ap_zero_rev : (x,y:F)(y_:(y [#] Zero))(x[#]Zero) ->
                                  (x [/] y [//]y_ [#] Zero).
(* End_Tex_Verb *)
Intros x y nzy Hx.
Unfold cf_div.
Apply mult_resp_ap_zero.
 Assumption.
Apply f_rcpcl_resp_ap_zero.
Qed.


(* Begin_Tex_Verb *)
Lemma div_resp_ap_zero : (x,y:F)(y_:(y [#] Zero))
  (x [/] y [//]y_ [#] Zero) -> (x[#]Zero).
(* End_Tex_Verb *)
Intros x y nzy Hxy.
Step (x[/]y[//]nzy)[*]y.
Qed.

(* Tex_Prose
The next lemma says \verb!x/(y/z) = (x.z)/y!
*)
(* Begin_Tex_Verb *)
Lemma div_div2 : (x,y,z:F)
  (y_:y [#] Zero)(z_:z[#]Zero)(yz_:(y[/]z[//]z_)[#]Zero)
  ((x[/](y[/]z[//]z_) [//]yz_) [=] ((x[*]z)[/]y[//]y_)).
(* End_Tex_Verb *)
Intros x y z nzy nzz nzyz.
Unfold cf_div.
Stepr x[*](z[*](f_rcpcl y nzy)).
Apply mult_wd_rht.
Cut (f_rcpcl z nzz) [#] Zero.
Intro nzrz.
Apply eq_transitive_unfolded with (f_rcpcl y nzy) [*] (f_rcpcl (f_rcpcl z nzz) nzrz).
 Apply f_rcpcl_mult.
Stepr (f_rcpcl y nzy)[*]z.
Apply mult_wd_rht.
Apply f_rcpcl_f_rcpcl.

Apply f_rcpcl_resp_ap_zero.
Qed.

(* Tex_Prose
The next lemma says \verb!(x.p)/(y.q) = (x/y).(p/q)!
*)
(* Begin_Tex_Verb *)
Lemma mult_of_divs : (x,y,p,q:F)
  (y_:(y[#]Zero))(q_:(q[#]Zero))(yq_:y[*]q[#]Zero)
    ((x[*]p)[/](y[*]q)[//]yq_ [=] (x[/]y[//]y_)[*](p[/]q[//]q_)).
(* End_Tex_Verb *)
Intros x y p q nzy nzq nzyq.
Unfold cf_div.
Step x[*](p[*](f_rcpcl (y[*]q) nzyq)).
Stepr x[*]((f_rcpcl y nzy)[*](p[*](f_rcpcl q nzq))).
Apply mult_wd_rht.
Stepr ((f_rcpcl y nzy)[*]p)[*](f_rcpcl q nzq).
Stepr (p[*](f_rcpcl y nzy))[*](f_rcpcl q nzq).
Stepr p[*]((f_rcpcl y nzy)[*](f_rcpcl q nzq)).
Apply mult_wd_rht.
Apply f_rcpcl_mult.
Qed.

(* Begin_Tex_Verb *)
Lemma div_dist : (x,y,z:F)(z_:z[#]Zero)
  (x[+]y)[/]z[//]z_ [=] x[/]z[//]z_[+]y[/]z[//]z_.
(* End_Tex_Verb *)
Unfold cf_div; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma div_dist' : (x,y,z:F)(z_:z[#]Zero)
  (x[-]y)[/]z[//]z_[=]x[/]z[//]z_[-]y[/]z[//]z_.
(* End_Tex_Verb *)
Unfold cf_div; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma div_semi_sym : (x,y,z:F)(y_:y[#]Zero)(z_:z[#]Zero)
                     (x[/]y[//]y_)[/]z[//]z_ [=] (x[/]z[//]z_)[/]y[//]y_.
(* End_Tex_Verb *)
Intros.
Unfold cf_div.
Rational.
Qed.

Hints Resolve div_semi_sym : algebra.

(* Begin_Tex_Verb *)
Lemma eq_div : (x,y,u,v:F)(y_:y[#]Zero)(v_:v[#]Zero)
               (x[*]v [=] u[*]y) -> (x[/]y[//]y_ [=] u[/]v[//]v_).
(* End_Tex_Verb *)
Intros x y u v Hy Hv H.
Step (x[*]One)[/]y[//]Hy.
Step (x[*](v[/]v[//]Hv))[/]y[//]Hy.
Step ((x[*]v)[/]v[//]Hv)[/]y[//]Hy.
Step ((u[*]y) [/] v[//]Hv) [/]y[//]Hy.
Step ((u[*]y) [/] y[//]Hy) [/]v[//]Hv.
Step (u[*] (y [/] y[//]Hy)) [/]v[//]Hv.
Step_final (u[*] One) [/]v[//]Hv.
Qed.

(* Begin_Tex_Verb *)
Lemma div_strong_ext : (x,x',y,y':F)(y_:y[#]Zero)(y'_:y'[#]Zero)
                       (x[/]y[//]y_ [#] x'[/]y'[//]y'_) ->
                       (x[#]x') + (y[#]y').
(* End_Tex_Verb *)
Intros x x' y y' Hy Hy' H.
Unfold cf_div in H.
Elim (bin_op_strext F cr_mult ???? H).
 Auto.
Intro H1.
Right.
Unfold f_rcpcl in H1.
Exact (pfstrx ?????? H1).
Qed.

End Div_properties.

Hints Resolve div_1 div_1' div_1'' div_wd x_div_x x_div_one div_div div_div2
  mult_of_divs x_mult_y_div_z mult_of_divs div_dist div_dist' div_semi_sym
  div_prop : algebra.


Section Mult_Cancel_Ap_Zero.

Variable F : CField.

(* Begin_Tex_Verb *)
Lemma mult_cancel_ap_zero_lft :
 (x,y:F)(x [*] y [#] Zero) -> x [#] Zero.
(* End_Tex_Verb *)
Intros x y H.
Cut x [*] y [#] Zero[*]Zero.
Intro H0.
Elim (bin_op_strext_unfolded ? ? ? ? ? ? H0); Intro H1.
 3: Stepr (Zero::F).
Assumption.

Step (x[*]y)[/]y[//]H1.
Apply div_resp_ap_zero_rev.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma mult_cancel_ap_zero_rht :
 (x,y:F)(x [*] y [#] Zero) -> y [#] Zero.
(* End_Tex_Verb *)
Intros x y H.
Apply mult_cancel_ap_zero_lft with x.
Step x[*]y.
Qed.

(* Begin_Tex_Verb *)
Lemma recip_ap_zero :
 (x:F)(x_:x[#]Zero)(One[/]x[//]x_)[#]Zero.
(* End_Tex_Verb *)
Intros; Apply cring_mult_ap_zero with x.
Step (One::F).
Qed.

(* Begin_Tex_Verb *)
Lemma recip_resp_ap : (x,y:F)(x_:x[#]Zero)
 (y_:y[#]Zero)(x[#]y)->(One[/]x[//]x_)[#](One[/]y[//]y_).
(* End_Tex_Verb *)
Intros x y x_ y_ H.
Apply zero_minus_apart.
Apply mult_cancel_ap_zero_lft with x[*]y.
Apply ap_well_def_lft with (y[-]x).
 Apply minus_ap_zero.
 Apply ap_symmetric_unfolded; Assumption.
EApply eq_transitive_unfolded.
 2: Apply eq_symmetric_unfolded; Apply dist_2b.
Apply cg_minus_wd.
 Stepr (x[*]y)[*](One[/]x[//]x_).
 Stepr ((x[*]y)[*]One)[/]x[//]x_.
 Stepr (x[*]y)[/]x[//]x_.
 Stepr (y[*]x)[/]x[//]x_.
 Stepr y[*](x[/]x[//]x_).
 Step_final y[*]One.
Stepr (x[*]y)[*](One[/]y[//]y_).
Stepr ((x[*]y)[*]One)[/]y[//]y_.
Stepr (x[*]y)[/]y[//]y_.
Stepr x[*](y[/]y[//]y_).
Step_final x[*]One.
Qed.

End Mult_Cancel_Ap_Zero.

Section CField_Ops.

(* Tex_Prose
\section{Functional Operations}

We now move on to lifting these operations to functions.  As we are dealing with \emph{partial} functions, we don't have to worry explicitly about the function by which we are dividing being non-zero everywhere; this will simply be encoded in its domain.

\begin{convention} Let \verb!X:CField! and \verb!F,G:(PartFunct X)! have domains respectively \verb!P! and \verb!Q!.
\end{convention}
*)

Variable X:CField.

Variables F,G:(PartFunct X).

Local P := (pfpred X F).
Local Q := (pfpred X G).

Section Part_Function_Recip.

(* Tex_Prose
Some auxiliary notions are helpful in defining the domain.
*)

(* Begin_Tex_Verb *)
Local R:=(extend Q [x:X][Hx:(Q x)]((G x Hx)[#]Zero)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Local Ext2R := (!ext2 X Q [x:X][Hx:(Q x)]((G x Hx)[#]Zero)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma part_function_recip_strext :
  (x,y:X)(Hx:(R x))(Hy:(R y))
    ((One[/]?[//](Ext2R x Hx))[#](One[/]?[//](Ext2R y Hy)))->
      (x[#]y).
(* End_Tex_Verb *)
Intros x y Hx Hy H.
Elim (div_strong_ext ??????? H); Intro H1.
 ElimType False; Apply ap_irreflexive_unfolded with x:=(One::X); Auto.
Exact (pfstrx ?????? H1).
Qed.

(* Begin_Tex_Verb *)
Lemma part_function_recip_pred_wd : (pred_well_def X R).
(* End_Tex_Verb *)
Red; Intros x y H H0.
Elim H; Intros H1 H2; Split.
 Apply (pfprwd X G x y H1 H0).
Intro H3; Step (G x H1).
Qed.

(* Begin_Tex_Verb *)
Definition Frecip := (Build_PartFunct X ? 
  part_function_recip_pred_wd
  [x:X][Hx:(R x)](One[/]?[//](Ext2R x Hx))
  part_function_recip_strext).
(* End_Tex_Verb *)

End Part_Function_Recip.

Section Part_Function_Div.

(* Tex_Prose
For division things work out almost in the same way.
*)

(* Begin_Tex_Verb *)
Local R:=(Conj P (extend Q [x:X][Hx:(Q x)]((G x Hx)[#]Zero))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Local Ext2R := (!ext2 X Q [x:X][Hx:(Q x)]((G x Hx)[#]Zero)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma part_function_div_strext : (x,y:X)(Hx:(R x))(Hy:(R y))
  (((F x (prj1 X ??? Hx))[/]?[//](Ext2R x (prj2 X ??? Hx)))[#]
    ((F y (prj1 X ??? Hy))[/]?[//](Ext2R y (prj2 X ??? Hy))))->
      (x[#]y).
(* End_Tex_Verb *)
Intros x y Hx Hy H.
Elim (div_strong_ext ??????? H); Intro H1; Exact (pfstrx ?????? H1).
Qed.

(* Begin_Tex_Verb *)
Lemma part_function_div_pred_wd : (pred_well_def X R).
(* End_Tex_Verb *)
Red; Intros x y H H0.
Elim H; Intros H1 H2; Split.
 Apply (pfprwd X F x y H1 H0).
Clear H1.
Elim H2; Intros H1 H3; Split.
 Apply (pfprwd X G x y H1 H0).
Intro H4; Step (G x H1).
Qed.

(* Begin_Tex_Verb *)
Definition Fdiv := (Build_PartFunct X ? 
  part_function_div_pred_wd
  [x:X][Hx:(R x)]((F x (prj1 X ??? Hx))[/]?[//](Ext2R x (prj2 X ??? Hx)))
  part_function_div_strext).
(* End_Tex_Verb *)

(* Tex_Prose
\begin{notation}
\begin{itemize}
\item We denote \verb!(Frecip ? F)! by {\tt\hypertarget{Operator_20}{\{1/\}F}}.
\item We denote \verb!(Fdiv ? F G)! by {\tt\hypertarget{Operator_21}{F\{/\}G}}.
\end{itemize}
\end{notation}
*)

End Part_Function_Div.

End CField_Ops.

Implicits Frecip [1].
Distfix RIGHTA 1 "{1/} _" Frecip.

Implicits Fdiv [1].
Infix NONA 6 "{/}" Fdiv.
