(* $Id: Reflection.v,v 1.7 2003/03/13 12:06:16 lcf Exp $ *)

Require Export CFields.

Section New_Reflection.

Variable F:CField.

Definition varindex : Set := nat.
Definition funindex : Set := nat.

Inductive expr : Set :=
   expr_var  : varindex->expr
 | expr_int  : Z->expr
 | expr_plus : expr->expr->expr
 | expr_mult : expr->expr->expr
 | expr_div  : expr->expr->expr
 | expr_part : funindex->expr->expr.

Definition expr_zero : expr := (expr_int `0`).
Definition expr_one : expr := (expr_int `1`).
Definition expr_nat [n:nat] : expr := (expr_int (inject_nat n)).
Definition expr_inv [e:expr] : expr := (expr_mult (expr_int `-1`) e).
Definition expr_minus [e,e':expr] : expr := (expr_plus e (expr_inv e')).
Fixpoint expr_power [n:nat] : expr->expr := [e:expr]
  Cases n of
    O => expr_one
  | (S m) => (expr_mult e (expr_power m e))
  end.

Variable val : varindex->F.
Variable fun : funindex->(PartFunct F).

Inductive interp : expr->F->CProp :=
   interp_var : (i:varindex)(z:F)((val i) [=] z)->
     (interp (expr_var i) z)
 | interp_int : (k:Z)(z:F)((zring k) [=] z)->
     (interp (expr_int k) z)
 | interp_plus : (e,f:expr)(x,y,z:F)(x[+]y [=] z)->
     (interp e x)->(interp f y)->(interp (expr_plus e f) z)
 | interp_mult : (e,f:expr)(x,y,z:F)(x[*]y [=] z)->
     (interp e x)->(interp f y)->(interp (expr_mult e f) z)
 | interp_div : (e,f:expr)(x,y,z:F)(nzy:(y [#] Zero))(x[/]y[//]nzy [=] z)->
     (interp e x)->(interp f y)->(interp (expr_div e f) z)
 | interp_part : (e:expr)(f:funindex)(x,z:F)(Hx:(Pred (fun f) x))(((fun f)  x Hx)[=]z)->
     (interp e x)->(interp (expr_part f e) z).

Definition wf [e:expr] := (sigS ? (interp e)).

Inductive xexpr : F->Set :=
   xexpr_var   : (i:varindex)(xexpr (val i))
 | xexpr_int   : (k:Z)(xexpr (zring k))
 | xexpr_plus  : (x,y:F)(e:(xexpr x))(f:(xexpr y))(xexpr x[+]y)
 | xexpr_mult  : (x,y:F)(e:(xexpr x))(f:(xexpr y))(xexpr x[*]y)
 | xexpr_div   : (x,y:F)(e:(xexpr x))(f:(xexpr y))
                       (nzy:(y [#] Zero))(xexpr x[/]y[//]nzy)
 | xexpr_part  : (x:F)(f:funindex)(e:(xexpr x))(Hx:(Pred (fun f) x))(xexpr ((fun f) x Hx))
 | xexpr_zero  : (xexpr Zero)
 | xexpr_one   : (xexpr One)
 | xexpr_nat   : (n:nat)(xexpr (nring n))
 | xexpr_inv   : (x:F)(e:(xexpr x))(xexpr [--]x)
 | xexpr_minus : (x,y:F)(e:(xexpr x))(f:(xexpr y))(xexpr x[-]y)
 | xexpr_power : (x:F)(e:(xexpr x))(n:nat)(xexpr x[^]n).

Fixpoint xforget [x:F; e:(xexpr x)] : expr :=
  Cases e of
    (xexpr_var i) => (expr_var i)
  | (xexpr_int k) => (expr_int k)
  | (xexpr_plus _ _ e f) => (expr_plus (xforget ? e) (xforget ? f))
  | (xexpr_mult _ _ e f) => (expr_mult (xforget ? e) (xforget ? f))
  | (xexpr_div _ _ e f _) => (expr_div (xforget ? e) (xforget ? f))
  | (xexpr_part _ f e _) => (expr_part f (xforget ? e))
  | (xexpr_zero) => (expr_zero)
  | (xexpr_one) => (expr_one)
  | (xexpr_nat n) => (expr_nat n)
  | (xexpr_inv _ e) => (expr_inv (xforget ? e))
  | (xexpr_minus _ _ e f) => (expr_minus (xforget ? e) (xforget ? f))
  | (xexpr_power _ e n) => (expr_power n (xforget ? e))
  end.

Definition xinterp := [x:F][e:(xexpr x)]x.

Lemma xexpr2interp : (x:F)(e:(xexpr x))(interp (xforget ? e) x).
Intros.
Elim e; Intros.
Apply (interp_var i); Algebra.
Apply (interp_int k); Algebra.
Apply (interp_plus (xforget ? e0) (xforget ? f) x0 y x0[+]y); Algebra.
Apply (interp_mult (xforget ? e0) (xforget ? f) x0 y x0[*]y); Algebra.
Apply (interp_div (xforget ? e0) (xforget ? f) x0 y x0[/]y[//]nzy nzy);
  Algebra.
EApply (interp_part (xforget ? e0) f x0 ((fun f)  x0 Hx)).
Apply eq_reflexive_unfolded.
Algebra.
Apply (interp_int `0`); Algebra.
Apply (interp_int `1`); Step_final (One::F).
Apply (interp_int (inject_nat n)); Algebra.
Apply (interp_mult (expr_int `-1`) (xforget ? e0) (zring `-1`) x0 [--]x0);
  Algebra.
Apply (interp_int `-1`); Algebra.
Apply (interp_plus (xforget ? e0) (xforget ? (xexpr_inv ? f)) x0 [--]y x0[-]y);
  Algebra.
Apply (interp_mult (expr_int `-1`) (xforget ? f) (zring `-1`) y [--]y);
  Algebra.
Apply (interp_int `-1`); Algebra.
Elim n.
Apply (interp_int `1`); Step_final (One::F).
Intros.
Apply (interp_mult (xforget ? e0) (expr_power n0 (xforget ? e0))
  x0 x0[^]n0 x0[^](S n0)); Auto.
Step_final x0[^]n0[*]x0.
Qed.

Definition xexpr_diagram_commutes :
  (x:F)(e:(xexpr x))(interp (xforget ? e) (xinterp ? e)) :=
  xexpr2interp.

Lemma xexpr2wf : (x:F)(e:(xexpr x))(wf (xforget ? e)).
Intros.
Unfold wf.
Exists x.
Apply xexpr2interp.
Qed.

Load Opaque_algebra.

Lemma refl_interp : (e:expr)(x,y:F)(interp e x)->(interp e y)->
			(x [=] y).
Intro e.
Elim e.

Intros v x y Hx Hy.
Inversion Hx.
Inversion Hy.
Step_final (val v).

Intros k x y Hx Hy.
Inversion Hx.
Inversion Hy.
Step_final (!zring F k).

Intros e0 H e1 H0 x y H1 H2.
Inversion H1.
Inversion H2.
Step x0[+]y0; Step_final x1[+]y1.

Intros e0 H e1 H0 x y H1 H2.
Inversion H1.
Inversion H2.
Step x0[*]y0; Step_final x1[*]y1.

Intros.
Inversion H1.
Inversion H2.
Step x0[/]y0[//]nzy; Step_final x1[/]y1[//]nzy0.

Intros.
Inversion H0.
Inversion H1.
Step ((fun f) x0 Hx); Stepr ((fun f) x1 Hx0).
Apply pfwdef; Algebra.
Qed.

Lemma interp_wd : (e:expr)(x,y:F)(interp e x)->(x [=] y)->(interp e y).
Intros.
Inversion H.
Apply interp_var. Step_final x.
Apply interp_int. Step_final x.
Apply interp_plus with x0 y0; Auto. Step_final x.
Apply interp_mult with x0 y0; Auto. Step_final x.
Apply interp_div with x0 y0 nzy; Auto. Step_final x.
Apply interp_part with x0 Hx; Auto. Step_final x.
Qed.

End New_Reflection.
