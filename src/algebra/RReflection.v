(* $Id: RReflection.v,v 1.7 2003/03/13 12:06:16 lcf Exp $ *)

Require Export CRings.
Require Export EqNat.

(* Reflection for CRings *)

Section CRing_Reflection.

Definition Rvarindex : Set := nat.
Definition Rfunindex : Set := nat.

Inductive Rexpr : Set :=
   Rexpr_var  : Rvarindex->Rexpr
 | Rexpr_int  : Z->Rexpr
 | Rexpr_plus : Rexpr->Rexpr->Rexpr
 | Rexpr_mult : Rexpr->Rexpr->Rexpr
 | Rexpr_part : Rfunindex->Rexpr->Rexpr.


Definition Rexpr_zero : Rexpr := (Rexpr_int `0`).
Definition Rexpr_one : Rexpr := (Rexpr_int `1`).
Definition Rexpr_nat [n:nat] : Rexpr := (Rexpr_int (inject_nat n)).
Definition Rexpr_inv [e:Rexpr] : Rexpr := (Rexpr_mult (Rexpr_int `-1`) e).
Definition Rexpr_minus [e,e':Rexpr] : Rexpr := (Rexpr_plus e (Rexpr_inv e')).
Fixpoint Rexpr_power [n:nat] : Rexpr->Rexpr := [e:Rexpr]
  Cases n of
    O => Rexpr_one
  | (S m) => (Rexpr_mult e (Rexpr_power m e))
  end.

Variable F : CRing.
Variable val : Rvarindex->F.
Variable fun : Rfunindex->(PartFunct F).

Inductive Rinterp : Rexpr->F->Prop :=
   Rinterp_var : (i:Rvarindex)(z:F)((val i) [=] z)->
     (Rinterp (Rexpr_var i) z)
 | Rinterp_int : (k:Z)(z:F)((zring k) [=] z)->
     (Rinterp (Rexpr_int k) z)
 | Rinterp_plus : (e,f:Rexpr)(x,y,z:F)(x[+]y [=] z)->
     (Rinterp e x)->(Rinterp f y)->(Rinterp (Rexpr_plus e f) z)
 | Rinterp_mult : (e,f:Rexpr)(x,y,z:F)(x[*]y [=] z)->
     (Rinterp e x)->(Rinterp f y)->(Rinterp (Rexpr_mult e f) z)
 | Rinterp_part : (e:Rexpr)(f:Rfunindex)(x,z:F)(Hx:(Pred (fun f) x))(((fun f) x Hx)[=]z)->
     (Rinterp e x)->(Rinterp (Rexpr_part f e) z).

Definition Rwf [e:Rexpr] := (sig ? (Rinterp e)).

Inductive Rxexpr : F->Set :=
   Rxexpr_var   : (i:Rvarindex)(Rxexpr (val i))
 | Rxexpr_int   : (k:Z)(Rxexpr (zring k))
 | Rxexpr_plus  : (x,y:F)(e:(Rxexpr x))(f:(Rxexpr y))(Rxexpr x[+]y)
 | Rxexpr_mult  : (x,y:F)(e:(Rxexpr x))(f:(Rxexpr y))(Rxexpr x[*]y)
 | Rxexpr_part  : (x:F)(f:Rfunindex)(e:(Rxexpr x))(Hx:(Pred (fun f) x))(Rxexpr ((fun f) x Hx))
(* more things rrational translates: *)
 | Rxexpr_zero  : (Rxexpr Zero)
 | Rxexpr_one   : (Rxexpr One)
 | Rxexpr_nat   : (n:nat)(Rxexpr (nring n))
 | Rxexpr_inv   : (x:F)(e:(Rxexpr x))(Rxexpr [--]x)
 | Rxexpr_minus : (x,y:F)(e:(Rxexpr x))(f:(Rxexpr y))(Rxexpr x[-]y)
 | Rxexpr_power : (x:F)(e:(Rxexpr x))(n:nat)(Rxexpr x[^]n).

Fixpoint Rxforget [x:F; e:(Rxexpr x)] : Rexpr :=
  Cases e of
    (Rxexpr_var i) => (Rexpr_var i)
  | (Rxexpr_int k) => (Rexpr_int k)
  | (Rxexpr_plus _ _ e f) => (Rexpr_plus (Rxforget ? e) (Rxforget ? f))
  | (Rxexpr_mult _ _ e f) => (Rexpr_mult (Rxforget ? e) (Rxforget ? f))
  | (Rxexpr_part _ f e _) => (Rexpr_part f (Rxforget ? e))
  | (Rxexpr_zero) => (Rexpr_zero)
  | (Rxexpr_one) => (Rexpr_one)
  | (Rxexpr_nat n) => (Rexpr_nat n)
  | (Rxexpr_inv _ e) => (Rexpr_inv (Rxforget ? e))
  | (Rxexpr_minus _ _ e f) => (Rexpr_minus (Rxforget ? e) (Rxforget ? f))
  | (Rxexpr_power _ e n) => (Rexpr_power n (Rxforget ? e))
  end.

Definition Rxinterp := [x:F][e:(Rxexpr x)]x.

Lemma Rxexpr2interp : (x:F)(e:(Rxexpr x))(Rinterp (Rxforget ? e) x).
Intros x e.
Induction e.

Apply (Rinterp_var i); Algebra.

Apply (Rinterp_int k); Algebra.

Apply (Rinterp_plus (Rxforget ? e1) (Rxforget ? e0) x y x[+]y); Algebra.

Apply (Rinterp_mult (Rxforget ? e1) (Rxforget ? e0) x y x[*]y); Algebra.

EApply (Rinterp_part (Rxforget ? e) f x ((fun f) x Hx)).
 Apply eq_reflexive_unfolded.
Algebra.

Apply (Rinterp_int `0`); Algebra.

Apply (Rinterp_int `1`); Step_final (One::F).

Apply (Rinterp_int (inject_nat n)); Algebra.

Apply (Rinterp_mult (Rexpr_int `-1`) (Rxforget ? e) (zring `-1`) x [--]x); Algebra.
Apply (Rinterp_int `-1`); Algebra.

Apply (Rinterp_plus (Rxforget ? e1) (Rxforget ? (Rxexpr_inv ? e0)) x [--]y x[-]y); Algebra.
Apply (Rinterp_mult (Rexpr_int `-1`) (Rxforget ? e0) (zring `-1`) y [--]y); Algebra.
Apply (Rinterp_int `-1`); Algebra.

Induction n.
 Apply (Rinterp_int `1`); Step_final (One::F).
Apply (Rinterp_mult (Rxforget ? e) (Rexpr_power n (Rxforget ? e)) x x[^]n x[^](S n)); Algebra.
Qed.

Definition Rxexpr_diagram_commutes :
  (x:F)(e:(Rxexpr x))(Rinterp (Rxforget ? e) (Rxinterp ? e)) :=
  Rxexpr2interp.

Lemma Rxexpr2wf : (x:F)(e:(Rxexpr x))(Rwf (Rxforget ? e)).
Intros x e.
Exists x.
Apply Rxexpr2interp.
Qed.

Record Rfexpr : Set :=
  { Rfinterp : F;
    Rfexpr2xexpr : (Rxexpr Rfinterp)
  }.

Definition Rfexpr_var := [i:Rvarindex](Build_Rfexpr ? (Rxexpr_var i)).
Definition Rfexpr_int := [k:Z] (Build_Rfexpr ? (Rxexpr_int k)).
Definition Rfexpr_plus := [e,e':Rfexpr]
  (Build_Rfexpr ?
    (Rxexpr_plus (Rfinterp e) (Rfinterp e') (Rfexpr2xexpr e) (Rfexpr2xexpr e'))).
Definition Rfexpr_mult := [e,e':Rfexpr]
  (Build_Rfexpr ?
    (Rxexpr_mult (Rfinterp e) (Rfinterp e') (Rfexpr2xexpr e) (Rfexpr2xexpr e'))).

Definition Rfforget := [e:Rfexpr](Rxforget (Rfinterp e) (Rfexpr2xexpr e)).

Lemma Rfexpr2interp : (e:Rfexpr)(Rinterp (Rfforget e) (Rfinterp e)).
Intros e.
Elim e. Intros x e'.
Unfold Rfforget. Simpl.
Apply Rxexpr2interp.
Qed.

Lemma Rfexpr2wf : (e:Rfexpr)(Rwf (Rfforget e)).
Intro e.
Unfold Rfforget.
Apply Rxexpr2wf.
Qed.

Opaque csg_crr.
Opaque cm_crr.
Opaque cg_crr.
Opaque cr_crr.
Opaque csf_fun.
Opaque csbf_fun.
Opaque csr_rel.
Opaque cs_eq.
Opaque cs_neq.
Opaque cs_ap.
Opaque csg_unit.
Opaque csg_op.
Opaque cg_inv.
Opaque cg_minus.
Opaque cr_one.
Opaque cr_mult.
Opaque nexp_op.

Lemma refl_Rinterp : (e:Rexpr)(x,y:F)(Rinterp e x)->(Rinterp e y)->
			(x [=] y).
Intro e.
Induction e.

Intros x y Hx Hy.
Inversion Hx.
Inversion Hy.
Step_final (val r).

Intros x y Hx Hy.
Inversion Hx.
Inversion Hy.
Step_final ((zring z)::F).

Intros x y H1 H2.
Inversion H1.
Inversion H2.
Step x0[+]y0.
Step_final x1[+]y1.

Intros x y H1 H2.
Inversion H1.
Inversion H2.
Step x0[*]y0.
Step_final x1[*]y1.

Intros x y H0 H1.
Inversion H0.
Inversion H1.
Step ((fun r) x0 Hx); Stepr ((fun r) x1 Hx0).
Algebra.
Qed.

Lemma Rinterp_wd : (e:Rexpr)(x,y:F)(Rinterp e x)->(x [=] y)->(Rinterp e y).
Intros e x y H H0.
Inversion H.
Apply Rinterp_var. Step_final x.
Apply Rinterp_int. Step_final x.
Apply Rinterp_plus with x0 y0; Auto. Step_final x.
Apply Rinterp_mult with x0 y0; Auto. Step_final x.
Apply Rinterp_part with x0 Hx; Auto. Step_final x.
Qed.

(* To be fixed
Lemma Rexpr2Rfexpr_exists : (e:Rexpr)(Rwf e)->
  { f:Rfexpr &
    (toCProp ((Rfforget f) = e)) *
    ((x:F)(Rinterp e x)->((Rfinterp f) [=] x))}.
Intros.
Elim H. Intro. Intro H0.
Elim H0.
Intro. Intro. Intro H1.
Exists (Rfexpr_var i). Split. Auto. 
Intro.  Intro H2. Simpl. Inversion H2. Assumption.
Intro. Intro. Intro H1.
Exists (Rfexpr_int k). Split. Auto.
Intro.  Intro H2. Inversion H2. Assumption.
Do 5 Intro. Intros H1 H2 H3 H4 H5.
Elim H3. Elim H5. Intro. Intro H6. Intro. Intro H7.
Elim H6. Elim H7. Intros H8 H9 H10 H11.
Apply (Set_toCProp_e ? H8); Clear H8; Intro H8.
Apply (Set_toCProp_e ? H10); Clear H10; Intro H10.
Exists (Rfexpr_plus x2 x1). Split.
Apply toCProp_i. Rewrite <- H8. Rewrite <- H10. Auto.
Intros.
Apply refl_Rinterp with (Rexpr_plus e0 f).
Apply Rinterp_plus with x0 y.
Simpl; Algebra .
Assumption. Assumption. Assumption.
Do 5 Intro. Intros H1 H2 H3 H4 H5.
Elim H3. Elim H5. Intro. Intro H6. Intro. Intro H7.
Elim H6. Elim H7. Intros H8 H9 H10 H11.
Apply (Set_toCProp_e ? H8); Clear H8; Intro H8.
Apply (Set_toCProp_e ? H10); Clear H10; Intro H10.
Exists (Rfexpr_mult x2 x1). Split.
Rewrite <- H8. Rewrite <- H10. Auto.
Intros.
Apply refl_Rinterp with (Rexpr_mult e0 f).
Apply Rinterp_mult with x0 y.
Simpl; Algebra .
Assumption. Assumption. Assumption.
Qed.
*)

(*
Ax_iom Rexpr2Rfexpr : (e:Rexpr)(Rwf e)->Rfexpr.

Ax_iom Rexpr2Rfexpr_compat : (e:Rexpr)(H:(Rwf e))
  (Rfforget (Rexpr2Rfexpr e H)) = e.

Ax_iom Rexpr2Rfexpr_corr : (e:Rexpr)(H:(Rwf e))(x:F)(Rinterp e x)->
  (Rfinterp (Rexpr2Rfexpr e H)) [=] x.
*)

End CRing_Reflection.


