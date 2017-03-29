(* $Id: Refl_corr.v,v 1.4 2003/03/11 13:35:55 lcf Exp $ *)

Require Export Reflection.

Load Opaque_algebra.

Section NormCorrect.

Variable F : CField.
Variable val : varindex->F.
Variable fun : funindex->(PartFunct F).

Syntactic Definition II := (interp F val fun).

Fixpoint MI_mult [e:expr] : expr->expr := [f:expr]
let d = (expr_mult e f) in
  Cases e f of
    e (expr_int ZERO) => (expr_int ZERO)
  | (expr_mult e1 e2) f => (expr_mult e1 (MI_mult e2 f))
  | (expr_int i) (expr_int j) => (expr_int (Zmult i j))
  | _ _ => d
  end.

Opaque Zmult.
Lemma MI_mult_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (MI_mult e f) x[*]y).
Cut (x,y:F)
     (II (expr_int ZERO) y)->(II (expr_int ZERO) x[*]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (MI_mult e2 f) x[*]y))
     ->(II (expr_mult e1 e2) x)
     ->(II f y)
     ->(II (expr_mult e1 (MI_mult e2 f)) x[*]y).
Cut (i,j:Z; x,y:F)
     (II (expr_int i) x)
     ->(II (expr_int j) y)
     ->(II (expr_int (Zmult i j)) x[*]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Induction e; Induction f; Simpl; Auto.
Induction z; Simpl; Auto.
Induction z0; Induction z; Simpl; Auto.
Induction z; Simpl; Auto.
Induction z; Simpl; Auto.
Induction z; Simpl; Auto.
Induction f0; Simpl; Auto.
Induction z; Simpl; Auto.
Induction f; Simpl; Auto.
Induction f; Simpl; Auto.
Induction z; Simpl; Auto.
Intros; Apply interp_mult with x y; Algebra.
Intros; Apply interp_wd with ((zring (Zmult i j))::F).
Apply interp_int; Algebra.
Inversion H. Inversion H0.
Step_final ((zring i)[*](zring j)::F).
Intros. Inversion H0.
Apply interp_wd with x0[*](y0[*]y); Algebra .
Apply interp_mult with x0 y0[*]y; Algebra.
Step (x0[*]y0)[*]y; Algebra.
Intros. Inversion H.
Apply interp_wd with ((zring `0`)::F).
Apply interp_int; Algebra .
Step (Zero::F).
Step x[*]Zero.
Step_final x[*](zring `0`).
Qed.
Transparent Zmult.

Fixpoint eq_expr [e:expr] : expr -> bool := [f:expr]
  Cases e f of
    (expr_var n) (expr_var m) => (eq_nat n m)
  | (expr_int z) (expr_int z') => (eq_int z z')
  | (expr_plus e1 e2) (expr_plus f1 f2) => (andb (eq_expr e1 f1) (eq_expr e2 f2))
  | (expr_mult e1 e2) (expr_mult f1 f2) => (andb (eq_expr e1 f1) (eq_expr e2 f2))
  | (expr_div e1 e2) (expr_div f1 f2) => (andb (eq_expr e1 f1) (eq_expr e2 f2))
  | (expr_part n e') (expr_part m f') => (andb (eq_nat n m) (eq_expr e' f'))
  | _ _ => false
  end.

Fixpoint lt_expr [e:expr] : expr -> bool := [f:expr]
  Cases e f of
    (expr_var n) (expr_var m) => (lt_nat n m)
  | (expr_var n) _ => true
  | _ (expr_var n) => false

  | (expr_int z) (expr_int z') => (lt_int z z')
  | (expr_int _) _ => true
  | _ (expr_int _) => false

  | (expr_plus e1 e2) (expr_plus f1 f2) => (orb (lt_expr e1 f1) (andb (eq_expr e1 f1) (lt_expr e2 f2)))
  | (expr_plus _ _) _ => true
  | _ (expr_plus _ _) => false

  | (expr_mult e1 e2) (expr_mult f1 f2) => (orb (lt_expr e1 f1) (andb (eq_expr e1 f1) (lt_expr e2 f2)))
  | (expr_mult _ _) _ => true
  | _ (expr_mult _ _) => false

  | (expr_div e1 e2) (expr_div f1 f2) => (orb (lt_expr e1 f1) (andb (eq_expr e1 f1) (lt_expr e2 f2)))
  | (expr_div _ _) _ => true
  | _ (expr_div _ _) => false

  | (expr_part n e') (expr_part m f') => (orb (lt_nat n m) (andb (eq_nat n m) (lt_expr e' f')))
  end.

Definition le_expr [e,f:expr] := (orb (eq_expr e f) (lt_expr e f)).

Lemma eq_nat_corr : (n,m:nat)((eq_nat n m)=true)->(n=m).
Induction n; Induction m; Simpl; Intros.
Trivial.
Inversion H0.
Inversion H0.
Rewrite (H n1 H1). Trivial.
Qed.

Lemma eq_int_corr : (n,m:Z)((eq_int n m)=true)->(n=m).
Induction n; Induction m; Simpl; Intros.
Trivial.
Inversion H.
Inversion H.
Inversion H.
Rewrite <- (convert_is_POS p). Rewrite <- (convert_is_POS p0). 
Cut (convert p)=(convert p0). Auto. Apply eq_nat_corr. Assumption.
Inversion H.
Inversion H.
Inversion H.
Cut p=p0; Intros.
Rewrite H0; Auto.
Rewrite (anti_convert_pred_convert p). Rewrite (anti_convert_pred_convert p0).
Cut (convert p)=(convert p0). Intro. Auto. Apply eq_nat_corr. Assumption.
Qed.

Lemma eq_expr_corr : (e,e':expr)((eq_expr e e')=true)->(e=e').
Induction e; Induction e'; Simpl; Intros; Try Inversion H3; Try Inversion H2; Try Inversion H1; Try Inversion H0; Try Inversion H.
Cut v=v0. Intro. Rewrite H0; Auto. Apply eq_nat_corr; Assumption. 
Cut z=z0. Intro. Rewrite H0; Auto. Apply eq_int_corr; Assumption. 
Clear H1 H2. Elim (andb_prop ?? H3); Intros. 
Cut e0=e2. Cut e1=e3. Intros. Rewrite H4; Rewrite H6. Auto. 
Apply H0. Assumption. Apply H. Assumption.
Clear H1 H2. Elim (andb_prop ?? H3); Intros. 
Cut e0=e2. Cut e1=e3. Intros. Rewrite H4; Rewrite H6. Auto. 
Apply H0. Assumption. Apply H. Assumption.
Clear H1 H2. Elim (andb_prop ?? H3); Intros. 
Cut e0=e2. Cut e1=e3. Intros. Rewrite H4; Rewrite H6. Auto. 
Apply H0. Assumption. Apply H. Assumption.
Clear H0. Elim (andb_prop ?? H1); Intros. 
Cut f=f0. Cut e0=e1. Intros. Rewrite H4. Rewrite H5. Auto. 
Apply H. Assumption. Apply eq_nat_corr. Assumption. 
Qed.

Fixpoint MV_mult [e:expr] : expr->expr := [f:expr]
let d = (expr_mult e f) in
  Cases e f of
    (expr_mult (expr_var n) e') (expr_var m) =>
      Cases (lt_nat n m) of
        true => (expr_mult (expr_var n) (MV_mult e' f))
      | false => (expr_mult f e)
      end
  | (expr_mult (expr_var n) e') (expr_part _ _) =>
      (expr_mult (expr_var n) (MV_mult e' f))
  | (expr_mult (expr_part _ _) e') (expr_var _) =>
      (expr_mult f e)
  | (expr_mult (expr_part n e') e0) (expr_part m f') =>
      Cases (lt_expr (expr_part n e') f) of
        true => (expr_mult (expr_part n e') (MV_mult e0 f))
      | false => (expr_mult f e)
      end
  | (expr_int i) f => (MI_mult (expr_mult f expr_one) e)
  | _ _ => d
  end.

Opaque MI_mult.
Lemma MV_mult_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (MV_mult e f) x[*]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (MV_mult e2 f) x[*]y))
     ->(II (expr_mult e1 e2) x)
     ->(II f y)
     ->(II (expr_mult e1 (MV_mult e2 f)) x[*]y).
Cut (e,f:expr; x,y:F)
     (II e x)->(II f y)->(II (MI_mult (expr_mult f expr_one) e) x[*]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_mult f e) x[*]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Intros H H0 H1 H2 e. Elim e.
Simpl; Auto.
Simpl; Auto.
Intros e1 H3 e2 H4.
Elim e1; Simpl; Auto.
Intros e1 H3 e2 H4.
Elim e1; Simpl; Auto.
Intros n f.
Elim f; Simpl; Auto.
Intro m.
Elim (lt_nat n m); Simpl; Auto.
Intros n f.
Intros H5 f0.
Elim f0; Simpl; Auto.
Intros f1 e0 H6.
Elim (orb (lt_nat n f1) (andb (eq_nat n f1) (lt_expr f e0))); Simpl; Auto.
Intros e1 H3 e2 H4.
Elim e1; Simpl; Auto.
Intros n f.
Elim f; Simpl; Auto.
Intros; Apply interp_mult with x y; Algebra.
Intros; Apply interp_wd with y[*]x; Algebra.
Apply interp_mult with y x; Algebra.
Intros; Apply interp_wd with (y[*]One)[*]x.
Apply MI_mult_corr; Auto.
Apply interp_mult with y (One::F); Algebra .
Unfold expr_one.
Apply interp_int; Algebra .
Step_final x[*](y[*]One).
Intros. Inversion H0.
Apply interp_wd with x0[*](y0[*]y).
Apply interp_mult with x0 y0[*]y; Algebra.
Step_final (x0[*]y0)[*]y.
Qed.
Transparent MI_mult.

Fixpoint MM_mult [e:expr] : expr->expr := [f:expr]
let d = (expr_mult e f) in
  Cases e f of
    (expr_mult e1 e2) f => (MV_mult (MM_mult e2 f) e1)
  | (expr_int i) f => (MI_mult f e)
  | _ _ => d
  end.

Opaque MV_mult MI_mult.
Lemma MM_mult_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (MM_mult e f) x[*]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (MM_mult e2 f) x[*]y))
     ->(II (expr_mult e1 e2) x)
     ->(II f y)
     ->(II (MV_mult (MM_mult e2 f) e1) x[*]y).
Cut (i:Z; f:expr; x,y:F)
     (II (expr_int i) x)->(II f y)->(II (MI_mult f (expr_int i)) x[*]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros; Apply interp_mult with x y; Algebra.
Intros; Apply interp_wd with y[*]x; Algebra.
Apply MI_mult_corr; Auto.
Intros. Inversion H0.
Apply interp_wd with (y0[*]y)[*]x0.
Apply MV_mult_corr; Auto.
Step x0[*](y0[*]y).
Step_final (x0[*]y0)[*]y.
Qed.
Transparent MV_mult MI_mult.

Fixpoint MM_plus [e:expr] : expr->expr := [f:expr]
let d = (expr_plus e f) in
  Cases e f of
    (expr_mult (expr_var n) e') (expr_mult (expr_var m) f') =>
      Cases (eq_nat n m) of
        true => (MV_mult (MM_plus e' f') (expr_var n))
      | false => d
      end
  | (expr_mult (expr_part g arg) e') (expr_mult (expr_part h arg') f') =>
      Cases (andb (eq_nat g h) (eq_expr arg arg')) of
        true => (MV_mult (MM_plus e' f') (expr_part g arg))
      | false => d
      end
  | (expr_int i) (expr_int j) => (expr_int (Zplus i j))
  | _ _ => d
  end.

Opaque MV_mult.
Lemma MM_plus_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (MM_plus e f) x[+]y).
Cut (i,j:Z; x,y:F)
     (II (expr_int i) x)
     ->(II (expr_int j) y)
     ->(II (expr_int (Zplus i j)) x[+]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_plus e f) x[+]y).
Intros H H0 e; Elim e.
Simpl; Auto.
Intros z f; Elim f; Simpl; Auto.
Simpl; Auto.
Intros e1 H1 e2 H2.
Elim e1; Simpl; Auto.
Intros n f.
Elim f; Simpl; Auto.
Intros f1 H3 f2 H4.
Elim f1; Simpl; Auto.
Intro m.
Cut (eq_nat n m)=true->n=m.
Elim (eq_nat n m); Simpl; Auto.
Intros. Inversion H6. Inversion H7.
Apply interp_wd with (y0[+]y1)[*]x0.
Apply MV_mult_corr; Auto.
Step x0[*](y0[+]y1).
Step x0[*]y0[+]x0[*]y1.
Cut x0[=]x1. Intro.
Step_final x0[*]y0[+]x1[*]y1.
Apply refl_interp with val fun (expr_var n).
Assumption.
Rewrite (H5 (refl_equal ? true)). Assumption.
Intros; Apply eq_nat_corr; Auto.
Intros f e0 H3.
Intro f0.
Elim f0; Simpl; Auto.
Intros e3 H4 e4 H5.
Elim e3; Simpl; Auto.
Intros f1 e5 H6.
Cut (andb (eq_nat f f1) (eq_expr e0 e5))=true->(f=f1).
Cut (andb (eq_nat f f1) (eq_expr e0 e5))=true->e0=e5.
Elim (andb (eq_nat f f1) (eq_expr e0 e5)); Simpl; Auto.
Intros. Inversion H9. Inversion H10. Apply interp_wd with (y0[+]y1)[*]x0.
Apply MV_mult_corr; Auto.
Stepr (x0[*]y0)[+](x1[*]y1). Step (y0[*]x0)[+](y1[*]x0).
Apply bin_op_wd_unfolded. Algebra. Stepr y1[*]x1. Apply mult_wd_rht.
Clear H6 H5 H4 H3 H2 H1.
Clear H9 H10.
Apply refl_interp with val fun (expr_part f e0).
Auto. Rewrite H7; Auto. Rewrite H8; Auto. 
Intro. Elim (andb_prop ?? H7); Intros. Apply eq_expr_corr; Auto. 
Intro. Elim (andb_prop ?? H7); Intros. Apply eq_nat_corr; Auto.
Simpl; Auto.
Simpl; Auto.
Intros; Apply interp_plus with x y; Algebra.
Intros. Inversion H. Inversion H0.
Apply interp_wd with ((zring `i+j`)::F).
Apply interp_int; Algebra.
Step_final ((zring i)[+](zring j)::F).
Qed.
Transparent MV_mult.

Fixpoint eq_monom [e:expr] : expr->bool := [f:expr]
  Cases e f of
    (expr_mult (expr_var n) e') (expr_mult (expr_var m) f') =>
      (andb (eq_nat n m) (eq_monom e' f'))
  | (expr_mult (expr_part n e1) e') (expr_mult (expr_part m f1) f') =>
      (andb (eq_nat n m) (andb (eq_monom e' f') (eq_expr e1 f1)))
  | (expr_int _) (expr_int _) => true
  | _ _ => false
  end.

Fixpoint lt_monom [e:expr] : expr->bool := [f:expr]
  Cases e f of
    (expr_mult (expr_var n) e') (expr_mult (expr_var m) f') =>
      (ifb (eq_nat n m) (lt_monom e' f') (lt_nat n m))
  | (expr_mult (expr_var _) _) (expr_mult (expr_part _ _) _) => true
  | (expr_mult (expr_part n e1) e') (expr_mult (expr_part m f1) f') =>
      (ifb (eq_expr (expr_part n e1) (expr_part m f1)) (lt_expr e' f') (lt_expr (expr_part n e1) (expr_part m f1)))
  | _ (expr_int _) => true
  | _ _ => false
  end.

Fixpoint PM_plus [e:expr] : expr->expr := [f:expr]
let d = (expr_plus e f) in
  Cases e f of
    (expr_plus e1 e2) (expr_int _) => (expr_plus e1 (PM_plus e2 f))
  | (expr_int i) (expr_int j) => (MM_plus e f)
  | (expr_plus e1 e2) f =>
      Cases (eq_monom e1 f) of
        true => (PM_plus e2 (MM_plus e1 f))
      | false => 
          Cases (lt_monom e1 f) of
            true => (expr_plus e1 (PM_plus e2 f))
          | false => (expr_plus f e)
          end
      end
  | (expr_int i) f => (expr_plus f e)
  | _ _ => d
  end.

Opaque MM_plus.
Lemma PM_plus_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (PM_plus e f) x[+]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (PM_plus e2 f) x[+]y))
     ->(II (expr_plus e1 e2) x)
     ->(II f y)
     ->(II (expr_plus e1 (PM_plus e2 f)) x[+]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (PM_plus e2 f) x[+]y))
     ->(II (expr_plus e1 e2) x)
     ->(II f y)
     ->(II (PM_plus e2 (MM_plus e1 f)) x[+]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (MM_plus e f) x[+]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_plus e f) x[+]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_plus f e) x[+]y).
Intros H H0 H1 H2 H3 e. Elim e.
Simpl; Auto.
Intros z f; Elim f; Intros; Simpl; Auto.
Intros e1 H4 e2 H5 f. Simpl.
Elim (lt_monom e1 f); Elim (eq_monom e1 f); Elim f; Intros; Simpl; Auto.
Simpl; Auto.
Simpl; Auto.
Simpl; Auto.
Intros; Apply interp_wd with y[+]x; Algebra.
Apply interp_plus with y x; Algebra.
Intros; Apply interp_plus with x y; Algebra.
Intros; Apply MM_plus_corr; Auto.
Intros. Inversion H0.
Apply interp_wd with y0[+](x0[+]y).
Apply H; Auto.
Apply MM_plus_corr; Auto.
Step (y0[+]x0)[+]y.
Step_final (x0[+]y0)[+]y.
Intros. Inversion H0.
Apply interp_wd with x0[+](y0[+]y).
Apply interp_plus with x0 y0[+]y; Algebra .
Step_final (x0[+]y0)[+]y.
Qed.
Transparent MM_plus.

Fixpoint PP_plus [e:expr] : expr->expr := [f:expr]
let d = (expr_plus e f) in
  Cases e f of
    (expr_plus e1 e2) f => (PM_plus (PP_plus e2 f) e1)
  | (expr_int i) f => (PM_plus f e)
  | _ _ => d
  end.

Opaque PM_plus.
Lemma PP_plus_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (PP_plus e f) x[+]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (PP_plus e2 f) x[+]y))
     ->(II (expr_plus e1 e2) x)
     ->(II f y)
     ->(II (PM_plus (PP_plus e2 f) e1) x[+]y).
Cut (i:Z; f:expr; x,y:F)
     (II (expr_int i) x)->(II f y)->(II (PM_plus f (expr_int i)) x[+]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_plus e f) x[+]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros. Apply interp_plus with x y; Algebra.
Intros. Apply interp_wd with y[+]x; Algebra.
Apply PM_plus_corr; Auto.
Intros. Inversion H0.
Apply interp_wd with (y0[+]y)[+]x0.
Apply PM_plus_corr; Auto.
Step x0[+](y0[+]y).
Step_final (x0[+]y0)[+]y.
Qed.
Transparent PM_plus.

Fixpoint PM_mult [e:expr] : expr->expr := [f:expr]
let d = (expr_mult e f) in
  Cases e f of
    (expr_plus e1 e2) f => (PM_plus (PM_mult e2 f) (MM_mult e1 f))
  | (expr_int i) _ => (PM_plus (expr_int ZERO) (MI_mult f e))
  | _ _ => d
  end.

Opaque PM_plus MM_mult MI_mult.
Lemma PM_mult_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (PM_mult e f) x[*]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (PM_mult e2 f) x[*]y))
     ->(II (expr_plus e1 e2) x)
     ->(II f y)
     ->(II (PM_plus (PM_mult e2 f) (MM_mult e1 f)) x[*]y).
Cut (i:Z; f:expr; x,y:F)
     (II (expr_int i) x)
     ->(II f y)
     ->(II (PM_plus (expr_int ZERO) (MI_mult f (expr_int i))) x[*]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros. Apply interp_mult with x y; Algebra.
Intros. Apply interp_wd with (zring `0`)[+](y[*]x).
Apply PM_plus_corr.
Apply interp_int; Algebra .
Apply MI_mult_corr; Auto.
Step Zero[+]y[*]x.
Step_final y[*]x.
Intros. Inversion H0.
Apply interp_wd with y0[*]y[+]x0[*]y.
Apply PM_plus_corr; Auto.
Apply MM_mult_corr; Auto.
Step (y0[+]x0)[*]y.
Step_final (x0[+]y0)[*]y.
Qed.
Transparent PM_plus MM_mult MI_mult.

Fixpoint PP_mult [e:expr] : expr->expr := [f:expr]
let d = (expr_mult e f) in
  Cases e f of
    (expr_plus e1 e2) f => (PP_plus (PM_mult f e1) (PP_mult e2 f))
  | (expr_int i) f => (PM_mult f e)
  | _ _ => d
  end.

Opaque PP_plus PM_mult.
Lemma PP_mult_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (PP_mult e f) x[*]y).
Cut (e1,e2,f:expr; x,y:F)
     ((f:expr; x,y:F)(II e2 x)->(II f y)->(II (PP_mult e2 f) x[*]y))
     ->(II (expr_plus e1 e2) x)
     ->(II f y)
     ->(II (PP_plus (PM_mult f e1) (PP_mult e2 f)) x[*]y).
Cut (i:Z; f:expr; x,y:F)
     (II (expr_int i) x)->(II f y)->(II (PM_mult f (expr_int i)) x[*]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros. Apply interp_mult with x y; Algebra.
Intros. Apply interp_wd with y[*]x; Algebra.
Apply PM_mult_corr; Auto.
Intros. Inversion H0.
Apply interp_wd with y[*]x0[+]y0[*]y.
Apply PP_plus_corr; Auto.
Apply PM_mult_corr; Auto.
Step x0[*]y[+]y0[*]y.
Step_final (x0[+]y0)[*]y.
Qed.
Transparent PP_plus PM_mult.

Definition FF_plus [e:expr] : expr->expr := [f:expr]
let d = (expr_plus e f) in
  Cases e f of
    (expr_div e1 e2) (expr_div f1 f2) =>
      (expr_div (PP_plus (PP_mult e1 f2) (PP_mult e2 f1)) (PP_mult e2 f2))
  | _ _ => d
  end.

Lemma FF_plus_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (FF_plus e f) x[+]y).
Cut (e1,e2,f1,f2:expr; x,y:F)
     (II (expr_div e1 e2) x)
     ->(II (expr_div f1 f2) y)
     ->(II
         (expr_div (PP_plus (PP_mult e1 f2) (PP_mult e2 f1))
           (PP_mult e2 f2)) x[+]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_plus e f) x[+]y).
Intros H H0 e f.
Elim e; Elim f; Intros; Simpl; Auto.
Intros. Apply interp_plus with x y; Algebra.
Intros. Inversion H. Inversion H0.
Cut y0[*]y1[#]Zero. Intro.
Apply interp_div with x0[*]y1[+]y0[*]x1 y0[*]y1 H13; Auto.
Step (x0[*]y1)[/](y0[*]y1)[//]H13[+](y0[*]x1)[/](y0[*]y1)[//]H13.
Step
  (x0[/]y0[//]nzy)[*](y1[/]y1[//]nzy0)[+](y0[/]y0[//]nzy)[*](x1[/]y1[//]nzy0).
Step (x0[/]y0[//]nzy)[*]One[+]One[*](x1[/]y1[//]nzy0).
Step_final x0[/]y0[//]nzy[+]x1[/]y1[//]nzy0.
Apply PP_plus_corr; Auto.
Apply PP_mult_corr; Auto.
Apply PP_mult_corr; Auto.
Apply PP_mult_corr; Auto.
Apply mult_resp_ap_zero; Auto.
Qed.

Definition FF_mult [e:expr] : expr->expr := [f:expr]
let d = (expr_mult e f) in
  Cases e f of
    (expr_div e1 e2) (expr_div f1 f2) =>
      (expr_div (PP_mult e1 f1) (PP_mult e2 f2))
  | _ _ => d
  end.

Lemma FF_mult_corr : (e,f:expr; x,y:F)
  (II e x)->(II f y)->(II (FF_mult e f) x[*]y).
Cut (e1,e2,f1,f2:expr; x,y:F)
     (II (expr_div e1 e2) x)
     ->(II (expr_div f1 f2) y)
     ->(II (expr_div (PP_mult e1 f1) (PP_mult e2 f2)) x[*]y).
Cut (e,f:expr; x,y:F)(II e x)->(II f y)->(II (expr_mult e f) x[*]y).
Intros H H0 e f.
Elim e; Elim f; Intros; Simpl; Auto.
Intros. Apply interp_mult with x y; Algebra.
Intros. Inversion H. Inversion H0.
Cut y0[*]y1[#]Zero. Intro.
Apply interp_div with x0[*]x1 y0[*]y1 H13.
Step_final (x0[/]y0[//]nzy)[*](x1[/]y1[//]nzy0).
Apply PP_mult_corr; Auto.
Apply PP_mult_corr; Auto.
Apply mult_resp_ap_zero; Auto.
Qed.

Definition FF_div [e:expr] : expr->expr := [f:expr]
let d = (expr_div e f) in
  Cases e f of
    (expr_div e1 e2) (expr_div f1 f2) =>
      (expr_div (PP_mult e1 f2) (PP_mult e2 f1))
  | _ _ => d
  end.

Lemma FF_div_corr : (e,f:expr; x,y:F; nzy:y[#]Zero)
  (II e x)->(II f y)->(II (FF_div e f) x[/]y[//]nzy).
Cut (e1,e2,f1,f2:expr; x,y:F; nzy:(y[#]Zero))
     (II (expr_div e1 e2) x)
     ->(II (expr_div f1 f2) y)
     ->(II (expr_div (PP_mult e1 f2) (PP_mult e2 f1)) x[/]y[//]nzy).
Cut (e,f:expr; x,y:F; nzy:(y[#]Zero))
     (II e x)->(II f y)->(II (expr_div e f) x[/]y[//]nzy).
Intros H H0 e f.
Elim e; Elim f; Intros; Simpl; Auto.
Intros. Apply interp_div with x y nzy; Algebra.
Intros. Inversion H. Inversion H0.
Cut x1[#]Zero. Intro nzx1.
Cut y0[*]x1[#]Zero. Intro.
Cut x1[/]y1[//]nzy1[#]Zero. Intro.
Apply interp_div with x0[*]y1 y0[*]x1 H13.
Step (y1[*]x0)[/](y0[*]x1)[//]H13.
Step ((y1[*]x0)[/]y0[//]nzy0)[/]x1[//]nzx1.
Step (y1[*](x0[/]y0[//]nzy0))[/]x1[//]nzx1.
Step ((x0[/]y0[//]nzy0)[*]y1)[/]x1[//]nzx1.
Step_final (x0[/]y0[//]nzy0)[/](x1[/]y1[//]nzy1)[//]H14.
Apply PP_mult_corr; Auto.
Apply PP_mult_corr; Auto.
Apply div_resp_ap_zero_rev; Auto.
Apply mult_resp_ap_zero; Auto.
Apply div_resp_ap_zero with y1 nzy1.
Step y.
Qed.

Fixpoint Norm [e:expr] : expr :=
  Cases e of
    (expr_var n) =>
      (expr_div (expr_plus (expr_mult e expr_one) expr_zero) expr_one)
  | (expr_int i) =>
      (expr_div e expr_one)
  | (expr_plus e1 e2) => (FF_plus (Norm e1) (Norm e2))
  | (expr_mult e1 e2) => (FF_mult (Norm e1) (Norm e2))
  | (expr_div e1 e2) => (FF_div (Norm e1) (Norm e2))
  | (expr_part f e) =>
      (expr_div (expr_plus (expr_mult (expr_part f (Norm e)) expr_one) expr_zero) expr_one)
  end.

Lemma Norm_corr : (e:expr; x:F)(II e x)->(II (Norm e) x).
Intro; Elim e; Intros; Simpl.
Apply (interp_div F val fun
        (expr_plus (expr_mult (expr_var v) expr_one) expr_zero)
        expr_one x (One::F) x (ring_non_triv F)).
Algebra.
Apply (interp_plus F val fun (expr_mult (expr_var v) expr_one) expr_zero x
        (Zero::F) x).
Algebra.
Apply (interp_mult F val fun (expr_var v) expr_one x (One::F) x); Algebra.
Apply (interp_int F val fun `1`); Algebra.
Apply (interp_int F val fun `0`); Algebra.
Apply (interp_int F val fun `1`); Algebra.
Apply (interp_div F val fun (expr_int z) expr_one x (One::F) x (ring_non_triv F)).
Algebra. Algebra. Apply (interp_int F val fun `1`); Algebra.
Inversion H1. Apply interp_wd with x0[+]y. Apply FF_plus_corr; Auto. Auto.
Inversion H1. Apply interp_wd with x0[*]y. Apply FF_mult_corr; Auto. Auto.
Inversion H1. Apply interp_wd with x0[/]y[//]nzy.
Apply FF_div_corr; Auto. Auto.
Apply (interp_div F val fun
        (expr_plus (expr_mult (expr_part f (Norm e0)) expr_one) expr_zero)
        expr_one x (One::F) x (ring_non_triv F)).
Algebra.
Apply (interp_plus F val fun (expr_mult (expr_part f (Norm e0)) expr_one) expr_zero x
        (Zero::F) x).
Algebra.
Apply (interp_mult F val fun (expr_part f (Norm e0)) expr_one x (One::F) x); Algebra.
Inversion H0.
Apply (interp_part F val fun (Norm e0) f x0 x Hx); Auto.
Apply (interp_int F val fun `1`); Algebra.
Apply (interp_int F val fun `0`); Algebra.
Apply (interp_int F val fun `1`); Algebra.
Qed.

Lemma Norm_wf : (e:expr)(wf F val fun e)->(wf F val fun (Norm e)).
Unfold wf.
Intros.
Elim H.
Intros.
Exists x.
Apply Norm_corr.
Assumption.
Qed.

Definition expr_is_zero [e:expr] : Prop :=
  Cases e of
    (expr_div (expr_int ZERO) _) => True
  | _ => False
  end.

Lemma expr_is_zero_corr : (e:expr)(wf F val fun e)->(expr_is_zero e)->(II e Zero).
Unfold wf.
Intros e H.
Elim H. Intro.
Elim e; Simpl; Try (Intros; Tauto).
Intros e0 H0 e1 H1.
Elim e0; Simpl; Try (Intros; Tauto).
Intro.
Elim z; Simpl; Try Tauto; Intros H2 H3.
Inversion H2.
Apply interp_div with (Zero::F) y nzy.
Apply div_prop.
Apply interp_int.
Algebra.
Assumption.
Qed.

Lemma Tactic_lemma_zero : (x:F)(e:(xexpr F val fun x))
  (expr_is_zero (Norm (xforget ???? e)))->(x [=] Zero).
Intros.
Apply refl_interp with val fun (Norm (xforget ???? e)).
Apply Norm_corr.
Apply xexpr2interp.
Apply expr_is_zero_corr.
Apply Norm_wf.
Apply xexpr2wf.
Assumption.
Qed.

Lemma Tactic_lemma : (x,y:F)(e:(xexpr F val fun x))(f:(xexpr F val fun y))
  (expr_is_zero (Norm (xforget ???? (xexpr_minus ????? e f))))->(x [=] y).
Intros.
Apply cg_inv_unique_2.
Apply Tactic_lemma_zero with (xexpr_minus ????? e f).
Assumption.
Qed.

End NormCorrect.
