(* $Id: RRefl_corr.v,v 1.5 2003/03/11 13:35:54 lcf Exp $ *)

Require Export RReflection.
Require Export Bool.

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

Section RNormCorrect.

Variable F : CRing.
Variable val : Rvarindex->F.
Variable fun : Rfunindex->(PartFunct F).

Syntactic Definition II := (Rinterp F val fun).

(*
four kinds of Rexprs:

  I	(Rexpr_int _)
  V	(Rexpr_var _)
  M	(Rexpr_mult V M)
	I
  P	(Rexpr_plus M P)
	I

M: sorted on V
P: sorted on M, all M's not an I
*)

Fixpoint RMI_mult [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_mult e f) in
  Cases e f of
    e (Rexpr_int ZERO) => (Rexpr_int ZERO)
  | (Rexpr_mult e1 e2) f => (Rexpr_mult e1 (RMI_mult e2 f))
  | (Rexpr_int i) (Rexpr_int j) => (Rexpr_int (Zmult i j))
  | _ _ => d
  end.

Opaque Zmult.
Lemma RMI_mult_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RMI_mult e f) x[*]y).
Cut (x,y:F)
     (II (Rexpr_int ZERO) y)->(II (Rexpr_int ZERO) x[*]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RMI_mult e2 f) x[*]y))
     ->(II (Rexpr_mult e1 e2) x)
     ->(II f y)
     ->(II (Rexpr_mult e1 (RMI_mult e2 f)) x[*]y).
Cut (i,j:Z; x,y:F)
     (II (Rexpr_int i) x)
     ->(II (Rexpr_int j) y)
     ->(II (Rexpr_int (Zmult i j)) x[*]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_mult e f) x[*]y).
Induction e; Induction f; Simpl; Auto.
Induction z; Simpl; Auto.
Induction z0; Induction z; Simpl; Auto.
Induction z; Simpl; Auto.
Induction z; Simpl; Auto.
Induction f; Simpl; Auto.
Induction z; Simpl; Auto.
Induction z0; Simpl; Auto.
Intros; Apply Rinterp_mult with x y; Algebra.
Intros; Apply Rinterp_wd with ((zring (Zmult i j))::F).
Apply Rinterp_int; Algebra.
Inversion H. Inversion H0.
Step_final ((zring i)[*](zring j)::F).
Intros. Inversion H0.
Apply Rinterp_wd with x0[*](y0[*]y); Algebra .
Apply Rinterp_mult with x0 y0[*]y; Algebra.
Step (x0[*]y0)[*]y; Algebra.
Intros. Inversion H.
Apply Rinterp_wd with ((zring `0`)::F).
Apply Rinterp_int; Algebra .
Step (Zero::F).
Step x[*]Zero.
Step_final x[*](zring `0`).
Qed.
Transparent Zmult.

Fixpoint eq_nat [n:nat] : nat -> bool := [m:nat]
  Cases n m of
    (S n') (S m') => (eq_nat n' m')
  | O O => true
  | _ _ => false
  end.

Fixpoint lt_nat [n:nat] : nat -> bool := [m:nat]
  Cases n m of
    (S n') (S m') => (lt_nat n' m')
  | O (S _) => true
  | _ _ => false
  end.

Definition le_nat [n,m:nat] := (orb (eq_nat n m) (lt_nat n m)).

Definition eq_int [z:Z] : Z -> bool := [z':Z]
  Cases z z' of
    (POS n) (POS m) => (eq_nat (convert n) (convert m))
  | ZERO ZERO => true
  | (NEG n) (NEG m) => (eq_nat (convert n) (convert m))
  | _ _ => false
  end.

Definition lt_int [z:Z] : Z -> bool := [z':Z]
  Cases z z' of
    (POS n) (POS m) => (lt_nat (convert n) (convert m))
  | (POS n) _ => false
  | ZERO (POS n) => true
  | ZERO _ => false
  | (NEG n) (NEG m) => (lt_nat (convert m) (convert n))
  | (NEG n) _ => true
  end.

Definition le_int [z,z':Z] := (orb (eq_int z z') (lt_int z z')).

Fixpoint eq_Rexpr [e:Rexpr] : Rexpr -> bool := [f:Rexpr]
  Cases e f of
    (Rexpr_var n) (Rexpr_var m) => (eq_nat n m)
  | (Rexpr_int z) (Rexpr_int z') => (eq_int z z')
  | (Rexpr_plus e1 e2) (Rexpr_plus f1 f2) => (andb (eq_Rexpr e1 f1) (eq_Rexpr e2 f2))
  | (Rexpr_mult e1 e2) (Rexpr_mult f1 f2) => (andb (eq_Rexpr e1 f1) (eq_Rexpr e2 f2))
  | (Rexpr_part n e') (Rexpr_part m f') => (andb (eq_nat n m) (eq_Rexpr e' f'))
  | _ _ => false
  end.

Fixpoint lt_Rexpr [e:Rexpr] : Rexpr -> bool := [f:Rexpr]
  Cases e f of
    (Rexpr_var n) (Rexpr_var m) => (lt_nat n m)
  | (Rexpr_var n) _ => true
  | _ (Rexpr_var n) => false

  | (Rexpr_int z) (Rexpr_int z') => (lt_int z z')
  | (Rexpr_int _) _ => true
  | _ (Rexpr_int _) => false

  | (Rexpr_plus e1 e2) (Rexpr_plus f1 f2) => (orb (lt_Rexpr e1 f1) (andb (eq_Rexpr e1 f1) (lt_Rexpr e2 f2)))
  | (Rexpr_plus _ _) _ => true
  | _ (Rexpr_plus _ _) => false

  | (Rexpr_mult e1 e2) (Rexpr_mult f1 f2) => (orb (lt_Rexpr e1 f1) (andb (eq_Rexpr e1 f1) (lt_Rexpr e2 f2)))
  | (Rexpr_mult _ _) _ => true
  | _ (Rexpr_mult _ _) => false

  | (Rexpr_part n e') (Rexpr_part m f') => (orb (lt_nat n m) (andb (eq_nat n m) (lt_Rexpr e' f')))
  end.

Definition le_Rexpr [e,f:Rexpr] := (orb (eq_Rexpr e f) (lt_Rexpr e f)).

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

Lemma eq_Rexpr_corr : (e,e':Rexpr)((eq_Rexpr e e')=true)->(e=e').
Induction e; Induction e'; Simpl; Intros; Try Inversion H3; Try Inversion H2; Try Inversion H1; Try Inversion H0; Try Inversion H.
Cut r=r0. Intro. Rewrite H0; Auto. Apply eq_nat_corr; Assumption. 
Cut z=z0. Intro. Rewrite H0; Auto. Apply eq_int_corr; Assumption. 
Clear H1 H2. Elim (andb_prop ?? H3); Intros. 
Cut r=r1. Cut r0=r2. Intros. Rewrite H4; Rewrite H6. Auto. 
Apply H0. Assumption. Apply H. Assumption.
Clear H1 H2. Elim (andb_prop ?? H3); Intros. 
Cut r=r1. Cut r0=r2. Intros. Rewrite H4; Rewrite H6. Auto. 
Apply H0. Assumption. Apply H. Assumption.
Clear H0. Elim (andb_prop ?? H1); Intros. 
Cut r=r1. Cut r0=r2. Intros. Rewrite H4. Rewrite H5. Auto. 
Apply H. Assumption. Apply eq_nat_corr. Assumption. 
Qed.

Fixpoint RMV_mult [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_mult e f) in
  Cases e f of
    (Rexpr_mult (Rexpr_var n) e') (Rexpr_var m) =>
      Cases (lt_nat n m) of
        true => (Rexpr_mult (Rexpr_var n) (RMV_mult e' f))
      | false => (Rexpr_mult f e)
      end
  | (Rexpr_mult (Rexpr_var n) e') (Rexpr_part _ _) =>
      (Rexpr_mult (Rexpr_var n) (RMV_mult e' f))
  | (Rexpr_mult (Rexpr_part _ _) e') (Rexpr_var _) =>
      (Rexpr_mult f e)
  | (Rexpr_mult (Rexpr_part n e') e0) (Rexpr_part m f') =>
      Cases (lt_Rexpr (Rexpr_part n e') f) of
        true => (Rexpr_mult (Rexpr_part n e') (RMV_mult e0 f))
      | false => (Rexpr_mult f e)
      end
  | (Rexpr_int i) f => (RMI_mult (Rexpr_mult f Rexpr_one) e)
  | _ _ => d
  end.

Opaque RMI_mult.
Lemma RMV_mult_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RMV_mult e f) x[*]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RMV_mult e2 f) x[*]y))
     ->(II (Rexpr_mult e1 e2) x)
     ->(II f y)
     ->(II (Rexpr_mult e1 (RMV_mult e2 f)) x[*]y).
Cut (e,f:Rexpr; x,y:F)
     (II e x)->(II f y)->(II (RMI_mult (Rexpr_mult f Rexpr_one) e) x[*]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_mult f e) x[*]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_mult e f) x[*]y).
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
Elim (orb (lt_nat n f1) (andb (eq_nat n f1) (lt_Rexpr f e0))); Simpl; Auto.
Intros n f.
Elim f; Simpl; Auto.
Intros; Apply Rinterp_mult with x y; Algebra.
Intros; Apply Rinterp_wd with y[*]x; Algebra.
Apply Rinterp_mult with y x; Algebra.
Intros; Apply Rinterp_wd with (y[*]One)[*]x.
Apply RMI_mult_corr; Auto.
Apply Rinterp_mult with y (One::F); Algebra .
Unfold Rexpr_one.
Apply Rinterp_int; Algebra .
Step_final x[*](y[*]One).
Intros. Inversion H0.
Apply Rinterp_wd with x0[*](y0[*]y).
Apply Rinterp_mult with x0 y0[*]y; Algebra.
Step_final (x0[*]y0)[*]y.
Qed.
Transparent RMI_mult.

Fixpoint RMM_mult [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_mult e f) in
  Cases e f of
    (Rexpr_mult e1 e2) f => (RMV_mult (RMM_mult e2 f) e1)
  | (Rexpr_int i) f => (RMI_mult f e)
  | _ _ => d
  end.

Opaque RMV_mult RMI_mult.
Lemma RMM_mult_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RMM_mult e f) x[*]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RMM_mult e2 f) x[*]y))
     ->(II (Rexpr_mult e1 e2) x)
     ->(II f y)
     ->(II (RMV_mult (RMM_mult e2 f) e1) x[*]y).
Cut (i:Z; f:Rexpr; x,y:F)
     (II (Rexpr_int i) x)->(II f y)->(II (RMI_mult f (Rexpr_int i)) x[*]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_mult e f) x[*]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros; Apply Rinterp_mult with x y; Algebra.
Intros; Apply Rinterp_wd with y[*]x; Algebra.
Apply RMI_mult_corr; Auto.
Intros. Inversion H0.
Apply Rinterp_wd with (y0[*]y)[*]x0.
Apply RMV_mult_corr; Auto.
Step x0[*](y0[*]y).
Step_final (x0[*]y0)[*]y.
Qed.
Transparent RMV_mult RMI_mult.

Fixpoint RMM_plus [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_plus e f) in
  Cases e f of
    (Rexpr_mult (Rexpr_var n) e') (Rexpr_mult (Rexpr_var m) f') =>
      Cases (eq_nat n m) of
        true => (RMV_mult (RMM_plus e' f') (Rexpr_var n))
      | false => d
      end
  | (Rexpr_mult (Rexpr_part g arg) e') (Rexpr_mult (Rexpr_part h arg') f') =>
      Cases (andb (eq_nat g h) (eq_Rexpr arg arg')) of
        true => (RMV_mult (RMM_plus e' f') (Rexpr_part g arg))
      | false => d
      end
  | (Rexpr_int i) (Rexpr_int j) => (Rexpr_int (Zplus i j))
  | _ _ => d
  end.

Opaque RMV_mult.
Lemma RMM_plus_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RMM_plus e f) x[+]y).
Cut (i,j:Z; x,y:F)
     (II (Rexpr_int i) x)
     ->(II (Rexpr_int j) y)
     ->(II (Rexpr_int (Zplus i j)) x[+]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_plus e f) x[+]y).
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
Apply Rinterp_wd with (y0[+]y1)[*]x0.
Apply RMV_mult_corr; Auto.
Step x0[*](y0[+]y1).
Step x0[*]y0[+]x0[*]y1.
Cut x0[=]x1. Intro.
Step_final x0[*]y0[+]x1[*]y1.
Apply refl_Rinterp with val fun (Rexpr_var n).
Assumption.
Rewrite (H5 (refl_equal ? true)). Assumption.
Intros; Apply eq_nat_corr; Auto.
Intros f e0 H3.
Intro f0.
Elim f0; Simpl; Auto.
Intros e3 H4 e4 H5.
Elim e3; Simpl; Auto.
Intros f1 e5 H6.
Cut (andb (eq_nat f f1) (eq_Rexpr e0 e5))=true->(f=f1).
Cut (andb (eq_nat f f1) (eq_Rexpr e0 e5))=true->e0=e5.
Elim (andb (eq_nat f f1) (eq_Rexpr e0 e5)); Simpl; Auto.
Intros. Inversion H9. Inversion H10. Apply Rinterp_wd with (y0[+]y1)[*]x0.
Apply RMV_mult_corr; Auto.
Stepr (x0[*]y0)[+](x1[*]y1). Step (y0[*]x0)[+](y1[*]x0).
Apply bin_op_wd_unfolded. Algebra. Stepr y1[*]x1. Apply mult_wd_rht.
Clear H6 H5 H4 H3 H2 H1.
Clear H9 H10.
Apply refl_Rinterp with val fun (Rexpr_part f e0).
Auto. Rewrite H7; Auto. Rewrite H8; Auto. 
Intro. Elim (andb_prop ?? H7); Intros. Apply eq_Rexpr_corr; Auto. 
Intro. Elim (andb_prop ?? H7); Intros. Apply eq_nat_corr; Auto.
Simpl; Auto.
Simpl; Auto.
Intros; Apply Rinterp_plus with x y; Algebra.
Intros. Inversion H. Inversion H0.
Apply Rinterp_wd with ((zring `i+j`)::F).
Apply Rinterp_int; Algebra.
Step_final ((zring i)[+](zring j)::F).
Qed.
Transparent RMV_mult.

Fixpoint eq_Rmonom [e:Rexpr] : Rexpr->bool := [f:Rexpr]
  Cases e f of
    (Rexpr_mult (Rexpr_var n) e') (Rexpr_mult (Rexpr_var m) f') =>
      (andb (eq_nat n m) (eq_Rmonom e' f'))
  | (Rexpr_mult (Rexpr_part n e1) e') (Rexpr_mult (Rexpr_part m f1) f') =>
      (andb (eq_nat n m) (andb (eq_Rmonom e' f') (eq_Rexpr e1 f1)))
  | (Rexpr_int _) (Rexpr_int _) => true
  | _ _ => false
  end.

Fixpoint lt_Rmonom [e:Rexpr] : Rexpr->bool := [f:Rexpr]
  Cases e f of
    (Rexpr_mult (Rexpr_var n) e') (Rexpr_mult (Rexpr_var m) f') =>
      (ifb (eq_nat n m) (lt_Rmonom e' f') (lt_nat n m))
  | (Rexpr_mult (Rexpr_var _) _) (Rexpr_mult (Rexpr_part _ _) _) => true
  | (Rexpr_mult (Rexpr_part n e1) e') (Rexpr_mult (Rexpr_part m f1) f') =>
      (ifb (eq_Rexpr (Rexpr_part n e1) (Rexpr_part m f1)) (lt_Rexpr e' f') (lt_Rexpr (Rexpr_part n e1) (Rexpr_part m f1)))
  | _ (Rexpr_int _) => true
  | _ _ => false
  end.

Fixpoint RPM_plus [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_plus e f) in
  Cases e f of
    (Rexpr_plus e1 e2) (Rexpr_int _) => (Rexpr_plus e1 (RPM_plus e2 f))
  | (Rexpr_int i) (Rexpr_int j) => (RMM_plus e f)
  | (Rexpr_plus e1 e2) f =>
      Cases (eq_Rmonom e1 f) of
        true => (RPM_plus e2 (RMM_plus e1 f))
      | false => 
          Cases (lt_Rmonom e1 f) of
            true => (Rexpr_plus e1 (RPM_plus e2 f))
          | false => (Rexpr_plus f e)
          end
      end
  | (Rexpr_int i) f => (Rexpr_plus f e)
  | _ _ => d
  end.

Opaque RMM_plus.
Lemma RPM_plus_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RPM_plus e f) x[+]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RPM_plus e2 f) x[+]y))
     ->(II (Rexpr_plus e1 e2) x)
     ->(II f y)
     ->(II (Rexpr_plus e1 (RPM_plus e2 f)) x[+]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RPM_plus e2 f) x[+]y))
     ->(II (Rexpr_plus e1 e2) x)
     ->(II f y)
     ->(II (RPM_plus e2 (RMM_plus e1 f)) x[+]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (RMM_plus e f) x[+]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_plus e f) x[+]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_plus f e) x[+]y).
Intros H H0 H1 H2 H3 e. Elim e.
Simpl; Auto.
Intros z f; Elim f; Intros; Simpl; Auto.
Intros e1 H4 e2 H5 f. Simpl.
Elim (lt_Rmonom e1 f); Elim (eq_Rmonom e1 f); Elim f; Intros; Simpl; Auto.
Simpl; Auto.
Simpl; Auto.
Intros; Apply Rinterp_wd with y[+]x; Algebra.
Apply Rinterp_plus with y x; Algebra.
Intros; Apply Rinterp_plus with x y; Algebra.
Intros; Apply RMM_plus_corr; Auto.
Intros. Inversion H0.
Apply Rinterp_wd with y0[+](x0[+]y).
Apply H; Auto.
Apply RMM_plus_corr; Auto.
Step (y0[+]x0)[+]y.
Step_final (x0[+]y0)[+]y.
Intros. Inversion H0.
Apply Rinterp_wd with x0[+](y0[+]y).
Apply Rinterp_plus with x0 y0[+]y; Algebra .
Step_final (x0[+]y0)[+]y.
Qed.
Transparent RMM_plus.

Fixpoint RPP_plus [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_plus e f) in
  Cases e f of
    (Rexpr_plus e1 e2) f => (RPM_plus (RPP_plus e2 f) e1)
  | (Rexpr_int i) f => (RPM_plus f e)
  | _ _ => d
  end.

Opaque RPM_plus.
Lemma RPP_plus_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RPP_plus e f) x[+]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RPP_plus e2 f) x[+]y))
     ->(II (Rexpr_plus e1 e2) x)
     ->(II f y)
     ->(II (RPM_plus (RPP_plus e2 f) e1) x[+]y).
Cut (i:Z; f:Rexpr; x,y:F)
     (II (Rexpr_int i) x)->(II f y)->(II (RPM_plus f (Rexpr_int i)) x[+]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_plus e f) x[+]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros. Apply Rinterp_plus with x y; Algebra.
Intros. Apply Rinterp_wd with y[+]x; Algebra.
Apply RPM_plus_corr; Auto.
Intros. Inversion H0.
Apply Rinterp_wd with (y0[+]y)[+]x0.
Apply RPM_plus_corr; Auto.
Step x0[+](y0[+]y).
Step_final (x0[+]y0)[+]y.
Qed.
Transparent RPM_plus.

Fixpoint RPM_mult [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_mult e f) in
  Cases e f of
    (Rexpr_plus e1 e2) f => (RPM_plus (RPM_mult e2 f) (RMM_mult e1 f))
  | (Rexpr_int i) _ => (RPM_plus (Rexpr_int ZERO) (RMI_mult f e))
  | _ _ => d
  end.

Opaque RPM_plus RMM_mult RMI_mult.
Lemma RPM_mult_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RPM_mult e f) x[*]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RPM_mult e2 f) x[*]y))
     ->(II (Rexpr_plus e1 e2) x)
     ->(II f y)
     ->(II (RPM_plus (RPM_mult e2 f) (RMM_mult e1 f)) x[*]y).
Cut (i:Z; f:Rexpr; x,y:F)
     (II (Rexpr_int i) x)
     ->(II f y)
     ->(II (RPM_plus (Rexpr_int ZERO) (RMI_mult f (Rexpr_int i))) x[*]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_mult e f) x[*]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros. Apply Rinterp_mult with x y; Algebra.
Intros. Apply Rinterp_wd with (zring `0`)[+](y[*]x).
Apply RPM_plus_corr.
Apply Rinterp_int; Algebra .
Apply RMI_mult_corr; Auto.
Step Zero[+]y[*]x.
Step_final y[*]x.
Intros. Inversion H0.
Apply Rinterp_wd with y0[*]y[+]x0[*]y.
Apply RPM_plus_corr; Auto.
Apply RMM_mult_corr; Auto.
Step (y0[+]x0)[*]y.
Step_final (x0[+]y0)[*]y.
Qed.
Transparent RPM_plus RMM_mult RMI_mult.

Fixpoint RPP_mult [e:Rexpr] : Rexpr->Rexpr := [f:Rexpr]
let d = (Rexpr_mult e f) in
  Cases e f of
    (Rexpr_plus e1 e2) f => (RPP_plus (RPM_mult f e1) (RPP_mult e2 f))
  | (Rexpr_int i) f => (RPM_mult f e)
  | _ _ => d
  end.

Opaque RPP_plus RPM_mult.
Lemma RPP_mult_corr : (e,f:Rexpr; x,y:F)
  (II e x)->(II f y)->(II (RPP_mult e f) x[*]y).
Cut (e1,e2,f:Rexpr; x,y:F)
     ((f:Rexpr; x,y:F)(II e2 x)->(II f y)->(II (RPP_mult e2 f) x[*]y))
     ->(II (Rexpr_plus e1 e2) x)
     ->(II f y)
     ->(II (RPP_plus (RPM_mult f e1) (RPP_mult e2 f)) x[*]y).
Cut (i:Z; f:Rexpr; x,y:F)
     (II (Rexpr_int i) x)->(II f y)->(II (RPM_mult f (Rexpr_int i)) x[*]y).
Cut (e,f:Rexpr; x,y:F)(II e x)->(II f y)->(II (Rexpr_mult e f) x[*]y).
Intros H H0 H1 e.
Elim e; Intros; Simpl; Auto.
Intros. Apply Rinterp_mult with x y; Algebra.
Intros. Apply Rinterp_wd with y[*]x; Algebra.
Apply RPM_mult_corr; Auto.
Intros. Inversion H0.
Apply Rinterp_wd with y[*]x0[+]y0[*]y.
Apply RPP_plus_corr; Auto.
Apply RPM_mult_corr; Auto.
Step x0[*]y[+]y0[*]y.
Step_final (x0[+]y0)[*]y.
Qed.
Transparent RPP_plus RPM_mult.

Fixpoint RNorm [e:Rexpr] : Rexpr :=
  Cases e of
    (Rexpr_var n) => (Rexpr_plus (Rexpr_mult e Rexpr_one) Rexpr_zero)
  | (Rexpr_int i) => e
  | (Rexpr_plus e1 e2) => (RPP_plus (RNorm e1) (RNorm e2))
  | (Rexpr_mult e1 e2) => (RPP_mult (RNorm e1) (RNorm e2))
  | (Rexpr_part f e) =>
      (Rexpr_plus (Rexpr_mult (Rexpr_part f (RNorm e)) Rexpr_one) Rexpr_zero)
  end.

Lemma RNorm_corr : (e:Rexpr; x:F)(II e x)->(II (RNorm e) x).
Intro; Elim e; Intros; Simpl.
Apply (Rinterp_plus F val fun (Rexpr_mult (Rexpr_var r) Rexpr_one) Rexpr_zero x
        (Zero::F) x).
Algebra.
Apply (Rinterp_mult F val fun (Rexpr_var r) Rexpr_one x (One::F) x); Algebra.
Apply (Rinterp_int F val fun `1`); Algebra.
Apply (Rinterp_int F val fun `0`); Algebra.
Assumption.
Inversion H1. Apply Rinterp_wd with x0[+]y. Apply RPP_plus_corr; Auto. Auto.
Inversion H1. Apply Rinterp_wd with x0[*]y. Apply RPP_mult_corr; Auto. Auto.
Apply (Rinterp_plus F val fun
        (Rexpr_mult (Rexpr_part r (RNorm r0)) Rexpr_one) Rexpr_zero x (Zero::F) x).
Algebra.
Apply (Rinterp_mult F val fun (Rexpr_part r (RNorm r0)) Rexpr_one x (One::F) x); Algebra.
Inversion H0.
Apply (Rinterp_part F val fun (RNorm r0) r x0 x Hx); Auto.
Apply (Rinterp_int F val fun `1`); Algebra.
Apply (Rinterp_int F val fun `0`); Algebra.
Qed.

Lemma RNorm_wf : (e:Rexpr)(Rwf F val fun e)->(Rwf F val fun (RNorm e)).
Unfold Rwf.
Intros.
Elim H.
Intros.
Exists x.
Apply RNorm_corr.
Assumption.
Qed.

(*
Definition RfNorm : (Rfexpr F val)->(Rfexpr F val) :=
  [e:(Rfexpr F val)]
  let e' = (Rfforget ? ? e) in
    (Rexpr2Rfexpr ? ? (RNorm e') (RNorm_wf e' (Rfexpr2wf ? ? e))).

Lemma RfNorm_compat : (e:(Rfexpr F val))
  (Rfforget ? ? (RfNorm e)) = (RNorm (Rfforget ? ? e)).
Intros.
Unfold RfNorm.
Apply Rexpr2Rfexpr_compat.
Qed.

Lemma RfNorm_corr : (e:(Rfexpr F val))
  (Rfinterp ? ? (RfNorm e)) [=] (Rfinterp ? ? e).
Intros.
Unfold RfNorm.
Apply Rexpr2Rfexpr_corr.
Apply RNorm_corr.
Apply Rfexpr2interp.
Qed.
*)

Definition Rexpr_is_zero [e:Rexpr] : Prop :=
  Cases e of
    (Rexpr_int ZERO) => True
  | _ => False
  end.

Lemma Rexpr_is_zero_corr : (e:Rexpr)(Rwf F val fun e)->(Rexpr_is_zero e)->(II e Zero).
Unfold Rwf.
Intros e H.
Elim H. Intro.
Elim e; Simpl; Try ((* FIXME *) Intros; Tauto).
Intro.
Elim z; Simpl; Try Tauto; Intros.
Apply Rinterp_int.
Algebra.
Qed.

Lemma RTactic_lemma_zero : (x:F)(e:(Rxexpr F val fun x))
  (Rexpr_is_zero (RNorm (Rxforget ? ? ? ? e)))->(x [=] Zero).
Intros.
Apply refl_Rinterp with val fun (RNorm (Rxforget ? ? ? ? e)).
Apply RNorm_corr.
Apply Rxexpr2interp.
Apply Rexpr_is_zero_corr.
Apply RNorm_wf.
Apply Rxexpr2wf.
Assumption.
Qed.

Lemma RTactic_lemma : (x,y:F)(e:(Rxexpr F val fun x))(f:(Rxexpr F val fun y))
  (Rexpr_is_zero (RNorm (Rxforget ? ? ? ? (Rxexpr_minus ? ? ? ? ? e f))))->(x [=] y).
Intros.
Apply cg_inv_unique_2.
Apply RTactic_lemma_zero with (Rxexpr_minus ? ? ? ? ? e f).
Assumption.
Qed.

End RNormCorrect.
