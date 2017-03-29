(* $Id: CVectorSpace.v,v 1.5 2003/03/11 13:35:54 lcf Exp $ *)

(* Obsolete but maintained *)

Require Export CFields.

Implicit Arguments On.
Record VSpace [F:CField] : Type :=
  { vs_vs  :> CGroup;
    vs_op  : (CSetoid_outer_op F vs_vs);
    vs_assoc : (a,b:F)(v:vs_vs)
               (vs_op (a [*] b) v) [=] (vs_op a (vs_op b v));
    vs_unit  : (v:vs_vs)(vs_op One v) [=] v;
    vs_distl : (a,b:F)(v:vs_vs)
               (vs_op (a [+] b) v) [=] ((vs_op a v) [+] (vs_op b v));
    vs_distr : (a:F)(v,u:vs_vs)
               (vs_op a (v [+] u)) [=] ((vs_op a v) [+] (vs_op a u))
  }.
Implicit Arguments Off.

Hints Resolve vs_assoc vs_unit vs_distl vs_distr : algebra.

Implicits vs_op [1 2].
Infix NONA 6 "[']" vs_op.

Section VS_basics.
Variable F : CField.
Variable V : (VSpace F).

Lemma vs_op_zero: (a:F)(a ['] (Zero::V)) [=] Zero.
Intros.
Apply cg_cancel_lft with (a ['] (Zero::V)).
Step (a ['] ((Zero::V) [+] Zero)).
Step_final (a ['] (Zero::V)).
Qed.

Lemma zero_vs_op: (v:V)(Zero ['] v) [=] Zero.
Intros.
Apply cg_cancel_lft with (Zero ['] v).
Step ((Zero [+] Zero) ['] v).
Step_final (Zero ['] v).
Qed.

Hints Resolve vs_op_zero zero_vs_op : algebra.

Lemma vs_op_inv_V: (x:F; y:V) x ['] ([--]y) [=] [--](x ['] y).
Intros.
Apply cg_inv_unique.
Step x['](y[+]([--]y)).
Step_final x['](Zero::V).
Qed.

Lemma vs_op_inv_S: (x:F; y:V) ([--]x) ['] y [=] [--](x ['] y).
Intros.
Apply cg_inv_unique.
Step (x[+]([--]x))[']y.
Step_final Zero[']y.
Qed.

Hints Resolve vs_op_inv_V vs_op_inv_S : algebra.

Lemma vs_inv_assoc:
   (a:F; nz:(a[#]Zero))(v:V) v [=] (f_rcpcl a nz) ['] (a[']v).
Intros.
Step One[']v.
Step_final ((f_rcpcl a nz)[*]a)[']v.
Qed.
Hints Resolve vs_inv_assoc : algebra.


Lemma ap_zero_vs_op_l: (a:F)(v:V)(a[']v [#] Zero) -> a [#] Zero.
Intros.
Elim (csoo_strext ? ? (!vs_op F V) a Zero v v).
Auto.
Intro contra; Elim (ap_irreflexive ? ? contra).
Stepr (Zero::V).
Qed.

Lemma ap_zero_vs_op_r: (a:F)(v:V)(a[']v [#] Zero) -> v [#] Zero.
Intros.
Elim (csoo_strext ? ? (!vs_op F V) a a v Zero).
Intro contra; Elim (ap_irreflexive ? ? contra).
Auto.
Stepr (Zero::V).
Qed.

(* note this is the same proof as mult_resp_ap_zero *)
Lemma vs_op_resp_ap_rht:
   (a:F)(v,u:V)(a[#]Zero) -> (v[#]u) -> (a[']v) [#] (a[']u).
Intros.
Cut ((f_rcpcl a H) ['] (a ['] v)) [#] ((f_rcpcl a H) ['] (a ['] u)).
Intros.
Case (csoo_strext ? ? ? ? ? ? ? H1).
Intro contra; Elim (ap_irreflexive ? ? contra).
Auto.
Stepr u.
Step v.
Qed.

Lemma vs_op_resp_ap_zero:
   (a:F)(v:V)(a [#] Zero) -> (v [#] Zero) -> a[']v [#] Zero.
Intros.
Stepr a['](Zero::V).
Apply vs_op_resp_ap_rht; Assumption.
Qed.

Lemma vs_op_resp_ap_lft:
   (a,b:F)(v:V)(a[#]b) -> (v [#] Zero) -> (a[']v) [#] (b[']v).
Intros.
Apply zero_minus_apart.
Step (a[-]b)[']v.
Apply vs_op_resp_ap_zero;[Idtac|Assumption].
Apply minus_ap_zero; Assumption.
Unfold cg_minus. Step_final a[']v[+]([--]b[']v).
Qed.

End VS_basics.
Hints Resolve vs_op_zero zero_vs_op : algebra.
