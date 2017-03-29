(* $Id: TaylorLemma.v,v 1.18 2003/03/13 12:06:24 lcf Exp $ *)

Require Export Rolle.

Opaque Min.

Section Taylor_Defs.

(* Tex_Prose
\chapter{Taylor's Theorem}

We now prove the Taylor theorem for the remainder of the Taylor series.  This proof is done in two steps: first, we prove the lemma for a proper compact interval; next we generalize the result to two arbitrary (eventually equal) points in a proper interval.

We asSume two different points $a$ and $b$ in the domain of $F$ and define the nth order derivative of $F$ in the interval $[\min(a,b),\max(a,b)]$.
*)

Variables a,b:IR.
Hypothesis Hap:a[#]b.

Local Hab':=(ap_imp_Min_less_Max ?? Hap).
Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

Variable F:PartIR.
Hypothesis Ha:(Pred F a).
Hypothesis Hb:(Pred F b).

(* Begin_Tex_Verb *)
Local fi:=[n:nat][Hf:(Diffble_I_n Hab' n F)][i:nat]
  [Hi:(lt i (S n))](ProjS1 (Diffble_I_n_imp_deriv_n ???
    i F (le_imp_Diffble_I ????? (lt_n_Sm_le ?? Hi) ? Hf))).
(* End_Tex_Verb *)

(* Tex_Prose
This last local definition is simply: $f_i=f^{(i)}$.
*)

Local Taylor_lemma1 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(i:nat)(Hi:(lt i (S n)))(Derivative_I_n Hab' i F (PartInt (fi n Hf i Hi))).
Intros.
Unfold fi.
Apply projS2.
Qed.

(* Tex_Prose
Now we can define the Taylor sequence around $a$.  The auxiliary definition gives, for any $i$, the function expressed by the rule \[g(x)=\frac{f^{(i)}(a)}{i!}*(x-a)^i.\]
*)

Local compact_a := (compact_Min_lft ?? Hab).

Local compact_b := (compact_Min_rht ?? Hab).

(* Begin_Tex_Verb *)
Local funct_i := [n:nat][Hf:(Diffble_I_n Hab' n F)]
  [i:nat][Hi:(lt i (S n))]
  ({-C-}((fi n Hf i Hi (Build_subcsetoid_crr IR ?? compact_a))
    [/]?[//](nring_fac_ap_zero ? i)))
  {*}(FId{-}{-C-}a){^}i.
(* End_Tex_Verb *)

Local funct_i' := [n:nat][Hf:(Diffble_I_n Hab' n F)][i:nat][Hi:(lt i (S n))]
  ((PartInt (fi n Hf i Hi)){*}({-C-}(One[/]?[//](nring_fac_ap_zero IR i)))){*}(({-C-}b){-}FId){^}i.

Local a_i : (n,Hf,i,Hi:?)(Pred (funct_i n Hf i Hi) a).
Split; Split; Simpl; Auto.
Qed.

Local b_i : (n,Hf,i,Hi:?)(Pred (funct_i n Hf i Hi) b).
Split; Split; Simpl; Auto.
Qed.

Local x_i : (x:IR)(I x)->(n,Hf,i,Hi:?)(Pred (funct_i n Hf i Hi) x).
Split; Split; Simpl; Auto.
Qed.

Local a_i' : (n,Hf,i,Hi:?)(Pred (funct_i' n Hf i Hi) a).
Split; Split; Simpl; Auto.
Qed.

Local b_i' : (n,Hf,i,Hi:?)(Pred (funct_i' n Hf i Hi) b).
Split; Split; Simpl; Auto.
Qed.

Local x_i' : (x:IR)(I x)->(n,Hf,i,Hi:?)(Pred (funct_i' n Hf i Hi) x).
Split; Split; Simpl; Auto.
Qed.

Local Taylor_lemma2 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(good_fun_seq ? (funct_i n Hf)).
Red; Intros.
Simpl.
Apply mult_wd.
Apply div_wd.
2: Rewrite H; Algebra.
Generalize H' Hx Hy; Clear Hy Hx H'.
Rewrite <- H; Intros.
Cut (Ha1,Ha2:?)((PartInt (fi n Hf i H0)) a Ha1)[=]((PartInt (fi n Hf i H')) a Ha2); Intros.
Simpl in H2.
Apply H2.
Apply Feq_imp_eq with (Compact Hab).
Unfold Hab; Apply Derivative_I_n_unique with i F; Apply Taylor_lemma1.
Apply compact_a.
Rewrite H.
Step (x[+][--]a)[^]j; Step_final (y[+][--]a)[^]j.
Qed.

Local Taylor_lemma2' : (n:nat)(Hf:(Diffble_I_n Hab' n F))(good_fun_seq' ? (funct_i n Hf)).
Repeat Intro.
Repeat Split.
Qed.

Local Taylor_lemma3 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(good_fun_seq ? (funct_i' n Hf)).
Red; Intros.
Simpl.
Apply mult_wd.
Apply mult_wd.
2: Rewrite H; Algebra.
Generalize H' Hx Hy; Clear Hy Hx H'.
Rewrite <- H; Intros.
Cut (Hx',Hy':?)((PartInt (fi n Hf i H0)) x Hx')[=]((PartInt (fi n Hf i H')) y Hy'); Intros.
Simpl in H2.
Apply H2.
Cut (Pred (PartInt (fi n Hf i H')) x); [Intro | Apply pfprwd with y; Algebra].
Apply eq_transitive_unfolded with (pfpfun ? ? H2).
Apply Feq_imp_eq with (Compact Hab).
Unfold Hab; Apply Derivative_I_n_unique with i F; Apply Taylor_lemma1.
Simpl in Hx.
Elim Hx; Intros.
Inversion_clear a0; Auto.
Algebra.
Rewrite H.
Step (b[+][--]x)[^]j; Step_final (b[+][--]y)[^]j.
Qed.

Local Taylor_lemma3' : (n:nat)(Hf:(Diffble_I_n Hab' n F))(good_fun_seq' ? (funct_i' n Hf)).
Repeat Intro.
Elim H2; Intros.
Simpl in a0 b0.
Clear b0; Inversion_clear a0.
Inversion_clear H3; Repeat Split.
Stepr x; Auto.
Step x; Auto.
Qed.

(* Tex_Prose
Adding the previous expressions up to a given bound $n$ gives us the Taylor Sum of order $n$.
*)

(* Begin_Tex_Verb *)
Definition Taylor_seq' [n:nat][Hf:(Diffble_I_n Hab' n F)] :=
  (FSumx ? (funct_i n Hf)).
(* End_Tex_Verb *)

Local Taylor_seq'_aux [n:nat][Hf:(Diffble_I_n Hab' n F)] := (FSumx ? (funct_i' n Hf)).

Lemma lemma_a : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Pred (Taylor_seq' n Hf) a).
Intros.
Repeat Split.
Apply FSumx_pred'.
Repeat Split.
Repeat Split.
Qed.

(* Tex_Prose
It is easy to show that $b$ is in the domain of this series, which allows us to write down the Taylor remainder around $b$.
*)

(* Begin_Tex_Verb *)
Lemma lemma_b : (n:nat)(Hf:(Diffble_I_n Hab' n F))
  (Pred (Taylor_seq' n Hf) b).
(* End_Tex_Verb *)
Intros.
Repeat Split.
Apply FSumx_pred'.
Repeat Split.
Repeat Split.
Qed.

Lemma lemma_a' : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Pred (Taylor_seq'_aux n Hf) a).
Intros.
Split.
Apply FSumx_pred'.
Red; Intros.
Simpl in H2.
Inversion_clear H2.
Inversion_clear H3.
Simpl.
Split; Split; Auto.
Apply compact_wd with x; Auto.
Intros.
Apply a_i'.
Apply a_i'.
Qed.

Lemma lemma_b' : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Pred (Taylor_seq'_aux n Hf) b).
Intros.
Split.
Apply FSumx_pred'.
Red; Intros.
Simpl in H2.
Inversion_clear H2.
Inversion_clear H3.
Simpl.
Split; Split; Auto.
Apply compact_wd with x; Auto.
Intros.
Apply b_i'.
Apply b_i'.
Qed.

(* Begin_Tex_Verb *)
Definition Taylor_rem [n:nat][Hf:(Diffble_I_n Hab' n F)] :=
  (F b Hb)[-]((Taylor_seq' n Hf) b (lemma_b n Hf)).
(* End_Tex_Verb *)

Local g:=[n:nat][Hf:(Diffble_I_n Hab' n F)][Hab:(b[-]a)[#]Zero]
  (({-C-}(F b Hb)){-}(Taylor_seq'_aux n Hf)){-}
   ({-C-}(Taylor_rem n Hf)){*}(({-C-}b{-}FId){*}({-C-}(One[/]?[//]Hab))).

Local Taylor_lemma4 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hab:(b[-]a)[#]Zero)(Ha':?)((g n Hf Hab) a Ha')[=]Zero.
Unfold g; Clear g; Intros.
Cut (Pred (({-C-}(F b Hb)){-}(Taylor_seq'_aux n Hf)){-}({-C-}(Taylor_rem n Hf)) a); Intros.
Apply eq_transitive_unfolded with (pfpfun ? ? H).
Opaque Taylor_seq'_aux Taylor_rem.
Simpl; Rational.
Transparent Taylor_rem.
Unfold Taylor_rem.
Apply eq_transitive_unfolded with (pfpfun ? ? (lemma_b n Hf))[-](pfpfun ? ? (lemma_a' n Hf)).
Opaque Taylor_seq'.
Simpl; Rational.
Transparent Taylor_seq' Taylor_seq'_aux.
Unfold Taylor_seq' Taylor_seq'_aux.
Cut (Pred (FSum O n (FSumx_to_FSum ? (funct_i n Hf))) b); Intros.
Cut (Pred (FSum O n (FSumx_to_FSum ? (funct_i' n Hf))) a); Intros.
Apply eq_transitive_unfolded with (pfpfun ? ? H0)[-](pfpfun ? ? H1).
Apply eq_symmetric_unfolded; Apply cg_minus_wd; Apply FSum_FSumx_to_FSum.
Apply Taylor_lemma2.
Apply Taylor_lemma2'.
Apply Taylor_lemma3.
Apply Taylor_lemma3'.
EApply eq_transitive_unfolded.
Simpl.
Apply eq_symmetric_unfolded; Apply Sum_minus_Sum.
Apply Sum_zero.
Auto with arith.
Intros.
Cut (Hb':?)(Ha':?)((FSumx_to_FSum (S n) (funct_i n Hf) i) b Hb')[-]((FSumx_to_FSum (S n) (funct_i' n Hf) i) a Ha')[=]Zero; Auto.
Unfold FSumx_to_FSum.
Elim le_lt_dec; Intro; Simpl.
Algebra.
Intros.
LetTac w:=((fi n Hf i b0 (Build_subcsetoid_crr ??? compact_a))[*](One[/]?[//](nring_fac_ap_zero IR i)))[*]((b[+][--]a)[^]i).
Stepr w[-]w; Unfold w; Simpl.
Repeat First [Apply cg_minus_wd | Apply mult_wd]; Try Apply csetoid_fun_wd_unfolded; Algebra.
Rational.
Simpl; Algebra.
Simpl; Intro i.
Opaque funct_i'.
Unfold FSumx_to_FSum.
Elim le_lt_dec; Intro; Simpl.
Auto.
Apply a_i'.
Opaque funct_i.
Simpl; Intro i.
Unfold FSumx_to_FSum.
Elim le_lt_dec; Intro; Simpl.
Auto.
Apply b_i.
Split; Split; Split; Auto.
Apply FSumx_pred'.
Red; Intros.
Inversion_clear H2.
Inversion_clear H3.
Simpl in H2.
Split; Split; Auto.
Simpl; Apply compact_wd with x; Auto.
Intros; Apply a_i'.
Qed.

Transparent funct_i funct_i'.

Local Taylor_lemma5 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hab:(b[-]a)[#]Zero)(Hb':?)((g n Hf Hab) b Hb')[=]Zero.
Unfold g; Intros.
Cut (Pred ({-C-}(F b Hb)){-}(Taylor_seq'_aux n Hf) b); Intros.
Apply eq_transitive_unfolded with (pfpfun ? ? H).
Opaque Taylor_seq'_aux.
Simpl; Rational.
Transparent Taylor_seq'_aux.
Unfold Taylor_seq'_aux.
Cut (Pred (FSum O n (FSumx_to_FSum ? (funct_i' n Hf))) b); Intros.
Apply eq_transitive_unfolded with (F b Hb)[-](pfpfun ? ? H0).
Opaque FSumx.
Apply eq_transitive_unfolded with (F b Hb)[-]((FSumx (S n) (funct_i' n Hf)) b (ProjIR2 H)).
Simpl; Rational.
Apply cg_minus_wd.
Algebra.
Apply eq_symmetric_unfolded; Apply FSum_FSumx_to_FSum.
Apply Taylor_lemma3.
Apply Taylor_lemma3'.
Simpl.
Stepr (pfpfun ? ? Hb)[-](pfpfun ? ? Hb); Apply cg_minus_wd.
Algebra.
EApply eq_transitive_unfolded.
Apply Sum_first.
Stepr (pfpfun ? ? Hb)[+]Zero; Apply bin_op_wd_unfolded.
Cut (H':?)((FSumx_to_FSum (S n) (funct_i' n Hf) O) b H')[=](pfpfun ? ? Hb); Auto.
Unfold FSumx_to_FSum.
Elim le_lt_dec; Intro; Simpl.
ElimType False; Inversion a0.
Intros; Simpl.
RStepr (pfpfun ? ? Hb)[*]One[*]One.
Apply mult_wd_lft.
Apply mult_wd.
2: Rational.
Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with ((PartInt (fi n Hf O b0)) b compact_b).
2: Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply Feq_imp_eq with (Compact Hab).
Apply (ProjS2 (Diffble_I_n_imp_deriv_n ????? (le_imp_Diffble_I ????? (lt_n_Sm_le O n b0) ? Hf))).
Apply compact_b.
Apply Sum_zero.
Auto with arith.
Intros.
Cut (H':?)((FSumx_to_FSum (S n) (funct_i' n Hf) i) b H')[=]Zero; Auto.
Unfold FSumx_to_FSum.
Elim le_lt_dec; Intro; Simpl.
Algebra.
Intro.
Stepr (fi n Hf i b0 (Build_subcsetoid_crr IR ? b (ProjIR1 (ProjIR1 H'))))[*](One[/]?[//](nring_fac_ap_zero ? i))[*]Zero.
Apply mult_wd_rht.
Step (b[-]b)[^]i.
Step_final (Zero::IR)[^]i.
Intro i.
Opaque funct_i'.
Unfold FSumx_to_FSum.
Elim le_lt_dec; Intro; Simpl.
Auto.
Apply b_i'.
Split.
Simpl; Auto.
Simpl.
Apply lemma_b'.
Qed.

Transparent funct_i' FSumx.

Local funct_aux [n:nat][Hf:(Diffble_I_n Hab' (S n) F)] := [i:nat][Hi:(lt i (S n))]
  ((PartInt (fi (S n) Hf (S i) (lt_n_S ?? Hi))){*}({-C-}(One[/]?[//](nring_fac_ap_zero IR i)))){*}({-C-}b{-}FId){^}i.

Local Taylor_lemma6 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hf':(Diffble_I_n Hab' (S n) F))(i:nat)(Hi:(lt i (S n)))
  (Derivative_I Hab' (PartInt (fi n Hf i Hi)) (PartInt (fi (S n) Hf' (S i) (lt_n_S ?? Hi)))).
Intros.
Cut (Derivative_I_n Hab' (1) (PartInt (fi n Hf i Hi)) (PartInt (fi (S n) Hf' (S i) (lt_n_S i (S n) Hi)))).
Intro.
Simpl in H.
Elim H; Intros f' H1 H2.
Apply Derivative_I_wdr with (PartInt f'); Assumption.
Cut (S i)=(plus (1) i); [Intro | Omega].
Cut (lt (plus (1) i) (S (S n))); [Intro | Omega].
Apply Derivative_I_n_wdr with (PartInt (fi (S n) Hf' ? H0)).
Apply Derivative_I_n_unique with (S i) F.
Generalize H0; Clear H0.
Rewrite <- H; Intro.
Apply Taylor_lemma1.
Apply Taylor_lemma1.
Apply Derivative_I_n_wdl with (n_deriv_I ????? (le_imp_Diffble_I ????? (lt_n_Sm_le i n Hi) ? Hf)).
2: Apply Derivative_I_n_wdr with (n_deriv_I ????? (le_imp_Diffble_I ????? (lt_n_Sm_le ?? H0) ? Hf')).
3: Apply n_deriv_plus.
Apply Derivative_I_n_unique with i F.
Apply n_deriv_lemma.
Apply Taylor_lemma1.
Apply Derivative_I_n_unique with (plus (1) i) F.
Apply n_deriv_lemma.
Apply Taylor_lemma1.
Qed.

Tactic Definition Lazy_Included := Repeat First [Apply included_IR | Apply included_FPlus | Apply included_FInv | Apply included_FMinus | Apply included_FMult | Apply included_FNth | Apply included_refl].

Tactic Definition Lazy_Eq := Repeat First [Apply bin_op_wd_unfolded | Apply un_op_wd_unfolded | Apply cg_minus_wd | Apply div_wd | Apply csetoid_fun_wd_unfolded]; Algebra.

Local Taylor_lemma7 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hf':(Diffble_I_n Hab' (S n) F))(i:nat)(Hi:(lt O i))(Hi':(lt i (S n)))
  (Derivative_I Hab' (funct_i' n Hf i Hi') (funct_aux n Hf' i Hi'){-}(funct_aux n Hf' (pred i) (lt_5 ?? Hi'))).
Do 5 Intro.
Rewrite (S_pred ?? Hi).
LetTac p:=(pred i); ClearBody p; Clear Hi i.
Intros.
Cut (Derivative_I Hab' (PartInt (fi n Hf ? Hi')) (PartInt (fi (S n) Hf' (S (S p)) (lt_n_S ?? Hi')))); [Intro | Apply Taylor_lemma6].
Unfold funct_aux funct_i'.
New_Deriv.
Apply Feq_reflexive.
Lazy_Included.
Apply eq_imp_Feq.
Lazy_Included.
Lazy_Included.
Intros.
Simpl in Hx Hx'; Simpl.
LetTac fiSp1 := (fi n Hf (S p) Hi').
LetTac fiSp2 := (fi (S n) Hf' (S p) (lt_n_S p (S n) (lt_5 (S p) (S n) Hi'))).
Cut (x,y:(subset I))(((scs_elem ?? x)[=](scs_elem ?? y))->(fiSp1 x)[=](fiSp2 y)); Intros.
LetTac x1:=(Build_subcsetoid_crr IR ?? (ProjIR1 (ProjIR1 (ProjIR1 Hx)))).
Simpl in x1; Fold x1.
LetTac x2:=(Build_subcsetoid_crr IR ?? (ProjIR1 (ProjIR1 (ProjIR2 Hx')))).
Simpl in x2; Fold x2.
LetTac x3:=(Build_subcsetoid_crr IR ?? (ProjIR1 (ProjIR1 (ProjIR1 (ProjIR2  Hx))))).
Simpl in x3; Fold x3.
LetTac x4:=(Build_subcsetoid_crr IR ?? (ProjIR1 (ProjIR1 (ProjIR1 Hx')))).
Simpl in x4; Fold x4.
LetTac x5:=(Build_subcsetoid_crr IR ?? (ProjIR1 (ProjIR2 (ProjIR1 (ProjIR2 Hx))))).
Simpl in x5; Fold x5.
LetTac fiSSp := (fi (S n) Hf' (S (S p)) (lt_n_S (S p) (S n) Hi')).
LetTac pp:=(One[/](nring (plus (fac p) (mult p (fac p))))[//](nring_fac_ap_zero IR (S p))).
LetTac bxp:=(nexp ? p b[-]x).
LetTac a1:=(fiSp1 x1); LetTac a5:=(fiSSp x5); Simpl in a1 a5; Fold a1 a5.
RStep (a5[*]pp)[*](bxp[*](b[-]x))[-](a1[*](((nring p)[+]One)[*]pp))[*]bxp.
Unfold a1 a5; Clear a1 a5.
Lazy_Eq.
Unfold x4 x5; Algebra.
Simpl; Algebra.
Unfold pp.
RStepr (nring (S p))[*](One[/]?[//](mult_resp_ap_zero ??? (nring_fac_ap_zero ? p) (pos_ap_zero ?? (pos_nring_S IR p)))); Simpl.
Apply mult_wd_rht; Apply div_wd.
Algebra.
Clear H1 H bxp pp x5 x4 x3 x2 x1 fiSSp fiSp1 fiSp2 Hx.
Cut (plus (fac p) (mult p (fac p)))=(mult (fac p) (S p)).
Intro; Rewrite H.
EApply eq_transitive_unfolded.
Apply nring_comm_mult.
Algebra.
Transitivity (mult (S p) (fac p)); Auto with arith.
Unfold fiSp1 fiSp2.
Apply eq_transitive_unfolded with ((PartInt (fi n Hf (S p) Hi')) (scs_elem ?? x0) (scs_prf ?? x0)).
2: Apply eq_transitive_unfolded with ((PartInt (fi (S n) Hf' (S p) (lt_n_S ?? (lt_5 ?? Hi')))) (scs_elem ?? x0) (scs_prf ?? x0)).
Simpl; Apply csetoid_fun_wd_unfolded.
Case x0; Simpl; Algebra.
Apply Feq_imp_eq with (Compact Hab).
Unfold Hab; Apply Derivative_I_n_unique with (S p) F; Apply Taylor_lemma1.
Apply scs_prf.
Simpl; Apply csetoid_fun_wd_unfolded.
Generalize H1; Case x0; Case y; Auto.
Qed.

Local Taylor_lemma8 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hf':(Diffble_I_n Hab' (S n) F))(Hi:(lt O (S n)))
  (Derivative_I Hab' (funct_i' n Hf O Hi) (funct_aux n Hf' O Hi)).
Intros.
Cut (Derivative_I Hab' (PartInt (fi n Hf ? Hi)) (PartInt (fi (S n) Hf' (1) (lt_n_S ?? Hi)))); [Intro | Apply Taylor_lemma6].
Unfold funct_aux funct_i'; New_Deriv.
Apply Feq_reflexive; Lazy_Included.
Apply eq_imp_Feq.
Lazy_Included.
Lazy_Included.
Intros; Simpl.
Apply eq_transitive_unfolded with ((fi (S n) Hf' (1) (lt_n_S ?? Hi) (Build_subcsetoid_crr ??? (ProjIR1 (ProjIR2 (ProjIR1 (ProjIR2 Hx))))))[*](One[/]?[//](nring_fac_ap_zero IR O)))[*]One.
Simpl; Rational.
Lazy_Eq; Simpl; Algebra.
Qed.

Local Taylor_lemma9 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hf':(Diffble_I_n Hab' (S n) F))
  (Derivative_I Hab' (Taylor_seq'_aux n Hf) (funct_aux n Hf' n (lt_n_Sn n))).
Intro; Induction n.
Intros.
Unfold Taylor_seq'_aux; Simpl.
Apply Derivative_I_wdl with (funct_i' O Hf O (lt_n_Sn O)).
Apply eq_imp_Feq.
Split; Split; Simpl; Auto.
Split; Split; Split; Simpl; Auto.
Intros; Simpl.
Apply eq_transitive_unfolded with Zero[+]
  ((fi O Hf O (lt_n_Sn O) (Build_subcsetoid_crr ??? (ProjIR1 (ProjIR1 Hx))))[*](One[/](Zero[+]One)[//](nring_fac_ap_zero IR O)))[*]One.
Simpl; Rational.
Lazy_Eq; Simpl; Algebra.
Apply Taylor_lemma8; Assumption.
Cut {p:nat | (S n)=p}; [Intro | Exists (S n); Auto].
Elim H; Intros p H0.
Rewrite H0.
Intros.
Unfold Taylor_seq'_aux; Simpl.
Generalize Hf Hf'; Clear Hf Hf'.
Rewrite <- H0; Intros.
Cut (Diffble_I_n Hab' n F); [Intro | Apply le_imp_Diffble_I with (S n); [Omega | Assumption]].
Apply Derivative_I_wdl with (Taylor_seq'_aux n H1){+}(funct_i' ? Hf ? (lt_n_Sn (S n))).
Unfold Taylor_seq'_aux.
Apply eq_imp_Feq.
Repeat (Split; Auto).
Apply FSumx_pred'.
Red; Intros.
Exact (Taylor_lemma3' ???? H3 ???? H5 H6).
Intros; Simpl; Repeat (Split; Auto).
Repeat (Split; Auto).
Apply FSumx_pred'.
Red; Intros.
Exact (Taylor_lemma3' ???? H3 ???? H5 H6).
Intros; Simpl; Repeat (Split; Auto).
Intros; Simpl.
Repeat First [Apply mult_wd | Apply bin_op_wd_unfolded | Apply csetoid_fun_wd_unfolded | Apply eq_reflexive_unfolded]; Simpl.
3: Algebra.
Apply Feq_imp_eq with (Compact Hab).
2: Assumption.
Apply FSumx_wd'.
Intros; Apply eq_imp_Feq.
Repeat (Split; Auto).
Repeat (Split; Auto).
Intros; Simpl.
Repeat Apply mult_wd_lft.
Apply eq_transitive_unfolded with ((PartInt (fi n H1 i (lt_S ?? H3))) x0 H4).
Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply eq_transitive_unfolded with ((PartInt (fi (S n) Hf i (lt_S ?? (lt_S ?? H')))) x0 H4).
2: Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply Feq_imp_eq with (Compact Hab).
Unfold Hab; Apply Derivative_I_n_unique with i F; Apply Taylor_lemma1.
Auto.
Apply eq_transitive_unfolded with ((PartInt (fi n H1 n (lt_n_Sn ?))) x H2).
2: Apply eq_transitive_unfolded with ((PartInt (fi (S n) Hf n (lt_S ?? (lt_n_Sn ?)))) x H2).
Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
2: Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply Feq_imp_eq with (Compact Hab).
Unfold Hab; Apply Derivative_I_n_unique with n F; Apply Taylor_lemma1.
Auto.
Apply Derivative_I_wdr with  (funct_aux (S n) Hf' (pred (S n)) (lt_5 ?? (lt_n_Sn (S n)))){+}
  ((funct_aux ? Hf' ? (lt_n_Sn (S n))){-}(funct_aux (S n) Hf' (pred (S n)) (lt_5 ?? (lt_n_Sn (S n))))).
Opaque funct_aux.
FEQ.
Transparent funct_aux.
Repeat (Split; Auto).
Repeat (Split; Auto).
Apply Derivative_I_plus.
Apply Derivative_I_wdr with (funct_aux n Hf n (lt_n_Sn n)).
Apply eq_imp_Feq.
Repeat (Split; Auto).
Repeat (Split; Auto).
Intros; Simpl.
Repeat Apply mult_wd_lft.
Apply eq_transitive_unfolded with ((PartInt (fi (S n) Hf (S n) (lt_n_S ?? (lt_n_Sn ?)))) x H2).
2: Apply eq_transitive_unfolded with ((PartInt (fi (S (S n)) Hf' (S n) (lt_n_S ?? (lt_5 ?? (lt_n_Sn (S n)))))) x H2).
Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
2: Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply Feq_imp_eq with (Compact Hab).
Unfold Hab; Apply Derivative_I_n_unique with (S n) F; Apply Taylor_lemma1.
Auto.
Apply Hrecn.
Apply Taylor_lemma7.
Omega.
Qed.

Local g':=[n:nat][Hf:(Diffble_I_n Hab' n F)][Hf':(Diffble_I_n Hab' (S n) F)][Hab:(b[-]a)[#]Zero]
  ({-C-}((Taylor_rem n Hf)[/]?[//]Hab)){-}(funct_aux n Hf' n (lt_n_Sn n)).

Local Taylor_lemma10 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hf':(Diffble_I_n Hab' (S n) F))(Hab:(b[-]a[#]Zero))(H:a[#]b)
  (Derivative_I Hab' (g n Hf Hab) (g' n Hf Hf' Hab)).
Unfold g g'.
Intros.
Cut (Derivative_I Hab' (Taylor_seq'_aux n Hf) (funct_aux n Hf' n (lt_n_Sn n))); [Intro | Apply Taylor_lemma9; Assumption].
Opaque Taylor_rem funct_aux.
New_Deriv.
Apply Feq_reflexive; Lazy_Included.
Included.
Apply eq_imp_Feq.
Lazy_Included.
Included.
Lazy_Included.
Included.
Intros; Simpl; Rational.
Qed.

Transparent Taylor_rem funct_aux.

(* Tex_Prose
Now for the Taylor theorem.

\begin{convention} Let \verb!e! be a positive real number.
\end{convention}
*)

Variable e:IR.
Hypothesis He : Zero[<]e.

Local Taylor_lemma11 : (n:nat)(Hf:(Diffble_I_n Hab' n F))(Hf':(Diffble_I_n Hab' (S n) F))(H:(b[-]a[#]Zero))
  {c:IR & (I c) | (Hc:?)((AbsIR ((g' n Hf Hf' H) c Hc))[<=]e[*](AbsIR One[/]?[//]H))}.
Intros.
Cut (Pred (g n Hf H) (Min a b)); Intros.
Cut (Pred (g n Hf H) (Max a b)); Intros.
Cut (Pred (g n Hf H) a); Intros.
Cut (Pred (g n Hf H) b); Intros.
Unfold I Hab; Apply Rolle with (g n Hf H) H0 H1.
Apply Taylor_lemma10; Auto.
Elim (ap_imp_less ??? Hap); Intro.
Apply eq_transitive_unfolded with (Zero::IR).
EApply eq_transitive_unfolded.
2: Apply Taylor_lemma4 with Ha':=H2.
Apply pfwdef; Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
2: Apply Taylor_lemma5 with Hb':=H3.
Apply pfwdef; Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Apply eq_transitive_unfolded with (Zero::IR).
EApply eq_transitive_unfolded.
2: Apply Taylor_lemma5 with Hb':=H3.
Apply pfwdef; EApply eq_transitive_unfolded.
Apply Min_comm.
Apply leEq_imp_Min_is_lft; Apply less_leEq; Auto.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
2: Apply Taylor_lemma4 with Ha':=H2.
Apply pfwdef; EApply eq_transitive_unfolded.
Apply Max_comm.
Apply leEq_imp_Max_is_rht; Apply less_leEq; Auto.
Step Zero[*](AbsIR One[/]?[//]H).
Apply mult_resp_less.
Assumption.
Apply AbsIR_pos.
Apply div_resp_ap_zero_rev.
Apply one_ap_zero.
Split; Split; Split; Simpl; Auto.
3: Split; Split.
2: Split; Split; Auto; Apply compact_b.
Apply FSumx_pred'; Intros.
2: Apply b_i'.
Red; Intros.
Exact (Taylor_lemma3' ???? H3 ???? H5 H6).
Split; Split; Split; Simpl; Auto.
3: Split; Split.
2: Split; Split; Auto; Apply compact_a.
Apply FSumx_pred'; Intros.
2: Apply a_i'.
Red; Intros.
Exact (Taylor_lemma3' ???? H2 ???? H4 H5).
Split; Split; Split; Simpl; Auto.
3: Split; Split.
2: Split; Split; Auto; Apply compact_inc_rht.
Apply FSumx_pred'; Intros.
2: Apply x_i'.
Red; Intros.
Exact (Taylor_lemma3' ???? H1 ???? H3 H4).
Unfold I; Apply compact_inc_rht.
Split; Split; Split; Simpl; Auto.
3: Split; Split.
2: Split; Split; Auto; Apply compact_inc_lft.
Apply FSumx_pred'; Intros.
2: Apply x_i'.
Red; Intros.
Exact (Taylor_lemma3' ???? H0 ???? H2 H3).
Unfold I; Apply compact_inc_lft.
Qed.

(* Begin_Tex_Verb *)
Local deriv_Sn' := [n:nat][Hf':(Diffble_I_n Hab' (S n) F)]
  ((n_deriv_I ????? Hf'){*}
    ({-C-}(One[/]?[//](nring_fac_ap_zero ? n)))){*}
    ({-C-}b{-}FId){^}n.
(* End_Tex_Verb *)

Local H:(b[-]a)[#]Zero.
RStep [--](a[-]b).
Apply inv_resp_ap_zero.
Apply minus_ap_zero; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Taylor_lemma : (n:nat)(Hf:(Diffble_I_n Hab' n F))
  (Hf':(Diffble_I_n Hab' (S n) F)){c:IR & (I c) | (Hc:?)
    (AbsIR (Taylor_rem n Hf)[-]
           ((deriv_Sn' n Hf') c Hc)[*](b[-]a))[<=]e}.
(* End_Tex_Verb *)
Intros.
Cut {c:IR & (I c) | (Hc:?)(AbsIR ((g' n Hf Hf' H) c Hc))[<=]e[*](AbsIR One[/]?[//]H)}; [Intro | Apply Taylor_lemma11; Assumption].
Elim H0; Intros c Hc' Hc; Clear H0; Exists c.
Auto.
Intro.
Cut (Pred (funct_aux n Hf' n (lt_n_Sn n)) c); Intros.
Apply leEq_wdl with (AbsIR (((Taylor_rem n Hf)[/]?[//]H)[-](pfpfun ? ? H0))[*](b[-]a)).
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply shift_mult_leEq with (AbsIR_resp_ap_zero ? H).
Apply AbsIR_pos; Apply H.
RStepr e[*](One[/]?[//](AbsIR_resp_ap_zero ? H)).
Apply leEq_wdr with e[*](AbsIR One[/]?[//]H).
Opaque funct_aux.
Cut (Pred (g' n Hf Hf' H) c); Intros.
EApply leEq_wdl.
Apply (Hc H1).
Apply AbsIR_wd; Unfold g'.
Opaque Taylor_rem.
Simpl; Rational.
Repeat (Split; Auto).
Apply mult_wd_rht.
Apply AbsIR_recip.
Apply eq_symmetric_unfolded.
Apply eq_transitive_unfolded with (AbsIR ((Taylor_rem n Hf)[/]?[//]H)[-](pfpfun ? ? H0))[*](AbsIR b[-]a).
EApply eq_transitive_unfolded.
2: Apply AbsIR_resp_mult.
Apply AbsIR_wd.
RStepr (Taylor_rem n Hf)[-](pfpfun ? ? H0)[*](b[-]a).
Apply cg_minus_wd.
Algebra.
Apply mult_wd_lft.
Transparent Taylor_rem funct_aux.
Unfold deriv_Sn' funct_aux.
Cut (Pred (n_deriv_I ?? Hab' (S n) F Hf') c); Intros.
Simpl; Apply eq_transitive_unfolded with ((n_deriv_I ?? Hab' (S n) F Hf') c H1)[*](One[/]?[//](nring_fac_ap_zero ? n))[*](b[-]c)[^]n.
Repeat Apply mult_wd_lft; Apply pfwdef; Algebra.
Repeat Apply mult_wd_lft.
Apply eq_transitive_unfolded with ((PartInt (fi (S n) Hf' (S n) (lt_n_S ?? (lt_n_Sn ?)))) c Hc').
2: Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Apply Feq_imp_eq with (Compact Hab).
Unfold Hab; Apply Derivative_I_n_unique with (S n) F.
Apply n_deriv_lemma.
Apply Taylor_lemma1.
Auto.
Apply n_deriv_inc; Auto.
Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Repeat (Split; Auto).
Qed.

End Taylor_Defs.
