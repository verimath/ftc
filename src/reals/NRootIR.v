(* $Id: NRootIR.v,v 1.18 2003/03/13 12:06:25 lcf Exp $ *)

Require Export OddPolyRootIR.

Opaque IR.

(* Tex_Prose
\chapter{Roots of Real Numbers}
*)

Section NRoot.
(* Tex_Prose
\section{Roots exist}

\begin{convention} Let $n$ be a natural number and \verb!c! a nonnegative real.
\end{convention}
*)

Variable n : nat.
Hypothesis n_pos : (lt (0) n).
Variable c : IR.
Hypothesis c_nonneg : Zero [<=] c.

Local p := _X_[^]n[-](_C_ c).

(* Begin_Tex_Verb *)
Lemma CnrootIR : {x:IR | (Zero [<=] x) | (x[^]n [=] c)}.
(* End_Tex_Verb *)
Intros.
Cut (monic n p). Intro.
Elim (Ccpoly_pos' ? p Zero n); Auto.
Intro X. Intros H0 H1.
Cut {x:IR | (Zero [<=] x) /\ ((x [<=] X) /\ (p!x [=] Zero))}. Intro.
Elim H2. Clear H2. Intro. Intro H2.
Elim H2. Clear H2. Intros H2 H3. Elim H3. Clear H3. Intros.
Exists x. Auto.
Apply cg_inv_unique_2.
Step (_X_!x)[^]n[-](_C_ c)!x.
Step (_X_[^]n)!x[-](_C_ c)!x.
Step_final (_X_[^]n[-](_C_ c))!x.

Apply Civt_poly; Auto.
Apply monic_apzero with n; Auto.
Unfold p.
Step (_X_[^]n)!Zero[-](_C_ c)!Zero.
Step (_X_!Zero)[^]n[-]c.
Step Zero[^]n[-]c.
Step Zero[-]c.
Step [--]c.
Stepr [--](Zero::IR). Apply inv_resp_leEq. Auto.
Apply less_leEq. Auto.
Unfold p.
Apply monic_minus with (0).
Apply degree_le_c_.
Pattern 1 n. Replace n with (mult (1) n).
Apply monic_nexp.
Apply monic_x_.
Auto with arith.
Auto.
Qed.

End NRoot.

(* Tex_Prose
We define the root of order $n$ for any nonnegative real number and prove its main properties: $\left(\sqrt[n]x\right)^n=x$, $0\leq\sqrt[n]x$, if $0<x$ then $0<\sqrt[n]x$, $\sqrt[n]{x^n}=x$, and the nth root is monotonous---in particular, if $x<1$ then $\sqrt[n]x<1$.  \verb!(nroot ??)! will be written as {\tt\hypertarget{Syntactic_40}{NRoot}}.
*)

Section Nth_Root.

(* Begin_Tex_Verb *)
Lemma nroot: (x:IR)(k:nat)(Zero [<=] x)->(lt O k)->
  {y:IR | (Zero [<=] y) | (y[^]k [=] x)}.
(* End_Tex_Verb *)
Intros.
Elim (CnrootIR k H0 x H). Intro y. Intros.
Exists y; Auto.
Qed.

(* Begin_Tex_Verb *)
Definition NRoot [x:IR][n:nat][Hx:Zero[<=]x][Hn:(lt O n)]
  : IR := (proj1_sig2 ??? (nroot ?? Hx Hn)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma NRoot_power : (x,k,Hx,Hk:?)(NRoot x k Hx Hk)[^]k[=]x.
(* End_Tex_Verb *)
Intros.
Unfold NRoot.
Apply proj2b_sig2.
Qed.

Hints Resolve NRoot_power : algebra.

(* Begin_Tex_Verb *)
Lemma NRoot_nonneg : (x,k,Hx,Hk:?)Zero[<=](NRoot x k Hx Hk).
(* End_Tex_Verb *)
Intros.
Unfold NRoot.
Apply proj2a_sig2.
Qed.

(* Begin_Tex_Verb *)
Lemma NRoot_pos : (x,Hx,k,Hk:?)(Zero[<]x)->
  (Zero[<](NRoot x k Hx Hk)).
(* End_Tex_Verb *)
Intros.
Cut Zero [<=] (NRoot x k Hx Hk); Intros.
Cut ((NRoot x k Hx Hk) [<] Zero) + (Zero [<] (NRoot x k Hx Hk)); Intros.
Elim H1; Clear H1; Intro H1.
Elim (H0 H1).
Auto.
Apply ap_imp_less.
Apply un_op_strext_unfolded with (!nexp_op IR k).
Step x; Stepr (Zero::IR).
Apply pos_ap_zero; Auto.
Apply NRoot_nonneg.
Qed.

(* Begin_Tex_Verb *)
Lemma NRoot_power' : (x,k:?)(Hx':Zero[<=](x[^]k))
  (Hk:(lt O k))(Zero[<=]x)->(NRoot ?? Hx' Hk)[=]x.
(* End_Tex_Verb *)
Intros.
Apply root_unique with k; Auto.
Apply NRoot_nonneg.
Apply NRoot_power.
Qed.

(* Begin_Tex_Verb *)
Lemma NRoot_pres_less : (x,Hx,y,Hy,k,Hk:?)(x[<]y)->
  (NRoot x k Hx Hk)[<](NRoot y k Hy Hk).
(* End_Tex_Verb *)
Intros.
Apply power_cancel_less with k.
Apply NRoot_nonneg.
EApply less_wdl.
2: Apply eq_symmetric_unfolded; Apply NRoot_power.
EApply less_wdr.
2: Apply eq_symmetric_unfolded; Apply NRoot_power.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma NRoot_less_one : (x,Hx,k,Hk:?)(x[<]One)->(NRoot x k Hx Hk)[<]One.
(* End_Tex_Verb *)
Intros.
Apply power_cancel_less with k.
Apply less_leEq; Apply pos_one.
EApply less_wdl.
2: Apply eq_symmetric_unfolded; Apply NRoot_power.
Stepr (One::IR).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma NRoot_cancel : (x,Hx,y,Hy,k,Hk:?)
  ((NRoot x k Hx Hk)[=](NRoot y k Hy Hk))->(x[=]y).
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with (NRoot x k Hx Hk)[^]k.
Apply eq_symmetric_unfolded; Apply NRoot_power.
Apply eq_transitive_unfolded with (NRoot y k Hy Hk)[^]k.
2: Apply NRoot_power.
Apply nexp_wd; Algebra.
Qed.

(* Tex_Prose
\begin{convention} Let \verb!x,y! be nonnegative real numbers.
\end{convention}
*)

Variables x,y:IR.
Hypothesis Hx:Zero[<=]x.
Hypothesis Hy:Zero[<=]y.

(* Begin_Tex_Verb *)
Lemma NRoot_wd : (k,Hk,Hk':?)(x[=]y)->
  (NRoot x k Hx Hk)[=](NRoot y k Hy Hk').
(* End_Tex_Verb *)
Intros.
Apply root_unique with k; Auto.
Apply NRoot_nonneg.
Apply NRoot_nonneg.
EApply eq_transitive_unfolded.
EApply eq_transitive_unfolded.
2: Apply H.
Apply NRoot_power.
Apply eq_symmetric_unfolded; Apply NRoot_power.
Qed.

(* Begin_Tex_Verb *)
Lemma NRoot_unique : (k,Hk:?)(Zero[<]x)->
  ((x[^]k)[=]y)->(x[=](NRoot y k Hy Hk)).
(* End_Tex_Verb *)
Intros.
Apply root_unique with k; Auto.
Apply NRoot_nonneg.
EApply eq_transitive_unfolded.
Apply H0.
Apply eq_symmetric_unfolded; Apply NRoot_power.
Qed.

End Nth_Root.

Implicits NRoot [1 2].

(***********************************)
Section Square_root.
(***********************************)

(* Tex_Prose
\section{Square root}
*)

(* Begin_Tex_Verb *)
Definition sqrt [x:IR; xpos:(Zero [<=] x)] : IR :=
  (!NRoot x (2) xpos (lt_O_Sn (1))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma sqrt_sqr : (x:IR)(xpos:(Zero [<=] x))((sqrt x xpos)[^](2) [=] x).
(* End_Tex_Verb *)
Intros.
Unfold sqrt.
Apply NRoot_power.
Qed.

Hints Resolve sqrt_sqr : algebra.

(* Begin_Tex_Verb *)
Lemma sqrt_nonneg : (x:IR)(xpos:(Zero [<=] x))(Zero [<=] (sqrt x xpos)).
(* End_Tex_Verb *)
Intros.
Unfold sqrt.
Apply NRoot_nonneg.
Qed.

(* Begin_Tex_Verb *)
Lemma sqrt_wd : (x,y:IR)(xpos:(Zero [<=] x))(ypos:(Zero [<=] y))
  (x [=] y)->((sqrt x xpos) [=] (sqrt y ypos)).
(* End_Tex_Verb *)
Intros.
Unfold sqrt.
Apply NRoot_wd.
Auto.
Qed.

Hints Resolve sqrt_wd : algebra_c.

(* Begin_Tex_Verb *)
Lemma sqrt_to_nonneg : (x:IR)(Zero [<=] x)->(x2pos:(Zero [<=] x[^](2)))
  ((sqrt x[^](2) x2pos) [=] x).
(* End_Tex_Verb *)
Intros.
Apply root_unique with (2).
Apply sqrt_nonneg. Auto. Auto.
Step_final x[^](2).
Qed.

(* Begin_Tex_Verb *)
Lemma sqrt_to_nonpos : (x:IR)(x [<=] Zero)->(x2pos:(Zero [<=] x[^](2)))
  ((sqrt x[^](2) x2pos) [=] [--]x).
(* End_Tex_Verb *)
Intros.
Apply root_unique with (2).
Apply sqrt_nonneg.
Step [--](Zero::IR). Apply inv_resp_leEq. Auto.
Auto.
Step x[^](2). Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma sqrt_mult : (x,y:IR)
  (xpos:(Zero [<=] x))(ypos:(Zero [<=] y))(xypos:(Zero [<=] x[*]y))
    ((sqrt x[*]y xypos) [=] (sqrt x xpos)[*](sqrt y ypos)).
(* End_Tex_Verb *)
Intros.
Apply root_unique with (2).
Apply sqrt_nonneg.
Apply mult_resp_nonneg; Apply sqrt_nonneg.
Auto.
Step x[*]y.
Step (sqrt x xpos)[^](2)[*](sqrt y ypos)[^](2).
Rational.
Qed.

Hints Resolve sqrt_mult : algebra.

(* Begin_Tex_Verb *)
Lemma sqrt_mult_wd :
  (x,y,z:IR)(xpos:(Zero [<=] x))(ypos:(Zero [<=] y))(zpos:(Zero [<=] z))
    (z [=] x[*]y) -> (sqrt z zpos) [=] (sqrt x xpos)[*](sqrt y ypos).
(* End_Tex_Verb *)
Intros.
Cut Zero [<=] x[*]y. Intro.
Step_final (sqrt x[*]y H0).
Apply mult_resp_nonneg; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma sqrt_less : (x,y:IR)(ypos:(Zero [<=] y))
  (x[^](2) [<] y)->(x [<] (sqrt y ypos)).
(* End_Tex_Verb *)
Intros.
Apply power_cancel_less with (2).
Apply sqrt_nonneg.
Stepr y. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma sqrt_less' : (x,y:IR)(ypos:(Zero [<=] y))
  (x[^](2) [<] y)->([--]x [<] (sqrt y ypos)).
(* End_Tex_Verb *)
Intros.
Apply power_cancel_less with (2).
Apply sqrt_nonneg.
RStep x[^](2). Stepr y. Auto.
Qed.

End Square_root.

Hints Resolve sqrt_wd : algebra_c.
Hints Resolve NRoot_power NRoot_power' : algebra.
Hints Resolve sqrt_sqr sqrt_mult : algebra.


Section Absolute_Props.

(* Tex_Prose
\section{More on absolute value}

With the help of square roots, we can prove some more properties of absolute values in IR.
*)

(* Begin_Tex_Verb *)
Lemma AbsIR_sqrt_sqr : (x:IR; xxpos:(Zero [<=] x[^](2)))
  (AbsIR x) [=] (sqrt x[^](2) xxpos).
(* End_Tex_Verb *)
Intros. Unfold AbsIR. Simpl. Unfold ABSIR.
Apply equiv_imp_eq_max; Intros.
Apply power_cancel_less with (2).
Apply less_leEq.
Apply mult_cancel_less with (Two::IR). Apply pos_two.
RStep x[+][--]x.
RStepr y[+]y.
Apply plus_resp_less_both; Auto.
Step One[*]x[*]x.
RStep x[^](2)[+]Zero.
Apply shift_plus_less'.
RStepr (y[-]x)[*](y[-][--]x).
Apply mult_resp_pos.
Apply shift_zero_less_minus. Auto.
Apply shift_zero_less_minus. Auto.
Apply leEq_less_trans with (sqrt x[^](2) xxpos).
Apply power_cancel_leEq with (2). Auto.
Apply sqrt_nonneg.
Stepr x[^](2).
Apply leEq_reflexive.
Auto.
Apply leEq_less_trans with (sqrt x[^](2) xxpos).
Apply power_cancel_leEq with (2). Auto.
Apply sqrt_nonneg.
Stepr x[^](2).
RStep x[^](2).
Apply leEq_reflexive.
Auto.
Qed.

Hints Resolve AbsIR_sqrt_sqr : algebra.

(* Begin_Tex_Verb *)
Lemma AbsIR_resp_mult : (x,y:IR) (AbsIR (x[*]y))[=]((AbsIR x)[*](AbsIR y)).
(* End_Tex_Verb *)
Intros.
Step (sqrt (x[*]y)[^](2) (sqr_nonneg ? x[*]y)).
Cut Zero [<=] x[^](2)[*]y[^](2). Intro.
Step (sqrt x[^](2)[*]y[^](2) H).
Step_final (sqrt x[^](2) (sqr_nonneg ? x))[*](sqrt y[^](2) (sqr_nonneg ? y)).
Apply mult_resp_nonneg; Apply sqr_nonneg.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_product_positive : (x,y:IR)
  (Zero[<=]y)->(AbsIR x[*]y)[=](AbsIR x)[*]y.
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with (AbsIR x)[*](AbsIR y).
Apply AbsIR_resp_mult.
Apply bin_op_wd_unfolded.
Algebra.
Unfold AbsIR; Simpl; Unfold ABSIR.
Apply eq_transitive_unfolded with (Max [--]y y).
Apply Max_comm.
Apply leEq_imp_Max_is_rht.
Apply leEq_transitive with (Zero::IR).
Stepr [--](Zero::IR).
Apply inv_resp_leEq; Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_product_positive' : (x,y:IR)(Zero[<=]x)->
  (AbsIR x[*]y)[=]x[*](AbsIR y).
(* End_Tex_Verb *)
Intros.
Step (AbsIR y[*]x).
EApply eq_transitive_unfolded.
Apply AbsIR_product_positive; Auto.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_nexp : (x:IR)(n:nat)(AbsIR (nexp ? n x))[=](nexp ? n (AbsIR x)).
(* End_Tex_Verb *)
Intros.
Induction n.
Simpl; Apply AbsIR_eq_x; Apply less_leEq; Apply pos_one.
Simpl.
EApply eq_transitive_unfolded.
Apply AbsIR_resp_mult.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_nexp_op : (n:nat)(x:IR)(AbsIR x[^]n)[=](AbsIR x)[^]n.
(* End_Tex_Verb *)
Intros; Simpl; Apply AbsIR_nexp.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_less_square : (x,y:IR)((AbsIR x)[<]y)->(x[^](2))[<](y[^](2)).
(* End_Tex_Verb *)
Intros.
EApply less_wdl.
2: Apply AbsIR_eq_x; Apply sqr_nonneg.
EApply less_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_nexp_op.
Apply nexp_resp_less; Auto.
Apply AbsIR_nonneg.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_leEq_square : (x,y:IR)((AbsIR x)[<=]y)->(x[^](2))[<=](y[^](2)).
(* End_Tex_Verb *)
Intros.
EApply leEq_wdl.
2: Apply AbsIR_eq_x; Apply sqr_nonneg.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_nexp_op.
Apply nexp_resp_leEq; Auto.
Apply AbsIR_nonneg.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_division : (x,y:IR)(H,Hy:?)
  (AbsIR x[/]y[//]H)[=]((AbsIR x)[/](AbsIR y)[//]Hy).
(* End_Tex_Verb *)
Intros.
RStepr (AbsIR x)[*](One[/](AbsIR y)[//]Hy).
Apply eq_transitive_unfolded with (AbsIR x[*](One[/]y[//]H)).
Apply un_op_wd_unfolded; Rational.
Apply eq_transitive_unfolded with (AbsIR x)[*](AbsIR One[/]y[//]H).
Apply AbsIR_resp_mult.
Apply mult_wd_rht.
Cut (y[<]Zero)+(Zero[<]y).
Intros.
Elim H0.
Intros.
Apply eq_transitive_unfolded with [--](One[/]y[//]H).
Apply AbsIR_eq_inv_x.
RStepr Zero[/][--]y[//](inv_resp_ap_zero ? ? H).
Apply shift_leEq_div.
Step [--](Zero::IR).
Apply inv_resp_less; Assumption.
RStep [--](One::IR).
Stepr [--](Zero::IR); Apply inv_resp_leEq; Apply less_leEq; Apply pos_one.
RStep One[/][--]y[//](inv_resp_ap_zero ? ? H).
Apply div_wd.
Algebra.
Apply eq_symmetric_unfolded; Apply AbsIR_eq_inv_x.
Apply less_leEq; Assumption.
Intros.
Apply eq_transitive_unfolded with One[/]y[//]H.
Apply AbsIR_eq_x.
Apply less_leEq; Apply recip_resp_pos; Assumption.
Apply div_wd; [Algebra | Apply eq_symmetric_unfolded; Apply AbsIR_eq_x; Apply less_leEq; Assumption].
Apply ap_imp_less.
Assumption.
Qed.

(* Tex_Prose
Some special cases.
*)

(* Begin_Tex_Verb *)
Lemma AbsIR_recip : (x:IR)(H,Ha:?)(AbsIR One[/]x[//]H)[=]One[/](AbsIR x)[//]Ha.
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with (AbsIR One)[/](AbsIR x)[//]Ha.
Apply AbsIR_division.
Apply div_wd.
2:Algebra.
Apply AbsIR_eq_x; Apply less_leEq; Apply pos_one.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_div_two : (x:IR)(AbsIR x[/]TwoNZ)[=](AbsIR x)[/]TwoNZ.
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with (AbsIR x)[/](AbsIR Two)[//](AbsIR_resp_ap_zero ? (ap_symmetric_unfolded ? ? ? (less_imp_ap ? ? ? (pos_two ?)))).
Apply AbsIR_division.
Apply div_wd.
Algebra.
Apply AbsIR_eq_x; Apply less_leEq; Apply pos_two.
Qed.

(* Tex_Prose
Cauchy-Schwartz for IR and variants on that subject.
*)

(* Begin_Tex_Verb *)
Lemma triangle_IR: (x,y:IR) (AbsIR (x[+]y)) [<=] ((AbsIR x)[+](AbsIR y)).
(* End_Tex_Verb *)
Intros.
Step (sqrt (x[+]y)[^](2) (sqr_nonneg ? x[+]y)).
Stepr (sqrt x[^](2) (sqr_nonneg ? x))[+](sqrt y[^](2) (sqr_nonneg ? y)).
Apply power_cancel_leEq with (2). Auto.
Step Zero[+](Zero::IR). Apply plus_resp_leEq_both; Apply sqrt_nonneg.
Step (x[+]y)[^](2).
RStep x[^](2)[+]y[^](2)[+]Two[*](x[*]y).
RStepr (sqrt x[^](2) (sqr_nonneg (IR) x))[^](2)[+]
  (sqrt y[^](2) (sqr_nonneg (IR) y))[^](2)[+]
    Two[*]((sqrt x[^](2) (sqr_nonneg (IR) x))[*](sqrt y[^](2) (sqr_nonneg (IR) y))).
Apply plus_resp_leEq_both.
Stepr x[^](2)[+]y[^](2). Apply leEq_reflexive.
Apply mult_resp_leEq_lft.
Apply power_cancel_leEq with (2). Auto.
Apply mult_resp_nonneg; Apply sqrt_nonneg.
RStepr (sqrt x[^](2) (sqr_nonneg ? x))[^](2)[*]
  (sqrt y[^](2) (sqr_nonneg ? y))[^](2).
Stepr x[^](2)[*]y[^](2).
Step x[^](2)[*]y[^](2).
Apply leEq_reflexive.
Apply less_leEq. Apply pos_two.
Qed.

(* Begin_Tex_Verb *)
Lemma triangle_SumIR : (k,l:nat)(s:nat->IR)(le k (S l)) ->
  (AbsIR (Sum k l s)) [<=] (Sum k l [i:nat](AbsIR (s i))).
(* End_Tex_Verb *)
Intros. Induction l; Intros.
Generalize (toCle ?? H); Clear H; Intro H.
Inversion H.
Unfold Sum. Unfold Sum1. Simpl.
RStepr (Zero::IR).
Stepr (AbsIR Zero).
Apply eq_imp_leEq. Apply AbsIR_wd. Rational.
Inversion H1.
Unfold Sum. Unfold Sum1. Simpl.
RStepr (ABSIR (s (0))).
Apply eq_imp_leEq. Apply AbsIR_wd. Rational.
Elim (le_lt_eq_dec k (S (S l))); Try Intro y.
Apply leEq_wdl with (AbsIR (Sum k l s)[+](s (S l))).
Apply leEq_wdr with (Sum k l [i:nat](AbsIR (s i)))[+](AbsIR (s (S l))).
Apply leEq_transitive with (AbsIR (Sum k l s))[+](AbsIR (s (S l))).
Apply triangle_IR.
Apply plus_resp_leEq. Apply Hrecl. Auto with arith.
Apply eq_symmetric_unfolded.
Apply Sum_last with f := [i:nat](AbsIR (s i)).
Apply AbsIR_wd.
Apply eq_symmetric_unfolded. Apply Sum_last.
Rewrite y.
Unfold Sum. Unfold Sum1. Simpl.
RStepr (Zero::IR).
Stepr (AbsIR Zero).
Apply eq_imp_leEq. Apply AbsIR_wd. Rational.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma triangle_IR_minus : (x,y:IR)(AbsIR x[-]y)[<=](AbsIR x)[+](AbsIR y).
(* End_Tex_Verb *)
Intros.
Unfold cg_minus.
Apply leEq_wdr with (AbsIR x)[+](AbsIR [--]y).
Apply triangle_IR.
Apply bin_op_wd_unfolded.
Algebra.
Unfold AbsIR; Simpl; Unfold ABSIR.
Apply eq_transitive_unfolded with (Max [--]y y).
Apply bin_op_wd_unfolded; Algebra.
Apply Max_comm.
Qed.

(* Begin_Tex_Verb *)
Lemma weird_triangleIR : (x,y:IR)(AbsIR x)[-](AbsIR y[-]x)[<=](AbsIR y).
(* End_Tex_Verb *)
Intros.
Apply shift_minus_leEq.
Simpl; Unfold ABSIR; Apply Max_leEq.
RStep y[+][--](y[-]x).
Apply plus_resp_leEq_both; [Apply lft_leEq_Max | Apply rht_leEq_Max].
RStep [--]y[+](y[-]x).
Apply plus_resp_leEq_both; [Apply rht_leEq_Max | Apply lft_leEq_Max].
Qed.

(* Begin_Tex_Verb *)
Lemma triangle_IR_minus' : (x,y:IR)(AbsIR x)[-](AbsIR y)[<=](AbsIR x[-]y).
(* End_Tex_Verb *)
Intros.
EApply leEq_wdr.
2: Apply AbsIR_minus.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Apply weird_triangleIR.
Qed.

(* Begin_Tex_Verb *)
Lemma triangle_SumxIR : (n:nat)(f:(i:nat)(lt i n)->IR)
  (AbsIR (Sumx f))[<=](Sumx [i:nat][H:(lt i n)](AbsIR (f i H))).
(* End_Tex_Verb *)
Induction n.
Intros; Simpl.
Apply eq_imp_leEq; Apply AbsIRz_isz.
Clear n; Intros.
Simpl; EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq.
EApply leEq_wdr.
Apply H.
Apply Sumx_wd.
Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma triangle_Sum2IR : (m,n:nat)(le m (S n))->
  (f:(i:nat)(le m i)->(le i n)->IR)
  (AbsIR (Sum2 f))[<=](Sum2 [i,Hm,Hn:?](AbsIR (f i Hm Hn))).
(* End_Tex_Verb *)
Intros.
Unfold Sum2.
EApply leEq_wdr.
Apply triangle_SumIR.
Assumption.
Apply Sum_wd'.
Assumption.
Intros.
Elim (le_lt_dec m i); Intro; [Simpl | ElimType False; Apply (le_not_lt m i); Auto with arith].
Elim (le_lt_dec i n); Intro; [Simpl | ElimType False; Apply (le_not_lt i n); Auto with arith].
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_str_bnd_AbsIR : (a,b,e:IR)
  ((AbsIR a[-]b)[<]e)->((AbsIR b)[<](AbsIR a)[+]e).
(* End_Tex_Verb *)
Intros.
Apply shift_less_plus'.
EApply leEq_less_trans.
Apply triangle_IR_minus'.
EApply less_wdl; [Apply H | Apply AbsIR_minus].
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_bnd_AbsIR : (a,b,e:IR)
  ((AbsIR a[-]b)[<=]e)->((AbsIR b)[<=](AbsIR a)[+]e).
(* End_Tex_Verb *)
Intros.
Apply shift_leEq_plus'.
EApply leEq_transitive.
Apply triangle_IR_minus'.
EApply leEq_wdl; [Apply H | Apply AbsIR_minus].
Qed.

End Absolute_Props.

Section Consequences.

(* Tex_Prose
\section{Cauchy sequences}

With these results, we can also prove that the sequence of reciprocals of a Cauchy sequence that is never zero and whose Limit is not zero is also a Cauchy sequence.
*)

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_recip :
  (seq:nat->IR)(y:IR)(Cauchy_Lim_prop2 seq y)->
  (Hn:(n:nat)(seq n)[#]Zero)(Hy:y[#]Zero)
  (Cauchy_Lim_prop2 [n:nat]One[/]?[//](Hn n) One[/]?[//]Hy).
(* End_Tex_Verb *)
Intros.
Red; Red in H.
Intros eps He.
Cut {n0:nat | (n:nat)(le n0 n)->(AbsIR y)[/]TwoNZ[<=](AbsIR (seq n))}.
Intro.
Elim H0; Clear H0; Intros n0 Hn0.
Cut Zero[<](eps[/]TwoNZ)[*]((AbsIR y)[*](AbsIR y)).
Intro.
Elim (H ? H0); Clear H.
Intros N HN.
Exists (max N n0).
Intros.
Apply AbsIR_imp_AbsSmall.
Apply leEq_wdl with (One[/]?[//](AbsIR_resp_ap_zero ? (Hn m)))[*](One[/]?[//](AbsIR_resp_ap_zero ? Hy))[*](AbsIR (seq m)[-]y).
RStepr (Two[/]?[//](AbsIR_resp_ap_zero ? Hy))[*](One[/]?[//](AbsIR_resp_ap_zero ? Hy))[*]((eps[/]TwoNZ)[*]((AbsIR y)[*](AbsIR y))).
Apply mult_resp_leEq_both.
Step (Zero::IR)[*]Zero; Apply mult_resp_leEq_both; Try Apply leEq_reflexive.
Apply less_leEq; Apply recip_resp_pos; Apply AbsIR_pos; Apply Hn.
Apply less_leEq; Apply recip_resp_pos; Apply AbsIR_pos; Apply Hy.
Apply AbsIR_nonneg.
Apply mult_resp_leEq_rht.
RStepr One[/]?[//](div_resp_ap_zero_rev ??? (two_ap_zero ?) (AbsIR_resp_ap_zero ? Hy)).
Apply recip_resp_leEq.
Apply pos_div_two; Apply AbsIR_pos; Apply Hy.
Apply Hn0.
Apply le_trans with (max N n0); Auto with arith.
Apply less_leEq; Apply recip_resp_pos; Apply AbsIR_pos; Apply Hy.
Apply AbsSmall_imp_AbsIR.
Apply HN.
Apply le_trans with (max N n0); Auto with arith.
Apply eq_transitive_unfolded with (AbsIR (One[/]?[//](Hn m)))[*](AbsIR (One[/]?[//]Hy))[*](AbsIR y[-](seq m)).
Repeat Apply mult_wd; Apply eq_symmetric_unfolded.
Apply AbsIR_recip.
Apply AbsIR_recip.
Apply AbsIR_minus.
Apply eq_transitive_unfolded with (AbsIR (One[/]?[//](Hn m))[*](One[/]?[//]Hy)[*](y[-](seq m))).
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_wd_lft.
Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply AbsIR_wd.
Rational.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive.
Apply pos_div_two; Assumption.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive; Apply AbsIR_pos; Apply Hy.
Cut {n0:nat | (n:nat)(le n0 n)->(AbsSmall (AbsIR y)[/]TwoNZ (seq n)[-]y)}.
2: Apply H.
2: EApply less_wdr.
3: Apply AbsIR_div_two.
2: Apply AbsIR_pos.
2: Apply div_resp_ap_zero_rev; Apply Hy.
Intro.
Elim H0; Intros n0 Hn0; Clear H0; Exists n0; Intros.
Apply leEq_transitive with (AbsIR y)[-](AbsIR (seq n)[-]y).
Apply shift_leEq_minus; Apply shift_plus_leEq'.
RStepr (AbsIR y)[/]TwoNZ.
Apply AbsSmall_imp_AbsIR.
Apply Hn0; Assumption.
Apply weird_triangleIR.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_recip : (seq:(CauchySeq IR))(Hn:(n:nat)(seq n)[#]Zero)
  (Hy:(Lim seq)[#]Zero)(Cauchy_prop [n:nat]One[/]?[//](Hn n)).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_prop2_prop.
Exists One[/]?[//]Hy.
Apply Cauchy_Lim_recip.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_recip : (seq:(CauchySeq IR))
  (Hn:(n:nat)(seq n)[#]Zero)(Hy:(Lim seq)[#]Zero)
  (Lim (Build_CauchySeq IR ? (Cauchy_recip seq Hn Hy)))[=]
    One[/]?[//]Hy.
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded; Apply Limits_unique.
Simpl; Apply Cauchy_Lim_recip.
Apply Cauchy_complete.
Qed.

End Consequences.
