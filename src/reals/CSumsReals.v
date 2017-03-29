(* $Id: CSumsReals.v,v 1.11 2003/03/11 13:36:16 lcf Exp $ *)

Require Export CReals1.

Opaque IR.

(* Tex_Prose
\chapter{Sums over Reals}

\begin{convention}
Let \verb!c! be a real.
\end{convention}

Here we prove that
\[\Sigma_{m\leq i \leq n}~c^k = \frac{c^{n+1}-c^m}{c-1}.\]
*)

Section Sums_over_Reals.

Variable c: IR.

(* Begin_Tex_Verb *)
Lemma Sum0_c_exp : (H:c[-]One[#]Zero)(m:nat)
        ((Sum0 m [i:nat](c[^]i)) [=] ((c[^]m [-] One)[/](c [-] One)[//]H)).
(* End_Tex_Verb *)
Intros.
Elim m.
Simpl.
Rational.
Simpl.
Intros.
Step ((nexp IR n c)[-]One)[/](c[-]One)[//]H [+](nexp IR n c).
Rational.
Qed.

Hints Resolve Sum0_c_exp.

(* Begin_Tex_Verb *)
Lemma Sum_c_exp : (H:c[-]One[#]Zero)
                      (m,n:nat)((Sum m n [i:nat](c[^]i))
                      [=]((c[^](S n) [-] c[^]m)[/](c [-] One)[//]H)).
(* End_Tex_Verb *)
Intros.
Unfold Sum.
Unfold Sum1.
Step_lft ((c[^](S n) [-] One)[/](c [-] One)[//]H) [-]
         ((c[^]m [-] One)[/](c [-] One)[//]H).
Rational.
Qed.
Hints Resolve Sum_c_exp.

(* Tex_Prose
The following formulation is often more useful if $c<1$.
*)
(* Begin_Tex_Verb *)
Lemma Sum_c_exp' : (H:One[-]c[#]Zero)
                       (m,n:nat)((Sum m n [i:nat](c[^]i))
		        [=]((c[^]m [-] c[^](S n))[/](One [-] c)[//]H)).
(* End_Tex_Verb *)
Intros.
Cut c[-]One [#]Zero.
Intro.
Step_lft ((c[^](S n) [-] c[^]m)[/](c [-] One)[//]H0).
Rational.
RStep [--](One[-]c).
Apply inv_resp_ap_zero.
Assumption.
Qed.

Hints Resolve Sum_c_exp'.

End Sums_over_Reals.

Hints Resolve Sum0_c_exp Sum_c_exp Sum_c_exp' : algebra.

(* Begin_Tex_Verb *)
Lemma diff_is_Sum0 : (s:nat->IR)(n:nat)
  ((s n)[-](s O)) [=] (Sum0 n [i:nat](s (S i))[-](s i)).
(* End_Tex_Verb *)
Proof.
Intros s.
Induction n.
Simpl. Algebra.
Intros.
Simpl.
Apply eq_transitive_unfolded with
	(((s (S n0))[-] (s(n0))) [+] ((s(n0))[-](s (0)))).
Rational.
Apply eq_transitive_unfolded with
	((s (S n0))[-](s n0)
            [+](Sum0 n0 [i:nat](s (S i))[-](s i)) ).
Exact (plus_resp_eq ? ? ? ? H).
Rational.
Qed.


(* Begin_Tex_Verb *)
Lemma diff_is_sum : (s:nat->IR)(N,m:nat)(lt N m) ->
  ((s m)[-](s N)) [=] (Sum N (pred m) [i:nat](s (S i))[-](s i)).
(* End_Tex_Verb *)
Proof.
Intros s N m ltNm.
Unfold Sum. Unfold Sum1.
Generalize (S_pred m N ltNm).
Intro H.
Rewrite <- H.
Generalize (diff_is_Sum0 s N).
Intro HsN.
Generalize (diff_is_Sum0 s m).
Intro Hsm.
Apply eq_transitive_unfolded with (((s m) [-] (s O)) [-] ((s N) [-] (s O))).
Rational.
Apply (cg_minus_wd IR).
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_pres_less : (s,t:nat->IR)((i:nat)((s i)[<](t i)))-> 
  (n:nat)(Sum0 n s) [<=] (Sum0 n t).
(* End_Tex_Verb *)
Proof.
Intros s t H.
Induction n.
Simpl.
Exact (leEq_reflexive ? ?).
Intros.
Simpl.
Apply leEq_transitive with ((Sum0 n0 t)[+](s n0)).
Apply plus_resp_leEq.
Assumption.
Apply plus_resp_leEq_lft.
Apply less_leEq;Exact (H ?).
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_pres_less : (s,t:nat->IR)
  ((i:nat)((s i)[<](t i))) -> (N,m:nat)
  (le N m) -> ((Sum N m s) [<=] (Sum N m t)).
(* End_Tex_Verb *)
Intros.
Apply less_leEq.
Apply Sum_resp_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_pres_leEq : (s,t:nat->IR)
  ((i:nat)((s i)[<=](t i))) -> (N,m:nat)
  (le N m) -> ((Sum N m s) [<=] (Sum N m t)).
(* End_Tex_Verb *)
Intros.
Apply Sum_resp_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_comm_scal : (s:nat->IR;a:IR)(m:nat)
  (Sum0 m [i:nat]((s i)[*]a)) [=] (Sum0 m [i:nat](s i))[*]a.
(* End_Tex_Verb *)
Intros. Induction m; Intros.
Simpl. Algebra.
Simpl. Step_final (Sum0 m [i:nat](s i))[*]a[+](s m)[*]a.
Qed.

Hints Resolve Sum0_comm_scal : algebra.

(* Begin_Tex_Verb *)
Lemma Sum_comm_scal : (s:nat->IR;a:IR)(N,m:nat)
  (Sum N m [i:nat]((s i)[*]a)) [=] (Sum N m [i:nat](s i))[*]a.
(* End_Tex_Verb *)
Unfold Sum. Unfold Sum1. Intros.
Step_final (Sum0 (S m) [i:nat](s i))[*]a[-](Sum0 N [i:nat](s i))[*]a.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_comm_scal' : (c:IR)(x:nat->IR)(m:nat)
  (Sum0 m [i:nat]c[*](x i)) [=] c[*](Sum0 m x).
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with (Sum0 m [n:nat](x n))[*]c.
2: Step_rht (Sum0 m x)[*]c; Apply mult_wd_lft.
2: Apply Sum0_wd; Algebra.
EApply eq_transitive_unfolded.
2: Apply Sum0_comm_scal.
Apply Sum0_wd; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_comm_scal' : (c:IR)(x:nat->IR)(m,n:nat)
  (Sum m n [i:nat]c[*](x i)) [=] c[*](Sum m n x).
(* End_Tex_Verb *)
Intros.
Unfold Sum Sum1.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply dist_2a.
Apply cg_minus_wd; Apply Sum0_comm_scal'.
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_comm_scal' : (n:nat)(c:IR)(f:(i:nat)(lt i n)->IR)
  (Sumx [i:nat][H:(lt i n)]c[*](f i H)) [=] c[*](Sumx f).
(* End_Tex_Verb *)
Induction n.
Intros; Simpl; Algebra.
Clear n; Intros; Simpl.
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply ring_dist_unfolded.
Apply bin_op_wd_unfolded.
Apply H with f:=[i:nat][l:(lt i n)](f i (lt_S ?? l)).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum2_comm_scal' : (c:IR)(m,n:nat)(le m (S n))->(f:?)
  (Sum2 [i:nat][Hm:(le m i)][Hn:(le i n)]c[*](f i Hm Hn)) [=] c[*](Sum2 f).
(* End_Tex_Verb *)
Intros; Unfold Sum2.
EApply eq_transitive_unfolded.
2: Apply Sum_comm_scal'.
Apply Sum_wd'.
Assumption.
Intros.
Elim (le_lt_dec m i); Intros; Simpl.
Elim (le_lt_dec i n); Intros; Simpl; Algebra.
Algebra.
Qed.
