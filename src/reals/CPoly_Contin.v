(* $Id: CPoly_Contin.v,v 1.12 2003/03/11 13:36:15 lcf Exp $ *)

(* Tex_Prose
\chapter{Continuity of polynomials}
*)

Require Export RealFuncts.
Require Export CPolynomials.

Opaque IR.

(* Begin_Tex_Verb *)
Lemma mult_op_contin : 
   (f,g,h:(CSetoid_un_op IR))(contin f)->(contin g)->
   ((x:IR)((f x)[*](g x) [=] (h x))) -> (contin h).
(* End_Tex_Verb *)
Intros f g h f_contin g_contin  f_g_h.
Unfold contin in f_contin.
Unfold continAt in f_contin.
Unfold funLim in f_contin.
Unfold contin in g_contin.
Unfold continAt in g_contin.
Unfold funLim in g_contin.
Unfold contin. Unfold continAt. Unfold funLim.
Intros.
Elim (mult_contin ? (f x) (g x) e H). Intro b. Intros H0 H1.
Elim H1. Clear H1. Intro c. Intros H1 H2.
Elim (f_contin x b H0). Clear f_contin. Intro d'. Intros H3 H4.
Elim (g_contin x c H1). Clear g_contin. Intro d''. Intros H5 H6.
Exists (Min d' d'').
Apply less_Min; Auto. Intro x'. Intros.
Stepr (f x)[*](g x)[-](f x')[*](g x').
Apply H2.
Apply H4. Apply AbsSmall_leEq_trans with (Min d' d''); Auto. Apply Min_leEq_lft.
Apply H6. Apply AbsSmall_leEq_trans with (Min d' d''); Auto. Apply Min_leEq_rht.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_contin :
  (R:COrdField)(x,y,e:R)(Zero [<] e) ->
    {c:R & (Zero [<] c) & { d:R & (Zero [<] d) |
      (x',y':R)(AbsSmall c x[-]x') -> (AbsSmall d y[-]y') ->
        (AbsSmall e (x[+]y)[-](x'[+]y'))}}.
(* End_Tex_Verb *)
Intros.
Cut Zero [<] e[/]TwoNZ. Intro.
Exists e[/]TwoNZ. Auto.
Exists e[/]TwoNZ. Auto.
Intros.
Apply AbsSmall_wd_rht_unfolded with (x[-]x')[+](y[-]y').
Apply AbsSmall_eps_div_two; Auto.
Rational.
Apply div_resp_pos. Apply pos_two. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_op_contin : 
   (f,g,h:(CSetoid_un_op IR))(contin f)->(contin g)->
   ((x:IR)((f x)[+](g x) [=] (h x))) -> (contin h).
(* End_Tex_Verb *)
Intros f g h f_contin g_contin  f_g_h.
Unfold contin in f_contin.
Unfold continAt in f_contin.
Unfold funLim in f_contin.
Unfold contin in g_contin.
Unfold continAt in g_contin.
Unfold funLim in g_contin.
Unfold contin. Unfold continAt. Unfold funLim.
Intros.
Elim (plus_contin ? (f x) (g x) e H). Intro b. Intros H0 H1.
Elim H1. Clear H1. Intro c. Intros H1 H2.
Elim (f_contin x b H0). Clear f_contin. Intro d'. Intros H3 H4.
Elim (g_contin x c H1). Clear g_contin. Intro d''. Intros H5 H6.
Exists (Min d' d'').
Apply less_Min; Auto. Intro x'. Intros H10.
Stepr ((f x)[+](g x))[-]((f x')[+](g x')).
Apply H2.
Apply H4. Apply AbsSmall_leEq_trans with (Min d' d''); Auto. Apply Min_leEq_lft.
Apply H6. Apply AbsSmall_leEq_trans with (Min d' d''); Auto. Apply Min_leEq_rht.
Qed.

(* Begin_Tex_Verb *)
Lemma linear_op_contin : 
   (f,g:(CSetoid_un_op IR))(a:IR)(contin f)->
   ((x:IR)(x[*](f x)[+]a [=] (g x))) -> (contin g).
(* End_Tex_Verb *)
Intros f g a f_contin f_g.
Unfold contin in f_contin.
Unfold continAt in f_contin.
Unfold funLim in f_contin.
Unfold contin. Unfold continAt. Unfold funLim.
Intros.
Elim (mult_contin ? x (f x) e). Intro d'. Intros H0 H1.
Elim H1. Clear H1. Intro c. Intros H1 H2.
Elim (f_contin x c). Clear f_contin. Intro d''. Intros H3 H4.
Exists (Min d' d''). 
Apply less_Min; Auto. Intro x'. Intros H8.
Stepr (x[*](f x)[+]a)[-](x'[*](f x')[+]a).
RStepr x[*](f x)[-]x'[*](f x').
Apply H2. Clear H2.
Apply AbsSmall_leEq_trans with (Min d' d''); Auto. Apply Min_leEq_lft.
Apply H4. Clear H4.
Apply AbsSmall_leEq_trans with (Min d' d''); Auto. Apply Min_leEq_rht.
Auto. Auto. 
Qed.

(* Begin_Tex_Verb *)
Lemma cpoly_op_contin : (g : (cpoly IR))(contin (cpoly_csetoid_op ? g)).
(* End_Tex_Verb *)
Intro g.
Elim g.
Unfold contin. Unfold continAt. Unfold funLim.
Intros.
Exists (One::IR). Apply pos_one.
Intros.
Simpl.
Unfold AbsSmall.
Split; Apply less_leEq.
RStepr [--](Zero::IR). Apply inv_resp_less. Auto.
Step (Zero::IR). Auto.
Intros a f. Intros.
Apply linear_op_contin with (cpoly_csetoid_op ? f) a. Auto.
Intros. Simpl. Rational.
Qed.
