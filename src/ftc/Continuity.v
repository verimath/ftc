(* $Id: Continuity.v,v 1.18 2003/03/13 12:06:17 lcf Exp $ *)

Require Export NRootIR.
Require Export FunctSums.

Section Definitions_and_Basic_Results.

(* Tex_Prose
\chapter{Continuity}

Constructively, continuity is the most fundamental property of any function---so strongly that no example is known of a constructive function that is not continuous.  However, the classical definition of continuity is not good for our purposes, as it is not true, for example, that a function which is continuous in a compact interval is uniformly continuous in that same interval (for a discussion of this see Bishop [1967]).  Thus, our notion of continuity will be the uniform one\footnote{Similar remarks apply to convergence of sequences of functions, which we will define ahead, and elsewhere; we will refrain from discussing this issue at those places.}.

\begin{convention} Throughout this section, \verb!a! and \verb!b! will be real numbers, \verb!I! will denote the compact interval $[a,b]$ and \verb!F,G,H! will denote arbitrary partial functions with domains respectively \verb!P,Q! and \verb!R!.
\end{convention}

\section{Definitions and Basic Results}

Here we define continuity and prove some basic properties of continuous functions.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variable F:PartIR.
Local P:=(Pred F).

(* Begin_Tex_Verb *)
Definition Continuous_I := (included I P)*
  ((e:IR)(Zero[<]e)->{d:IR & (Zero[<]d) | 
    (x,y:IR)(I x)->(I y)->(Hx,Hy:?)((AbsIR x[-]y)[<=]d)->
      ((AbsIR (F x Hx)[-](F y Hy))[<=]e)}).
(* End_Tex_Verb *)

(* Tex_Prose
For convenience, we distinguish the two properties of continuous functions.
*)

(* Begin_Tex_Verb *)
Lemma contin_imp_inc : Continuous_I->(included (Compact Hab) P).
(* End_Tex_Verb *)
Intro; Elim H; Intros; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma contin_prop : Continuous_I->
  ((e:IR)(Zero[<]e)->{d:IR & (Zero[<]d) |
  (x,y:IR)(I x)->(I y)->(Hx,Hy:?)((AbsIR x[-]y)[<=]d)->
    ((AbsIR (F x Hx)[-](F y Hy))[<=]e)}).
(* End_Tex_Verb *)
Intro; Elim H; Do 2 Intro; Assumption.
Qed.

(* Tex_Prose
Assume \verb!F! to be continuous in \verb!I!.  Then it has a least upper bound and a greater lower bound on \verb!I!.
*)

Hypothesis contF : Continuous_I.

Local Hinc':=(contin_imp_inc contF).

(* Begin_Tex_Verb *)
Lemma Continuous_I_imp_tb_image : (totally_bounded
  [x:IR]{y:IR & {Hy:(I y) | x[=](F y (Hinc' y Hy))}}).
(* End_Tex_Verb *)
Cut (totally_bounded (compact a b Hab)).
2: Apply compact_is_totally_bounded; Assumption.
Intro.
Elim contF; Intros H0 H1.
Split; Intros.
Inversion_clear H.
Inversion_clear H2.
Exists (Part (FRestr H0) x H).
Exists x; Exists H; Simpl; Rational.
Elim (H1 ? H2).
Intros d H3 H4.
Clear H1.
Elim H; Clear H.
Intros non_empty H.
Elim H with d; Clear H.
Intros l Hl' Hl.
2: Assumption.
Exists (map2 F l [x:IR][Hx:(member x l)](H0 x (Hl' x Hx))).
Intros.
Clear Hl; Induction l.
ElimType CFalse; Assumption.
Simpl in H; Inversion_clear H.
Cut (x:IR)(member x l)->(compact a b Hab x); Intros.
Apply Hrecl with H.
EApply map2_wd.
Apply H1.
Apply Hl'; Left; Assumption.
Exists a0.
Exists (Hl' a0 (inright (member a0 l) a0[=]a0 (eq_reflexive_unfolded IR a0))).
EApply eq_transitive_unfolded.
Apply H1.
Rational.
Intros; Simpl.
Inversion_clear H.
Elim H1; Clear H1; Intros Hy H1.
Elim (Hl x0 Hy); Intros x1 H H5.
Exists (F x1 (H0 x1 (Hl' x1 H))).
Apply map2_pres_member; Assumption.
Stepr (F x0 (Hinc' x0 Hy))[-](F x1 (H0 x1 (Hl' x1 H))).
Apply AbsIR_imp_AbsSmall.
Apply H4.
Assumption.
Apply Hl'; Assumption.
Apply AbsSmall_imp_AbsIR; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_imp_lub :
  {x:IR & (fun_lub_IR (FRestr Hinc') x)}.
(* End_Tex_Verb *)
Cut {z:IR & (set_lub_IR [x:IR]{y:IR & {Hy:(I y) | x[=]((FRestr Hinc') y Hy)}} z)}.
Intro.
Inversion_clear H.
Exists x.
Inversion_clear H0.
Split.
Intros.
Apply H.
Exists x0; Exists Hx; Algebra.
Intros.
Elim (H1 e H0).
Intros; Clear H1.
Elim p; Clear p; Intros y Hy.
Elim Hy; Clear Hy; Intros Hy Hy'.
Exists y; Exists Hy.
Step x[-]x0; Assumption.
Apply totally_bounded_has_lub.
Apply Continuous_I_imp_tb_image.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_imp_glb :
  {x:IR & (fun_glb_IR (FRestr Hinc') x)}.
(* End_Tex_Verb *)
Cut {z:IR & (set_glb_IR [x:IR]{y:IR & {Hy:(I y) | x[=]((FRestr Hinc') y Hy)}} z)}.
Intro.
Inversion_clear H.
Exists x.
Inversion_clear H0.
Split.
Intros.
Apply H.
Exists x0; Exists Hx; Algebra.
Intros.
Elim (H1 e H0).
Intros; Clear H1.
Elim p; Clear p; Intros y Hy.
Elim Hy; Clear Hy; Intros Hy Hy'.
Exists y; Exists Hy.
Step x0[-]x; Assumption.
Apply totally_bounded_has_glb.
Apply Continuous_I_imp_tb_image.
Qed.

(* Tex_Prose
We now make this glb and lub into operators.
*)

(* Begin_Tex_Verb *)
Definition lub_funct := (ProjS1 Continuous_I_imp_lub).
Definition glb_funct := (ProjS1 Continuous_I_imp_glb).
(* End_Tex_Verb *)

(* Tex_Prose
We already defined a notion of lub and glb for functions; here we define them for compact intervals.
*)

(* Begin_Tex_Verb *)
Definition fun_lub [z:IR] := (included I P)*
  ({(x:IR)(I x)->(Hx:(P x))((F x Hx)[<=]z)}*
  ((e:IR)(Zero[<]e)->{x:IR & {Hx:(I x) &
    (Hx':(P x))((z[-](F x Hx'))[<]e)}})).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition fun_glb [z:IR] := (included I P)*
  ({(x:IR)(I x)->(Hx:(P x))(z[<=](F x Hx))}*
  ((e:IR)(Zero[<]e)->{x:IR & {Hx:(I x) &
    (Hx':(P x))(((F x Hx')[-]z)[<]e)}})).
(* End_Tex_Verb *)

(* Tex_Prose
These operatores have the expected properties.
*)

(* Begin_Tex_Verb *)
Lemma lub_is_lub : (fun_lub_IR (FRestr Hinc') lub_funct).
(* End_Tex_Verb *)
Intros.
Exact (ProjS2 Continuous_I_imp_lub).
Qed.

(* Begin_Tex_Verb *)
Lemma lub_is_lub' : (fun_lub lub_funct).
(* End_Tex_Verb *)
Intros.
Elim lub_is_lub; Intros H0 H1.
Split.
Apply Hinc'.
Split.
Intros.
Simpl in H0.
EApply leEq_wdl.
Apply (H0 x H).
Rational.
Intros e He; Elim (H1 e He); Intros x Hx.
Elim Hx; Clear Hx; Intros Hx Hx'.
Simpl; Simpl in Hx; Simpl in Hx'.
Exists x; Exists Hx.
Intro; EApply less_wdl.
Apply Hx'.
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma glb_is_glb : (fun_glb_IR (FRestr Hinc') glb_funct).
(* End_Tex_Verb *)
Intros.
Exact (ProjS2 Continuous_I_imp_glb).
Qed.

(* Begin_Tex_Verb *)
Lemma glb_is_glb' : (fun_glb glb_funct).
(* End_Tex_Verb *)
Intros.
Elim glb_is_glb; Intros H1 H2.
Split.
Apply Hinc'.
Split.
Intros.
Simpl in H1.
EApply leEq_wdr.
Apply (H1 x H).
Rational.
Intros e He; Elim (H2 e He); Intros x Hx.
Elim Hx; Clear Hx; Intros Hx Hx'.
Simpl; Simpl in Hx; Simpl in Hx'.
Exists x; Exists Hx.
Intro; EApply less_wdl.
Apply Hx'.
Rational.
Qed.

(* Tex_Prose
The \emph{norm} of a function is defined as being the supremum of its absolute value; that is equivalent to the following definition (which is often more convenient to use).
*)

(* Begin_Tex_Verb *)
Definition Norm_Funct := (Max lub_funct [--]glb_funct).
(* End_Tex_Verb *)

(* Tex_Prose
The norm effectively bounds the absolute value of a function.
*)

(* Begin_Tex_Verb *)
Lemma norm_bnd_AbsIR : (x:IR)(I x)->
  (Hx:(P x))(AbsIR (F x Hx))[<=]Norm_Funct.
(* End_Tex_Verb *)
Intros.
Cut (fun_lub lub_funct).
Cut (fun_glb glb_funct).
Intros; Simpl; Unfold ABSIR.
Apply Max_leEq.
Apply leEq_transitive with lub_funct.
Inversion_clear H1.
Elim H3; Clear H2 H3; Intros H2 H3.
Simpl in H2; Apply H2; Assumption.
Unfold Norm_Funct; Apply lft_leEq_Max.
Apply leEq_transitive with [--]glb_funct.
Apply inv_resp_leEq.
Inversion_clear H0.
Elim H3; Clear H2 H3; Intros H2 H3.
Simpl in H2; Apply H2; Assumption.
Unfold Norm_Funct; Apply rht_leEq_Max.
Apply glb_is_glb'.
Apply lub_is_lub'.
Qed.

(* Tex_Prose
The following is another way of characterizing the norm:
*)

(* Begin_Tex_Verb *)
Lemma Continuous_I_imp_abs_lub : {z:IR |
   (x:IR)(I x)->(Hx:(P x))(AbsIR (F x Hx))[<=]z}.
(* End_Tex_Verb *)
Exists Norm_Funct.
Exact norm_bnd_AbsIR.
Qed.

(* Tex_Prose
We now prove some basic properties of the norm---namely that it is positive, and that it provides a least upper bound for the absolute value of its argument.
*)

(* Begin_Tex_Verb *)
Lemma positive_norm : Zero[<=]Norm_Funct.
(* End_Tex_Verb *)
Apply leEq_transitive with (AbsIR ((FRestr Hinc') a (compact_inc_lft ???))).
Apply AbsIR_nonneg.
Simpl; Apply norm_bnd_AbsIR; Unfold I; Apply compact_inc_lft.
Qed.

(* Begin_Tex_Verb *)
Lemma norm_fun_lub : (e:IR)(Zero[<]e)->{x:IR & {Hx:(I x)
  & (Hx':(P x))(Norm_Funct[-]e[<](AbsIR (F x Hx')))}}.
(* End_Tex_Verb *)
Intros.
Cut {x:IR & {Hx:(I x) & (Hx':(P x))(Norm_Funct[<](AbsIR (F x Hx'))[+]e)}}.
Intro.
Elim H0; Intros y Hy.
Elim Hy; Clear H0 Hy; Intros Hy Hy'.
Exists y; Exists Hy.
Intro; Apply shift_minus_less; Apply Hy'.
Cut (fun_lub lub_funct).
Cut (fun_glb glb_funct).
Intros.
Cut {x:IR & {Hx:(I x) & (Hx':(P x))(F x Hx')[<](glb_funct[+]e[/]TwoNZ)}}.
Cut {x:IR & {Hx:(I x) & (Hx':(P x))(lub_funct[-]e[/]TwoNZ)[<](F x Hx')}}.
Intros.
Elim H2; Intros x Hx.
Elim Hx; Clear H2 Hx; Intros Hx Hx0.
Elim H3; Intros x' Hx'.
Elim Hx'; Clear H3 Hx'; Intros Hx' Hx'0.
Cut (Zero[<]([--]glb_funct)[-]lub_funct)+(([--]glb_funct)[-]lub_funct[<]e[/]TwoNZ).
Intro.
2: Apply cotrans_less_unfolded; Apply pos_div_two; Assumption.
Inversion_clear H2.
Exists x'; Exists Hx'.
Unfold Norm_Funct.
Intro; EApply less_wdl.
2: Apply eq_symmetric_unfolded; Apply leEq_imp_Max_is_rht.
Apply shift_less_plus.
RStep [--](glb_funct[+]e).
EApply less_leEq_trans.
2: Apply inv_leEq_AbsIR.
Apply inv_resp_less.
EApply less_transitive_unfolded.
Apply Hx'0 with Hx':=Hx'1.
Apply plus_resp_less_lft.
Apply pos_div_two'; Assumption.
Step Zero[+]lub_funct; Apply less_leEq; Apply shift_plus_less.
Assumption.
Exists x; Exists Hx.
Unfold Norm_Funct.
Intro; Apply less_leEq_trans with lub_funct[+]e[/]TwoNZ.
Apply Max_less.
Apply shift_less_plus'; Step (Zero::IR).
Apply pos_div_two; Assumption.
Apply shift_less_plus'; Assumption.
Apply shift_leEq_plus.
RStep lub_funct[-]e[/]TwoNZ.
EApply leEq_transitive.
Apply less_leEq; Apply Hx0 with Hx':=Hx'1.
Apply leEq_AbsIR.
Inversion_clear H1.
Elim H3; Clear H2 H3; Intros H2 H3.
Simpl in H3.
Elim (H3 ? (pos_div_two ?? H)).
Intros x Hx; Elim Hx; Clear Hx; Intros Hx Hx'.
Exists x; Exists Hx.
Intro; Apply shift_minus_less; Apply shift_less_plus'; Apply Hx'.
Inversion_clear H0.
Elim H3; Clear H2 H3; Intros H2 H3.
Simpl in H3.
Elim (H3 ? (pos_div_two ?? H)).
Intros x Hx; Elim Hx; Clear Hx; Intros Hx Hx'.
Exists x; Exists Hx.
Intro; Apply shift_less_plus'; Apply Hx'.
Apply glb_is_glb'.
Apply lub_is_lub'.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_Norm_Funct : (e:IR)((x:IR)(I x)->
  (Hx:(P x))(AbsIR (F x Hx))[<=]e)->(Norm_Funct[<=]e).
(* End_Tex_Verb *)
Intros.
Stepr Zero[+]e; Apply shift_leEq_plus.
Red; Apply approach_zero_weak.
Intros d Hd.
Apply shift_minus_leEq.
Cut {x:IR & {Hx:(I x) & (Hx':(P x))(Norm_Funct[-]d)[<](AbsIR (F x Hx'))}}.
2: Apply norm_fun_lub; Assumption.
Intro.
Elim H0; Clear H0; Intros x Hx.
Elim Hx; Clear Hx; Intros Hx Hx'.
Apply plus_cancel_leEq_rht with [--](AbsIR (F x (Hinc' x Hx))).
Step Norm_Funct[-](AbsIR (F x (Hinc' x Hx))).
Apply less_leEq; Apply less_leEq_trans with d.
Apply shift_minus_less; Apply shift_less_plus'; Apply Hx'.
RStepr d[+](e[-](AbsIR (F x (Hinc' x Hx)))).
Step d[+]Zero; Apply plus_resp_leEq_lft.
Apply shift_leEq_minus; Step (AbsIR (F x (Hinc' x Hx))); Apply H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma less_Norm_Funct : (e:IR)((x:IR)(I x)->
  (Hx:(P x))(AbsIR (F x Hx))[<]e)->(Norm_Funct[<=]e).
(* End_Tex_Verb *)
Intros.
Apply leEq_Norm_Funct.
Intros; Apply less_leEq; Apply H; Assumption.
Qed.

End Definitions_and_Basic_Results.

Implicits Continuous_I [1 2].
Implicits Norm_Funct [1 2 3 4].

Section Local_Results.

(* Tex_Prose
\section{Algebraic Properties}

We now state and prove some results about continuous functions.  Assume that \verb!I! is included in the domain of both \verb!F! and \verb!G!.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables F,G:PartIR.

Local P:=(Pred F).
Local Q:=(Pred G).

Hypothesis incF : (included (Compact Hab) P).
Hypothesis incG : (included (Compact Hab) Q).

(* Tex_Prose
The first result does not require the function to be continuous; however, its preconditions are easily verified by continuous functions, which justifies its inclusion in this section.
*)

(* Begin_Tex_Verb *)
Lemma cont_no_sign_change : (e:IR)(Zero[<]e)->
  (x,y:IR)(I x)->(I y)->(Hx:(P x))(Hy:(P y))
  ((AbsIR (F x Hx)[-](F y Hy))[<=]e)->(e[<](AbsIR (F x Hx)))->
    ((Zero[<](F x Hx))->(Zero[<](F y Hy)))*
    (((F x Hx)[<]Zero)->((F y Hy)[<]Zero)).
(* End_Tex_Verb *)
Intros.
LetTac fx:=(F x Hx).
LetTac fy:=(F y Hy).
Split; Intro.
Cut (e[<]fx); Intros.
Step e[-]e.
Apply shift_minus_less; Apply shift_less_plus'.
Apply less_leEq_trans with fx[-]fy.
Apply minus_resp_less; Assumption.
EApply leEq_transitive; [Apply leEq_AbsIR | Assumption].
Cut (e[<]fx)+(fx[<][--]e); [Intro | Apply less_AbsIR; Assumption].
Inversion_clear H5.
Assumption.
ElimType False.
Cut Zero[<][--]e.
Intro; Cut e[<]Zero.
Exact (less_antisymmetric_unfolded ??? H).
Step [--][--]e; Stepr [--](Zero::IR); Apply inv_resp_less; Assumption.
Apply less_transitive_unfolded with fx; Assumption.
Stepr e[-]e.
Apply shift_less_minus.
Apply less_leEq_trans with fy[-]fx.
2: EApply leEq_transitive.
3: Apply H2.
2: EApply leEq_wdr; [Apply leEq_AbsIR | Apply AbsIR_minus].
Unfold cg_minus; Apply plus_resp_less_lft.
Cut (e[<]fx)+(fx[<][--]e); [Intro | Apply less_AbsIR; Assumption].
Inversion_clear H5.
Apply less_transitive_unfolded with (Zero::IR).
Apply less_transitive_unfolded with fx; Assumption.
Step [--](Zero::IR); Apply inv_resp_less; Assumption.
Step [--][--]e; Apply inv_resp_less; Assumption.
Qed.

(* Tex_Prose
Being continuous is an extensional property.
*)

(* Begin_Tex_Verb *)
Lemma Continuous_I_wd : (Feq I F G)->(Continuous_I Hab F)->(Continuous_I Hab G).
(* End_Tex_Verb *)
Intros.
Elim H0; Clear H0; Intros Hinc H0.
Elim H; Clear H; Intros H' H.
Elim H'; Clear H'; Intros incF' incG'.
Split.
Apply incG'.
Intros e He; Elim (H0 e He); Clear H0; Intros d H0 H1.
Exists d.
Assumption.
Intros.
Apply leEq_wdl with (AbsIR (F x (incF' x H2))[-](F y (incF' y H3))).
Apply H1; Assumption.
Simpl in H.
Apply AbsIR_wd.
Apply cg_minus_wd; Apply H; Assumption.
Qed.

(* Tex_Prose
A continuous function remains continuous if you restrict its domain.
*)

(* Begin_Tex_Verb *)
Lemma included_imp_contin : (c,d,Hcd:?)
  (included (compact c d Hcd) (Compact Hab))->
  (Continuous_I Hab F)->(Continuous_I Hcd F).
(* End_Tex_Verb *)
Intros.
Elim H0; Clear H0; Intros incF' contF.
Split.
Apply included_trans with (Compact Hab); [Apply H | Apply incF'].
Intros e He; Elim (contF e He); Intros e' H0 H1.
Exists e'.
Assumption.
Intros; Apply H1.
Apply H; Assumption.
Apply H; Assumption.
Assumption.
Qed.

(* Tex_Prose
Constant functions and identity are continuous.
*)

(* Begin_Tex_Verb *)
Lemma Continuous_I_const : (c:IR)(Continuous_I Hab {-C-}c).
(* End_Tex_Verb *)
Intro.
Split.
Included.
Intros; Exists (One::IR).
Apply pos_one.
Intros.
Apply leEq_wdl with (AbsIR Zero).
Step (Zero::IR); Apply less_leEq; Assumption.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_id : (Continuous_I Hab FId).
(* End_Tex_Verb *)
Split.
Included.
Intros; Exists e.
Assumption.
Intros; Assumption.
Qed.

(* Tex_Prose
Assume \verb!F! and \verb!G! are continuous in \verb!I!.  Then functions derived from these through algebraic operations are also continuous, provided (in the case of reciprocal and division) some extra conditions are met.
*)

Hypothesis contF:(Continuous_I Hab F).
Hypothesis contG:(Continuous_I Hab G).

(* Begin_Tex_Verb *)
Lemma Continuous_I_plus : (Continuous_I Hab F{+}G).
(* End_Tex_Verb *)
Clear incF incG.
Elim contF; Intros incF' contF'.
Elim contG; Intros incG' contG'.
Split.
Included.
Intros.
Elim (contF' e[/]TwoNZ).
Elim (contG' e[/]TwoNZ).
Clear contF contG contF' contG'.
2: Apply pos_div_two; Assumption.
2: Apply pos_div_two; Assumption.
Intros df H0 H1 dg H2 H3.
Exists (Min df dg).
Apply less_Min; Assumption.
Intros.
Simpl.
Apply leEq_wdl with 
  (AbsIR ((F x (ProjIR1 Hx))[-](F y (ProjIR1 Hy)))[+]((G x (ProjIR2 Hx))[-](G y (ProjIR2 Hy)))).
RStepr e[/]TwoNZ[+]e[/]TwoNZ.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
Simpl; Apply H3; Try Assumption.
Apply leEq_transitive with (Min df dg); [Assumption | Apply Min_leEq_rht].
Simpl; Apply H1; Try Assumption.
Apply leEq_transitive with (Min df dg); [Assumption | Apply Min_leEq_lft].
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_inv : (Continuous_I Hab {--}F).
(* End_Tex_Verb *)
Clear incF.
Elim contF; Intros incF' contF'.
Split.
Included.
Intros.
Elim (contF' e H).
Intros d H0 H1.
Exists d.
Assumption.
Intros; Simpl.
Apply leEq_wdl with (AbsIR ((F x Hx))[-](F y Hy)).
Apply H1; Assumption.
EApply eq_transitive_unfolded.
Apply AbsIR_inv.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_mult : (Continuous_I Hab F{*}G).
(* End_Tex_Verb *)
Clear incF incG.
Elim contF; Intros incF' contF'.
Elim contG; Intros incG' contG'.
Split; [Included | Intros].
Cut {xf:IR | (x:IR)(Hx:(I x))(Hx':(P x))(AbsIR (F x Hx'))[<=]xf}.
Cut {xg:IR | (x:IR)(Hx:(I x))(Hx':(Q x))(AbsIR (G x Hx'))[<=]xg}.
2: Unfold I Q; Apply Continuous_I_imp_abs_lub; Assumption.
2: Unfold I P; Apply Continuous_I_imp_abs_lub; Assumption.
Intros.
Inversion_clear H0.
Inversion_clear H1.
Elim (contF' (e[/]TwoNZ)[/](Max x One)[//](max_one_ap_zero ?)); Clear contF.
Elim (contG' (e[/]TwoNZ)[/](Max x0 One)[//](max_one_ap_zero ?)); Clear contG.
Intros dg H1 H3 df H4 H5.
2: Apply div_resp_pos.
2: Apply pos_max_one.
2: Apply pos_div_two; Assumption.
2: Apply div_resp_pos.
2: Apply pos_max_one.
2: Apply pos_div_two; Assumption.
Exists (Min df dg).
Apply less_Min; Assumption.
Intros; Simpl.
RStepr (e[/]TwoNZ)[+](e[/]TwoNZ).
Apply leEq_wdl with (AbsIR (F x1 (ProjIR1 Hx))[*]((G x1 (ProjIR2 Hx))[-](G y (ProjIR2 Hy)))[+]
  ((F x1 (ProjIR1 Hx))[-](F y (ProjIR1 Hy)))[*](G y (ProjIR2 Hy))).
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with x0[*](AbsIR ((G x1 (ProjIR2 Hx))[-](G y (ProjIR2 Hy)))).
Apply mult_resp_leEq_rht.
Apply H0; Assumption.
Apply AbsIR_nonneg.
Apply leEq_transitive with (Max x0 One)[*](AbsIR (G x1 (ProjIR2 Hx))[-](G y (ProjIR2 Hy))).
Apply mult_resp_leEq_rht; [Apply lft_leEq_Max | Apply AbsIR_nonneg].
Step (AbsIR (G x1 (ProjIR2 Hx))[-](G y (ProjIR2 Hy)))[*](Max x0 One).
Apply shift_mult_leEq with (max_one_ap_zero x0); [Apply pos_max_one | Simpl; Apply H3]; Try Assumption.
Apply leEq_transitive with (Min df dg); [Assumption | Apply Min_leEq_rht].
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply leEq_transitive with (AbsIR (F x1 (ProjIR1 Hx))[-](F y (ProjIR1 Hy)))[*]x.
Apply mult_resp_leEq_lft; [Apply H2 | Apply AbsIR_nonneg]; Assumption.
Apply leEq_transitive with (AbsIR (F x1 (ProjIR1 Hx))[-](F y (ProjIR1 Hy)))[*](Max x One).
Apply mult_resp_leEq_lft; [Apply lft_leEq_Max with y:=(One::IR) | Apply AbsIR_nonneg].
Apply shift_mult_leEq with (max_one_ap_zero x); [Apply pos_max_one | Simpl; Apply H5]; Try Assumption.
Apply leEq_transitive with (Min df dg); [Assumption | Apply Min_leEq_lft].
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Hypothesis Hg':(bnd_away_zero I G).
Hypothesis Hg'':(x:IR)(Hx:(I x))(Hx':(Q x))(G x Hx')[#]Zero.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Continuous_I_recip : (Continuous_I Hab {1/}G).
(* End_Tex_Verb *)
Clear incF incG.
Elim contG; Intros incG' contG'.
Split.
Included; Assumption.
Elim Hg'; Intros Haux Hg2.
Elim Hg2; Clear Haux Hg2; Intros c H H0.
Intros.
Elim contG' with c[*]c[*]e; Clear contG contG'.
Intros d H2 H3.
Exists d; Intros.
Assumption.
Simpl.
LetTac Hxx:=(incG' x H4).
LetTac Hyy:=(incG' y H5).
Apply leEq_wdl with (AbsIR ((G y Hyy)[-](G x Hxx))[/]?[//](mult_resp_ap_zero ??? (Hg'' x H4 Hxx) (Hg'' y H5 Hyy))).
Apply leEq_wdl with 
  (AbsIR ((G y Hyy)[-](G x Hxx)))[/]?[//](AbsIR_resp_ap_zero ? (mult_resp_ap_zero ??? (Hg'' x H4 Hxx) (Hg'' y H5 Hyy))).
Apply leEq_transitive with 
  (AbsIR ((G y Hyy)[-](G x Hxx)))[/]?[//](mult_resp_ap_zero ??? (pos_ap_zero ?? H) (pos_ap_zero ?? H)).
RStep 
  (AbsIR ((G y Hyy)[-](G x Hxx)))[*](One[/]?[//](AbsIR_resp_ap_zero ? (mult_resp_ap_zero ??? (Hg'' x H4 Hxx) (Hg'' y H5 Hyy)))).
RStepr 
  (AbsIR ((G y Hyy)[-](G x Hxx)))[*](One[/]?[//](mult_resp_ap_zero ??? (pos_ap_zero ?? H) (pos_ap_zero ?? H))).
Apply mult_resp_leEq_lft.
Apply recip_resp_leEq.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive; Assumption.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try (Apply less_leEq; Assumption).
EApply leEq_wdr; [Apply (H0 x H4 Hxx) | Algebra].
EApply leEq_wdr; [Apply (H0 y H5 Hyy) | Algebra].
Apply AbsIR_nonneg.
Apply shift_div_leEq'.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive; Assumption.
EApply leEq_wdl.
2: Apply AbsIR_minus.
Apply H3; Assumption.
Apply eq_symmetric_unfolded; Apply AbsIR_division.
Apply AbsIR_wd.
Rational.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive.
Step (Zero::IR)[*]Zero; Apply mult_resp_less_both; Try Apply leEq_reflexive; Assumption.
Assumption.
Qed.

End Local_Results.

Hints Resolve contin_imp_inc : included.

Section Corolaries.

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(Compact Hab).

Variables F,G:PartIR.

Local P:=(Pred F).
Local Q:=(Pred G).

Hypothesis contF : (Continuous_I Hab F).
Hypothesis contG : (Continuous_I Hab G).

(* Tex_Prose
The corresponding properties for subtraction, division and multiplication by a scalar are easily proved as corollaries; exponentiation is proved by induction, appealing to the results on product and constant functions.
*)

(* Begin_Tex_Verb *)
Lemma Continuous_I_minus : (Continuous_I Hab F{-}G).
(* End_Tex_Verb *)
Apply Continuous_I_wd with F{+}{--}G.
FEQ.
Apply Continuous_I_plus.
Apply contF.
Apply Continuous_I_inv; Apply contG.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_scal : (c:IR)(Continuous_I Hab c{**}F).
(* End_Tex_Verb *)
Intros.
Unfold Fscalmult.
Apply Continuous_I_mult.
Apply Continuous_I_const.
Apply contF.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_nth : (n:nat)(Continuous_I Hab F{^}n).
(* End_Tex_Verb *)
Induction n.
Apply Continuous_I_wd with {-C-}(One::IR).
Apply FNth_zero'; Apply contin_imp_inc; Auto.
Apply Continuous_I_const.
Clear n; Intros.
Apply Continuous_I_wd with F{*}F{^}n.
Apply FNth_mult'; Apply contin_imp_inc; Auto.
Apply Continuous_I_mult; Assumption.
Qed.

Hypothesis Hg':(bnd_away_zero I G).
Hypothesis Hg'':(x:IR)(Hx:(I x))(Hx':(Q x))(G x Hx')[#]Zero.

(* Begin_Tex_Verb *)
Lemma Continuous_I_div : (Continuous_I Hab F{/}G).
(* End_Tex_Verb *)
Apply Continuous_I_wd with F{*}{1/}G.
FEQ.
Apply Continuous_I_mult.
Assumption.
Apply Continuous_I_recip; Assumption.
Qed.

End Corolaries.

Section Absolute_Value.

(* Tex_Prose
\section{Other Useful Results}
*)

Variables a,b:IR.
Hypothesis Hab:(a[<=]b).
Local I:=(Compact Hab).

Variable F : PartIR.
Hypothesis contF : (Continuous_I Hab F).

Local P:=(Pred F).

Section Lemmas.

Hypothesis incF : (included (Compact Hab) P).

(* Tex_Prose
Next we prove that the absolute value of a function is continuous if the original function also is; we start by unfolding a previous lemma in more pratical forms:
*)

(* Begin_Tex_Verb *)
Lemma cont_no_sign_change_pos : (e:IR)(Zero[<]e)->
  (x,y:IR)(I x)->(I y)->(Hx:(P x))(Hy:(P y))
  ((AbsIR (F x Hx)[-](F y Hy))[<=]e)->(e[<](AbsIR (F x Hx)))->
    (e[<](F x Hx))->(Zero[<](F y Hy)).
(* End_Tex_Verb *)
Intros.
Cut ((Zero[<](F x Hx))->(Zero[<](F y Hy)))*(((F x Hx)[<]Zero)->((F y Hy)[<]Zero)).
2: Exact (cont_no_sign_change a b Hab F e H x y H0 H1 Hx Hy H2 H3).
Intro; Inversion_clear H5.
Apply H6.
Apply less_transitive_unfolded with e; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma cont_no_sign_change_neg : (e:IR)(Zero[<]e)->
  (x,y:IR)(I x)->(I y)->(Hx:(P x))(Hy:(P y))
  ((AbsIR (F x Hx)[-](F y Hy))[<=]e)->(e[<](AbsIR (F x Hx)))->
    ((F x Hx)[<][--]e)->((F y Hy)[<]Zero).
(* End_Tex_Verb *)
Intros.
Cut ((Zero[<](F x Hx))->(Zero[<](F y Hy)))*(((F x Hx)[<]Zero)->((F y Hy)[<]Zero)).
2: Exact (cont_no_sign_change a b Hab F e H x y H0 H1 Hx Hy H2 H3).
Intro; Inversion_clear H5.
Apply H7.
Apply less_transitive_unfolded with [--]e.
Assumption.
Stepr [--](Zero::IR); Apply inv_resp_less; Assumption.
Qed.

End Lemmas.

(* Tex_Prose
From these two lemmas it easy to prove our result.
*)

(* Begin_Tex_Verb *)
Lemma Continuous_I_abs : (Continuous_I Hab (FAbs F)).
(* End_Tex_Verb *)
Elim contF; Intros incF contF'.
Split; [Included | Intros e He].
Cut e[/]FourNZ[<]e[/]ThreeNZ.
Intro.
Cut (Zero[<]e[/]FourNZ); [Intro | Apply pos_div_four; Assumption].
Elim (contF' ? H0).
Intros d Hd H2.
Exists d.
Assumption.
Intros.
Simpl in Hx Hy.
Cut (e[/]FourNZ[<](AbsIR (F x Hx)))+((AbsIR (F x Hx))[<]e[/]ThreeNZ).
2: Apply cotrans_less_unfolded.
Intro.
Inversion_clear H5.
Cut (e[/]FourNZ[<](F x Hx))+((F x Hx)[<][--](e[/]FourNZ)); [Intro | Apply less_AbsIR; Assumption].
Inversion_clear H5.
Cut (Zero[<](F y Hy)).
2: Exact (cont_no_sign_change_pos e[/]FourNZ (pos_div_four ?? He) x y H1 H3 Hx Hy (H2 x y H1 H3 Hx Hy H4) H6 H7).
Intro.
Apply leEq_wdl with (AbsIR (F x Hx)[-](F y Hy)).
Apply leEq_transitive with e[/]FourNZ.
Simpl; Apply H2; Assumption.
Apply less_leEq; Apply pos_div_four'; Assumption.
Apply AbsIR_wd.
Simpl.
Apply eq_symmetric_unfolded; Apply cg_minus_wd; Apply AbsIR_eq_x; Apply less_leEq.
Apply less_transitive_unfolded with e[/]FourNZ.
Apply pos_div_four; Assumption.
Assumption.
Assumption.
Cut ((F y Hy)[<]Zero).
2: Exact (cont_no_sign_change_neg e[/]FourNZ (pos_div_four ?? He) x y H1 H3 Hx Hy (H2 x y H1 H3 Hx Hy H4) H6 H7).
Intro.
Apply leEq_wdl with (AbsIR (F y Hy)[-](F x Hx)).
Apply leEq_transitive with e[/]FourNZ.
Apply leEq_wdl with (AbsIR (F x Hx)[-](F y Hy)); [Simpl; Apply H2 | Apply AbsIR_minus]; Assumption.
Apply less_leEq; Apply pos_div_four'; Assumption.
Apply AbsIR_wd.
Simpl.
RStep ([--](F x Hx))[-]([--](F y Hy)).
Apply eq_symmetric_unfolded; Apply cg_minus_wd; Apply AbsIR_eq_inv_x; Apply less_leEq.
Apply less_transitive_unfolded with [--](e[/]FourNZ).
Assumption.
Stepr [--](Zero::IR); Apply inv_resp_less; Apply pos_div_four; Assumption.
Assumption.
EApply leEq_transitive.
Apply triangle_IR_minus.
RStepr e[/]ThreeNZ[+](e[/]ThreeNZ[+]e[/]ThreeNZ).
Apply plus_resp_leEq_both; (EApply leEq_wdl; [Idtac | Apply eq_symmetric_unfolded; Apply AbsIR_eq_x]).
Apply less_leEq; Apply H6; Assumption.
Simpl; Apply AbsIR_nonneg.
Simpl.
Apply leEq_wdl with (AbsIR (F x Hx)[-]((F x Hx)[-](F y Hy))).
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both.
Apply less_leEq; Apply H6; Assumption.
EApply leEq_transitive.
Simpl; Apply H2; Assumption.
Apply less_leEq; Assumption.
Simpl; Apply AbsIR_nonneg.
Assumption.
RStep e[*](One[/]FourNZ); RStepr e[*](One[/]ThreeNZ).
Apply mult_resp_less_lft.
Apply recip_resp_less.
Apply pos_three.
Apply three_less_four.
Assumption.
Qed.

End Absolute_Value.

Section Other.

Section Sums.

(* Tex_Prose
We finally prove that the sum of an arbitrary family of continuous functions is still a continuous function.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Hypothesis Hab':a[<]b.

Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Lemma Continuous_I_Sum0 : (f:nat->PartIR)
  ((n:nat)(Continuous_I Hab (f n)))->
    (n:nat)(Continuous_I Hab (FSum0 n f)).
(* End_Tex_Verb *)
Intros.
Induction n.
EApply Continuous_I_wd.
Apply FSum0_0.
2: Apply Continuous_I_const.
Intro; Apply contin_imp_inc; Auto.
EApply Continuous_I_wd.
Apply FSum0_S.
Intro; Apply contin_imp_inc; Auto.
Apply Continuous_I_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_Sumx : (n:nat)(f:(i:nat)(lt i n)->PartIR)
  ((i:nat)(Hi:?)(Continuous_I Hab (f i Hi)))->
    (Continuous_I Hab (FSumx n f)).
(* End_Tex_Verb *)
Intro; Induction n; Intros f contF.
Simpl; Apply Continuous_I_const.
Simpl; Apply Continuous_I_plus.
Apply Hrecn.
Intros; Apply contF.
Apply contF.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_I_Sum : (f:nat->PartIR)
  ((n:nat)(Continuous_I Hab (f n)))->
    (m,n:nat)(Continuous_I Hab (FSum m n f)).
(* End_Tex_Verb *)
Intros.
EApply Continuous_I_wd.
Apply Feq_symmetric; Apply FSum_FSum0'.
Intro; Apply contin_imp_inc; Auto.
Apply Continuous_I_minus; Apply Continuous_I_Sum0; Auto.
Qed.

End Sums.

(* Tex_Prose
For practical purposes, these characterization results are useful:
*)

(* Begin_Tex_Verb *)
Lemma lub_charact : (a,b:IR)(Hab:?)(F:PartIR)
  (contF:(Continuous_I Hab F))(z:IR)(fun_lub a b Hab F z)->
    z[=](lub_funct ???? contF).
(* End_Tex_Verb *)
Intros.
Elim H; Intros incF Hz.
Inversion_clear Hz.
LetTac y:=(lub_funct ???? contF).
Elim (lub_is_lub' ???? contF); Fold y; Intros incF' Hy.
Inversion_clear Hy.
Apply leEq_imp_eq; Intro.
Cut Zero[<](z[-]y); Intros.
Elim (H1 ? H5); Intros x Hx.
Elim Hx; Clear Hx; Intros Hx Hx'.
Apply less_irreflexive_unfolded with x:=y.
Apply less_leEq_trans with (F x (incF x Hx)).
Apply inv_cancel_less.
Apply plus_cancel_less with z.
RStep z[-](pfpfun ? ? (incF x Hx)); RStepr z[-]y.
Apply Hx'.
Apply H2; Assumption.
Apply shift_less_minus; Step y; Assumption.
Cut Zero[<](y[-]z); Intros.
Elim (H3 ? H5); Intros x Hx.
Elim Hx; Clear Hx; Intros Hx Hx'.
Apply less_irreflexive_unfolded with x:=z.
Apply less_leEq_trans with (F x (incF x Hx)).
Apply inv_cancel_less.
Apply plus_cancel_less with y.
RStep y[-](pfpfun ? ? (incF x Hx)); RStepr y[-]z.
Apply Hx'.
Apply H0; Assumption.
Apply shift_less_minus; Step z; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma glb_charact : (a,b:IR)(Hab:?)(F:PartIR)
  (contF:(Continuous_I Hab F))(z:IR)(fun_glb a b Hab F z)->
    z[=](glb_funct ???? contF).
(* End_Tex_Verb *)
Intros.
Elim H; Intros incF Hz.
Inversion_clear Hz.
LetTac y:=(glb_funct ???? contF).
Elim (glb_is_glb' ???? contF); Fold y; Intros incF' Hy.
Inversion_clear Hy.
Apply leEq_imp_eq; Intro.
Cut Zero[<](z[-]y); Intros.
Elim (H3 ? H5); Intros x Hx.
Elim Hx; Clear Hx; Intros Hx Hx'.
Apply less_irreflexive_unfolded with x:=z.
Apply leEq_less_trans with (F x (incF x Hx)).
Apply H0; Assumption.
Apply plus_cancel_less with [--]y.
Unfold cg_minus in Hx'; Apply Hx'.
Apply shift_less_minus; Step y; Assumption.
Cut Zero[<](y[-]z); Intros.
Elim (H1 ? H5); Intros x Hx.
Elim Hx; Clear Hx; Intros Hx Hx'.
Apply less_irreflexive_unfolded with x:=y.
Apply leEq_less_trans with (F x (incF x Hx)).
Apply H2; Assumption.
Apply plus_cancel_less with [--]z.
Unfold cg_minus in Hx'; Apply Hx'.
Apply shift_less_minus; Step z; Assumption.
Qed.

(* Tex_Prose
The following result is also extremely useful, as it allows us to set a lower bound on the glb of a function.
*)

(* Begin_Tex_Verb *)
Lemma leEq_glb : (a,b,Hab:?)(F:PartIR)(contF,x:?)
  ((y:IR)(Compact Hab y)->(Hy:?)(x[<=](F y Hy)))->
  x[<=](glb_funct a b Hab F contF).
(* End_Tex_Verb *)
Intros.
Elim (glb_is_glb' ???? contF); Intros.
Inversion_clear b0.
Stepr (glb_funct ???? contF)[+]Zero; Apply shift_leEq_plus'.
Red; Apply approach_zero_weak.
Intros.
Elim (H1 ? H2); Intros y Hy.
Inversion_clear Hy.
Apply less_leEq; EApply leEq_less_trans.
2: Apply (H3 (contin_imp_inc ???? contF ? x0)).
Apply minus_resp_leEq; Auto.
Qed.

(* Tex_Prose
The norm is also an extensional property.
*)

(* Begin_Tex_Verb *)
Lemma Norm_Funct_wd : (a,b:IR)(Hab:a[<=]b)
  (F,G:PartIR)(Feq (Compact Hab) F G)->
  (contF:(Continuous_I Hab F))(contG:(Continuous_I Hab G))
    (Norm_Funct contF)[=](Norm_Funct contG).
(* End_Tex_Verb *)
Intros.
Elim H; Clear H; Intros H' H.
Elim H'; Clear H'; Intros incF incG.
Unfold Norm_Funct; Apply bin_op_wd_unfolded.
Elim (lub_is_lub' ???? contF); Intros incF' Hlub.
Inversion_clear Hlub.
Apply lub_charact.
Split.
Auto.
Split.
Intros.
Apply leEq_wdl with (F x (incF x H2)).
Apply H0; Assumption.
Algebra.
Intros.
Elim (H1 e H2); Intros x Hx.
Inversion_clear Hx.
Exists x; Exists x0.
Intro; EApply less_wdl.
Apply (H3 (incF x x0)).
Algebra.
Apply un_op_wd_unfolded.
Elim (glb_is_glb' ???? contF); Intros incF' Hglb.
Inversion_clear Hglb.
Apply glb_charact.
Split.
Auto.
Split.
Intros.
Apply leEq_wdr with (F x (incF x H2)).
Apply H0; Assumption.
Algebra.
Intros.
Elim (H1 e H2); Intros x Hx.
Inversion_clear Hx.
Exists x; Exists x0.
Intro; EApply less_wdl.
Apply (H3 (incF x x0)).
Algebra.
Qed.

(* Tex_Prose
The value of the norm is covariant with the length of the interval.
*)

(* Begin_Tex_Verb *)
Lemma included_imp_norm_leEq :
  (a,b,c,d,Hab,Hcd,F,contF1,contF2:?)
  (included (compact c d Hcd) (compact a b Hab))->
  (!Norm_Funct c d Hcd F contF2)[<=](!Norm_Funct a b Hab F contF1).
(* End_Tex_Verb *)
Intros.
Apply leEq_Norm_Funct; Intros.
Apply norm_bnd_AbsIR; Auto.
Qed.

End Other.

Hints Resolve Continuous_I_const Continuous_I_id Continuous_I_plus
  Continuous_I_inv Continuous_I_minus Continuous_I_mult Continuous_I_scal Continuous_I_recip
  Continuous_I_div Continuous_I_nth Continuous_I_abs : continuous.

Tactic Definition Contin := Auto with continuous included.
