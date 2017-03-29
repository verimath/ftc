(* $Id: Differentiability.v,v 1.10 2003/03/13 12:06:18 lcf Exp $ *)

Require Export PartInterval.
Require Export DerivativeOps.

Section Definitions.

(* Tex_Prose
\chapter{Differentiability}

We will now use our work on derivatives to define a notion of differentiable function and prove its main properties.

\begin{convention} Throughout this section, \verb!a,b! will be real numbers with $a<b$, \verb!I! will denote the interval $[a,b]$ and \verb!F,G,H! will be differentiable functions.
\end{convention}

Usually a function $F$ is said to be differentiable in a proper compact interval $[a,b]$ if there exists another function $F'$ such that $F'$ is a derivative of $F$ in that interval.  There is a problem in formalizing this definition, as we pointed out earlier on, which is that if we simply write it down as is we are not able to get such a function $F'$ from a hypothesis that $F$ is differentiable.

However, it turns out that this is not altogether the best definition for the following reason: if we say that $F$ is differentiable in $[a,b]$, we mean that there is a partial function $F'$ which is defined in $[a,b]$ and satisfies a certain condition in that interval but \emph{nothing is required of the behaviour of the function outside $[a,b]$}.  Thus we can argue that, from a mathematical point of view, the $F'$ that we get eliminating a hypothesis of differentiability should be defined exactly on that interval.  If we do this, we can quantify over the set of setoid functions in that interval and eliminate the existencial quantifier without any problems.
*)

(* Begin_Tex_Verb *)
Definition Diffble_I [a,b:IR][Hab:a[<]b][F:PartIR] := 
  {f':(CSetoid_fun (subset (Compact (less_leEq ??? Hab))) IR) &
    (Derivative_I Hab F (PartInt f'))}.
(* End_Tex_Verb *)

End Definitions.

Implicits Diffble_I [1 2].

Section Local_Properties.

(* Tex_Prose
From this point on, we just prove results analogous to the ones for derivability.

A function differentiable in $[a,b]$ is differentiable in every proper compact subinterval of $[a,b]$.
*)

(* Begin_Tex_Verb *)
Lemma included_imp_diffble : (a,b,Hab,c,d,Hcd,F:?)
  (included (compact c d (less_leEq ??? Hcd))
            (compact a b (less_leEq ??? Hab)))->
  (Diffble_I Hab F)->(Diffble_I Hcd F).
(* End_Tex_Verb *)
Intros.
Elim H0; Clear H0; Intros f' derF.
Exists (int_partIR (!Frestr (PartInt f') ? (compact_wd ???) H) ??? (included_refl ?)).
Apply Derivative_I_wdr with (PartInt f').
FEQ.
Simpl; Apply csetoid_fun_wd_unfolded; Simpl; Algebra.
Exact (included_imp_deriv ???????? H derF).
Qed.

(* Tex_Prose
A function differentiable in an interval is everywhere defined in that interval.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Lemma diffble_imp_inc :
   (F:PartIR)(Diffble_I Hab' F)->(included I (Pred F)).
(* End_Tex_Verb *)
Intros.
Inversion_clear H.
Unfold I Hab; Included.
Qed.

(* Tex_Prose
If a function has a derivative in an interval then it is differentiable in that interval.
*)

(* Begin_Tex_Verb *)
Lemma deriv_imp_Diffble_I :
  (F,F':PartIR)(Derivative_I Hab' F F')->(Diffble_I Hab' F).
(* End_Tex_Verb *)
Intros.
Exists (IntPartIR (derivative_imp_inc' ????? H)).
Apply Derivative_I_wdr with F'.
Apply int_part_int.
Assumption.
Qed.

End Local_Properties.

Hints Resolve diffble_imp_inc : included.

Section Operations.

(* Tex_Prose
All the algebraic results carry on.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

Section Constants.

(* Begin_Tex_Verb *)
Lemma Diffble_I_const : (c:IR)(Diffble_I Hab' {-C-}c).
(* End_Tex_Verb *)
Intros.
Exists (ifunct_const a b Hab Zero).
Apply Derivative_I_wdr with ({-C-}Zero::PartIR).
Apply part_int_const.
Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_I_id : (Diffble_I Hab' FId).
(* End_Tex_Verb *)
Exists (ifunct_const a b Hab One).
Apply Derivative_I_wdr with ({-C-}One::PartIR).
Apply part_int_const.
Deriv.
Qed.

End Constants.

Section Well_Definedness.

Variables F,H:PartIR.

Hypothesis diffF:(Diffble_I Hab' F).

(* Begin_Tex_Verb *)
Lemma Diffble_I_wd : (Feq (Compact Hab) F H)->(Diffble_I Hab' H).
(* End_Tex_Verb *)
Intros.
Exists (ProjS1 diffF).
EApply Derivative_I_wdl.
Apply H0.
Apply projS2.
Qed.

End Well_Definedness.

Variables F,G:PartIR.

Hypothesis diffF:(Diffble_I Hab' F).
Hypothesis diffG:(Diffble_I Hab' G).

(* Begin_Tex_Verb *)
Lemma Diffble_I_plus : (Diffble_I Hab' F{+}G).
(* End_Tex_Verb *)
Elim diffF; Intros F' derF.
Elim diffG; Intros G' derG.
Exists (IPlus F' G').
EApply Derivative_I_wdr.
Apply part_int_plus with F:=(PartInt F') G:=(PartInt G').
Apply Feq_reflexive; Included.
Apply Feq_reflexive; Included.
Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_I_inv : (Diffble_I Hab' {--}F).
(* End_Tex_Verb *)
Elim diffF; Intros F' derF.
Exists (IInv F').
EApply Derivative_I_wdr.
Apply part_int_inv with F:=(PartInt F').
Apply Feq_reflexive; Included.
Deriv.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_I_mult : (Diffble_I Hab' F{*}G).
(* End_Tex_Verb *)
Elim diffF; Intros F' derF.
Elim diffG; Intros G' derG.
Exists (IPlus (IMult (IntPartIR (diffble_imp_inc ???? diffF)) G') (IMult F' (IntPartIR (diffble_imp_inc ???? diffG)))).
EApply Derivative_I_wdr.
Apply part_int_plus with 
  F:=(PartInt (IMult (IntPartIR (diffble_imp_inc ???? diffF)) G')) 
  G:=(PartInt (IMult F' (IntPartIR (diffble_imp_inc ???? diffG)))).
Apply Feq_reflexive; Included.
Apply Feq_reflexive; Included.
EApply Derivative_I_wdr.
Apply Feq_plus with F:=F{*}(PartInt G') G:=(PartInt F'){*}G.
Apply part_int_mult.
FEQ.
Apply Feq_reflexive; Included.
Apply part_int_mult.
Apply Feq_reflexive; Included.
FEQ.
Deriv.
Qed.

(* Begin_Tex_Verb *)
Hypothesis Gbnd:(bnd_away_zero I G).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Diffble_I_recip : (Diffble_I Hab' {1/}G).
(* End_Tex_Verb *)
Elim diffG; Intros G' derG.
Cut (included I (Pred G)); [Intro Hg' | Unfold I Hab; Included].
Unfold I in Hg'; Cut (x:(subset I)) (IMult (IntPartIR Hg') (IntPartIR Hg') x)[#]Zero; Intros.
Exists (IInv (IDiv G' ? H)).
EApply Derivative_I_wdr.
Apply part_int_inv with F:=(PartInt (IDiv G' ? H)).
Apply Feq_reflexive; Included.
EApply Derivative_I_wdr.
Apply Feq_inv with F:=(PartInt G'){/}(PartInt (IMult (IntPartIR Hg') (IntPartIR Hg'))).
Apply part_int_div.
Apply Feq_reflexive; Included.
Apply Feq_reflexive; Simpl; Included.
Red; Intros.
Split.
Simpl; Included.
Elim Gbnd; Intros Hinc c.
Elim c; Clear c; Intros c H0 H1.
Exists c[*]c.
Apply mult_resp_pos; Assumption.
Intros.
Simpl.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Auto; Apply less_leEq; Assumption.
EApply Derivative_I_wdr.
Apply Feq_inv with F:=(PartInt G'){/}(G{*}G).
Apply Feq_div.
Included.
Apply Feq_reflexive; Included.
Apply part_int_mult.
FEQ.
FEQ.
Deriv.
Simpl.
Apply mult_resp_ap_zero; Apply bnd_imp_ap_zero with I; Auto; Apply scs_prf.
Qed.

End Operations.

Section Corollaries.

Variables a,b:IR.
Hypothesis Hab':a[<]b.

Local Hab:=(less_leEq ??? Hab').
Local I:=(Compact Hab).

Variables F,G:PartIR.

Hypothesis diffF : (Diffble_I Hab' F).
Hypothesis diffG : (Diffble_I Hab' G).

(* Begin_Tex_Verb *)
Lemma Diffble_I_minus : (Diffble_I Hab' F{-}G).
(* End_Tex_Verb *)
Apply Diffble_I_wd with F{+}{--}G.
Apply Diffble_I_plus.
Assumption.
Apply Diffble_I_inv; Assumption.
FEQ.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_I_scal : (c:IR)(Diffble_I Hab' c{**}F).
(* End_Tex_Verb *)
Intro.
Unfold Fscalmult.
Apply Diffble_I_mult.
Apply Diffble_I_const.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_I_nth : (n:nat)(Diffble_I Hab' F{^}n).
(* End_Tex_Verb *)
Intro.
Induction n.
EApply Diffble_I_wd.
2: Apply FNth_zero'; Included.
Apply Diffble_I_const.
EApply Diffble_I_wd.
2: Apply FNth_mult'; Included.
Apply Diffble_I_mult; Assumption.
Qed.

Hypothesis Gbnd:(bnd_away_zero I G).

(* Begin_Tex_Verb *)
Lemma Diffble_I_div : (Diffble_I Hab' F{/}G).
(* End_Tex_Verb *)
Apply Diffble_I_wd with F{*}{1/}G.
Apply Diffble_I_mult.
Assumption.
Apply Diffble_I_recip; Assumption.
FEQ.
Qed.

End Corollaries.

Section Derivative_Sums.

(* Tex_Prose
\section{Sums}

We will now prove several corollaries of these lemmas and the ones we already had for derivation.

The derivation rules for families of functions are easily proved by induction using the constant and addition rules.
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Hypothesis Hab':a[<]b.

Local I:=(Compact Hab).

(* Begin_Tex_Verb *)
Lemma Derivative_I_Sum0 : (f,f':nat->PartIR)
  ((n:nat)(Derivative_I Hab' (f n) (f' n)))->
  (n:nat)(Derivative_I Hab' (FSum0 n f) (FSum0 n f')).
(* End_Tex_Verb *)
Intros.
Induction n.
EApply Derivative_I_wdl.
Apply FSum0_0; Included.
EApply Derivative_I_wdr.
Apply FSum0_0; Included.
Apply Derivative_I_const.
EApply Derivative_I_wdl.
Apply FSum0_S; Included.
EApply Derivative_I_wdr.
Apply FSum0_S; Included.
Apply Derivative_I_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_Sumx :
  (n:nat)(f,f':(i:nat)(lt i n)->PartIR)
  ((i:nat)(Hi,Hi':?)(Derivative_I Hab' (f i Hi) (f' i Hi')))->
    (Derivative_I Hab' (FSumx n f) (FSumx n f')).
(* End_Tex_Verb *)
Intro; Induction n; Intros f f' derF.
Simpl; Apply Derivative_I_const; Auto.
Simpl; Apply Derivative_I_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_I_Sum : (f,f':nat->PartIR)
  ((n:nat)(Derivative_I Hab' (f n) (f' n)))->
  (m,n:nat)(Derivative_I Hab' (FSum m n f) (FSum m n f')).
(* End_Tex_Verb *)
Intros.
EApply Derivative_I_wdl.
Apply Feq_symmetric; Apply FSum_FSum0'; Included.
EApply Derivative_I_wdr.
Apply Feq_symmetric; Apply FSum_FSum0'; Included.
Apply Derivative_I_minus; Apply Derivative_I_Sum0; Auto.
Qed.

End Derivative_Sums.

Hints Resolve Derivative_I_Sum0 Derivative_I_Sum Derivative_I_Sumx : derivate.

Section Other_Properties.

(* Tex_Prose
Analogous results hold for differentiability.
*)

Variables a,b:IR.
Hypothesis Hab':a[<]b.

(* Begin_Tex_Verb *)
Lemma Diffble_I_Sum0 : (f:nat->PartIR)
  (diffF:(n:nat)(Diffble_I Hab' (f n)))
  (n:nat)(Diffble_I Hab' (FSum0 n f)).
(* End_Tex_Verb *)
Intros.
Induction n.
Apply Diffble_I_wd with (!Fconst IR Zero).
Apply Diffble_I_const.
FEQ.
Red; Simpl; Intros.
Apply (diffble_imp_inc ???? (diffF n)); Assumption.
Apply Diffble_I_wd with (FSum0 n f){+}(f n).
Apply Diffble_I_plus.
Auto.
Auto.
FEQ.
Simpl; Red; Intros.
Apply (diffble_imp_inc ???? (diffF n0)); Assumption.
Simpl.
Apply bin_op_wd_unfolded; Try Apply Sum0_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_I_Sumx :
  (n:nat)(f:(i:nat)(lt i n)->PartIR)
  (diffF:(i:nat)(Hi:?)(Diffble_I Hab' (f i Hi)))
  (Diffble_I Hab' (FSumx n f)).
(* End_Tex_Verb *)
Intro; Induction n; Intros.
Simpl; Apply Diffble_I_const.
Simpl.
Apply Diffble_I_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_I_Sum : (f:nat->PartIR)
  (diffF:(n:nat)(Diffble_I Hab' (f n)))
  (m,n:nat)(Diffble_I Hab' (FSum m n f)).
(* End_Tex_Verb *)
Intros.
EApply Diffble_I_wd.
2: Apply Feq_symmetric; Apply FSum_FSum0'; Included.
Apply Diffble_I_minus; Apply Diffble_I_Sum0; Auto.
Qed.

End Other_Properties.

(* Tex_Prose
Finally, a differentiable function is continuous.

\begin{convention} Let \verb!F! be a partial function with derivative \verb!F'! on \verb!I!.
\end{convention}
*)

(* Begin_Tex_Verb *)
Lemma diffble_imp_contin_I :
  (a,b:IR)(Hab':a[<]b)(Hab:a[<=]b)(F:PartIR)
  (Diffble_I Hab' F)->(Continuous_I Hab F).
(* End_Tex_Verb *)
Intros.
Apply deriv_imp_contin_I with Hab' (PartInt (ProjS1 H)).
Apply projS2.
Qed.

Hints Immediate included_imp_contin deriv_imp_contin_I deriv_imp_contin'_I diffble_imp_contin_I : continuous.

Hints Immediate included_imp_deriv : derivate.
