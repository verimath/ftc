(* $Id: PartFunEquality.v,v 1.15 2003/03/13 12:06:21 lcf Exp $ *)

Require Export Intervals.

Section Definitions.

(* Tex_Prose
\chapter{Equality of Partial Functions}

\section{Definitions}

In some contexts (namely when quantifying over partial functions) we need to refer explicitly to the subsetoid of elements satisfying a given predicate rather than to the predicate itself.  The following definition makes this possible.
*)

(* Begin_Tex_Verb *)
Definition subset [P:IR->CProp] : CSetoid :=
  (Build_SubCSetoid IR P).
(* End_Tex_Verb *)

(* Tex_Prose
The core of our work will revolve around the following fundamental notion: two functions are equal in a given domain (predicate) iff they coincide on every point of that domain\footnote{Notice that, according to our definition of partial function, it is equivalent to prove the equality for every proof or for a specific proof.  Typically it is easier to consider a generic case}.  This file is concerned with proving the main properties of this equality relation.
*)

(* Begin_Tex_Verb *)
Definition Feq [P:IR->CProp][F,G:(PartIR)] := 
  (included P (Pred F))*(included P (Pred G))*
  {(x:IR)(P x)->(Hx,Hx':?)(F x Hx)[=](G x Hx')}.
(* End_Tex_Verb *)

(* Tex_Prose
Notice that, because the quantification over the proofs is universal, we must require explicitly that the predicate be included in the domain of each function; otherwise the basic properties of equality (like, for example, transitivity) would fail to hold\footnote{To see this it is enough to realize that the empty function would be equal to every other function in every domain.}.  The way to circumvent this would be to quantify existentially over the proofs; this, however, would have two major disadvantages: first, proofs of equality would become very cumbersome and clumsy; secondly (and most important), we often need to prove the inclusions from an equality hypothesis, and this definition allows us to do it in a very easy way.  Also, the pointwise equality is much nicer to use from this definition than in an existentially quantified one.
*)

End Definitions.

Section Equality_Results.

(* Tex_Prose
\section{Properties of Inclusion}

We will now prove the main properties of the equality relation.

\begin{convention} Let \verb!I,R:IR->CProp! and \verb!F,G:PartIR!, and denote by \verb!P! and \verb!Q!, respectively, the domains of \verb!F! and \verb!G!.
\end{convention}
*)

Variable I:IR->CProp.
Variables F,G:PartIR.

Local P:=(Pred F).
Local Q:=(Pred G).

Variable R:IR->CProp.

(* Tex_Prose
We start with two lemmas which make it much easier to prove and use this definition:
*)

(* Begin_Tex_Verb *)
Lemma eq_imp_Feq : (included I P)->(included I Q)->
  ((x:IR)(I x)->(Hx,Hx':?)(F x Hx)[=](G x Hx'))->
  (Feq I F G).
(* End_Tex_Verb *)
Intros.
Split.
Split; Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_imp_eq : (Feq I F G)->(x:IR)(I x)->
  (Hx,Hx':?)(F x Hx)[=](G x Hx').
(* End_Tex_Verb *)
Intros.
Elim H; Intros.
Elim a; Auto.
Qed.

(* Tex_Prose
Next, we show how the inclusion relation works with the operations on partial functions (the first lemma applies, obviously, to total functions).
*)

(* Begin_Tex_Verb *)
Lemma included_IR : (included I [x:IR]CTrue).
(* End_Tex_Verb *)
Split.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FPlus : (included R P)->(included R Q)->
  (included R (Pred F{+}G)).
(* End_Tex_Verb *)
Intros; Simpl; Apply included_conj; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FPlus' :
  (included R (Pred F{+}G))->(included R P).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_lft; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FPlus'' :
  (included R (Pred F{+}G))->(included R Q).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_rht; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FInv :
  (included R P)->(included R (Pred {--}F)).
(* End_Tex_Verb *)
Intro; Simpl; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FInv' :
  (included R (Pred {--}F))->(included R P).
(* End_Tex_Verb *)
Intro; Simpl; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FMinus : (included R P)->(included R Q)->
  (included R (Pred F{-}G)).
(* End_Tex_Verb *)
Intros; Simpl; Apply included_conj; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FMinus' :
  (included R (Pred F{-}G))->(included R P).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_lft; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FMinus'' :
  (included R (Pred F{-}G))->(included R Q).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_rht; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FMult : (included R P)->(included R Q)->
  (included R (Pred F{*}G)).
(* End_Tex_Verb *)
Intros; Simpl; Apply included_conj; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FMult' :
  (included R (Pred F{*}G))->(included R P).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_lft; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FMult'' :
  (included R (Pred F{*}G))->(included R Q).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_rht; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FRecip : (included R Q)->
  ((x:IR)(R x)->(Hx:?)(G x Hx)[#]Zero)->
  (included R (Pred {1/}G)).
(* End_Tex_Verb *)
Intros.
Simpl.
Unfold extend.
Split.
Apply H; Assumption.
Intros; Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FRecip' :
  (included R (Pred {1/}G))->(included R Q).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_extend; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FDiv : (included R P)->(included R Q)->
  ((x:IR)(R x)->(Hx:?)(G x Hx)[#]Zero)->
  (included R (Pred F{/}G)).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply included_conj.
Assumption.
Unfold extend.
Split.
Apply H0; Assumption.
Intros; Apply H1; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FDiv' :
  (included R (Pred F{/}G))->(included R P).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_lft; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FDiv'' :
  (included R (Pred F{/}G))->(included R Q).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_extend; EApply included_conj_rht; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FComp : (included R P)->
  ((x:IR)(Hx:(R x))(Hx':(P x))(Q (F x Hx')))->
  (included R (Pred G{o}F)).
(* End_Tex_Verb *)
Intros.
Simpl.
Red; Intros.
Exists (H x H1).
Apply H0.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FComp' :
  (included R (Pred G{o}F))->(included R P).
(* End_Tex_Verb *)
Intros; Simpl in H; Red; Intros.
Elim (H x H0); Intros; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FScalMult : (included R P)->
  (c:IR)(included R (Pred c{**}F)).
(* End_Tex_Verb *)
Intros; Simpl; Apply included_conj.
Red; Intros; Auto.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FScalMult' : (c:IR)
  (included R (Pred c{**}F))->(included R P).
(* End_Tex_Verb *)
Intros; Simpl in H; EApply included_conj_rht; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FNth : (included R P)->
  (n:nat)(included R (Pred F{^}n)).
(* End_Tex_Verb *)
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_FNth' : (n:nat)
  (included R (Pred F{^}n))->(included R (Pred F)).
(* End_Tex_Verb *)
Auto.
Qed.

End Equality_Results.

Section Some_More.

(* Tex_Prose
Also, if two function coincide on a given subset then they coincide in any smaller subset.
*)

(* Begin_Tex_Verb *)
Lemma included_Feq : (P,Q,F,G:?)
  (included P Q)->(Feq Q F G)->(Feq P F G).
(* End_Tex_Verb *)
Intros.
Inversion_clear H0.
Inversion_clear H1.
Apply eq_imp_Feq.
EApply included_trans.
Apply H.
Assumption.
EApply included_trans.
Apply H.
Assumption.
Intros; Apply H2.
Apply H; Assumption.
Qed.

End Some_More.

Tactic Definition Included := EAuto with included.

Hints Resolve included_IR included_refl included_refl' compact_map1 compact_map2 compact_map3
  included_compact included2_compact included3_compact
  included_FPlus included_FInv included_FMinus included_FMult included_FRecip included_FDiv
  included_FScalMult included_FNth included_FComp : included.

Hints Immediate included_trans included_FPlus' included_FPlus'' included_FInv'
  included_FMinus' included_FMinus'' included_FMult' included_FMult'' included_FRecip'
  included_FDiv' included_FDiv'' included_FScalMult' included_FNth' included_FComp' : included.

Tactic Definition FEQ := Apply eq_imp_Feq; [Included | Included | Intros; Try (Simpl; Rational)].

Section Away_from_Zero.

Section Definitions.

(* Tex_Prose
\section{Away from Zero}

Before we prove our main results about the equality we have to do some work on division.  A function is said to be \emph{bounded away from zero} in a set if there exists a positive lower bound for the set of absolute values of its image of that set.

\begin{convention} Let \verb!I:IR->CProp!, \verb!F:PartIR! and denote by \verb!P! the domain of \verb!F!.
\end{convention}
*)

Variable I:IR->CProp.
Variable F:PartIR.
Local P:=(Pred F).

(* Begin_Tex_Verb *)
Definition bnd_away_zero := (included I P) * ({c:IR & (Zero[<]c) |
  (y:IR)(Hy:(I y))(Hy':(P y))(c[<=](AbsIR (F y Hy')))}).
(* End_Tex_Verb *)

(* Tex_Prose
If $F$ is bounded away from zero in $I$ then $F$ is necessarily apart from zero in $I$; also this means that $I$ is included in the domain of $\frac1F$.
*)

(* Begin_Tex_Verb *)
Hypothesis Hf:bnd_away_zero.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma bnd_imp_ap_zero :
  (x:IR)(Hx:(I x))(Hx':(P x))(F x Hx')[#]Zero.
(* End_Tex_Verb *)
Intros.
Apply AbsIR_cancel_ap_zero.
Apply Greater_imp_ap.
Elim Hf; Intros.
Inversion_clear b.
EApply less_leEq_trans; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma bnd_imp_inc_recip : (included I (Pred {1/}F)).
(* End_Tex_Verb *)
Red.
Intros.
Elim Hf; Intros.
Split.
Apply (a x H).
Intro.
EApply ap_well_def_lft_unfolded.
Apply (bnd_imp_ap_zero x H H0).
Apply eq_reflexive_unfolded.
Qed.

(* Begin_Tex_Verb *)
Lemma bnd_imp_inc_div : (G:?)(included I (Pred G))->(included I (Pred G{/}F)).
(* End_Tex_Verb *)
Red.
Intros.
Split; Auto.
Elim Hf; Intros.
Split.
Apply (a x H0).
Intro.
EApply ap_well_def_lft_unfolded.
Apply (bnd_imp_ap_zero x H0 H1).
Apply eq_reflexive_unfolded.
Qed.

End Definitions.

(* Tex_Prose
Boundedness away from zero is preserved through restriction of the set.

\begin{convention} Let \verb!F! be a partial function and \verb!P,Q! be predicates.
\end{convention}
*)

Variable F:PartIR.
Variables P,Q:IR->CProp.

(* Begin_Tex_Verb *)
Lemma included_imp_bnd : (included Q P)->
  (bnd_away_zero P F)->(bnd_away_zero Q F).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Inversion_clear H0; Split.
Apply included_trans with P; Auto.
Elim H2; Intros c Hc Hc'.
Exists c; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FRestr_bnd : (HP,H:?)(included Q P)->
  (bnd_away_zero Q F)->(bnd_away_zero Q (!Frestr F P HP H)).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Inversion_clear H1; Split.
Auto.
Elim H3; Intro c; Intros.
Exists c; Auto.
Simpl; Auto.
Qed.

(* Tex_Prose
A function is said to be bounded away from zero \emph{everywhere} if it is bounded away from zero in every compact subinterval of its domain; a similar definition is made for arbitrary sets, which will be necessary for future work.
*)

(* Begin_Tex_Verb *)
Definition bnd_away_zero_everywhere [G:PartIR] : CProp := 
  (a,b:IR)(Hab:?)(included (compact a b Hab) (Pred G))->
  (bnd_away_zero (compact a b Hab) G).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition bnd_away_zero_in_P : CProp := (a,b:IR)(Hab:?)
  (included (compact a b Hab) P)->
  (bnd_away_zero (compact a b Hab) F).
(* End_Tex_Verb *)

(* Tex_Prose
An immediate consequence:
*)

(* Begin_Tex_Verb *)
Lemma bnd_in_P_imp_ap_zero : (pred_well_def ? P)->
  bnd_away_zero_in_P->
  (x:IR)(P x)->(Hx:?)(F x Hx)[#]Zero.
(* End_Tex_Verb *)
Intros.
Apply bnd_imp_ap_zero with (Compact (leEq_reflexive ? x)).
Apply H0.
Red; Intros.
Cut x[=]x0; Intros.
Apply H with x; Auto.
Inversion_clear H2; Apply leEq_imp_eq; Auto.
Split; Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma FRestr_bnd' : (HP,H:?)(bnd_away_zero_everywhere F)->
  (bnd_away_zero_everywhere (!Frestr F P HP H)).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H0 a b Hab); Intros.
Split.
Auto.
Elim b0; Intro c; Intros.
Exists c; Auto.
Simpl; Auto.
Apply included_trans with P; Simpl in H1; Auto.
Qed.

End Away_from_Zero.

Hints Resolve bnd_imp_inc_recip bnd_imp_inc_div : included.
Hints Immediate bnd_in_P_imp_ap_zero : included.

Section More_on_Equality.

(* Tex_Prose
\section{Properties of Equality}

We are now finally able to prove the main properties of the equality relation.  We begin by showing it to be an equivalence relation.

\begin{convention} Let \verb!I! be a predicate and \verb!F,F',G,G',H! be partial functions.
\end{convention}
*)

Variable I:IR->CProp.

Section Feq_Equivalence.

Variables F,G,H:PartIR.

(* Begin_Tex_Verb *)
Lemma Feq_reflexive : (included I (Pred F))->(Feq I F F).
(* End_Tex_Verb *)
Intro; FEQ.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_symmetric : (Feq I F G)->(Feq I G F).
(* End_Tex_Verb *)
Intro.
Elim H0; Intros H' H1.
Elim H'; Intros incF incG.
FEQ; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_transitive : (Feq I F G)->(Feq I G H)->(Feq I F H).
(* End_Tex_Verb *)
Intro.
Elim H0; Intros H' H1.
Elim H'; Intros incF incG.
Clear H0 H'.
Intro.
Elim H0; Intros H' H2.
Elim H'; Intros incG' incH.
Clear H0 H'.
FEQ.
Step_final (G x (incG x H0)).
Qed.

End Feq_Equivalence.

Section Operations.

(* Tex_Prose
Also it is preserved through application of functional constructors and restriction.
*)

Variables F,F',G,G':PartIR.

(* Begin_Tex_Verb *)
Lemma Feq_plus : (Feq I F F')->(Feq I G G')->
  (Feq I F{+}G F'{+}G').
(* End_Tex_Verb *)
Intros H0 H1.
Elim H0; Intros H0' H2.
Elim H0'; Clear H0 H0'; Intros incF incG.
Elim H1; Intros H1' H0.
Elim H1'; Clear H1 H1'; Intros incF' incG'.
FEQ; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_inv : (Feq I F F')->(Feq I {--}F {--}F').
(* End_Tex_Verb *)
Intro H0.
Elim H0; Intros H0' H1.
Elim H0'; Clear H0 H0'; Intros incF incF'.
FEQ; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_minus : (Feq I F F')->(Feq I G G')->
  (Feq I F{-}G F'{-}G').
(* End_Tex_Verb *)
Intros H0 H1.
Elim H0; Intros H0' H2.
Elim H0'; Clear H0 H0'; Intros incF incG.
Elim H1; Intros H1' H0.
Elim H1'; Clear H1 H1'; Intros incF' incG'.
FEQ; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_mult : (Feq I F F')->(Feq I G G')->
  (Feq I F{*}G F'{*}G').
(* End_Tex_Verb *)
Intros H0 H1.
Elim H0; Intros H0' H2.
Elim H0'; Clear H0 H0'; Intros incF incG.
Elim H1; Intros H1' H0.
Elim H1'; Clear H1 H1'; Intros incF' incG'.
FEQ; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_nth : (n:nat)(Feq I F F')->(Feq I F{^}n F'{^}n).
(* End_Tex_Verb *)
Intros n H0.
Elim H0; Intros H0' H1.
Elim H0'; Clear H0 H0'; Intros incF incF'.
FEQ.
Step (F x Hx)[^]n; Step_final (Part F' x Hx')[^]n.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_recip : (bnd_away_zero I F)->(Feq I F F')->
  (Feq I {1/}F {1/}F').
(* End_Tex_Verb *)
Intros Hbnd H0.
Elim H0; Intros H0' H1.
Elim H0'; Clear H0 H0'; Intros incF incF'.
FEQ.
Apply included_FRecip.
Auto.
Intros; Apply ap_well_def_lft_unfolded with (F x (incF x H)).
Apply bnd_imp_ap_zero with I; Assumption.
Auto.
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_recip' : (bnd_away_zero I F)->(Feq I F' F)->
  (Feq I {1/}F' {1/}F).
(* End_Tex_Verb *)
Intros.
Apply Feq_symmetric; Apply Feq_recip.
Assumption.
Apply Feq_symmetric; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_div : (bnd_away_zero I G)->(Feq I F F')->
  (Feq I G G')->(Feq I F{/}G F'{/}G').
(* End_Tex_Verb *)
Intros Hbnd H0 H1.
Elim H0; Intros H0' H2.
Elim H0'; Clear H0 H0'; Intros incF incF'.
Elim H1; Intros H1' H0.
Elim H1'; Clear H1 H1'; Intros incG incG'.
FEQ.
Apply included_FDiv; Auto.
Intros; Apply ap_well_def_lft_unfolded with (G x (incG x H)).
Apply bnd_imp_ap_zero with I; Assumption.
Auto.
Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Feq_div' : (bnd_away_zero I G)->(Feq I F' F)->
  (Feq I G' G)->(Feq I F'{/}G' F{/}G).
(* End_Tex_Verb *)
Intros.
Apply Feq_symmetric; Apply Feq_div.
Assumption.
Apply Feq_symmetric; Assumption.
Apply Feq_symmetric; Assumption.
Qed.

(* Tex_Prose
Notice that in the case of division we only need to require boundedness away from zero for one of the functions (as they are equal); thus the two last lemmas are stated in two different ways, as according to the context one or the other condition may be easier to prove.

Finally, the restriction of a function is well defined.
*)

(* Begin_Tex_Verb *)
Lemma FRestr_wd : (Iwd,Hinc:?)(Feq I F (!Frestr F I Iwd Hinc)).
(* End_Tex_Verb *)
Intros.
FEQ.
Qed.

End Operations.

End More_on_Equality.

Section Nth_Power.

(* Tex_Prose
\section{Nth Power}

We finish this group of lemmas with characterization results for the power function (similar to those already proved for arbitrary rings).  The characterization is done at first pointwise and later using the equality relation.

\begin{convention} Let \verb!F! be a partial function with domain \verb!P! and \verb!Q! be a predicate on the real numbers assumed to be included in \verb!P!.
\end{convention}
*)

Variable F:PartIR.
Local P:=(Pred F).

Variable Q:IR->CProp.
Hypothesis H:(included Q [x:IR]CTrue).
Hypothesis Hf:(included Q (Pred F)).

(* Begin_Tex_Verb *)
Lemma FNth_zero : (x:IR)(Q x)->(Hx:?)(Hx':?)
  ({-C-}One x Hx)[=](F{^}O x Hx').
(* End_Tex_Verb *)
Intros.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Variable n:nat.
Hypothesis H':(included Q (Pred F{*}F{^}n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma FNth_mult : (x:IR)(Q x)->(Hx,Hx':?)
  (F{*}F{^}n x Hx)[=](F{^}(S n) x Hx').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
2: Apply mult_commutes.
Apply mult_wd.
Rational.
Change (F x (ProjIR2 Hx))[^]n[=](F x Hx')[^]n.
Apply nexp_wd; Rational.
Qed.

End Nth_Power.

Section Strong_Nth_Power.

(* Tex_Prose
\begin{convention} Let \verb!a,b! be real numbers such that \verb!I!$=[a,b]$ is included in the domain of \verb!F!.
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab:a[<=]b.
Local I:=(compact a b Hab).

Variable F:PartIR.
Hypothesis incF:(included I (Pred F)).

(* Begin_Tex_Verb *)
Lemma FNth_zero' : (Feq I {-C-}One F{^}O).
(* End_Tex_Verb *)
FEQ.
Qed.

(* Begin_Tex_Verb *)
Lemma FNth_mult' : (n:nat)(Feq I F{*}F{^}n F{^}(S n)).
(* End_Tex_Verb *)
Intro; FEQ.
Simpl.
EApply eq_transitive_unfolded.
2: Apply mult_commutes.
Apply bin_op_wd_unfolded.
Rational.
Change (F x (ProjIR2 Hx))[^]n[=](F x Hx')[^]n.
Apply nexp_wd; Rational.
Qed.

End Strong_Nth_Power.
