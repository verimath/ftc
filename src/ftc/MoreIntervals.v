(* $Id: MoreIntervals.v,v 1.17 2003/03/11 13:36:07 lcf Exp $ *)

Require Export NthDerivative.

Opaque Min Max.

Section Intervals.

(* Tex_Prose
\chapter{Generalized Intervals}

At this stage we have enough material to begin generalizing our concepts in preparation for the fundamental theorem of calculus and the definition of the main (non-polynomial) functions of analysis.

In order to define functions via power series (or any other kind of series!)\ we need to formalize a notion of convergence more general than the one we already have on compact intervals.  This is necessary for practical reasons: we want to define a single exponential function with domain \RR, not several exponential functions defined on compact intervals which we prove to be the same wherever their domains overlap.  In a similar way, we want to define indefinite integrals on infinite domains and not only on compact intervals.

Unfortunately, proceeding in a way analogous to how we defined the concept of global continuity will lead us nowhere; the concept turns out to be to general, and the behaviour on too small domains (typically intervals $[a,a']$ where $a=a'$ is neither provably true nor provably false) will be unsatisfactory.

There is a special family of sets, however, where this problems can be avoided: intervals.  Intervals have some nice properties that allow us to prove good results, namely the facts that if $a$ and $b$ are elements of an interval $I$ then so are $\min(a,b)$ and $\max(a,b)$ (which is in general not true) and also the compact interval $[a,b]$ is included in $I$.  Furthermore, all intervals are characterized by simple, well defined predicates, and the nonempty and proper concepts become very easy to define.

\section{Definitions and Basic Results}

We define an inductive type of intervals\footnote{The compact interval which we will define here is obviously the same that we have been working with all the way through; why, then, the different formulation?  The reason is simple: if we had worked with intervals from the beginning we would have had case definitions at every spot, and our lemmas and proofs would have been very awkward.  Also, it seems more natural to characterize a compact interval by two real numbers [and a proof] than as a particular case of a more general concept which doesn't have an intuitive interpretation.  Finally, the definitions we will make here will have the elegant consequence that from this point on we can work with \emph{any} kind of intervals in exactly the same way.} with nine constructors, corresponding to the nine basic types of intervals\footnote{The reason why so many constructors are needed is that we do not have a notion of real line, for many reasons which we will not discuss here.  Also it seems simple to directly define finite intervals than to define then later as intersections of infinite intervals, as it would only mess things up.}.
*)

(* Begin_Tex_Verb *)
Inductive interval : Set :=
  realline : interval
  | openl : IR->interval
  | openr : IR->interval
  | closel : IR->interval
  | closer : IR->interval
  | olor : IR->IR->interval
  | olcr : IR->IR->interval
  | clor : IR->IR->interval
  | clcr : IR->IR->interval.
(* End_Tex_Verb *)

(* Tex_Prose
To each interval a predicate (set) is assigned by the following map:
*)

(* Begin_Tex_Verb *)
Definition iprop [I:interval] : IR->CProp := [x:IR] Cases I of
  realline     => CTrue
  | (openr b)  => x[<]b
  | (openl a)  => a[<]x
  | (closer b) => (toCProp x[<=]b)
  | (closel a) => (toCProp a[<=]x)
  | (olor a b) => (a[<]x)*(x[<]b)
  | (olcr a b) => (a[<]x)*{x[<=]b}
  | (clor a b) => {a[<=]x}*(x[<]b)
  | (clcr a b) => {a[<=]x}*{x[<=]b}
  end.
(* End_Tex_Verb *)

(* Tex_Prose
We now define what it means for an interval to be nonvoid, proper, finite and compact in the obvious way.
*)

(* Begin_Tex_Verb *)
Definition nonvoid [I:interval] : CProp := Cases I of
  realline     => CTrue
  | (openr b)  => CTrue
  | (openl a)  => CTrue
  | (closer b) => CTrue
  | (closel a) => CTrue
  | (olor a b) => a[<]b
  | (olcr a b) => a[<]b
  | (clor a b) => a[<]b
  | (clcr a b) => (toCProp a[<=]b)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition proper [I:interval] : CProp := Cases I of
  realline     => CTrue
  | (openr b)  => CTrue
  | (openl a)  => CTrue
  | (closer b) => CTrue
  | (closel a) => CTrue
  | (olor a b) => a[<]b
  | (olcr a b) => a[<]b
  | (clor a b) => a[<]b
  | (clcr a b) => a[<]b
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition finite [I:interval] : CProp := Cases I of
  realline     => CFalse
  | (openr b)  => CFalse
  | (openl a)  => CFalse
  | (closer b) => CFalse
  | (closel a) => CFalse
  | (olor a b) => CTrue
  | (olcr a b) => CTrue
  | (clor a b) => CTrue
  | (clcr a b) => CTrue
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition compact_ [I:interval] : CProp := Cases I of
  realline     => CFalse
  | (openr b)  => CFalse
  | (openl a)  => CFalse
  | (closer b) => CFalse
  | (closel a) => CFalse
  | (olor a b) => CFalse
  | (olcr a b) => CFalse
  | (clor a b) => CFalse
  | (clcr a b) => (toCProp a[<=]b)
  end.
(* End_Tex_Verb *)

(* Tex_Prose
Finite intervals have a left end and a right end.
*)

(* Begin_Tex_Verb *)
Definition left_end [I:interval] : (finite I)->IR.
(* End_Tex_Verb *)
Intro.
Elim I; Intros.
Inversion H.
Inversion H.
Inversion H.
Inversion H.
Inversion H.
Apply c.
Apply c.
Apply c.
Apply c.
Defined.

(* Begin_Tex_Verb *)
Definition right_end [I:interval] : (finite I)->IR.
(* End_Tex_Verb *)
Intro.
Elim I; Intros.
Inversion H.
Inversion H.
Inversion H.
Inversion H.
Inversion H.
Apply c0.
Apply c0.
Apply c0.
Apply c0.
Defined.

(* Tex_Prose
Some trivia: compact intervals are finite; proper intervals are nonvoid; an interval is nonvoid iff it contains some point.
*)

(* Begin_Tex_Verb *)
Lemma compact_finite : (I:interval)(compact_ I)->(finite I).
(* End_Tex_Verb *)
Intros; Induction I; Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma proper_nonvoid : (I:interval)(proper I)->(nonvoid I).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Auto.
Apply ts; Apply less_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nonvoid_point : (I:interval)(nonvoid I)->{x:IR & (iprop I x)}.
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros.
Exists (Zero::IR); Auto.
Exists c[+]One; Apply less_plusOne.
Exists c[-]One; Apply shift_minus_less; Apply less_plusOne.
Exists c; Apply ts; Apply leEq_reflexive.
Exists c; Apply ts; Apply leEq_reflexive.
Exists c[+](c0[-]c)[/]TwoNZ; Split.
Step c[+]Zero; Apply plus_resp_less_lft.
Apply div_resp_pos.
Apply pos_two.
Apply shift_less_minus; Step c; Auto.
RStepr c[+](c0[-]c).
Apply plus_resp_less_lft.
Apply pos_div_two'.
Apply shift_less_minus; Step c; Auto.
Exists c0; Split; Auto; Apply leEq_reflexive.
Exists c; Split; Auto; Apply leEq_reflexive.
Exists c; Split; [Apply leEq_reflexive | Inversion H; Auto].
Qed.

(* Begin_Tex_Verb *)
Lemma nonvoid_char : (I:interval)(x:IR)(iprop I x)->(nonvoid I).
(* End_Tex_Verb *)
Intro; Elim I; Simpl; Intros; Auto; Inversion_clear H.
Apply less_transitive_unfolded with x; Auto.
Apply less_leEq_trans with x; Auto.
Apply leEq_less_trans with x; Auto.
Apply ts; Apply leEq_transitive with x; Auto.
Qed.

(* Tex_Prose
For practical reasons it helps to define left end and right end of compact intervals.
*)

(* Begin_Tex_Verb *)
Definition Lend [I:interval][H:(compact_ I)] :=
  (left_end I (compact_finite I H)).
Definition Rend [I:interval][H:(compact_ I)] :=
  (right_end I (compact_finite I H)).
(* End_Tex_Verb *)

(* Tex_Prose
In a compact interval, the left end is always less than or equal to the right end.
*)

(* Begin_Tex_Verb *)
Lemma Lend_leEq_Rend :
  (I:interval)(cI:(compact_ I))(Lend ? cI)[<=](Rend ? cI).
(* End_Tex_Verb *)
Intro; Elim I; Simpl; Intros; Try Inversion cI; Auto.
Qed.

(* Tex_Prose
Some nice characterizations of inclusion:
*)

(* Begin_Tex_Verb *)
Lemma compact_included : (a,b,Hab,I:?)(iprop I a)->(iprop I b)->
  (included (compact a b Hab) (iprop I)).
(* End_Tex_Verb *)
Induction I; Red; Simpl; Intros; Try Inversion_clear H; Try Inversion_clear H0; Try Inversion_clear H1; Try Apply ts.
Auto.
Apply less_leEq_trans with a; Auto.
Apply leEq_less_trans with b; Auto.
Apply leEq_transitive with a; Auto.
Apply leEq_transitive with b; Auto.
Split; [Apply less_leEq_trans with a| Apply leEq_less_trans with b]; Auto.
Split; [Apply less_leEq_trans with a| Apply leEq_transitive with b]; Auto.
Split; [Apply leEq_transitive with a| Apply leEq_less_trans with b]; Auto.
Split; [Apply leEq_transitive with a| Apply leEq_transitive with b]; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_interval' : (I,x,y,z,w:?)
  (iprop I x)->(iprop I y)->(iprop I z)->(iprop I w)->
  (H:?)(included (compact (Min x z) (Max y w) H) (iprop I)).
(* End_Tex_Verb *)
Intro I; Elim I; Simpl; Intros; Red; Intros t Ht; Inversion_clear Ht; Simpl; 
  Try Inversion_clear H; Try Inversion_clear H0; Try Inversion_clear H1; Try Inversion_clear H2; Try Split.
Apply less_leEq_trans with (Min x z); Try Apply less_Min; Auto.
Apply leEq_less_trans with (Max y w); Try Apply Max_less; Auto.
Apply leEq_transitive with (Min x z); Try Apply leEq_Min; Auto.
Apply leEq_transitive with (Max y w); Try Apply Max_leEq; Auto.
Apply less_leEq_trans with (Min x z); Try Apply less_Min; Auto.
Apply leEq_less_trans with (Max y w); Try Apply Max_less; Auto.
Apply less_leEq_trans with (Min x z); Try Apply less_Min; Auto.
Apply leEq_transitive with (Max y w); Try Apply Max_leEq; Auto.
Apply leEq_transitive with (Min x z); Try Apply leEq_Min; Auto.
Apply leEq_less_trans with (Max y w); Try Apply Max_less; Auto.
Apply leEq_transitive with (Min x z); Try Apply leEq_Min; Auto.
Apply leEq_transitive with (Max y w); Try Apply Max_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_interval : (I,x,y:?)(iprop I x)->(iprop I y)->
  (H:?)(included (compact (Min x y) (Max x y) H) (iprop I)).
(* End_Tex_Verb *)
Intros; Apply included_interval'; Auto.
Qed.

(* Tex_Prose
A weirder inclusion result.
*)

(* Begin_Tex_Verb *)
Lemma included3_interval : (I:?)(x,y,z:IR)(Hxyz:?)
  (iprop I x)->(iprop I y)->(iprop I z)->
  (included (compact (Min (Min x y) z) (Max (Max x y) z) Hxyz)
            (iprop I)).
(* End_Tex_Verb *)
Intros.
Apply included_interval'; Auto.
Apply (included_interval I x y H H0 (Min_leEq_Max ??)).
Apply compact_inc_lft.
Apply (included_interval I x y H H0 (Min_leEq_Max ??)).
Apply compact_inc_rht.
Qed.

(* Tex_Prose
Finally, all intervals are characterized by well defined predicates.
*)

(* Begin_Tex_Verb *)
Lemma iprop_wd : (I:interval)(pred_well_def ? (iprop I)).
(* End_Tex_Verb *)
Intro; Elim I; Unfold iprop; Red; Intros; Try Inversion_clear H; Try Inversion H0; Try Inversion H1; Try Apply ts.
Auto.
Stepr x; Auto.
Step x; Auto.
Stepr x; Auto.
Step x; Auto.
Split.
Stepr x; Auto.
Step x; Auto.
Split.
Stepr x; Auto.
Step x; Auto.
Split.
Stepr x; Auto.
Step x; Auto.
Split.
Stepr x; Auto.
Step x; Auto.
Qed.

End Intervals.

Implicits Lend [1].
Implicits Rend [1].

Section Compact_Constructions.

Section Single_Compact_Interval.

(* Tex_Prose
\section{Constructions with Compact Intervals}

Several important constructions are now discussed.

We begin by defining the compact interval $[x,x]$.

\begin{convention} Let \verb!P:IR->CProp! be well defined, and \verb!x:IR! such that $P(x)$ holds.
\end{convention}
*)

Variable P:IR->CProp.
Hypothesis wdP : (pred_well_def IR P).
Variable x:IR.

Hypothesis Hx : (P x).

(* Begin_Tex_Verb *)
Definition compact_single := (Compact (leEq_reflexive ? x)).
(* End_Tex_Verb *)

(* Tex_Prose
This interval contains $x$ and only (elements equal to) $x$; furthermore, for every (well-defined) $P$, if $x\in P$ then $[x,x]\subseteq P$.
*)

(* Begin_Tex_Verb *)
Lemma compact_single_prop : (compact_single x).
(* End_Tex_Verb *)
Split; Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma compact_single_pt : (y:IR)(compact_single y)->x[=]y.
(* End_Tex_Verb *)
Intros.
Inversion_clear H; Apply leEq_imp_eq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma compact_single_inc : (included compact_single P).
(* End_Tex_Verb *)
Red; Intros.
Apply wdP with x.
Auto.
Apply compact_single_pt; Auto.
Qed.

End Single_Compact_Interval.

(* Tex_Prose
The special case of intervals is worth singling out, as one of the hypothesis becomes a theorem.
*)

(* Begin_Tex_Verb *)
Definition compact_single_iprop [I:interval] :=
  (compact_single_inc (iprop I) (iprop_wd I)).
(* End_Tex_Verb *)

(* Tex_Prose
Now for more interesting and important results.

Let $I$ be a proper interval and $x$ be a point of $I$.  Then there is a proper compact interval $[a,b]$ such that $x\in[a,b]\subseteq I$.
*)

Section Proper_Compact_with_One_or_Two_Points.

Local cip1' : (c,x:IR)(c[<=]x)->(x[-](x[-]c)[/]TwoNZ)[<=]x.
Intros.
Stepr x[-]Zero.
Unfold 1 3 cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq; Apply shift_leEq_div.
Apply pos_two.
Apply shift_leEq_minus; RStep c; Auto.
Qed.

Local cip1'' : (c,x:IR)(c[<]x)->(x[-](x[-]c)[/]TwoNZ)[<]x.
Intros.
Stepr x[-]Zero.
Unfold 1 3 cg_minus; Apply plus_resp_less_lft.
Apply inv_resp_less; Apply shift_less_div.
Apply pos_two.
Apply shift_less_minus; RStep c; Auto.
Qed.

Local cip1''' : (c0,x:IR)(x[<=]c0)->x[<=](x[+](c0[-]x)[/]TwoNZ).
Intros.
Step x[+]Zero.
Apply plus_resp_leEq_lft.
Apply shift_leEq_div.
Apply pos_two.
Apply shift_leEq_minus; RStep x; Auto.
Qed.

Local cip1'''' : (c0,x:IR)(x[<]c0)->x[<](x[+](c0[-]x)[/]TwoNZ).
Intros.
Step x[+]Zero.
Apply plus_resp_less_lft.
Apply shift_less_div.
Apply pos_two.
Apply shift_less_minus; RStep x; Auto.
Qed.

Local cip2 : (c,x,x0:IR)(c[<=]x)->((x[-](x[-]c)[/]TwoNZ)[<=]x0)->(c[<=]x0).
Intros.
Apply leEq_transitive with c[+](x[-]c)[/]TwoNZ.
Step c[+]Zero; Apply plus_resp_leEq_lft.
Apply shift_leEq_div.
Apply pos_two.
Apply shift_leEq_minus; RStep c; Auto.
EApply leEq_wdl.
Apply H0.
Rational.
Qed.

Local cip2' : (c,x,x0:IR)(c[<]x)->((x[-](x[-]c)[/]TwoNZ)[<=]x0)->(c[<]x0).
Intros.
Apply less_leEq_trans with c[+](x[-]c)[/]TwoNZ.
Step c[+]Zero; Apply plus_resp_less_lft.
Apply shift_less_div.
Apply pos_two.
Apply shift_less_minus; RStep c; Auto.
EApply leEq_wdl.
Apply H0.
Rational.
Qed.

Local cip2'' : (c,x,x0:IR)(c[<=]x)->((x[-](x[-]c)[/]TwoNZ)[<]x0)->(c[<]x0).
Intros.
Apply leEq_less_trans with c[+](x[-]c)[/]TwoNZ.
Step c[+]Zero; Apply plus_resp_leEq_lft.
Apply shift_leEq_div.
Apply pos_two.
Apply shift_leEq_minus; RStep c; Auto.
EApply less_wdl.
Apply H0.
Rational.
Qed.

Local cip2''' : (c,x,x0:IR)(c[<]x)->((x[-](x[-]c)[/]TwoNZ)[<]x0)->(c[<]x0).
Intros.
Apply cip2'' with x.
Apply less_leEq; Auto.
Auto.
Qed.

Local cip3 : (c0,x,x0:IR)(x[<=]c0)->(x0[<=](x[+](c0[-]x)[/]TwoNZ))->(x0[<=]c0).
Intros.
EApply leEq_transitive.
Apply H0.
RStep c0[-](c0[-]x)[/]TwoNZ.
Stepr c0[-]Zero; Unfold 1 3 cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq.
Apply shift_leEq_div.
Apply pos_two.
Apply shift_leEq_minus; RStep x; Auto.
Qed.

Local cip3' : (c0,x,x0:IR)(x[<]c0)->(x0[<=](x[+](c0[-]x)[/]TwoNZ))->(x0[<]c0).
Intros.
EApply leEq_less_trans.
Apply H0.
RStep c0[-](c0[-]x)[/]TwoNZ.
Stepr c0[-]Zero; Unfold 1 3 cg_minus; Apply plus_resp_less_lft.
Apply inv_resp_less.
Apply shift_less_div.
Apply pos_two.
Apply shift_less_minus; RStep x; Auto.
Qed.

Local cip3'' : (c0,x,x0:IR)(x[<=]c0)->(x0[<](x[+](c0[-]x)[/]TwoNZ))->(x0[<]c0).
Intros.
EApply less_leEq_trans.
Apply H0.
RStep c0[-](c0[-]x)[/]TwoNZ.
Stepr c0[-]Zero; Unfold 1 3 cg_minus; Apply plus_resp_leEq_lft.
Apply inv_resp_leEq.
Apply shift_leEq_div.
Apply pos_two.
Apply shift_leEq_minus; RStep x; Auto.
Qed.

Local cip3''' : (c0,x,x0:IR)(x[<]c0)->(x0[<](x[+](c0[-]x)[/]TwoNZ))->(x0[<]c0).
Intros.
Apply cip3'' with x; Try Apply less_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Definition compact_in_interval
  [I:interval][pI:(proper I)][x:IR][Hx:(iprop I x)] : interval.
(* End_Tex_Verb *)
Intros; Elim I; Intros.
Apply (clcr x x[+]One).
Apply (clcr x x[+]One).
Apply (clcr x[-]One x).
Apply (clcr x x[+]One).
Apply (clcr x[-]One x).
Apply (clcr x[-](x[-]c)[/]TwoNZ x[+](c0[-]x)[/]TwoNZ).
Apply (clcr x[-](x[-]c)[/]TwoNZ x[+](c0[-]x)[/]TwoNZ).
Apply (clcr x[-](x[-]c)[/]TwoNZ x[+](c0[-]x)[/]TwoNZ).
Apply (clcr c c0).
Defined.

(* Begin_Tex_Verb *)
Lemma compact_compact_in_interval : (I,pI,x,Hx:?)
  (compact_ (compact_in_interval I pI x Hx)).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx; Try Apply ts; Apply less_leEq.
Apply less_plusOne.
Apply less_plusOne.
Apply shift_minus_less; Apply less_plusOne.
Apply less_plusOne.
Apply shift_minus_less; Apply less_plusOne.
EApply less_transitive_unfolded; [Apply cip1'' | Apply cip1'''']; Auto.
EApply less_leEq_trans; [Apply cip1'' | Apply cip1''']; Auto.
EApply leEq_less_trans; [Apply cip1' | Apply cip1'''']; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma proper_compact_in_interval : (I,pI,x,Hx:?)
  (proper (compact_in_interval I pI x Hx)).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx.
Apply less_plusOne.
Apply less_plusOne.
Apply shift_minus_less; Apply less_plusOne.
Apply less_plusOne.
Apply shift_minus_less; Apply less_plusOne.
EApply less_transitive_unfolded; [Apply cip1'' | Apply cip1'''']; Auto.
EApply less_leEq_trans; [Apply cip1'' | Apply cip1''']; Auto.
EApply leEq_less_trans; [Apply cip1' | Apply cip1'''']; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma proper_compact_in_interval' :
  (I,pI,x,Hx,H:?)(!Lend (compact_in_interval I pI x Hx) H)[<]
                 (!Rend (compact_in_interval I pI x Hx) H).
(* End_Tex_Verb *)
Do 4 Intro.
Cut (proper (compact_in_interval I pI x Hx)).
2: Apply proper_compact_in_interval.
Elim (compact_in_interval I pI x Hx); Intros; Try Inversion H0.
Simpl; Simpl in H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_compact_in_interval : (I,pI,x,Hx:?)
  (included (iprop (compact_in_interval I pI x Hx)) (iprop I)).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; 
  Try Inversion_clear Hx; Red; Simpl; Intros;
  Try Inversion_clear H; Try Inversion_clear H0; Try Inversion_clear H1; Try Inversion H2; Try Inversion H3; Try Apply ts; Auto.
Apply less_leEq_trans with x; Auto.
Apply leEq_less_trans with x; Auto.
Apply leEq_transitive with x; Auto.
Apply leEq_transitive with x; Auto.
Split.
Apply cip2' with x; Auto.
Apply cip3' with x; Auto.
Split.
Apply cip2' with x; Auto.
Apply cip3 with x; Auto.
Split.
Apply cip2 with x; Auto.
Apply cip3' with x; Auto.
Split; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval :
  (I,pI,x,Hx:?)(iprop (compact_in_interval I pI x Hx) x).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx; Split; Auto; Try Apply leEq_reflexive.
Apply less_leEq; Apply less_plusOne.
Apply less_leEq; Apply less_plusOne.
Apply less_leEq; Apply shift_minus_less; Apply less_plusOne.
Apply less_leEq; Apply less_plusOne.
Apply less_leEq; Apply shift_minus_less; Apply less_plusOne.
Apply less_leEq; Apply cip1''; Auto.
Apply less_leEq; Apply cip1''''; Auto.
Apply less_leEq; Apply cip1''; Auto.
Apply less_leEq; Apply cip1''''; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval' : (I,pI,x,Hx,H,H':?)
  (compact (!Lend (compact_in_interval I pI x Hx) H)
           (!Rend (compact_in_interval I pI x Hx) H) H' x).
(* End_Tex_Verb *)
Do 4 Intro.
Cut (iprop (compact_in_interval I pI x Hx) x).
2: Apply iprop_compact_in_interval.
Elim (compact_in_interval I pI x Hx); Intros; Try Inversion H0.
Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval_inc1 : (I,pI,x,Hx,H,H':?)
  (included (compact (!Lend (compact_in_interval I pI x Hx) H)
                     (!Rend (compact_in_interval I pI x Hx) H) H') 
    (iprop (compact_in_interval I pI x Hx))).
(* End_Tex_Verb *)
Do 4 Intro.
Elim (compact_in_interval I pI x Hx); Intros; Try Inversion H.
Unfold compact; Unfold iprop; Simpl; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval_inc2 : (I,pI,x,Hx,H,H':?)
  (included
    (iprop (compact_in_interval I pI x Hx))
    (compact (!Lend (compact_in_interval I pI x Hx) H)
             (!Rend (compact_in_interval I pI x Hx) H) H')).
(* End_Tex_Verb *)
Do 4 Intro.
Elim (compact_in_interval I pI x Hx); Intros; Try Inversion H.
Unfold compact; Unfold iprop; Simpl; Included.
Qed.

(* Tex_Prose
If $x=y$ then the construction yields the same interval whether we use $x$ or $y$ in its definition\footnote{This property is required at some stage, which is why we formalized this result as a functional definition rather than as an existential formula.}.
*)

(* Begin_Tex_Verb *)
Lemma compact_in_interval_wd1 : (I,pI,x,Hx,y,Hy,H,H':?)(x[=]y)->
  (!Lend (compact_in_interval I pI x Hx) H)[=]
    (!Lend (compact_in_interval I pI y Hy) H').
(* End_Tex_Verb *)
Intro I; Elim I; Simpl; Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma compact_in_interval_wd2 : (I,pI,x,Hx,y,Hy,H,H':?)(x[=]y)->
  (!Rend (compact_in_interval I pI x Hx) H)[=]
    (!Rend (compact_in_interval I pI y Hy) H').
(* End_Tex_Verb *)
Intro I; Elim I; Simpl; Intros; Algebra.
Qed.

(* Tex_Prose
We can make an analogous construction for two points.
*)

(* Begin_Tex_Verb *)
Definition compact_in_interval2 [I:interval][pI:(proper I)]
  [x,y:IR][Hx:(iprop I x)][Hy:(iprop I y)] : interval.
(* End_Tex_Verb *)
Intros.
LetTac z1:=(Min x y).
LetTac z2:=(Max x y).
Elim I; Intros.
Apply (clcr z1 z2[+]One).
Apply (clcr z1 z2[+]One).
Apply (clcr z1[-]One z2).
Apply (clcr z1 z2[+]One).
Apply (clcr z1[-]One z2).
Apply (clcr z1[-](z1[-]c)[/]TwoNZ z2[+](c0[-]z2)[/]TwoNZ).
Apply (clcr z1[-](z1[-]c)[/]TwoNZ z2[+](c0[-]z2)[/]TwoNZ).
Apply (clcr z1[-](z1[-]c)[/]TwoNZ z2[+](c0[-]z2)[/]TwoNZ).
Apply (clcr c c0).
Defined.

(* Begin_Tex_Verb *)
Lemma compact_compact_in_interval2 : (I,pI,x,y,Hx,Hy:?)
  (compact_ (compact_in_interval2 I pI x y Hx Hy)).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx; Try Inversion_clear Hy; Try Apply ts; Apply less_leEq.
Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply shift_minus_less; Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply shift_minus_less; Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
EApply less_transitive_unfolded; [Apply cip1'' | EApply leEq_less_trans; [Apply Min_leEq_Max | Apply cip1'''']]; 
  Try Apply less_Min; Try Apply Max_less; Auto.
EApply less_leEq_trans; [Apply cip1'' | EApply leEq_transitive; [Apply Min_leEq_Max | Apply cip1''']]; 
  Try Apply less_Min; Try Apply Max_leEq; Auto.
EApply leEq_less_trans; [Apply cip1' | EApply leEq_less_trans; [Apply Min_leEq_Max | Apply cip1'''']]; 
  Try Apply leEq_Min; Try Apply Max_less; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma proper_compact_in_interval2 : (I,pI,x,y,Hx,Hy:?)
  (proper (compact_in_interval2 I pI x y Hx Hy)).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx; Try Inversion_clear Hy.
Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply shift_minus_less; Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
Apply shift_minus_less; Apply leEq_less_trans with (Max x y); [Apply Min_leEq_Max | Apply less_plusOne].
EApply less_transitive_unfolded; [Apply cip1'' | EApply leEq_less_trans; [Apply Min_leEq_Max | Apply cip1'''']];
  Try Apply less_Min; Try Apply Max_less; Auto.
EApply less_leEq_trans; [Apply cip1'' | EApply leEq_transitive; [Apply Min_leEq_Max | Apply cip1''']]; 
  Try Apply less_Min; Try Apply Max_leEq; Auto.
EApply leEq_less_trans; [Apply cip1' | EApply leEq_less_trans; [Apply Min_leEq_Max | Apply cip1'''']]; 
  Try Apply leEq_Min; Try Apply Max_less; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma proper_compact_in_interval2' : (I,pI,x,y,Hx,Hy,H:?)
  (!Lend (compact_in_interval2 I pI x y Hx Hy) H)[<]
    (!Rend (compact_in_interval2 I pI x y Hx Hy) H).
(* End_Tex_Verb *)
Do 6 Intro.
Cut (proper (compact_in_interval2 I pI x y Hx Hy)).
2: Apply proper_compact_in_interval2.
Elim (compact_in_interval2 I pI x y Hx Hy); Intros; Try Inversion H0.
Simpl; Simpl in H; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma included_compact_in_interval2 : (I,pI,x,y,Hx,Hy:?)
  (included (iprop (compact_in_interval2 I pI x y Hx Hy))
            (iprop I)).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx; Try Inversion_clear Hy; Red; Simpl; Intros; 
  Try Inversion_clear H; Try Inversion_clear H1; Try Inversion_clear H3; Try Apply ts; Auto.
Apply less_leEq_trans with (Min x y); Try Apply less_Min; Auto.
Apply leEq_less_trans with (Max x y); Try Apply Max_less; Auto.
Apply leEq_transitive with (Min x y); Try Apply leEq_Min; Auto.
Apply leEq_transitive with (Max x y); Try Apply Max_leEq; Auto.
Split.
Apply cip2' with (Min x y); Try Apply less_Min; Auto.
Apply cip3' with (Max x y); Try Apply Max_less; Auto.
Split.
Apply cip2' with (Min x y); Try Apply less_Min; Auto.
Apply cip3 with (Max x y); Try Apply Max_leEq; Auto.
Split.
Apply cip2 with (Min x y); Try Apply leEq_Min; Auto.
Apply cip3' with (Max x y); Try Apply Max_less; Auto.
Split; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval2x : (I,pI,x,y,Hx,Hy:?)
  (iprop (compact_in_interval2 I pI x y Hx Hy) x).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx; Try Inversion_clear Hy; Split; Auto; Try Apply Min_leEq_lft; Try Apply lft_leEq_Max.
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply lft_leEq_Max | Apply less_plusOne].
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply lft_leEq_Max | Apply less_plusOne].
Apply less_leEq; Apply shift_minus_less; Apply leEq_less_trans with x; [Apply Min_leEq_lft | Apply less_plusOne].
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply lft_leEq_Max | Apply less_plusOne].
Apply less_leEq; Apply shift_minus_less; Apply leEq_less_trans with x; [Apply Min_leEq_lft | Apply less_plusOne].
Apply less_leEq; EApply less_leEq_trans; [Apply cip1'' | Apply Min_leEq_lft]; Try Apply less_Min; Auto.
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply lft_leEq_Max | Apply cip1'''']; Try Apply Max_less; Auto.
Apply less_leEq; EApply less_leEq_trans; [Apply cip1'' | Apply Min_leEq_lft]; Try Apply less_Min; Auto.
Apply leEq_transitive with (Max x y); [Apply lft_leEq_Max | Apply cip1''']; Try Apply Max_leEq; Auto.
EApply leEq_transitive; [Apply cip1' | Apply Min_leEq_lft]; Try Apply leEq_Min; Auto.
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply lft_leEq_Max | Apply cip1'''']; Try Apply Max_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval2y : (I,pI,x,y,Hx,Hy:?)
  (iprop (compact_in_interval2 I pI x y Hx Hy) y).
(* End_Tex_Verb *)
Intro.
Elim I; Simpl; Intros; Try Inversion_clear Hx; Try Inversion_clear Hy; Split; Auto; Try Apply Min_leEq_rht; Try Apply rht_leEq_Max.
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply rht_leEq_Max | Apply less_plusOne].
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply rht_leEq_Max | Apply less_plusOne].
Apply less_leEq; Apply shift_minus_less; Apply leEq_less_trans with y; [Apply Min_leEq_rht | Apply less_plusOne].
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply rht_leEq_Max | Apply less_plusOne].
Apply less_leEq; Apply shift_minus_less; Apply leEq_less_trans with y; [Apply Min_leEq_rht | Apply less_plusOne].
Apply less_leEq; EApply less_leEq_trans; [Apply cip1'' | Apply Min_leEq_rht]; Try Apply less_Min; Auto.
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply rht_leEq_Max | Apply cip1'''']; Try Apply Max_less; Auto.
Apply less_leEq; EApply less_leEq_trans; [Apply cip1'' | Apply Min_leEq_rht]; Try Apply less_Min; Auto.
Apply leEq_transitive with (Max x y); [Apply rht_leEq_Max | Apply cip1''']; Try Apply Max_leEq; Auto.
EApply leEq_transitive; [Apply cip1' | Apply Min_leEq_rht]; Try Apply leEq_Min; Auto.
Apply less_leEq; Apply leEq_less_trans with (Max x y); [Apply rht_leEq_Max | Apply cip1'''']; Try Apply Max_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval2x' : (I,pI,x,y,Hx,Hy,H,H':?)
  (compact (!Lend (compact_in_interval2 I pI x y Hx Hy) H)
           (!Rend (compact_in_interval2 I pI x y Hx Hy) H) H' x).
(* End_Tex_Verb *)
Do 6 Intro.
Cut (iprop (compact_in_interval2 I pI x y Hx Hy) x).
2: Apply iprop_compact_in_interval2x.
Elim (compact_in_interval2 I pI x y Hx Hy); Intros; Try Inversion H0.
Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval2y' : (I,pI,x,y,Hx,Hy,H,H':?)
  (compact (!Lend (compact_in_interval2 I pI x y Hx Hy) H)
           (!Rend (compact_in_interval2 I pI x y Hx Hy) H) H' y).
(* End_Tex_Verb *)
Do 6 Intro.
Cut (iprop (compact_in_interval2 I pI x y Hx Hy) y).
2: Apply iprop_compact_in_interval2y.
Elim (compact_in_interval2 I pI x y Hx Hy); Intros; Try Inversion H0.
Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval2_inc1 : (I,pI,x,y,Hx,Hy,H,H':?)
  (included
    (compact (!Lend (compact_in_interval2 I pI x y Hx Hy) H)
             (!Rend (compact_in_interval2 I pI x y Hx Hy) H) H') 
    (iprop (compact_in_interval2 I pI x y Hx Hy))).
(* End_Tex_Verb *)
Do 6 Intro.
Elim (compact_in_interval2 I pI x y Hx Hy); Intros; Try Inversion H.
Unfold compact; Unfold iprop; Simpl; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma iprop_compact_in_interval2_inc2 : (I,pI,x,y,Hx,Hy,H,H':?)
  (included
    (iprop (compact_in_interval2 I pI x y Hx Hy))
    (compact (!Lend (compact_in_interval2 I pI x y Hx Hy) H)
             (!Rend (compact_in_interval2 I pI x y Hx Hy) H) H')).
(* End_Tex_Verb *)
Do 6 Intro.
Elim (compact_in_interval2 I pI x y Hx Hy); Intros; Try Inversion H.
Unfold compact; Unfold iprop; Simpl; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma compact_in_interval_x_lft : (I,pI,x,y,Hx,Hy,H,H':?)
  (!Lend (compact_in_interval2 I pI x y Hx Hy) H)[<=]
    (!Lend (compact_in_interval I pI x Hx) H').
(* End_Tex_Verb *)
Intro I; Elim I; Simpl; Intros; Try Apply minus_resp_leEq; Try Apply Min_leEq_lft; Try Apply leEq_reflexive;
  (RStep c[+]((Min x y)[-]c)[/]TwoNZ; RStepr c[+](x[-]c)[/]TwoNZ; Apply plus_resp_leEq_lft;
  Apply div_resp_leEq; [Apply pos_two | Apply minus_resp_leEq; Apply Min_leEq_lft]).
Qed.

(* Begin_Tex_Verb *)
Lemma compact_in_interval_y_lft : (I,pI,x,y,Hx,Hy,H,H':?)
  (!Lend (compact_in_interval2 I pI x y Hx Hy) H)[<=]
    (!Lend (compact_in_interval I pI y Hy) H').
(* End_Tex_Verb *)
Intro I; Elim I; Simpl; Intros; Try Apply minus_resp_leEq; Try Apply Min_leEq_rht; Try Apply leEq_reflexive;
  (RStep c[+]((Min x y)[-]c)[/]TwoNZ; RStepr c[+](y[-]c)[/]TwoNZ; Apply plus_resp_leEq_lft;
  Apply div_resp_leEq; [Apply pos_two | Apply minus_resp_leEq; Apply Min_leEq_rht]).
Qed.

(* Begin_Tex_Verb *)
Lemma compact_in_interval_x_rht : (I,pI,x,y,Hx,Hy,H,H':?)
  (!Rend (compact_in_interval I pI x Hx) H)[<=]
    (!Rend (compact_in_interval2 I pI x y Hx Hy) H').
(* End_Tex_Verb *)
Intro I; Elim I; Simpl; Intros; Try Apply plus_resp_leEq; Try Apply lft_leEq_Max; Try Apply leEq_reflexive;
  (RStep c0[-](c0[-]x)[/]TwoNZ; RStepr c0[-](c0[-](Max x y))[/]TwoNZ;
  Unfold cg_minus; Apply plus_resp_leEq_lft; Apply inv_resp_leEq; Apply div_resp_leEq;
  [Apply pos_two | Apply plus_resp_leEq_lft; Apply inv_resp_leEq; Apply lft_leEq_Max]).
Qed.

(* Begin_Tex_Verb *)
Lemma compact_in_interval_y_rht : (I,pI,x,y,Hx,Hy,H,H':?)
  (!Rend (compact_in_interval I pI y Hy) H)[<=]
    (!Rend (compact_in_interval2 I pI x y Hx Hy) H').
(* End_Tex_Verb *)
Intro I; Elim I; Simpl; Intros; Try Apply plus_resp_leEq; Try Apply rht_leEq_Max; Try Apply leEq_reflexive;
  (RStep c0[-](c0[-]y)[/]TwoNZ; RStepr c0[-](c0[-](Max x y))[/]TwoNZ;
  Unfold cg_minus; Apply plus_resp_leEq_lft; Apply inv_resp_leEq; Apply div_resp_leEq;
  [Apply pos_two | Apply plus_resp_leEq_lft; Apply inv_resp_leEq; Apply rht_leEq_Max]).
Qed.

End Proper_Compact_with_One_or_Two_Points.

(* Tex_Prose
Compact intervals are exactly\ldots\ compact intervals.
*)

(* Begin_Tex_Verb *)
Lemma interval_compact_inc : (I:interval)(cI:(compact_ I))
  (H:?)(included (iprop I) (compact (Lend cI) (Rend cI) H)).
(* End_Tex_Verb *)
Intro.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI H; Clear H0 H cI c0 c.
Simpl; Intros a b Hab Hab'.
Red; Intros.
Simpl in H.
Inversion_clear H; Split; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma compact_interval_inc : (I:interval)(cI:(compact_ I))
  (H:?)(included (compact (Lend cI) (Rend cI) H) (iprop I)).
(* End_Tex_Verb *)
Intro.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI H; Clear H0 H cI c0 c.
Simpl; Intros a b Hab.
Red; Intros.
Inversion_clear H0; Split; Auto.
Qed.

(* Tex_Prose
A generalization of the previous results: if $[a,b]\subseteq J$ and $J$ is proper, then we can find a proper interval $[a',b']$ such that $[a,b]\subseteq[a',b']\subseteq J$.
*)

(* Begin_Tex_Verb *)
Lemma compact_proper_in_interval : (J,a,b,Hab:?)
  (included (compact a b Hab) (iprop J))->(proper J)->
    {a':? & {b':? & {Hab':? & 
      (included (compact a' b' (less_leEq ??? Hab')) (iprop J)) &
      (included (Compact Hab) (Compact (less_leEq ??? Hab')))}}}.
(* End_Tex_Verb *)
Intros.
Exists (Lend (compact_compact_in_interval2 J H0 a b (H ? (compact_inc_lft ?? Hab)) (H ? (compact_inc_rht ?? Hab)))).
Exists (Rend (compact_compact_in_interval2 J H0 a b (H ? (compact_inc_lft ?? Hab)) (H ? (compact_inc_rht ?? Hab)))).
Exists (proper_compact_in_interval2' ?????? 
  (compact_compact_in_interval2 J H0 a b (H ? (compact_inc_lft ?? Hab)) (H ? (compact_inc_rht ?? Hab)))).
EApply included_trans.
Apply compact_interval_inc.
Apply included_compact_in_interval2.
Apply included_compact.
Apply iprop_compact_in_interval2x'.
Apply iprop_compact_in_interval2y'.
Qed.

End Compact_Constructions.

Section Functions.

(* Tex_Prose
\section{Properties of Functions in Intervals}

We now define notions of continuity, differentiability and so on on arbitrary intervals.  As expected, a function $F$ has property $P$ in the [proper] interval $I$ iff it has property $P$ in every compact interval included in $I$.  We can formalize this in a nice way using previously defined concepts.

\begin{convention} Let \verb!n:nat! and \verb!I:interval!.
\end{convention}
*)

Variable n:nat.
Variable I:interval.

(* Begin_Tex_Verb *)
Definition Continuous [F:PartIR] :=
  (included (iprop I) (Pred F))*
  ((a,b:IR)(Hab:a[<=]b)(included (Compact Hab) (iprop I))->
    (Continuous_I Hab F)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Derivative [pI:(proper I)][F,G:PartIR] :=
  (included (iprop I) (Pred F))*
  ((included (iprop I) (Pred G))*
  ((a,b:IR)(Hab:a[<]b)
    (included (Compact (less_leEq ??? Hab)) (iprop I))->
    (Derivative_I Hab F G))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Diffble [pI:(proper I)][F:PartIR] :=
  (included (iprop I) (Pred F))*
  ((a,b:IR)(Hab:a[<]b)
    (included (Compact (less_leEq ??? Hab)) (iprop I))->
    (Diffble_I Hab F)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Derivative_n [pI:(proper I)][F,G:PartIR] :=
  (included (iprop I) (Pred F))*
  ((included (iprop I) (Pred G))*
  ((a,b:IR)(Hab:a[<]b)
    (included (Compact (less_leEq ??? Hab)) (iprop I))->
    (Derivative_I_n Hab n F G))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Diffble_n [pI:(proper I)][F:PartIR] :=
  (included (iprop I) (Pred F))*
  ((a,b:IR)(Hab:a[<]b)
    (included (Compact (less_leEq ??? Hab)) (iprop I))->
    (Diffble_I_n Hab n F)).
(* End_Tex_Verb *)

End Functions.

Section Reflexivity_Properties.

(* Tex_Prose
In the case of compact intervals, this definitions collapse to the old ones.
*)

(* Begin_Tex_Verb *)
Lemma Continuous_Int :
  (I:interval)(cI:(compact_ I))(H:?)(F:PartIR)
  (!Continuous_I (Lend cI) (Rend cI) H F)->(Continuous I F).
(* End_Tex_Verb *)
Intros.
Cut (included (iprop I) (compact (Lend cI) (Rend cI) H)).
2: Apply interval_compact_inc; Auto.
Cut (included (compact (Lend cI) (Rend cI) H) (iprop I)).
2: Apply compact_interval_inc; Auto.
Generalize cI H H0; Clear H0 H cI.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI H H0 H1 H2; Clear H3 H2 H1 H0 H cI c0 c.
Simpl; Intros a b Hab Hab' contF inc1 inc2.
Split.
Apply included_trans with (Compact Hab'); Included.
Intros.
Apply included_imp_contin with Hab:=Hab'; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Int_Continuous :
  (I:interval)(cI:(compact_ I))(H:?)(F:PartIR)
  (Continuous I F)->(!Continuous_I (Lend cI) (Rend cI) H F).
(* End_Tex_Verb *)
Intro.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI H F H0; Clear H1 H0 F H cI c0 c.
Simpl; Intros a b Hab Hab' F contF.
Inversion_clear contF.
Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Derivative_Int :
  (I:interval)(cI:(compact_ I))(pI:(proper I))(H:?)(F,F':PartIR)
  (!Derivative_I (Lend cI) (Rend cI) H F F')->
    (Derivative I pI F F').
(* End_Tex_Verb *)
Do 4 Intro.
Cut (included (iprop I) (compact (Lend cI) (Rend cI) (less_leEq ??? H))).
2: Apply interval_compact_inc; Auto.
Cut (included (compact (Lend cI) (Rend cI) (less_leEq ??? H)) (iprop I)).
2: Apply compact_interval_inc; Auto.
Generalize cI pI H; Clear H cI pI.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI pI H H0 H1 F F' H2; Clear H3 H2 F' F H1 H0 H pI cI c0 c.
Simpl; Intros a b Hab Hnonv Hab' inc1 inc2 F F' derF.
Split.
Apply included_trans with (Compact (less_leEq ??? Hab')); Included.
Split.
Apply included_trans with (Compact (less_leEq ??? Hab')); Included.
Intros c d Hcd' Hinc.
Apply included_imp_deriv with Hab:=Hab'; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Int_Derivative :
  (I:interval)(cI:(compact_ I))(pI:(proper I))(H:?)(F,F':PartIR)
  (Derivative I pI F F')->
    (!Derivative_I (Lend cI) (Rend cI) H F F').
(* End_Tex_Verb *)
Intro.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI pI H F F' H0; Clear H1 H0 F' F H pI cI c0 c.
Simpl; Intros a b Hab Hnonv Hab' F F' derF.
Inversion_clear derF.
Inversion_clear H0.
Apply H2; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma Diffble_Int :
  (I:interval)(cI:(compact_ I))(pI:(proper I))(H:?)(F:PartIR)
  (!Diffble_I (Lend cI) (Rend cI) H F)->(Diffble I pI F).
(* End_Tex_Verb *)
Do 4 Intro.
Cut (included (iprop I) (compact (Lend cI) (Rend cI) (less_leEq ??? H))).
2: Apply interval_compact_inc; Auto.
Cut (included (compact (Lend cI) (Rend cI) (less_leEq ??? H)) (iprop I)).
2: Apply compact_interval_inc; Auto.
Generalize cI pI H; Clear H pI cI.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI pI H H0 H1 F H2; Clear H3 H2 F H1 H0 H pI cI c0 c.
Simpl; Intros a b Hab Hnonv Hab' inc1 inc2 F diffF.
Red; Simpl.
Split.
Apply included_trans with (Compact (less_leEq ??? Hab')); Included.
Intros c d Hcd' Hinc.
Apply included_imp_diffble with Hab:=Hab'; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Int_Diffble :
  (I:interval)(cI:(compact_ I))(pI:(proper I))(H:?)(F:PartIR)
  (Diffble I pI F)->(!Diffble_I (Lend cI) (Rend cI) H F).
(* End_Tex_Verb *)
Intro.
Elim I; Intros; Try Inversion cI.
Generalize c c0 cI pI H F H0; Clear H1 H0 F H pI cI c0 c.
Simpl; Intros a b Hab Hnonv Hab' F diffF.
Inversion_clear diffF.
Apply H0; Included.
Qed.

End Reflexivity_Properties.

Section Lemmas.

(* Tex_Prose
Interestingly, inclusion and equality in an interval are also characterizable in a similar way:
*)

(* Begin_Tex_Verb *)
Lemma included_imp_inc : (J,P:?)
  ((a,b,Hab:?)(included (compact a b Hab) (iprop J))->
    (included (compact a b Hab) P))->
  (included (iprop J) P).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Apply (H ?? (leEq_reflexive ??) (compact_single_iprop J x H0)).
Apply compact_inc_lft.
Qed.

(* Begin_Tex_Verb *)
Lemma included_Feq'' : (I,F,G:?)(proper I)->
  ((a,b,Hab:?)(included (Compact (less_leEq ??? Hab)) (iprop I))->
    (Feq (compact a b (less_leEq ??? Hab)) F G))->
  (Feq (iprop I) F G).
(* End_Tex_Verb *)
Intros.
Apply eq_imp_Feq.
Red; Intros.
Elim (compact_proper_in_interval I x x (leEq_reflexive ? x)); Included.
2: Exact (compact_single_iprop I x H1).
Intros a Ha.
Elim Ha; Clear Ha.
Intros b Hb.
Elim Hb; Clear Hb.
Intros Hab H2 H3.
Elim (H0 ??? H2); Intros.
Inversion_clear a0.
Apply H4; Apply H3; Apply compact_single_prop.
Red; Intros.
Elim (compact_proper_in_interval I x x (leEq_reflexive ? x)); Included.
2: Exact (compact_single_iprop I x H1).
Intros a Ha.
Elim Ha; Clear Ha.
Intros b Hb.
Elim Hb; Clear Hb.
Intros Hab H2 H3.
Elim (H0 ??? H2); Intros.
Inversion_clear a0.
Apply H5; Apply H3; Apply compact_single_prop.
Intros.
Elim (compact_proper_in_interval I x x (leEq_reflexive ? x)); Included.
2: Exact (compact_single_iprop I x H1).
Intros a Ha.
Elim Ha; Clear Ha.
Intros b Hb.
Elim Hb; Clear Hb.
Intros Hab H2 H3.
Elim (H0 ??? H2); Intros.
Apply b0; Apply H3; Apply compact_single_prop.
Qed.

(* Begin_Tex_Verb *)
Lemma included_Feq' : (I,F,G:?)
  ((a,b,Hab:?)(included (compact a b Hab) (iprop I))->
    (Feq (Compact Hab) F G))->
  (Feq (iprop I) F G).
(* End_Tex_Verb *)
Intros.
Apply eq_imp_Feq.
Red; Intros.
Elim (H x x (leEq_reflexive ? x) (compact_single_iprop I x H0)); Intros.
Inversion_clear a.
Apply H1; Apply compact_single_prop.
Red; Intros.
Elim (H x x (leEq_reflexive ? x) (compact_single_iprop I x H0)); Intros.
Inversion_clear a.
Apply H2; Apply compact_single_prop.
Intros.
Elim (H x x (leEq_reflexive ? x) (compact_single_iprop I x H0)); Intros.
Apply b; Apply compact_single_prop.
Qed.

End Lemmas.

Hints Resolve included_interval included_interval' included3_interval compact_single_inc compact_single_iprop
  included_compact_in_interval iprop_compact_in_interval_inc1 iprop_compact_in_interval_inc2
  included_compact_in_interval2 iprop_compact_in_interval2_inc1 iprop_compact_in_interval2_inc2
  interval_compact_inc compact_interval_inc iprop_wd : included.
