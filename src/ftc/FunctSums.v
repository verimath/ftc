(* $Id: FunctSums.v,v 1.15 2003/03/13 12:06:19 lcf Exp $ *)

Require Export CSumsReals.
Require Export PartFunEquality.

Section FunctSums.

Section Definitions_and_Lemmas.

(* Tex_Prose
\chapter{Sums of Functions}

In this file we define Sums are defined of arbitrary families of partial functions.

Given a countable family of functions, their Sum is defined on the intersection of all the domains.  As is the case for groups, we will define three different kinds of Sums.

\section{Definitions}

We will first consider the case of a family $\{f_i\}_{i\in\NN}$ of functions; we can both define $\sum_{i,n}f_i$ (\verb!FSum0!) or $\sum_{i=m}^nf_i$ (\verb!FSum!).
*)

(* Begin_Tex_Verb *)
Definition FSum0 [n:nat][f:nat->PartIR] : PartIR.
(* End_Tex_Verb *)
Intros.
Apply Build_PartFunct with [x:IR](n:nat)(Pred (f n) x) [x:IR][Hx:(n:nat)(Pred (f n) x)](Sum0 n [n:nat](Part (f n) x (Hx n))).
Red; Intros.
Apply (pfprwd ? (f n0) x).
Apply H.
Assumption.
Intros.
Cut {i:nat & (Part (f i) x (Hx i))[#](Part (f i) y (Hy i))}; Intros.
Elim H0; Intros i Hi.
Apply pfstrx with (f i) (Hx i) (Hy i); Assumption.
Exact (Sum0_strext' ???? H).
Defined.

(* Begin_Tex_Verb *)
Definition FSum [m,n:nat][f:nat->PartIR] : PartIR.
(* End_Tex_Verb *)
Intros.
Apply Build_PartFunct with [x:IR](n:nat)(Pred (f n) x) [x:IR][Hx:(n:nat)(Pred (f n) x)](Sum m n [n:nat](Part (f n) x (Hx n))).
Red; Intros.
Apply (pfprwd ? (f n0) x).
Apply H.
Assumption.
Intros.
Cut {i:nat & ((f i) x (Hx i))[#]((f i) y (Hy i))}; Intros.
Elim H0; Intros i Hi.
Apply pfstrx with (f i) (Hx i) (Hy i); Assumption.
Exact (Sum_strext' ????? H).
Defined.

(* Tex_Prose
Although \verb!FSum! is here defined directly, it has the same relationship to the \verb!FSum0! operator as \verb!Sum! has to \verb!Sum0!.  Also, all the results for \verb!Sum! and \verb!Sum0! hold when these operators are replaced by their functional equivalents\footnote{This is an immediate consequence of the fact that the partial functions form a group; however, as we already mentioned, their forming too big a type makes it impossible to use those results.}.
*)

(* Begin_Tex_Verb *)
Lemma FSum_FSum0 : (m,n:nat)(f:nat->PartIR)(x:IR)(Hx,Hx',Hx'':?)
  ((FSum m n f) x Hx)[=]
    ((FSum0 (S n) f) x Hx')[-]((FSum0 m f) x Hx'').
(* End_Tex_Verb *)
Intros.
Simpl; Unfold Sum Sum1; Simpl.
Apply cg_minus_wd; Try Apply bin_op_wd_unfolded; Try Apply Sum0_wd; Intros; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum0_wd : (m:nat)(f,g:nat->PartIR)
  ((x:IR)(HxF,HxG:?)(i:nat)
    ((f i) x (HxF i))[=]((g i) x (HxG i)))->
  (x:IR)(HxF,HxG:?)((FSum0 m f) x HxF)[=]((FSum0 m g) x HxG).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply Sum0_wd.
Intros; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_one : (n:nat)(f:nat->PartIR)(x:IR)(Hx,Hx':?)
  ((FSum n n f) x Hx')[=]((f n) x (Hx n)).
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
Apply Sum_one.
Simpl; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_FSum : (l,m,n:nat)(f:nat->PartIR)(x,Hx,Hx',Hx'':?)
  ((FSum l m f) x Hx)[+]((FSum (S m) n f) x Hx')
    [=]((FSum l n f) x Hx'').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
2: Apply Sum_Sum with l:=l m:=m.
Apply bin_op_wd_unfolded; Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_first : (m,n:nat)(f:nat->PartIR)(x:IR)(Hx,Hx',Hx'':?)
  ((FSum m n f) x Hx)[=]
    ((f m) x Hx')[+]((FSum (S m) n f) x Hx'').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
Apply Sum_first.
Apply bin_op_wd_unfolded; Try Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_last : (m,n:nat)(f:nat->PartIR)(x:IR)(Hx,Hx',Hx'':?)
  ((FSum m (S n) f) x Hx)[=]
    ((FSum m n f) x Hx')[+]((f (S n)) x Hx'').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
Apply Sum_last.
Apply bin_op_wd_unfolded; Try Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_last' : (m,n:nat)(f:nat->PartIR)(x:IR)(Hx,Hx',Hx'':?)
  (lt O n)->((FSum m n f) x Hx)[=]
    ((FSum m (pred n) f) x Hx')[+]((f n) x Hx'').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
Apply Sum_last'.
Assumption.
Apply bin_op_wd_unfolded; Try Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_wd : (m,n:nat)(f,g:nat->PartIR)
  ((x:IR)(HxF,HxG:?)(i:nat)
    ((f i) x (HxF i))[=]((g i) x (HxG i)))->
  (x:IR)(HxF,HxG:?)
    ((FSum m n f) x HxF)[=]((FSum m n g) x HxG).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply Sum_wd.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_plus_FSum : (f,g:nat->PartIR)(m,n:nat)(x:IR)
  (Hx,HxF,HxG:?)((FSum m n [i:nat]((f i){+}(g i))) x Hx)[=]
    ((FSum m n f) x HxF)[+]((FSum m n g) x HxG).
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
2: Apply Sum_plus_Sum.
Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_FSum : (f:nat->PartIR)(m,n:nat)(x:IR)(Hx,Hx':?)
  ((FSum m n [i:nat]{--}(f i)) x Hx)[=]
    [--]((FSum m n f) x Hx').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
2: Apply inv_Sum.
Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_minus_FSum : (f,g:nat->PartIR)(m,n:nat)(x:IR)
  (Hx,HxF,HxG:?)((FSum m n [i:nat]((f i){-}(g i))) x Hx)[=]
    ((FSum m n f) x HxF)[-]((FSum m n g) x HxG).
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
2: Apply Sum_minus_Sum.
Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_wd' : (m,n:nat)(le m (S n))->(f,g:nat->PartIR)
  ((x:IR)(HxF,HxG:?)((i:nat)(le m i)->(le i n)->
    (((f i) x (HxF i))[=](((g i) x (HxG i))))))->
  (x:IR)(HxF,HxG:?)
    ((FSum m n f) x HxF)[=]((FSum m n g) x HxG).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply Sum_wd'; Try Assumption.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_resp_less : (f,g:nat->PartIR)(m,n:nat)(le m n)->
  ((x:IR)(HxF,HxG:?)((i:nat)(le m i)->(le i n)->
    ((f i) x (HxF i))[<]((g i) x (HxG i))))->
  (x:IR)(HxF,HxG:?)
    ((FSum m n f) x HxF)[<]((FSum m n g) x HxG).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply Sum_resp_less; Try Assumption.
Intros; Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_resp_leEq : (f,g:nat->PartIR)(m,n:nat)(le m (S n))->
  ((x:IR)(HxF,HxG:?)((i:nat)(le m i)->(le i n)->
    ((f i) x (HxF i))[<=]((g i) x (HxG i))))->
  (x:IR)(HxF,HxG:?)
    ((FSum m n f) x HxF)[<=]((FSum m n g) x HxG).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply Sum_resp_leEq; Try Assumption.
Intros; Apply H0; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_comm_scal : (f:nat->PartIR)(c,m,n:?)(x:IR)(Hx,Hx':?)
  ((FSum m n [i:nat]((f i){*}{-C-}c)) x Hx)[=]
    (((FSum m n f){*}{-C-}c) x Hx').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
2: Apply (Sum_comm_scal [n:nat]((f n) x (ProjIR1 Hx' n)) c m n).
Apply Sum_wd; Intros; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_comm_scal' : (f:nat->PartIR)(c,m,n:?)(x:IR)(Hx,Hx':?)
  ((FSum m n [i:nat]{-C-}c{*}(f i)) x Hx)[=]
    (({-C-}c{*}(FSum m n f)) x Hx').
(* End_Tex_Verb *)
Intros.
Simpl.
EApply eq_transitive_unfolded.
2: Apply (Sum_comm_scal' c [n:nat]((f n) x (ProjIR2 Hx' n)) m n).
Apply Sum_wd; Intros; Rational.
Qed.

End Definitions_and_Lemmas.

Section More_Sums.

(* Tex_Prose
Also important is the case when we have a \emph{finite} family $\{f_i\}_{i=0}^{n-1}$ of functions; in this case we need to use the \verb!FSumx! operator.
*)

(* Begin_Tex_Verb *)
Fixpoint FSumx [n:nat] : ((i:nat)(lt i n)->PartIR)->PartIR := 
  <[n:nat]((i:nat)(lt i n)->PartIR)->PartIR>
  Cases n of
    O => [_:(i:nat)(lt i O)->PartIR]{-C-}Zero
  | (S p) => [f:(i:nat)(lt i (S p))->PartIR]
      ((FSumx p [i:nat][l:(lt i p)](f i (lt_S i p l))){+}
        (f p (lt_n_Sn p)))
  end.
(* End_Tex_Verb *)

(* Tex_Prose
This operator is well defined, as expected.
*)

(* Begin_Tex_Verb *)
Lemma FSumx_wd : (n:nat)(f,g:(i:nat)(lt i n)->PartIR)
  ((i:nat)(Hi:(lt i n))(x:IR)(HxF,HxG:?)
    ((f i Hi) x HxF)[=]((g i Hi) x HxG))->
  (x:IR)(HxF,HxG:?)((FSumx ? f) x HxF)[=]
    ((FSumx ? g) x HxG).
(* End_Tex_Verb *)
Intro; Case n.
Intros; Simpl; Algebra.
Clear n.
Induction n.
Intros; Simpl; Algebra.
Clear n; Intro.
Cut {p:nat | (S n)=p}; [Intro | Exists (S n); Auto].
Elim H; Intros p Hp.
Rewrite Hp; Intros.
Simpl.
Apply bin_op_wd_unfolded.
Apply H0.
Intros; Apply H1.
Apply H1.
Qed.

(* Begin_Tex_Verb *)
Lemma FSumx_wd' :
  (P:IR->CProp)(n:nat)(f,g:(i:nat)(lt i n)->PartIR)
  ((i:nat)(H,H':?)(Feq P (f i H) (g i H')))->
    (Feq P (FSumx ? f) (FSumx ? g)).
(* End_Tex_Verb *)
Intros; Induction n.
Simpl; Apply Feq_reflexive; Apply included_IR.
Simpl; Apply Feq_plus; Auto.
Qed.

(* Tex_Prose
As was already the case for \verb!Sumx!, in many cases we will need to explicitly asSume that $f_i$ is independent of the proof that $i<n$.  This holds both for the value and the domain of the partial function $f_i$.
*)

(* Begin_Tex_Verb *)
Definition good_fun_seq [n:nat][f:(i:nat)(lt i n)->PartIR] :=
  (i,j:nat)i=j->(H:(lt i n))(H':(lt j n))(x,y:IR)(x[=]y)->
    (Hx,Hy:?)((f i H) x Hx)[=]((f j H') y Hy).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition good_fun_seq' [n:nat][f:(i:nat)(lt i n)->PartIR] :=
  (i,j:nat)i=j->(H:(lt i n))(H':(lt j n))(x,y:IR)(x[=]y)->
    (Pred (f i H) x)->(Pred (f j H') y).
(* End_Tex_Verb *)

(* Tex_Prose
Under these asSumptions, we can characterize the domain and the value of the Sum function from the domains and values of the Summands:
*)

(* Begin_Tex_Verb *)
Lemma FSumx_pred : (n:nat)(f:(i:nat)(lt i n)->PartIR)
  (good_fun_seq' ? f)->(x:IR)(Pred (FSumx n f) x)->
  (i:nat)(Hi:(lt i n))(Pred (f i Hi) x).
(* End_Tex_Verb *)
Intros; Induction n.
ElimType False; Inversion Hi.
Simpl in H.
Elim (le_lt_eq_dec ?? Hi); Intro.
Cut (lt i n); [Intro | Auto with arith].
LetTac g:=[i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)).
Apply H with i (lt_S ?? H1) x.
Auto.
Algebra.
Change (Pred (g i H1) x).
Apply Hrecn.
Unfold g; Red; Intros.
Apply H with i0 (lt_S i0 n H3) x0; Auto.
Inversion_clear H0; Assumption.
Inversion_clear H0; Clear H1.
Red in H.
Apply H with n (lt_n_Sn n) x; Auto.
Symmetry; Auto.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSumx_pred' : (n:nat)(f:(i:nat)(lt i n)->PartIR)
  (good_fun_seq' ? f)->(x:IR)((i:nat)(Hi:(lt i n))
    (Pred (f i Hi) x))->(Pred (FSumx n f) x).
(* End_Tex_Verb *)
Intros; Induction n.
Simpl; Auto.
Split.
Apply Hrecn.
Red; Intros.
Red in H.
Exact (H ?? H1 ???? H3 H4).
Intros; Auto.
Apply H0.
Qed.

(* Begin_Tex_Verb *)
Lemma FSumx_char : (n,f,x,Hx,Hf:?)((FSumx n f) x Hx)[=]
  (Sumx [i:nat][Hi:(lt i n)]
    ((f i Hi) x (FSumx_pred n f Hf x Hx i Hi))).
(* End_Tex_Verb *)
Intro; Induction n.
Algebra.
Intros; Simpl.
Apply bin_op_wd_unfolded; Algebra.
Cut (good_fun_seq' n [i:nat][Hi:?](f i (lt_S i n Hi))); Repeat Intro.
EApply eq_transitive_unfolded.
Apply Hrecn with Hf:=H.
Apply Sumx_wd; Intros; Simpl; Algebra.
Red in Hf.
Apply Hf with i (lt_S i n H0) x0; Auto.
Qed.

(* Tex_Prose
As we did for arbitrary groups, it is often useful to rewrite this Sums as ordinary Sums.
*)

(* Begin_Tex_Verb *)
Definition FSumx_to_FSum [n:nat] :
  ((i:nat)(lt i n)->PartIR)->nat->PartIR.
(* End_Tex_Verb *)
Intros n f i.
Elim (le_lt_dec n i); Intro.
Apply ({-C-}Zero::PartIR).
Apply (f i b).
Defined.

(* Begin_Tex_Verb *)
Lemma FSumx_lt : (n:nat)(f:((i:nat)(lt i n)->PartIR))
  (good_fun_seq ? f)->(i:nat)(Hi:(lt i n))(x:IR)(Hx,Hx':?)
    ((FSumx_to_FSum n f i) x Hx)[=]((f i Hi) x Hx').
(* End_Tex_Verb *)
Do 6 Intro.
Unfold FSumx_to_FSum.
Elim (le_lt_dec n i); Intro; Simpl.
ElimType False; Apply (le_not_lt n i); Auto.
Intros; Apply H; Auto.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSumx_le : (n:nat)(f:((i:nat)(lt i n)->PartIR))
  (good_fun_seq ? f)->(i:nat)(Hi:(le n i))
    (x:IR)(Hx:?)((FSumx_to_FSum n f i) x Hx)[=]Zero.
(* End_Tex_Verb *)
Do 6 Intro.
Unfold FSumx_to_FSum.
Elim (le_lt_dec n i); Intro; Simpl.
Intro; Algebra.
ElimType False; Apply (le_not_lt n i); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_FSumx_to_FSum : (n:nat)(f:(i:nat)(lt i (S n))->PartIR)
  (good_fun_seq ? f)->(good_fun_seq' ? f)->(x:IR)(Hx,Hx':?)
  ((FSum O n (FSumx_to_FSum ? f)) x Hx)[=]((FSumx ? f) x Hx').
(* End_Tex_Verb *)
Induction n.
Intros; Simpl.
EApply eq_transitive_unfolded.
Apply Sum_one.
Simpl.
Cut (lt O (1)); [Intro | Apply lt_n_Sn].
Stepr (Part (f O (lt_n_Sn O)) x (ProjIR2 Hx')).
Apply FSumx_lt; Assumption.
Clear n; Intros.
Simpl.
EApply eq_transitive_unfolded.
Apply Sum_last.
Apply bin_op_wd_unfolded.
LetTac g:=[i:nat][l:(lt i (S n))](f i (lt_S ?? l)).
Cut (good_fun_seq ? g); Intros.
Cut (good_fun_seq' ? g); Intros.
Step_rht ((FSumx n [i:nat][l:(lt i n)](g i (lt_S ?? l))) x (ProjIR1 (ProjIR1 Hx')))[+]((g n (lt_n_Sn n)) x (ProjIR2 (ProjIR1 Hx'))).
Cut (Pred (FSumx ? g) x); Intros.
Cut (m:nat)(Pred (FSumx_to_FSum (S n) g m) x).
Intro Hx''.
Simpl in H.
Apply eq_transitive_unfolded with (Sum O n [m:nat]((FSumx_to_FSum (S n) g m) x (Hx'' m))).
2: Apply H with f:=g; Try Assumption.
Apply Sum_wd'.
Auto with arith.
Intros.
Cut (lt i (S (S n))); [Intro | Auto with arith].
Apply eq_transitive_unfolded with ((f i H7) x (FSumx_pred ?? H1 x Hx' i H7)).
Apply FSumx_lt; Assumption.
Cut (lt i (S n)); [Intro | Auto with arith].
Apply eq_transitive_unfolded with ((g i H8) x (FSumx_pred ?? H3 x H4 i H8)).
2: Apply eq_symmetric_unfolded; Apply FSumx_lt; Assumption.
Unfold g; Apply H0; Auto.
Algebra.
Intro.
Simpl in Hx.
Generalize (Hx m); Clear H4 H3 H2 Hx.
Unfold FSumx_to_FSum.
Elim (le_lt_dec (S n) m); Elim (le_lt_dec (S (S n)) m); Do 2 Intro; Simpl; Intro.
Auto.
Auto.
Unfold g; Apply FSumx_pred with n:=(S (S n)); Assumption.
Unfold g; Apply FSumx_pred with n:=(S (S n)); Assumption.
Simpl in Hx'.
Unfold g; Inversion_clear Hx'; Intros; Assumption.
Unfold g; Red; Intros.
Red in H1; Apply H1 with i (lt_S ?? H4) x0; Auto.
Unfold g; Red; Intros.
Red in H0; Apply H0; Auto.
Apply FSumx_lt; Auto.
Qed.

End More_Sums.

Section Characterizations.

(* Tex_Prose
Some useful lemmas follow.
*)

(* Begin_Tex_Verb *)
Lemma FSum0_0 : (P,f:?)((n:?)(included P (Pred (f n))))->
  (Feq P {-C-}Zero (FSum0 O f)).
(* End_Tex_Verb *)
Intros.
FEQ.
Simpl.
Red; Intros; Apply (H n); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum0_S :
  (P,f,n:?)((m:?)(included P (Pred (f m))))->
  (Feq P ((FSum0 n f){+}(f n)) (FSum0 (S n) f)).
(* End_Tex_Verb *)
Intros.
FEQ.
Apply included_FPlus; Auto.
Simpl; Red; Intros.
Apply (H n0); Auto.
Simpl.
Red; Intros; Apply (H n0); Auto.
Simpl; Apply bin_op_wd_unfolded; Algebra.
Apply Sum0_wd; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_0 :
  (P,f,n:?)((i:?)(included P (Pred (f i))))->
  (Feq P (f n) (FSum n n f)).
(* End_Tex_Verb *)
Intros.
FEQ.
Simpl.
Red; Intros; Apply (H n0); Auto.
Simpl.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply Sum_one.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_S :
  (P,f,m,n:?)((i:?)(included P (Pred (f i))))->
  (Feq P ((FSum m n f){+}(f (S n))) (FSum m (S n) f)).
(* End_Tex_Verb *)
Intros.
Apply eq_imp_Feq.
Apply included_FPlus; Auto.
Simpl.
Red; Intros; Apply (H n0); Auto.
Simpl.
Red; Intros; Apply (H n0); Auto.
Intros; Simpl; Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
Apply Sum_last.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma FSum_FSum0' :
  (P,f,m,n:?)((i:?)(included P (Pred (f i))))->
  (Feq P (FSum m n f) ((FSum0 (S n) f){-}(FSum0 m f))).
(* End_Tex_Verb *)
Intros.
Apply eq_imp_Feq.
Red; Intros; Intro; Apply (H n0); Auto.
Apply included_FMinus; Red; Intros; Intro; Apply (H n0); Auto.
Intros.
Apply eq_transitive_unfolded with (pfpfun ? ? (ProjIR1 Hx'))[-]((FSum0 m f) ? (ProjIR2 Hx')).
Apply FSum_FSum0.
Simpl; Rational.
Qed.

End Characterizations.

End FunctSums.
