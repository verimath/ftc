(* $Id: RefLemma.v,v 1.15 2003/03/13 12:06:22 lcf Exp $ *)

Require Export RefSeparating.
Require Export RefSeparated.
Require Export RefSepRef.

Section Refinement_Lemma.

(* Tex_Prose
\chapter{The Refinement Lemmas}

Here we resume the results proved in four different files.  The aim is to prove the following result (last part of Theorem~2.9 of Bishop [1967]):

\noindent\textbf{Theorem} Let $f$ be a continuous function on a compact interval $[a,b]$ with modulus of continuity\footnote{From our point of view, the modulus of continuity is simply the proof that $f$ is continuous.} $\omega$.  Let $P$ be a partition of $[a,b]$ and $\varepsilon>0$ be such that mesh($P$)$<\omega(\varepsilon)$.  Then \[\left|S(f,P)-\int_a^bf(x)dx\right|\leq\varepsilon(b-a)\] where $S(f,P)$ denotes any sum of the function $f$ respecting the partition $P$ (as previously defined).

The proof of this theorem relies on the fact that for any two partitions $P$ and $R$ of $[a,b]$ it is possible to define a partition $Q$ which is ``almost'' a common refinement of $P$ and $R$---that is, given $\varepsilon>0$ it is possible to define $Q$ such that for every point $x$ of either $P$ or $R$ there is a point $y$ of $Q$ such that $|x-y|<\varepsilon$.  This requires three separate constructions (done in three separate files, \verb!RefinementSeparated.v!, \verb!RefinementSeparating.v! and \verb!RefinementSepRef.v!) which are then properly combined to give the final result.  We recommend the reader to ignore this technical constructions.

In the file \verb!RefSeparated.v! (ommited) we prove that if $P$ and $R$ are both separated (though not necessarily separated from each other) then we can define a partition $P'$ arbitrarily close to $P$ (that is, such that given $\alpha>0$ and $\xi>0$ $P'$ satisfies both $\mathrm{mesh}(P')<\mathrm{mesh}(P)+\xi$ and for every choice of points $x_i$ respecting $P$ there is a choice of points $x'_i$ respecting $P'$ such that $|S(f,P)-S(f,P')|<\alpha$) that is separated from $R$.

In the file \verb!RefSeparating.v! (ommited) we prove that given any partition $P$ and assuming $a\neq b$ we can define a partition $P'$ arbitrarily close to $P$ (in the same sense as above) which is separated.

Finally, in \verb!RefSepRef.v! (ommited) we prove that every two separated partitions $P$ and $R$ have a common refinement---as every two points in $P$ and $R$ are apart, we can decide which one is smaller.  We use here the technical results about ordering that we proved in the file \verb!IntegralLemmas.v!.

Using the results from these files, we prove our main lemma in several steps (and versions).

\begin{convention} Throughout this section:
\begin{itemize}
\item \verb!a,b:IR! and \verb!I!$=[a,b]$!;
\item \verb!F! is a partial function continuous in \verb!I!;
\end{itemize}
\end{convention}
*)

Variables a,b:IR.
Hypothesis Hab:(a[<=]b).
Local I:=(Compact Hab).

Variable F:PartIR.
Hypothesis contF:(Continuous_I Hab F).
Hypothesis incF:(included (Compact Hab) (Pred F)).

Local contF' := (contin_prop ???? contF).

Section First_Refinement_Lemma.

(* Tex_Prose
This is the first part of the proof of Theorem~2.9.

\begin{convention}
\begin{itemize}
\item \verb!P,Q! are partitions of \verb!I! with, respectively, \verb!n! and \verb!m! points;
\item \verb!Q! is a refinement of \verb!P!;
\item \verb!e! is a positive real number;
\item \verb!d! is the modulus of continuity of \verb!F! for \verb!e!;
\item the mesh of \verb!P! is less or equal to \verb!d!;
\item \verb!fP! and \verb!fQ! are choices of points respecting the partitions \verb!P! and \verb!Q!, respectively.
\end{itemize}
\end{convention}
*)

Variable e:IR.
Hypothesis He:Zero[<]e.

Local d := (proj1_sigS2P ??? (contF' e He)).

Variables m,n:nat.
Variable P:(Partition Hab n).
Hypothesis HMesh : (Mesh P)[<=]d.

Variable Q:(Partition Hab m).
Hypothesis Href : (Refinement P Q).

Variable fP:(i:nat)(lt i n)->IR.
Hypothesis HfP:(Points_in_Partition P fP).
Hypothesis HfP':(nat_less_n_fun ?? fP).

Variable fQ:(i:nat)(lt i m)->IR.
Hypothesis HfQ:(Points_in_Partition Q fQ).
Hypothesis HfQ':(nat_less_n_fun ?? fQ).

Local sub := (proj1_sig2P ??? Href).

Local sub0 : (sub O)=O.
Elim (proj2a_sig2P ??? Href); Auto.
Qed.

Local subn : (sub n)=m.
Elim (proj2a_sig2P ??? Href); Intros.
Elim H0; Auto.
Qed.

Local sub_mon : (i,j:nat)(lt i j)->(lt (sub i) (sub j)).
Elim (proj2a_sig2P ??? Href); Intros.
Elim H0; Intros.
Elim H1; Auto.
Qed.

Local sub_mon' : (i,j:nat)(le i j)->(le (sub i) (sub j)).
Intros.
Elim (le_lt_eq_dec ?? H); Intro.
Apply lt_le_weak; Apply sub_mon; Assumption.
Rewrite b0; Apply le_n.
Qed.

Local sub_hyp : (i:nat)(H:(le i n)){H':(Cle (sub i) m) | (Pts P i H)[=](Pts Q (sub i) (Cle_to ?? H'))}.
Apply (proj2b_sig2P ??? Href).
Qed.

Local sub_S : (i:nat)(lt O (sub (S i))).
Rewrite <- sub0.
Intro; Apply sub_mon; Apply lt_O_Sn.
Qed.

Local H : (i,j:nat)(lt i n)->(le j (pred (sub (S i))))->(lt j m).
Intros.
Cut (le (S i) n); [Intro | Apply H].
Elim (le_lt_eq_dec ?? H1); Clear H1; Intro.
Cut (lt (sub (S i)) (sub n)); [Intro | Apply sub_mon; Assumption].
Rewrite <- subn.
Apply le_lt_trans with (sub (S i)); Auto; EApply le_trans; [Apply H0 | Apply le_pred_n].
Cut (lt O (sub (S i))); [Intro | Apply sub_S].
Rewrite <- subn.
Rewrite <- b0.
Rewrite (S_pred ?? H1); Auto with arith.
Qed.

Local H' : (i,j:nat)(lt i n)->(le j (pred (sub (S i))))->(le (S j) m).
Intros; Exact (H ?? H0 H1).
Qed.

Local H0 : (i:nat)(lt (sub i) (sub (S i))).
Intro; Apply sub_mon; Apply lt_n_Sn.
Qed.

Local sub_SS : (i:nat)(le (sub i) (S (pred (sub (S i))))).
Intro; Cut (lt (sub i) (sub (S i))); [Intro | Apply H0].
Rewrite <- (S_pred ?? H1); Apply lt_le_weak; Apply H0.
Qed.

Local h : nat->IR.
Intro i.
Elim (le_lt_dec i m); Intro.
Apply (Pts Q ? a0).
Apply (Zero::IR).
Defined.

Local g : nat->IR.
Intro i.
Elim (le_lt_dec m i); Intro.
Apply (Zero::IR).
Apply (Pts Q ? b0)[-](Pts Q ? (lt_le_weak ?? b0)).
Defined.

Local ref_calc1 : (i:nat)(Hi:(lt i n))(Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
  (Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))[=](Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi)).
Intros.
Unfold Sum2.
Elim (sub_hyp (S i) Hi); Intros P1 HP1.
Elim (sub_hyp i (lt_le_weak ?? Hi)); Intros P2 HP2.
Apply eq_transitive_unfolded with (Pts Q ? (Cle_to ?? P1))[-](Pts Q ? (Cle_to ?? P2)).
2: Apply eq_symmetric_unfolded; Apply cg_minus_wd; [Apply HP1 | Apply HP2].
Cut (sub (S i))=(S (pred (sub (S i)))).
2: Apply S_pred with O; Apply sub_S.
Intro.
Generalize P1 HP1; Clear HP1 P1; Pattern 1 2 3 12 13 (sub (S i)).
Rewrite H1; Intros.
EApply eq_transitive_unfolded.
Apply str_Mengolli_Sum_gen with f:=h.
Apply sub_SS.
Intros j Hj Hj'.
Elim (le_lt_dec j (pred (sub (S i)))); Intro; Simpl.
Elim (le_lt_dec (sub i) j ); Intro; Simpl.
Unfold h.
Apply cg_minus_wd.
Elim (le_lt_dec (S j) m); Intro; Simpl.
Apply prf1; Auto.
Cut (le (S j) m); [Intro | Apply H' with i; Assumption].
ElimType False; Apply (le_not_lt ?? H2 b0).
Elim (le_lt_dec j m); Intro; Simpl.
Apply prf1; Auto.
Cut (lt j m); [Intro | Apply H with i; Assumption].
ElimType False; Apply le_not_lt with m j; Auto with arith.
ElimType False; Apply le_not_lt with (sub i) j; Auto with arith.
ElimType False; Apply (le_not_lt ?? Hj' b0).
Unfold h.
Apply cg_minus_wd.
Elim (le_lt_dec (S (pred (sub (S i)))) m); Intro; Simpl.
Apply prf1; Auto.
ElimType False.
Cut (le (S (pred (sub (S i)))) m); [Intro | Apply Cle_to; Assumption].
Apply (le_not_lt ?? H2 b0).
Elim (le_lt_dec (sub i) m); Intro; Simpl.
Apply prf1; Auto.
ElimType False.
Cut (le (sub i) m); [Intro | Apply Cle_to; Assumption].
Apply (le_not_lt ?? H2 b0).
Qed.

Syntactic Definition just1:=(incF ? (Pts_part_lemma ?????? HfP ??)).
Syntactic Definition just2:=(incF ? (Pts_part_lemma ?????? HfQ ??)).

Local ref_calc2 : (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum HfQ incF))[=](AbsIR 
  (Sumx [i:nat][Hi:(lt i n)]((Part F (fP i Hi) just1)[*]
    (Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
      (Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))[-]
  (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    (Part F (fQ j (H ?? Hi Hj')) just2)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))).
Apply AbsIR_wd; Unfold Partition_Sum.
Apply cg_minus_wd.
Apply Sumx_wd; Intros.
Apply mult_wd_rht.
Apply eq_symmetric_unfolded; Apply ref_calc1.
Apply eq_symmetric_unfolded; Unfold Sum2.
Apply eq_transitive_unfolded with (Sumx [j:nat][Hj:(lt j m)](part_tot_nat_fun ?? [i:nat][H:(lt i m)]
  (Part F (fQ i H) just2)[*]((Pts Q ? H)[-](Pts Q ? (lt_le_weak ?? H))) j)).
Apply str_Sumx_Sum_Sum with
  g:=[i:nat][Hi:(lt i n)][i0:nat]
         (sumbool_rec (le (sub i) i0) (lt i0 (sub i))
           [_:({(le (sub i) i0)}+{(lt i0 (sub i))})]IR
           [_:(le (sub i) i0)]
            (sumbool_rec (le i0 (pred (sub (S i))))
              (lt (pred (sub (S i))) i0)
              [_:({(le i0 (pred (sub (S i))))}
                   +{(lt (pred (sub (S i))) i0)})]IR
              [a1:(le i0 (pred (sub (S i))))]
               ((Part F (fQ i0 (H i i0 Hi a1)) just2)[*]
                 ((Pts Q (S i0) (H' i i0 Hi a1))[-](Pts Q i0 (lt_le_weak i0 m (H i i0 Hi a1)))))
              [_:(lt (pred (sub (S i))) i0)]Zero
              (le_lt_dec i0 (pred (sub (S i)))))
           [_:(lt i0 (sub i))]Zero (le_lt_dec (sub i) i0))
  h:=(part_tot_nat_fun ?? [i:nat][H:(lt i m)](Part F (fQ i H) just2)[*]((Pts Q ? H)[-](Pts Q ? (lt_le_weak ?? H)))).
Exact sub0.
Exact sub_mon.
Clear g h; Intros.
Elim (le_lt_dec (sub i) j); Intro; Simpl.
Elim (le_lt_dec j (pred (sub (S i)))); Intro; Simpl.
Unfold part_tot_nat_fun.
Elim (le_lt_dec m j); Intro; Simpl.
ElimType False.
Cut (lt O (sub (S i))); [Intro | Apply sub_S].
Cut (le (sub (S i)) m); Intros.
Apply (le_not_lt ?? H4); Apply le_lt_trans with j; Auto.
Rewrite <- subn.
Apply sub_mon'; Apply Hi.
Apply mult_wd.
Apply pfwdef.
Apply HfQ'; Auto.
Apply cg_minus_wd; Apply prf1; Auto.
ElimType False; Apply (le_not_lt ?? b0).
Rewrite <- (S_pred ?? (sub_S i)); Auto.
ElimType False; Apply (le_not_lt ?? H1 b0).
Symmetry; Apply subn.
Apply Sumx_wd; Intros.
Unfold part_tot_nat_fun.
Elim (le_lt_dec m i); Intro; Simpl.
ElimType False; Apply le_not_lt with m i; Auto.
Apply mult_wd.
Apply pfwdef; Apply HfQ'; Auto.
Apply cg_minus_wd; Apply prf1; Auto.
Qed.

Local ref_calc3 : (AbsIR (Sumx [i:nat][Hi:(lt i n)]((Part F (fP i Hi) just1)[*]
    (Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))](Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))[-]
    (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
      (Part F (fQ j (H ?? Hi Hj')) just2)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))))[=]
  (AbsIR
    (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
      (Part F (fP i Hi) just1)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))[-]
    (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
      (Part F (fQ j (H ?? Hi Hj')) just2)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))).
Apply AbsIR_wd.
Apply cg_minus_wd; Apply Sumx_wd; Intros.
Apply eq_symmetric_unfolded; Apply Sum2_comm_scal' with
  f:=[j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))](Pts Q (S j) (H' ?? H1 Hj'))[-](Pts Q j (lt_le_weak ?? (H ?? H1 Hj'))).
Apply sub_SS.
Algebra.
Qed.

Local ref_calc4 : (AbsIR (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
      (Part F (fP i Hi) just1)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))[-]
    (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
      (Part F (fQ j (H ?? Hi Hj')) just2)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))))[=]
  (AbsIR (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    ((Part F (fP i Hi) just1)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))[-]
    ((Part F (fQ j (H ?? Hi Hj')) just2)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))))).
Apply AbsIR_wd.
EApply eq_transitive_unfolded.
Apply Sumx_minus_Sumx.
Apply Sumx_wd; Intros.
EApply eq_transitive_unfolded.
Apply Sum2_minus_Sum2.
Apply sub_SS.
Algebra.
Qed.

Local ref_calc5 : (AbsIR (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    ((Part F (fP i Hi) just1)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))[-]
    ((Part F (fQ j (H ?? Hi Hj')) just2)[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))))[=]
  (AbsIR (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    ((Part F (fP i Hi) just1)[-](Part F (fQ j (H ?? Hi Hj')) just2))[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))).
Apply AbsIR_wd; Apply Sumx_wd; Intros.
Apply Sum2_wd; Intros.
Apply sub_SS.
Algebra.
Qed.

Local ref_calc6 : (AbsIR (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    ((Part F (fP i Hi) just1)[-](Part F (fQ j (H ?? Hi Hj')) just2))[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))))[<=]
  (Sumx [i:nat][Hi:(lt i n)](AbsIR (Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    ((Part F (fP i Hi) just1)[-](Part F (fQ j (H ?? Hi Hj')) just2))[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))).
EApply leEq_wdr.
Apply triangle_SumxIR.
Apply Sumx_wd.
Intros.
Apply AbsIR_wd.
Apply Sum2_wd.
Apply sub_SS.
Intros j Hj Hj'.
Algebra.
Qed.

Local ref_calc7 : (Sumx [i:nat][Hi:(lt i n)](AbsIR (Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    ((Part F (fP i Hi) just1)[-](Part F (fQ j (H ?? Hi Hj')) just2))[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))))[<=]
  (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    (AbsIR ((Part F (fP i Hi) just1)[-](Part F (fQ j (H ?? Hi Hj')) just2))[*]
      ((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))))).
Apply Sumx_resp_leEq; Intros.
EApply leEq_wdr.
Apply triangle_Sum2IR.
Apply sub_SS.
Algebra.
Qed.

Local ref_calc8 : (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    (AbsIR ((Part F (fP i Hi) just1)[-](Part F (fQ j (H ?? Hi Hj')) just2))[*]
      ((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))))[<=]
  (Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
    e[*]((Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj')))))).
Apply Sumx_resp_leEq; Intros.
Apply Sum2_resp_leEq.
Apply sub_SS.
Intros j Hj Hj'.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both.
Apply AbsIR_nonneg.
Apply AbsIR_nonneg.
Generalize (proj2b_sigS2P ??? (contF' e He)); Fold d; Intros.
Apply H2.
Unfold I; Apply Pts_part_lemma with n P; Assumption.
Unfold I; Apply Pts_part_lemma with m Q; Assumption.
Apply leEq_transitive with (Mesh P).
2: Assumption.
Apply leEq_transitive with (AbsIR (Pts P (S i) H1)[-](Pts P i (lt_le_weak ?? H1))).
2: EApply leEq_wdl.
3: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply Mesh_lemma.
2: Apply shift_leEq_minus; Step (Pts P i (lt_le_weak ?? H1)); Apply prf2.
Apply compact_elements with (prf2 ???? P i (lt_le_weak ?? H1) H1).
Apply HfP.
Elim (HfQ j (H ?? H1 Hj')); Intros.
Split.
Elim (sub_hyp i (lt_le_weak ?? H1)); Intros.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply p.
Apply leEq_transitive with (Pts Q j (lt_le_weak ?? (H i j H1 Hj'))).
Apply Partition_mon; Assumption.
Assumption.
Elim (sub_hyp (S i) H1); Intros.
EApply leEq_wdr.
2: Apply eq_symmetric_unfolded; Apply p.
Apply leEq_transitive with (Pts Q ? (H i j H1 Hj')).
Assumption.
Apply Partition_mon.
Rewrite (S_pred ?? (sub_S i)); Auto with arith.
Apply eq_imp_leEq; Apply AbsIR_eq_x.
Apply shift_leEq_minus; Step (Pts Q j (lt_le_weak ?? (H ?? H1 Hj'))); Apply prf2.
Qed.

(* Begin_Tex_Verb *)
Lemma first_refinement_lemma :
  (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum HfQ incF))
    [<=]e[*](b[-]a).
(* End_Tex_Verb *)
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply ref_calc2.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply ref_calc3.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply ref_calc4.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply ref_calc5.
EApply leEq_transitive.
Apply ref_calc6.
EApply leEq_transitive.
Apply ref_calc7.
EApply leEq_transitive.
Apply ref_calc8.
Apply leEq_wdl with e[*](Sumx [i:nat][Hi:(lt i n)](Sum2 [j:nat][Hj:(le (sub i) j)][Hj':(le j (pred (sub (S i))))]
  (Pts Q ? (H' ?? Hi Hj'))[-](Pts Q ? (lt_le_weak ?? (H ?? Hi Hj'))))).
Apply mult_resp_leEq_lft.
2: Apply less_leEq; Assumption.
Apply leEq_wdl with (Sumx [i:nat][Hi:(lt i n)](Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi))).
2: Apply Sumx_wd; Intros.
2: Apply eq_symmetric_unfolded; Apply ref_calc1.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply Mengolli_Sum with f:=[i:nat][Hi:(le i n)](Pts P i Hi).
EApply leEq_transitive.
Apply leEq_AbsIR.
EApply leEq_wdr.
2: Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step a; Assumption.
Apply compact_elements with Hab; Apply Partition_in_compact.
Red; Intros; Apply prf1; Auto.
Intros; Apply cg_minus_wd; Apply prf1; Auto.
Apply eq_symmetric_unfolded; EApply eq_transitive_unfolded.
2: Apply Sumx_comm_scal'.
Apply Sumx_wd; Intros.
EApply eq_transitive_unfolded.
2: Apply Sum2_comm_scal'.
Algebra.
Apply sub_SS.
Qed.

End First_Refinement_Lemma.

Section Second_Refinement_Lemma.

(* Tex_Prose
This is inequality~(2.6.7).

\begin{convention}
\begin{itemize}
\item \verb!P,Q,R! are partitions of \verb!I! with, respectively, \verb!j,n! and \verb!k! points;
\item \verb!Q! is a common refinement of \verb!P! and \verb!R!;
\item \verb!e,e'! are positive real numbers;
\item \verb!d,d'! are the moduli of continuity of \verb!F! for \verb!e,e'!;
\item the Mesh of \verb!P! is less or equal to \verb!d!;
\item the Mesh of \verb!R! is less or equal to \verb!d'!;
\item \verb!fP,fQ! and \verb!fR! are choices of points respecting the partitions \verb!P,Q! and \verb!R!, respectively.
\end{itemize}
\end{convention}
*)

Variables n,j,k:nat.

Variable P:(Partition Hab j).
Variable Q:(Partition Hab n).
Variable R:(Partition Hab k).

Hypothesis HrefP : (Refinement P Q).
Hypothesis HrefR : (Refinement R Q).

Variables e,e':IR.
Hypothesis He:Zero[<]e.
Hypothesis He':Zero[<]e'.

Local d:=(proj1_sigS2P ??? (contF' e He)).
Local d':=(proj1_sigS2P ??? (contF' e' He')).

Hypothesis HMeshP : (Mesh P)[<=]d.
Hypothesis HMeshR : (Mesh R)[<=]d'.

Variable fP:(i:nat)(lt i j)->IR.
Hypothesis HfP:(Points_in_Partition P fP).
Hypothesis HfP':(nat_less_n_fun ?? fP).

Variable fQ:(i:nat)(lt i n)->IR.
Hypothesis HfQ:(Points_in_Partition Q fQ).
Hypothesis HfQ':(nat_less_n_fun ?? fQ).

Variable fR:(i:nat)(lt i k)->IR.
Hypothesis HfR:(Points_in_Partition R fR).
Hypothesis HfR':(nat_less_n_fun ?? fR).

(* Begin_Tex_Verb *)
Lemma second_refinement_lemma :
  (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum HfR incF))
    [<=]e[*](b[-]a)[+]e'[*](b[-]a).
(* End_Tex_Verb *)
Apply leEq_wdl with (AbsIR ((Partition_Sum HfP incF)[-](Partition_Sum HfQ incF))[+]((Partition_Sum HfQ incF)[-](Partition_Sum HfR incF))).
2: Apply AbsIR_wd; Rational.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
Apply first_refinement_lemma with He; Assumption.
EApply leEq_wdl.
2: Apply AbsIR_minus.
Apply first_refinement_lemma with He'; Assumption.
Qed.

End Second_Refinement_Lemma.

Section Third_Refinement_Lemma.

(* Tex_Prose
This is an approximation of inequality~(2.6.7), but without assuming the existence of a common refinement of $P$ and $R$.

\begin{convention}
\begin{itemize}
\item \verb!P,R! are partitions of \verb!I! with, respectively, \verb!n! and \verb!m! points;
\item \verb!e,e'! are positive real numbers;
\item \verb!d,d'! are the moduli of continuity of \verb!F! for \verb!e,e'!;
\item the Mesh of \verb!P! is less than \verb!d!;
\item the Mesh of \verb!R! is less than \verb!d'!;
\item \verb!fP! and \verb!fR! are choices of points respecting the partitions \verb!P! and \verb!R!, respectively;
\item \verb!beta! is a positive real number.
\end{itemize}
\end{convention}
*)

Variables n,m:nat.

Variable P:(Partition Hab n).
Variable R:(Partition Hab m).

Variables e,e':IR.
Hypothesis He:Zero[<]e.
Hypothesis He':Zero[<]e'.

Local d:=(proj1_sigS2P ??? (contF' e He)).
Local d':=(proj1_sigS2P ??? (contF' e' He')).

Hypothesis HMeshP : (Mesh P)[<]d.
Hypothesis HMeshR : (Mesh R)[<]d'.

Variable fP:(i:nat)(lt i n)->IR.
Hypothesis HfP:(Points_in_Partition P fP).
Hypothesis HfP':(nat_less_n_fun ?? fP).

Variable fR:(i:nat)(lt i m)->IR.
Hypothesis HfR:(Points_in_Partition R fR).
Hypothesis HfR':(nat_less_n_fun ?? fR).

Hypothesis Hab' : a[<]b.

Variable beta : IR.
Hypothesis Hbeta : Zero[<]beta.

Local alpha := beta[/]ThreeNZ.

Local Halpha : Zero[<]alpha.
Unfold alpha; Apply pos_div_three; Assumption.
Qed.

Local csi1 := (Min b[-]a ((d[-](Mesh P))[/]TwoNZ)).

Local Hcsi1 : Zero[<]csi1.
Unfold csi1; Apply less_Min.
Apply shift_less_minus; Step a; Assumption.
Apply pos_div_two.
Apply shift_less_minus.
Step (Mesh P); Assumption.
Qed.

Local delta1 := (Min csi1 alpha[/]?[//](mult_resp_ap_zero 
  IR ?? (nring_ap_zero ? n (SPap_n ??? Hab' ? P)) (max_one_ap_zero (Norm_Funct contF)))).

Local Hdelta1 : (delta1[/]TwoNZ)[<]b[-]a.
Apply shift_div_less'.
Apply pos_two.
Apply leEq_less_trans with b[-]a.
Unfold delta1; Clear delta1.
Apply leEq_transitive with csi1.
Apply Min_leEq_lft.
Unfold csi1.
Apply Min_leEq_lft.
Step Zero[+](b[-]a); RStepr (b[-]a)[+](b[-]a).
Apply plus_resp_less_rht.
Apply shift_less_minus; Step a; Assumption.
Qed.

Local P':=(sep__part ??? F contF Hab' ? P ? Halpha ? Hcsi1 Hdelta1).

Local sep_P' : (_Separated P').
Red; Intros.
Unfold P'; Apply sep__part_mon.
Qed.

Local Mesh_P' : (Mesh P')[<]d.
Unfold P'.
EApply leEq_less_trans.
Apply sep__part_mon_Mesh.
Unfold csi1.
Apply shift_plus_less'; EApply leEq_less_trans.
Apply Min_leEq_rht.
Apply pos_div_two'.
Apply shift_less_minus.
Step (Mesh P); Assumption.
Qed.

Local fP' := (sep__part_pts ??? F contF Hab' ? P ? Halpha ? Hcsi1 fP).

Local fP'_in_P' : (Points_in_Partition P' fP').
Unfold fP' P'; Apply sep__part_pts_in_Partition.
Assumption.
Qed.

Local P'_P_sum : (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum fP'_in_P' incF))[<=]alpha.
Apply leEq_wdl with 
  (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum (sep__part_pts_in_Partition ??? F contF Hab' ? P ? Halpha ? Hcsi1 Hdelta1 ? HfP) incF)).
Apply sep__part_Sum.
Assumption.
Apply AbsIR_wd; Apply cg_minus_wd.
Algebra.
Unfold Partition_Sum; Apply Sumx_wd; Intros.
Algebra.
Qed.

Local csi2 := (Min b[-]a ((d'[-](Mesh R))[/]TwoNZ)).

Local Hcsi2 : Zero[<]csi2.
Unfold csi2; Apply less_Min.
Apply shift_less_minus; Step a; Assumption.
Apply pos_div_two.
Apply shift_less_minus.
Step (Mesh R); Assumption.
Qed.

Local delta2 := (Min csi2 alpha[/]?[//](mult_resp_ap_zero 
  IR ?? (nring_ap_zero ? m (SPap_n ??? Hab' ? R)) (max_one_ap_zero (Norm_Funct contF)))).

Local Hdelta2 : (delta2[/]TwoNZ)[<]b[-]a.
Apply shift_div_less'.
Apply pos_two.
Apply leEq_less_trans with b[-]a.
Unfold delta2; Clear delta2.
Apply leEq_transitive with csi2.
Apply Min_leEq_lft.
Unfold csi2.
Apply Min_leEq_lft.
Step Zero[+](b[-]a); RStepr (b[-]a)[+](b[-]a).
Apply plus_resp_less_rht.
Apply shift_less_minus; Step a; Assumption.
Qed.

Local R':=(sep__part ??? F contF Hab' ? R ? Halpha ? Hcsi2 Hdelta2).

Local sep_R' : (_Separated R').
Red; Intros.
Unfold R'; Apply sep__part_mon.
Qed.

Local Mesh_R' : (Mesh R')[<]d'.
Unfold R'.
EApply leEq_less_trans.
Apply sep__part_mon_Mesh.
Unfold csi2.
Apply shift_plus_less'; EApply leEq_less_trans.
Apply Min_leEq_rht.
Apply pos_div_two'.
Apply shift_less_minus.
Step (Mesh R); Assumption.
Qed.

Local fR' := (sep__part_pts ??? F contF Hab' ? R ? Halpha ? Hcsi2 fR).

Local fR'_in_R' : (Points_in_Partition R' fR').
Unfold fR' R'; Apply sep__part_pts_in_Partition.
Assumption.
Qed.

Local R'_R_sum : (AbsIR (Partition_Sum HfR incF)[-](Partition_Sum fR'_in_R' incF))[<=]alpha.
Apply leEq_wdl with 
  (AbsIR (Partition_Sum HfR incF)[-](Partition_Sum (sep__part_pts_in_Partition ??? F contF Hab' ? R ? Halpha ? Hcsi2 Hdelta2 ? HfR) incF)).
Apply sep__part_Sum.
Assumption.
Apply AbsIR_wd; Apply cg_minus_wd.
Algebra.
Unfold Partition_Sum; Apply Sumx_wd; Intros.
Algebra.
Qed.

Local csi3 := d[-](Mesh P').

Local Hcsi3 : Zero[<]csi3.
Unfold csi3.
Apply shift_less_minus; Step (Mesh P').
Apply Mesh_P'.
Qed.

Local Q := (sep__sep_part ??? F contF Hab' ???? sep_P' sep_R' ? Halpha ? Hcsi3).

Local Mesh_Q : (Mesh Q)[<=]d.
Unfold Q; EApply leEq_wdr.
Apply sep__sep_Mesh.
Unfold csi3; Rational.
Qed.

Local sep_Q : (Separated Q R').
Unfold Q; Apply sep__sep_lemma.
Qed.

Local fQ := (sep__sep_points ??? F contF Hab' ???? sep_P' sep_R' ? Halpha ? Hcsi3 fP').

Local fQ_in_Q : (Points_in_Partition Q fQ).
Unfold Q fQ; Apply sep__sep_points_lemma.
Apply fP'_in_P'.
Qed.

Local Q_P'_sum : (AbsIR (Partition_Sum fP'_in_P' incF)[-](Partition_Sum fQ_in_Q incF))[<=]alpha.
Apply leEq_wdl with (AbsIR (Partition_Sum fP'_in_P' incF)[-]
  (Partition_Sum (sep__sep_points_lemma ??? F contF Hab' ???? sep_P' sep_R' ? Halpha ? Hcsi3 ? fP'_in_P') incF)).
Unfold Q fQ; Apply sep__sep_Sum.
Apply AbsIR_wd.
Unfold Partition_Sum; Apply cg_minus_wd.
Algebra.
Apply Sumx_wd; Intros.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma third_refinement_lemma :
  (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum HfR incF))
    [<=](e[*](b[-]a))[+](e'[*](b[-]a))[+]beta.
(* End_Tex_Verb *)
Apply leEq_wdl with (AbsIR ((Partition_Sum HfP incF)[-](Partition_Sum fP'_in_P' incF))[+]
  ((Partition_Sum fP'_in_P' incF)[-](Partition_Sum fQ_in_Q incF))[+]((Partition_Sum fQ_in_Q incF)[-](Partition_Sum fR'_in_R' incF))[+]
  ((Partition_Sum fR'_in_R' incF)[-](Partition_Sum HfR incF))).
Apply leEq_wdr with alpha[+]alpha[+]((e[*](b[-]a))[+]e'[*](b[-]a))[+]alpha.
2: Unfold alpha; Rational.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
Apply P'_P_sum.
Apply Q_P'_sum.
2: EApply leEq_wdl.
3: Apply AbsIR_minus.
2: Apply R'_R_sum.
2: Apply AbsIR_wd; Rational.
EApply second_refinement_lemma with Q:=(Separated_Refinement ??????? sep_Q) He:=He He':=He'.
Apply Separated_Refinement_lft.
Apply Separated_Refinement_rht.
Apply Mesh_Q.
Apply less_leEq; Apply Mesh_R'.
Apply Partition_imp_points_1.
Apply Partition_imp_points_2.
Qed.

End Third_Refinement_Lemma.

Section Fourth_Refinement_Lemma.

Local Fa:=(Part F a (incF ? (compact_inc_lft a b Hab))).

Syntactic Definition just:=[z:?](incF ? (Pts_part_lemma ?????? z ??)).

Local sum_lemma_aux : (n:nat)(P:(Partition Hab n))(fP:?)(HfP:(Points_in_Partition P fP))
  (Partition_Sum HfP incF)[=](Fa)[*](b[-]a)[-]
    (Sumx [i:nat][Hi:(lt i n)]((Fa)[-](Part F (fP i Hi) (just HfP)))[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi)))).
Intros; Apply eq_transitive_unfolded with
    (Sumx [i:nat][Hi:(lt i n)]Fa[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi))))[-]
    (Sumx [i:nat][Hi:(lt i n)](Fa[-](Part F (fP i Hi) (just HfP)))[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi)))).
EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply Sumx_minus_Sumx.
Unfold Partition_Sum; Apply Sumx_wd; Intros.
EApply eq_transitive_unfolded.
2: Apply ring_distl_minus.
Apply mult_wd_lft.
RStepr (Part F (fP i H) (just HfP)); Algebra.
Apply cg_minus_wd.
2: Algebra.
Stepr Fa[*]b[-]Fa[*]a.
EApply eq_transitive_unfolded.
Apply Mengolli_Sum with f:=[i:nat][Hi:(le i n)]Fa[*](Pts P i Hi).
Red; Intros.
Apply mult_wd_rht.
Apply prf1; Auto.
Intros; Algebra.
Apply cg_minus_wd; Apply mult_wd_rht.
Apply finish.
Apply start.
Qed.

(* Tex_Prose
Finally, this is inequality~(2.6.7) exactly as stated.

\begin{convention}
\begin{itemize}
\item \verb!P,R! are partitions of \verb!I! with, respectively, \verb!n! and \verb!m! points;
\item \verb!e,e'! are positive real numbers;
\item \verb!d,d'! are the moduli of continuity of \verb!F! for \verb!e,e'!;
\item the Mesh of \verb!P! is less than \verb!d!;
\item the Mesh of \verb!R! is less than \verb!d'!;
\item \verb!fP! and \verb!fR! are choices of points respecting the partitions \verb!P! and \verb!R!, respectively;
\end{itemize}
\end{convention}
*)

Variables n,m:nat.

Variable P:(Partition Hab n).
Variable R:(Partition Hab m).

Variables e,e':IR.
Hypothesis He:Zero[<]e.
Hypothesis He':Zero[<]e'.

Local d:=(proj1_sigS2P ??? (contF' e He)).
Local d':=(proj1_sigS2P ??? (contF' e' He')).

Hypothesis HMeshP : (Mesh P)[<]d.
Hypothesis HMeshR : (Mesh R)[<]d'.

Variable fP:(i:nat)(lt i n)->IR.
Hypothesis HfP:(Points_in_Partition P fP).
Hypothesis HfP':(nat_less_n_fun ?? fP).

Variable fR:(i:nat)(lt i m)->IR.
Hypothesis HfR:(Points_in_Partition R fR).
Hypothesis HfR':(nat_less_n_fun ?? fR).

(* Begin_Tex_Verb *)
Hypothesis Hab' : b[-]a[<](Min d d').
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fourth_refinement_lemma :
  (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum HfR incF))
    [<=]e[*](b[-]a)[+]e'[*](b[-]a).
(* End_Tex_Verb *)
Generalize (proj2b_sigS2P ??? (contF' e He)); Generalize (proj2a_sigS2P ??? (contF' e He)); Fold d; Intros Hd Hdd.
Generalize (proj2b_sigS2P ??? (contF' e' He')); Generalize (proj2a_sigS2P ??? (contF' e' He')); Fold d'; Intros Hd' Hdd'.
Apply leEq_wdl with (AbsIR
  (Fa[*](b[-]a)[-]
    (Sumx [i:nat][Hi:(lt i n)](Fa[-](Part F (fP i Hi) (just HfP)))[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi)))))[-]
  (Fa[*](b[-]a)[-]
    (Sumx [j:nat][Hj:(lt j m)](Fa[-](Part F (fR j Hj) (just HfR)))[*]((Pts R ? Hj)[-](Pts R ? (lt_le_weak ?? Hj)))))).
2: Apply AbsIR_wd; Apply eq_symmetric_unfolded.
2: Apply cg_minus_wd; Apply sum_lemma_aux.
Apply leEq_wdl with (AbsIR
    (Sumx [j:nat][Hj:(lt j m)](Fa[-](Part F (fR j Hj) (just HfR)))[*]((Pts R ? Hj)[-](Pts R ? (lt_le_weak ?? Hj))))[-]
    (Sumx [i:nat][Hi:(lt i n)](Fa[-](Part F (fP i Hi) (just HfP)))[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi))))).
2: Apply AbsIR_wd; Rational.
RStepr e'[*](b[-]a)[+]e[*](b[-]a).
EApply leEq_transitive.
Apply triangle_IR_minus.
Apply plus_resp_leEq_both.
EApply leEq_transitive.
Apply triangle_SumxIR.
Apply leEq_wdr with (Sumx [i:nat][Hi:(lt i m)]e'[*]((Pts R ? Hi)[-](Pts R ? (lt_le_weak ?? Hi)))).
Apply Sumx_resp_leEq; Intros.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
Unfold Fa; Apply Hdd'; Unfold I.
Apply compact_inc_lft.
Apply Pts_part_lemma with m R; Assumption.
Apply leEq_transitive with (AbsIR b[-]a).
Apply compact_elements with Hab.
Apply compact_inc_lft.
Apply Pts_part_lemma with m R; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step a; Assumption.
EApply leEq_transitive.
Apply less_leEq; Apply Hab'.
Apply Min_leEq_rht.
Apply eq_imp_leEq; Apply AbsIR_eq_x.
Apply shift_leEq_minus; Step (Pts R i (lt_le_weak ?? H)); Apply prf2.
EApply eq_transitive_unfolded.
Apply Sumx_comm_scal' with f:=[i:nat][Hi:(lt i m)]((Pts R ? Hi)[-](Pts R ? (lt_le_weak ?? Hi))).
Apply mult_wd_rht.
EApply eq_transitive_unfolded.
Apply Mengolli_Sum with f:=[i:nat][Hi:(le i m)](Pts R i Hi).
Red; Intros.
Apply prf1; Auto.
Intros; Algebra.
Apply cg_minus_wd; [Apply finish | Apply start].
EApply leEq_transitive.
Apply triangle_SumxIR.
Apply leEq_wdr with (Sumx [i:nat][Hi:(lt i n)]e[*]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi)))).
Apply Sumx_resp_leEq; Intros.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_resp_mult.
Apply mult_resp_leEq_both; Try Apply AbsIR_nonneg.
Unfold Fa; Apply Hdd; Unfold I.
Apply compact_inc_lft.
Apply Pts_part_lemma with n P; Assumption.
Apply leEq_transitive with (AbsIR b[-]a).
Apply compact_elements with Hab.
Apply compact_inc_lft.
Apply Pts_part_lemma with n P; Assumption.
EApply leEq_wdl.
2: Apply eq_symmetric_unfolded; Apply AbsIR_eq_x.
2: Apply shift_leEq_minus; Step a; Assumption.
EApply leEq_transitive.
Apply less_leEq; Apply Hab'.
Apply Min_leEq_lft.
Apply eq_imp_leEq; Apply AbsIR_eq_x.
Apply shift_leEq_minus; Step (Pts P i (lt_le_weak ?? H)); Apply prf2.
EApply eq_transitive_unfolded.
Apply Sumx_comm_scal' with f:=[i:nat][Hi:(lt i n)]((Pts P ? Hi)[-](Pts P ? (lt_le_weak ?? Hi))).
Apply mult_wd_rht.
EApply eq_transitive_unfolded.
Apply Mengolli_Sum with f:=[i:nat][Hi:(le i n)](Pts P i Hi).
Red; Intros.
Apply prf1; Auto.
Intros; Algebra.
Apply cg_minus_wd; [Apply finish | Apply start].
Qed.

End Fourth_Refinement_Lemma.

Section Main_Refinement_Lemma.

(* Tex_Prose
We finish by presenting Theorem~9.

\begin{convention}
\begin{itemize}
\item \verb!P,R! are partitions of \verb!I! with, respectively, \verb!n! and \verb!m! points;
\item \verb!e,e'! are positive real numbers;
\item \verb!d,d'! are the moduli of continuity of \verb!F! for \verb!e,e'!;
\item the Mesh of \verb!P! is less than \verb!d!;
\item the Mesh of \verb!R! is less than \verb!d'!;
\item \verb!fP! and \verb!fR! are choices of points respecting the partitions \verb!P! and \verb!R!, respectively;
\end{itemize}
\end{convention}
*)

Variables n,m:nat.

Variable P:(Partition Hab n).
Variable R:(Partition Hab m).

Variables e,e':IR.
Hypothesis He:Zero[<]e.
Hypothesis He':Zero[<]e'.

Local d:=(proj1_sigS2P ??? (contF' e He)).
Local d':=(proj1_sigS2P ??? (contF' e' He')).

Hypothesis HMeshP : (Mesh P)[<]d.
Hypothesis HMeshR : (Mesh R)[<]d'.

Variable fP:(i:nat)(lt i n)->IR.
Hypothesis HfP:(Points_in_Partition P fP).
Hypothesis HfP':(nat_less_n_fun ?? fP).

Variable fR:(i:nat)(lt i m)->IR.
Hypothesis HfR:(Points_in_Partition R fR).
Hypothesis HfR':(nat_less_n_fun ?? fR).

(* Begin_Tex_Verb *)
Lemma refinement_lemma :
  (AbsIR (Partition_Sum HfP incF)[-](Partition_Sum HfR incF))
    [<=]e[*](b[-]a)[+]e'[*](b[-]a).
(* End_Tex_Verb *)
Cut Zero[<](Min d d').
Intro; Elim (cotrans_less_unfolded ??? H b[-]a); Intro.
Stepr (e[*](b[-]a)[+]e'[*](b[-]a))[+]Zero.
Apply shift_leEq_plus'.
Red; Apply approach_zero_weak.
Intros beta Hbeta.
Apply shift_minus_leEq.
Stepr (e[*](b[-]a)[+]e'[*](b[-]a))[+]beta.
Apply third_refinement_lemma with He:=He He':=He'; Try Assumption.
Step Zero[+]a; Apply shift_plus_less; Assumption.
Apply fourth_refinement_lemma with He He'.
Assumption.
Apply less_Min.
Unfold d; Apply proj2a_sigS2P.
Unfold d'; Apply proj2a_sigS2P.
Qed.

End Main_Refinement_Lemma.

End Refinement_Lemma.
