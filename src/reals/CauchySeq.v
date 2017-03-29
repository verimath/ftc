(* $Id: CauchySeq.v,v 1.4 2003/03/11 13:36:16 lcf Exp $ *)

Require Export CReals.

(* Tex_Prose
\begin{convention}
Let {\tt\hypertarget{Single_Axiom}{IR}} be a structure for real numbers.
\end{convention}
*)

(*
Require Export R_CReals.
Definition IR : CReals := Concrete_R.
Opaque IR.
*)

Axiom IR : CReals.

Syntactic Definition PartIR := (PartFunct IR).
Syntactic Definition ProjIR1 := (prj1 IR ???).
Syntactic Definition ProjIR2 := (prj2 IR ???).

Load Transparent_algebra.

(* Tex_Prose
\begin{convention}
With {\tt\hypertarget{Syntactic_31}{ZeroR}} and {\tt\hypertarget{Syntactic_32}{OneR}} we denote the zero and one of this structure.
\end{convention}
*)

Syntactic Definition ZeroR := (Zero::IR).
Syntactic Definition OneR := (One::IR).

Section CReals_axioms.
(* Tex_Prose
\section{CReals axioms}
*)

(* Begin_Tex_Verb *)
Lemma CReals_is_CReals : (is_CReals IR (!Lim IR)).
(* End_Tex_Verb *)
Unfold Lim.
Elim IR; Intros.
Exact crl_proof.
Qed.

(* Tex_Prose
First properties which follow trivially from the axioms.
*)

(* Begin_Tex_Verb *)
Lemma Lim_Cauchy : (s:(CauchySeq IR))(SeqLimit s (Lim s)).
(* End_Tex_Verb *)
Elim CReals_is_CReals; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Archimedes : (x:IR){n:nat | (x [<=] (nring n))}.
(* End_Tex_Verb *)
Elim CReals_is_CReals; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Archimedes' : (x:IR){n:nat & (x [<] (nring n))}.
(* End_Tex_Verb *)
Intro x.
Elim (Archimedes x[+]One); Intros n Hn.
Exists n.
Apply less_leEq_trans with x[+]One; Auto.
Apply less_plusOne.
Qed.

(* Tex_Prose
A stronger version, which often comes in useful.
*)

(* Begin_Tex_Verb *)
Lemma str_Archimedes : (x:IR)(Zero[<=]x)->
  {n:nat | (x[<=](nring n))/\((le (2) n)->((nring n)[-]Two)[<=]x)}.
(* End_Tex_Verb *)
Intros.
Elim (Archimedes x); Intros n Hn.
Induction n.
Exists O; Split; Auto.
Intro; ElimType False; Omega.

Clear Hrecn.
Induction n.
Exists (1).
Split; Intros; [Assumption | EApply leEq_transitive].
2: Apply H.
Simpl.
RStep [--](One::IR); Stepr [--](Zero::IR); Apply less_leEq; Apply inv_resp_less; Apply pos_one.
Cut (!nring IR n)[<](nring (S n)).
Intros.
Cut ((nring n)[<]x)+(x[<](nring (S n))).
Intros.
Elim H1; Intros.
Exists (S (S n)).
Split.
Assumption.
Intros.
Simpl; RStep (!nring IR n); Apply less_leEq; Assumption.
Apply Hrecn; Apply less_leEq; Assumption.
Apply cotrans_less_unfolded; Assumption.
Simpl; Apply less_plusOne.
Qed.

(* Begin_Tex_Verb *)
Definition CauchySeqR := (CauchySeq IR).
(* End_Tex_Verb *)

End CReals_axioms.

Section Cauchy_Defs.
(* Tex_Prose
\section{Cauchy definitions}
This section gives several definitions of Cauchy sequences. There
are no lemmas in this section.

\begin{enumerate}
\item
The current definition of Cauchy (\verb!Cauchy_prop!) is:
\[\forall \epsilon>0. \exists N. \forall m\geq N. |seq_m - seq_N|\leq\epsilon\]
\item
Variant 1 of Cauchy (\verb!Cauchy_prop1!) is:\\
\[\forall k. \exists N. \forall m \geq N. |seq_m - seq_N|\leq1/(k+1) \]

\item
 In all of the following variants the Limit occurs in the definition.
 Therefore it is useful to define an auxiliary
 predicate \verb!Cauchy_Lim_prop?!,
 in terms of which \verb!Cauchy_prop?! is defined.

Variant 2 of Cauchy (\verb!Cauchy_prop2!):
\[\begin{array}{l}
\exists y. \verb!Cauchy_Lim_prop2!~seq~y \text{ where }\\
\verb!Cauchy_Lim_prop2!~seq~y :=
\forall \epsilon>0. \exists N. \forall m \geq N. |seq_m - y|\leq\epsilon
\end{array}\]

Note that \verb!Cauchy_Lim_prop2! equals \verb!seqLimit!.
\item
Variant 3 of Cauchy (\verb!Cauchy_prop3!):
\[\begin{array}{l}
\exists y. \verb!Cauchy_Lim_prop3!~seq~y \text{ where }\\
\verb!Cauchy_Lim_prop3!~seq~y :=
\forall k. \exists N. \forall m\geq N. |seq_m - y|\leq1/(k+1)
\end{array}\]
\item
 The following variant is more restricted.\\
Variant 4 of Cauchy (\verb!Cauchy_prop4!):
\[\begin{array}{l}
\exists y. \verb!Cauchy_Lim_prop4!~seq~y \text{ where }\\
\verb!Cauchy_Lim_prop4!~seq~y := \forall k. |seq_k - y|\leq1/(k+1)
\end{array}\]
\end{enumerate}
 So
\[ \verb!Cauchy_prop4! \Rightarrow
   \verb!Cauchy_prop3! \Leftrightarrow
   \verb!Cauchy_prop2! \Leftrightarrow
   \verb!Cauchy_prop1! \Leftrightarrow
   \verb!Cauchy_prop!\]

 Note: I don't know which formulations are useful.

The inequalities are stated with $\leq$ rather than with $<$ for the following reason: both formulations
are equivalent, as is well known; and $\leq$ being a negative statement it makes proofs sometimes easier
and program extraction much more efficient.
*)

(* Begin_Tex_Verb *)
Definition Cauchy_prop1 := [seq:(nat->IR)]
                           (k:nat){ N:nat | (m:nat)((le N m) ->
                           (AbsSmall (one_div_succ k) ((seq m) [-] (seq N))))}.
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Definition Cauchy_Lim_prop2 := [seq:(nat->IR)][y:IR]
                               (eps:IR)(Zero [<] eps) ->
                               {N:nat | (m:nat)((le N m) ->
                               (AbsSmall eps ((seq m) [-] y)))}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_prop2 := [seq:(nat->IR)]
                           {y:IR & (Cauchy_Lim_prop2 seq y)}.
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Definition Cauchy_Lim_prop3 := [seq:(nat->IR)][y:IR]
                               (k:nat)
                               {N:nat | (m:nat)((le N m) ->
                               (AbsSmall (one_div_succ k) ((seq m) [-] y)))}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_prop3 := [seq:(nat->IR)]
                           {y:IR & (Cauchy_Lim_prop3 seq y)}.
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Definition Cauchy_Lim_prop4 := [seq:(nat->IR)][y:IR]
                         (((m:nat)(AbsSmall (one_div_succ m) ((seq m)[-]y)))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_prop4 := [seq:(nat->IR)]
                           {y:IR | Cauchy_Lim_prop4 seq y}.
(* End_Tex_Verb *)
End Cauchy_Defs.


Section Inequalities.
(* Tex_Prose
\section{Inequalities of Limits}
*)

(* Tex_Prose
The next lemma is equal to lemma \verb!Lim_Cauchy!.
*)
(* Begin_Tex_Verb *)
Lemma Cauchy_complete : (seq:(CauchySeq IR))
                        (Cauchy_Lim_prop2 seq (Lim seq)).
(* End_Tex_Verb *)
Exact Lim_Cauchy.
Qed.

(* Begin_Tex_Verb *)
Lemma less_Lim_so_less_seq : (seq:(CauchySeq IR))(y:IR)(y [<] (Lim seq)) ->
             {N:nat & (m:nat)(le N m)->(y [<] (seq m))}.
(* End_Tex_Verb *)
Intros.
Elim (Cauchy_complete seq ((Lim seq)[-]y)[/]TwoNZ).
Intro N.
Intros H0.
Split with N.
Intros.
Generalize (H0 ? H1); Intro.
Unfold AbsSmall in H2.
Elim H2.
Intros.

Apply plus_cancel_less with [--](Lim seq).
RStep [--]((Lim seq)[-]y).
RStepr (seq m) [-] (Lim seq).
EApply less_leEq_trans.
2: Apply H3.
Apply inv_resp_less; Apply pos_div_two'.
Apply shift_less_minus; Step y; Auto.

Apply pos_div_two.
Apply shift_less_minus; Step y; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_less_so_seq_less : (seq:(CauchySeq IR))(y:IR)((Lim seq) [<] y) ->
                            {N:nat & (m:nat)(le N m)->((seq m) [<] y)}.
(* End_Tex_Verb *)
Intros.
Elim (Cauchy_complete seq (y[-](Lim seq))[/]TwoNZ).
Intro N.
Intros H0.
Split with N.
Intros.
Generalize (H0 ? H1); Intro.
Unfold AbsSmall in H2.
Elim H2.
Intros H3 H4.

Apply plus_cancel_less with [--](Lim seq).
EApply leEq_less_trans.
Apply H4.
Apply pos_div_two'.
Apply shift_less_plus; RStep (Lim seq); Auto.

Apply pos_div_two.
Apply shift_less_minus; Step (Lim seq); Auto.
Qed.


(* Begin_Tex_Verb *)
Lemma Lim_less_Lim_so_seq_less_seq :
      	       (seq1,seq2:(CauchySeq IR))
               ((Lim seq1) [<] (Lim seq2)) ->
               { N:nat & (m:nat)(le N m)->((seq1 m) [<] (seq2 m))}.
(* End_Tex_Verb *)
Intros.
LetTac Av := ((Lim seq1) [+] (Lim seq2)) [/]TwoNZ in Goal.
Cut (Lim seq1) [<] Av; Try Intro.
Cut Av [<] (Lim seq2); Try Intro.
Generalize (Lim_less_so_seq_less ? ? H0); Intro.
Generalize (less_Lim_so_less_seq ? ? H1); Intro.
Elim H2; Intro N1; Intro H4.
Elim H3; Intro N2; Intro H5.
Exists (max N1 N2); Intros.
Apply less_leEq_trans with Av.
Apply H4.
Apply le_trans with (max N1 N2).
Apply le_max_l.
Assumption.
Apply less_leEq.
Apply H5.
Apply le_trans with (max N1 N2).
Apply le_max_r.
Assumption.
Unfold Av.
Apply Average_less_Greatest.
Assumption.
Unfold Av.
Apply Smallest_less_Average.
Assumption.
Qed.

(* Tex_Prose
The next lemma
follows from \verb!less_Lim_so_less_seq! with $y := (y+(\verb!Lim!~seq))/2$.
*)

(* Begin_Tex_Verb *)
Lemma less_Lim_so : (seq:(CauchySeq IR))(y:IR)(y [<] (Lim seq)) ->
             {eps:IR & (Zero [<] eps) &
                { N:nat & (m:nat)(le N m)->((y[+]eps) [<] (seq m))}}.
(* End_Tex_Verb *)
Intros.
Elim (less_Lim_so_less_seq seq ((y [+] (Lim seq)) [/]TwoNZ)).
Intros x H0.
Exists ((Lim seq) [-] y) [/]TwoNZ.
Apply pos_div_two.
Apply shift_zero_less_minus.
Assumption.
Exists x.
Intros.
RStep (y[+](Lim seq))[/]TwoNZ.
Apply H0.
Assumption.
Apply Average_less_Greatest.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_less_so : (seq:(CauchySeq IR))(y:IR)((Lim seq) [<] y) ->
             {eps:IR & (Zero [<] eps) &
               {N:nat & (m:nat)(le N m)->(((seq m)[+]eps) [<] y)}}.
(* End_Tex_Verb *)
Intros.
Elim (Lim_less_so_seq_less seq (((Lim seq) [+] y) [/]TwoNZ)). 
Intros x H0.
Exists (y [-] (Lim seq)) [/]TwoNZ.
Apply pos_div_two.
Apply shift_zero_less_minus.
Assumption.
Exists x.
Intros.
Apply shift_plus_less.
RStepr ((Lim seq)[+]y)[/]TwoNZ.
Apply H0.
Assumption.
Apply Smallest_less_Average.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_seq_so_leEq_Lim : (seq:CauchySeqR)(y:IR)((i:nat)y[<=](seq i)) ->
                                             (y[<=](Lim seq)).
(* End_Tex_Verb *)
Intros.
Unfold leEq.
Intro.
Generalize (Lim_less_so_seq_less ? ? H0); Intro.
Elim H1; Intros N H2.
Apply (H N).
Apply H2.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma str_leEq_seq_so_leEq_Lim : (seq:(CauchySeq IR))
  (y:IR)(EX N:nat | ((i:nat)(le N i)->y[<=](seq i)))->y[<=](Lim seq).
(* End_Tex_Verb *)
Intros.
Red; Intro.
Generalize (Lim_less_so_seq_less ?? H0).
Elim H; Intros N HN.
Intro.
Elim H1; Intros M HM.
Cut y[<]y.
Apply less_irreflexive_unfolded.
Apply leEq_less_trans with (seq (max N M)).
Apply HN; Apply le_max_l.
Apply HM; Apply le_max_r.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_leEq_Lim : (seq1,seq2:CauchySeqR)((i:nat)(seq1 i)[<=](seq2 i)) ->
                                           ((Lim seq1)[<=](Lim seq2)).
(* End_Tex_Verb *)
Intros.
Unfold leEq.
Intro.
Generalize (Lim_less_Lim_so_seq_less_seq ? ? H0); Intro.
Elim H1; Intros N H2.
Apply (H N).
Apply H2.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma seq_leEq_so_Lim_leEq : (seq:CauchySeqR)(y:IR)((i:nat)(seq i)[<=]y) ->
                                    ((Lim seq)[<=] y).
(* End_Tex_Verb *)
Intros.
Unfold leEq.
Intro.
Generalize (less_Lim_so_less_seq ? ? H0); Intro.
Elim H1; Intros N H2.
Apply (H N).
Apply H2.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma str_seq_leEq_so_Lim_leEq : (seq:(CauchySeq IR))
  (y:IR)(EX N:nat | ((i:nat)(le N i)->(seq i)[<=]y))->(Lim seq)[<=]y.
(* End_Tex_Verb *)
Intros.
Red; Intro.
Generalize (less_Lim_so_less_seq ?? H0).
Elim H; Intros N HN.
Intro.
Elim H1; Intros M HM.
Cut y[<]y.
Apply less_irreflexive_unfolded.
Apply less_leEq_trans with (seq (max N M)).
Apply HM; Apply le_max_r.
Apply HN; Apply le_max_l.
Qed.

(* Begin_Tex_Verb *)
Lemma Limits_unique : (seq:(CauchySeq IR))(y:IR)
                      (Cauchy_Lim_prop2 seq y) -> (y [=] (Lim seq)).
(* End_Tex_Verb *)
Intros.
Apply not_ap_imp_eq.
Unfold not; Intro.
Generalize (ap_imp_less ? ? ? H0); Intro.
Elim H1; Intro H2.
Elim (less_Lim_so ? ? H2); Intro eps; Intros H4 H5.
Elim H5; Intro N; Intro H6.
Unfold Cauchy_Lim_prop2 in H.
Elim (H ? H4); Intro N'; Intro H7.
Generalize (le_max_l N N'); Intro H8.
Generalize (le_max_r N N'); Intro H9.
Generalize (H6 ? H8); Intro H10.
Generalize (H7 ? H9); Intro H11.
Elim H11; Intros H12 H13.
Apply less_irreflexive_unfolded with x:=y[+]eps.
EApply less_leEq_trans.
Apply H10.
Apply plus_cancel_leEq_rht with [--]y.
RStepr eps.
Exact H13.

(* Second case similar to first case *)
Elim (Lim_less_so ? ? H2); Intro eps; Intros H4 H5.
Elim H5; Intro N; Intros H6.
Unfold Cauchy_Lim_prop2 in H.
Elim (H ? H4); Intro N'; Intros H7.
Generalize (le_max_l N N'); Intro H8.
Generalize (le_max_r N N'); Intro H9.
Generalize (H6 ? H8); Intro H10.
Generalize (H7 ? H9); Intro H11.
Elim H11; Intros H12 H13.
Apply less_irreflexive_unfolded with x:=y.
EApply leEq_less_trans.
2: Apply H10.
Apply plus_cancel_leEq_rht with (([--]y)[-]eps).
RStep [--]eps.
RStepr (seq (max N N'))[-]y.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_wd : (seq:nat->IR)(x,y:IR)(x[=]y)->
  (Cauchy_Lim_prop2 seq x)->(Cauchy_Lim_prop2 seq y).
(* End_Tex_Verb *)
Intros.
Red; Red in H0.
Intros.
Elim (H0 ? H1).
Intros N HN.
Exists N.
Intros.
Stepr (seq m)[-]x.
Apply HN; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_strext : (seq1,seq2:(CauchySeq IR))
  ((Lim seq1)[#](Lim seq2))->{n:nat & (seq1 n)[#](seq2 n)}.
(* End_Tex_Verb *)
Intros.
Cut {n:nat & (seq1 n)[<](seq2 n)}+{n:nat & (seq2 n)[<](seq1 n)}.
Intro; Inversion_clear H0; Elim H1; Intros n Hn.
Exists n; Apply less_imp_ap; Assumption.
Exists n; Apply Greater_imp_ap; Assumption.
Cut ((Lim seq1)[<](Lim seq2))+((Lim seq2)[<](Lim seq1)); Intros.
2: Apply ap_imp_less; Assumption.
Inversion_clear H0; [Left | Right].
Cut {n:nat & (m:nat)(le n m)->(seq1 m)[<](seq2 m)}.
2: Apply Lim_less_Lim_so_seq_less_seq; Assumption.
Intro; Elim H0; Intros N HN.
Exists N; Apply HN; Auto with arith.
Cut {n:nat & (m:nat)(le n m)->(seq2 m)[<](seq1 m)}.
2: Apply Lim_less_Lim_so_seq_less_seq; Assumption.
Intro; Elim H0; Intros N HN.
Exists N; Apply HN; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_ap_imp_seq_ap : (seq1,seq2:(CauchySeq IR))
  ((Lim seq1)[#](Lim seq2))->{N:nat & (m:nat)(le N m)->(seq1 m)[#](seq2 m)}.
(* End_Tex_Verb *)
Intros.
Elim (ap_imp_less ??? H); Intro.
Elim (Lim_less_Lim_so_seq_less_seq ?? a); Intros N HN.
Exists N; Intros.
Apply less_imp_ap; Apply HN; Assumption.
Elim (Lim_less_Lim_so_seq_less_seq ?? b); Intros N HN.
Exists N; Intros.
Apply Greater_imp_ap; Apply HN; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_ap_imp_seq_ap' : (seq1,seq2:(CauchySeq IR))
  ((Lim seq1)[#](Lim seq2))->{N:nat & (seq1 N)[#](seq2 N)}.
(* End_Tex_Verb *)
Intros.
Elim (Lim_ap_imp_seq_ap ?? H); Intros N HN.
Exists N; Apply HN.
Apply le_n.
Qed.

End Inequalities.

Section Equiv_Cauchy.
(* Tex_Prose
\section{Equivalence of formulations of Cauchy}
*)

(* Begin_Tex_Verb *)
Lemma Cauchy_prop1_prop : (seq:(nat->IR))
                          (Cauchy_prop1 seq) -> (Cauchy_prop seq).
(* End_Tex_Verb *)
Intros.
Unfold Cauchy_prop1 in H.
Unfold Cauchy_prop.
Intros.
Cut e[#]Zero.
Intro eNZ.
Elim (Archimedes (One [/]e[//]eNZ)).
Intros x H1.
Elim (H x).
Intros x0 H2.
Split with x0.
Intros.
Generalize (H2 ? H3).
Intro.
Apply AbsSmall_leEq_trans with (!one_div_succ IR x).

Unfold one_div_succ.
Unfold Snring.
Apply shift_div_leEq'.
Apply nring_pos.
Auto with arith.

Stepr (e[*](nring (S x))).
Apply leEq_transitive with e[*](nring x).
Apply shift_leEq_mult' with eNZ.
Assumption.

Assumption.

Apply less_leEq.
Apply mult_resp_less_lft.
Apply nring_less.
Auto.

Assumption.

Assumption.
Apply pos_ap_zero.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_prop2_prop : (seq:(nat->IR))
                          (Cauchy_prop2 seq) -> (Cauchy_prop seq).
(* End_Tex_Verb *)
Intros.
Unfold Cauchy_prop.
Intros.
Unfold Cauchy_prop2 in H.
Elim H.
Intro y; Intros H1.
Unfold Cauchy_Lim_prop2 in H1.
Elim (H1 (e[/]TwoNZ)).
Intro N.
Intros H2.
Exists N.
Intros.
Generalize (H2 ? H3); Intro.
Generalize (le_n N); Intro.
Generalize (H2 ? H5); Intro.
Generalize (AbsSmall_minus ? ? ? ? H6); Intro.
Generalize (AbsSmall_plus ? ? ? ? ? H4 H7); Intro.
RStep ((e[/]TwoNZ) [+] (e[/]TwoNZ)).
RStepr ((seq m)[-]y)[+](y[-](seq N)).
Assumption.
Apply pos_div_two.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_prop3_prop2 : (seq:(nat->IR))(y:IR)
                         (Cauchy_Lim_prop3 seq y) -> (Cauchy_Lim_prop2 seq y).
(* End_Tex_Verb *)
Intros.
Unfold Cauchy_Lim_prop2.
Intros.
Unfold Cauchy_Lim_prop3 in H.
Generalize (pos_ap_zero ? ? H0); Intro Heps.
Elim (Archimedes (One[/]eps[//]Heps)).
Intro K; Intros H1.
Elim (H K).
Intro N; Intros H2.
Exists N.
Intros.
Generalize (H2 ? H3); Intro.
Apply AbsSmall_leEq_trans with (!one_div_succ IR K); Try Assumption.
Unfold one_div_succ.
Unfold Snring.
Apply shift_div_leEq'.
Apply nring_pos.
Auto with arith.
Apply leEq_transitive with eps[*](nring K).
Apply shift_leEq_mult' with Heps; Assumption.

Step (nring K)[*]eps.
Apply less_leEq.
Apply mult_resp_less; Try Assumption.
Apply nring_less.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_prop3_prop2 : (seq:(nat->IR))
                          (Cauchy_prop3 seq) -> (Cauchy_prop2 seq).
(* End_Tex_Verb *)
Unfold Cauchy_prop2.
Unfold Cauchy_prop3.
Intros.
Elim H; Intros x H0.
Exists x.
Apply Cauchy_Lim_prop3_prop2.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_prop3_prop : (seq:(nat->IR))
                          (Cauchy_prop3 seq) -> (Cauchy_prop seq).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_prop2_prop.
Apply Cauchy_prop3_prop2.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Build_CauchySeq1 : (seq:(nat->IR))
                         (Cauchy_prop1 seq) -> CauchySeqR.
(* End_Tex_Verb *)
Intros.
Unfold CauchySeqR.
Apply Build_CauchySeq with seq.
Apply Cauchy_prop1_prop.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_prop4_prop3 : (seq:(nat->IR))(y:IR)
                        (Cauchy_Lim_prop4 seq y) -> (Cauchy_Lim_prop3 seq y).
(* End_Tex_Verb *)
Intros.
Unfold Cauchy_Lim_prop4 in H.
Unfold Cauchy_Lim_prop3.
Intros.
Exists k.
Intros.
Apply AbsSmall_leEq_trans with (!one_div_succ IR m).
2: Apply H.
Apply one_div_succ_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_prop4_prop2 : (seq:(nat->IR))(y:IR)
                        (Cauchy_Lim_prop4 seq y) -> (Cauchy_Lim_prop2 seq y).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_Lim_prop3_prop2.
Apply Cauchy_Lim_prop4_prop3.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_prop4_prop3 : (seq:(nat->IR))
                        (Cauchy_prop4 seq) -> (Cauchy_prop3 seq).
(* End_Tex_Verb *)
Unfold Cauchy_prop4.
Unfold Cauchy_prop3.
Intros.
Elim H; Intros.
Exists x.
Apply Cauchy_Lim_prop4_prop3.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_prop4_prop : (seq:(nat->IR))
                             (Cauchy_prop4 seq) -> (Cauchy_prop seq).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_prop3_prop.
Apply Cauchy_prop4_prop3.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Build_CauchySeq4 : (seq:(nat->IR))
                         (Cauchy_prop4 seq) -> CauchySeqR.
(* End_Tex_Verb *)
Intros.
Unfold CauchySeqR.
Apply Build_CauchySeq with seq.
Apply Cauchy_prop4_prop.
Assumption.
Defined.

(* Begin_Tex_Verb *)
Definition Build_CauchySeq4_y : (seq:(nat->IR))(y:IR)
                           (Cauchy_Lim_prop4 seq y) -> CauchySeqR.
(* End_Tex_Verb *)
Intros.
Apply Build_CauchySeq4 with seq.
Unfold Cauchy_prop4.
Exists y.
Assumption.
Defined.

(* Begin_Tex_Verb *)
Lemma Lim_CauchySeq4 : (seq:(nat->IR))(y:IR)
                       (H:(Cauchy_Lim_prop4 seq y))
                       ((Lim (Build_CauchySeq4_y seq y H)) [=] y).
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded.
Apply Limits_unique.
Apply Cauchy_Lim_prop3_prop2.
Apply Cauchy_Lim_prop4_prop3.
Unfold Build_CauchySeq4_y.
Unfold Build_CauchySeq4.
Unfold CS_seq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Build_CauchySeq2 : (seq:(nat->IR))
                         (Cauchy_prop2 seq) -> CauchySeqR.
(* End_Tex_Verb *)
Intros.
Unfold CauchySeqR.
Apply Build_CauchySeq with seq.
Apply Cauchy_prop2_prop.
Assumption.
Defined.

(* Begin_Tex_Verb *)
Definition Build_CauchySeq2_y : (seq:(nat->IR))(y:IR)
                           (Cauchy_Lim_prop2 seq y) -> CauchySeqR.
(* End_Tex_Verb *)
Intros.
Apply Build_CauchySeq2 with seq.
Unfold Cauchy_prop2.
Exists y.
Assumption.
Defined.

(* Begin_Tex_Verb *)
Lemma Lim_CauchySeq2 : (seq:(nat->IR))(y:IR)
                       (H:(Cauchy_Lim_prop2 seq y))
                       ((Lim (Build_CauchySeq2_y seq y H)) [=] y).
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded.
Apply Limits_unique.
Unfold Build_CauchySeq2_y.
Unfold Build_CauchySeq2.
Unfold CS_seq.
Assumption.
Qed.

(* Tex_Prose
Well definedness.
*)

(* Begin_Tex_Verb *)
Lemma Cauchy_prop_wd : (seq1,seq2:nat->IR)(Cauchy_prop seq1)->
  ((n:nat)(seq1 n)[=](seq2 n))->(Cauchy_prop seq2).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H e H1).
Intros N Hn; Exists N; Intros.
Stepr (seq1 m)[-](seq1 N).
Apply Hn; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_prop2_wd : (seq1,seq2:nat->IR)(c:IR)
  (Cauchy_Lim_prop2 seq1 c)->((n:nat)(seq1 n)[=](seq2 n))->
  (Cauchy_Lim_prop2 seq2 c).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (H eps H1).
Intros N Hn; Exists N; Intros.
Stepr (seq1 m)[-]c.
Apply Hn; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_wd' : (seq1,seq2:(CauchySeq IR))
  ((n:nat)(seq1 n)[=](seq2 n))->(Lim seq1)[=](Lim seq2).
(* End_Tex_Verb *)
Intros.
Cut (Cauchy_Lim_prop2 seq1 (Lim seq2)).
Intro.
Apply eq_symmetric_unfolded.
Apply Limits_unique; Assumption.
Apply Cauchy_Lim_prop2_wd with (seq2::nat->IR).
Apply Cauchy_complete.
Intro; Apply eq_symmetric_unfolded; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_unique : (seq:nat->IR)(x,y:IR)
  (Cauchy_Lim_prop2 seq x)->(Cauchy_Lim_prop2 seq y)->(x[=]y).
(* End_Tex_Verb *)
Intros.
Cut (Cauchy_prop seq); [Intro | Apply Cauchy_prop2_prop; Exists y; Auto].
Apply eq_transitive_unfolded with (Lim (Build_CauchySeq ?? H1)).
Apply Limits_unique; Auto.
Apply eq_symmetric_unfolded; Apply Limits_unique; Auto.
Qed.

End Equiv_Cauchy.

Section Cauchy_props.

(* Tex_Prose
\section{Properties of Cauchy sequences}

We begin by defining the constant sequence and proving that it is Cauchy with the expected Limit.
*)

(* Begin_Tex_Verb *)
Definition Cauchy_const : IR->(CauchySeq IR).
(* End_Tex_Verb *)
Intro x.
Apply Build_CauchySeq with [n:nat]x.
Intros; Exists O.
Intros; Stepr (Zero::IR).
Apply zero_AbsSmall; Apply less_leEq; Assumption.
Defined.

(* Begin_Tex_Verb *)
Lemma Lim_const : (x:IR)(x[=](Lim (Cauchy_const x))).
(* End_Tex_Verb *)
Intros.
Apply Limits_unique.
Red; Intro; Exists O.
Intros; Unfold Cauchy_const; Simpl.
Stepr (Zero::IR); Apply zero_AbsSmall; Apply less_leEq; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_plus : (seq1,seq2:(nat->IR))(y1,y2:IR)
                (Cauchy_Lim_prop2 seq1 y1) -> (Cauchy_Lim_prop2 seq2 y2) ->
                (Cauchy_Lim_prop2 ([n:nat]((seq1 n) [+] (seq2 n))) (y1[+]y2)).
(* End_Tex_Verb *)
Intros.
Unfold Cauchy_Lim_prop2.
Intros.
Cut (Zero [<] eps [/]TwoNZ).
Intro.
Elim (H ? H2); Intros x H3.
Elim (H0 ? H2); Intros x0 H4.
Exists (max x x0).
Intros.
RStepr ((seq1 m) [-] y1)[+] ((seq2 m) [-] y2).
Apply AbsSmall_eps_div_two.
Apply H3.
Apply le_trans with (max x x0).
Apply le_max_l.
Assumption.

Apply H4.
Apply le_trans with (max x x0).
Apply le_max_r.
Assumption.

Apply pos_div_two.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_plus : (seq1,seq2:CauchySeqR)
                   (Cauchy_prop ([n:nat]((seq1 n) [+] (seq2 n)))).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_prop2_prop.
Unfold Cauchy_prop2.
Exists (Lim seq1) [+] (Lim seq2).
Apply Cauchy_Lim_plus.
Apply Cauchy_complete.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_plus : (seq1,seq2:CauchySeqR)
  (Lim (Build_CauchySeq IR ([n:nat]((seq1 n) [+] (seq2 n)))
                         (Cauchy_plus seq1 seq2)))
    [=] ((Lim seq1) [+] (Lim seq2)).
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded.
Apply Limits_unique.
Simpl.
Apply Cauchy_Lim_plus.
Apply Cauchy_complete.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_inv : (seq:(nat->IR))(y:IR)
                (Cauchy_Lim_prop2 seq y) ->
                (Cauchy_Lim_prop2 ([n:nat]([--](seq n))) ([--]y)).
(* End_Tex_Verb *)
Intros.
Unfold Cauchy_Lim_prop2.
Intros.
Elim (H ? H0); Intros x H1.
Exists x.
Intros.
RStepr [--]((seq m)[-] y).
Apply inv_resp_AbsSmall.
Apply H1.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_inv : (seq:CauchySeqR)
                     (Cauchy_prop ([n:nat]([--](seq n)))).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_prop2_prop.
Unfold Cauchy_prop2.
Exists [--](Lim seq).
Apply Cauchy_Lim_inv.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_inv : (seq:CauchySeqR)
  (Lim (Build_CauchySeq IR ([n:nat]([--] (seq n)))
                         (Cauchy_inv seq)))
    [=] ([--](Lim seq)).
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded.
Apply Limits_unique.
Simpl.
Apply Cauchy_Lim_inv.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_minus : (seq1,seq2:(nat->IR))(y1,y2:IR)
                (Cauchy_Lim_prop2 seq1 y1) -> (Cauchy_Lim_prop2 seq2 y2) ->
                (Cauchy_Lim_prop2 ([n:nat]((seq1 n) [-] (seq2 n))) (y1[-]y2)).
(* End_Tex_Verb *)
Intros.
Unfold cg_minus.
Change (Cauchy_Lim_prop2 ([n:nat](seq1 n)[+]([m:nat][--](seq2 m) n)) (y1[+][--]y2)).
Apply Cauchy_Lim_plus.
Assumption.
Apply Cauchy_Lim_inv.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_minus : (seq1,seq2:CauchySeqR)
                   (Cauchy_prop ([n:nat]((seq1 n) [-] (seq2 n)))).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_prop2_prop.
Unfold Cauchy_prop2.
Exists (Lim seq1) [-] (Lim seq2).
Apply Cauchy_Lim_minus.
Apply Cauchy_complete.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_minus : (seq1,seq2:CauchySeqR)
  (Lim (Build_CauchySeq IR ([n:nat]((seq1 n) [-] (seq2 n)))
                         (Cauchy_minus seq1 seq2)))
    [=] ((Lim seq1) [-] (Lim seq2)).
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded.
Apply Limits_unique.
Simpl.
Apply Cauchy_Lim_minus.
Apply Cauchy_complete.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Lim_mult : (seq1,seq2:(nat->IR))(y1,y2:IR)
                (Cauchy_Lim_prop2 seq1 y1) -> (Cauchy_Lim_prop2 seq2 y2) ->
                (Cauchy_Lim_prop2 ([n:nat]((seq1 n) [*] (seq2 n))) (y1[*]y2)).
(* End_Tex_Verb *)
Unfold Cauchy_Lim_prop2. Intros.
Elim (mult_contin ? y1 y2 eps H1). Intro c. Intros H2 H3.
Elim H3. Clear H3. Intro d. Intros H3 H4.
Elim (H c H2). Clear H. Intro N1. Intros H.
Elim (H0 d H3). Clear H0. Intro N2. Intros H0.
Cut {N:nat | (le N1 N) /\ (le N2 N)}. Intro.
Elim H5. Clear H5. Intro N. Intro H5. Elim H5. Clear H5. Intros.
Exists N. Intros.
Apply AbsSmall_wd_rht_unfolded with [--](y1[*]y2[-](seq1 m)[*](seq2 m)).
Apply inv_resp_AbsSmall.
Apply H4; Clear H4; Intros.
Apply AbsSmall_wd_rht_unfolded with [--]((seq1 m)[-]y1).
Apply inv_resp_AbsSmall.
Apply H. Apply le_trans with N; Auto.
Rational.
Apply AbsSmall_wd_rht_unfolded with [--]((seq2 m)[-]y2).
Apply inv_resp_AbsSmall.
Apply H0. Apply le_trans with N; Auto.
Rational.
Rational.
Elim (le_lt_dec N1 N2); Intros.
Exists N2. Auto.
Exists N1. Split. Auto. Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_mult : (seq1,seq2:CauchySeqR)
                   (Cauchy_prop ([n:nat]((seq1 n) [*] (seq2 n)))).
(* End_Tex_Verb *)
Intros.
Apply Cauchy_prop2_prop.
Unfold Cauchy_prop2.
Exists (Lim seq1) [*] (Lim seq2).
Apply Cauchy_Lim_mult.
Apply Cauchy_complete.
Apply Cauchy_complete.
Qed.

(* Begin_Tex_Verb *)
Lemma Lim_mult : (seq1,seq2:CauchySeqR)
  (Lim (Build_CauchySeq IR ([n:nat]((seq1 n) [*] (seq2 n)))
                         (Cauchy_mult seq1 seq2)))
    [=] ((Lim seq1) [*] (Lim seq2)).
(* End_Tex_Verb *)
Intros.
Apply eq_symmetric_unfolded.
Apply Limits_unique.
Simpl.
Apply Cauchy_Lim_mult.
Apply Cauchy_complete.
Apply Cauchy_complete.
Qed.

End Cauchy_props.
