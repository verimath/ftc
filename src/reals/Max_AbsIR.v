(* $Id: Max_AbsIR.v,v 1.6 2003/03/13 12:06:25 lcf Exp $ *)

Require Export CauchySeq.

Section Maximum.

Section Max_function.
(* Tex_Prose
\subsection{The actual max function}

\begin{convention}
Let \verb!x! and \verb!y! be reals
(we will define the maximum of \verb!x! and \verb!y!).
\end{convention}
*)

Variable x,y:IR.

(* Tex_Prose
\verb!Max_seq i! corresponds with $s_i$ in informal Definition~\ref{defmax}.
*)
(* Begin_Tex_Verb *)
Definition Max_seq : nat->IR.
(* End_Tex_Verb *)
Intro i.
Elim (cotrans_less_unfolded IR Zero (one_div_succ i)) with x[-]y.
  3: Apply one_div_succ_pos.
 Intro H; Apply x.
Intro H; Apply y.
Defined.

(* Begin_Tex_Verb *)
Lemma Max_seq_char : (n:nat)
  ((Zero[<]x[-]y)*{(Max_seq n)[=]x})+
  ((x[-]y[<](one_div_succ n))*{(Max_seq n)[=]y}).
(* End_Tex_Verb *)
Intros.
Unfold Max_seq.
Elim cotrans_less_unfolded; Intro H; Simpl.
 Left; Split; Algebra.
Right; Split; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_Max_seq : (Cauchy_prop Max_seq).
(* End_Tex_Verb *)
Apply Cauchy_prop1_prop.
Intro k.
Exists k; Intros m H.
Unfold Max_seq.
Elim cotrans_less_unfolded; Intro Hm; Simpl; Elim cotrans_less_unfolded; Intro Hk; Simpl.

Stepr (Zero::IR); Split; Apply less_leEq.
 Stepr [--](Zero::IR); Apply inv_resp_less; Apply one_div_succ_pos.
Apply one_div_succ_pos.

Apply leEq_imp_AbsSmall; Apply less_leEq; Auto.

Apply AbsSmall_minus.
Apply leEq_imp_AbsSmall; Apply less_leEq; Auto.
Apply less_leEq_trans with (!one_div_succ IR m); Auto.
Apply one_div_succ_resp_leEq; Auto.

Stepr (Zero::IR); Split; Apply less_leEq.
 Stepr [--](Zero::IR); Apply inv_resp_less; Apply one_div_succ_pos.
Apply one_div_succ_pos.
Qed.

(* Begin_Tex_Verb *)
Definition Max_CauchySeq : CauchySeqR.
(* End_Tex_Verb *)
Unfold CauchySeqR.
Apply Build_CauchySeq with Max_seq.
Exact Cauchy_Max_seq.
Defined.

(* Begin_Tex_Verb *)
Definition MAX : IR.
(* End_Tex_Verb *)
Apply Lim.
Exact Max_CauchySeq.
Defined.

(* Tex_Prose
Constructively, the elementary properties of the maximum function are:
\begin{itemize}
\item $x\leq \maxx (x,y)$,
\item $x\leq \maxx (x,y)$,
\item $z<\maxx(x,y) \Rightarrow z<x \vee z<y$.
\end{itemize}
(This can be more concisely expressed as
 $z<\maxx(x,y) \Leftrightarrow z<x \vee z<y$).
From these elementary properties we can prove all other properties, including
strong extensionality.
With strong extensionality, we can make the binary {\em operation} \verb!Max!.
(So \verb!Max! is \verb!MAX! coupled with some proofs.)
*)

(* Begin_Tex_Verb *)
Lemma lft_leEq_MAX : x[<=]MAX.
(* End_Tex_Verb *)
Stepr Zero[+]MAX; Apply shift_leEq_plus.
Red; Apply approach_zero_weak.
Intros e He.
Apply leEq_wdl with (Lim (Cauchy_const x))[-]MAX.
 2: Apply cg_minus_wd; [Apply eq_symmetric_unfolded; Apply Lim_const | Algebra].
Unfold MAX.
EApply leEq_wdl.
 2: Apply Lim_minus.
Simpl.
Elim (Archimedes One[/]e[//](pos_ap_zero ?? He)); Intros n Hn.
Cut Zero[<](!nring IR n).
Intro posn.
Apply str_seq_leEq_so_Lim_leEq.
Exists n; Intros i Hi.
Simpl.
Unfold Max_seq.
Elim cotrans_less_unfolded; Intro H; Simpl.
 Step (Zero::IR); Apply less_leEq; Auto.
Apply less_leEq; EApply less_transitive_unfolded.
Apply H.
Unfold one_div_succ Snring; Apply shift_div_less.
 Apply pos_nring_S.
Apply shift_less_mult' with (pos_ap_zero ?? He).
 Auto.
EApply leEq_less_trans.
 Apply Hn.
Apply nring_less; Auto with arith.

EApply less_leEq_trans.
 2: Apply Hn.
Apply recip_resp_pos; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma rht_leEq_MAX : y[<=]MAX.
(* End_Tex_Verb *)
Unfold MAX.
Apply leEq_seq_so_leEq_Lim.
Intro i; Simpl.
Unfold Max_seq.
Elim cotrans_less_unfolded; Intro H; Simpl.
 2: Apply leEq_reflexive.
Apply less_leEq; Step Zero[+]y.
Apply shift_plus_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma less_MAX_imp : (z:IR)(z[<]MAX) -> (z[<]x) + (z[<]y).
(* End_Tex_Verb *)
Intros.
Unfold MAX in H.
Elim (less_Lim_so_less_seq ?? H).
Intros N HN.
Simpl in HN.
Elim (Max_seq_char N); Intro Hseq; Inversion_clear Hseq;
 [Left | Right]; Stepr (Max_seq N); Auto with arith.
Qed.

End Max_function.

(* Begin_Tex_Verb *)
Lemma MAX_strong_ext : (bin_op_strong_ext ? MAX).
(* End_Tex_Verb *)
Unfold bin_op_strong_ext.
Unfold bin_fun_strong_ext.
Intros x1 x2 y1 y2 H.
Generalize (ap_imp_less ? ? ? H); Intro.
Elim H0; Intro H1.
 Generalize (less_MAX_imp ? ? ? H1); Intro H2.
 Elim H2; Intro H3.
  Left.
  Apply less_imp_ap.
  Apply leEq_less_trans with (MAX x1 y1); Auto.
  Apply lft_leEq_MAX.
 Right.
 Apply less_imp_ap.
 Apply leEq_less_trans with (MAX x1 y1); Auto.
 Apply rht_leEq_MAX.
Generalize (less_MAX_imp ? ? ? H1); Intro H2.
Elim H2; Intro.
 Left.
 Apply Greater_imp_ap.
 Apply leEq_less_trans with (MAX x2 y2); Auto.
 Apply lft_leEq_MAX.
Right.
Apply Greater_imp_ap.
Apply leEq_less_trans with (MAX x2 y2); Auto.
Apply rht_leEq_MAX.
Qed.

(* Begin_Tex_Verb *)
Lemma MAX_well_def : (bin_op_well_def IR MAX).
(* End_Tex_Verb *)
Unfold bin_op_well_def.
Apply  bin_fun_strong_ext_imp_well_def.
Exact MAX_strong_ext.
Qed.

Section properties_of_Max.

(* Tex_Prose
\subsection{Properties of Max}
*)

(* Begin_Tex_Verb *)
Definition Max := (Build_CSetoid_bin_op ? MAX MAX_strong_ext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma max_wd_unfolded : (x,y,x',y':IR)
  (x[=]x')->(y[=]y')->(Max x y)[=](Max x' y').
(* End_Tex_Verb *)
Cut (bin_op_well_def ? MAX); [Intro | Apply MAX_well_def].
Red in H.
Red in H.
Intros; Apply H; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma lft_leEq_Max : (x,y:IR)x [<=] (Max x y).
(* End_Tex_Verb *)
Unfold Max.
Simpl.
Exact lft_leEq_MAX.
Qed.

(* Begin_Tex_Verb *)
Lemma rht_leEq_Max : (x,y:IR)y [<=] (Max x y).
(* End_Tex_Verb *)
Unfold Max.
Simpl.
Exact rht_leEq_MAX.
Qed.

(* Begin_Tex_Verb *)
Lemma less_Max_imp : (x,y,z:IR)(z[<](Max x y)) -> (z[<]x) + (z[<]y).
(* End_Tex_Verb *)
Unfold Max.
Simpl.
Exact less_MAX_imp.
Qed.

(* Begin_Tex_Verb *)
Lemma Max_leEq : (x,y,z:IR)(x[<=]z) -> (y[<=]z) -> (Max x y)[<=]z.
(* End_Tex_Verb *)
Unfold Max.
Simpl.
Intros.
Unfold leEq.
Intro.
Generalize (less_MAX_imp ? ? ? H1); Intro.
Elim H2; Intros.
Elim H.
Assumption.
Elim H0.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Max_less : (x,y,z:IR)(x [<] z) -> (y [<] z) -> (Max x y) [<] z.
(* End_Tex_Verb *)
Intros.
Elim (smaller ? z[-]x z[-]y). Intro e. Intros H1 H2. Elim H2. Clear H2. Intros H2 H3.
Cut z[-]e[/]TwoNZ [<] z. Intro H4.
Elim (cotrans_less_unfolded ??? H4 (Max x y)); Intros H5.
Elim (less_Max_imp ? ? ? H5); Intros H6.
Cut (Not (e[/]TwoNZ [<] z[-]x)). Intro. Elim H7.
Apply less_leEq_trans with e; Auto.
Apply pos_div_two'; Auto.
Apply less_antisymmetric_unfolded.
Apply shift_minus_less. Apply shift_less_plus'. Auto.
Cut (Not (e[/]TwoNZ [<] z[-]y)). Intro. Elim H7.
Apply less_leEq_trans with e; Auto.
Apply pos_div_two'; Auto.
Apply less_antisymmetric_unfolded.
Apply shift_minus_less. Apply shift_less_plus'. Auto.
Auto.
Apply shift_minus_less. Step z[+]Zero.
Apply plus_resp_less_lft. Apply pos_div_two. Auto.
Apply shift_less_minus. Step x. Auto.
Apply shift_less_minus. Step y. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma equiv_imp_eq_max : (x,x',m:IR)
  ((y:IR)(x [<] y) -> (x' [<] y) -> (m [<] y)) ->
  ((y:IR)(m [<] y) -> (x [<] y)) ->
  ((y:IR)(m [<] y) -> (x' [<] y)) ->
    (Max x x') [=] m.
(* End_Tex_Verb *)
Intros.
Apply lt_equiv_imp_eq; Intros.
Apply H.
Apply leEq_less_trans with (Max x x').
Apply lft_leEq_Max. Auto.
Apply leEq_less_trans with (Max x x').
Apply rht_leEq_Max. Auto.
Apply Max_less; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Max_id : (x:IR)(Max x x) [=] x.
(* End_Tex_Verb *)
Intros.
Apply equiv_imp_eq_max; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Max_comm : (x,y:IR)(Max x y)[=](Max y x).
(* End_Tex_Verb *)
Cut (x,y:IR)(Max x y)[<=](Max y x).
Intros.
Apply leEq_imp_eq.
Apply H.
Apply H.
Intros.
Apply Max_leEq.
Apply rht_leEq_Max.
Apply lft_leEq_Max.
Qed.

(* Tex_Prose
\begin{lemma} \label{lemmaxgeq}
$\forall x,y\in\RR[ x\leq y \leftrightarrow \maxx(x,y) = y]$.
\end{lemma}
*)

(* Begin_Tex_Verb *)
Lemma leEq_imp_Max_is_rht : (x,y:IR)(x [<=] y) -> (Max x y) [=] y.
(* End_Tex_Verb *)
Intros.
Apply leEq_imp_eq.
Apply Max_leEq.
Assumption.
Apply leEq_reflexive.
Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma Max_is_rht_imp_leEq : (x,y:IR)((Max x y) [=] y) -> (x [<=] y).
(* End_Tex_Verb *)
Intros.
Unfold leEq.
Intro.
Generalize (less_leEq ? ? ? H0); Intro.
Generalize (leEq_imp_Max_is_rht ? ? H1); Intro.
Cut y[=]x.
Intro.
Elim (less_irreflexive_unfolded ? x).
Step y.
Assumption.
Step (Max x y).
Stepr (Max y x).
Apply Max_comm.
Qed.

(* Begin_Tex_Verb *)
Lemma Max_minus_eps_leEq : (x,y:IR)(e:IR)
  (Zero[<]e)->({((Max x y)[-]e)[<=]x}+{((Max x y)[-]e)[<=]y}).
(* End_Tex_Verb *)
Intros.
Cut (((Max x y)[-]e)[<]x)+(((Max x y)[-]e)[<]y).
Intro; Elim H0; Intros; Clear H0.
Left; Apply less_leEq; Assumption.
Right; Apply less_leEq; Assumption.
Apply less_Max_imp.
Apply shift_minus_less.
Apply shift_less_plus'.
Step (Zero::IR); Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma max_one_ap_zero : (x:IR)(Max x One)[#]Zero.
(* End_Tex_Verb *)
Intros.
Apply ap_symmetric_unfolded.
Apply less_imp_ap.
Apply less_leEq_trans with (One::IR).
Apply pos_one.
Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma pos_max_one : (x:IR)(Zero[<](Max x One)).
(* End_Tex_Verb *)
Intro.
Apply less_leEq_trans with (One::IR); [Apply pos_one | Apply rht_leEq_Max].
Qed.

(* Begin_Tex_Verb *)
Lemma x_div_Max_leEq_x : (x,y:IR)(Zero[<]x)->
  (x[/](Max y One)[//](max_one_ap_zero ?))[<=]x.
(* End_Tex_Verb *)
Intros.
Apply shift_div_leEq'.
Apply pos_max_one.
Step One[*]x.
Apply mult_resp_leEq_rht; [Apply rht_leEq_Max | Apply less_leEq; Assumption].
Qed.

End properties_of_Max.

End Maximum.

Hints Resolve Max_id : algebra.

Section Minimum.

(* Tex_Prose
\subsection{Mininum}

The minimum is defined by the formula $\min(x,y)=-\max(-x,-y)$.
*)

(* Begin_Tex_Verb *)
Definition MIN [x,y:IR] : IR := [--](Max [--]x [--]y).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma min_wd_unfolded : (x,y,a,b:IR)
  (((x[=]a)/\(y[=]b))->
    ([--](Max [--]x [--]y)[=][--](Max [--]a [--]b))).
(* End_Tex_Verb *)
Intros.
Apply un_op_wd_unfolded.
Apply bin_op_wd_unfolded; Apply un_op_wd_unfolded; Elim H; Trivial.
Qed.

(* Begin_Tex_Verb *)
Lemma min_wd : (bin_op_well_def ? MIN).
(* End_Tex_Verb *)
Red.
Red.
Intro.
Unfold MIN.
Intros.
Apply min_wd_unfolded.
Split; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma min_strext_unfolded : (x,y,a,b:IR)
  (([--](Max [--]x [--]y)[#][--](Max [--]a [--]b))->((x[#]a)+(y[#]b))).
(* End_Tex_Verb *)
Intros.
Cut ([--]x[#][--]a)+([--]y[#][--]b).
Intros.
Elim H0.
Intro.
Left; Apply un_op_strext_unfolded with (!cg_inv IR); Assumption.
Intro.
Right; Apply un_op_strext_unfolded with (!cg_inv IR); Assumption.
Apply bin_op_strext_unfolded with Max.
Apply un_op_strext_unfolded with (!cg_inv IR); Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma min_strext : (bin_op_strong_ext ? MIN).
(* End_Tex_Verb *)
Red.
Red.
Unfold MIN.
Intros.
Apply min_strext_unfolded.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Min : (CSetoid_bin_op IR) := 
  (Build_CSetoid_bin_op IR [x,y:IR]([--](Max [--]x [--]y)) min_strext).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Min_leEq_lft : (x,y:IR) (Min x y)[<=]x.
(* End_Tex_Verb *)
Intros.
Unfold Min; Simpl.
RStepr ([--][--]x).
Apply inv_resp_leEq.
Apply lft_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma Min_leEq_rht : (x,y:IR) (Min x y)[<=]y.
(* End_Tex_Verb *)
Intros.
Unfold Min; Simpl.
RStepr [--][--]y.
Apply inv_resp_leEq.
Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma Min_less_imp : (x,y,z:IR)((Min x y)[<]z)->(x[<]z)+(y[<]z).
(* End_Tex_Verb *)
Unfold Min; Simpl.
Intros.
Cut ([--]z[<][--]x)+([--]z[<][--]y).
Intros.
Elim H0; Intro.
Left.
Apply inv_cancel_less; Assumption.
Right.
Apply inv_cancel_less; Assumption.
Apply less_Max_imp.
Apply inv_cancel_less.
Apply less_wdr with z.
Assumption.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_Min : (x,y,z:IR)((z[<=]x)->(z[<=]y)->(z[<=](Min x y))).
(* End_Tex_Verb *)
Intros.
Unfold Min; Simpl.
RStep [--][--]z.
Apply inv_resp_leEq.
Apply Max_leEq; Apply inv_resp_leEq; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma less_Min : (x,y,z:IR)((z[<]x)->(z[<]y)->(z[<](Min x y))).
(* End_Tex_Verb *)
Intros.
Unfold Min; Simpl.
RStep [--][--]z.
Apply inv_resp_less.
Apply Max_less; Apply inv_resp_less; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma equiv_imp_eq_min : (x,x',m:IR)
  ((y:IR)(y[<]x)->(y[<]x')->(y[<]m))->
  ((y:IR)(y[<]m)->(y[<]x))->
  ((y:IR)(y[<]m)->(y[<]x'))->
  (Min x x')[=]m.
(* End_Tex_Verb *)
Intros.
Unfold Min; Simpl.
Stepr [--][--]m.
Apply un_op_wd_unfolded.
Apply equiv_imp_eq_max.
Intros.
RStepr [--][--]y.
Apply inv_resp_less.
Apply H.
RStepr [--][--]x.
Apply inv_resp_less.
Assumption.
RStepr [--][--]x'.
Apply inv_resp_less.
Assumption.
Intros.
RStepr [--][--]y.
Apply inv_resp_less.
Apply H0.
RStepr [--][--]m.
Apply inv_resp_less.
Assumption.
Intros.
RStepr [--][--]y.
Apply inv_resp_less.
Apply H1.
RStepr [--][--]m.
Apply inv_resp_less.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Min_id : (x:IR)((Min x x)[=]x).
(* End_Tex_Verb *)
Intro.
Unfold Min; Simpl.
Stepr [--][--]x.
Apply un_op_wd_unfolded; Apply Max_id.
Qed.

(* Begin_Tex_Verb *)
Lemma Min_comm : (x,y:IR)((Min x y)[=](Min y x)).
(* End_Tex_Verb *)
Intros.
Unfold Min; Simpl.
Apply un_op_wd_unfolded; Apply Max_comm.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_imp_Min_is_lft : (x,y:IR)((x[<=]y)->((Min x y)[=]x)).
(* End_Tex_Verb *)
Intros.
Unfold Min; Simpl.
Stepr [--][--]x.
Apply un_op_wd_unfolded.
Apply eq_transitive_unfolded with (Max [--]y [--]x).
Apply Max_comm.
Apply leEq_imp_Max_is_rht.
Apply inv_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Min_is_lft_imp_leEq : (x,y:IR)(((Min x y)[=]x)->(x[<=]y)).
(* End_Tex_Verb *)
Unfold Min; Simpl.
Intros.
RStep [--][--]x.
RStepr [--][--]y.
Apply inv_resp_leEq.
Apply Max_is_rht_imp_leEq.
Step [--][--](Max [--]y [--]x).
Apply eq_transitive_unfolded with [--][--](Max [--]x [--]y).
Apply un_op_wd_unfolded; Apply un_op_wd_unfolded; Apply Max_comm.
Apply un_op_wd_unfolded; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_Min_plus_eps : (x,y:IR)(e:IR)(Zero[<]e)->
  ({x[<=]((Min x y)[+]e)}+{y[<=]((Min x y)[+]e)}).
(* End_Tex_Verb *)
Intros.
Cut (x[<]((Min x y)[+]e))+(y[<]((Min x y)[+]e)).
Intro; Elim H0; Intros; Clear H0.
Left; Apply less_leEq; Assumption.
Right; Apply less_leEq; Assumption.
Apply Min_less_imp.
Apply shift_less_plus'.
Step (Zero::IR); Assumption.
Qed.

(* Begin_Tex_Verb *)
Variables a,b:IR.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Min_leEq_Max : (Min a b)[<=](Max a b).
(* End_Tex_Verb *)
Intros.
Apply leEq_transitive with a; [Apply Min_leEq_lft | Apply lft_leEq_Max].
Qed.

(* Begin_Tex_Verb *)
Lemma Min_leEq_Max' : (z:IR)(Min a z)[<=](Max b z).
(* End_Tex_Verb *)
Intros; Apply leEq_transitive with z.
Apply Min_leEq_rht.
Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma Min3_leEq_Max3 : (c:IR)(Min (Min a b) c)[<=](Max (Max a b) c).
(* End_Tex_Verb *)
Intros; EApply leEq_transitive.
Apply Min_leEq_rht.
Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma Min_less_Max : (c,d:IR)(a[<]b)->(Min a c)[<](Max b d).
(* End_Tex_Verb *)
Intros.
Apply leEq_less_trans with a.
Apply Min_leEq_lft.
Apply less_leEq_trans with b.
Assumption.
Apply lft_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma ap_imp_Min_less_Max : (a[#]b)->(Min a b)[<](Max a b).
(* End_Tex_Verb *)
Intro Hap; Elim (ap_imp_less ??? Hap); (Intro H;
  [EApply leEq_less_trans; [Idtac | EApply less_leEq_trans; [Apply H | Idtac]]]).
Apply Min_leEq_lft.
Apply rht_leEq_Max.
Apply Min_leEq_rht.
Apply lft_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma Min_less_Max_imp_ap : ((Min a b)[<](Max a b))->a[#]b.
(* End_Tex_Verb *)
Intro.
Elim (Min_less_imp ??? H); Clear H; Intro H; Elim (less_Max_imp ??? H); Intro H0.
ElimType False; Exact (less_irreflexive ?? H0).
Apply less_imp_ap; Auto.
Apply Greater_imp_ap; Auto.
ElimType False; Exact (less_irreflexive ?? H0).
Qed.

End Minimum.

(***********************************)
Section Absolute.
(***********************************)

(* Tex_Prose
\section{Absolute value}
*)

(* Begin_Tex_Verb *)
Definition ABSIR := [x:IR](Max x ([--]x)) : IR -> IR.
(* End_Tex_Verb *)


(* Begin_Tex_Verb *)
Lemma ABSIR_strong_ext : (un_op_strong_ext ? ABSIR).
(* End_Tex_Verb *)
Unfold un_op_strong_ext.
Unfold fun_strong_ext.
Unfold ABSIR.
Intros.
Generalize (csbf_strext ? ? ? Max); Intro.
Unfold bin_fun_strong_ext in H0.
Generalize (H0 ? ? ? ? H); Intro.
Elim H1.
Intro.
Assumption.
Intro H2.
Apply zero_minus_apart.
Generalize (minus_ap_zero ? ? ? H2); Intro.
Generalize (inv_resp_ap_zero ? ? H3); Intro.
Cut x[-]y [=] [--]([--]x[-][--]y).
Intro.
Step [--]([--]x[-][--]y).
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma ABSIR_well_def : (un_op_well_def ? ABSIR).
(* End_Tex_Verb *)
Unfold un_op_well_def.
Apply fun_strong_ext_imp_well_def.
Exact ABSIR_strong_ext.
Qed.

(* Begin_Tex_Verb *)
Definition AbsIR := (Build_CSetoid_un_op ? ABSIR ABSIR_strong_ext)
                 :  (CSetoid_un_op IR).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma AbsIR_wd: (x,y:IR) (x[=]y)->(AbsIR x) [=] (AbsIR y).
(* End_Tex_Verb *)
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Abs_wd_lft_unfolded : (x,y,e:IR)(x[=]y) -> ((AbsIR x)[<]e) ->
((AbsIR y)[<]e).
(* End_Tex_Verb *)
Proof.
Intros.
Apply less_wdl with (AbsIR x).
Assumption.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Abs_wd_rht_unfolded : (x,y,e:IR)(x[=]y) -> (e[<](AbsIR x)) ->
(e[<](AbsIR y)).
(* End_Tex_Verb *)
Proof.
Intros.
Apply less_wdr with (AbsIR x).
Assumption.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIRz_isz :(AbsIR Zero)[=]Zero.
(* End_Tex_Verb *)
Intros. Unfold AbsIR. Simpl. Unfold ABSIR.
Step_final (Max Zero Zero).
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_nonneg : (x:IR)(Zero[<=](AbsIR x)).
(* End_Tex_Verb *)
Intro; Intro.
Cut (Zero[<](Zero::IR)).
Apply less_irreflexive.
Apply less_wdl with (AbsIR x); Auto.
EApply eq_transitive_unfolded.
2: Apply AbsIRz_isz.
Apply AbsIR_wd.
Unfold AbsIR in H; Simpl in H; Unfold ABSIR in H.
Apply leEq_imp_eq; Apply less_leEq.
Apply leEq_less_trans with (Max x [--]x).
Apply lft_leEq_Max.
Assumption.
Apply inv_cancel_less.
Apply leEq_less_trans with (Max x [--]x).
Apply rht_leEq_Max.
Stepr (Zero::IR); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_pos : (x:IR)(x[#]Zero)->Zero[<](AbsIR x).
(* End_Tex_Verb *)
Intros.
Cut (x[<]Zero)+(Zero[<]x).
2: Apply ap_imp_less; Assumption.
Intros.
Unfold AbsIR; Simpl; Unfold ABSIR.
Elim H0.
Intro.
Apply less_leEq_trans with [--]x.
Step [--](Zero::IR).
Apply inv_resp_less.
Assumption.
Apply rht_leEq_Max.
Intro.
Apply less_leEq_trans with x.
Assumption.
Apply lft_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_cancel_ap_zero : (x:IR)(((AbsIR x)[#]Zero)->(x[#]Zero)).
(* End_Tex_Verb *)
Intros.
Apply un_op_strext_unfolded with AbsIR.
Apply ap_well_def_rht_unfolded with (Zero::IR).
Assumption.
Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_resp_ap_zero : (x:IR)(x[#]Zero)->(AbsIR x)[#]Zero.
(* End_Tex_Verb *)
Intros.
Apply ap_symmetric_unfolded; Apply less_imp_ap.
Apply AbsIR_pos; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_AbsIR : (x:IR)(x[<=](AbsIR x)).
(* End_Tex_Verb *)
Intros.
Unfold AbsIR; Simpl; Unfold ABSIR; Apply lft_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_leEq_AbsIR : (x:IR)([--]x[<=](AbsIR x)).
(* End_Tex_Verb *)
Intros.
Unfold AbsIR; Simpl; Unfold ABSIR; Apply rht_leEq_Max.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_e : (e:IR)(x:IR)(AbsSmall e x)->(Zero[<=]e).
(* End_Tex_Verb *)
Intros.
Red in H.
Cut [--]e[<=]e.
2: Inversion_clear H; Apply leEq_transitive with x; Assumption.
Intro.
Apply mult_cancel_leEq with (Two::IR); Step (Zero::IR).
Apply pos_two.
RStepr e[+]e.
Apply shift_leEq_plus; Step [--]e.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_imp_AbsIR : (x,y:IR) (AbsSmall y x)->((AbsIR x)[<=]y).
(* End_Tex_Verb *)
Intros.
Unfold AbsIR; Simpl; Unfold ABSIR.
Inversion_clear H.
Apply Max_leEq.
Assumption.
Apply inv_cancel_leEq.
Stepr x; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_eq_AbsSmall :(x,e:IR)([--]e [<=] x) -> (x [<=] e) ->
	(AbsSmall e x).
(* End_Tex_Verb *)
Intros.
Unfold AbsSmall.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_imp_AbsSmall : (x,y:IR) ((AbsIR x)[<=]y)->(AbsSmall y x).
(* End_Tex_Verb *)
Intros.
Unfold AbsSmall.
Simpl in H.
Unfold ABSIR in H.
Simpl in H.
Split.
Generalize (rht_leEq_Max x [--]x).
Intro H1.
Generalize (leEq_transitive ? ? (MAX x [--]x) ? H1 H).
Intro H2.
RStepr [--][--]x.
Apply inv_resp_leEq.
Assumption.
Generalize (lft_leEq_Max x [--]x).
Intro H1.
Generalize (leEq_transitive ? ? (MAX x [--]x) ? H1 H).
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsSmall_transitive : (e:IR)(x,y:IR)(AbsSmall e x)->
  ((AbsIR y)[<=](AbsIR x))->(AbsSmall e y).
(* End_Tex_Verb *)
Intros.
Apply AbsIR_imp_AbsSmall.
EApply leEq_transitive.
Apply H0.
Apply AbsSmall_imp_AbsIR; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma zero_less_AbsIR_plus_one : (q:IR)(Zero[<](AbsIR q)[+]One).
(* End_Tex_Verb *)
Intros.
Apply less_leEq_trans with (Zero[+](One::IR)).
RStepr (One::IR); Apply pos_one.
Apply plus_resp_leEq; Apply AbsIR_nonneg.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_inv : (x:IR)(AbsIR x)[=](AbsIR [--]x).
(* End_Tex_Verb *)
Intros.
Unfold AbsIR; Simpl; Unfold ABSIR.
Apply eq_transitive_unfolded with (Max [--][--]x [--]x).
Apply bin_op_wd_unfolded; Algebra.
Apply Max_comm.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_minus : (x,y:IR)(AbsIR x[-]y)[=](AbsIR y[-]x).
(* End_Tex_Verb *)
Intros.
EApply eq_transitive_unfolded.
Apply AbsIR_inv.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_eq_x : (x:IR)(Zero[<=]x)->(AbsIR x)[=]x.
(* End_Tex_Verb *)
Intros.
Unfold AbsIR; Simpl; Unfold ABSIR.
Apply eq_transitive_unfolded with (Max [--]x x).
Apply Max_comm.
Apply leEq_imp_Max_is_rht.
Apply leEq_transitive with (Zero::IR).
2: Assumption.
Stepr [--](Zero::IR).
Apply inv_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_eq_inv_x : (x:IR)(x[<=]Zero)->(AbsIR x)[=][--]x.
(* End_Tex_Verb *)
Intros.
Apply eq_transitive_unfolded with (AbsIR [--]x).
Apply AbsIR_inv.
Apply AbsIR_eq_x.
Step [--](Zero::IR).
Apply inv_resp_leEq.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma less_AbsIR : (x,y:IR)(Zero[<]x)->(x[<](AbsIR y))->((x[<]y)+(y[<][--]x)).
(* End_Tex_Verb *)
Intros.
Simpl in H0.
Unfold ABSIR in H0.
Cut (x[<]y)+(x[<][--]y).
Intro; Inversion_clear H1.
Left; Assumption.
Right; Step [--][--]y; Apply inv_resp_less; Assumption.
Apply less_Max_imp; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma leEq_distr_AbsIR : (x,y:IR)(Zero[<]x)->
  (x[<=](AbsIR y))->{x[<=]y}+{y[<=][--]x}.
(* End_Tex_Verb *)
Intros.
Cut x[*](Three[/]FourNZ)[<](AbsIR y); Intros.
Elim (less_AbsIR x[*](Three[/]FourNZ) y); Intros; [Left | Right | Idtac | Auto].
Stepr Zero[+]y; Apply shift_leEq_plus.
Red; Apply approach_zero.
Cut (e:IR)(Zero[<]e)->(e[<]x[/]TwoNZ)->(x[-]y)[<]e; Intros.
Cut x[/]FourNZ[<]x[/]TwoNZ; Intros.
2: RStep (x[/]TwoNZ)[/]TwoNZ; Apply pos_div_two'; Apply pos_div_two; Auto.
Elim (cotrans_less_unfolded ??? H4 e); Intro.
Apply leEq_less_trans with x[/]FourNZ; Auto.
Apply less_leEq.
Apply shift_minus_less; Apply shift_less_plus'.
RStep x[*](Three[/]FourNZ); Auto.
Apply H2; Auto.
Apply shift_minus_less; Apply shift_less_plus'.
Cut x[-]e[<](AbsIR y); Intros.
2: Apply less_leEq_trans with x; Auto.
2: Apply shift_minus_less; Apply shift_less_plus'; Step (Zero::IR); Auto.
Elim (less_AbsIR x[-]e y); Auto.
Intro; ElimType False.
Apply (less_irreflexive_unfolded ? y).
EApply leEq_less_trans.
2: Apply a.
Apply less_leEq; EApply less_transitive_unfolded.
Apply b.
Step Zero[-](x[-]e).
Apply shift_minus_less.
Stepr (x[*](Three[/]FourNZ)[+]x)[-]e.
Apply shift_less_minus; Step e.
EApply less_leEq_trans.
Apply H3.
Apply less_leEq.
RStep x[*](Zero[+]Zero[+]One[/]TwoNZ); RStepr x[*](One[+]One[/]FourNZ[+]One[/]TwoNZ).
Apply mult_resp_less_lft; Auto.
Apply plus_resp_less_rht; Apply plus_resp_less_leEq.
Apply pos_one.
Apply less_leEq; Apply pos_div_four; Apply pos_one.
Apply shift_less_minus; Step e.
EApply less_leEq_trans.
Apply H3.
Apply less_leEq; Apply pos_div_two'; Auto.
Stepr Zero[+][--]x; Apply shift_leEq_plus.
Apply leEq_wdl with y[+]x.
2: Unfold cg_minus; Algebra.
Red; Apply approach_zero.
Cut (e:IR)(Zero[<]e)->(e[<]x[/]TwoNZ)->(y[+]x)[<]e; Intros.
Cut x[/]FourNZ[<]x[/]TwoNZ; Intros.
2: RStep (x[/]TwoNZ)[/]TwoNZ; Apply pos_div_two'; Apply pos_div_two; Auto.
Elim (cotrans_less_unfolded ??? H4 e); Intro.
Apply leEq_less_trans with x[/]FourNZ; Auto.
Apply less_leEq; Apply shift_plus_less.
RStepr [--](x[*](Three[/]FourNZ)); Auto.
Apply H2; Auto.
Cut x[-]e[<](AbsIR y); Intros.
2: Apply less_leEq_trans with x; Auto.
2: Apply shift_minus_less; Apply shift_less_plus'; Step (Zero::IR); Auto.
Elim (less_AbsIR x[-]e y); Auto.
Intro; ElimType False.
Apply (less_irreflexive_unfolded ? y).
EApply leEq_less_trans.
2: Apply a.
Apply less_leEq; EApply less_transitive_unfolded.
Apply b.
Apply shift_less_minus; Apply shift_plus_less'.
EApply less_transitive_unfolded.
Apply H3.
RStep x[*](Zero[+]Zero[+]One[/]TwoNZ); RStepr x[*](One[+]One[/]FourNZ[+]One[/]TwoNZ).
Apply mult_resp_less_lft; Auto.
Apply plus_resp_less_rht; Apply plus_resp_less_leEq.
Apply pos_one.
Apply less_leEq; Apply pos_div_four; Apply pos_one.
Intro.
RStep y[-][--]x.
Apply shift_minus_less.
RStepr [--](x[-]e); Auto.
Apply shift_less_minus; Step e.
EApply less_leEq_trans.
Apply H3.
Apply less_leEq; Apply pos_div_two'; Auto.
Step (Zero::IR)[*](Three[/]FourNZ).
Apply mult_resp_less; Auto.
Apply pos_div_four; Apply pos_three.
Apply less_leEq_trans with x; Auto.
Stepr x[*]One.
Stepr x[*](Four[/]FourNZ).
Apply mult_resp_less_lft; Auto.
Apply div_resp_less.
Apply pos_four.
Apply three_less_four.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_approach_zero : (x:IR)((e:IR)(Zero[<]e)->(AbsIR x)[<=]e)->x[=]Zero.
(* End_Tex_Verb *)
Intros.
Apply leEq_imp_eq.
Red; Apply approach_zero_weak.
Intros.
EApply leEq_transitive; [Apply leEq_AbsIR | Exact (H e H0)].
Step [--](Zero::IR); Stepr [--][--]x; Apply inv_resp_leEq.
Red; Apply approach_zero_weak.
Intros.
EApply leEq_transitive; [Apply inv_leEq_AbsIR | Exact (H e H0)].
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_eq_zero : (x:IR)((AbsIR x)[=]Zero)->(x[=]Zero).
(* End_Tex_Verb *)
Intros.
Apply AbsIR_approach_zero; Intros.
Step (Zero::IR); Apply less_leEq; Auto.
Qed.
(* Begin_Tex_Verb *)

Lemma Abs_Max : (a,b:IR)(AbsIR a[-]b)[=](Max a b)[-](Min a b).
(* End_Tex_Verb *)
Intros.
Apply leEq_imp_eq.
Apply leEq_wdl with (Max a[-]b b[-]a).
2: Simpl; Unfold ABSIR.
2: Apply max_wd_unfolded; Rational.
Apply Max_leEq.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply lft_leEq_Max.
Apply inv_resp_leEq; Apply Min_leEq_rht.
Unfold cg_minus; Apply plus_resp_leEq_both.
Apply rht_leEq_Max.
Apply inv_resp_leEq; Apply Min_leEq_lft.
Stepr Zero[+](AbsIR a[-]b).
Apply shift_leEq_plus.
Red; Apply approach_zero_weak.
Intros.
Do 2 Apply shift_minus_leEq.
EApply leEq_wdr.
2: Apply plus_assoc.
Apply shift_leEq_plus'.
Elim (Max_minus_eps_leEq a b e H); Intro.
Apply leEq_transitive with a.
Assumption.
Apply shift_leEq_plus'.
Apply leEq_Min.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply AbsIR_nonneg.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Apply leEq_AbsIR.
Apply leEq_transitive with b.
Assumption.
Apply shift_leEq_plus'.
Apply leEq_Min.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
RStep [--](a[-]b); Apply inv_leEq_AbsIR.
Apply shift_minus_leEq; Apply shift_leEq_plus'.
Step (Zero::IR); Apply AbsIR_nonneg.
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_str_bnd : (a,b,e:IR)
  ((AbsIR a[-]b)[<]e)->(b[<]a[+]e).
(* End_Tex_Verb *)
Intros.
Apply shift_less_plus'.
Apply leEq_less_trans with (AbsIR a[-]b); Auto.
EApply leEq_wdr; [Apply leEq_AbsIR | Apply AbsIR_minus].
Qed.

(* Begin_Tex_Verb *)
Lemma AbsIR_bnd : (a,b,e:IR)
  ((AbsIR a[-]b)[<=]e)->(b[<=]a[+]e).
(* End_Tex_Verb *)
Intros.
Apply shift_leEq_plus'.
Apply leEq_transitive with (AbsIR a[-]b); Auto.
EApply leEq_wdr; [Apply leEq_AbsIR | Apply AbsIR_minus].
Qed.

End Absolute.

Hints Resolve AbsIRz_isz : algebra.

Section Part_Function_Abs.

(* Tex_Prose
\subsection{Functional Operators}

The existence of these operators allows us to lift them to functions.  We will only define the absolute value, but maximum and minimum of two partial functions could easily be similarly defined.

\begin{notation} \verb!(PartFunct IR}! is denoted by {\tt\hypertarget{Syntactic_33}{PartIR}}.

On predicates, {\tt\hypertarget{Syntactic_34}{ProjIR1}} and {\tt\hypertarget{Syntactic_35}{ProjIR2}} will denote the first and second projections of a conjunction.
\end{notation}

\begin{convention} Let \verb!F:PartIR! and denote by \verb!P! its domain.
\end{convention}
*)

Variables F,G:(PartFunct IR).

Local P := (Pred F).

(* Begin_Tex_Verb *)
Lemma part_function_AbsIR_strext : (x,y:IR)(Hx,Hy:?)
  (((AbsIR (F x Hx))[#](AbsIR (F y Hy)))->(x[#]y)).
(* End_Tex_Verb *)
Intros.
Apply pfstrx with F Hx Hy.
Apply un_op_strext_unfolded with AbsIR.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition FAbs := (Build_PartFunct IR ? 
  (pfprwd ??)
  [x:IR][Hx:(P x)](AbsIR (F x Hx)) 
  part_function_AbsIR_strext).
(* End_Tex_Verb *)

End Part_Function_Abs.
