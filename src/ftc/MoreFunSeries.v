(* $Id: MoreFunSeries.v,v 1.16 2003/03/13 12:06:20 lcf Exp $ *)

Require Export FunctSeries.
Require Export MoreFunctions.

Section Definitions.

(* Tex_Prose
\chapter{More on Sequences and Series}

We will now extend our convergence definitions and results for sequences and series of functions defined in compact intervals to arbitrary intervals.

\begin{convention} Throughout this file, \verb!J! will be an interval, \verb!f,g! will be sequences of continuous (in \verb!J!) functions and \verb!F,G! will be continuous (in \verb!J!) functions.
\end{convention}

\section{Sequences}

First we will consider the case of sequences.

\subsection{Definitions}

Some of the definitions do not make sense in this more general setting (for instance, because the norm of a function is no longer defined), but the ones which do we simply adapt in the usual way.
*)

Variable J:interval.
Variable f:nat->PartIR.
Variable F:PartIR.

Hypothesis contf:(n:nat)(Continuous J (f n)).
Hypothesis contF:(Continuous J F).

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq_IR :=
  (a,b:IR)(Hab:a[<=]b)(Hinc:(included (Compact Hab) (iprop J)))
  (Cauchy_fun_seq a b Hab f
    [n:nat](included_imp_Continuous ?? (contf n) ??? Hinc)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition conv_fun_seq_IR :=
  (a,b:IR)(Hab:a[<=]b)(Hinc:(included (Compact Hab) (iprop J)))
  (conv_fun_seq a b Hab f
    [n:nat](included_imp_Continuous ?? (contf n) ??? Hinc)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition conv_fun_seq'_IR :=
  (a,b:IR)(Hab:a[<=]b)(Hinc:(included (Compact Hab) (iprop J)))
  (conv_fun_seq' a b Hab f F
    [n:nat](included_imp_Continuous ?? (contf n) ??? Hinc)
    (included_imp_Continuous ?? contF ??? Hinc)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq2_IR :=
  (a,b:IR)(Hab:a[<=]b)(Hinc:(included (Compact Hab) (iprop J)))
  (Cauchy_fun_seq2 a b Hab f
    [n:nat](included_imp_Continuous ?? (contf n) ??? Hinc)).
(* End_Tex_Verb *)

(* Tex_Prose
The equivalences between these definitions still hold.
*)

(* Begin_Tex_Verb *)
Lemma conv_Cauchy_fun_seq'_IR :
  conv_fun_seq'_IR->Cauchy_fun_seq_IR.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros.
Apply conv_Cauchy_fun_seq' with F (included_imp_Continuous ?? contF ??? Hinc); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq_seq2_IR :
  Cauchy_fun_seq_IR->Cauchy_fun_seq2_IR.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros.
Apply Cauchy_fun_seq_seq2; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq2_seq_IR :
  Cauchy_fun_seq2_IR->Cauchy_fun_seq_IR.
(* End_Tex_Verb *)
Intro.
Red; Red in H.
Intros.
Apply Cauchy_fun_seq2_seq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_real_IR : Cauchy_fun_seq_IR->(x,Hx:?)
  (Cauchy_prop [n:nat](pfpfun ? ? (Continuous_imp_inc ?? (contf n) x Hx))).
(* End_Tex_Verb *)
Intros.
Red in H.
Cut (included (compact_single x) (iprop J)); Intros.
LetTac contf':=[i:nat](included_imp_Continuous J (f i) (contf i) ?? (leEq_reflexive ? x) H0).
Apply Cauchy_prop_wd with 
  [n:nat](Part (f n) x ([i:nat](contin_imp_inc ?? (leEq_reflexive ? x) (f i) (contf' i)) n x (compact_single_prop x))).
Apply Cauchy_fun_real.
Unfold contf'; Simpl; Apply H.
Intro; Simpl; Algebra.
Apply compact_single_iprop; Auto.
Qed.

End Definitions.

Section More_Definitions.

(* Tex_Prose
Limit is defined and works in the same way as before.
*)

Variable J:interval.
Variable f:nat->PartIR.

Hypothesis contf:(n:nat)(Continuous J (f n)).
(* Begin_Tex_Verb *)
Hypothesis conv : (Cauchy_fun_seq_IR J f contf).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Cauchy_fun_seq_Lim_IR : PartIR.
(* End_Tex_Verb *)
Apply Build_PartFunct with 
  pfpfun:=[x:IR][Hx:(iprop J x)](Lim (Build_CauchySeq ?? (Cauchy_fun_real_IR ??? conv x Hx))).
Apply iprop_wd.
Intros.
Elim (Lim_strext ?? H).
Intros n Hn.
Simpl in Hn.
Exact (pfstrx ?????? Hn).
Defined.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq_Lim_char : 
  (a,b:IR)(Hab:a[<=]b)(Hinc:(included (Compact Hab) (iprop J)))
  (Feq (Compact Hab)
       Cauchy_fun_seq_Lim_IR
       (Cauchy_fun_seq_Lim ????? (conv a b Hab Hinc))).
(* End_Tex_Verb *)
Intros.
FEQ.
Simpl.
Apply Lim_wd'; Intros; Simpl; Algebra.
Qed.

End More_Definitions.

Section Irrelevance_of_Proofs.

(* Tex_Prose
\subsection{Basic Properties}

Proofs are irrelevant as before---they just have to be present.
*)

Variable J:interval.
Variable f:nat->PartIR.
(* Begin_Tex_Verb *)
Hypothesis contf,contf0:(n:nat)(Continuous J (f n)).
(* End_Tex_Verb *)

Variable F:PartIR.
(* Begin_Tex_Verb *)
Hypothesis contF,contF0:(Continuous J F).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wd_IR : (conv_fun_seq'_IR ??? contf contF)->
  (conv_fun_seq'_IR ??? contf0 contF0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
EApply conv_fun_seq'_wd.
Apply (H a b Hab Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq2_wd_IR : (Cauchy_fun_seq2_IR ?? contf)->
  (Cauchy_fun_seq2_IR ?? contf0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
EApply Cauchy_fun_seq2_wd.
Apply (H a b Hab Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq_wd_IR : (conv_fun_seq_IR ?? contf)->
  (conv_fun_seq_IR ?? contf0).
(* End_Tex_Verb *)
Intro.
Red; Intros.
EApply conv_fun_seq_wd.
Apply (H a b Hab Hinc).
Qed.

End Irrelevance_of_Proofs.

Opaque Cauchy_fun_seq_Lim_IR.

Section More_Properties.

Variable J:interval.
Variables f,g:nat->PartIR.

(* Begin_Tex_Verb *)
Hypothesis contf,contf0:(n:nat)(Continuous J (f n)).
Hypothesis contg,contg0:(n:nat)(Continuous J (g n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Cauchy_conv_fun_seq'_IR :
  (H:(Cauchy_fun_seq_IR ?? contf))
  (contf':(Continuous J (Cauchy_fun_seq_Lim_IR ??? H)))
    (conv_fun_seq'_IR ??? contf contf').
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply conv_fun_seq'_wdr.
Apply Feq_symmetric.
Apply (Cauchy_fun_seq_Lim_char J f contf H a b Hab Hinc).
Apply Cauchy_conv_fun_seq' with H:=(H a b Hab Hinc) contf':=(Cauchy_cont_Lim ????? (H a b Hab Hinc)).
Qed.

Variables F,G:PartIR.
(* Begin_Tex_Verb *)
Hypothesis contF,contF0:(Continuous J F).
Hypothesis contG,contG0:(Continuous J G).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdl_IR :
  ((n:nat)(Feq (iprop J) (f n) (g n)))->
  (conv_fun_seq'_IR ??? contf contF)->
  (conv_fun_seq'_IR ??? contg contF0).
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply conv_fun_seq'_wdl with f:=f.
2: Apply (H0 a b Hab Hinc).
Intro; Elim (H n); Intros.
Inversion_clear a0.
Apply eq_imp_Feq; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdr_IR : (Feq (iprop J) F G)->
  (conv_fun_seq'_IR ??? contf contF)->
  (conv_fun_seq'_IR ??? contf0 contG).
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply conv_fun_seq'_wdr with F:=F.
2: Apply (H0 a b Hab Hinc).
Apply included_Feq with (iprop J); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdl'_IR :
  ((n:nat)(Feq (iprop J) (f n) (g n)))->
  (conv_fun_seq'_IR ??? contf contF)->
  (conv_fun_seq'_IR ??? contg contF).
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply conv_fun_seq'_wdl' with f:=f; Auto.
Intro; Elim (H n); Intros.
Inversion_clear a0.
Apply eq_imp_Feq; Included.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_fun_seq'_wdr'_IR : (Feq (iprop J) F G)->
  (conv_fun_seq'_IR ??? contf contF)->
  (conv_fun_seq'_IR ??? contf contG).
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply conv_fun_seq'_wdr' with F:=F.
2: Apply (H0 a b Hab Hinc).
Apply included_Feq with (iprop J); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_cont_Lim_IR : (H:(Cauchy_fun_seq_IR ?? contf))
  (Continuous J (Cauchy_fun_seq_Lim_IR ?? contf H)).
(* End_Tex_Verb *)
Intros.
Split; Included.
Intros; EApply Continuous_I_wd.
Apply Feq_symmetric.
Apply (Cauchy_fun_seq_Lim_char J f contf H a b Hab H0).
Contin.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_conv_fun_seq_IR :
  (Cauchy_fun_seq_IR ?? contf)->(conv_fun_seq_IR ?? contf).
(* End_Tex_Verb *)
Intro.
Red; Intros.
EApply Cauchy_conv_fun_seq.
Apply (H a b Hab Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma conv_Cauchy_fun_seq_IR :
  (conv_fun_seq_IR ?? contf)->(Cauchy_fun_seq_IR ?? contf).
(* End_Tex_Verb *)
Intro.
Red; Intros.
EApply conv_Cauchy_fun_seq.
Apply (H a b Hab Hinc).
Qed.

End More_Properties.

Hints Resolve Cauchy_cont_Lim_IR : continuous.

Section Algebraic_Properties.

(* Tex_Prose
\subsection{Algebraic Properties}

Algebraic operations still work well.
*)

Variable J:interval.
Variables f,g:nat->PartIR.

Hypothesis contf:(n:nat)(Continuous J (f n)).
Hypothesis contg:(n:nat)(Continuous J (g n)).

(* Begin_Tex_Verb *)
Lemma FLim_unique_IR : (F,G,HF,HG:?)
  (conv_fun_seq'_IR J f F contf HF)->
  (conv_fun_seq'_IR J f G contf HG)->(Feq (iprop J) F G).
(* End_Tex_Verb *)
Intros.
Apply included_Feq'.
Intros.
Apply FLim_unique with f [n:nat](included_imp_Continuous ?? (contf n) ??? H1) 
  (included_imp_Continuous ?? HF ??? H1) (included_imp_Continuous ?? HG ??? H1); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cauchy_fun_seq_wd_IR :
  ((n:nat)(Feq (iprop J) (f n) (g n)))->
  (Cauchy_fun_seq_IR ?? contf)->(Cauchy_fun_seq_IR ?? contg).
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply Cauchy_fun_seq_wd with f:=f.
2: Apply (H0 a b Hab Hinc).
Intro; Apply included_Feq with (iprop J); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_const_IR : (H:PartIR)(contH,contH':?)
  (conv_fun_seq'_IR J [n:nat]H H contH contH').
(* End_Tex_Verb *)
Exists O; Intros.
EApply leEq_wdl.
2: EApply eq_transitive_unfolded.
2: Apply eq_symmetric_unfolded; Apply AbsIRz_isz.
Apply less_leEq; Assumption.
Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_const_IR : (H:PartIR)(contH:?)
  (Cauchy_fun_seq_IR J [n:nat]H contH).
(* End_Tex_Verb *)
Intros.
Apply conv_Cauchy_fun_seq'_IR with H (contH O).
Apply fun_Lim_seq_const_IR.
Qed.

Variables F,G:PartIR.
Hypothesis contF:(Continuous J F).
Hypothesis contG:(Continuous J G).

(* Begin_Tex_Verb *)
Hypothesis convF:(conv_fun_seq'_IR ??? contf contF).
Hypothesis convG:(conv_fun_seq'_IR ??? contg contG).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_plus'_IR : (H,H':?)
  (conv_fun_seq'_IR J [n:nat](f n){+}(g n) F{+}G H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply fun_Lim_seq_plus'.
Apply (convF a b Hab Hinc).
Apply (convG a b Hab Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_minus'_IR : (H,H':?)
  (conv_fun_seq'_IR J [n:nat](f n){-}(g n) F{-}G H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply fun_Lim_seq_minus'.
Apply (convF a b Hab Hinc).
Apply (convG a b Hab Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_mult'_IR : (H,H':?)
  (conv_fun_seq'_IR J [n:nat](f n){*}(g n) F{*}G H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
EApply fun_Lim_seq_mult'.
Apply (convF a b Hab Hinc).
Apply (convG a b Hab Hinc).
Qed.

End Algebraic_Properties.

Section More_Algebraic_Properties.

(* Tex_Prose
If we work with the Limit function things fit in just as well.
*)

Variable J:interval.
Variables f,g:nat->PartIR.

Hypothesis contf:(n:nat)(Continuous J (f n)).
Hypothesis contg:(n:nat)(Continuous J (g n)).

(* Begin_Tex_Verb *)
Hypothesis Hf:(Cauchy_fun_seq_IR ?? contf).
Hypothesis Hg:(Cauchy_fun_seq_IR ?? contg).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_plus_IR : (H,H':?)
  (conv_fun_seq'_IR J [n:nat](f n){+}(g n)
    (Cauchy_fun_seq_Lim_IR ??? Hf){+}
      (Cauchy_fun_seq_Lim_IR ??? Hg) H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (Hf a b Hab Hinc))); [Intro | Contin].
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (Hg a b Hab Hinc))); [Intro | Contin].
EApply conv_fun_seq'_wdr with
  contF:=(Continuous_I_plus ????? H0 H1).
Apply Feq_symmetric; Apply Feq_plus; Apply Cauchy_fun_seq_Lim_char.
Apply fun_Lim_seq_plus with Hf:=(Hf a b Hab Hinc) Hg:=(Hg a b Hab Hinc) H:=[n:nat](included_imp_Continuous ?? (H n) ??? Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_plus :
  (H:?)(Cauchy_fun_seq_IR J [n:nat](f n){+}(g n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous J (Cauchy_fun_seq_Lim_IR ??? Hf){+}(Cauchy_fun_seq_Lim_IR ??? Hg)); [Intro | Contin].
Apply conv_Cauchy_fun_seq'_IR with (Cauchy_fun_seq_Lim_IR ??? Hf){+}(Cauchy_fun_seq_Lim_IR ??? Hg) H0.
Apply fun_Lim_seq_plus_IR.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_inv_IR : (H,H':?)
  (conv_fun_seq'_IR J [n:nat]{--}(f n)
    {--}(Cauchy_fun_seq_Lim_IR ??? Hf) H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (Hf a b Hab Hinc))); [Intro | Contin].
Intros.
EApply conv_fun_seq'_wdr with contF:=(Continuous_I_inv ???? H0).
Apply Feq_symmetric; Apply Feq_inv; Apply Cauchy_fun_seq_Lim_char.
Apply fun_Lim_seq_inv with Hf:=(Hf a b Hab Hinc) H:=[n:nat](included_imp_Continuous ?? (H n) ??? Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_inv :
  (H:?)(Cauchy_fun_seq_IR J [n:nat]{--}(f n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous J ({--}(Cauchy_fun_seq_Lim_IR ??? Hf))); [Intro | Contin].
Apply conv_Cauchy_fun_seq'_IR with ({--}(Cauchy_fun_seq_Lim_IR ??? Hf)) H0.
Apply fun_Lim_seq_inv_IR.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_minus_IR : (H,H':?)
  (conv_fun_seq'_IR J [n:nat](f n){-}(g n)
    (Cauchy_fun_seq_Lim_IR ??? Hf){-}
      (Cauchy_fun_seq_Lim_IR ??? Hg) H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (Hf a b Hab Hinc))); [Intro | Contin].
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (Hg a b Hab Hinc))); [Intro | Contin].
Intros.
EApply conv_fun_seq'_wdr with
  contF:=(Continuous_I_minus ????? H0 H1).
Apply Feq_symmetric; Apply Feq_minus; Apply Cauchy_fun_seq_Lim_char.
Apply fun_Lim_seq_minus with Hf:=(Hf a b Hab Hinc) Hg:=(Hg a b Hab Hinc) H:=[n:nat](included_imp_Continuous ?? (H n) ??? Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_minus :
  (H:?)(Cauchy_fun_seq_IR J [n:nat](f n){-}(g n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous J (Cauchy_fun_seq_Lim_IR ??? Hf){-}(Cauchy_fun_seq_Lim_IR ??? Hg)); [Intro | Contin].
Apply conv_Cauchy_fun_seq'_IR with (Cauchy_fun_seq_Lim_IR ??? Hf){-}(Cauchy_fun_seq_Lim_IR ??? Hg) H0.
Apply fun_Lim_seq_minus_IR.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Lim_seq_mult_IR : (H,H':?)
  (conv_fun_seq'_IR J [n:nat](f n){*}(g n)
    (Cauchy_fun_seq_Lim_IR ??? Hf){*}
      (Cauchy_fun_seq_Lim_IR ??? Hg) H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (Hf a b Hab Hinc))); [Intro | Contin].
Cut (Continuous_I Hab (Cauchy_fun_seq_Lim ????? (Hg a b Hab Hinc))); [Intro | Contin].
Intros.
EApply conv_fun_seq'_wdr with
  contF:=(Continuous_I_mult ????? H0 H1).
Apply Feq_symmetric; Apply Feq_mult; Apply Cauchy_fun_seq_Lim_char.
Apply fun_Lim_seq_mult with Hf:=(Hf a b Hab Hinc) Hg:=(Hg a b Hab Hinc) H:=[n:nat](included_imp_Continuous ?? (H n) ??? Hinc).
Qed.

(* Begin_Tex_Verb *)
Lemma fun_Cauchy_prop_mult :
  (H:?)(Cauchy_fun_seq_IR J [n:nat](f n){*}(g n) H).
(* End_Tex_Verb *)
Intro.
Cut (Continuous J (Cauchy_fun_seq_Lim_IR ??? Hf){*}(Cauchy_fun_seq_Lim_IR ??? Hg)); [Intro | Contin].
Apply conv_Cauchy_fun_seq'_IR with (Cauchy_fun_seq_Lim_IR ??? Hf){*}(Cauchy_fun_seq_Lim_IR ??? Hg) H0.
Apply fun_Lim_seq_mult_IR.
Qed.

End More_Algebraic_Properties.

Section Other.

(* Tex_Prose
\subsection{Miscellaneous}

Finally, we define a mapping between sequences of real numbers and sequences of (constant) functions and prove that convergence is preserved.
*)

(* Begin_Tex_Verb *)
Definition seq_to_funseq [x:nat->IR] : nat->PartIR :=
  [n:nat]{-C-}(x n).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma funseq_conv : (J,x,y:?)(nonvoid J)->
  (conv_fun_seq'_IR J (seq_to_funseq x) {-C-}y
    [n:nat](Continuous_const ??) (Continuous_const ??))->
  (Cauchy_Lim_prop2 x y).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (nonvoid_point J H); Intros x0 Hx0.
Cut (included (compact_single x0) (iprop J)).
2: Apply compact_single_iprop; Auto.
Intro.
Elim (H0 ?? (leEq_reflexive ??) H2 eps).
Intros N HN.
Exists N; Intros.
Simpl in HN.
Apply AbsIR_imp_AbsSmall.
Apply HN with x0.
Auto.
Fold (compact_single x0).
Apply compact_single_prop.
Auto.
Qed.

(* Tex_Prose
Another interesting fact: if a sequence of constant functions converges then it must converge to a constant function.
*)

(* Begin_Tex_Verb *)
Lemma fun_const_Lim : (J,f,F,contf,contF:?)(proper J)->
  (conv_fun_seq'_IR J f F contf contF)->
  ((n:nat){c:IR & (Feq (iprop J) (f n) {-C-}c)})->
  {c:IR & (Feq (iprop J) F {-C-}c)}.
(* End_Tex_Verb *)
Intros J f F contf contF pJ; Intros.
LetTac incF:=(Continuous_imp_inc ?? contF).
LetTac incf:=[n:nat](Continuous_imp_inc ?? (contf n)).
Elim (nonvoid_point ? (proper_nonvoid ? pJ)); Intros x0 Hx0.
Exists (Part F x0 (incF x0 Hx0)).
FEQ.
Simpl.
Apply cg_inv_unique_2; Apply AbsIR_approach_zero.
Intros.
Cut (included (Compact (Min_leEq_Max x x0)) (iprop J)).
2: Apply included_interval; Auto.
Intro Hinc.
Elim (H ??? Hinc ? (pos_div_two ?? H2)); Intros N HN.
LetTac Fx:=(pfpfun ? ? Hx).
LetTac Fa:=(pfpfun ? ? (incF x0 Hx0)).
LetTac fx:=(pfpfun ? ? (incf N x H1)).
LetTac fa:=(pfpfun ? ? (incf N x0 Hx0)).
Apply leEq_wdl with (AbsIR (Fx[-]fx)[+](fx[-]fa)[+](fa[-]Fa)).
2: Apply AbsIR_wd; Rational.
RStepr e[/]TwoNZ[+]Zero[+]e[/]TwoNZ.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_transitive.
Apply triangle_IR.
Apply plus_resp_leEq_both.
EApply leEq_wdl.
2: Apply AbsIR_minus.
EApply leEq_wdl.
Apply (HN N (le_n N) x (compact_Min_lft ???)).
Unfold Fx fx; Apply AbsIR_wd; Rational.
Elim (H0 N); Intros c Hc.
Apply eq_imp_leEq.
EApply eq_transitive_unfolded.
2: Apply AbsIRz_isz.
Inversion_clear Hc.
Inversion_clear H3.
Apply AbsIR_wd; Unfold fx fa; Stepr c[-]c.
Apply cg_minus_wd; Simpl in H4; Apply H4; Auto.
EApply leEq_wdl.
Apply (HN N (le_n N) x0 (compact_Min_rht ???)).
Unfold Fa fa; Apply AbsIR_wd; Rational.
Qed.

End Other.

Section Series_Definitions.

(* Tex_Prose
\section{Series}

We now consider series of functions defined in arbitrary intervals.

\subsection{Definitions}

Convergence is defined as expected---through convergence in every compact interval.
*)

Variable J:interval.
Variable f:nat->PartIR.

(* Begin_Tex_Verb *)
Definition fun_series_convergent_IR :=
  (a,b:IR)(Hab:a[<=]b)(Hinc:(included (Compact Hab) (iprop J)))
  (fun_series_convergent a b Hab f).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_series_conv_imp_conv_IR :
  fun_series_convergent_IR->(x:IR)(iprop J x)->(Hx:?)
   (convergent [n:nat]((f n) x (Hx n))).
(* End_Tex_Verb *)
Intros.
Apply fun_series_conv_imp_conv with Hab:=(leEq_reflexive ? x).
Apply H.
Fold (compact_single x); Apply compact_single_iprop; Auto.
Apply compact_single_prop.
Qed.

(* Begin_Tex_Verb *)
Hypothesis H:fun_series_convergent_IR.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma fun_series_inc_IR :
  (x:IR)(iprop J x)->(n:nat)(Pred (f n) x).
(* End_Tex_Verb *)
Intros.
Elim (H ?? (leEq_reflexive ? x) (compact_single_iprop J x H0)).
Intros contF CauchyF.
Apply (contin_imp_inc ???? (contF n)).
Apply compact_single_prop.
Qed.

(* Begin_Tex_Verb *)
Local h:=[x:IR][Hx:(iprop J x)](series_sum ?
  (fun_series_conv_imp_conv ????
    (H ?? (leEq_reflexive ? x) (compact_single_iprop J x Hx))
     x (compact_single_prop x) (fun_series_inc_IR x Hx))).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_strext_IR : (x,y,Hx,Hy:?)
  (((h x Hx)[#](h y Hy))->(x[#]y)).
(* End_Tex_Verb *)
Unfold h; Clear h; Intros.
Unfold series_sum in H0.
Elim (Lim_strext ?? H0); Intros N HN.
Simpl in HN; Unfold seq_part_sum in HN.
Elim (Sum0_strext ???? HN); Intros.
Exact (pfstrx ?????? q).
Qed.

(* Begin_Tex_Verb *)
Definition FSeries_Sum : PartIR.
(* End_Tex_Verb *)
Apply Build_PartFunct with pfpfun:=h.
Apply iprop_wd.
Exact FSeries_Sum_strext_IR.
Defined.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_char :
  (a,b:IR)(Hab:a[<=]b)(Hinc:(included (Compact Hab) (iprop J)))
  (Feq (Compact Hab) FSeries_Sum
                     (Fun_Series_Sum (H a b Hab Hinc))).
(* End_Tex_Verb *)
Intros; FEQ.
Simpl; Included.
Simpl; Unfold h.
Apply series_sum_wd; Intros; Algebra.
Qed.

End Series_Definitions.

Implicits FSeries_Sum [1 2].

Section More_Series_Definitions.

Variable J:interval.
Variable f:nat->PartIR.

(* Tex_Prose
Absolute convergence still exists.
*)

(* Begin_Tex_Verb *)
Definition fun_series_abs_convergent_IR :=
  (fun_series_convergent_IR J [n:nat](FAbs (f n))).
(* End_Tex_Verb *)

End More_Series_Definitions.

Section Convergence_Results.

(* Tex_Prose
As before, any series converges to its Sum.
*)

Variable J:interval.
Variable f:nat->PartIR.

(* Begin_Tex_Verb *)
Lemma FSeries_conv : (convF,H,H':?)
  (conv_fun_seq'_IR J [n:nat](FSum0 n f)
    (!FSeries_Sum J f convF) H H').
(* End_Tex_Verb *)
Intros.
Red; Intros.
Elim (convF ??? Hinc); Intros Hcont Hconv.
Apply conv_fun_seq'_wdr with 
  f:=[n:nat](FSum0 n f)
  contf:=[n:nat](included_imp_Continuous ?? (H n) ??? Hinc)
  contF:=(Fun_Series_Sum_cont ???? (convF ??? Hinc)).
Apply Feq_symmetric; Apply FSeries_Sum_char.
Apply conv_fun_seq'_wdl with 
  f:=(fun_seq_part_sum f)
  contf:=[n:nat](included_imp_Continuous ?? (H n) ??? Hinc)
  contF:=(Fun_Series_Sum_cont ???? (convF ??? Hinc)).
Intro; Apply Feq_reflexive.
Red; Intros.
Simpl; Intros.
Apply (contin_imp_inc ???? (Hcont n0)); Auto.
Apply fun_series_conv.
Qed.

(* Begin_Tex_Verb *)
Lemma convergent_imp_inc : (fun_series_convergent_IR J f)->
  (n:nat)(included (iprop J) (Pred (f n))).
(* End_Tex_Verb *)
Intros.
Apply included_imp_inc.
Intros.
Red in H.
Elim (H ??? H0); Intros.
Apply contin_imp_inc; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma convergent_imp_Continuous : 
  (fun_series_convergent_IR J f)->(n:nat)(Continuous J (f n)).
(* End_Tex_Verb *)
Intros.
Split.
Exact (convergent_imp_inc H n).
Intros; Auto.
Elim (H a b Hab H0); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Continuous_FSeries_Sum :
  (H:?)(Continuous J (!FSeries_Sum J f H)).
(* End_Tex_Verb *)
Intros.
Split; Included.
Intros.
EApply Continuous_I_wd.
Apply Feq_symmetric; Apply (FSeries_Sum_char ?? H ??? H0).
EApply Continuous_I_wd.
Apply Fun_Series_Sum_char.
Apply Cauchy_cont_Lim.
Qed.

End Convergence_Results.

Hints Resolve convergent_imp_inc : included.
Hints Resolve convergent_imp_Continuous Continuous_FSeries_Sum : continuous.

Section Operations.

(* Tex_Prose
\subsection{Algebraic Operations}

Convergence is well defined and preserved by operations.
*)

Variable J:interval.

(* Begin_Tex_Verb *)
Lemma conv_fun_const_series_IR : (x:nat->IR)(convergent x)->
  (fun_series_convergent_IR J [n:nat]{-C-}(x n)).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Apply conv_fun_const_series; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_const_series_Sum_IR : (y:nat->IR)(H:(convergent y))
  (H':(fun_series_convergent_IR J [n:nat]{-C-}(y n)))
  (x,Hx:?)((FSeries_Sum H') x Hx)[=](series_sum ? H).
(* End_Tex_Verb *)
Intros.
Simpl.
Apply series_sum_wd.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma conv_zero_fun_series_IR :
  (fun_series_convergent_IR J [n:nat]{-C-}Zero).
(* End_Tex_Verb *)
Apply conv_fun_const_series_IR with x:=[n:nat](Zero::IR).
Apply conv_zero_series.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_zero_IR :
  (H:(fun_series_convergent_IR J [n:nat]{-C-}Zero))
  (x:IR)(Hx:?)((FSeries_Sum H) x Hx)[=]Zero.
(* End_Tex_Verb *)
Intros.
Simpl.
Apply series_sum_zero.
Qed.

Variables f,g:nat->PartIR.

(* Begin_Tex_Verb *)
Lemma fun_series_convergent_wd_IR :
  ((n:nat)(Feq (iprop J) (f n) (g n)))->
  (fun_series_convergent_IR J f)->(fun_series_convergent_IR J g).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Apply fun_series_convergent_wd with f.
Intros; Apply included_Feq with (iprop J); Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Hypothesis convF : (fun_series_convergent_IR J f).
Hypothesis convG : (fun_series_convergent_IR J g).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_wd' :
  ((n:nat)(Feq (iprop J) (f n) (g n)))->
  (Feq (iprop J) (FSeries_Sum convF) (FSeries_Sum convG)).
(* End_Tex_Verb *)
Intros.
Apply included_Feq'; Intros.
EApply Feq_transitive.
Apply (FSeries_Sum_char ?? convF a b Hab H0).
EApply Feq_transitive.
2: Apply Feq_symmetric; Apply (FSeries_Sum_char ?? convG a b Hab H0).
Apply Fun_Series_Sum_wd'.
Intro; Apply included_Feq with (iprop J); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_plus_conv :
  (fun_series_convergent_IR J [n:nat](f n){+}(g n)).
(* End_Tex_Verb *)
Red; Intros.
Apply conv_fun_series_plus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_plus :
  (H:(fun_series_convergent_IR J [n:nat](f n){+}(g n)))
  (Feq (iprop J) (FSeries_Sum H)
                 (FSeries_Sum convF){+}(FSeries_Sum convG)).
(* End_Tex_Verb *)
Intros.
Apply included_Feq'; Intros.
EApply Feq_transitive.
Apply (FSeries_Sum_char ?? H a b Hab H0).
EApply Feq_transitive.
Apply Fun_Series_Sum_plus with convF:=(convF a b Hab H0) convG:=(convG a b Hab H0).
Apply Feq_symmetric; Apply Feq_plus; Apply FSeries_Sum_char.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_inv_conv :
  (fun_series_convergent_IR J [n:nat]{--}(f n)).
(* End_Tex_Verb *)
Red; Intros.
Apply conv_fun_series_inv; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_inv :
  (H:(fun_series_convergent_IR J [n:nat]{--}(f n)))
  (Feq (iprop J) (FSeries_Sum H) {--}(FSeries_Sum convF)).
(* End_Tex_Verb *)
Intros.
Apply included_Feq'; Intros.
EApply Feq_transitive.
Apply (FSeries_Sum_char ?? H a b Hab H0).
EApply Feq_transitive.
Apply Fun_Series_Sum_inv with convF:=(convF a b Hab H0).
Apply Feq_symmetric; Apply Feq_inv; Apply FSeries_Sum_char.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_minus_conv :
  (fun_series_convergent_IR J [n:nat](f n){-}(g n)).
(* End_Tex_Verb *)
Red; Intros.
Apply conv_fun_series_minus; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_minus :
  (H:(fun_series_convergent_IR J [n:nat](f n){-}(g n)))
  (Feq (iprop J) (FSeries_Sum H)
                 (FSeries_Sum convF){-}(FSeries_Sum convG)).
(* End_Tex_Verb *)
Intros.
Apply included_Feq'; Intros.
EApply Feq_transitive.
Apply (FSeries_Sum_char ?? H a b Hab H0).
EApply Feq_transitive.
Apply Fun_Series_Sum_minus with convF:=(convF a b Hab H0) convG:=(convG a b Hab H0).
Apply Feq_symmetric; Apply Feq_minus; Apply FSeries_Sum_char.
Qed.

(* Tex_Prose
\begin{convention} Let \verb!c:IR! and \verb!H:PartIR! be continuous in \verb!J!.
\end{convention}
*)

Variable c:IR.
Variable H:PartIR.
Hypothesis contH:(Continuous J H).

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_scal_conv :
  (fun_series_convergent_IR J [n:nat]H{*}(f n)).
(* End_Tex_Verb *)
Red; Intros.
Apply conv_fun_series_mult_scal; Auto.
EApply included_imp_Continuous.
Apply contH.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma FSeries_Sum_scal :
  (H':(fun_series_convergent_IR J [n:nat]H{*}(f n)))
  (Feq (iprop J) (FSeries_Sum H') H{*}(FSeries_Sum convF)).
(* End_Tex_Verb *)
Intros.
Apply included_Feq'; Intros.
Cut (Continuous_I Hab H); Intros.
EApply Feq_transitive.
Apply (FSeries_Sum_char ?? H' a b Hab H0).
EApply Feq_transitive.
Apply Fun_Series_Sum_mult_scal with convF:=(convF a b Hab H0).
Auto.
Apply Feq_symmetric; Apply Feq_mult.
Apply Feq_reflexive; Included.
Apply FSeries_Sum_char.
EApply included_imp_Continuous.
Apply contH.
Auto.
Qed.

End Operations.

Section Convergence_Criteria.

(* Tex_Prose
\subsection{Convergence Criteria}

The most important tests for convergence of series still apply: the comparison test (in both versions) and the ratio test.
*)

Variable J:interval.
Variable f:nat->PartIR.
Hypothesis contF : (n:nat)(Continuous J (f n)).

(* Begin_Tex_Verb *)
Lemma fun_str_comparison_IR : (g:nat->PartIR)
  (fun_series_convergent_IR J g)->
  {k:nat | ((n:nat)(le k n)->(x:IR)((iprop J x)->
    (Hx,Hx':?)(AbsIR ((f n) x Hx))[<=]((g n) x Hx')))}->
  (fun_series_convergent_IR J f).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Apply fun_str_comparison with g.
Intro; Apply included_imp_Continuous with J; Auto.
Auto.
Elim H0; Clear H0; Intros k Hk.
Exists k; Intros.
Apply Hk; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_comparison_IR : (g:nat->PartIR)
  (fun_series_convergent_IR J g)->
  ((n:nat)(x:IR)(iprop J x)->
    (Hx,Hx':?)(AbsIR ((f n) x Hx))[<=]((g n) x Hx'))->
  (fun_series_convergent_IR J f).
(* End_Tex_Verb *)
Intros.
Apply fun_str_comparison_IR with g; Auto.
Exists O; Intros; Apply H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma abs_imp_conv_IR : (fun_series_abs_convergent_IR J f)->
  (fun_series_convergent_IR J f).
(* End_Tex_Verb *)
Intros.
Apply fun_comparison_IR with [n:nat](FAbs (f n)).
Apply H.
Intros; Simpl; Apply eq_imp_leEq; Apply AbsIR_wd; Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma fun_ratio_test_conv_IR : {N:nat & {c:IR &
  (c[<]One) | (Zero[<=]c) /\ (x:IR)(iprop J x)->
    (n:nat)(le N n)->(Hx,Hx':?)
    (AbsIR ((f (S n)) x Hx'))[<=]
      c[*](AbsIR ((f n) x Hx))}}->
  (fun_series_convergent_IR J f).
(* End_Tex_Verb *)
Intros.
Red; Intros.
Apply fun_ratio_test_conv.
Intro; Apply included_imp_Continuous with J; Auto.
Elim H; Intros N HN.
Elim HN; Clear H HN; Intros c Hc H.
Inversion_clear H.
Exists N; Exists c; Repeat Split; Auto.
Qed.

End Convergence_Criteria.

Section Insert_Series.

(* Tex_Prose
\subsection{Translation}

When working in particular with power series and Taylor series, it is sometimes useful to ``shift'' all the terms in the series one position forward, that is, replacing each $f_{i+1}$ by $f_i$ and inserting the null function in the first position.  This does not affect convergence or the Sum of the series.
*)

Variable J:interval.
Variable f:nat->PartIR.
Hypothesis convF:(fun_series_convergent_IR J f).

(* Begin_Tex_Verb *)
Definition insert_series : nat->PartIR := [n:nat]
  Cases n of
    O     => {-C-}Zero
  | (S p) => (f p)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma insert_series_cont :
  (n:nat)(Continuous J (insert_series n)).
(* End_Tex_Verb *)
Intro; Elim n; Intros.
Simpl; Apply Continuous_const.
Simpl; Apply convergent_imp_Continuous; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma insert_series_sum_char : (n:nat)(x,Hx,Hx':?)
  ((fun_seq_part_sum f n) x Hx)[=]
    ((fun_seq_part_sum insert_series (S n)) x Hx').
(* End_Tex_Verb *)
Intro; Induction n.
Intros; Simpl; Algebra.
Intros; Simpl; Simpl in Hrecn; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma insert_series_conv :
  (fun_series_convergent_IR J insert_series).
(* End_Tex_Verb *)
Red; Intros.
Elim (convF ??? Hinc); Intros Hcont HCauchy.
Exists [n:nat](included_imp_Continuous ?? (insert_series_cont n) ??? Hinc).
Red; Intros.
Elim (HCauchy e H); Intros N HN.
Exists (S N); Do 4 Intro.
Cut m=(S (pred m)); [Intro | Apply S_pred with O; Apply lt_le_trans with (S N); Auto with arith].
Cut n=(S (pred n)); [Intro | Apply S_pred with O; Apply lt_le_trans with (S N); Auto with arith].
Generalize H0 H1; Clear H1 H0.
Rewrite H2; Rewrite H3; Clear H2 H3.
Intros.
Cut (le N (pred m)); [Intro | Auto with arith].
Cut (le N (pred n)); [Intro | Auto with arith].
EApply leEq_wdl.
Apply (HN ?? H2 H3 x Hx).
Apply AbsIR_wd.
Apply cg_minus_wd; Apply insert_series_sum_char.
Qed.

(* Begin_Tex_Verb *)
Lemma insert_series_sum :
  (Feq (iprop J) (FSeries_Sum convF)
                 (FSeries_Sum insert_series_conv)).
(* End_Tex_Verb *)
LetTac contF:=(convergent_imp_Continuous ?? convF).
Apply FLim_unique_IR with [n:nat](FSum0 n f) [n:nat](Continuous_Sum0 ?? contF n) 
  (Continuous_FSeries_Sum ?? convF) (Continuous_FSeries_Sum ?? insert_series_conv).
Apply FSeries_conv.
Red; Intros.
LetTac convS:=
  (FSeries_conv ?? insert_series_conv (Continuous_Sum0 ?? insert_series_cont) (Continuous_FSeries_Sum ?? insert_series_conv) ??? Hinc).
ClearBody convS.
Red; Intros.
Elim (convS e H); Intros N HN.
Clear convS; Exists N; Intros.
EApply leEq_wdl.
Apply (HN (S n) (le_S ?? H0) ? Hx).
Apply AbsIR_wd; Apply cg_minus_wd.
2: Algebra.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
EApply eq_transitive_unfolded.
2: Apply (insert_series_sum_char n x 
  (contin_imp_inc ???? (included_imp_Continuous ?? (Continuous_Sum0 ?? contF n) ??? Hinc) ? Hx)
  (contin_imp_inc ???? (included_imp_Continuous ?? (Continuous_Sum0 ?? insert_series_cont (S n)) ??? Hinc) ? Hx)).
Unfold fun_seq_part_sum; Algebra.
Unfold fun_seq_part_sum; Algebra.
Qed.

End Insert_Series.
