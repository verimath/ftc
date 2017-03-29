(* $Id: CLogic.v,v 1.9 2003/03/12 08:57:44 lcf Exp $ *)

Require Export Compare_dec.
Require Export Basics.
Require Export ZArith.
Require Export ZArithRing.
Require Export Div2.
Require Export Wf_nat.

(* Tex_Prose
\chapter{Extending the {\tt Coq} Logic}
Because notions of apartness and order have computational meaning, we
will have to define logical connectives in \verb!Set!.  In order to
keep a syntactic distinction between types of terms, we define \verb!CProp!
as an alias for \verb!Set!, to be used as type of (computationally meaningful)
propositions.

Falsehood and negation will tipically not be needed in \verb!CProp!, as they are used to refer
to negative statements, which carry no computational meaning.  Therefore, we will
simply define a negation operator from \verb!Set! to \verb!Prop! .

Conjunction, disjunction and existential quantification will have to come in
multiple varieties.  For conjunction, we will need four operators of type
$s_1\rightarrow s_2\rightarrow s_3$, where $s_3$ is \verb!Prop! if both $s_1$ and $s_2$
are \verb!Prop! and \verb!CProp! otherwise.

Disjunction is slightly different, as it will always return a value in \verb!CProp! even
if both arguments are propositions.  This is because in general 
it may be computationally important to know which of the two branches of the disjunction actually holds.

Existential quantification will similarly always return a value in \verb!CProp!.

\begin{notation}
\begin{itemize}
\item \verb!CProp!-valued conjuction will be denoted as {\tt *};
\item \verb!CProp!-valued conjuction will be denoted as \verb!+!;
\item in both preceding cases, objects of type \verb!Prop! will be enclosed in curly braces;
\item Existential quantification will be written as \verb!{x:A & B}! or \verb!{x:A | B}!, 
according to whether \verb!B! is respectively of type \verb!CProp! or \verb!Prop!.
\end{itemize}
\end{notation}

In a few specific situations we {\em do} need truth, false and negation in \verb!CProp!, so we will
also introduce them; this should be a temporary option\ldots

Finally, for other formulae that might occur in our \verb!CProp!-valued
propositions, such as \verb!(le m n)!, we have to introduce a \verb!CProp!-valued
version.
*)

Definition CProp := Set.

Section Basics.
(* Tex_Prose
\section{Basics}
Here we treat conversion from \verb!Prop! to \verb!CProp! and vice versa,
and some basic connectives in \verb!CProp!.
*)

(* Begin_Tex_Verb *)
Definition Not := [P:CProp](P->False).
Definition Iff [A,B:CProp] : CProp := (A->B)*(B->A).
Inductive CFalse : CProp :=.
Inductive CTrue : CProp := CI : CTrue.

Inductive sig2P [A:Set;P:A->Prop;Q:A->CProp] : CProp
      := exist2P : (x:A)(P x) -> (Q x) -> (sig2P A P Q).

Inductive sigS2P [A:Set;P:A->CProp;Q:A->Prop] : CProp
      := existS2P : (x:A)(P x) -> (Q x) -> (sigS2P A P Q).

  Definition proj1_sig2 [A:Set;P,Q:A->Prop]:=
   [e:(sig2 A P Q)]Cases e of (exist2 a b c) => a  end.

  Definition proj2a_sig2 [A:Set;P,Q:A->Prop]:=
   [e:(sig2 A P Q)]
     <[e:(sig2 A P Q)](P (proj1_sig2 A P Q e))>Cases e of (exist2 a b c) => b  end.

  Definition proj2b_sig2 [A:Set;P,Q:A->Prop]:=
   [e:(sig2 A P Q)]
     <[e:(sig2 A P Q)](Q (proj1_sig2 A P Q e))>Cases e of (exist2 a b c) => c  end.

  Definition proj1_sig2P [A:Set;P,Q:A->?]:=
   [e:(sig2P A P Q)]Cases e of (exist2P a b c) => a  end.

  Definition proj2a_sig2P [A:Set;P,Q:A->?]:=
   [e:(sig2P A P Q)]
     <[e:(sig2P A P Q)](P (proj1_sig2P A P Q e))>Cases e of (exist2P a b c) => b  end.

  Definition proj2b_sig2P [A:Set;P,Q:A->?]:=
   [e:(sig2P A P Q)]
     <[e:(sig2P A P Q)](Q (proj1_sig2P A P Q e))>Cases e of (exist2P a b c) => c  end.

  Definition proj1_sigS2P [A:Set;P,Q:A->?]:=
   [e:(sigS2P A P Q)]Cases e of (existS2P a b c) => a  end.

  Definition proj2a_sigS2P [A:Set;P,Q:A->?]:=
   [e:(sigS2P A P Q)]
     <[e:(sigS2P A P Q)](P (proj1_sigS2P A P Q e))>Cases e of (existS2P a b c) => b  end.

  Definition proj2b_sigS2P [A:Set;P,Q:A->?]:=
   [e:(sigS2P A P Q)]
     <[e:(sigS2P A P Q)](Q (proj1_sigS2P A P Q e))>Cases e of (existS2P a b c) => c  end.

Inductive toCProp [A:Prop] : CProp := ts : A->(toCProp A).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma toCProp_e : (A:Prop)(toCProp A)->(P:Prop)(A->P)->P.
(* End_Tex_Verb *)
Intros A H P H0.
Elim H.
Intros H1.
Apply H0.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition CNot := [A:Prop]A->CFalse.

Lemma Ccontrapos':(A,phi:Prop)(A->phi)->(~phi)->(CNot A).
(* End_Tex_Verb *)
Proof.
 Intros A phi H H0.
 Intro H1.
 Elim H0.
 Auto.
Qed.

(* Begin_Tex_Verb *)
Inductive andl [A:CProp][B:Prop] : CProp := conjl : A->B->(andl A B).
Inductive andr [A:Prop][B:CProp] : CProp := conjr : A->B->(andr A B).
Inductive andps [A,B:Prop] : CProp := conjps : A->B->(andps A B).

Inductive sumorr [A:Prop;B:CProp] : CProp :=
    inleft'  : A -> (sumorr A B)
  | inright' : B -> (sumorr A B).
(* End_Tex_Verb *)

End Basics.

(* Syntax and pretty printing:
  - disjunction will be written as P+Q;
  - conjunction will be written as P*Q;
  - arguments of type Prop should be enclosed in {curly braces}.
*)

Arguments Scope sumbool [type_scope type_scope].
Arguments Scope sumor [type_scope type_scope].
Arguments Scope sumorr [type_scope type_scope].
Arguments Scope sum [type_scope type_scope].

Notation "{ A } + { B }" := ((sumbool A B) :: CProp) (at level 1).
Notation "A + { B }" := ((sumor A B) :: CProp) (at level 4).
Notation "{ A } + B" := (sumorr A B) (at level 1).
Notation "A + B" := ((sum A B) :: CProp) (at level 4).

Arguments Scope andps [type_scope type_scope].
Arguments Scope andl [type_scope type_scope].
Arguments Scope andr [type_scope type_scope].
Arguments Scope prod [type_scope type_scope].

Notation "{ A } * { B }" := (andps A B) (at level 1).
Notation "A * { B }" := (andl A B) (at level 3).
Notation "{ A } * B" := (andr A B) (at level 1).
Notation "A * B" := ((prod A B) :: CProp) (at level 3).

Arguments Scope sig [type_scope type_scope].
Arguments Scope sig2 [type_scope type_scope type_scope].

Notation "{ x : A  |  P }"       := ((sig A [x:A]P) :: CProp)         (at level 1).
Notation "{ x : A  |  P  |  Q }" := ((sig2 A [x:A]P [x:A]Q) :: CProp) (at level 1).

Arguments Scope sigS [type_scope type_scope].
Arguments Scope sigS2 [type_scope type_scope type_scope].

Notation "{ x : A  &  P }"       := ((sigS A [x:A]P) :: CProp)         (at level 1).
Notation "{ x : A  &  P  &  Q }" := ((sigS2 A [x:A]P [x:A]Q) :: CProp) (at level 1).

Arguments Scope sig2P [type_scope type_scope type_scope].
Arguments Scope sigS2P [type_scope type_scope type_scope].

Notation "{ x : A  |  P  &  Q }" := (sig2P A [x:A]P [x:A]Q) (at level 1).
Notation "{ x : A  &  P  |  Q }" := (sigS2P A [x:A]P [x:A]Q) (at level 1).

Syntax constr level 5:
  sig_print [ (sig $c1 [$c2:$c1]$c3) ] -> [ "{" $c2 ":" $c1 " | " $c3 "}" ].

Syntax constr level 5:
  sigS_print [ (sigS $c1 [$c2:$c1]$c3) ] -> [ "{" $c2 ":" $c1 " & " $c3 "}" ].

Syntax constr level 5:
  sig2_print [ (sig2 $c1 [$c2:$c1]$c3 [$c2:$c1]$c4) ] -> [ "{" $c2 ":" $c1 " | (" $c3 ") | (" $c4 ")}" ].

Syntax constr level 5:
  sigS2_print [ (sigS2 $c1 [$c2:$c1]$c3 [$c2:$c1]$c4) ] -> [ "{" $c2 ":" $c1 " & (" $c3 ") & (" $c4 ")}" ].

Syntax constr level 5:
  cprop_hide [ (($c1) :: CProp) ] -> [ $c1:L ].

(*
Section teste.

Variable A:Set.
Variables P,Q:A->Prop.
Variables X,Y:A->CProp.

Check {x:A | (P x)}.
Check {x:A & (X x)}.
Check {x:A & (X x) & (Y x)}.
Check {x:A | (P x) | (Q x)}.
Check {x:A | (P x) & (X x)}.
Check {x:A & (X x) | (P x)}.

End teste.
*)

Hints Resolve CI : core.

Section Logical_Remarks.

(* Tex_Prose
We prove a few logical results which are helpful to have as lemmas when {\tt A}, {\tt B} and
{\tt C} are non trivial.
*)

(* Begin_Tex_Verb *)
Lemma CNot_Not_or : (A,B,C:CProp)(A->(Not C))->(B->(Not C))->~(Not A+B)->(Not C).
(* End_Tex_Verb *)
Intros.
Intro.
Apply H1.
Intro.
Elim H3.
Intro; Apply H; Auto.
Intro; Apply H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cnot_not_or : (A,B:Prop;C:CProp)(A->(Not C))->(B->(Not C))->~(Not {A}+{B})->(Not C).
(* End_Tex_Verb *)
Intros.
Intro.
Apply H1.
Intro.
Elim H3.
Intro; Apply H; Auto.
Intro; Apply H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cnot_Not_or : (A:Prop;B,C:CProp)(A->(Not C))->(B->(Not C))->~(Not {A}+B)->(Not C).
(* End_Tex_Verb *)
Intros.
Intro.
Apply H1.
Intro.
Elim H3.
Intro; Apply H; Auto.
Intro; Apply H0; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma CNot_not_or : (A:CProp;B:Prop;C:CProp)(A->(Not C))->(B->(Not C))->~(Not A+{B})->(Not C).
(* End_Tex_Verb *)
Intros.
Intro.
Apply H1.
Intro.
Elim H3.
Intro; Apply H; Auto.
Intro; Apply H0; Auto.
Qed.

End Logical_Remarks.

Section CRelation_Definition.
(* Tex_Prose
\section{CProp-valued Relations}
Similar to \verb!Relations.v! in Coq's standard library.
*)

(* Begin_Tex_Verb *)
Variable A: Set.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Crelation :=  A -> A -> CProp.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Variable R: Crelation.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Creflexive : CProp :=  (x: A) (R x x).
Definition Ctransitive : CProp := (x,y,z: A)(R x y)->(R y z)->(R x z).
Definition Csymmetric : CProp :=  (x,y: A) (R x y) -> (R y x).
Definition Cequiv : CProp := Creflexive * 
                                   (Ctransitive * Csymmetric).
(* End_Tex_Verb *)

End CRelation_Definition.

(* Begin_Tex_Verb *)
Inductive eqs [A : Set; x: A] :A->CProp := Crefl_equal :(eqs A x x).
(* End_Tex_Verb *)

(*
Section Set_equality.

* Tex_Prose
\begin{convention} Let \verb!A! be a set and \verb!x,y:A!.
\end{convention}
*

 Variable A: Set.
 Variable x,y: A.

* Begin_Tex_Verb *
Lemma toCProp_eq:(x=y)->(eqs ? x y).
* End_Tex_Verb *
Proof.
 Intros.
 Apply (eq_rec A x [a:A](eqs ? x a)).
 Apply Crefl_equal.
 Assumption.
Qed.

* Begin_Tex_Verb *
Lemma Set_eq_to:(eqs ? x y)->(x=y).
* End_Tex_Verb *
Proof.
 Intros. 
 Apply (eqs_ind A x [a:A;H:(eqs A x a)](x=a)). 
 Apply refl_equal.
 Assumption.
Qed.
 
End Set_equality.

* Begin_Tex_Verb *
Theorem Set_sym_equal:(A:Set;x,y:A)(eqs ? x y)->(eqs ? y x).
* End_Tex_Verb *
Proof.
 Intros.
 Apply toCProp_eq.
 Apply sym_equal.
 Apply Set_eq_to.
 Assumption.
Qed.

* Begin_Tex_Verb *
Theorem Set_trans_equal:(A:Set; x,y,z:A)(eqs ? x y)->(eqs ? y z)->(eqs ? x z).
* End_Tex_Verb *
Proof.
 Intros.
 Apply toCProp_eq.
 Apply trans_equal with y.
 Apply Set_eq_to.
 Assumption.
 Apply Set_eq_to.
 Assumption.
Qed.
*)
 
Section le_odd.

(* Tex_Prose
\section{The relation {\tt le}, {\tt lt}, {\tt odd} and {\tt even}}
*)

(* Begin_Tex_Verb *)
Inductive Cle [n:nat] : nat -> CProp
    := Cle_n : (Cle n n)
     | Cle_S : (m:nat)(Cle n m)->(Cle n (S m)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Theorem Cnat_double_ind : (R:nat->nat->CProp)
     ((n:nat)(R O n)) -> ((n:nat)(R (S n) O))
     -> ((n,m:nat)(R n m)->(R (S n) (S m)))
     -> (n,m:nat)(R n m).
(* End_Tex_Verb *)
Proof.
  Induction n; Auto.
  Induction m; Auto.
Qed.

(* Begin_Tex_Verb *)
Theorem my_Cle_ind : (n:nat; P:(nat->CProp))
        (P n)
        ->((m:nat)(Cle n m)->(P m)->(P (S m)))
        ->(n0:nat)(Cle n n0)->(P n0).
(* End_Tex_Verb *)
Intros n P.
Generalize (Cle_rec n [n0:nat][H:(Cle n n0)](P n0)); Intro.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Theorem Cle_n_S : (n,m:nat)(Cle n m)->(Cle (S n) (S m)).
(* End_Tex_Verb *)
Intros n m H.
Pattern m.
Apply (my_Cle_ind n).

Apply Cle_n.

Intros.
Apply Cle_S.
Assumption.

Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma toCle : (m,n:nat)(le m n)->(Cle m n).
(* End_Tex_Verb *)
Intros m.
Induction m.

Induction n.

Intro H.
Apply Cle_n.

Intros n0 H H0.
Apply Cle_S.
Apply H.
Apply le_O_n.

Induction n.

Intro.
ElimType False.
Inversion H.

Intros n0 H H0.
Generalize (le_S_n ?? H0); Intro H1.
Generalize (Hrecm ? H1); Intro H2.
Apply Cle_n_S.
Assumption.
Qed.

Hints Resolve toCle.

(* Begin_Tex_Verb *)
Lemma Cle_to : (m,n:nat)(Cle m n)->(le m n).
(* End_Tex_Verb *)
Intros m n H.
Elim H.

Apply le_n.

Intros m0 s H0.
Apply le_S.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Definition Clt [m,n:nat] := (Cle (S m) n) : CProp.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma toCProp_lt : (m,n:nat)(lt m n)->(Clt m n).
(* End_Tex_Verb *)
Unfold lt.
Unfold Clt.
Intros m n H.
Apply toCle.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Clt_to : (m,n:nat)(Clt m n)->(lt m n).
(* End_Tex_Verb *)
Unfold lt.
Unfold Clt.
Intros m n H.
Apply Cle_to.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Cle_le_S_eq : (p,q:nat)(le p q)->{le (S p) q}+{p=q}.
(* End_Tex_Verb *)
Intros p q H.
Elim (gt_eq_gt_dec p q); Intro H0.

Elim H0; Auto.

ElimType False.
Apply lt_not_le with q p; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Cnat_total_order : (m,n: nat) ~ m=n -> {lt m n} + {lt n m}.
(* End_Tex_Verb *)
Intros m n H.
Elim (gt_eq_gt_dec m n). 
Intro H0.

Elim H0; Intros. 

Left; Auto.

ElimType False.
Auto.

Auto.
Qed.

(* Begin_Tex_Verb *)
Mutual Inductive
      Codd : nat->CProp :=  
                Codd_S : (n:nat)(Ceven n)->(Codd (S n))
  with
      Ceven : nat->CProp :=
        Ceven_O : (Ceven (0)) | 
        Ceven_S : (n:nat)(Codd n)->(Ceven (S n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma Codd_even_to : 
             (n:nat)((Codd n)->(odd n)) /\ ((Ceven n) -> (even n)).
(* End_Tex_Verb *)
Induction n.

Split.

Intro H.
Inversion H.

Intro.
Apply even_O.

Intros n0 H.
Elim H; Intros H0 H1.
Split.

Intro H2.
Inversion H2.
Apply odd_S.
Apply H1.
Assumption.

Intro H2.
Inversion H2.
Apply even_S.
Apply H0.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Codd_to : (n:nat)(Codd n)->(odd n).
(* End_Tex_Verb *)
Intros n H.
Elim (Codd_even_to n); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Ceven_to : (n:nat)(Ceven n) -> (even n).
(* End_Tex_Verb *)
Intros n H.
Elim (Codd_even_to n); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma to_Codd_even : 
             (n:nat)((odd n)->(Codd n)) * ((even n)->(Ceven n)).
(* End_Tex_Verb *)
Induction n.

Split.

Intro H.
ElimType False.
Inversion H.

Intro H.
Apply Ceven_O.

Intros n0 H.
Elim H; Intros H0 H1.
Split.

Intro H2.
Apply Codd_S.
Apply H1.
Inversion H2.
Assumption.

Intro H2.
Apply Ceven_S.
Apply H0.
Inversion H2.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma to_Codd : (n:nat)(odd n)->(Codd n).
(* End_Tex_Verb *)
Intros.
Elim (to_Codd_even n); Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma to_Ceven : (n:nat)(even n)->(Ceven n).
(* End_Tex_Verb *)
Intros.
Elim (to_Codd_even n); Auto.
Qed.

End le_odd.

Section Misc.

(* Tex_Prose
\section{Miscellaneous}
*)

(* Begin_Tex_Verb *)
Lemma CZ_exh : (z:Z){n:nat | z=n} + {n:nat | z=`-n`}.
(* End_Tex_Verb *)
Intro z.
Elim z.

Left.
Exists O.
Auto.

Intro p.
Left.
Exists (convert p).
Rewrite convert_is_POS.
Reflexivity.

Intro p.
Right.
Exists (convert p).
Rewrite min_convert_is_NEG.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma Cnats_Z_ind :
              (P:Z->CProp)((n:nat)(P n)) -> ((n:nat)(P `-n`)) -> (z:Z)(P z).
(* End_Tex_Verb *)
Intros P H H0 z.
Elim (CZ_exh z); Intros H1.

Elim H1; Intros n H2.
Rewrite H2.
Apply H.

Elim H1; Intros n H2.
Rewrite H2.
Apply H0.
Qed.

(* Begin_Tex_Verb *)
Lemma Cdiff_Z_ind : (P:Z->CProp)((m,n:nat)(P `m-n`)) -> ((z:Z)(P z)).
(* End_Tex_Verb *)
Intros P H z.
Apply Cnats_Z_ind.

Intro n.
Replace (inject_nat `n`) with `n-O`.
Apply H.
Simpl.
Auto with zarith.

Intro n.
Replace `-n` with `O-n`.
Apply H.
Simpl.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma Cpred_succ_Z_ind : (P:Z->CProp)(P `0`) ->
                                   ((n:Z)(P n)->(P `n+1`)) ->
                                   ((n:Z)(P n)->(P `n-1`)) ->
                                   (z:Z)(P z).
(* End_Tex_Verb *)
Intros P H H0 H1 z.
Apply Cnats_Z_ind.

Intro n.
Elim n.

Exact H.

Intros n0 H2.
Replace ((S n0)::Z) with `n0+1`.

Apply H0.
Assumption.

Rewrite inj_S.
Reflexivity.

Intro n.
Elim n.

Exact H.

Intros n0 H2.
Replace `-(S n0)` with `-n0-1`.

Apply H1.
Assumption.

Rewrite inj_S.
Unfold Zs.
Rewrite Zopp_Zplus.
Reflexivity.
Qed.

(*
* Begin_Tex_Verb *
Lemma sum_rec_or : (A,B:Set)(S:Set)(l,r:S)(s:A+B)
                  (sum_rec A B [_:A+B]S [x:A]l [x:B]r s) = l \/
                  (sum_rec A B [_:A+B]S [x:A]l [x:B]r s) = r.
* End_Tex_Verb *
Intros. Elim s.
Intros. Left. Reflexivity.
Intros. Right. Reflexivity.
Qed.
*)

(* Begin_Tex_Verb *)
Lemma not_r_sum_rec : (A,B:Set)(S:Set)(l,r:S)(Not B)->(H:A+B)
                  (sum_rec A B [_:A+B]S [x:A]l [x:B]r H) = l.
(* End_Tex_Verb *)
Intros A B S l r H H0. Elim H0.
Intro a. Reflexivity.
Intro b. Elim H. Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma not_l_sum_rec : (A,B:Set)(S:Set)(l,r:S)(Not A)->(H:A+B)
                          (sum_rec A B [_:A+B]S [x:A]l [x:B]r H) = r.
(* End_Tex_Verb *)
Intros A B S l r H H0. Elim H0.
Intro a. Elim H. Assumption.
Intros. Reflexivity.
Qed.

End Misc.

(* Tex_Prose
\section{Results about the natural numbers}

We now define a class of predicates on a finite subset of natural numbers that will be important throughout all our work.  Essentially, these are simply setoid predicates, but for clearness we will never write them in that form but we will single out the preservation of the setoid equality.
*)

(* Begin_Tex_Verb *)
Definition nat_less_n_pred [n:nat][P:(i:nat)(lt i n)->CProp] :=
  (i,j:nat)(i=j)->(H:(lt i n))(H':(lt j n))(P i H)->(P j H').
Definition nat_less_n_pred' [n:nat][P:(i:nat)(le i n)->CProp] :=
  (i,j:nat)(i=j)->(H:(le i n))(H':(le j n))(P i H)->(P j H').
(* End_Tex_Verb *)

Section Odd_and_Even.

(* Tex_Prose
\subsection*{Odd and Even}

For our work we will many times need to distinguish cases between even or odd numbers.  We begin by proving that this case distinction is decidable:
*)

(* Tex_Prose
Next, we prove the usual results about sums of even and odd numbers:
*)

(* Begin_Tex_Verb *)
Lemma even_plus_n_n : (n:nat)(even (plus n n)).
(* End_Tex_Verb *)
Intro n; Induction n.

Auto with arith.

Replace (plus (S n) (S n)) with (S (S (plus n n))).

Apply even_S; Apply odd_S; Apply Hrecn.

Rewrite plus_n_Sm; Simpl; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma even_or_odd_plus : (k:nat)
  {j:nat & {k=(plus j j)}+{k=(S (plus j j))}}.
(* End_Tex_Verb *)
Intro k.
Elim (even_odd_dec k); Intro H.

Elim (even_2n k H); Intros j Hj; Exists j; Auto.

Elim (odd_S2n k H); Intros j Hj; Exists j; Auto.
Qed.

(* Tex_Prose
Finally, we prove that an arbitrary natural number can be written in some canonical way.
*)

(* Begin_Tex_Verb *)
Lemma even_or_odd_plus_gt : (i,j:nat)(le i j)->
  {k:nat & {j=(plus i (plus k k))}
         + {j=(plus i (S (plus k k)))}}.
(* End_Tex_Verb *)
Intros i j H.
Elim (even_or_odd_plus (minus j i)).
Intros k Hk.
Elim Hk; Intro H0.

Exists k; Left; Rewrite <- H0; Auto with arith.

Exists k; Right; Rewrite <- H0; Auto with arith.
Qed.

End Odd_and_Even.

Hints Resolve even_plus_n_n : arith.
Hints Resolve toCle : core.

Section Natural_Numbers.

(* Tex_Prose
\subsection*{Algebraic Properties}

We now present a series of trivial things proved with \verb!Omega! that are stated as lemmas to make proofs shorter and to aid in auxiliary definitions.  Giving a name to these results allows us to use them in definitions keeping conciseness.
*)

(* Begin_Tex_Verb *)
Lemma Clt_le_weak : (i,j:nat)(Clt i j)->(Cle i j).
(* End_Tex_Verb *)
Intros.
Apply toCle; Apply lt_le_weak; Apply Clt_to; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_5 : (i,n:nat)(lt i n)->(lt (pred i) n).
(* End_Tex_Verb *)
Intros; Apply le_lt_trans with (pred n).
Apply le_pred; Auto with arith.
Apply lt_pred_n_n; Apply le_lt_trans with i; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_8 : (m,n:nat)(lt m (pred n))->(lt m n).
(* End_Tex_Verb *)
Intros; Apply lt_le_trans with (pred n); Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma pred_lt : (m,n:nat)(lt m (pred n))->(lt (S m) n).
(* End_Tex_Verb *)
Intros; Apply le_lt_trans with (pred n); Auto with arith.
Apply lt_pred_n_n; Apply le_lt_trans with m.
Auto with arith.
Apply lt_le_trans with (pred n); Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_10 : (i,m,n:nat)(lt O i)->(lt i (pred (plus m n)))->
  (lt (pred i) (plus (pred m) (pred n))).
(* End_Tex_Verb *)
Intros; Omega.
Qed.

(* Begin_Tex_Verb *)
Lemma lt_pred' : (m,n:nat)(lt O m)->(lt m n)->
  (lt (pred m) (pred n)).
(* End_Tex_Verb *)
Intros m n H H0; Red.
NewDestruct n.

Inversion H0.

Rewrite <- (S_pred m O); Auto.
Simpl.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma le_1 : (m,n:nat)(Cle m n)->(le (pred m) n).
(* End_Tex_Verb *)
Intros.
Cut (le m n); [Intro | Apply Cle_to; Assumption].
Apply le_trans with (pred n); Auto with arith.
Apply le_pred; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma le_2 : (i,j:nat)(lt i j)->(le i (pred j)).
(* End_Tex_Verb *)
Intros; Omega.
Qed.

(* Begin_Tex_Verb *)
Lemma plus_eq_one_imp_eq_zero :
  (m,n:nat)(le (plus m n) (1))->{m=O}+{n=O}.
(* End_Tex_Verb *)
Intros m n H.
Elim (le_lt_dec m O); Intro.
Left; Auto with arith.
Right; Omega.
Qed.

(* Tex_Prose
We now prove some properties of functions on the natural numbers.
*)

(* Begin_Tex_Verb *)
Variable h:nat->nat.
(* End_Tex_Verb *)

(* Tex_Prose
First we characterize monotonicity by a local condition: if $h(n)<h(n+1)$ for every natural number $n$ then $h$ is monotonous.  An analogous result holds for weak monotonicity.
*)

(* Begin_Tex_Verb *)
Lemma nat_local_mon_imp_mon : ((i:nat)(lt (h i) (h (S i))))->
  (i,j:nat)(lt i j)->(lt (h i) (h j)).
(* End_Tex_Verb *)
Intros H i j H0.
Induction j.

ElimType False; Omega.

Cut (le i j); [Intro H1 | Auto with arith].
Elim (le_lt_eq_dec ?? H1); Intro H2.

Cut (lt (h i) (h j)); [Intro | Apply Hrecj; Assumption].
Cut (lt (h j) (h (S j))); [Intro | Apply H].
Apply lt_trans with (h j); Auto.

Rewrite H2; Apply H.
Qed.

(* Begin_Tex_Verb *)
Lemma nat_local_mon_imp_mon_le : ((i:nat)(le (h i) (h (S i))))->
  (i,j:nat)(le i j)->(le (h i) (h j)).
(* End_Tex_Verb *)
Intros H i j H0.
Induction j.

Cut i=O; [Intro H1 | Auto with arith].
Rewrite H1; Apply le_n.

Elim (le_lt_eq_dec ?? H0); Intro H1.

Cut (le (h i) (h j)); [Intro | Apply Hrecj; Auto with arith].
Cut (le (h j) (h (S j))); [Intro | Apply H].
Apply le_trans with (h j); Auto.

Rewrite H1; Apply le_n.
Qed.

(* Tex_Prose
A strictly increasing function is injective:
*)

(* Begin_Tex_Verb *)
Lemma nat_mon_imp_inj : ((i,j:nat)(lt i j)->(lt (h i) (h j)))->
  (i,j:nat)((h i)=(h j))->i=j.
(* End_Tex_Verb *)
Intros H i j H0.
Cut ~~i=j; [Omega | Intro H1].
Cut (lt i j)\/(lt j i); [Intro H2 | Omega].
Inversion_clear H2.

Cut (lt (h i) (h j)); [Rewrite H0; Apply lt_n_n | Apply H; Assumption].

Cut (lt (h j) (h i)); [Rewrite H0; Apply lt_n_n | Apply H; Assumption].
Qed.

(* Tex_Prose
And (not completely trivial) a function that preserves $<$ also preserves $\leq$.
*)

(* Begin_Tex_Verb *)
Lemma nat_mon_imp_mon' : ((i,j:nat)(lt i j)->(lt (h i) (h j)))->
  (i,j:nat)(le i j)->(le (h i) (h j)).
(* End_Tex_Verb *)
Intros H i j H0.
Elim (le_lt_eq_dec ?? H0); Intro H1.

Apply lt_le_weak; Apply H; Assumption.

Rewrite H1; Apply le_n.
Qed.

(* Tex_Prose
The last lemma in this section states that a monotonous function in the natural numbers completely covers the natural numbers, that is, for every $n\in\NN$ there is an $i$ such that \[h(i)\leq n<(n+1)\leq h(i+1)\]
*)

(* Begin_Tex_Verb *)
Lemma mon_fun_covers :
  ((i,j:nat)(lt i j)->(lt (h i) (h j)))->(h O)=O->
  (n:nat){k:nat | (le (S n) (h k))}->
    {i:nat | (le (h i) n) | (le (S n) (h (S i)))}.
(* End_Tex_Verb *)
Intros H H0 n H1.
Elim H1; Intros k Hk.
Induction k.

Exists O.

Rewrite H0; Auto with arith.

Cut (lt (h O) (h (1))); [Intro; Apply le_trans with (h O); Auto with arith | Apply H; Apply lt_n_Sn].

Cut (lt (h k) (h (S k))); [Intro H2 | Apply H; Apply lt_n_Sn].
Elim (le_lt_dec (S n) (h k)); Intro H3.

Elim (Hreck H3); Intros i Hi.
Exists i; Assumption.

Exists k; Auto with arith.
Qed.

End Natural_Numbers.

Section Predicates_to_CProp.

(* Tex_Prose
\subsection*{Logical Properties}

This section contains lemmas that aid in logical reasoning with natural numbers.  First, we present some principles of induction, both for \verb!CProp!- and \verb!Prop!-valued predicates.  We begin by presenting the results for \verb!CProp!-valued predicates:
*)

(* Begin_Tex_Verb *)
Lemma even_induction : (P:nat->CProp)(P O)->
  ((n:nat)(even n)->(P n)->(P (S (S n))))->
  (n:nat)(even n)->(P n).
(* End_Tex_Verb *)
Intros P H H0 n.
Pattern n; Apply lt_wf_rec.
Clear n.
Intros n H1 H2.
Induction n.

Auto.

Induction n.

ElimType False; Inversion H2; Inversion H4.

Apply H0.

Inversion H2; Inversion H4; Auto.

Apply H1.

Auto with arith.

Inversion H2; Inversion H4; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma odd_induction : (P:nat->CProp)(P (1))->
  ((n:nat)(odd n)->(P n)->(P (S (S n))))->
  (n:nat)(odd n)->(P n).
(* End_Tex_Verb *)
Intros P H H0 n; Case n.

Intro H1; ElimType False; Inversion H1.

Clear n; Intros n H1.
Pattern n; Apply even_induction; Auto.

Intros n0 H2 H3; Auto with arith.

Inversion H1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma four_induction : (P:nat->CProp)
  (P (0))->(P (1))->(P (2))->(P (3))->
  ((n:nat)(P n)->(P (S (S (S (S n))))))->(n:nat)(P n).
(* End_Tex_Verb *)
Intros.
Apply lt_wf_rec.
Intro m.
Case m; Auto.
Clear m; Intro m.
Case m; Auto.
Clear m; Intro m.
Case m; Auto.
Clear m; Intro m.
Case m; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma nat_complete_double_induction : (P:nat->nat->CProp)
  ((m,n:nat)
    ((m',n':nat)(lt m' m)->(lt n' n)->(P m' n'))->(P m n))->
  (m,n:nat)(P m n).
(* End_Tex_Verb *)
Intros P H m.
Pattern m; Apply lt_wf_rec; Auto with arith.
Qed.

(* Tex_Prose
For subsetoid predicates in the natural numbers we can eliminate disjunction (and existential quantification) as follows.
*)

(* Begin_Tex_Verb *)
Lemma finite_or_elim : (n:nat)(P,Q:(i:nat)(le i n)->CProp)
  (nat_less_n_pred' n P)->(nat_less_n_pred' n Q)->
  ((i:nat)(H:(le i n))((P i H)+(Q i H)))->
    ({m:nat & {Hm:(Cle m n) &
      (P m (Cle_to ?? Hm))}}+(i:nat)(H:(le i n))(Q i H)).
(* End_Tex_Verb *)
Intro n; Induction n.

Intros P Q HP HQ H.
Elim (H ? (Cle_to ?? (toCle ?? (le_n O)))); Intro H0.

Left; Exists O; Exists (toCle ?? (le_n O)); Assumption.

Right; Intros i H1.
Apply HQ with H:=(Cle_to ?? (toCle ?? (le_n O))); Auto with arith.

Intros P Q H H0 H1.
Elim (H1 ? (Cle_to ?? (toCle ?? (le_n (S n))))); Intro H2.

Left; Exists (S n); Exists (toCle ?? (le_n (S n))); Assumption.

LetTac P':=[i:nat][H:(le i n)](P i (le_S ?? H)).
LetTac Q':=[i:nat][H:(le i n)](Q i (le_S ?? H)).
Cut {m:nat & {Hm:(Cle m n) & (P' m (Cle_to m n Hm))}}+(i:nat)(H:(le i n))(Q' i H).

Intro H3; Elim H3; Intro H4.

Left.
Elim H4; Intros m Hm; Elim Hm; Clear H4 Hm; Intros Hm Hm'.
Exists m.
Unfold P' in Hm'.
Exists (Cle_S ?? Hm).
EApply H with i:=m; [Omega | Apply Hm'].

Right.
Intros i H5.
Unfold Q' in H4.
Elim (le_lt_eq_dec ?? H5); Intro H6.

Cut (le i n); [Intro | Auto with arith].
EApply H0 with i:=i; [Auto with arith | Apply (H4 i H7)].

EApply H0 with i:=(S n); [Auto with arith | Apply H2].

Apply Hrecn.
Intro i; Intros j H3 H4 H5 H6.
Unfold P'.
Exact (H ?? H3 ?? H6).

Intro i; Intros j H3 H4 H5 H6.
Unfold Q'.
Exact (H0 ?? H3 ?? H6).

Intros i H3.
Unfold P' Q'; Apply H1.
Qed.

(* Begin_Tex_Verb *)
Lemma str_finite_or_elim : (n:nat)(P,Q:(i:nat)(le i n)->CProp)
  (nat_less_n_pred' ? P)->(nat_less_n_pred' ? Q)->
  ((i:nat)(H:(le i n))((P i H)+(Q i H)))->
  {j:nat & {Hj:(Cle j n) &
    (P j (Cle_to ?? Hj))*(j':nat)
      (Hj':(le j' n))(lt j' j)->(Q j' Hj')}}+
    (i:nat)(H:(le i n))(Q i H).
(* End_Tex_Verb *)
Intro n; Induction n.
Intros P Q H H0 H1.
Elim (H1 O (le_n O)); Intro HPQ.

Left.
Exists O; Exists (toCle ?? (le_n O)).
Split.

Apply H with H:=(le_n O); Auto.
Intros; ElimType False; Inversion H2.

Right; Intros.
Apply H0 with H:=(le_n O); Auto with arith.

Intros P Q H H0 H1.
LetTac P':=[i:nat][H:(le i n)](P i (le_S ?? H)).
LetTac Q':=[i:nat][H:(le i n)](Q i (le_S ?? H)).
Elim (Hrecn P' Q').

Intro H2.
Left.
Elim H2; Intros m Hm; Elim Hm; Clear H2 Hm; Intros Hm Hm'.
Exists m.
Unfold P' in Hm'.
Exists (Cle_S ?? Hm).
Elim Hm'; Clear Hm'; Intros Hm' Hj.
Split.

EApply H with i:=m; [Auto with arith | Apply Hm'].

Unfold Q' in Hj; Intros j' Hj' H2.
Cut (le m n); [Intro H3 | Exact (Cle_to ?? Hm)].
Cut (le j' n); [Intro H4 | Apply le_trans with m; Auto with arith].
Apply H0 with H:=(le_S ?? H4); [Auto | Apply Hj; Assumption].

Elim (H1 (S n) (Cle_to ?? (toCle ?? (le_n (S n))))); Intro H1'.

Intro H2.
Left; Exists (S n); Exists (toCle ?? (le_n (S n))); Split.

Assumption.

Intros j' Hj' H3; Unfold Q' in H1'.
Cut (le j' n); [Intro H4 | Auto with arith].
Unfold Q' in H2.
Apply H0 with H:=(le_S ?? H4); Auto.

Intro H2.
Right; Intros i H3.
Unfold Q' in H1'.
Elim (le_lt_eq_dec ?? H3); Intro H4.

Cut (le i n); [Intro H5 | Auto with arith].
Unfold Q' in H2.
Apply H0 with H:=(le_S ?? H5); Auto.

Apply H0 with H:=(Cle_to ?? (toCle ?? (le_n (S n)))); Auto.

Intro i; Intros j H2 H3 H4 H5.
Unfold P'.
Exact (H ?? H2 ?? H5).

Intro i; Intros j H2 H3 H4 H5.
Unfold Q'.
Exact (H0 ?? H2 ?? H5).

Intros i H2.
Unfold P' Q'.
Apply H1.
Qed.

End Predicates_to_CProp.

Section Predicates_to_Prop.

(* Tex_Prose
Finally, analogous results for \verb!Prop!-valued predicates are presented for completeness' sake.
*)

(* Begin_Tex_Verb *)
Lemma even_ind : (P:nat->Prop)(P O)->
  ((n:nat)(even n)->(P n)->(P (S (S n))))->
  (n:nat)(even n)->(P n).
(* End_Tex_Verb *)
Intros P H H0 n.
Pattern n; Apply lt_wf_ind.
Clear n.
Intros n H1 H2.
Induction n.

Auto.

Induction n.

ElimType False; Inversion H2; Inversion H4.

Apply H0.

Inversion H2; Inversion H4; Auto.

Apply H1.

Auto with arith.
Inversion H2; Inversion H4; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma odd_ind : (P:nat->Prop)(P (1))->
  ((n:nat)(P n)->(P (S (S n))))->
  (n:nat)(odd n)->(P n).
(* End_Tex_Verb *)
Intros P H H0 n; Case n.

Intro H1; ElimType False; Inversion H1.

Clear n; Intros n H1.
Pattern n; Apply even_ind; Auto.
Inversion H1; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nat_complete_double_ind : (P:nat->nat->Prop)
  ((m,n:nat)
    ((m',n':nat)(lt m' m)->(lt n' n)->(P m' n'))->(P m n))->
  (m,n:nat)(P m n).
(* End_Tex_Verb *)
Intros P H m.
Pattern m; Apply lt_wf_ind; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma four_ind : (P:nat->Prop)
  (P (0))->(P (1))->(P (2))->(P (3))->
  ((n:nat)(P n)->(P (S (S (S (S n))))))->(n:nat)(P n).
(* End_Tex_Verb *)
Intros.
Apply lt_wf_ind.
Intro m.
Case m; Auto.
Clear m; Intro m.
Case m; Auto.
Clear m; Intro m.
Case m; Auto.
Clear m; Intro m.
Case m; Auto with arith.
Qed.

End Predicates_to_Prop.

(* Tex_Prose
\section{Integers}

Similar results for integers.
*)

(* FIXME *)
Grammar tactic simple_tactic : tactic := 
  elimcompare 
  [ "ElimCompare" constrarg($c) constrarg($d) ] -> [ (ElimCompare $c $d) ].

(* Begin_Tex_Verb *)
Definition Zlts:=[x,y:Z](eqs fast_integer.relation (Zcompare x y) INFERIEUR). 
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Lemma toCProp_Zlt:(x,y:Z)`x < y`->(Zlts x y).
(* End_Tex_Verb *)
Proof.
 Intros x y H.
 Unfold Zlts.
 Unfold Zlt in H.
 Rewrite H.
 Apply Crefl_equal.
Qed.

(* Begin_Tex_Verb *)
Lemma CZlt_to:(x,y:Z)(Zlts x y)->`x<y`.
(* End_Tex_Verb *)
Proof.
 Intros x y H.
 Unfold Zlt.
 Inversion H.
 Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Zsgn_1:(x:Z){`(Zsgn x)=0`}+{`(Zsgn x)=1`}+{`(Zsgn x)=(-1)`}. 
(* End_Tex_Verb *)
Proof.
Intro x.
Case x.

Left.
Left.
Unfold Zsgn.
Reflexivity.

Intro p.
Simpl.
Left.
Right.
Reflexivity.

Intro p.
Right.
Simpl.
Reflexivity.
Qed.


(* Begin_Tex_Verb *)
Lemma Zsgn_2:(x:Z)`(Zsgn x)=0`->`x=0`.   
(* End_Tex_Verb *)
Proof.
 Intro x.
 Case x.

 Intro H.
 Reflexivity.

 Intros p H.
 Inversion H.

 Intros p H.
 Inversion H.
Qed.


(* Begin_Tex_Verb *)
Lemma Zsgn_3:(x:Z)`x<>0`->`(Zsgn x)<>0`.  
(* End_Tex_Verb *)
Proof.
 Intro x.
 Case x.

 Intro H.
 Elim H.
 Reflexivity.

 Intros p H.
 Simpl.
 Discriminate.

 Intros p H.
 Simpl.
 Discriminate.
Qed.

(* Tex_Prose
The following have unusual names, in line with the series of ZLn lemmata in {\tt fast\_integers.v}.
*)

(* Begin_Tex_Verb *)
Lemma  ZL9: (p:positive)(inject_nat (convert p))=(POS p). 
(* End_Tex_Verb *)
Proof.
Intro p.
Elim (ZL4 p).
Intros x H0.
Rewrite H0.
Unfold inject_nat.
Apply f_equal with A:=positive B:=Z f:=POS.
Cut ((anti_convert (convert p))=(anti_convert (S x))).

Intro H1.
Rewrite bij2 in H1.
Cut ((sub_un  (add_un p))=(sub_un (anti_convert (S x)))).

Intro H2.
Rewrite sub_add_one in H2.
Simpl in H2.
Rewrite sub_add_one in H2.
Auto.

Apply f_equal with A:=positive B:=positive f:=sub_un.
Assumption.

Apply f_equal with f:=anti_convert.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Theorem Zsgn_4:(a:Z)`a=(Zsgn a)*(absolu a)`. 
(* End_Tex_Verb *)
Proof.
 Intro a.
 Case a.

 Simpl.
 Reflexivity.

 Intro p.
 Unfold Zsgn.
 Unfold absolu.
 Rewrite Zmult_1_n.
 Symmetry.
 Apply ZL9.

 Intro p.
 Unfold Zsgn.
 Unfold absolu.
 Rewrite ZL9.
 Constructor.
Qed.

(* Begin_Tex_Verb *)
Theorem Zsgn_5: (a,b,x,y:Z)`x<>0`->`y<>0`-> 
                 `(Zsgn a)*x=(Zsgn b)*y`->`(Zsgn a)*y=(Zsgn b)*x`.  
(* End_Tex_Verb *)
Proof.
 Intros a b x y H H0.
 Case a.

 Case b.

  Simpl.
  Trivial.

  Intro p.
  Unfold Zsgn.
  Intro H1.
  Rewrite Zmult_1_n in H1.
  Simpl in H1.
  Elim H0.
  Auto.

  Intro p.
  Unfold Zsgn.
  Intro H1.
  Elim H0.
  Apply Zopp_intro.
  Simpl.
  Transitivity `(-1)*y`; Auto.

 Intro p.
 Unfold 1 Zsgn.
 Unfold 2 Zsgn.
 Intro H1.
 Transitivity y.

 Rewrite Zmult_1_n.
 Reflexivity.

 Transitivity `(Zsgn b)*((Zsgn b)*y)`.

 Case (Zsgn_1 b).

  Intro H2.
  Case H2.

  Intro H3.
  Elim H.
  Rewrite H3 in H1.
  Change `1*x=0` in H1.
  Rewrite Zmult_1_n in H1.
  Assumption.

  Intro H3.
  Rewrite H3.
  Rewrite Zmult_1_n.
  Rewrite Zmult_1_n.
  Reflexivity.

  Intro H2.
  Rewrite H2.
  Ring.

 Rewrite Zmult_1_n in H1.
 Rewrite H1.
 Reflexivity.

 Intro p.
 Unfold 1 Zsgn.
 Unfold 2 Zsgn.
 Intro H1.
 Transitivity `(Zsgn b)*((-1)*((Zsgn b)*y))`.

 Case (Zsgn_1 b).
  Intro H2.
  Case H2.

  Intro H3.
  Elim H.
  Apply Zopp_intro.
  Transitivity `(-1)*x`.

  Ring.
  Unfold Zopp.
  Rewrite H3 in H1.
  Transitivity `0*y`; Auto.

  Intro H3.
  Rewrite H3.
  Ring.

 Intro H2.
 Rewrite H2.
 Ring.

 Rewrite <- H1.
 Ring.
Qed.


(* Begin_Tex_Verb *)
Lemma nat_nat_pos:(m,n:nat)`(m+1)*(n+1)>0`.
(* End_Tex_Verb *)
Proof.
Intros m n.
Apply Zlt_gt.
Cut (`(inject_nat m)+1>0`).

Intro H.
Cut(`0<(inject_nat n)+1`).

Intro H0.
Cut (`(((inject_nat m)+1)*0) < ((inject_nat m)+1)*((inject_nat n)+1)`).

Rewrite Zero_mult_right.
Auto.

Apply Zlt_reg_mult_l; Auto.

Change (`0<(Zs (inject_nat n))`).
Apply Zle_lt_n_Sm.
Change (`(inject_nat O) <= (inject_nat n)`).
Apply inj_le.
Apply le_O_n.

Apply Zlt_gt.
Change (`0<(Zs (inject_nat m))`).
Apply Zle_lt_n_Sm.
Change (`(inject_nat O) <= (inject_nat m)`).
Apply inj_le.
Apply le_O_n.
Qed.

(* Begin_Tex_Verb *)
Theorem S_predn:(m:nat)(~(m=O))->(S (pred m))=m.
(* End_Tex_Verb *)
Proof.
Intros m H.
Symmetry.
Apply S_pred with O.
Omega.
Qed.

(* Begin_Tex_Verb *)
Lemma absolu_1:(x:Z)((absolu x)=O)->(`x=0`).
(* End_Tex_Verb *)
Proof.
Intros x H.
Case (dec_eq x `0`).

Auto.

Intro H0.
Apply False_ind.

ElimCompare x `0`.

Intro H2.
Apply H0.
Elim (Zcompare_EGAL x O).
Intros H3 H4.
Auto.

Intro H2.
Cut ((EX h:nat| (absolu x)=(S h))).

Intro H3.
Case H3.
Rewrite H.
Exact O_S.

Change (`x<0`) in H2.
LetTac H3:=(Zlt_gt ?? H2).
Elim (SUPERIEUR_POS ?? H3).
Intros x0 H5.
Cut (EX q:positive |x=(NEG q)).

Intro H6.
Case H6.
Intros x1 H7.
Rewrite H7.
Unfold absolu.
Generalize x1.
Exact ZL4.

Cut (x=(Zopp (POS x0))).

Simpl.
Intro H6.
Exists x0.
Assumption.
Rewrite <- (Zopp_Zopp x).
Exact (f_equal Z Z Zopp `-x` (POS x0) H5).

Intro H2.
Cut ((EX h:nat| (absolu x)=(S h))).

Intro H3.
Case H3.
Rewrite H.
Exact O_S.

Elim (SUPERIEUR_POS ?? H2).
Simpl.
Rewrite Zero_right.
Intros x0 H4.
Rewrite H4.
Unfold absolu.
Generalize x0.
Exact ZL4.
Qed.

(* Begin_Tex_Verb *)
Lemma absolu_2: (x:Z)(`x<>0`)->(~((absolu x)=O)).
(* End_Tex_Verb *)
Proof.
Intros x H.
Intro H0.
Apply H.
Apply absolu_1.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Zgt_mult_conv_absorb_l: (a,x,y:Z)`a<0`->`a*x>a*y`->`x<y`.
(* End_Tex_Verb *)
Proof.
Intros a x y H H0.
Case (dec_eq x y).

Intro H1.
Apply False_ind.
Rewrite H1 in H0.
Cut (`a*y=a*y`).

Change (`a*y<>a*y`).
Apply Zgt_not_eq.
Assumption.

Trivial.

Intro H1.
Case (not_Zeq x y H1).

Trivial.

Intro H2.
Apply False_ind.
Cut (`a*y>a*x`).

Apply Zgt_not_sym with m:=`a*y` n:=`a*x`.
Assumption.

Apply Zlt_conv_mult_l.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Zgt_mult_reg_absorb_l:(a,x,y:Z)`a>0`->`a*x>a*y`->`x>y`.
(* End_Tex_Verb *)
Proof.
Intros a x y H H0.
Cut (`(-a)<(Zopp 0)`).

Rewrite <- (Zopp_Zopp a) in H.
Rewrite <- (Zopp_Zopp `0`) in H.

Simpl.
Intro H1.
Rewrite <- (Zopp_Zopp x).
Rewrite <- (Zopp_Zopp y).
Apply Zlt_opp.
Apply Zgt_mult_conv_absorb_l with a:=`-a` x:=`-x`.

Assumption.

Rewrite Zopp_Zmult.
Rewrite Zopp_Zmult.
Apply Zlt_opp.
Rewrite <- Zopp_Zmult_r.
Rewrite <- Zopp_Zmult_r.
Apply Zgt_lt.
Apply Zlt_opp.
Apply Zgt_lt.
Assumption.

Omega.
Qed.

(* Begin_Tex_Verb *)
Lemma Zmult_Sm_Sn:(m,n:Z)`(m+1)*(n+1)=m*n+(m+n)+1`.
(* End_Tex_Verb *)
Proof.
Intros.
Ring.
Qed.
