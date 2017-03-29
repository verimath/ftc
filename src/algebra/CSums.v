(* $Id: CSums.v,v 1.13 2003/03/11 13:35:54 lcf Exp $ *)

Require Export CGroups.
Require Export PolyList.
Require Export Peano_dec.

(* Tex_Prose
\chapter{Sums}

\begin{convention}
Let \verb!G! be a group.
\end{convention}
*)

Section Sums.

Variable G : CGroup. (* Sum1 and Sum use subtraction *)

(* Begin_Tex_Verb *)
Fixpoint Sumlist [l:(list G)] : G :=
  Cases l of
    nil => (Zero::G)
  | (cons x k) => x[+](Sumlist k)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Fixpoint Sumx [n:nat] : ((i:nat)(lt i n)->G)->G :=
  <[n:nat](((i:nat)(lt i n)->G)->G)>
  Cases n of
    O => [_:(i:nat)(lt i O)->G](Zero::G)
  | (S m) => [f:(i:nat)(lt i (S m))->G]
      (Sumx m [i:nat][l:(lt i m)](f i (lt_S ? ? l)))
        [+](f m (lt_n_Sn m))
  end.
(* End_Tex_Verb *)

(* Tex_Prose
It is sometimes useful to view a function defined on $\{0,\ldots,i-1\}$ as a function on the natural numbers which evaluates to $0$ when the input is greater than or equal to $i$.
*)

(* Begin_Tex_Verb *)
Definition part_tot_nat_fun [n:nat][f:(i:nat)(lt i n)->G] : nat->G.
(* End_Tex_Verb *)
Intros n f i.
Elim (le_lt_dec n i).
 Intro a; Apply (Zero::G).
Intro b; Apply (f i b).
Defined.

(* Begin_Tex_Verb *)
Lemma part_tot_nat_fun_ch1 : (n:nat)(f:(i:nat)(lt i n)->G)
  (nat_less_n_fun ?? f)->
  (i:nat)(Hi:(lt i n))(part_tot_nat_fun n f i)[=](f i Hi).
(* End_Tex_Verb *)
Intros n f Hf i Hi.
Unfold part_tot_nat_fun.
Elim le_lt_dec; Intro.
 ElimType False; Apply (le_not_lt n i); Auto.
Simpl; Apply Hf; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma part_tot_nat_fun_ch2 : (n:nat)(f:(i:nat)(lt i n)->G)
  (i:nat)(Hi:(le n i))(part_tot_nat_fun n f i)[=]Zero.
(* End_Tex_Verb *)
Intros n f i Hi.
Unfold part_tot_nat_fun.
Elim le_lt_dec; Intro.
 Simpl; Algebra.
ElimType False; Apply (le_not_lt n i); Auto.
Qed.

(* Begin_Tex_Verb *)
Fixpoint Sum0 [n:nat] : (nat->G)->G := [f:nat->G]
(* Sum i=0..(n-1) *)
  Cases n of
    O => (Zero::G)
  | (S m) => (Sum0 m f)[+](f m)
  end.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Sum1 : nat->nat->(nat->G)->G :=
(* Sum i=m..(n-1) *)
  [m,n:nat][f:nat->G]((Sum0 n f)[-](Sum0 m f)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Sum : nat->nat->(nat->G)->G :=
(* Sum i=m..n *)
  [m,n:nat](Sum1 m (S n)).
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition Sum2 [m,n:nat][h:(i:nat)(le m i)->(le i n)->G] : G.
(* End_Tex_Verb *)
Intros m n h.
Apply (Sum m n).
Intro i.
Elim (le_lt_dec m i); Intro H.
 Elim (le_lt_dec i n); Intro H0.
  Apply (h i H H0).
 Apply (Zero::G).
Apply (Zero::G).
Defined.

(* Begin_Tex_Verb *)
Lemma Sum_one : (n:nat)(f:nat->G)(Sum n n f)[=](f n).
(* End_Tex_Verb *)
Intros n f.
Unfold Sum.
Unfold Sum1.
Simpl.
Step_final ((f n)[+](Sum0 n f))[-](Sum0 n f).
Qed.

Hints Resolve Sum_one : algebra.

(* Begin_Tex_Verb *)
Lemma Sum_empty : (n:nat)(f:nat->G)(lt O n)->
  (Sum n (pred n) f)[=]Zero.
(* End_Tex_Verb *)
Intros n f H.
Unfold Sum.
Rewrite <- (S_pred ?? H).
Unfold Sum1; Algebra.
Qed.

Hints Resolve Sum_empty : algebra.

(* Begin_Tex_Verb *)
Lemma Sum_Sum : (l,m,n:nat)(f:nat->G)
  (Sum l m f)[+](Sum (S m) n f)[=](Sum l n f).
(* End_Tex_Verb *)
Intros l m n f.
Unfold Sum.
Unfold Sum1.
Step ((Sum0 (S n) f)[-](Sum0 (S m) f))[+]((Sum0 (S m) f)[-](Sum0 l f)).
Step (((Sum0 (S n) f)[-](Sum0 (S m) f))[+](Sum0 (S m) f))[-](Sum0 l f).
Step ((Sum0 (S n) f)[-]((Sum0 (S m) f)[-](Sum0 (S m) f)))[-](Sum0 l f).
Step ((Sum0 (S n) f)[-]Zero)[-](Sum0 l f).
Step ((Sum0 (S n) f)[+][--]Zero)[-](Sum0 l f).
Step_final ((Sum0 (S n) f)[+]Zero)[-](Sum0 l f).
Qed.

Hints Resolve Sum_Sum : algebra.

(* Begin_Tex_Verb *)
Lemma Sum_first : (m,n:nat)(f:nat->G)
  (Sum m n f) [=] (f m)[+](Sum (S m) n f).
(* End_Tex_Verb *)
Intros m n f.
Unfold Sum.
Unfold Sum1.
Step_rht ((f m)[+](Sum0 (S n) f))[-](Sum0 (S m) f).
Step_rht ((Sum0 (S n) f)[+](f m))[-](Sum0 (S m) f).
Step_rht (Sum0 (S n) f)[+]((f m)[-](Sum0 (S m) f)).
Unfold cg_minus.
Apply bin_op_wd_unfolded.
Algebra.
Simpl.
Step_rht (f m)[+][--]((f m)[+](Sum0 m f)).
Step_rht (f m)[+]([--](f m)[+][--](Sum0 m f)).
Step_rht ((f m)[+][--](f m))[+][--](Sum0 m f).
Step_rht Zero[+][--](Sum0 m f).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_last : (m,n:nat)(f:nat->G)
  (Sum m (S n) f) [=] (Sum m n f)[+](f (S n)).
(* End_Tex_Verb *)
Intros m n f.
Unfold Sum.
Unfold Sum1.
Simpl.
Unfold cg_minus.
Step_lft (Sum0 n f)[+](f n)[+] ((f (S n))[+][--](Sum0 m f)).
Step_rht (Sum0 n f)[+](f n)[+] ([--](Sum0 m f)[+](f (S n))).
Algebra.
Qed.

Hints Resolve Sum_last : algebra.

(* Begin_Tex_Verb *)
Lemma Sum_last' : (m,n:nat)(f:nat->G)(lt O n) ->
  (Sum m n f) [=] (Sum m (pred n) f)[+](f n).
(* End_Tex_Verb *)
Intros m n f H. Induction n.
 Elim (lt_n_n (0) H).
Apply Sum_last.
Qed.

(* Tex_Prose
We add some extensionality results which will be quite useful when working with integration.
*)

(* Begin_Tex_Verb *)
Lemma Sum0_strext : 
  (f,g:?)(n:nat)((Sum0 n f)[#](Sum0 n g))->
  {i:nat | (lt i n) & ((f i)[#](g i))}.
(* End_Tex_Verb *)
Intros f g n H.
Induction n.
 Simpl in H.
 Elim (ap_irreflexive_unfolded ?? H).
Simpl in H.
Cut {i:nat | (lt i n) & ((f i)[#](g i))}+((f n)[#](g n)).
Intro H0.
Elim H0; Intro H1.
 Elim H1; Intros i H2 H3; Exists i; Auto with arith.
Exists n; Auto with arith.

Cut ((Sum0 n f)[#](Sum0 n g))+((f n)[#](g n)).
Intro H0; Elim H0; Intro H1.
 Left; Apply Hrecn; Assumption.
Auto.

Apply bin_op_strext_unfolded with (!csg_op G).
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_strext : (f,g:?)(m,n:nat)
  (le m (S n))->((Sum m n f)[#](Sum m n g))->
  {i:nat | (le m i)/\(le i n) & ((f i)[#](g i))}.
(* End_Tex_Verb *)
Intros f g m n H H0.
Induction n.
 Elim (le_lt_eq_dec ?? H); Intro H2.
  Cut m=O.
  Intro H1.
  Rewrite H1; Exists O; Auto.
  Rewrite H1 in H0.
  Step (Sum O O f); Stepr (Sum O O g); Assumption.

  Inversion H2; [Auto | Inversion H3].
 ElimType False.
 Cut O=(pred (1)); [Intro H3 | Auto].
 Rewrite H3 in H0.
 Rewrite H2 in H0.
 Apply (ap_irreflexive_unfolded G Zero).
 EApply ap_well_def_lft_unfolded.
  EApply ap_well_def_rht_unfolded.
   Apply H0.
  Apply Sum_empty; Auto.
 Apply Sum_empty; Auto.
Elim (le_lt_eq_dec ?? H); Intro Hmn.
 Cut ((Sum m n f)[#](Sum m n g))+((f (S n))[#](g (S n))).
 Intro H1; Elim H1; Intro H2.
  Cut {i:nat | (le m i)/\(le i n) & ((f i)[#](g i))}.
  Intro H3; Elim H3; Intros i H4 H5; Elim H4; Intros H6 H7; Clear H1 H4.
  Exists i; Try Split; Auto with arith.

  Apply Hrecn; Auto with arith.
 Exists (S n); Try Split; Auto with arith.

 Apply bin_op_strext_unfolded with (!csg_op G).
 Step (Sum m (S n) f); Stepr (Sum m (S n) g); Assumption.
Clear Hrecn.
ElimType False.
Cut (S n)=(pred (S (S n))); [Intro H1 | Auto].
Rewrite H1 in H0.
Rewrite Hmn in H0.
Apply (ap_irreflexive_unfolded G Zero).
EApply ap_well_def_lft_unfolded.
 EApply ap_well_def_rht_unfolded.
  Apply H0.
 Apply Sum_empty; Auto with arith.
Apply Sum_empty; Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_strext : (n:nat)(f,g:(i:nat)(lt i n)->G)
  (nat_less_n_fun ?? f)->(nat_less_n_fun ?? g)->
  ((Sumx ? f)[#](Sumx ? g))->
  {N:nat & {HN:(Clt N n) &
    (f N (Clt_to ?? HN))[#](g N (Clt_to ?? HN))}}.
(* End_Tex_Verb *)
Intro n; Induction n.
Intros f g H H0 H1.
Elim (ap_irreflexive_unfolded ?? H1).
Intros f g H H0 H1.
Simpl in H1.
Elim (bin_op_strext_unfolded ?????? H1); Clear H1; Intro H1.
 Cut (nat_less_n_fun ?? [i:nat][l:(lt i n)](f i (lt_S ?? l))); [Intro H2 | Red; Intros; Apply H; Assumption].
 Cut (nat_less_n_fun ?? [i:nat][l:(lt i n)](g i (lt_S ?? l))); [Intro H3 | Red; Intros; Apply H0; Assumption].
 Elim (Hrecn ?? H2 H3 H1); Intros N HN.
 Elim HN; Clear HN; Intros HN H'.
 Exists N.
 Cut (Clt N (S n)); [Intro H4 | Apply toCProp_lt; Apply lt_S; Apply Clt_to; Assumption].
 Exists H4.
 EApply ap_well_def_lft_unfolded.
  EApply ap_well_def_rht_unfolded.
   Apply H'.
  Algebra.
 Algebra.
Exists n.
Exists (toCProp_lt ?? (lt_n_Sn n)).
EApply ap_well_def_lft_unfolded.
 EApply ap_well_def_rht_unfolded.
  Apply H1.
 Algebra.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_strext' : (f,g:?)
  (n:nat)((Sum0 n f)[#](Sum0 n g))->
  {i:nat & ((f i)[#](g i))}.
(* End_Tex_Verb *)
Intros f g n H.
Elim (Sum0_strext ??? H); Intros i Hi Hi'; Exists i; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_strext' : (f,g:?)(m,n:nat)
  ((Sum m n f)[#](Sum m n g))->{i:nat & ((f i)[#](g i))}.
(* End_Tex_Verb *)
Intros f g m n H.
Unfold Sum Sum1 in H.
Elim (cg_minus_strext ????? H); Intro H1;
 Elim (Sum0_strext ??? H1);
 Intros i Hi Hi'; Exists i; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_wd : (m:nat)(f,f':nat->G)((i:nat)(f i)[=](f' i)) ->
                (Sum0 m f)[=](Sum0 m f').
(* End_Tex_Verb *)
Intros m f f' H. 
Elim m; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_wd : (m,n:nat)(f,f':nat->G)((i:nat)(f i)[=](f' i)) ->
               (Sum m n f)[=](Sum m n f').
(* End_Tex_Verb *)
Intros m n f f' H.
Unfold Sum.
Unfold Sum1.
Unfold cg_minus.
Apply bin_op_wd_unfolded.
 Apply Sum0_wd; Exact H.
Apply un_op_wd_unfolded.
Apply Sum0_wd; Exact H.
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_wd : (n:nat)(f,g:(i:nat)(lt i n)->G)
  ((i:nat)(H:(lt i n))(f i H)[=](g i H))->
  ((Sumx ? f)[=](Sumx ? g)).
(* End_Tex_Verb *)
Intro n; Elim n; Intros; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_wd' :
  (m,n:nat)(le m (S n)) -> (f,f':nat->G)
    ((i:nat)(le m i) -> (le i n) -> ((f i)[=](f' i))) ->
      (Sum m n f)[=](Sum m n f').
(* End_Tex_Verb *)
Intros m n. Induction n; Intros H f f' H0.
 Generalize (toCle ?? H); Clear H; Intro H.
 Inversion H.
  Unfold Sum. Unfold Sum1. Step_final (Zero::G).
 Inversion H2.
 Step (f (0)). Step_rht (f' (0)). Apply H0; Auto.
 Rewrite H3; Auto.
Elim (le_lt_eq_dec m (S (S n)) H); Intro H1.
 Step (Sum m n f)[+](f (S n)).
 Stepr (Sum m n f')[+](f' (S n)).
 Apply bin_op_wd_unfolded; Auto with arith.
Rewrite H1.
Unfold Sum. Unfold Sum1. Step_final (Zero::G).
Qed.

(* Begin_Tex_Verb *)
Lemma Sum2_wd : (m,n:nat)(le m (S n))->
  (f,g:(i:nat)(le m i)->(le i n)->G)
  ((i:nat)(Hm:(le m i))(Hn:(le i n))(f i Hm Hn)[=](g i Hm Hn))->
  (Sum2 ?? f)[=](Sum2 ?? g).
(* End_Tex_Verb *)
Intros m n H f g H0.
Unfold Sum2.
Apply Sum_wd'.
 Assumption.
Intros i H1 H2.
Elim le_lt_dec; Intro H3; [Simpl | ElimType False; Apply (le_not_lt i n); Auto].
Elim le_lt_dec; Intro H4; [Simpl | ElimType False; Apply (le_not_lt m i); Auto].
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_plus_Sum0 : (f,g:nat->G)(m:nat)
                     (Sum0 m [i:nat]((f i)[+](g i))) [=]
                     ((Sum0 m f) [+] (Sum0 m g)).
(* End_Tex_Verb *)
Intros f g m.
Elim m.
 Simpl; Algebra.
Intros n H.
Simpl.
Step (Sum0 n f)[+](Sum0 n g) [+] ((f n)[+](g n)).
Step (Sum0 n f)[+]((Sum0 n g) [+] ((f n)[+](g n))).
Step (Sum0 n f)[+]((Sum0 n g) [+] (f n)[+](g n)).
Step (Sum0 n f)[+]((f n) [+] (Sum0 n g)[+](g n)).
Step (Sum0 n f)[+]((f n) [+] (Sum0 n g))[+](g n).
Step_final (Sum0 n f)[+](f n) [+] (Sum0 n g)[+](g n).
Qed.
Hints Resolve Sum0_plus_Sum0 : algebra.

(* Begin_Tex_Verb *)
Lemma Sum_plus_Sum : (f,g:nat->G)(m,n:nat)
                     (Sum m n [i:nat]((f i)[+](g i))) [=]
                     ((Sum m n f) [+] (Sum m n g)).
(* End_Tex_Verb *)
Intros f g m n.
Unfold Sum.
Unfold Sum1.
Step_lft ((Sum0 (S n) f) [+] (Sum0 (S n) g))[-] ((Sum0 m f) [+](Sum0 m g)).
Step_lft ((((Sum0 (S n) f) [+] (Sum0 (S n) g)) [-] (Sum0 m f)) [-] (Sum0 m g)).
Unfold cg_minus.
Step_rht ((Sum0 (S n) f)[+][--](Sum0 m f)
            [+](Sum0 (S n) g))[+][--](Sum0 m g).
Apply bin_op_wd_unfolded.
 Step_lft (Sum0 (S n) f)[+]((Sum0 (S n) g)[+][--](Sum0 m f)).
 Step_lft (Sum0 (S n) f)[+]([--](Sum0 m f)[+](Sum0 (S n) g)).
 Algebra.
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_plus_Sumx : (n:nat)(f,g:(i:nat)(lt i n)->G)
  (Sumx ? f)[+](Sumx ? g)[=]
    (Sumx ? [i:nat][Hi:(lt i n)](f i Hi)[+](g i Hi)).
(* End_Tex_Verb *)
Intro n; Induction n.
 Intros; Simpl; Algebra.
Intros f g; Simpl.
Apply eq_transitive_unfolded with ((Sumx ? [i:nat][l:(lt i n)](f i (lt_S i n l)))[+](Sumx ? [i:nat][l:(lt i n)](g i (lt_S i n l))))[+]
  ((f n (lt_n_Sn n))[+](g n (lt_n_Sn n))).
 LetTac Sf:=(Sumx ? [i:nat][l:(lt i n)](f i (lt_S i n l))).
 LetTac Sg:=(Sumx ? [i:nat][l:(lt i n)](g i (lt_S i n l))).
 LetTac fn:=(f n (lt_n_Sn n)); LetTac gn:=(g n (lt_n_Sn n)).
 Step Sf[+]fn[+]Sg[+]gn.
 Step Sf[+](fn[+]Sg)[+]gn.
 Step Sf[+](Sg[+]fn)[+]gn.
 Step_final Sf[+]Sg[+]fn[+]gn.
Apply bin_op_wd_unfolded; Algebra.
Apply Hrecn with f:=[i:nat][l:(lt i n)](f i (lt_S i n l)) g:=[i:nat][l:(lt i n)](g i (lt_S i n l)).
Qed.

(* Begin_Tex_Verb *)
Lemma Sum2_plus_Sum2 : (m,n:nat)(le m (S n))->
  (f,g:(i:nat)(le m i)->(le i n)->G)
  (Sum2 ?? f)[+](Sum2 ?? g)[=]
    (Sum2 ?? [i,Hm,Hn:?](f i Hm Hn)[+](g i Hm Hn)).
(* End_Tex_Verb *)
Intros m n H f g.
Unfold Sum2; Simpl.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
 2: Apply Sum_plus_Sum.
Apply Sum_wd; Intro i.
Elim le_lt_dec; Intro H0; Simpl; Elim le_lt_dec; Intro H1; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_Sum0 : (f:nat->G)(n:nat)
                     (Sum0 n [i:nat]([--](f i))) [=]
                     ([--](Sum0 n f)).
(* End_Tex_Verb *)
Intros f n.
Induction n.
 Simpl; Algebra.
Simpl.
Step_final ([--](Sum0 n f)) [+] ([--](f n)).
Qed.

Hints Resolve inv_Sum0 : algebra.

(* Begin_Tex_Verb *)
Lemma inv_Sum : (f:nat->G)(m,n:nat)
                     (Sum m n [i:nat]([--](f i))) [=]
                     ([--](Sum m n f)).
(* End_Tex_Verb *)
Intros f a b.
Unfold Sum.
Unfold Sum1.
Step ([--](Sum0 (S b) f)) [-] ([--](Sum0 a f)).
Step ([--](Sum0 (S b) f)) [+] [--] ([--](Sum0 a f)).
Step_final [--]((Sum0 (S b) f) [+] ([--](Sum0 a f))).
Qed.

Hints Resolve inv_Sum : algebra.

(* Begin_Tex_Verb *)
Lemma inv_Sumx : (n:nat)(f:(i:nat)(lt i n)->G)
  [--](Sumx ? f)[=](Sumx ? [i:nat][Hi:(lt i n)][--](f i Hi)).
(* End_Tex_Verb *)
Intro n; Induction n.
 Simpl; Algebra.
Intro f; Simpl.
Step ([--](Sumx ? [i:nat][l:(lt i n)](f i (lt_S i n l))))[+]([--](f n (lt_n_Sn n))).
Apply bin_op_wd_unfolded.
 Apply Hrecn with f:=[i:nat][l:(lt i n)](f i (lt_S i n l)).
Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma inv_Sum2 : (m,n:nat)(le m (S n))->
  (f:(i:nat)(le m i)->(le i n)->G)
  [--](Sum2 ?? f)[=](Sum2 ?? [i,Hm,Hn:?][--](f i Hm Hn)).
(* End_Tex_Verb *)
Intros m n H f.
Unfold Sum2; Simpl.
Apply eq_symmetric_unfolded.
EApply eq_transitive_unfolded.
 2: Apply inv_Sum.
Apply Sum_wd; Intro i.
Elim le_lt_dec; Intro; Simpl; Elim le_lt_dec; Intro; Simpl; Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_minus_Sum : (f,g:nat->G)(m,n:nat)
                      (Sum m n [i:nat]((f i)[-](g i))) [=]
                      ((Sum m n f) [-] (Sum m n g)).
(* End_Tex_Verb *)
(* WHAT A MISERY TO PROVE THIS *)
Intros f g a b.
Step (Sum a b [i:nat]((f i)[+] ([--](g i)))).
Cut (Sum a b [i:nat]((f i)[+]( ([j:nat]([--](g j))) i))) [=]
    (Sum a b f)[+](Sum a b [j:nat]([--](g j))).
Intro H.
Step (Sum a b f)[+](Sum a b [j:nat]([--](g j))).
Step_final ((Sum a b f) [+][--] (Sum a b g)).

Change (Sum a b [i:nat]((f i)[+]( ([j:nat]([--](g j))) i))) [=]
       (Sum a b f)[+](Sum a b [j:nat]([--](g j))).
Apply Sum_plus_Sum.
Qed.

Hints Resolve Sum_minus_Sum : algebra.

(* Begin_Tex_Verb *)
Lemma Sumx_minus_Sumx : (n:nat)(f,g:(i:nat)(lt i n)->G)
  (Sumx ? f)[-](Sumx ? g)[=](Sumx ? [i,Hi:?](f i Hi)[-](g i Hi)).
(* End_Tex_Verb *)
Intros n f g; Unfold cg_minus.
EApply eq_transitive_unfolded.
 2: Apply Sumx_plus_Sumx with f:=f g:=[i:nat][Hi:(lt i n)][--](g i Hi).
Apply bin_op_wd_unfolded; Algebra.
Apply inv_Sumx.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum2_minus_Sum2 : (m,n:nat)(le m (S n))->
  (f,g:(i:nat)(le m i)->(le i n)->G)
  (Sum2 ?? f)[-](Sum2 ?? g)[=]
    (Sum2 ?? [i,Hm,Hn:?](f i Hm Hn)[-](g i Hm Hn)).
(* End_Tex_Verb *)
Intros m n H f g; Unfold cg_minus.
EApply eq_transitive_unfolded.
 2: Apply Sum2_plus_Sum2 with f:=f g:=[i:nat][Hm:(le m i)][Hn:(le i n)][--](g i Hm Hn); Assumption.
Apply bin_op_wd_unfolded.
 Algebra.
Apply inv_Sum2; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_apzero : (f:nat->G)(m,n:nat)(le m n) ->
  ((Sum m n f) [#] Zero) ->
    {i:nat | (le m i)/\(le i n) & ((f i) [#] Zero)}.
(* End_Tex_Verb *)
Intros a k l H H0. Induction l.
 Exists (0). Split; Auto. Cut k=O. 
 Intro H'. Rewrite H' in H0.
 Step (Sum (0) (0) a).
 Inversion H. Auto.
Elim (le_lt_eq_dec k (S l) H); Intro HH.
Cut ((Sum k l a) [#] Zero) + ((a (S l)) [#] Zero). Intro H1.
Elim H1; Clear H1; Intro H1.
 Elim Hrecl; Auto with arith.
 Intro i. Intros H2 H6. Exists i; Auto.
 Elim H2; Intros H3 H4; Auto.
Exists (S l); Try Split; Auto with arith.

Apply cg_add_ap_zero.
Apply ap_well_def_lft_unfolded with (Sum k (S l) a). Auto.
Apply Sum_last.

Rewrite HH in H0.
Exists (S l); Auto.
Step (Sum (S l) (S l) a).
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_zero : (f:nat->G)(m,n:nat)(le m (S n)) ->
  ((i:nat)(le m i) -> (le i n) -> (f i) [=] Zero) ->
    (Sum m n f) [=] Zero.
(* End_Tex_Verb *)
Intros a k l H H0. Induction l.
 Elim (le_lt_eq_dec ?? H); Clear H; Intro H.
  Replace k with O. Step (a O). Apply H0. Auto.
  Auto with arith. Auto. Inversion H. Auto. Inversion H2. 
 Rewrite H.
 Unfold Sum. Unfold Sum1. Algebra.
Elim (le_lt_eq_dec k (S (S l)) H); Intro HH.
 Step (Sum k l a)[+](a (S l)).
 Stepr Zero[+](Zero::G).
 Apply bin_op_wd_unfolded.
  Apply Hrecl; Auto with arith.
 Apply H0; Auto with arith.
Rewrite HH.
Unfold Sum. Unfold Sum1. Algebra.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum_term : (f:nat->G)(m,i,n:nat)(le m i) -> (le i n) ->
  ((j:nat)(le m j) -> (~j=i) -> (le j n) -> (f j) [=] Zero) ->
    (Sum m n f) [=] (f i).
(* End_Tex_Verb *)
Intros a k i0 l H H0 H1.
Step (Sum k i0 a)[+](Sum (S i0) l a).
Stepr (a i0)[+]Zero.
Apply bin_op_wd_unfolded.
 Elim (O_or_S i0); Intro H2.
  Elim H2; Intros m Hm.
  Rewrite <- Hm.
  Step (Sum k m a)[+](a (S m)).
  Stepr Zero[+](a (S m)).
  Apply bin_op_wd_unfolded.
   Apply Sum_zero. Rewrite Hm; Auto.
   Intros i H3 H4. Apply H1. Auto. Omega. Omega.
  Algebra.
 Rewrite <- H2 in H. Rewrite <- H2. 
 Generalize (toCle ?? H); Clear H; Intro H.
 Inversion H. Algebra.
Apply Sum_zero. Auto with arith.
Intros. Apply H1. Omega. Omega. Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma Sum0_shift : (f,g:nat->G)(n:nat)
  ((i:nat)((f i) [=] (g (S i)))) ->
    (g (0))[+](Sum0 n f) [=] (Sum0 (S n) g).
(* End_Tex_Verb *)
Intros a b l H. Induction l.
 Simpl; Algebra.
Simpl.
Step (b (0))[+](Sum0 l a)[+](a l).
Step_final (Sum0 (S l) b)[+](a l).
Qed.

Hints Resolve Sum0_shift : algebra.

(* Begin_Tex_Verb *)
Lemma Sum_shift : (f,g:nat->G)(m,n:nat)
  ((i:nat)((f i) [=] (g (S i)))) ->
    (Sum m n f) [=] (Sum (S m) (S n) g).
(* End_Tex_Verb *)
Unfold Sum. Unfold Sum1. Intros a b k l H.
Step (((Sum0 (S l) a)[+](b (0)))[-](b (0)))[-](Sum0 k a).
Step ((Sum0 (S l) a)[+](b (0)))[-]((b (0))[+](Sum0 k a)).
Step_final ((b (0))[+](Sum0 (S l) a))[-]((b (0))[+](Sum0 k a)).
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_Sum0 : (n,f,g:?)((i:nat)(Hi:(lt i n))
  (f i Hi)[=](g i))->(Sumx n f)[=](Sum0 n g).
(* End_Tex_Verb *)
Intro; Induction n; Simpl; Algebra.
Qed.

End Sums.

Implicits Sum [1].
Implicits Sum0 [1].
Implicits Sumx [1 2].
Implicits Sum2 [1 2 3].

Section More_Sums.

Variable G:CGroup.

(* Tex_Prose
The next results are useful for calculating some special Sums, often referred to as ``Mengolli Sums''.
*)

(* Begin_Tex_Verb *)
Lemma Mengolli_Sum : (n:nat)(f:(i:nat)(le i n)->G)
  (g:(i:nat)(lt i n)->G)(nat_less_n_fun' ?? f)->
  ((i:nat)(H:(lt i n))
    ((g i H)[=](f (S i) H)[-](f i (lt_le_weak ?? H))))->
  (Sumx g)[=]((f n (le_n n))[-](f O (le_O_n n))).
(* End_Tex_Verb *)
Intro n; Induction n; Intros f g Hf H; Simpl.
 Step (f O (le_n O))[-](f O (le_n O)).
 Apply cg_minus_wd; Algebra.
Apply eq_transitive_unfolded with ((f ? (le_n (S n)))[-](f ? (le_S ?? (le_n n))))[+]((f ? (le_S ?? (le_n n)))[-](f O (le_O_n (S n)))).
 EApply eq_transitive_unfolded.
  Apply cm_commutes_unfolded.
 Apply bin_op_wd_unfolded.
  EApply eq_transitive_unfolded.
   Apply H.
  Apply cg_minus_wd; Apply Hf; Algebra.
 LetTac f':=[i:nat][H:(le i n)](f i (le_S ?? H)).
 LetTac g':=[i:nat][H:(lt i n)](g i (lt_S ?? H)).
 Apply eq_transitive_unfolded with (f' n (le_n n))[-](f' O (le_O_n n)).
  Apply Hrecn.
   Red; Intros; Unfold f'; Apply Hf; Algebra.
  Intros i Hi.
  Unfold f'; Unfold g'.
  EApply eq_transitive_unfolded.
   Apply H.
  Apply cg_minus_wd; Apply Hf; Algebra.
 Unfold f'; Apply cg_minus_wd; Apply Hf; Algebra.
Stepr ((f (S n) (le_n (S n)))[+]Zero)[-](f O (le_O_n (S n))).
Stepr ((f (S n) (le_n (S n)))[+]([--](f n (le_S ?? (le_n n)))[+](f n (le_S ?? (le_n n)))))[-](f O (le_O_n (S n))).
Step_final (((f (S n) (le_n (S n)))[+][--](f n (le_S ?? (le_n n))))[+](f n (le_S ?? (le_n n))))[-](f O (le_O_n (S n))).
Qed.

(* Begin_Tex_Verb *)
Lemma Mengolli_Sum_gen : (f,g:nat->G)
  ((n:nat)(g n)[=]((f (S n))[-](f n)))->
  (m,n:nat)(le m (S n))->(Sum m n g)[=]((f (S n))[-](f m)).
(* End_Tex_Verb *)
Intros f g H m n; Induction n; Intro Hmn.
 Elim (le_lt_eq_dec ?? Hmn); Intro H0.
  Cut m=O; [Intro H1 | Inversion H0; Auto with arith; Inversion H2].
  Rewrite H1.
  EApply eq_transitive_unfolded; [Apply Sum_one | Apply H].
 Cut O=(pred (1)); [Intro H1 | Auto].
 Rewrite H0; Stepr (Zero::G); Rewrite H1; Apply Sum_empty.
 Auto with arith.
Simpl in Hmn; Elim (le_lt_eq_dec ?? Hmn); Intro H0.
 Apply eq_transitive_unfolded with ((f (S (S n)))[-](f (S n)))[+]((f (S n))[-](f m)).
  EApply eq_transitive_unfolded.
   Apply Sum_last.
  EApply eq_transitive_unfolded.
   Apply cm_commutes_unfolded.
  Apply bin_op_wd_unfolded; [Apply H | Apply Hrecn].
  Auto with arith.
 Stepr ((f (S (S n)))[+]Zero)[-](f m).
 Stepr ((f (S (S n)))[+]([--](f (S n))[+](f (S n))))[-](f m).
 Step_final (((f (S (S n)))[+][--](f (S n)))[+](f (S n)))[-](f m).
Rewrite H0.
Stepr (Zero::G).
Cut (S n)=(pred (S (S n))); [Intro H2 | Auto].
Rewrite H2; Apply Sum_empty.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma str_Mengolli_Sum_gen : (f,g:nat->G)(m,n:nat)(le m (S n))->
  ((i:nat)(le m i)->(le i n)->(g i)[=]((f (S i))[-](f i)))->
  (Sum m n g)[=]((f (S n))[-](f m)).
(* End_Tex_Verb *)
Intros f g m n H H0.
Apply eq_transitive_unfolded with (Sum m n [i:nat](f (S i))[-](f i)).
 Apply Sum_wd'; Assumption.
Apply Mengolli_Sum_gen; [Intro; Algebra | Assumption].
Qed.

(* Begin_Tex_Verb *)
Lemma Sumx_to_Sum : (n:nat)(lt O n)->(f:(i:nat)(lt i n)->G)
  (nat_less_n_fun ?? f)->
  (Sumx f)[=](Sum O (pred n) (part_tot_nat_fun ?? f)).
(* End_Tex_Verb *)
Intro n; Induction n; Intros H f Hf.
ElimType False; Inversion H.
Cut (le O n); [Intro H0 | Auto with arith].
Elim (le_lt_eq_dec ?? H0); Clear H H0; Intro H.
 Simpl.
 Pattern 6 n; Rewrite (S_pred ?? H).
 EApply eq_transitive_unfolded.
  2: Apply eq_symmetric_unfolded; Apply Sum_last.
 Apply bin_op_wd_unfolded.
  EApply eq_transitive_unfolded.
   Apply Hrecn; Auto.
   Red; Intros; Apply Hf; Auto.
  Apply Sum_wd'.
   Auto with arith.
  Intros i H1 H2.
  Cut (lt i n); [Intro | Omega].
  EApply eq_transitive_unfolded.
   Apply part_tot_nat_fun_ch1 with Hi:=H0.
   Red; Intros; Apply Hf; Auto.
  Apply eq_symmetric_unfolded.
  EApply eq_transitive_unfolded.
   Apply part_tot_nat_fun_ch1 with Hi:=(lt_S ?? H0).
   Red; Intros; Apply Hf; Auto.
  Algebra.
 Rewrite <- (S_pred ?? H).
Apply eq_symmetric_unfolded; Apply part_tot_nat_fun_ch1; Auto.
Generalize f Hf; Clear Hf f; Rewrite <- H.
Simpl; Intros f Hf.
EApply eq_transitive_unfolded.
 2: Apply eq_symmetric_unfolded; Apply Sum_one.
Step (f O (lt_n_Sn O)).
Apply eq_symmetric_unfolded; Apply part_tot_nat_fun_ch1; Auto.
Qed.

End More_Sums.

Hints Resolve Sum_one Sum_Sum Sum_first Sum_last Sum_last' Sum_wd
  Sum_plus_Sum: algebra.
Hints Resolve Sum_minus_Sum inv_Sum inv_Sum0 : algebra.
