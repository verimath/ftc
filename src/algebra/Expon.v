(* $Id: Expon.v,v 1.16 2003/03/11 13:35:54 lcf Exp $ *)

Require Export Arith.
Require Export COrdFields.

Load Transparent_algebra.

(* Tex_Prose
\chapter{Exponentiation}
\section{More properties about {\tt nexp}}
\begin{convention}
Let \verb!R! be an ordered field.
\end{convention}
*)
Section More_Nexp.

Variable R:COrdField.

(* Begin_Tex_Verb *)
Lemma nexp_resp_ap_zero : (x:R)(n:nat)(x[#]Zero)->(x[^]n [#] Zero).
(* End_Tex_Verb *)
Intros.
Elim n.
Simpl.
Algebra.
Intros.
Simpl.
Apply mult_resp_ap_zero.
Assumption.
Assumption.
Qed.

Hints Resolve nexp_resp_ap_zero : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_distr_div : (x,y:R)(n:nat)(H:y[#]Zero)(H1:y[^]n[#]Zero)
                       (x[/]y[//]H) [^] n [=] (x[^]n) [/] (y[^]n) [//] H1.
(* End_Tex_Verb *)
Induction n.
Intros.
Simpl.
Algebra.
Intros.
Simpl.
Generalize (H H0 (nexp_resp_ap_zero y n0 H0)); Intro.
Step  ((x[^]n0)[/](y[^]n0)[//](nexp_resp_ap_zero y n0 H0)) [*] (x[/]y[//]H0).
Simpl.
Rational.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_distr_div' : (x,y:R)(n:nat)(H:y[#]Zero)
  (x[/]y[//]H) [^] n [=] (x[^]n) [/] (y[^]n) [//] (nexp_resp_ap_zero y n H).
(* End_Tex_Verb *)
Intros.
Apply nexp_distr_div.
Qed.

(* Begin_Tex_Verb *)
Lemma small_nexp_resp_lt : (x:R)(m,n:nat)
            (Zero [<] x) -> (x [<] One) -> (lt m n) -> x[^]n [<] x[^]m.
(* End_Tex_Verb *)
Intros.
Cut (k:nat)(lt O k)-> x[^]k [<] One.
Intro.
Replace n with (plus m (minus n m)).
Step x[^]m [*] x[^](minus n m).
Stepr x[^]m [*] One.
Apply mult_resp_less_lft.
Apply H2.
Omega.
Apply nexp_resp_pos.
Assumption.
Auto with arith.
Induction k.
Intro.
ElimType False.
Inversion H2.
Intros.
Elim n0.
Step x.
Assumption.
Intros.
Step x[*](x[^](S n1)).
Stepr One[*](One::R).
Apply mult_resp_less_both.
Apply less_leEq.
Assumption.
Assumption.
Apply less_leEq.
Apply nexp_resp_pos.
Assumption.
Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma great_nexp_resp_lt : (x:R)(m,n:nat)
            (One [<] x) -> (lt m n) -> x[^]m [<] x[^]n.
(* End_Tex_Verb *)
Intros. Induction n; Intros.
ElimType False.
Inversion H0.
Cut (le m n). Intro.
Cut x[^]n [<] x[^](S n). Intro.
Elim (le_lt_eq_dec ? ? H1); Intro y.
Apply less_transitive_unfolded with x[^]n; Auto.
Rewrite y. Auto.
Step x[^]n[*]One.
Stepr x[^]n[*]x.
Apply mult_resp_less_lft. Auto.
Apply nexp_resp_pos.
Apply leEq_less_trans with (One::R). Apply less_leEq. Apply pos_one. Auto.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma small_nexp_resp_le : (x:R)(m,n:nat)
            (Zero [<=] x) -> (x [<=] One) -> (le m n) -> x[^]n [<=] x[^]m.
(* End_Tex_Verb *)
Intros.
Cut (k:nat) (x[^]k) [<=] One.
Intro.
Replace n with (plus m (minus n m)).
Step x[^]m [*] x[^](minus n m).
Stepr x[^]m [*] One.
Apply mult_resp_leEq_lft.
Apply H2.
Apply nexp_resp_nonneg. Auto.
Auto with arith.
Induction k.
Apply leEq_reflexive.
Clear H1 n; Intros.
Step x[^]n[*]x; Stepr (One::R)[*]One.
Apply mult_resp_leEq_both; Auto.
Apply nexp_resp_nonneg; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma great_nexp_resp_le : (x:R)(m,n:nat)
            (One [<=] x) -> (le m n) -> x[^]m [<=] x[^]n.
(* End_Tex_Verb *)
Intros.
Induction n; Intros.
Replace m with O.
Apply leEq_reflexive.
Auto with arith.
Elim (le_lt_eq_dec ?? H0); Intro.
Step x[^]m[*]One.
Stepr x[^]n[*]x.
Apply mult_resp_leEq_both; Auto with arith.
Apply nexp_resp_nonneg; Auto.
Apply leEq_transitive with (One::R); Auto.
Apply less_leEq. Apply pos_one.
Apply less_leEq. Apply pos_one.
Rewrite b. Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_resp_leEq :
  (x,y:R)(k:nat)(Zero [<=] x)->(x [<=] y)->(x[^]k [<=] y[^]k).
(* End_Tex_Verb *)
Unfold leEq. Intros. Intro. Apply H0.
Apply power_cancel_less with k; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_resp_leEq_one :
  (c:R)(Zero[<=]c)->(c[<=]One)->(n:nat)(c[^]n)[<=]One.
(* End_Tex_Verb *)
Induction n.
Red; Apply eq_imp_leEq.
Algebra.
Clear n; Intros.
Step c[^]n[*]c.
Stepr (One::R)[*]One.
Apply mult_resp_leEq_both; Auto.
Apply nexp_resp_nonneg; Assumption.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_resp_leEq_neg_even : (n:nat)(even n)->
  (x,y:R)(y[<=]Zero)->(x[<=]y)->(y[^]n[<=]x[^]n).
(* End_Tex_Verb *)
Do 2 Intro; Pattern n; Apply even_ind.
Intros; Simpl; Apply leEq_reflexive.
Clear H n; Intros.
Stepr x[^]n[*]x[*]x; Step y[^]n[*]y[*]y.
Stepr x[^]n[*](x[*]x); Step y[^]n[*](y[*]y).
Apply mult_resp_leEq_both.
EApply leEq_wdr.
2: Apply inv_nexp_even; Auto.
Apply nexp_resp_nonneg; Step [--](Zero::R); Apply inv_resp_leEq; Auto.
Stepr y[^](2); Apply sqr_nonneg.
Auto.
Step y[^](2); Stepr x[^](2).
EApply leEq_wdr.
2: Apply inv_nexp_even; Auto with arith.
EApply leEq_wdl.
2: Apply inv_nexp_even; Auto with arith.
Apply nexp_resp_leEq.
Step [--](Zero::R); Apply inv_resp_leEq; Auto.
Apply inv_resp_leEq; Auto.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_resp_leEq_neg_odd : (n:nat)(odd n)->
  (x,y:R)(y[<=]Zero)->(x[<=]y)->(x[^]n[<=]y[^]n).
(* End_Tex_Verb *)
Intro; Case n.
Intros; ElimType False; Inversion H.
Clear n; Intros.
Step x[^]n[*]x; Stepr y[^]n[*]y.
RStep [--](x[^]n[*][--]x); RStepr [--](y[^]n[*][--]y).
Apply inv_resp_leEq; Apply mult_resp_leEq_both.
EApply leEq_wdr.
2: Apply inv_nexp_even; Inversion H; Auto.
Apply nexp_resp_nonneg; Step [--](Zero::R); Apply inv_resp_leEq; Auto.
Step [--](Zero::R); Apply inv_resp_leEq; Auto.
Apply nexp_resp_leEq_neg_even; Auto; Inversion H; Auto.
Apply inv_resp_leEq; Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_distr_recip : (x:R)(n:nat)(H:x[#]Zero)(H1:x[^]n[#]Zero)
                         (One[/]x[//]H)[^]n [=] One[/](x[^]n)[//]H1.
(* End_Tex_Verb *)
Intros. Induction n; Intros.
Simpl. Algebra.
Step (One[/]x[//]H)[^]n[*](One[/]x[//]H).
Cut x[^]n [#] Zero. Intro.
Step (One[/](x[^]n)[//]H0)[*](One[/]x[//]H).
Cut x[^]n[*]x [#] Zero. Intro.
RStep One[/](x[^]n[*]x)[//]H2.
Apply div_wd; Algebra.
Apply mult_resp_ap_zero; Auto.
Apply nexp_resp_ap_zero. Auto.
Qed.

Hints Resolve nexp_distr_recip : algebra.

(* Begin_Tex_Verb *)
Lemma nexp_even_nonneg : (n:nat)(even n)->(x:R)(Zero[<=]x[^]n).
(* End_Tex_Verb *)
Do 2 Intro.
Pattern n; Apply even_ind; Intros.
Simpl; Apply less_leEq; Apply pos_one.
Apply leEq_wdr with x[^]n0[*](x[^](2)).
2: Simpl; Rational.
Apply mult_resp_nonneg.
Auto.
Apply sqr_nonneg.
Auto.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_resp_le' : (c:R)(Zero[<=]c)->(c[<=]One)->
  (m,n:nat)(le m n)->(c[^]n)[<=](c[^]m).
(* End_Tex_Verb *)
Intros.
Step Zero[+]c[^]n; Apply shift_plus_leEq.
LetTac N:=(minus n m).
Apply leEq_wdr with c[^]m[-]c[^]m[*]c[^]N.
RStepr (c[^]m)[*](One[-](c[^]N)).
Step (Zero::R)[*]Zero; Apply mult_resp_leEq_both; Try Apply leEq_reflexive.
Apply nexp_resp_nonneg; Auto.
Apply shift_leEq_minus.
Step c[^]N.
Apply nexp_resp_leEq_one; Assumption.
Apply cg_minus_wd.
Algebra.
EApply eq_transitive_unfolded.
Apply nexp_plus.
Replace n with (plus m (minus n m)).
Algebra.
Auto with arith.
Qed.

(* Begin_Tex_Verb *)
Lemma nexp_resp_le : (c:R)(One[<=]c)->
  (m,n:nat)(le m n)->(c[^]m)[<=](c[^]n).
(* End_Tex_Verb *)
Intros.
Cut Zero[<]c; Intros.
2: Apply less_leEq_trans with (One::R); [Apply pos_one | Assumption].
Cut (c[#]Zero); Intros.
2: Apply Greater_imp_ap; Assumption.
Cut (n:nat)(c[^]n[#]Zero); Intros.
2: Apply nexp_resp_ap_zero; Assumption.
Cut (n:nat)(One[/]?[//](H3 n))[#]Zero; Intros.
2: Apply div_resp_ap_zero_rev; Apply one_ap_zero.
RStep One[/]?[//](H4 m).
RStepr One[/]?[//](H4 n).
Apply recip_resp_leEq.
Apply recip_resp_pos; Apply nexp_resp_pos; Assumption.
EApply leEq_wdl.
2: Apply nexp_distr_recip with H:=H2.
EApply leEq_wdr.
2: Apply nexp_distr_recip with H:=H2.
Apply nexp_resp_le'.
Apply less_leEq. Apply recip_resp_pos; Assumption.
Apply shift_div_leEq.
Assumption.
Stepr c; Assumption.
Assumption.
Qed.

End More_Nexp.

Hints Resolve nexp_distr_div nexp_distr_recip : algebra.

Implicits nexp_resp_ap_zero [1 2].

(* Tex_Prose
\section{Definition of {\tt zexp} : integer exponentiation}
\begin{convention}
Let \verb!R! be an ordered field.
\end{convention}
*)

Section Zexp_def.

Variable R : CField.

(* Tex_Prose
It would be nicer to define \verb!zexp! using \verb!caseZdiff!, but we already
have most properties now.
*)

(* Begin_Tex_Verb *)
Definition zexp [x:R; x_:(x[#]Zero); n:Z] : R :=
         Cases n of
           ZERO => (One::R)
         | (POS p) => x [^] (convert p)
         | (NEG p) => (One[/]x[//]x_) [^] (convert p)
         end.
(* End_Tex_Verb *)

End Zexp_def.

(* Tex_Prose
\begin{notation}
\hypertarget{Operator_27}{}\verb!a [^^] b! stands for \verb!zexp ? a b!.
\end{notation}
*)

Implicits zexp [1].
Notation "( x [//] Hx ) [^^] n" := (zexp x Hx n) (at level 0).

Syntax constr level 6:
  zexp_nifix [(zexp $e1 $e2 $e3)] ->
    [[ <hov 1> "(" $e1:E [0 1]  "[//]" $e2 ")" "[^^]" $e3:L]].

(* Tex_Prose
\section{Properties of {\tt zexp}}
\begin{convention}
Let \verb!R! be an ordered field.
\end{convention}
*)

Section Zexp_properties.

Variable R:COrdField.

(* Begin_Tex_Verb *)
Lemma zexp_zero : (x:R)(Hx:x[#]Zero) ((x[//]Hx) [^^] `0`) [=] One.
(* End_Tex_Verb *)
Intros.
Unfold zexp.
Algebra.
Qed.

Hints Resolve zexp_zero : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_nexp : (x:R)(Hx:x[#]Zero)(n:nat)
                  ((x[//]Hx) [^^] n) [=] (x [^] n).
(* End_Tex_Verb *)
Intros.
Unfold zexp.
Simpl.
Elim n.
Simpl.
Algebra.
Intros.
Simpl.
Rewrite bij1.
Simpl.
Algebra.
Qed.

Hints Resolve zexp_nexp : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_inv_nexp : (x:R)(Hx:x[#]Zero)(n:nat)
                      ((x[//]Hx) [^^] `-n`) [=] ((One[/]x[//]Hx) [^] n).
(* End_Tex_Verb *)
Intros.
Unfold zexp.
Simpl.
Elim n.
Simpl.
Algebra.
Intros.
Simpl.
Rewrite bij1.
Simpl.
Algebra.
Qed.

Hints Resolve zexp_inv_nexp : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_inv_nexp' : (x:R)(n:nat)(Hx:x[#]Zero)(H1:x[^]n[#]Zero)
                       ((x[//]Hx) [^^] `-n`) [=] (One[/](x [^] n)[//]H1).
(* End_Tex_Verb *)
Intros.
Step (One [/] x [//] Hx) [^] `n`.
Stepr ((One[^]n)[/](x[^]n)[//]H1).
Apply nexp_distr_div.
Qed.

Hints Resolve zexp_inv_nexp' : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_strong_ext : (x,y:R)(m:Z)(Hx:x[#]Zero)(Hy:y[#]Zero)
                       ((x[//]Hx)[^^]m [#] (y[//]Hy)[^^] m) ->
                       x [#] y.
(* End_Tex_Verb *)
Intros x y m Hx Hy.
Pattern m.
Apply Cnats_Z_ind.
Intros.
Apply (nexp_strong_ext R n).
Change (x[^]n) [#] (y[^]n).
Step (x[//]Hx)[^^](n).
Stepr (y[//]Hy)[^^](n).
Intros.
Apply (nexp_strong_ext R n).
Change (x[^]n) [#] (y[^]n).
Cut One[/](x[^]n) [//] (nexp_resp_ap_zero n Hx) [#]
    One[/](y[^]n) [//] (nexp_resp_ap_zero n Hy).
Intro.
Generalize (div_strong_ext ? ? ? ? ? ? ? H0); Intro.
Elim H1; Intros H2.
Elim (ap_irreflexive_unfolded ? ? H2).
Assumption.
Step (x[//]Hx)[^^]`-n`.
Stepr (y[//]Hy)[^^]`-n`.
Qed.

(* Begin_Tex_Verb *)
Lemma zexp_well_def : (x,y:R)(m:Z)(Hx:x[#]Zero)(Hy:y[#]Zero)(x [=] y) ->
                       ((x[//]Hx)[^^]m [=] (y[//]Hy)[^^] m).
(* End_Tex_Verb *)
Intros.
Apply not_ap_imp_eq.
Intro.
Generalize (zexp_strong_ext ? ? ? ? ? H0); Intro.
Apply (eq_imp_not_ap ? ? ? H).
Assumption.
Qed.

Hints Resolve zexp_well_def : algebra_c.

(* Begin_Tex_Verb *)
Lemma zexp_plus1 : (x:R)(Hx:x[#]Zero)(m:Z)
                   ((x[//]Hx) [^^] `m+1`) [=] ((x[//]Hx) [^^] m) [*] x.
(* End_Tex_Verb *)
Intros.
Pattern m.
Apply nats_Z_ind.
Intro.
Replace `(inject_nat n)+1` with ((S n)::Z).
Step x[^](S n).
Stepr x[^]n [*] x.
Algebra.
Rewrite inj_S.
Reflexivity.
Intros.
Induction n.
Simpl.
Algebra.
Replace `(-(inject_nat (S n)))+1` with `-n`.
Step  (One [/] x[//]Hx) [^] n.
Stepr  (One [/] x[//]Hx) [^] (S n) [*] x.
Simpl.
Rational.
Rewrite inj_S.
Replace `(Zs (inject_nat n))` with `1+(inject_nat n)`.
Rewrite Zopp_Zplus.
Rewrite Zplus_sym.
Unfold 2 Zopp.
Rewrite Zplus_assoc.
Reflexivity.
Unfold Zs.
Apply Zplus_sym.
Qed.

Hints Resolve zexp_plus1: algebra.

(* Begin_Tex_Verb *)
Lemma zexp_resp_ap_zero : (x:R)(m:Z)(Hx:x[#]Zero)((x[//]Hx) [^^] m) [#] Zero.
(* End_Tex_Verb *)
Intros.
Pattern m.
Apply Cnats_Z_ind.
Intros.
Step x[^]n.
Apply nexp_resp_ap_zero.
Assumption.
Intro.
Step (One[/]x[//]Hx)[^]n.
Apply nexp_resp_ap_zero.
Apply div_resp_ap_zero_rev.
Algebra.
Qed.

Hints Resolve zexp_resp_ap_zero : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_inv : (x:R)(Hx:x[#]Zero)(m:Z)(Hexp: (x[//]Hx) [^^] m [#] Zero)
   ((x[//]Hx) [^^] `-m`) [=] One[/] ((x[//]Hx) [^^] m) [//] Hexp.
(* End_Tex_Verb *)
Intros x Hx m.
Pattern m.
Apply nats_Z_ind.
Intros.
(* Here I would like to use Rewrite zexp_inv_nexp', i.e. Rewriting with our
   own equality. *)
Apply eq_transitive_unfolded with (One[/](x [^] n)[//](nexp_resp_ap_zero n Hx)).
Apply zexp_inv_nexp'.
Apply div_wd.
Algebra.
Algebra.

Intros.
Rewrite Zopp_Zopp.
Step x[^]n.
Step (x[^]n) [/]OneNZ.
Apply eq_div.
Step x[^]n[*] ((One[/]x[//]Hx)[^]n).
Step  (x[*](One[/]x[//]Hx))[^]n.
Stepr (One::R).
Stepr (One::R)[^]n.
Apply nexp_wd.
Algebra.
Qed.

Hints Resolve zexp_inv : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_inv1 : (x:R)(Hx:x[#]Zero)(m:Z)
                   ((x[//]Hx) [^^] `m-1`) [=] ((x[//]Hx) [^^] m) [/] x [//] Hx.
(* End_Tex_Verb *)
Intros.
Replace `m-1` with `-((-m)+1)`.
(* Here I would like to use Rewriting with our own equality. *)
Step One[/] ((x[//]Hx) [^^] `(-m)+1`) [//] (zexp_resp_ap_zero x `(-m)+1` Hx).
Apply eq_div.
Stepr (x[//]Hx)[^^]m[*]((x[//]Hx)[^^](`-m`)[*]x).
Stepr (x[//]Hx)[^^]m[*]((One[/] ((x[//]Hx)[^^]m) [//] (zexp_resp_ap_zero x m Hx))[*]x).
Rational.
Rewrite Zopp_Zplus.
Rewrite Zopp_Zopp.
Reflexivity.
Qed.

Hints Resolve zexp_inv1 : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_plus : (x:R)(Hx:x[#]Zero)(m,n:Z)
              ((x[//]Hx) [^^] `m+n`) [=] ((x[//]Hx) [^^] m [*] (x[//]Hx) [^^]n).
(* End_Tex_Verb *)
Intros.
Pattern n.
Apply pred_succ_Z_ind.
Simpl.
Replace `m+0` with m.
Algebra.
Auto with zarith.
Intros.
Replace `m+(n0+1)` with `(m+n0)+1`.
Step  (x[//]Hx)[^^](`m+n0`) [*] x.
Stepr  (x[//]Hx)[^^]m[*]((x[//]Hx)[^^]n0 [*] x).
Stepr  (x[//]Hx)[^^]m[*](x[//]Hx)[^^]n0 [*] x.
Algebra.
Auto with zarith.
Intros.
Replace `m+(n0-1)` with `(m+n0)-1`.
Step  ((x[//]Hx)[^^](`m+n0`)) [/] x [//] Hx.
Stepr  ((x[//]Hx)[^^]m)[*](((x[//]Hx)[^^]n0) [/] x[//]Hx).
Stepr  (((x[//]Hx)[^^]m)[*]((x[//]Hx)[^^]n0)) [/] x[//]Hx.
Algebra.
Unfold Zminus.
Auto with zarith.
Qed.

Hints Resolve zexp_plus : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_minus : (x:R)(Hx:x[#]Zero)(m,n:Z)(Hexp : (x[//]Hx) [^^] n [#] Zero)
   ((x[//]Hx) [^^] `m-n`) [=]
   (((x[//]Hx) [^^] m) [/] ((x[//]Hx) [^^] n) [//] Hexp).
(* End_Tex_Verb *)
Intros.
Replace `m-n` with `m+(-n)`.
Step ((x[//]Hx) [^^] m [*] (x[//]Hx) [^^]`-n`).
Step ((x[//]Hx) [^^] m [*] (One [/] ((x[//]Hx) [^^]`n`) [//] Hexp)).
Step (((x[//]Hx) [^^] m [*] One) [/] ((x[//]Hx) [^^]`n`) [//] Hexp).
Algebra.
Reflexivity.
Qed.

Hints Resolve zexp_minus : algebra.

(* Begin_Tex_Verb *)
Lemma one_zexp : (z:Z)((One[//](ring_non_triv ?)) [^^] z [=] (One::R)).
(* End_Tex_Verb *)
Intro.
Pattern z.
Apply nats_Z_ind.
Intro.
(* Rewrite would be nice *)
Step (One::R)[^]n.
Apply one_nexp.
Intros.
Step One[/]((One[//](ring_non_triv ?))[^^]n)[//](zexp_resp_ap_zero One n (ring_non_triv ?)).
Stepr (One::R)[/]OneNZ.
Apply eq_div.
Stepr (One::R)[*]One[^]n.
Stepr (One::R)[*]One.
Algebra.
Qed.

Hints Resolve one_zexp : algebra.

(* Begin_Tex_Verb *)
Lemma mult_zexp : (x,y:R)(z:Z)(Hx:x[#]Zero)(Hy:y[#]Zero)(Hp:x[*]y[#]Zero)
                  ((x[*]y) [//] Hp) [^^] z [=]
                  (x[//]Hx) [^^] z [*] (y[//]Hy) [^^] z.
(* End_Tex_Verb *)
Intros.
Pattern z.
Apply nats_Z_ind.
Intros.
Step (x[*]y)[^]n.
Stepr x[^]n [*] y[^]n.
Apply mult_nexp.
Intros.
Step One[/] (((x[*]y)[//]Hp)[^^]n) [//] (zexp_resp_ap_zero (x[*]y) n Hp).
Stepr One[/] ((x[//]Hx)[^^]n) [//] (zexp_resp_ap_zero x n Hx) [*]
         (One[/] ((y[//]Hy)[^^]n) [//] (zexp_resp_ap_zero y n Hy)).
Step One[/] ((x[*]y)[^]n) [//] (nexp_resp_ap_zero n Hp).
Stepr One[/] (x[^]n) [//] (nexp_resp_ap_zero n Hx) [*]
         (One[/] (y[^]n) [//] (nexp_resp_ap_zero n Hy)).
RStepr One[/] ((x[^]n) [*] (y[^]n)) [//]
     (mult_resp_ap_zero ? ? ? (nexp_resp_ap_zero n Hx) (nexp_resp_ap_zero n Hy)).
Apply eq_div.
Algebra.
Qed.

Hints Resolve mult_zexp : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_mult :  (x:R)(m,n:Z)(Hx:x[#]Zero)(He:(x[//]Hx)[^^]m [#] Zero)
                  (x[//]Hx) [^^] `m*n` [=]
                  (((x[//]Hx) [^^] m) [//] He) [^^] n.
(* End_Tex_Verb *)
Intros.
Pattern n.
Apply pred_succ_Z_ind.
Rewrite <- Zmult_n_O.
Algebra.
Intros.
Rewrite Zmult_plus_distr_r.
Stepr ((x[//]Hx)[^^]m[//]He)[^^]`n0` [*] (x[//]Hx)[^^]m.
Rewrite Zmult_n_1.
Step (x[//]Hx)[^^]`m*n0` [*] (x[//]Hx) [^^]m.
Algebra.

Intros.
Rewrite Zmult_minus_distr_r.
Stepr (((x[//]Hx)[^^]m[//]He)[^^]`n0`) [/] ((x[//]Hx)[^^]m)[//]He.
Rewrite Zmult_n_1.
Step ((x[//]Hx)[^^]`m*n0`) [/] ((x[//]Hx) [^^]m)[//]He.
Algebra.
Qed.

Hints Resolve zexp_mult : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_two : (x:R)(Hx:x[#]Zero)(x[//]Hx) [^^] `2` [=] x[*]x.
(* End_Tex_Verb *)
Intros.
Simpl.
Algebra.
Qed.

Hints Resolve zexp_two : algebra.

(* Begin_Tex_Verb *)
Lemma inv_zexp_even : (x:R)(m:Z)(Zeven m)->(Hx:x[#]Zero)(Hneg:[--]x[#]Zero)
                  ([--]x[//]Hneg) [^^] m [=] (x[//]Hx) [^^] m.
(* End_Tex_Verb *)
Intros.
Pattern m.
Rewrite Zeven_div2.
Step ((([--]x[//]Hneg)[^^]`2`) [//] (zexp_resp_ap_zero ([--]x) `2` Hneg)) [^^] (Zdiv2 m).
Step ((([--]x)[*]([--]x)) [//] (mult_resp_ap_zero ? ? ? Hneg Hneg))[^^](Zdiv2 m).
Step ((x[*]x) [//] (mult_resp_ap_zero ? ? ? Hx Hx)) [^^](Zdiv2 m).
Step ((x[//]Hx)[^^]`2` [//] (zexp_resp_ap_zero x `2` Hx)) [^^] (Zdiv2 m).
Algebra.
Assumption.
Qed.

Hints Resolve inv_zexp_even : algebra.

(* Begin_Tex_Verb *)
Lemma inv_zexp_two : (x:R)(Hx:x[#]Zero)(Hneg:[--]x[#]Zero)
                     ([--]x[//]Hneg) [^^] `2` [=] (x[//]Hx) [^^] `2`.
(* End_Tex_Verb *)
Intros.
Apply inv_zexp_even.
Simpl.
Auto.
Qed.

Hints Resolve inv_zexp_two : algebra.

(* Begin_Tex_Verb *)
Lemma inv_zexp_odd : (x:R)(m:Z)(Zodd m)->(Hx:x[#]Zero)(Hneg:[--]x[#]Zero)
                  ([--]x[//]Hneg) [^^] m [=] [--]((x[//]Hx) [^^] m).
(* End_Tex_Verb *)
Intros.
Replace m with `(m-1)+1`.
Step  (([--]x[//]Hneg)[^^]`m-1`) [*] [--]x.
Stepr [--]((x[//]Hx)[^^]`m-1`[*]x).
RStepr ((x[//]Hx)[^^]`m-1`[*][--]x).
Apply mult_wd.
Apply inv_zexp_even.
Apply Zodd_Zeven_min1.
Assumption.
Simpl.
Auto.
Algebra.
Change `m+(-1)+1=m`.
Rewrite <- Zplus_assoc.
Simpl.
Rewrite <- Zplus_n_O.
Reflexivity.
Qed.

(* Begin_Tex_Verb *)
Lemma zexp_one : (x:R)(Hx:x[#]Zero)(x[//]Hx)[^^]`1` [=] x.
(* End_Tex_Verb *)
Intros.
Simpl.
Algebra.
Qed.

Hints Resolve zexp_one : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_funny : (x,y:R)(Hx:x[#]Zero)(Hy:y[#]Zero)
                   (x[+]y) [*] (x[-]y) [=]
                   (x[//]Hx)[^^]`2` [-] (y[//]Hy)[^^]`2`.
(* End_Tex_Verb *)
Intros.
Stepr x[*]x [-] y[*]y.
Rational.
Qed.

Hints Resolve zexp_funny : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_funny' : (x,y:R)(Hx:x[#]Zero)(Hy:y[#]Zero)
                    (x[-]y) [*] (x[+]y) [=]
                    (x[//]Hx)[^^]`2` [-] (y[//]Hy)[^^]`2`.
(* End_Tex_Verb *)
Intros.
Step (x[+]y) [*] (x[-]y).
Apply zexp_funny.
Qed.

Hints Resolve zexp_funny' : algebra.

(* Begin_Tex_Verb *)
Lemma zexp_pos : (x:R)(Hx:x[#]Zero)(z:Z)(Zero [<] x) ->
                 (Zero [<] (x[//]Hx) [^^] z).
(* End_Tex_Verb *)
Intros.
Pattern z.
Apply Cnats_Z_ind.
Intros.
Stepr x[^]n.
Apply nexp_resp_pos.
Assumption.
Intros.
Stepr One[/] (x[^]n) [//] (nexp_resp_ap_zero n Hx).
Apply div_resp_pos.
Apply nexp_resp_pos.
Assumption.
Apply pos_one.
Qed.

End Zexp_properties.

Hints Resolve nexp_resp_ap_zero zexp_zero zexp_nexp zexp_inv_nexp zexp_inv_nexp'
              zexp_plus1 zexp_resp_ap_zero zexp_inv zexp_inv1 zexp_plus zexp_minus
              one_zexp mult_zexp zexp_mult zexp_two inv_zexp_even inv_zexp_two
              zexp_one zexp_funny zexp_funny' : algebra.

Hints Resolve zexp_well_def : algebra_c.

Section Root_Unique.

Variable R:COrdField.

(* Begin_Tex_Verb *)
Lemma root_unique :
  (x,y:R)(Zero [<=] x) -> (Zero [<=] y) -> (n:nat)(lt (0) n) ->
    (x[^]n [=] y[^]n) -> (x [=] y).
(* End_Tex_Verb *)
Intros.
Apply leEq_imp_eq.
Apply power_cancel_leEq with n; Auto.
Stepr x[^]n.
Apply leEq_reflexive.
Apply power_cancel_leEq with n; Auto.
Step x[^]n.
Apply leEq_reflexive.
Qed.

(* Begin_Tex_Verb *)
Lemma root_one :
  (x:R)(Zero [<=] x) -> (n:nat)(lt (0) n) -> (x[^]n [=] One) -> (x [=] One).
(* End_Tex_Verb *)
Intros.
Apply root_unique with n; Auto.
Apply less_leEq. Apply pos_one.
Step_final (One::R).
Qed.

End Root_Unique.
