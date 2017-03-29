(* $Id: RealFuncts.v,v 1.7 2003/03/11 13:36:18 lcf Exp $ *)

Require Export CReals1.

(* Tex_Prose
\chapter{Functions on Reals}
*)

Implicit Arguments On.

Section Continuity.
Variable  f: (CSetoid_un_op IR).
Variable  f2: (CSetoid_bin_op IR).

(* Tex_Prose
\section{Continuity}
Let \verb!f! be a unary setoid operation on \verb!IR! and
let \verb!f2! be a binary setoid operation on \verb!IR!.

We use the following notations for intervals. \verb!Intclr a b! for the
closed interval $[a,b]$, \verb!Intolr a b! for the
open interval ${<}a,b{>}$, \verb!Intcl a! for the
left-closed interval $[a,\infty{>}$, \verb!Intol a! for the
left-open interval ${<}a,\infty{>}$, \verb!Intcr b! for the
right-closed interval ${<}-\infty,b]$.

Intervals like $[a,b]$ are defined for arbitrary reals $a,b$ (being
$\emptyset$ for $a>b$).
*)

(* Begin_Tex_Verb *)
Definition Intclr [a,b:IR; x:IR] : Prop :=
  (a [<=] x) /\ (x [<=] b).
Definition Intolr [a,b:IR; x:IR] : CProp :=
  (a [<] x) * (x [<] b).
Definition Intol [a:IR; x:IR] : CProp :=
  (a [<] x).
Definition Intcl [a:IR; x:IR] : Prop :=
  (a [<=] x).
Definition Intcr [b:IR; x:IR] : Prop :=
   (x [<=] b).
(* End_Tex_Verb *)

(* Tex_Prose
The limit of $f(x)$ as $x$ goes to $p = l$, for both unary and binary
functions:\\
The limit of $f$ in $p$ is $l$ if $\forall e\in\RR (0< e) \rightarrow
\exists d\in\RR (0< d) /\
 \forall x\in\RR(-d<p-x < d<) \rightarrow(AbsSmall -e <l-f(x) <e)$
*)

(* Begin_Tex_Verb *)
Definition funLim [p,l:IR] : CProp :=
  (e:IR)(Zero [<] e)->
    { d:IR & (Zero [<] d) |
             (x:IR)(AbsSmall d (p[-]x)) -> (AbsSmall e (l[-](f x)))}.
(* End_Tex_Verb *)

(* Tex_Prose
The definition of limit of $f$ in $p$ using Cauchy sequences.
*)

(* Begin_Tex_Verb *)
Definition funLim_Cauchy [p,l:IR] : CProp :=
  (s:CauchySeqR)((Lim s)[=] p) ->
    	(e:IR)(Zero [<] e) -> { N:nat | (m:nat)(le N m)
			   -> (AbsSmall e ((f(s m))[-]l))}.
(* End_Tex_Verb *)

(* Tex_Prose
The first definition implies the second one.

*)

(*
Ax_iom funLim_prop1 :(p,l:IR)(funLim p l)->(funLim_Cauchy p l).
*)
(*
Intros. Unfold funLim_Cauchy. Unfold funLim in H. Intros.
Elim (H e H1). Intros.
Elim s. Intros s_seq s_proof.
Decompose [and] H2.
Cut (Zero[<] x[/]TwoNZ).
Intro Hx2.
Elim (s_proof (x[/]TwoNZ) Hx2).
Intros N HN.
Exists N.
Intros.
Apply AbsSmall_minus.
Apply H5.
Generalize (HN m H3).
Intro HmN.
*)

(* Tex_Prose
The limit of $f$ in $(p,p')$ is $l$ if $\forall e\in\RR (0< e) \rightarrow
\exists d\in\RR (0< d) /\ \forall x\in\RR(-d<p-x < d<) \rightarrow
(-d<p'-y < d<) \rightarrow(AbsSmall -e <l-f(x,y) <e)$.
*)

(* Begin_Tex_Verb *)
Definition funLim2 [p,p',l:IR] : CProp :=
  (e:IR)(Zero [<] e)->
    {d:IR & (Zero [<] d) |
               (x,y:IR)(AbsSmall d (p[-]x)) -> (AbsSmall d (p'[-]y))
                        ->(AbsSmall e (l[-](f2 x y)))}.
(* End_Tex_Verb *)

(* Tex_Prose
The function $f$ is continuous at $p$ if the limit of $f(x)$ as $x$ goes to $p$
is $f(p)$.  This is the $\epsilon/\delta$ definition.
We also give the defintion with limits of Cauchy sequences.
*)

(* Begin_Tex_Verb *)
Definition continAt [p:IR]: CProp := (funLim p (f p)).
Definition continAtCauchy [p:IR]: CProp := (funLim_Cauchy p (f p)).
Definition continAt2 [p,q:IR]: CProp := (funLim2 p q (f2 p q)).
(* End_Tex_Verb *)

(*
Ax_iom continAt_prop1 :(p:IR)(continAt p)->(continAtCauchy p).
*)

(* Begin_Tex_Verb *)
Definition contin : CProp :=      (x:IR)(continAt x).
Definition continCauchy :CProp := (x:IR)(continAtCauchy x).
Definition contin2 :CProp :=      (x,y:IR)(continAt2 x y).
(* End_Tex_Verb *)

(* Tex_Prose
Continuous on a closed, resp.\ open, resp.\ left open, resp.\ left closed
interval
*)

(* Begin_Tex_Verb *)
Definition continOnc [a,b:IR]: CProp :=
  (x:IR)(Intclr a b x) -> (continAt x).
Definition continOno [a,b:IR]: CProp :=
  (x:IR)(Intolr a b x) -> (continAt x).
Definition continOnol [a:IR]: CProp :=
  (x:IR)(Intol a x) -> (continAt x).
Definition continOncl [a:IR]: CProp :=
  (x:IR)(Intcl a x) -> (continAt x).
(* End_Tex_Verb *)

(*
Section Sequence_and_function_limits.

(* _Tex_Prose
If $\lim_{x->p} (f x) = l$, then for every sequence $p_n$ whose
limit is $p$, $\lim_{n->\infty} f (p_n) =l$.
 *)
(* _Begin_Tex_Verb *)
Lemma funLim_SeqLimit:
  (p,l:IR)(fl:(funLim p l))
    (pn:nat->IR)(sl:(SeqLimit pn p)) (SeqLimit ([n:nat](f (pn n))) l).
(* _End_Tex_Verb *)
Proof.
Intros; Unfold seqLimit.
Intros eps epos.
Elim (fl ? epos); Intros del dh; Elim dh; Intros H0 H1.
Elim (sl ? H0); Intros N Nh.
Exists N. Intros m leNm.
Apply AbsSmall_minus.
Apply H1.
Apply AbsSmall_minus.
Apply (Nh ? leNm).
Qed.

(**** Is the converse constructively provable? **
Lemma SeqLimit_funLim:
  (p,l:IR)((pn:nat->IR)(sl:(SeqLimit pn p)) (SeqLimit ([n:nat](f (pn n))) l)) ->
    (funLim p l).
****)

(* _Tex_Prose
Now the same Lemma in terms of Cauchy sequences: if $\lim_{x->p} (f x) = l$,
then for every Cauchy sequence $s_n$ whose
limit is $p$, $\lim_{n->\infty} f (s_n) =l$.
 *)
(* _Begin_Tex_Verb *)
Ax_iom funLim_isCauchy:
  (p,l:IR)(funLim p l)->(s:CauchySeqR)((Lim s)[=] p) ->
	(e:IR)(Zero [<] e) -> (Ex [N:nat](m:nat)(le N m)
			   -> (AbsSmall e ((s m)[-](s N)))).
(* _End_Tex_Verb *)

End Sequence_and_function_limits.

Section Monotonic_functions.
(* _Begin_Tex_Verb *)
Definition str_monot  := (x,y:IR)(x[<]y)->((f x)[<](f y)).

Definition str_monotOnc  := [a,b:IR]
         (x,y:IR)(Intclr a b x)->(Intclr a b y)
                  ->(x[<]y)->((f x)[<](f y)).

Definition str_monotOncl  := [a:IR]
         (x,y:IR)(Intcl a x)->(Intcl a y)
                  ->(x[<]y)->((f x)[<](f y)).

Definition str_monotOnol  := [a:IR]
         (x,y:IR)(Intol a x)->(Intol a y)
                  ->(x[<]y)->((f x)[<](f y)).
(* _End_Tex_Verb *)

(* Following probably not needed for the FTA proof;
it stated that strong monotonicity on a closed interval implies that the
intermediate value theorem holds on this interval. For FTA we need IVT on
$[0,\infty>$.
*)
Ax_iom strmonc_imp_ivt :(a,b:IR)(str_monotOnc a b)
             -> (x,y:IR)(x[<]y)->(Intclr a b x)->(Intclr a b y)
                 -> ((f x)[<]Zero) -> (Zero [<] (f y))
                     -> (EX z:IR | (Intclr x y z)/\((f z)[=]Zero)).
(* _Tex_Prose
$\forall c\in\RR (f\mbox{ strongly monotonic on }[c,\infty>)
\rightarrow \forall a,b\in\RR(c <a)\rightarrow( c< b)\rightarrow\ (f (a)<0)
\rightarrow\ (0:<f(b))
         \rightarrow \forall x,y\in\RR (a\leq x\leq b)\rightarrow
	(a\leq y\leq b)\rightarrow (x<y)
                \rightarrow \exists z\in\RR(x\leq z\leq y)\wedge(f(z)\noto 0))$
*)
(* _Begin_Tex_Verb *)
Ax_iom strmon_ivt_prem : (c:IR)(str_monotOncl c) ->
  (a,b:IR)(Intcl c a)->(Intcl c b)-> ((f a)[<] Zero) -> (Zero [<](f b))
         -> (x,y:IR)(Intclr a b x)->(Intclr a b y) -> (x[<]y)
                ->(EX z:IR | (Intclr x y z)/\((f z)[#]Zero)).
(* _End_Tex_Verb *)

(* The following is lemma 5.8 from the skeleton *)
(* _Tex_Prose
$\forall c\in\RR (f\mbox{ strongly monotonic on }[c,\infty>)
\rightarrow \forall a,b\in\RR(a<b) \rightarrow(c <a)\rightarrow( c< b)
\rightarrow(f (a)<0)\rightarrow (0:<f(b))
         \rightarrow \exists z\in\RR(a\leq z\leq b)\wedge(f(z)= 0))$
*)
(* _Begin_Tex_Verb *)
Ax_iom strmoncl_imp_ivt : (c:IR)(str_monotOncl c)
             -> (a,b:IR)(a[<]b)->(Intcl c a)->(Intcl c b)
                 -> ((f a)[<]Zero) -> (Zero [<] (f b))
                     -> (EX z:IR | (Intclr a b z)/\ ((f z)[=]Zero)).
(* _End_Tex_Verb *)
End Monotonic_functions.

*)
End Continuity.

Implicit Arguments Off.


