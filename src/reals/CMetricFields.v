(* $Id: CMetricFields.v,v 1.5 2003/03/11 13:36:14 lcf Exp $ *)

Require Export CReals1.

Section CMetric_Fields.

(* Tex_Prose
\chapter{Metric Fields}

This is an obsolete file, but maintained.
*)

(* Begin_Tex_Verb *)
Record is_CMetricField [F: CField; abs : (CSetoid_fun F IR)] : Prop :=
 {ax_abs_gt_zero   : (x:F)(Zero[<=] (abs x));
  ax_abs_resp_mult : (x,y:F)(abs(x[*]y)) [=](abs x)[*](abs y);
  ax_abs_triangle  : (x,y:F)(abs(x[+]y)) [<=] (abs x)[+](abs y)
 }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record CMetricField : Type :=
  {cmf_crr   :> CField;
   cmf_abs   :  (CSetoid_fun cmf_crr IR);
   cmf_proof :  (is_CMetricField cmf_crr cmf_abs)
  }.
(* End_Tex_Verb *)

End CMetric_Fields.

Syntactic Definition MAbs := (cmf_abs ?).

Section CMetric_Field_Cauchy.
Variable F : CMetricField.

(* Tex_Prose
\begin{convention} Let \verb!F:CMetricField!.
\end{convention}
*)

(* Begin_Tex_Verb *)
Definition MCauchy_prop [g:nat -> F]: CProp :=
   (e:IR)(Zero [<] e) -> {N:nat | (m:nat)(le N m)
			   -> (MAbs((g m)[-](g N)))[<=]e}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record MCauchySeq : Set :=
  {MCS_seq  :> nat -> F;
   MCS_proof: (MCauchy_prop MCS_seq)
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition MseqLimit [seq:nat->F; lim:F]: CProp :=
   (e:IR)(Zero [<] e) -> {N:nat | (m:nat)(le N m)
				-> (MAbs((seq m)[-]lim))[<=]e}.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Definition is_MCauchyCompl  [lim : MCauchySeq -> F] : CProp :=
  (s:MCauchySeq)(MseqLimit s (lim s)).
(* End_Tex_Verb *)

End CMetric_Field_Cauchy.

Implicits MseqLimit [1].
