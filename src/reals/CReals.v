(* $Id: CReals.v,v 1.5 2003/03/11 13:36:15 lcf Exp $ *)

Require Export COrdFields.

(* Tex_Prose
\chapter{Reals}
\section{Definition of the notion of reals}
*)

(* Begin_SpecReals *)

(* Begin_Tex_Verb *)
Record is_CReals [R: COrdField; lim : (CauchySeq R) -> R] : CProp :=
  {ax_Lim  : (s:(CauchySeq R))(SeqLimit s (lim s));
   ax_Arch : (x:R){n:nat | (x [<=] (nring n))}
  }.
(* End_Tex_Verb *)

(* Begin_Tex_Verb *)
Record CReals : Type :=
  {crl_crr   :> COrdField;
   crl_lim   :  (CauchySeq crl_crr) -> crl_crr;
   crl_proof :  (is_CReals crl_crr crl_lim)
  }.
(* End_Tex_Verb *)

(* End_SpecReals *)

(* Begin_Tex_Verb *)
Definition Lim := crl_lim : (IR:CReals)(CauchySeq IR) -> IR.
(* End_Tex_Verb *)

Implicits Lim [1].
