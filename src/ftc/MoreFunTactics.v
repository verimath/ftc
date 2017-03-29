(* $Id: MoreFunTactics.v,v 1.7 2003/03/11 13:36:06 lcf Exp $ *)

Require Export MoreFunSeries.
Require Export Composition.
Require Export FunctTactics.

Tactic Definition Deriv_substR := 
  Match Context With [|-(Derivative ?1 ?)]->Let t=(derivative_of ?1) In Apply Derivative_wdr with t.

Inductive symbPF : Type :=
    shyp      : (I:interval)(pI:(proper I))(F,F':PartIR)(Derivative I pI F F')->symbPF
  | shyp'     : (I:interval)(pI:(proper I))(F:PartIR)(Diffble I pI F)->symbPF
  | sconst    : (c:IR)symbPF
  | sid       : symbPF
  | splus     : symbPF->symbPF->symbPF
  | sinv      : symbPF->symbPF
  | sminus    : symbPF->symbPF->symbPF
  | smult     : symbPF->symbPF->symbPF
  | sscalmult : IR->symbPF->symbPF
  | snth      : symbPF->nat->symbPF
  | srecip    : symbPF->symbPF
  | sdiv      : symbPF->symbPF->symbPF
  | scomp     : symbPF->symbPF->symbPF.
(*
  | ssum0     : nat->(nat->symbPF)->symbPF
  | ssumx     : (n:nat)((i:nat)(lt i n)->symbPF)->symbPF
  | ssum      : nat->nat->(nat->symbPF)->symbPF
*)

Fixpoint symb_to_PartIR [r:symbPF] : PartIR := Cases r of
    (shyp _ _ f _ _) => f
  | (shyp' _ _ f _)  => f
  | (sconst c)       => {-C-}c
  | sid              => FId
  | (splus f g)      => (symb_to_PartIR f) {+} (symb_to_PartIR g)
  | (sinv f)         => {--} (symb_to_PartIR f)
  | (sminus f g)     => (symb_to_PartIR f) {-} (symb_to_PartIR g)
  | (smult f g)      => (symb_to_PartIR f) {*} (symb_to_PartIR g)
  | (sscalmult c f)  => c {**} (symb_to_PartIR f)
  | (snth f n)       => (symb_to_PartIR f) {^} n
  | (srecip f)       => {1/} (symb_to_PartIR f)
  | (sdiv f g)       => (symb_to_PartIR f) {/} (symb_to_PartIR g)
  | (scomp f g)      => (symb_to_PartIR f) {o} (symb_to_PartIR g)
(*
  | (ssum0 n f)      => (FSum0 n [i:nat](symb_to_PartIR (f i)))
  | (ssumx n f)      => (FSumx n [i:nat][Hi:(lt i n)](symb_to_PartIR (f i Hi)))
  | (ssum m n f)     => (FSum m n [i:nat](symb_to_PartIR (f i)))
*)
  end.

Fixpoint symbPF_deriv [r:symbPF] : PartIR := Cases r of
    (shyp _ _ _ f' _) => f'
  | (shyp' J pJ F H)  => (Deriv J pJ F H)
  | (sconst c)        => {-C-}Zero
  | sid               => {-C-}One
  | (splus f g)       => (symbPF_deriv f) {+} (symbPF_deriv g)
  | (sinv f)          => {--} (symbPF_deriv f)
  | (sminus f g)      => (symbPF_deriv f) {-} (symbPF_deriv g)
  | (smult f g)       => ((symb_to_PartIR f) {*} (symbPF_deriv g)) {+} ((symbPF_deriv f) {*} (symb_to_PartIR g))
  | (sscalmult c f)   => c {**} (symbPF_deriv f)
  | (snth f n)        => Cases n of
                           O     => {-C-} Zero
                         | (S p) => (nring (S p)) {**} ((symbPF_deriv f) {*} (symb_to_PartIR (snth f p))) end
  | (srecip f)        => {--} ((symbPF_deriv f) {/} ((symb_to_PartIR f) {*} (symb_to_PartIR f)))
  | (sdiv f g)        => (((symbPF_deriv f) {*} (symb_to_PartIR g)) {-} ((symb_to_PartIR f) {*} (symbPF_deriv g))) {/}
                          ((symb_to_PartIR g) {*} (symb_to_PartIR g))
  | (scomp g f)       => ((symbPF_deriv g) {o} (symb_to_PartIR f)) {*} (symbPF_deriv f)
(*
  | (ssum0 n f)       => (FSum0 n [i:nat](symbPF_deriv (f i)))
  | (ssumx n f)       => (FSumx n [i:nat][Hi:(lt i n)](symbPF_deriv (f i Hi)))
  | (ssum m n f)      => (FSum m n [i:nat](symbPF_deriv (f i)))
*)
  end.

Recursive Meta Definition PartIR_to_symbPF f :=
  Match f With
      [{-C-}?3]  -> '(sconst ?3)
    | [(!Fid ?)] -> 'sid
    | [?3{+}?4]  -> Let t1=(PartIR_to_symbPF ?3) And t2=(PartIR_to_symbPF ?4) In '(splus t1 t2)
    | [{--}?3]   -> Let t1=(PartIR_to_symbPF ?3) In '(sinv t1)
    | [?3{-}?4]  -> Let t1=(PartIR_to_symbPF ?3) And t2=(PartIR_to_symbPF ?4) In '(sminus t1 t2)
    | [?3{*}?4]  -> Let t1=(PartIR_to_symbPF ?3) And t2=(PartIR_to_symbPF ?4) In '(smult t1 t2)
    | [?3{**}?4] -> Let t=(PartIR_to_symbPF ?4) In '(sscalmult ?3 t)
    | [?3{^}?4]  -> Let t1=(PartIR_to_symbPF ?3) In '(snth t1 ?4)
    | [{1/}?3]   -> Let t1=(PartIR_to_symbPF ?3) In '(srecip t1)
    | [?3{/}?4]  -> Let t1=(PartIR_to_symbPF ?3) And t2=(PartIR_to_symbPF ?4) In '(sdiv t1 t2)
    | [?3{o}?4]  -> Let t1=(PartIR_to_symbPF ?3) And t2=(PartIR_to_symbPF ?4) In '(scomp t1 t2)
    | [?3] -> (Let t=?3 In (Match Context With
        [H:(Derivative ?1 ?2 t ?4)|-?] -> '(shyp ?1 ?2 t ?4 H)
      | [H:(Diffble ?1 ?2 t)|-?]     -> '(shyp' ?1 ?2 t H))).

Tactic Definition Derivative_Help :=
  Match Context With 
    [|-(Derivative ?1 ?2 ?3 ?4)] -> (Let r=(PartIR_to_symbPF ?3) In
      (Apply Derivative_wdr with (symbPF_deriv r); [Unfold symbPF_deriv symb_to_PartIR | Simpl; Deriv])).
