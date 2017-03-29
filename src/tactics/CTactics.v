Declare ML Module "rational".

Tactic Definition Algebra :=
  Auto with algebra_r algebra algebra_c algebra_s.

Tactic Definition Step_lft y := First [
  Apply eq_transitive_unfolded with y; [Algebra | Idtac]
  | Apply ap_well_def_lft_unfolded with y; Algebra
  | Apply less_wdl with y; [Idtac | Algebra]
  | Apply leEq_wdl with y; [Idtac | Algebra]
  | Apply AbsSmall_wd_lft_unfolded with y; [Idtac | Algebra]
  | Apply Abs_wd_lft_unfolded with y; [Idtac | Algebra]
].

Tactic Definition Step y :=
  (Step_lft y).

Tactic Definition Step_rht y := First [
  Apply eq_transitive_unfolded with y; [Idtac | Algebra]
  | Apply ap_well_def_rht_unfolded with y; Algebra
  | Apply less_wdr with y; [Idtac | Algebra]
  | Apply leEq_wdr with y; [Idtac | Algebra]
  | Apply AbsSmall_wd_rht_unfolded with y; [Idtac | Algebra]
  | Apply Abs_wd_rht_unfolded with y; [Idtac | Algebra]
].

Tactic Definition Stepr y :=
  (Step_rht y).

Tactic Definition Step_final y :=
  Apply eq_transitive_unfolded with y;
    Algebra.

Grammar tactic simple_tactic : tactic :=
  Step_lft [ "Step_lft" constrarg($c) ] -> [ (Step_lft $c) ].
Grammar tactic simple_tactic : tactic :=
  Step [ "Step" constrarg($c) ] -> [ (Step $c) ].
Grammar tactic simple_tactic : tactic :=
  Step_rht [ "Step_rht" constrarg($c) ] -> [ (Step_rht $c) ].
Grammar tactic simple_tactic : tactic :=
  Stepr [ "Stepr" constrarg($c) ] -> [ (Stepr $c) ].
Grammar tactic simple_tactic : tactic :=
  Step_final [ "Step_final" constrarg($c) ] -> [ (Step_final $c) ].

Tactic Definition RStep y := First [
    Apply eq_transitive_unfolded with y; [Rational | Idtac]
  | Apply ap_well_def_lft_unfolded with y; [Idtac | Rational]
  | Apply less_wdl with y; [Idtac | Rational]
  | Apply leEq_wdl with y; [Idtac | Rational]
  | Apply AbsSmall_wd_lft_unfolded with y; [Idtac | Rational]
  | Apply Abs_wd_lft_unfolded with y; [Idtac | Rational]
].

Tactic Definition RStepr y := First [
    Apply eq_transitive_unfolded with y; [Idtac | Rational]
  | Apply ap_well_def_rht_unfolded with y; [Idtac | Rational]
  | Apply less_wdr with y; [Idtac | Rational]
  | Apply leEq_wdr with y; [Idtac | Rational]
  | Apply AbsSmall_wd_rht_unfolded with y; [Idtac | Rational]
  | Apply Abs_wd_rht_unfolded with y; [Idtac | Rational]
].

(* FIXME *)
Grammar tactic simple_tactic : tactic :=
  RStep [ "RStep" constrarg($c) ] -> [ (RStep $c) ].
Grammar tactic simple_tactic : tactic :=
  RStepr [ "RStepr" constrarg($c) ] -> [ (RStepr $c) ].

(*
Recursive Meta Definition CSE_to_int s x f :=
  Match f With
      [x] -> '(CSE_var s)
    | [(csf_fun ?1 ?1 ?2 ?3)] -> Let t1=(CSE_to_int s x ?3) And F=?2 In '(CSE_un_op s F t1)
    | [(csbf_fun ?1 ?1 ?1 ?2 ?3 ?4)] -> Let t1=(CSE_to_int s x ?3) And t2=(CSE_to_int s x ?4) And F=?2 In '(CSE_bin_op s F t1 t2)
    | [?3] -> Let t1=?3 In '(CSE_const s ?3).

Tactic Definition CSReplace_l x y := 
  Match Context With 
    [|-(cs_eq ?1 ?2 ?3)] -> (Let r=(CSE_to_int ?1 x ?2) In Let s=?1 In Let t=?3 In
      (Change (cs_eq s (CSE_int s x r) t);
       Apply eq_transitive_unfolded with (CSE_int s y r);
      [Apply CSE_int_wd | Simpl]; Algebra)).

Tactic Definition CSReplace_r x y := 
  Match Context With 
    [|-(cs_eq ?1 ?2 ?3)] -> (Let r=(CSE_to_int ?1 x ?3) In Let s=?1 In Let t=?2 In
      (Change (cs_eq s t (CSE_int s x r));
       Apply eq_transitive_unfolded with (CSE_int s y r);
      [Simpl | Apply CSE_int_wd]; Algebra)).

Tactic Definition CSReplace x y := 
  Match Context With 
    [|-(cs_eq ?1 ?2 ?3)] -> (Let r=(CSE_to_int ?1 x ?2) In Let s=?1 In
      (Change (cs_eq s (CSE_int s x r) (CSE_int s y r)));
      Apply CSE_int_wd; Algebra).
*)
