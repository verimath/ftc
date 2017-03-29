(* $Id: FunctTactics.v,v 1.6 2003/03/11 13:36:03 lcf Exp $ *)

Require Export Differentiability.

Section Automatizing_Continuity.

Variables a,b:IR.

Inductive cont_function : Type := 
  hyp_c : (Hab:?)(F:PartIR)(!Continuous_I a b Hab F)->cont_function
  | hyp_d : (Hab':?)(F,F':PartIR)(!Derivative_I a b Hab' F F')->cont_function
  | hyp_d' : (Hab':?)(F,F':PartIR)(!Derivative_I a b Hab' F F')->cont_function
  | hyp_diff : (Hab':?)(F:PartIR)(!Diffble_I a b Hab' F)->cont_function
  | cconst : (c:IR)cont_function
  | cid : cont_function
  | cplus : cont_function->cont_function->cont_function
  | cinv : cont_function->cont_function
  | cminus : cont_function->cont_function->cont_function
  | cmult : cont_function->cont_function->cont_function
  | cscalmult : IR->cont_function->cont_function
  | cnth : cont_function->nat->cont_function
  | cabs : cont_function->cont_function.

Fixpoint cont_to_pfunct [r:cont_function] : PartIR := Cases r of
  (hyp_c Hab F H) => F
  | (hyp_d Hab F F' H) => F
  | (hyp_d' Hab F F' H) => F'
  | (hyp_diff Hab F H) => F
  | (cconst c) => ({-C-}c)
  | cid => FId
  | (cplus f g) => ((cont_to_pfunct f){+}(cont_to_pfunct g))
  | (cinv f) => ({--}(cont_to_pfunct f))
  | (cminus f g) => ((cont_to_pfunct f){-}(cont_to_pfunct g))
  | (cmult f g) => ((cont_to_pfunct f){*}(cont_to_pfunct g))
  | (cscalmult c f) => (c{**}(cont_to_pfunct f))
  | (cnth f n) => ((cont_to_pfunct f){^}n)
  | (cabs f) => (FAbs (cont_to_pfunct f))
  end.

Lemma continuous_cont : (Hab:?)(f:cont_function)(!Continuous_I a b Hab (cont_to_pfunct f)).
Intros.
Induction f; Simpl; Intros.
Assumption.
Exact (deriv_imp_contin_I ?????? d).
Exact (deriv_imp_contin'_I ?????? d).
Exact (diffble_imp_contin_I ????? d).
Exact (Continuous_I_const ??? c).
Exact (Continuous_I_id ???).
Exact (Continuous_I_plus ????? Hrecf1 Hrecf0).
Exact (Continuous_I_inv ???? Hrecf).
Exact (Continuous_I_minus ????? Hrecf1 Hrecf0).
Exact (Continuous_I_mult ????? Hrecf1 Hrecf0).
Exact (Continuous_I_scal ???? Hrecf ?).
Exact (Continuous_I_nth ???? Hrecf ?).
Exact (Continuous_I_abs ???? Hrecf).
Qed.

End Automatizing_Continuity.

Recursive Meta Definition pfunct_to_cont a b f :=
  Match f With
    [({-C-} ?3)] -> '(cconst a b ?3)
    | [(!Fid ?)] -> '(cid a b)
    | [?3{+}?4] -> Let t1=(pfunct_to_cont a b ?3) And t2=(pfunct_to_cont a b ?4) In '(cplus a b t1 t2)
    | [{--}?3] -> Let t1=(pfunct_to_cont a b ?3) In '(cinv a b t1)
    | [?3{-}?4] -> Let t1=(pfunct_to_cont a b ?3) And t2=(pfunct_to_cont a b ?4) In '(cminus a b t1 t2)
    | [?3{*}?4] -> Let t1=(pfunct_to_cont a b ?3) And t2=(pfunct_to_cont a b ?4) In '(cmult a b t1 t2)
    | [?3{**}?4] -> Let t=(pfunct_to_cont a b ?4) In '(cscalmult a b ?3 t)
    | [?3{^}?4] -> Let t1=(pfunct_to_cont a b ?3) In '(cnth a b t1 ?4)
    | [(FAbs ?3)] -> Let t1=(pfunct_to_cont a b ?3) In '(cabs a b t1)
    | [?3] -> (Let t=?3 In (Match Context With
      [Hab:?;H:(!Continuous_I a b ?1 t)|-?] -> '(hyp_c a b ?1 t H)
      | [H:(!Derivative_I a b ?1 t ?4)|-?] -> '(hyp_d a b ?1 t ?4 H)
      | [H:(!Derivative_I a b ?1 ?4 t)|-?] -> '(hyp_d' a b ?1 ?4 t H)
      | [H:(!Diffble_I a b ?1 t)|-?] -> '(hyp_diff a b ?1 t H))).

Tactic Definition New_Contin := 
  Match Context With 
    [|-(!Continuous_I ?1 ?2 ?4 ?3)] -> (Let r=(pfunct_to_cont ?1 ?2 ?3) In Let a=?1 In Let b=?2 In
      (Apply Continuous_I_wd with (cont_to_pfunct a b r);
        [Unfold cont_to_pfunct | Apply continuous_cont])).

Section Automatizing_Derivatives.

Variables a,b:IR.

Inductive deriv_function : Type :=
  hyp : (Hab':?)(f,f':PartIR)(!Derivative_I a b Hab' f f')->deriv_function
  | hyp' : (Hab':?)(f:PartIR)(!Diffble_I a b Hab' f)->deriv_function
  | const : (c:IR)deriv_function
  | id : deriv_function
  | rplus : deriv_function->deriv_function->deriv_function
  | rinv : deriv_function->deriv_function
  | rminus : deriv_function->deriv_function->deriv_function
  | rmult : deriv_function->deriv_function->deriv_function
  | rscalmult : IR->deriv_function->deriv_function
  | rnth : deriv_function->nat->deriv_function.

Fixpoint deriv_to_pfunct [r:deriv_function] : PartIR := Cases r of
  (hyp Hab' f f' H) => f
  | (hyp' Hab' f H) => f
  | (const c) => ({-C-}c)
  | id => (FId)
  | (rplus f g) => ((deriv_to_pfunct f){+}(deriv_to_pfunct g))
  | (rinv f) => ({--}(deriv_to_pfunct f))
  | (rminus f g) => ((deriv_to_pfunct f){-}(deriv_to_pfunct g))
  | (rmult f g) => ((deriv_to_pfunct f){*}(deriv_to_pfunct g))
  | (rscalmult c f) => (c{**}(deriv_to_pfunct f))
  | (rnth f n) => ((deriv_to_pfunct f){^}n)
  end.

Fixpoint deriv_deriv [r:deriv_function] : PartIR := Cases r of
  (hyp Hab' f f' H) => f'
  | (hyp' Hab' f H) => (PartInt (ProjS1 H))
  | (const c) => ({-C-}Zero)
  | id => ({-C-}One)
  | (rplus f g) => ((deriv_deriv f){+}(deriv_deriv g))
  | (rinv f) => ({--}(deriv_deriv f))
  | (rminus f g) => ((deriv_deriv f){-}(deriv_deriv g))
  | (rmult f g) => ((deriv_to_pfunct f){*}(deriv_deriv g)){+}((deriv_deriv f){*}(deriv_to_pfunct g))
  | (rscalmult c f) => (c{**}(deriv_deriv f))
  | (rnth f n) => Cases n of
    O => ({-C-}Zero)
    | (S p) => (({-C-}(nring (S p))){*}((deriv_deriv f){*}(deriv_to_pfunct (rnth f p)))) end
  end.

Lemma deriv_restr : (Hab':?)(f:deriv_function)(!Derivative_I a b Hab' (deriv_to_pfunct f) (deriv_deriv f)).
Intros.
Induction f; Simpl.
Assumption.
Apply projS2.
Exact (Derivative_I_const ?? Hab' c).
Exact (Derivative_I_id ?? Hab').
Exact (Derivative_I_plus ??????? Hrecf1 Hrecf0).
Exact (Derivative_I_inv ????? Hrecf).
Exact (Derivative_I_minus ??????? Hrecf1 Hrecf0).
Exact (Derivative_I_mult ??????? Hrecf1 Hrecf0).
Exact (Derivative_I_scal ????? Hrecf ?).
Case n.
Apply Derivative_I_wdl with (!Fconst IR One).
Apply FNth_zero'.
Exact (derivative_imp_inc ????? Hrecf).
Exact (Derivative_I_const ?? Hab' ?).
Clear n; Intro.
Exact (Derivative_I_nth ????? Hrecf n).
Qed.

Lemma diffble_restr : (Hab':?)(f:deriv_function)(!Diffble_I a b Hab' (deriv_to_pfunct f)).
Intros.
Induction f; Simpl.
Apply deriv_imp_Diffble_I with f'; Assumption.
Assumption.
Exact (Diffble_I_const ?? Hab' c).
Exact (Diffble_I_id ?? Hab').
Exact (Diffble_I_plus ????? Hrecf1 Hrecf0).
Exact (Diffble_I_inv ???? Hrecf).
Exact (Diffble_I_minus ????? Hrecf1 Hrecf0).
Exact (Diffble_I_mult ????? Hrecf1 Hrecf0).
Exact (Diffble_I_scal ???? Hrecf ?).
Exact (Diffble_I_nth ???? Hrecf n).
Qed.

End Automatizing_Derivatives.

Recursive Meta Definition pfunct_to_restr a b f :=
  Match f With
    [{-C-}?3] -> '(const a b ?3)
    | [(!Fid ?)] -> '(id a b)
    | [?3{+}?4] ->  Let t1=(pfunct_to_restr a b ?3) And t2=(pfunct_to_restr a b ?4) In '(rplus a b t1 t2)
    | [{--}?3] -> Let t1=(pfunct_to_restr a b ?3) In '(rinv a b t1)
    | [?3{-}?4] -> Let t1=(pfunct_to_restr a b ?3) And t2=(pfunct_to_restr a b ?4) In '(rminus a b t1 t2)
    | [?3{*}?4] -> Let t1=(pfunct_to_restr a b ?3) And t2=(pfunct_to_restr a b ?4) In '(rmult a b t1 t2)
    | [?3{**}?4] -> Let t=(pfunct_to_restr a b ?4) In '(rscalmult a b ?3 t)
    | [?3{^}?4] -> Let t1=(pfunct_to_restr a b ?3) In '(rnth a b t1 ?4)
    | [?3] -> (Let t=?3 In (Match Context With
      [H:(!Derivative_I a b ?1 t ?4)|-?] -> '(hyp a b ?1 t ?4 H)
      | [H:(!Diffble_I a b ?1 t)|-?] -> '(hyp' a b ?1 t H))).

Tactic Definition New_Deriv := 
  Match Context With 
    [|-(!Derivative_I ?1 ?2 ? ?3 ?4)] -> (Let r=(pfunct_to_restr ?1 ?2 ?3) In 
      (Apply Derivative_I_wdl with (deriv_to_pfunct ?1 ?2 r); [
        Unfold deriv_to_pfunct
        | Apply Derivative_I_wdr with (deriv_deriv ?1 ?2 r); [Unfold deriv_deriv deriv_to_pfunct | Apply deriv_restr]])).

Tactic Definition Differentiate := 
  Match Context With 
    [|-(!Diffble_I ?1 ?2 ? ?3)] -> (Let r=(pfunct_to_restr ?1 ?2 ?3) In 
      (Apply Diffble_I_wd with (deriv_to_pfunct ?1 ?2 r); [Apply diffble_restr | Unfold deriv_deriv deriv_to_pfunct])).

Recursive Meta Definition derivative_of f :=
  Match f With
    [{-C-}?3] -> '({-C-}(Zero::IR))
    | [(!Fid ?)] -> '({-C-}(One::IR))
    | [?3{+}?4] -> Let t1=(derivative_of ?3) And t2=(derivative_of ?4) In '(t1{+}t2)
    | [{--}?3] -> Let t1=(derivative_of ?3) In '({--}t1)
    | [?3{-}?4] -> Let t1=(derivative_of ?3) And t2=(derivative_of ?4) In '(t1{-}t2)
    | [?3{*}?4] -> Let t1=(derivative_of ?3) And t2=(derivative_of ?4) And t3=?3 And t4=?4 In '(t3{*}t2{+}t1{*}t4)
    | [?3{**}?4] -> Let t1=(derivative_of ?4) And t2=?3 In '(t2{**}t1)
    | [?3{^}(0)] -> '({-C-}(Zero::IR))
    | [?3{^}(S ?4)] -> Let t1=(derivative_of ?3) And t2=?3 And t3=?4 In '((Nring (S t3)){**}(t1{*}t2{^}t3))
    | [{1/}?3] -> Let t1=(derivative_of ?3) And t2=?3 In '({--}(t1{/}(t2{*}t2)))
    | [?3{/}?4] -> Let t1=(derivative_of ?3) And t2=(derivative_of ?4) And t3=?3 And t4=?4 In '((t1{*}t4{-}t3{*}t2){/}(t4{*}t4))
    | [?3{o}?4] -> Let t1=(derivative_of ?3) And t2=(derivative_of ?4) And t3=?3 In '((t3{o}t2){*}t1)
    | [?3] -> (Let t=?3 In (Match Context With
      [H:(!Derivative_I ? t ?4)|-?] -> (Let t1=?4 In 't1))).

Tactic Definition Deriv_I_substR := 
  Match Context With [|-(Derivative_I ? ?1 ?)]->Let t=(derivative_of ?1) In Apply Derivative_I_wdr with t.
