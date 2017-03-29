Require Export CSetoids.

Recursive Tactic Definition ttb fx f x :=
  Let P='(Pred f x) In
    Match Context With
      [H:P |- ?] -> LetTac fx := (f x H)
    | _ -> Cut P; [Intro; ttb fx f x | Idtac].

(*
Grammar tactic simple_tactic : tactic :=
  ttb_def ["Allow" identarg($id) "to" "be" constrarg($c2) "of" constrarg($c3)] -> [(ttb $id $c2 $c3)].

Section test.

Variable S:CSetoid.
Variable F:(PartFunct S).
Variable x:S.

Goal True. (* I am not at all interested in proving anything *)
Allow Fx to be F of x.
Undo.
Cut (Pred F x).
Intro weird_hyp.
(* Now the relevant proof term is already in the context *)
Allow Fx to be F of x.
(* Notice that no hypothesis has been added *)
Abort.

End test.
*)
