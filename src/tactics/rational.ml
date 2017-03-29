(* $Id: rational.ml,v 1.3 2003/03/11 13:36:19 lcf Exp $ *)

open Util
open Pp
open Printer
open Term
open Names
open Nameops
open Libnames
open Closure
open Reductionops
open Tactics
open Tacmach
open Proof_trees
open Environ
open Declarations
open Inductiveops

let constant s = 
  try
    Declare.global_absolute_reference (path_of_string s)
  with Not_found ->
    error (Printf.sprintf "constant %s" s)
    | Anomaly _ ->
	error (Printf.sprintf "constant %s" s)

let constant_algebra s = constant ("Algebra.algebra." ^ s)

type xexpr =
    X_var of int
  | X_part of int * xexpr * constr
  | X_int of int
  | X_plus of xexpr * xexpr
  | X_mult of xexpr * xexpr
  | X_div of xexpr * xexpr * constr
  | X_zero
  | X_one
  | X_nat of int
  | X_inv of xexpr
  | X_minus of xexpr * xexpr
  | X_power of xexpr * int

let hd_app c = fst (destApplication c)

let args_app c = snd (destApplication c)

let first_arg c = (args_app c).(0)
let third_arg c = (args_app c).(2)
let fourth_arg c = (args_app c).(3)

let xinterp g c = fourth_arg (pf_type_of g c)

let mk_existential env = Evarutil.new_evar_in_sign env

let mk_lambda n t c = mkLambda (n,t,c)
let mk_cast c t = mkCast (c,t)
let mk_case ci a b c = mkCase (ci,a,b,c)

let pf_nf_betadeltaiota = pf_reduce nf_betadeltaiota
let pf_cbv_betadeltaiota = pf_reduce Tacred.cbv_betadeltaiota

let pf_whd_all_but sp =
  let flags =
    RedFlags.red_sub
      (RedFlags.red_add_transparent betadeltaiota (Conv_oracle.freeze()))
      (RedFlags.fCONST sp) in
  pf_reduce (clos_norm_flags flags) 

let frational verbose g a =

  let nat_nat = constant "Coq.Init.Datatypes.nat"
  and nat_O = constant "Coq.Init.Datatypes.O"
  and nat_S = constant "Coq.Init.Datatypes.S"
  and true_I = constant "Coq.Init.Logic.I"
  and pos_xI = constant "Coq.ZArith.fast_integer.xI"
  and pos_xO = constant "Coq.ZArith.fast_integer.xO"
  and pos_xH = constant "Coq.ZArith.fast_integer.xH"
  and int_ZERO = constant "Coq.ZArith.fast_integer.ZERO"
  and int_POS = constant "Coq.ZArith.fast_integer.POS"
  and int_NEG = constant "Coq.ZArith.fast_integer.NEG"

  and cs_eq = constant_algebra "CSetoids.cs_eq"
  and xexpr_var = constant_algebra "Reflection.xexpr_var"
  and xexpr_part = constant_algebra "Reflection.xexpr_part"
  and xexpr_int = constant_algebra "Reflection.xexpr_int"
  and xexpr_plus = constant_algebra "Reflection.xexpr_plus"
  and xexpr_mult = constant_algebra "Reflection.xexpr_mult"
  and xexpr_div = constant_algebra "Reflection.xexpr_div"
  and xexpr_zero = constant_algebra "Reflection.xexpr_zero"
  and xexpr_one = constant_algebra "Reflection.xexpr_one"
  and xexpr_nat = constant_algebra "Reflection.xexpr_nat"
  and xexpr_inv = constant_algebra "Reflection.xexpr_inv"
  and xexpr_minus = constant_algebra "Reflection.xexpr_minus"
  and xexpr_power = constant_algebra "Reflection.xexpr_power"
  and csf_fun = constant_algebra "CSetoids.csf_fun"
  and csbf_fun = constant_algebra "CSetoids.csbf_fun"
  and csg_unit = constant_algebra "CSemiGroups.csg_unit"
  and cr_one = constant_algebra "CRings.cr_one"
  and nring = constant_algebra "CRings.nring"
  and zring = constant_algebra "CRings.zring"
  and csg_op = constant_algebra "CSemiGroups.csg_op"
  and cg_inv = constant_algebra "CGroups.cg_inv"
  and cg_minus = constant_algebra "CGroups.cg_minus"
  and cr_mult = constant_algebra "CRings.cr_mult"
  and cf_div = constant_algebra "CFields.cf_div"
  and nexp_op = constant_algebra "CRings.nexp_op"
  and xforget = constant_algebra "Reflection.xforget"
  and expr_minus = constant_algebra "Reflection.expr_minus"
  and tactic_lemma = constant_algebra "Refl_corr.Tactic_lemma"
  and pfpfun = constant_algebra "CSetoids.pfpfun"
  and fid = constant_algebra "CSetoids.Fid"
  and norm = constant_algebra "Refl_corr.Norm"
  and partFunct = constant_algebra "CSetoids.PartFunct"

  (***
  and csg_crr = constant "#CSemiGroups#csg_crr.cci" "csg_crr"
  and cm_crr = constant "#CMonoids#cm_crr.cci" "cm_crr"
  and cg_crr = constant "#CGroups#cg_crr.cci" "cg_crr"
  and cr_crr = constant "#CRings#cr_crr.cci" "cr_crr"
  and cf_crr = constant "#CFields#cf_crr.cci" "cf_crr" 
  ***)
  in

  let the_csetoid = a.(0) in
  let the_csemigroup = first_arg the_csetoid in
  let the_cmonoid = first_arg the_csemigroup in
  let the_cgroup = first_arg the_cmonoid in
  let the_cring = first_arg the_cgroup in
  let the_cfield = first_arg the_cring in

  let ind_of_ref = function 
    | IndRef (kn,i) -> (kn,i)
    | _ -> anomaly "IndRef expected" in

  let nat_info = 
    let nat = ind_of_ref Coqlib.glob_nat in
    make_default_case_info (Global.env()) RegularStyle nat
  in
    
  let rec evalnat n =
    if eq_constr n nat_O then 0
    else if isApp n & eq_constr (hd_app n) nat_S then
      let a = args_app n in
	if Array.length a > 0 then (evalnat a.(0)) + 1
	else raise (Failure "evalnat")
    else raise (Failure "evalnat") in

  let rec evalpos n =
    if eq_constr n pos_xH then 1
    else if isApp n then
      let f = hd_app n
      and a = args_app n in
	if Array.length a > 0 then
	  if eq_constr f pos_xI then 2 * (evalpos a.(0)) + 1
	  else if eq_constr f pos_xO then 2 * (evalpos a.(0))
	  else raise (Failure "evalint")
	else raise (Failure "evalint")
    else raise (Failure "evalint") in

  let rec evalint n =
    if eq_constr n int_ZERO then 0
    else if isApp n then
      let f = hd_app n
      and a = args_app n in
	if Array.length a > 0 then
	  if eq_constr f int_POS then evalpos a.(0)
	  else if eq_constr f int_NEG then -(evalpos a.(0))
	  else raise (Failure "evalint")
	else raise (Failure "evalint")
    else raise (Failure "evalint") in
    
  let rec envindex : constr * constr list -> int * constr list =
    function (x,e) ->
      match e with
	  [] -> (0,[x])
	| y::f ->
	    if eq_constr x y then (0, e) else
	      let (i,g) = envindex (x,f) in
		(i + 1, y::g) in

  let lift_var : constr * constr list * constr list -> xexpr * constr list * constr list =
    function (x,e,e0) -> let (i,f) = envindex (x,e) in (X_var i, f, e0) in

  let rec lift_fun : constr * constr * constr * constr list * constr list -> xexpr * constr list * constr list =
    function (x,y,h,e,e0) -> let (z,f,f0) = lift (y,e,e0) in 
      let (i,g) = envindex (x,f0) in (X_part(i,z,h), f, g) and

    lift : constr * constr list * constr list -> xexpr * constr list * constr list =
    function (x,e,e') ->
      if isApp x then
	let f = hd_app x
	and a = args_app x in
	  if eq_constr f csg_unit then (X_zero, e, e')
	  else if eq_constr f cr_one then (X_one, e, e')
	  else if eq_constr f nring & Array.length a > 1 then
	    try (X_nat(evalnat a.(1)), e, e')
	    with Failure "evalnat" -> lift_var (x,e,e')
	  else if eq_constr f zring & Array.length a > 1 then
	    try (X_int(evalint a.(1)), e, e')
	    with Failure "evalint" -> lift_var (x,e,e')
          else if eq_constr f pfpfun & Array.length a > 3 then
            lift_fun(a.(1),a.(2),a.(3),e,e')
	  else if eq_constr f csbf_fun then
	    if Array.length a > 5 & isApp a.(3)
	    then let g = hd_app a.(3) in
                 if eq_constr g csg_op
		 then
		   let (t1,e1,e'1) = lift (a.(4),e,e') in
		   let (t2,e2,e'2) = lift (a.(5),e1,e'1) in
		   (X_plus(t1,t2), e2, e'2)
		 else if eq_constr g cr_mult
	              then
		        let (t1,e1,e'1) = lift (a.(4),e,e') in
		        let (t2,e2,e'2) = lift (a.(5),e1,e'1) in
			(X_mult(t1,t2), e2, e'2)
		      else lift_var (x,e,e')
            else lift_var (x,e,e')
	  else if eq_constr f csf_fun then
	    if Array.length a > 3 & isApp a.(2) then
	      let g = hd_app a.(2) in
	      let b = args_app a.(2) in
		if eq_constr g cg_inv then
		  let (t1,e1,e'1) = lift (a.(3),e,e') in
		    (X_inv(t1), e1, e'1)
		else if eq_constr g nexp_op & Array.length b > 1 then
		  try
		    let n = evalnat b.(1) in
		    let (t1,e1,e'1) = lift (a.(3),e,e') in
		      (X_power(t1,n), e1, e'1)
		  with Failure "evalnat" -> lift_var (x,e,e')
		else lift_var (x,e,e')
	    else lift_var (x,e,e')
	  else if eq_constr f cg_minus then
	    if Array.length a > 2 then
	      let (t1,e1,e'1) = lift (a.(1),e,e') in
	      let (t2,e2,e'2) = lift (a.(2),e1,e'1) in
		(X_minus(t1,t2), e2, e'2)
	    else lift_var (x,e,e')
          else if eq_constr f cf_div then
            if Array.length a > 3 then
              let (t1,e1,e'1) = lift (a.(1),e,e') in
              let (t2,e2,e'2) = lift (a.(2),e1,e'1) in
                (X_div(t1,t2,a.(3)), e2, e'2)
            else lift_var (x,e,e')
	  else if isApp f then
	    lift ((collapse_appl x), e, e')
	  else lift_var (x,e,e')
      else lift_var (x,e,e') in

  let rec natconstr i =
    if i > 0 then mkApp(nat_S, [| natconstr (i - 1) |]) else nat_O in

  let rec posconstr k =
    if k == 1 then pos_xH else
      let l = k mod 2 in
	mkApp((if l == 0 then pos_xO else pos_xI), [| posconstr (k / 2) |]) in

  let rec intconstr k =
    if k == 0 then int_ZERO else
    if k > 0 then mkApp(int_POS, [| posconstr k |]) else
      mkApp(int_NEG, [| posconstr (- k) |]) in
    
  let rec xexprconstr t rho rho0 =
    match t with
	X_var i -> mkApp(xexpr_var, [| the_cfield; rho; rho0; natconstr i |])
      | X_part (i,t,h) -> 
          let c = xexprconstr t rho rho0 in
          mkApp(xexpr_part, [| the_cfield; rho; rho0; xinterp g c; natconstr i; c; h |])
      | X_int i -> mkApp(xexpr_int, [| the_cfield; rho; rho0; intconstr i |])
      | X_plus (t1,t2) ->
	  let c1 = xexprconstr t1 rho rho0
	  and c2 = xexprconstr t2 rho rho0 in
	  mkApp(xexpr_plus, [| the_cfield; rho; rho0;
	                       xinterp g c1; xinterp g c2; c1; c2 |])
      | X_mult (t1,t2) ->
	  let c1 = xexprconstr t1 rho rho0
	  and c2 = xexprconstr t2 rho rho0 in
	  mkApp(xexpr_mult, [| the_cfield; rho; rho0;
		               xinterp g c1; xinterp g c2; c1; c2 |])
      | X_div (t1,t2,nz) ->
	  let c1 = xexprconstr t1 rho rho0
	  and c2 = xexprconstr t2 rho rho0 in
	  mkApp(xexpr_div, [| the_cfield; rho; rho0;
		              xinterp g c1; xinterp g c2; c1; c2; nz |])
      | X_zero ->
	  mkApp(xexpr_zero, [| the_cfield; rho; rho0 |])
      | X_one ->
	  mkApp(xexpr_one, [| the_cfield; rho; rho0 |])
      | X_nat i ->
	  mkApp(xexpr_nat, [| the_cfield; rho; rho0; natconstr i |])
      | X_inv (t1) ->
	  let c1 = xexprconstr t1 rho rho0 in
	  mkApp(xexpr_inv, [| the_cfield; rho; rho0; xinterp g c1; c1 |])
      | X_minus (t1,t2) ->
	  let c1 = xexprconstr t1 rho rho0
	  and c2 = xexprconstr t2 rho rho0 in
	  mkApp(xexpr_minus, [| the_cfield; rho; rho0;
		                xinterp g c1; xinterp g c2; c1; c2 |])
      | X_power (t1,n) ->
	  let c1 = xexprconstr t1 rho rho0 in
	  mkApp(xexpr_power, [| the_cfield; rho; rho0;
		                xinterp g c1; c1; natconstr n |]) in
    
  let rec valconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(csg_unit, [|the_csemigroup |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; valconstr f ta |]) in
    
  let rec funconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(fid, [|the_csetoid |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; funconstr f ta |]) in

  (***
  let solve_isevars g t =
    ise_resolve1 false (project g) (gLOB (pf_hyps g)) t in
  ***)

  let rec printval i e =
    match e with
	[] -> ()
      | c::f ->
	  msgnl (str "(" ++ int i ++ str ") -> " ++ prterm c);
	  printval (i + 1) f in

  let rec printfun i e =
    match e with
	[] -> ()
      | c::f ->
	  msgnl (str "(" ++ int i ++ str ") -> " ++ prterm c);
	  printfun (i + 1) f in

  let report g f f0 a xleft xright rho rho0 =
    (let left =
       pf_nf_betadeltaiota g
	 (mkApp(xforget, [| the_cfield; rho; rho0; xinterp g xleft; xleft |]))
     and right =
       pf_nf_betadeltaiota g
	 (mkApp(xforget, [| the_cfield; rho; rho0; xinterp g xright; xright |]))
     in
     let nleft = 
       pf_cbv_betadeltaiota g (mkApp(norm, [| left |]))
     and nright = 
       pf_cbv_betadeltaiota g (mkApp(norm, [| right |]))
     in
     let difference =
       (pf_cbv_betadeltaiota g
	  (mkApp(norm, [| mkApp(expr_minus, [| left; right |]) |]))) in
       msgnl (mt ()); printval 0 f; msgnl (mt ());
       msgnl (mt ()); printfun 0 f0; msgnl (mt ());
       msgnl (prterm a.(1));
       msgnl ( prterm left );
       msgnl ( prterm nleft ++ fnl ());
       msgnl ( prterm a.(2) );
       msgnl ( prterm right );
       msgnl ( prterm nright ++ fnl ());
       msgnl ( prterm difference ++ fnl ()))
  in
 
  (***   
  let cfield ta =
    if isApp ta & eq_constr (hd_app ta) csg_crr then
      let ta1 = (args_app ta).(0) in
	if isApp ta1 & eq_constr (hd_app ta1) cm_crr then
	  let ta2 = (args_app ta1).(0) in
	    if isApp ta2 & eq_constr (hd_app ta2) cg_crr then
	      let ta3 = (args_app ta2).(0) in
		if isApp ta3 & eq_constr (hd_app ta3) cr_crr then
		  let ta4 = (args_app ta3).(0) in
		    if isApp ta4 & eq_constr (hd_app ta4) cf_crr then
		      (args_app ta4).(0)
		    else raise (Failure "cfield")
		else raise (Failure "cfield")
	    else raise (Failure "cfield")
	else raise (Failure "cfield")
    else raise (Failure "cfield")
  in

  let cfield_check = cfield a.(0) in
  ***)

  let ta = pf_type_of g a.(1) in
  let fleft = a.(1) and fright = a.(2) in
  let (l,e,e0) = lift (fleft,[],[]) in
  let (r,f,f0) = lift (fright,e,e0) in
  let rho = valconstr f ta in
  let rho0 = funconstr f0 (mkApp(partFunct, [|the_csetoid|])) in
  let xleft = xexprconstr l rho rho0
  and xright = xexprconstr r rho rho0 in
    if verbose then
      report g f f0 a xleft xright rho rho0;
    let term =
      mkApp(tactic_lemma, [| the_cfield; rho; rho0;
			     fleft; fright; xleft; xright; true_I |])
    in
    (***
      if verbose then msgnl [< 'sTR "begin type check" >];
      let proof =
	try solve_isevars g term
	with _ ->
	  (* if not verbose then report g f a xleft xright; *)
	  error "cannot establish equality"
      in
	if verbose then msgnl [< 'sTR "end type check" >];
      ***)
	let result = 
	  try 
	    exact_check term g 
	  with e when Logic.catchable_exception e -> error "cannot establish equality"
	in
	if verbose then msgnl (str "end Rational");
	result

let rrational verbose g a =

  let nat_nat = constant "Coq.Init.Datatypes.nat"
  and nat_O = constant "Coq.Init.Datatypes.O"
  and nat_S = constant "Coq.Init.Datatypes.S"
  and true_I = constant "Coq.Init.Logic.I"
  and pos_xI = constant "Coq.ZArith.fast_integer.xI"
  and pos_xO = constant "Coq.ZArith.fast_integer.xO"
  and pos_xH = constant "Coq.ZArith.fast_integer.xH"
  and int_ZERO = constant "Coq.ZArith.fast_integer.ZERO"
  and int_POS = constant "Coq.ZArith.fast_integer.POS"
  and int_NEG = constant "Coq.ZArith.fast_integer.NEG"

  and cs_eq = constant_algebra "CSetoids.cs_eq"
  and xexpr_var = constant_algebra "RReflection.Rxexpr_var"
  and xexpr_part = constant_algebra "RReflection.Rxexpr_part"
  and xexpr_int = constant_algebra "RReflection.Rxexpr_int"
  and xexpr_plus = constant_algebra "RReflection.Rxexpr_plus"
  and xexpr_mult = constant_algebra "RReflection.Rxexpr_mult"
  and xexpr_zero = constant_algebra "RReflection.Rxexpr_zero"
  and xexpr_one = constant_algebra "RReflection.Rxexpr_one"
  and xexpr_nat = constant_algebra "RReflection.Rxexpr_nat"
  and xexpr_inv = constant_algebra "RReflection.Rxexpr_inv"
  and xexpr_minus = constant_algebra "RReflection.Rxexpr_minus"
  and xexpr_power = constant_algebra "RReflection.Rxexpr_power"
  and csf_fun = constant_algebra "CSetoids.csf_fun"
  and csbf_fun = constant_algebra "CSetoids.csbf_fun"
  and csg_unit = constant_algebra "CSemiGroups.csg_unit"
  and cr_one = constant_algebra "CRings.cr_one"
  and nring = constant_algebra "CRings.nring"
  and zring = constant_algebra "CRings.zring"
  and csg_op = constant_algebra "CSemiGroups.csg_op"
  and cg_inv = constant_algebra "CGroups.cg_inv"
  and cg_minus = constant_algebra "CGroups.cg_minus"
  and cr_mult = constant_algebra "CRings.cr_mult"
  and nexp_op = constant_algebra "CRings.nexp_op"
  and xforget = constant_algebra "RReflection.Rxforget"
  and expr_minus = constant_algebra "RReflection.Rexpr_minus"
  and tactic_lemma = constant_algebra "RRefl_corr.RTactic_lemma"
  and pfpfun = constant_algebra "CSetoids.pfpfun"
  and fid = constant_algebra "CSetoids.Fid"
  and norm = constant_algebra "RRefl_corr.RNorm"
  and partFunct = constant_algebra "CSetoids.PartFunct"
  in
  
  let the_csetoid = a.(0) in
  let the_csemigroup = first_arg the_csetoid in
  let the_cmonoid = first_arg the_csemigroup in
  let the_cgroup = first_arg the_cmonoid in
  let the_cring = first_arg the_cgroup in

  let ind_of_ref = function 
    | IndRef (kn,i) -> (kn,i)
    | _ -> anomaly "IndRef expected" in

  let nat_info = 
    let nat = ind_of_ref Coqlib.glob_nat in
    make_default_case_info (Global.env()) RegularStyle nat
  in
    
  let rec evalnat n =
    if eq_constr n nat_O then 0
    else if isApp n & eq_constr (hd_app n) nat_S then
      let a = args_app n in
	if Array.length a > 0 then (evalnat a.(0)) + 1
	else raise (Failure "evalnat")
    else raise (Failure "evalnat") in

  let rec evalpos n =
    if eq_constr n pos_xH then 1
    else if isApp n then
      let f = hd_app n
      and a = args_app n in
	if Array.length a > 0 then
	  if eq_constr f pos_xI then 2 * (evalpos a.(0)) + 1
	  else if eq_constr f pos_xO then 2 * (evalpos a.(0))
	  else raise (Failure "evalint")
	else raise (Failure "evalint")
    else raise (Failure "evalint") in

  let rec evalint n =
    if eq_constr n int_ZERO then 0
    else if isApp n then
      let f = hd_app n
      and a = args_app n in
	if Array.length a > 0 then
	  if eq_constr f int_POS then evalpos a.(0)
	  else if eq_constr f int_NEG then -(evalpos a.(0))
	  else raise (Failure "evalint")
	else raise (Failure "evalint")
    else raise (Failure "evalint") in
    
  let rec envindex : constr * constr list -> int * constr list =
    function (x,e) ->
      match e with
	  [] -> (0,[x])
	| y::f ->
	    if eq_constr x y then (0, e) else
	      let (i,g) = envindex (x,f) in
		(i + 1, y::g) in
    
  let lift_var : constr * constr list * constr list -> xexpr * constr list * constr list =
    function (x,e,e0) -> let (i,f) = envindex (x,e) in (X_var i, f, e0) in

  let rec lift_fun : constr * constr * constr * constr list * constr list -> xexpr * constr list * constr list =
    function (x,y,h,e,e0) -> let (z,f,f0) = lift (y,e,e0) in 
      let (i,g) = envindex (x,f0) in (X_part(i,z,h), f, g) and

    lift : constr * constr list * constr list -> xexpr * constr list * constr list =
    function (x,e,e') ->
      if isApp x then
	let f = hd_app x
	and a = args_app x in
	  if eq_constr f csg_unit then (X_zero, e, e')
	  else if eq_constr f cr_one then (X_one, e, e')
	  else if eq_constr f nring & Array.length a > 1 then
	    try (X_nat(evalnat a.(1)), e, e')
	    with Failure "evalnat" -> lift_var (x,e,e')
	  else if eq_constr f zring & Array.length a > 1 then
	    try (X_int(evalint a.(1)), e, e')
	    with Failure "evalint" -> lift_var (x,e,e')
          else if eq_constr f pfpfun & Array.length a > 3 then
            lift_fun(a.(1),a.(2),a.(3),e,e')
	  else if eq_constr f csbf_fun then
	    if Array.length a > 5 & isApp a.(3)
	    then let g = hd_app a.(3) in
                 if eq_constr g csg_op
		 then
		   let (t1,e1,e'1) = lift (a.(4),e,e') in
		   let (t2,e2,e'2) = lift (a.(5),e1,e'1) in
		   (X_plus(t1,t2), e2, e'2)
		 else if eq_constr g cr_mult
	              then
		        let (t1,e1,e'1) = lift (a.(4),e,e') in
		        let (t2,e2,e'2) = lift (a.(5),e1,e'1) in
			(X_mult(t1,t2), e2, e'2)
		      else lift_var (x,e,e')
            else lift_var (x,e,e')
	  else if eq_constr f csf_fun then
	    if Array.length a > 3 & isApp a.(2) then
	      let g = hd_app a.(2) in
	      let b = args_app a.(2) in
		if eq_constr g cg_inv then
		  let (t1,e1,e'1) = lift (a.(3),e,e') in
		    (X_inv(t1), e1, e'1)
		else if eq_constr g nexp_op & Array.length b > 1 then
		  try
		    let n = evalnat b.(1) in
		    let (t1,e1,e'1) = lift (a.(3),e,e') in
		      (X_power(t1,n), e1, e'1)
		  with Failure "evalnat" -> lift_var (x,e,e')
		else lift_var (x,e,e')
	    else lift_var (x,e,e')
	  else if eq_constr f cg_minus then
	    if Array.length a > 2 then
	      let (t1,e1,e'1) = lift (a.(1),e,e') in
	      let (t2,e2,e'2) = lift (a.(2),e1,e'1) in
		(X_minus(t1,t2), e2, e'2)
	    else lift_var (x,e,e')
	  else if isApp f then
	    lift ((collapse_appl x), e, e')
	  else lift_var (x,e,e')
      else lift_var (x,e,e') in

  let rec natconstr i =
    if i > 0 then mkApp(nat_S, [| natconstr (i - 1) |]) else nat_O in

  let rec posconstr k =
    if k == 1 then pos_xH else
      let l = k mod 2 in
	mkApp((if l == 0 then pos_xO else pos_xI), [| posconstr (k / 2) |]) in

  let rec intconstr k =
    if k == 0 then int_ZERO else
    if k > 0 then mkApp(int_POS, [| posconstr k |]) else
      mkApp(int_NEG, [| posconstr (- k) |]) in
    
  let rec xexprconstr t rho rho0 =
    match t with
	X_var i -> mkApp(xexpr_var, [| the_cring; rho; rho0; natconstr i |])
      | X_part (i,t,h) -> 
          let c = xexprconstr t rho rho0 in
          mkApp(xexpr_part, [| the_cring; rho; rho0; xinterp g c; natconstr i; c; h |])
      | X_int i -> mkApp(xexpr_int, [| the_cring; rho; rho0; intconstr i |])
      | X_plus (t1,t2) ->
	  let c1 = xexprconstr t1 rho rho0
	  and c2 = xexprconstr t2 rho rho0 in
	  mkApp(xexpr_plus, [| the_cring; rho; rho0;
	                       xinterp g c1; xinterp g c2; c1; c2 |])
      | X_mult (t1,t2) ->
	  let c1 = xexprconstr t1 rho rho0
	  and c2 = xexprconstr t2 rho rho0 in
	  mkApp(xexpr_mult, [| the_cring; rho; rho0;
		               xinterp g c1; xinterp g c2; c1; c2 |])
      | X_div (t1,t2,nz) -> raise (Failure "xexprconstr")
      | X_zero ->
	  mkApp(xexpr_zero, [| the_cring; rho; rho0 |])
      | X_one ->
	  mkApp(xexpr_one, [| the_cring; rho; rho0 |])
      | X_nat i ->
	  mkApp(xexpr_nat, [| the_cring; rho; rho0; natconstr i |])
      | X_inv (t1) ->
	  let c1 = xexprconstr t1 rho rho0 in
	  mkApp(xexpr_inv, [| the_cring; rho; rho0; xinterp g c1; c1 |])
      | X_minus (t1,t2) ->
	  let c1 = xexprconstr t1 rho rho0
	  and c2 = xexprconstr t2 rho rho0 in
	  mkApp(xexpr_minus, [| the_cring; rho; rho0;
		                xinterp g c1; xinterp g c2; c1; c2 |])
      | X_power (t1,n) ->
	  let c1 = xexprconstr t1 rho rho0 in
	  mkApp(xexpr_power, [| the_cring; rho; rho0;
		                xinterp g c1; c1; natconstr n |]) in
    
  let rec valconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(csg_unit, [| the_csemigroup |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; valconstr f ta |]) in

  let rec funconstr e ta =
    match e with
	[] -> mk_lambda Anonymous nat_nat
	    (mk_cast (mkApp(fid, [|the_csetoid |])) ta)
      | [c] -> mk_lambda Anonymous nat_nat c
      | c::f -> mk_lambda (Name (id_of_string "n")) nat_nat
	    (mk_case nat_info ta (mkRel 1) [| c; funconstr f ta |]) in

  (***    
  let solve_isevars g t =
    ise_resolve1 false (project g) (gLOB (pf_hyps g)) t in
  ***)

  let rec printval i e =
    match e with
	[] -> ()
      | c::f ->
	  msgnl (str "(" ++ int i ++ str ") -> " ++ prterm c);
	  printval (i + 1) f in

  let rec printfun i e =
    match e with
	[] -> ()
      | c::f ->
	  msgnl (str "(" ++ int i ++ str ") -> " ++ prterm c);
	  printfun (i + 1) f in

  let report g f f0 a xleft xright rho rho0 =
    (let left =
       pf_nf_betadeltaiota g
	 (mkApp(xforget, [| the_cring; rho; rho0; xinterp g xleft; xleft |]))
     and right =
       pf_nf_betadeltaiota g
	 (mkApp(xforget, [| the_cring; rho; rho0; xinterp g xright; xright |]))
     in
     let nleft = 
       pf_cbv_betadeltaiota g (mkApp(norm, [| left |]))
     and nright = 
       pf_cbv_betadeltaiota g (mkApp(norm, [| right |]))
     in
     let difference =
       (pf_cbv_betadeltaiota g
	  (mkApp(norm, [| mkApp(expr_minus, [| left; right |]) |]))) in
       msgnl (mt ()); printval 0 f; msgnl (mt ());
       msgnl (mt ()); printfun 0 f0; msgnl (mt ());
       msgnl ( prterm a.(1) );
       msgnl ( prterm left );
       msgnl ( prterm nleft ++ fnl ());
       msgnl ( prterm a.(2) );
       msgnl ( prterm right );
       msgnl ( prterm nright ++ fnl ());
       msgnl ( prterm difference ++ fnl ()) )
  in

  let ta = pf_type_of g a.(1) in
  let fleft = a.(1) and fright = a.(2) in
  let (l,e,e0) = lift (fleft,[],[]) in
  let (r,f,f0) = lift (fright,e,e0) in
  let rho = valconstr f ta in
  let rho0 = funconstr f0 (mkApp(partFunct, [|the_csetoid|])) in
  let xleft =
    try xexprconstr l rho rho0
    with _ -> error "not an equation over a CRing"
  and xright = xexprconstr r rho rho0 in
    if verbose then
      report g f f0 a xleft xright rho rho0;
    let term =
      mkApp(tactic_lemma, [| the_cring; rho; rho0;
			     fleft; fright; xleft; xright; true_I |])
    in
    (***
      if verbose then msgnl [< 'sTR "begin type check" >];
      let proof =
	try solve_isevars g term
	with _ ->
	  (* if not verbose then report g f a xleft xright; *)
	  error "cannot establish equality"
      in
	if verbose then msgnl [< 'sTR "end type check" >];
      ***)
    let result = 
      try
	exact_check term g 
      with e when Logic.catchable_exception e -> 
	error "cannot establish equality"
    in
    if verbose then msgnl (str "end Rational");
    result
      
	    
let rational verbose g =

  let cs_eq = constant_algebra "CSetoids.cs_eq" in

  let c = strip_outer_cast (pf_concl g) in
    if isApp c & eq_constr (hd_app c) cs_eq then
      let a = args_app c in
	if Array.length a > 2 then
	  try frational verbose g a
	  with _ -> rrational verbose g a
	else error "not an [=] equation"
    else error "not an [=] equation"
      
let rational1 verbose g =
  if verbose then msgnl (str "begin Rational");
  rational verbose g
      
TACTIC EXTEND Rational
| ["Rational"] -> [ rational1 false ]
END

TACTIC EXTEND RationalVerbose
| ["Rational" "Verbose"] -> [ rational1 true ]
END
