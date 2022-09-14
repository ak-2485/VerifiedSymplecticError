From vcfloat Require Import FPLang FPLangOpt RAux 
  Rounding Reify Float_notations Automate.
Require Import IntervalFlocq3.Tactic.
Import Binary.
Import List ListNotations.
Set Bullet Behavior "Strict Subproofs".

Open Scope R_scope.

Section WITHNANS.

Context {NANS: Nans}.

Ltac to_expr_list L ident_list n:=
match n with 
| S ?n' => let e:= constr:(nth n L (fun x => 0%F32)) in 
           let e1:= HO_reify_float_expr ident_list e in 
           let e2:= to_expr_list L ident_list n' in
              constr:(e2 ++ [e1])
| 0%nat => let e := constr:(nth 0%nat L (fun x => 0%F32)) in 
           let e1:= HO_reify_float_expr ident_list e in constr:([e1])
end.

Ltac Flist_to_expr_list L names := 
  let n:= eval compute in (length L - 1)%nat in 
  let e := to_expr_list L names n in 
  let e':= eval cbv [app] in e in e'.


Definition _h : ident := 1%positive.

Definition vmap_list (h : ftype Tsingle) :=    [(_h, existT ftype _ h)].

Definition vmap (h : ftype Tsingle) : valmap  :=
 ltac:(let z := compute_PTree (valmap_of_list (vmap_list h)) in exact z).

Definition bmap_list : list varinfo := 
  [ Build_varinfo Tsingle _h  0 1].

Definition bmap : boundsmap :=
 ltac:(let z := compute_PTree (boundsmap_of_list bmap_list) in exact z).


(* example 1 : midpoint *)
Definition M_midpointF_list := 
[ fun (h : ftype Tsingle) => ((1 -(h*h)/4) / (1 + (h*h)/4))%F32; 
  fun (h : ftype Tsingle) => (h / (1 + (h*h)/4))%F32; 
  fun (h : ftype Tsingle) => (-h / (1 + (h*h)/4))%F32; 
  fun (h : ftype Tsingle) => ((1 -(h*h)/4) / (1 + (h*h)/4))%F32 ].


Definition M_midpoint_expr_list := ltac:( 
    let e':= Flist_to_expr_list M_midpointF_list constr:([_h]) in exact e').

Definition M_midpointR_list (h : ftype Tsingle) : list R := 
  map (fun e => (FT2R (fval (env_ (vmap h)) e))) M_midpoint_expr_list. 

(* example 2 : Verlet *)
Definition M_VerletF_list :=
[fun (h : ftype Tsingle) => (1 - h*h/2)%F32;
  fun (h : ftype Tsingle) => (- h + h*h*h/4)%F32;
  fun (h : ftype Tsingle) => h;
  fun (h : ftype Tsingle) => (1 - h*h/2)%F32].

Definition M_Verlet_expr_list := ltac:( 
  let e':= Flist_to_expr_list M_VerletF_list constr:([_h]) in exact e').

Definition M_VerletR_list (h : ftype Tsingle) : list R := 
  map (fun e => (FT2R (fval (env_ (vmap h)) e))) M_Verlet_expr_list. 

From Coquelicot Require Import Coquelicot.

Definition list_to_matrix (l : list R) (n : nat) : matrix n n :=
    mk_matrix n n (fun i j => List.nth (i * n + j) l 0%R ).

Definition M_midpointR (h : ftype Tsingle) := list_to_matrix (M_midpointR_list h) 2.
Definition M_VerletR   (h : ftype Tsingle) := list_to_matrix (M_VerletR_list h) 2.

Definition detM (M : matrix 2 2) := 
 Rabs( (coeff_mat zero M 0%nat 0) * (coeff_mat zero M 1 1) -
    (coeff_mat zero M 1 0 ) * (coeff_mat zero M 0 1)).


Lemma Verlet_symp_error (h : ftype Tsingle) :
  boundsmap_denote bmap (vmap h) ->
  Rabs (detM (M_VerletR h) - 1) <= 3.51e-07. 
Proof.
intros.
cbv [M_VerletR M_VerletR_list M_Verlet_expr_list list_to_matrix map ]. 
repeat match goal with |- context[ fval ?a  ?b] =>
  let e:= fresh "e" in set (e:=  b);
  let f:= fresh "f" in set (f:=  fval a e)
end.
cbv [detM]. 
repeat rewrite coeff_mat_bij; try lia.
simpl.

assert (boundsmap_denote bmap (vmap h)) by auto; 
assert (P: prove_rndval bmap (vmap h) e1) by (prove_rndval; interval).

(** changes to unfold_prove_rndval*)
match type of P with prove_rndval _ _ _ => idtac end;
let BMD := fresh "BMD" in 
  match goal with H: boundsmap_denote _ _ |- _ => rename H into BMD end;
let H2 := fresh "H2" in let H3 := fresh "H3" in let r := fresh "r" in let s := fresh "s" in
destruct P as [[r s] [H2 H3]];
specialize (H3 BMD);
process_boundsmap_denote;
compute in H2; inversion H2; clear H2; subst;
fold Tsingle in H3; fold Tdouble in H3;
apply rndval_with_cond_result1_e in H3;
let errors := fresh "errors" in let H0 := fresh "H0" in
destruct H3 as [errors [H0 H2]].
let e := fresh "e" in 
 match type of H2 with context [fval ?env ?ee] => 
   set (e := fval env ee) in H2;
  let e1 := eval hnf in ee in change ee with e1 in e;
  cbv beta iota zeta delta [
      fval
      fop_of_binop fop_of_rounded_binop cast_lub_l cast_lub_r
      fop_of_unop fop_of_rounded_unop fop_of_exact_unop
      option_pair_of_options] in e;
   try change (type_of_expr _) with Tsingle in e;
   try change (type_of_expr _) with Tdouble in e;
   try change (type_lub _ _) with Tsingle in e;
   try change (type_lub _ _) with Tdouble in e;
   repeat change (type_lub ?x ?y) with x in e;
   repeat change (type_lub ?x ?y) with y in e;
   repeat change (cast  _ _ ?x) with x in e;
   repeat 
    match goal with
    | e := context [env_ ?a ?b ?c] |- _ =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v in *
   end
end.
 let FIN := fresh "FIN" in 
 destruct H2 as [FIN H2];
 unfold e in H2.
cbv beta iota zeta delta [
         reval Prog.binary Prog.unary Prog.real_operations
         Tree.binary_real Tree.unary_real] 
   in H2;
   repeat 
    match type of H2 with context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v in H2
   end.
change (Build_radix _ _) with radix2 in H2.


try change (type_of_expr _) with Tsingle in *;
try change (type_of_expr _) with Tdouble in *;
fold (@FT2R Tsingle) in *;
fold (@FT2R Tdouble) in *.
try repeat (let E := fresh "E" in  (*add try *)
            assert (E := Forall_inv H0); simpl in E;
          match type of E with
           |  Rle (Rabs ?a) (error_bound _ Normal') => 
                let d := fresh "d" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal') => 
                let d := fresh "e" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal2') => 
                   let d := fresh "e" in set (d := a) in *; clearbody d
           end;
           unfold error_bound in E;
           simpl bpow in E;
           rewrite Zpower_pos_powerRZ in E; 
           rewrite mul_hlf_powerRZ in E;
           simpl Z.sub in E;
           apply Forall_inv_tail in H0).
try match type of H0 with List.Forall _ (Maps.PTree.elements Maps.PTree.Empty) => clear H0 end; (**add this*)
try match type of H0 with Forall _ nil => clear H0 end.
clear errors.

(*****)

cbv [Datatypes.id].
repeat match goal with |- context[ @FT2R (type_lub ?a ?b) ?e ] =>
  let a':= fresh "a'" in 
  set (a' := (type_lub a b) ) ;
     let y := eval compute in a' in change a' with y; clear a'
 end.
fold Tsingle.

subst f1.
match goal with e := _ : ftype _ |- _ =>
     change (fval _ _) with e; clearbody e
 end.


assert (P: prove_rndval bmap (vmap h) e) by (prove_rndval; interval).
assert (boundsmap_denote bmap (vmap h)) by auto; unfold_prove_rndval P.
subst f.
match goal with e := _ : ftype _ |- _ =>
     change (fval _ _) with e; clearbody e
 end. clear e. 


assert (P2: prove_rndval bmap (vmap h) e0) by (prove_rndval; interval).
assert (boundsmap_denote bmap (vmap h)) by auto; unfold_prove_rndval P2.
subst f0.
match goal with e := _ : ftype _ |- _ =>
     change (fval _ _) with e; clearbody e
 end. clear e0. 


 (* incorporate the equation above the line *)
repeat match goal with H: _ = @FT2R _ _ |- _ => rewrite <- H; clear H end.
 (* Perform all env lookups *)
 repeat 
    match goal with
    | |- context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v
   end;
 (* Clean up all FT2R constants *)
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
 rewrite <- ?(F2R_eq radix2);
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end;
 (* Abstract all FT2R variables *)
 repeat 
  match goal with |- context [@FT2R ?t ?e] =>
     is_var e;
     let e' := fresh e in
     set (e' := @FT2R Tsingle e) in *; clearbody e'; clear e; rename e' into e
  end;
 (* clean up all powerRZ expressions *)
 compute_powerRZ.
match goal with |- (Rabs ?t ) <= ?r => 
  field_simplify t end.

match goal with |- (Rabs ?t ) <= ?r => 
  interval_intro ( (Rabs t )) with ( i_taylor (FT2R h), i_degree 15) as H99 end.

eapply Rle_trans; [ apply H99 | clear  ].
compute. nra.
Qed.



Lemma midpoint_symp_error (h : ftype Tsingle) :
boundsmap_denote bmap (vmap h) ->
Rabs (detM (M_midpointR h) - 1) <= 4e-06. 
Proof.
intros.
cbv [M_midpointR M_midpointR_list M_midpoint_expr_list list_to_matrix map ].
repeat match goal with |- context[ fval ?a  ?b] =>
  let e:= fresh "e" in set (e:=  b);
  let f:= fresh "f" in set (f:=  fval a e)
end.
cbv [detM]. 
repeat rewrite coeff_mat_bij; try lia.
simpl.

assert (boundsmap_denote bmap (vmap h)) by auto; 
assert (P: prove_rndval bmap (vmap h) e1) by (prove_rndval; interval).

(** changes to unfold_prove_rndval*)
match type of P with prove_rndval _ _ _ => idtac end;
let BMD := fresh "BMD" in 
  match goal with H: boundsmap_denote _ _ |- _ => rename H into BMD end;
let H2 := fresh "H2" in let H3 := fresh "H3" in let r := fresh "r" in let s := fresh "s" in
destruct P as [[r s] [H2 H3]];
specialize (H3 BMD);
process_boundsmap_denote;
compute in H2; inversion H2; clear H2; subst;
fold Tsingle in H3; fold Tdouble in H3;
apply rndval_with_cond_result1_e in H3;
let errors := fresh "errors" in let H0 := fresh "H0" in
destruct H3 as [errors [H0 H2]].
let e := fresh "e" in 
 match type of H2 with context [fval ?env ?ee] => 
   set (e := fval env ee) in H2;
  let e1 := eval hnf in ee in change ee with e1 in e;
  cbv beta iota zeta delta [
      fval
      fop_of_binop fop_of_rounded_binop cast_lub_l cast_lub_r
      fop_of_unop fop_of_rounded_unop fop_of_exact_unop
      option_pair_of_options] in e;
   try change (type_of_expr _) with Tsingle in e;
   try change (type_of_expr _) with Tdouble in e;
   try change (type_lub _ _) with Tsingle in e;
   try change (type_lub _ _) with Tdouble in e;
   repeat change (type_lub ?x ?y) with x in e;
   repeat change (type_lub ?x ?y) with y in e;
   repeat change (cast  _ _ ?x) with x in e;
   repeat 
    match goal with
    | e := context [env_ ?a ?b ?c] |- _ =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v in *
   end
end.
 let FIN := fresh "FIN" in 
 destruct H2 as [FIN H2];
 unfold e in H2.
cbv beta iota zeta delta [
         reval Prog.binary Prog.unary Prog.real_operations
         Tree.binary_real Tree.unary_real] 
   in H2;
   repeat 
    match type of H2 with context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v in H2
   end.
change (Build_radix _ _) with radix2 in H2.


try change (type_of_expr _) with Tsingle in *;
try change (type_of_expr _) with Tdouble in *;
fold (@FT2R Tsingle) in *;
fold (@FT2R Tdouble) in *.
try repeat (let E := fresh "E" in  (*add try *)
            assert (E := Forall_inv H0); simpl in E;
          match type of E with
           |  Rle (Rabs ?a) (error_bound _ Normal') => 
                let d := fresh "d" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal') => 
                let d := fresh "e" in set (d := a) in *; clearbody d
           |  Rle (Rabs ?a) (error_bound _ Denormal2') => 
                   let d := fresh "e" in set (d := a) in *; clearbody d
           end;
           unfold error_bound in E;
           simpl bpow in E;
           rewrite Zpower_pos_powerRZ in E; 
           rewrite mul_hlf_powerRZ in E;
           simpl Z.sub in E;
           apply Forall_inv_tail in H0).
try match type of H0 with List.Forall _ (Maps.PTree.elements Maps.PTree.Empty) => clear H0 end; (**add this*)
try match type of H0 with Forall _ nil => clear H0 end.

(*****)

cbv [Datatypes.id].
repeat match goal with |- context[ @FT2R (type_lub ?a ?b) ?e ] =>
  let a':= fresh "a'" in 
  set (a' := (type_lub a b) ) ;
     let y := eval compute in a' in change a' with y; clear a'
 end.
fold Tsingle.

subst f1.
match goal with e := _ : ftype _ |- _ =>
     change (fval _ _) with e; clearbody e
 end.


assert (P: prove_rndval bmap (vmap h) e) by (prove_rndval; interval).
assert (boundsmap_denote bmap (vmap h)) by auto; unfold_prove_rndval P.
subst f.
match goal with e := _ : ftype _ |- _ =>
     change (fval _ _) with e; clearbody e
 end. clear e. 


assert (P2: prove_rndval bmap (vmap h) e0) by (prove_rndval; interval).
assert (boundsmap_denote bmap (vmap h)) by auto; unfold_prove_rndval P2.
subst f0.
match goal with e := _ : ftype _ |- _ =>
     change (fval _ _) with e; clearbody e
 end. clear e0. 


 (* incorporate the equation above the line *)
repeat match goal with H: _ = @FT2R _ _ |- _ => rewrite <- H; clear H end.
 (* Perform all env lookups *)
 repeat 
    match goal with
    | |- context [env_ ?a ?b ?c] =>
       let u := constr:(env_ a b c) in let v := eval hnf in u in change u with v
   end;
 (* Clean up all FT2R constants *)
 repeat match goal with
 | |- context [@FT2R ?t (b32_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b32_B754_finite s m e H));
  simpl in j; subst j
 | |- context [@FT2R ?t (b64_B754_finite ?s ?m ?e ?H)] =>
 let j := fresh "j" in 
  set (j :=  @FT2R t (b64_B754_finite s m e H));
  simpl in j; subst j
 end;
 rewrite <- ?(F2R_eq radix2);
 (* clean up all   F2R radix2 {| Defs.Fnum := _; Defs.Fexp := _ |}   *)
 rewrite ?cleanup_Fnum;
 repeat match goal with |- context [cleanup_Fnum' ?f ?e] =>
  let x := constr:(cleanup_Fnum' f e) in
  let y := eval cbv - [Rdiv IZR] in x in
  change x with y
 end;
 (* Abstract all FT2R variables *)
 repeat 
  match goal with |- context [@FT2R ?t ?e] =>
     is_var e;
     let e' := fresh e in
     set (e' := @FT2R Tsingle e) in *; clearbody e'; clear e; rename e' into e
  end;
 (* clean up all powerRZ expressions *)
 compute_powerRZ.
match goal with |- (Rabs ?t ) <= ?r => 
  field_simplify t end.

match goal with |- (Rabs ?t ) <= ?r => 
  interval_intro ( (Rabs t )) with ( i_taylor (FT2R h), i_degree 15) as H99 end.

eapply Rle_trans; [ apply H99 | clear  ].
compute. nra.
Qed.



End WITHNANS.