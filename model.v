Require Import Utf8.
Require Import Program.
Require Import category.
Require Import stlc.

Fixpoint ty_denot {C : Type} `{CartesianClosed C} (t : type) : C :=
  match t with
  | unit_type => terminal_obj
  | prod_type t1 t2 => product (ty_denot t1) (ty_denot t2)
  | arrow_type t1 t2 => exponential (ty_denot t1) (ty_denot t2)
  end.

Fixpoint ctx_denot {C : Type} `{CartesianClosed C} (Γ : context) : C :=
  match Γ with
  | empty_context => terminal_obj
  | context_cons t Γ => product (ctx_denot Γ) (ty_denot t)
  end.

Fixpoint var_denot {C: Type} `{CartesianClosed C} {Γ t} (x : contains Γ t) : Hom (ctx_denot Γ) (ty_denot t).
Proof.
  destruct x eqn:Hx.
  + refine snd.
  + eapply compose.
    - apply var_denot.
      refine c.
    - refine fst.
Defined.

Fixpoint tm_denot {C} `{CartesianClosed C} {Γ t} (e : term Γ t)
: Hom (ctx_denot Γ) (ty_denot t).
Proof.
  destruct e eqn:He.
  + refine terminal_map.
  + simpl ty_denot.
    apply f_prod.
    - apply tm_denot.
      assumption.
    - apply tm_denot.
      assumption.
  + eapply compose.
    2:{
      refine (tm_denot _ _ _ _ _ _ _ _ t0).
    }
    - refine fst.
  + eapply compose.
    2:{
      refine (tm_denot _ _ _ _ _ _ _ _ t0).
    }
    - refine snd.
  + apply var_denot.
    refine c.
  + simpl.
    apply curry.
    replace (product (ctx_denot Γ) (ty_denot t1)) with (ctx_denot (context_cons t1 Γ)) by reflexivity.
    apply tm_denot.
    refine t0.
  + eapply compose.
    2:{
      eapply f_prod.
      + apply tm_denot.
        refine t0_1.
      + apply tm_denot.
        refine t0_2.
    }
    apply eval.
Defined.