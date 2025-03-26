Require Import Utf8.
Require Import Program.
Require Import category.
Require Import stlc.

Fixpoint ty_denot {C} `{CartesianClosed C} (t : type) : C :=
    match t with
    | unit_type => terminal_obj
    | prod_type t1 t2 => product (ty_denot t1) (ty_denot t2)
    | arrow_type t1 t2 => exponential (ty_denot t1) (ty_denot t2)
    end.

Fixpoint ctx_denot {C} `{CartesianClosed C} (Γ : context) : C :=
    match Γ with
    | empty_context => terminal_obj
    | context_cons t Γ => product (ty_denot t) (ctx_denot Γ) 
    end.

Fixpoint tm_denot {C} `{CartesianClosed C} {Γ t} (e : term Γ t)
: Hom (ctx_denot Γ) (ty_denot t).
Proof.
    destruct e.
    + 
Admitted.