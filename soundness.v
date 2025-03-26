Require Import Utf8.
Require Import Program.
Require Import category.
Require Import stlc.
Require Import model.

Print model.

Theorem soundness : ∀ {C} `{CartesianClosed C} {Γ t} (e1 e2 : term Γ t),
    eqn_in_context e1 e2 → tm_denot e1 = tm_denot e2.
Admitted.