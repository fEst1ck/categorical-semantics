Require Import Utf8.
Require Import Program.
Require Import category.
Require Import stlc.
Require Import model.

Fixpoint subst_denot {C} `{CartesianClosed C}
{Γ Δ : context} (ρ : ∀ t, contains Γ t → term Δ t) {struct Γ}:
Hom (ctx_denot Δ) (ctx_denot Γ).
Proof.
  destruct Γ.
  + refine terminal_map.
  + simpl.
    apply f_prod.
    2:{
      apply tm_denot.
      apply ρ.
      apply var_zero.
    }
    - apply subst_denot.
      intros.
      apply ρ.
      apply var_succ.
      assumption.
Defined.

Definition ext_ctx_denot
{C} `{CartesianClosed C}
{t'}
{Γ Δ : context}
:
Hom (ctx_denot Δ) (ctx_denot Γ) →
Hom (ctx_denot (context_cons t' Δ)) (ctx_denot (context_cons t' Γ)).
Proof.
  intro f.
  simpl.
  eapply prod_map.
  - refine f.
  - apply id.
Defined.

Lemma denot_comp :
∀ {C} `{CartesianClosed C}
{Γ Δ}
{ρ : ∀ t : type, contains Γ t → term Δ t}
{t}
(c : contains Γ t),
tm_denot (ρ t c) = compose (var_denot c) (subst_denot ρ).
Proof.
  intros.
  induction c.
  + simpl.
    rewrite f_prod_comm2.
    reflexivity.
  + simpl.
    rewrite compose_assoc.
    rewrite f_prod_comm1.
    rewrite <- IHc.
    reflexivity.
Qed.

Fixpoint ext_subst_denot 
{C} `{CartesianClosed C}
{Γ Δ}
{t'}
(ρ : ∀ t : type, contains Γ t → term Δ t) {struct Γ}:
subst_denot (exts ρ t') = ext_ctx_denot (subst_denot ρ).
Proof.
  destruct Γ.
  + 
   simpl.
    unfold ext_ctx_denot.
    unfold prod_map.
    rewrite compose_id_l.
    f_equal.
    apply terminal_uniq.
  + unfold subst_denot.
Admitted.

Lemma subst_denot:
∀ {C} `{CartesianClosed C}
{Γ}
{t} {e: term Γ t}
{Δ : context}
{ρ : ∀ t, contains Γ t → term Δ t},
tm_denot (subst ρ e) = compose (tm_denot e) (subst_denot ρ).
Proof.
  intros C HC HT HP HE HCC Γ t e.
  dependent induction e; intros.
  + simpl.
    apply terminal_uniq.
  + simpl.
    rewrite IHe1.
    rewrite IHe2.
    apply prod_map_comp_distr.
  + simpl.
    rewrite IHe.
    rewrite compose_assoc.
    reflexivity.
  + simpl.
    rewrite IHe.
    rewrite compose_assoc.
    reflexivity.
  + simpl.
    apply denot_comp.
  + simpl.
    rewrite IHe.
    rewrite ext_subst_denot
  .
    admit.
  + simpl.
    rewrite IHe1.
    rewrite IHe2.
    rewrite compose_assoc.
    f_equal.
    apply prod_map_comp_distr.
Admitted.

Theorem soundness : ∀ {C} `{CartesianClosed C} {Γ t} {e1 e2 : term Γ t},
    eqn_in_context e1 e2 → tm_denot e1 = tm_denot e2.
Proof.
  intros C Hc Ht Hp He Hcc Γ t e1 e2 Heq.
  induction Heq.
  + reflexivity.
  + rewrite IHHeq.
    reflexivity.
  + rewrite IHHeq1.
    apply IHHeq2.
  + simpl.
    rewrite IHHeq1.
    rewrite IHHeq2.
    reflexivity.
  + simpl.
    rewrite IHHeq.
    reflexivity.
  + unfold app.
    simpl.
    rewrite subst_denot.
   admit.
  + simpl.
    unfold shift_one.
    rewrite subst_denot.
   admit.
  + apply f_prod_comm1.
  + apply f_prod_comm2.
  + simpl.
    symmetry.
    apply f_prod_uniq; reflexivity.
Admitted.