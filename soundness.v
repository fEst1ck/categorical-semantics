Require Import Utf8.
Require Import Program.
Require Import category.
Require Import stlc.
Require Import model.

Fixpoint subst_cat {C} `{CartesianClosed C}
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
    - apply subst_cat.
      intros.
      apply ρ.
      apply var_succ.
      assumption.
Defined.

Lemma denot_comp :
∀ {C} `{CartesianClosed C}
{Γ Δ}
{ρ : ∀ t : type, contains Γ t → term Δ t}
{t}
(c : contains Γ t),
tm_denot (ρ t c) = compose (var_denot c) (subst_cat ρ).
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

Lemma subst_denot:
∀ {C} `{CartesianClosed C}
{Γ Δ : context}
{ρ : ∀ t, contains Γ t → term Δ t}
{t} {e: term Γ t},
tm_denot (subst ρ e) = compose (tm_denot e) (subst_cat ρ).
Proof.
  intros C HC HT HP HE HCC Γ Δ ρ t e.
  induction e.
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
    (* Set Printing Implicit. *)
    rewrite IHe with (ρ := (λ (t : type) (H : contains (context_cons t1 Γ) t), exts ρ H)).
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
   admit.
  + admit.
  + apply f_prod_comm1.
  + apply f_prod_comm2.
  + simpl.
    symmetry.
    apply f_prod_uniq; reflexivity.
Admitted.