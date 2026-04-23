Require Import Utf8.
Require Import Program.
Require Import category.
Require Import stlc.
Require Import model.

Fixpoint rename_denot {C} `{CartesianClosed C}
{Γ Δ : context} (ρ : ∀ t, contains Γ t → contains Δ t) {struct Γ}:
Hom (ctx_denot Δ) (ctx_denot Γ).
Proof.
  destruct Γ.
  + refine terminal_map.
  + simpl.
    apply f_prod.
    2:{
      apply tm_denot.
      apply var_term.
      apply ρ.
      apply var_zero.
    }
    - apply rename_denot.
      intros.
      apply ρ.
      apply var_succ.
      assumption.
Defined.

Lemma compose_var_denot_rename_denot :
∀ {C} `{CartesianClosed C}
{Δ Ω}
(g : ∀ t, contains Δ t → contains Ω t)
{t x},
compose (var_denot x) (rename_denot g) = var_denot (g t x).
Proof.
  intros.
  dependent induction x; solve_category_eq.
  rewrite IHx.
  reflexivity.
Qed.

Lemma rename_denot_comp :
∀ {C} `{CartesianClosed C}
{Γ Δ Ω: context}
(f : ∀ t, contains Γ t → contains Δ t)
(g : ∀ t, contains Δ t → contains Ω t),
rename_denot (fun t x => g t (f t x)) = compose (rename_denot f) (rename_denot g).
Proof.
  intros.
  dependent induction Γ.
  + solve_category_eq.
  + simpl.
    rewrite IHΓ.
    solve_category_eq.
    apply compose_var_denot_rename_denot.
Qed.

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

Lemma subst_rename_helper
{C} `{CartesianClosed C}
(* {Γ} *)
{Δ Ω : context}
(* (var_to_var : ∀ t, contains Γ t → contains Δ t) *)
(var_to_term : ∀ t, contains Δ t → term Ω t)
{t}
(x : contains Δ t)
:
compose (var_denot x) (subst_denot var_to_term) =
tm_denot (var_to_term t x).
Proof.
  dependent induction x; solve_category_eq; auto.
Qed.

Lemma subst_rename
{C} `{CartesianClosed C}
{Γ}
{Δ Ω : context}
(var_to_var : ∀ t, contains Γ t → contains Δ t)
(var_to_term : ∀ t, contains Δ t → term Ω t)
(* {struct Γ} *)
 :
subst_denot (fun _ var => var_to_term _ (var_to_var _ var))
= compose (rename_denot var_to_var) (subst_denot var_to_term).
Proof.
  induction Γ.
  + solve_category_eq.
  + simpl.
    rewrite IHΓ.
    solve_category_eq.
    apply subst_rename_helper.
Qed.

Lemma subst_denot_var_succ_comp :
∀ {C} `{CartesianClosed C}
{Γ Δ t}
(ρ : ∀ t0, contains Γ t0 → contains Δ t0),
@subst_denot _ _ _ _ _ _ Γ (context_cons t Δ)
  (fun _ x => var_term (var_succ (ρ _ x))) =
compose (@subst_denot _ _ _ _ _ _ Γ Δ (fun _ x => var_term (ρ _ x))) fst.
Proof.
  intros C Hc Ht Hp He Hcc Γ Δ t ρ.
  induction Γ.
  - simpl.
    apply terminal_uniq.
  - simpl.
    rewrite IHΓ.
    rewrite <- prod_map_comp_distr.
    simpl.
    reflexivity.
Qed.

Lemma subst_denot_var_term_id :
∀ {C} `{CartesianClosed C}
{Γ},
@subst_denot _ _ _ _ _ _ Γ Γ (fun _ x => var_term x) = id _.
Proof.
  intros C Hc Ht Hp He Hcc Γ.
  induction Γ.
  - simpl.
    apply terminal_obj_map.
  - simpl.
    rewrite (@subst_denot_var_succ_comp C Hc Ht Hp He Hcc Γ Γ t (fun _ x => x)).
    rewrite IHΓ.
    rewrite compose_id_l.
    symmetry.
    apply f_prod_uniq; solve_category_eq.
Qed.

Lemma var_succ_denot :
∀ {C} `{CartesianClosed C}
{Γ t},
@subst_denot _ _ _ _ _ _ Γ (context_cons t Γ) (fun _ x => (var_term (var_succ x))) = fst.
Proof.
  intros C Hc Ht Hp He Hcc Γ t.
  rewrite (@subst_denot_var_succ_comp C Hc Ht Hp He Hcc Γ Γ t (fun _ x => x)).
  rewrite subst_denot_var_term_id.
  solve_category_eq.
Qed.

Lemma subst1_map_denot :
∀ {C} `{CartesianClosed C}
{Γ t}
(e : term Γ t),
subst_denot (subst1_map e) = f_prod (id _) (tm_denot e).
Proof.
  intros.
  induction Γ.
  + simpl.
    rewrite terminal_obj_map.
    reflexivity.
  + simpl.
    f_equal.
    rewrite var_succ_denot.
    solve_category_eq.
Qed.

Definition ext_ctx_denot
{C} `{CartesianClosed C}
{t'}
{Γ Δ : context}
:
Hom (ctx_denot Δ) (ctx_denot Γ) →
Hom (ctx_denot (context_cons t' Δ)) (ctx_denot (context_cons t' Γ))
:= fun f => prod_map f (id _).

Lemma denot_comp :
∀ {C} `{CartesianClosed C}
{Γ Δ}
{ρ : ∀ t : type, contains Γ t → term Δ t}
{t}
(c : contains Γ t),
tm_denot (ρ t c) = compose (var_denot c) (subst_denot ρ).
Proof.
  intros.
  induction c; solve_category_eq.
  rewrite <- IHc.
  reflexivity.
Qed.

(* Renaming with an extra var_succ on the output:
   `rename_denot (λ x. var_succ (ρ x)) = rename_denot ρ ∘ fst`. *)
Lemma rename_var_succ_denot
{C} `{CartesianClosed C}
{Γ Δ} {t'} (ρ : ∀ t, contains Γ t → contains Δ t):
@rename_denot _ _ _ _ _ _ Γ (context_cons t' Δ) (fun t x => var_succ (ρ t x))
= compose (rename_denot ρ) fst.
Proof.
  revert Δ t' ρ.
  induction Γ; intros.
  + simpl. symmetry. apply terminal_uniq.
  + simpl.
    rewrite <- prod_map_comp_distr.
    f_equal.
    apply IHΓ.
Qed.

(* `rename_denot` of the identity variable map is the identity. *)
Lemma rename_denot_id
{C} `{CartesianClosed C}
{Γ}:
@rename_denot _ _ _ _ _ _ Γ Γ (fun _ x => x) = id _.
Proof.
  induction Γ.
  + simpl. apply terminal_obj_map.
  + simpl.
    rewrite (rename_var_succ_denot (fun _ x => x)).
    rewrite IHΓ.
    rewrite compose_id_l.
    symmetry.
    apply f_prod_uniq; apply compose_id_r.
Qed.

(* The weakening renaming `var_succ` denotes `fst`. *)
Lemma rename_denot_shift
{C} `{CartesianClosed C}
{Γ} {t'}:
@rename_denot _ _ _ _ _ _ Γ (context_cons t' Γ) (fun _ y => var_succ y) = fst.
Proof.
  rewrite (rename_var_succ_denot (fun _ y => y)).
  rewrite rename_denot_id.
  apply compose_id_l.
Qed.

(* Renaming commutes with term denotation. *)
Lemma rename_tm_denot
{C} `{CartesianClosed C}
{Γ t} (e : term Γ t):
∀ {Δ} (ρ : ∀ t, contains Γ t → contains Δ t),
tm_denot (rename ρ e) = compose (tm_denot e) (rename_denot ρ).
Proof.
  dependent induction e; intros; cbn.
  + apply terminal_uniq.
  + rewrite IHe1, IHe2.
    apply prod_map_comp_distr.
  + rewrite IHe. symmetry. apply compose_assoc.
  + rewrite IHe. symmetry. apply compose_assoc.
  + symmetry. apply compose_var_denot_rename_denot.
  + rewrite IHe.
    rewrite <- curry_subst.
    do 2 f_equal.
    cbn.
    unfold prod_map.
    rewrite compose_id_l.
    f_equal.
    apply rename_var_succ_denot.
  + rewrite IHe1, IHe2.
    rewrite compose_assoc.
    f_equal.
    apply prod_map_comp_distr.
Qed.

(* A substitution composed with a post-renaming: substitute-then-rename.
   `subst_denot (λ x. rename σ (ρ x)) = subst_denot ρ ∘ rename_denot σ`. *)
Lemma subst_rename_denot
{C} `{CartesianClosed C}
{Γ Δ Ω}
(ρ_sub : ∀ t, contains Γ t → term Δ t)
(ρ_ren : ∀ t, contains Δ t → contains Ω t):
@subst_denot _ _ _ _ _ _ Γ Ω (fun t x => rename ρ_ren (ρ_sub t x))
= compose (subst_denot ρ_sub) (rename_denot ρ_ren).
Proof.
  revert Δ Ω ρ_sub ρ_ren.
  induction Γ; intros.
  + simpl. symmetry. apply terminal_uniq.
  + simpl.
    rewrite <- prod_map_comp_distr.
    f_equal.
    - apply IHΓ.
    - apply rename_tm_denot.
Qed.

Lemma ext_subst_denot
{C} `{CartesianClosed C}
{Γ Δ}
{t'}
(ρ : ∀ t : type, contains Γ t → term Δ t):
subst_denot (exts ρ t') = ext_ctx_denot (subst_denot ρ).
Proof.
  unfold ext_ctx_denot.
  cbn.
  unfold prod_map.
  rewrite compose_id_l.
  f_equal.
  rewrite subst_rename_denot.
  f_equal.
  apply rename_denot_shift.
Qed.

Lemma subst_denot_decomp:
∀ {C} `{CartesianClosed C}
{Γ}
{t} {e: term Γ t}
{Δ : context}
{ρ : ∀ t, contains Γ t → term Δ t},
tm_denot (subst ρ e) = compose (tm_denot e) (subst_denot ρ).
Proof.
  intros C HC HT HP HE HCC Γ t e.
  dependent induction e; intros; simpl.
  + solve_category_eq.
  + rewrite IHe1.
    rewrite IHe2.
    apply prod_map_comp_distr.
  + rewrite IHe.
    rewrite compose_assoc.
    reflexivity.
  + rewrite IHe.
    rewrite compose_assoc.
    reflexivity.
  + apply denot_comp.
  + rewrite IHe.
    rewrite ext_subst_denot.
    rewrite <- curry_subst.
    reflexivity.
  + rewrite IHe1.
    rewrite IHe2.
    rewrite compose_assoc.
    f_equal.
    apply prod_map_comp_distr.
Qed.

Theorem soundness : ∀ {C} `{CartesianClosed C} {Γ t} {e1 e2 : term Γ t},
    eqn_in_context e1 e2 → tm_denot e1 = tm_denot e2.
Proof.
  intros C Hc Ht Hp He Hcc Γ t e1 e2 Heq.
  induction Heq; try solve_category_eq.
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
  + unfold stlc.app.
    simpl.
    rewrite subst_denot_decomp.
    rewrite subst1_map_denot.
    apply curry_prop.
  + simpl.
    unfold shift_one.
    rewrite subst_denot_decomp.
    rewrite var_succ_denot.
    symmetry.
    apply curry_uniq.
    f_equal.
    unfold prod_map.
    solve_category_eq.
  + solve_category_eq.
Qed.