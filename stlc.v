Require Import Utf8.
Require Import Program.

(* Types *)
Inductive type : Set :=
  | unit_type : type
  | prod_type : type → type → type
  | arrow_type : type → type → type.

Example ty1 : type := unit_type.
Example ty2 : type := arrow_type unit_type unit_type.

(* A context is a list of types, with the most recent type at the head. *)
Inductive context : Set :=
  | empty_context : context
  | context_cons : type → context → context.

Example ctx1 : context := context_cons unit_type empty_context.

(* A variable in context
   `x : contains Γ t` is a variable in context `Γ` with type `t`. *)
Inductive contains : context → type → Set :=
  | var_zero : ∀ {Γ t}, contains (context_cons t Γ) t
  | var_succ : ∀ {Γ t t'}, contains Γ t → contains (context_cons t' Γ) t.

Example var1 : contains ctx1 unit_type := var_zero.

(* A term in context
   `e : term Γ t` is a term in context `Γ` with type `t`. *)
Inductive term : context → type → Set :=
  | unit_term : ∀ {Γ}, term Γ unit_type
  | pair_term : ∀ {Γ t1 t2}, term Γ t1 → term Γ t2 → term Γ (prod_type t1 t2)
  | fst_term : ∀ {Γ t1 t2}, term Γ (prod_type t1 t2) → term Γ t1
  | snd_term : ∀ {Γ t1 t2}, term Γ (prod_type t1 t2) → term Γ t2
  | var_term : ∀ {Γ t}, contains Γ t → term Γ t
  | abs_term : ∀ {Γ t1 t2}, term (context_cons t1 Γ) t2 → term Γ (arrow_type t1 t2)
  | app_term : ∀ {Γ t1 t2}, term Γ (arrow_type t1 t2) → term Γ t1 → term Γ t2.

Example id_term : term empty_context (arrow_type unit_type unit_type) :=
  abs_term (var_term var_zero).

Program Definition ext {Γ Δ : context} (ρ : ∀ {t}, contains Γ t → contains Δ t) :
  ∀ {t t'}, contains (context_cons t' Γ) t → contains (context_cons t' Δ) t :=
(* This deifinition is rejected by Coq because of unification issues. *)
fun t t' var =>
  match var with
  | var_zero => var_zero
  | var_succ var' => var_succ (ρ var')
  end.
(* Proof.
  intros t t' var.
  inversion var; subst.
  + apply var_zero.
  + refine (var_succ _).
    apply ρ.
    refine H2.
Defined. *)

Program Fixpoint rename {Γ Δ : context} (ρ : ∀ t, contains Γ t → contains Δ t)
  {t} (e : term Γ t) : term Δ t :=
  match e with
  | unit_term => unit_term
  | @pair_term Γ _ _ e1 e2 => pair_term (rename ρ e1) (rename ρ e2)
  | @fst_term Γ _ _ e => fst_term (rename ρ e)
  | @snd_term Γ _ _ e => snd_term (rename ρ e)
  | @var_term Γ _ var => var_term (ρ _ var)
  | abs_term e => abs_term (rename _ e)
  | app_term e1 e2 => app_term (rename ρ e1) (rename ρ e2)
  end.
Next Obligation.
  eapply ext.
  eapply ρ.
  assumption.
Defined.
(* Proof.
  (* inversion e; subst. *)
  destruct e.
  + exact unit_term.
  + apply pair_term; eapply rename; eauto.
  + eapply fst_term.
    eapply rename. { refine ρ. }
    eassumption.
  + eapply snd_term.
    eapply rename. { refine ρ. }
    eassumption.
  + refine (var_term _).
    apply ρ.
    assumption.
  + refine (abs_term _).
    eapply rename.
    2:{
      eassumption.
    }
    {
      intro t.
      apply ext.
      assumption.
    }
  + eapply app_term; eapply rename; eassumption.
Defined. *)

Program Definition exts {Γ Δ : context} (ρ : ∀ {t}, contains Γ t → term Δ t) :
  ∀ {t t'}, contains (context_cons t' Γ) t → term (context_cons t' Δ) t :=
  fun t t' var =>
  match var with
  | var_zero => var_term var_zero
  | var_succ var' => rename _ (ρ var')
  end.
Next Obligation.
  apply var_succ.
  assumption.
Defined.
(* Proof.
  intros t t' var.
  inversion var; subst.
  + apply var_term.
    apply var_zero.
  + eapply rename.
    2:{
      eapply ρ.
      assumption.
    }
    intro.
    apply var_succ.
Defined. *)

Fixpoint subst {Γ Δ : context} (ρ : ∀ {t}, contains Γ t → term Δ t)
  {t} (e : term Γ t) {struct e} : term Δ t.
Proof.
  destruct e.
  + constructor.
  + constructor; eapply subst; eassumption.
  + eapply fst_term. eapply subst; eassumption.
  + eapply snd_term. eapply subst; eassumption.
  + apply ρ. assumption.
  + apply abs_term.
    eapply subst.
    2:{ eassumption. }
    intros.
    eapply (exts ρ).
    assumption.
  + eapply app_term; eapply subst; eassumption.
Defined.
  (* match e with
  | unit_term => unit_term
  | pair_term e1 e2 => pair_term (subst ρ e1) (subst ρ e2)
  | fst_term e => fst_term (subst ρ e)
  | snd_term e => snd_term (subst ρ e)
  | var_term var => ρ var
  | abs_term e => abs_term (subst (ext ρ) e)
  | app_term e1 e2 => app_term (subst ρ e1) (subst ρ e2)
  end. *)

Definition shift_one {Γ t t'} (e : term Γ t) : term (context_cons t' Γ) t :=
  subst (fun _ var => (var_term (var_succ var))) e.

(* subst #0 with e, #(n + 1) with #n *)
Program Definition subst1_map {Γ t}
(e : term Γ t) :
∀ t', contains (context_cons t Γ) t' → term Γ t' :=
  fun _ var =>
    match var with
      | var_zero => e
      | var_succ x => var_term x
    end.

(* Program Definition app {Γ t1 t2} (e1 : term (context_cons t1 Γ) t2) (e2 : term Γ t1) : term Γ t2 :=
  subst (fun _ var => match var with
  | var_zero => e2
  | var_succ x => var_term x
  end) e1. *)

Program Definition app {Γ t1 t2} (e1 : term (context_cons t1 Γ) t2) (e2 : term Γ t1) : term Γ t2 :=
  subst (subst1_map e2) e1.

Lemma app_pair_cong {Γ t1 t2 t3} (e1 : term (context_cons t3 Γ) t1) (e2 : term (context_cons t3 Γ) t2) (e3 : term Γ t3) :
  app (pair_term e1 e2) e3 = pair_term (app e1 e3) (app e2 e3).
Proof.
  cbn.
  f_equal.
Qed.

(* An equation in context
   `eqn_in_context {Γ t} e1 e2` is a judgement that `e1` and `e2` are equal in context `Γ` with type `t`. *)
Inductive eqn_in_context : ∀ {Γ t}, term Γ t → term Γ t → Prop :=
  | eqn_refl : ∀ {Γ t} (e : term Γ t), eqn_in_context e e
  | eqn_sym : ∀ {Γ t} (e1 e2 : term Γ t), eqn_in_context e1 e2 → eqn_in_context e2 e1
  | eqn_trans : ∀ {Γ t} (e1 e2 e3 : term Γ t), eqn_in_context e1 e2 → eqn_in_context e2 e3 → eqn_in_context e1 e3
  | eqn_app_cong : ∀ {Γ t1 t2}
    (e1 e1' : term Γ (arrow_type t1 t2))
    (e2 e2' : term Γ t1),
    eqn_in_context e1 e1' →
    eqn_in_context e2 e2' →
    eqn_in_context (app_term e1 e2) (app_term e1' e2')
  | eqn_abs_epsilon : ∀ {Γ t1 t2}
    {e1 e2 : term (context_cons t1 Γ) t2},
    eqn_in_context e1 e2 →
    eqn_in_context
      (abs_term e1)
      (abs_term e2)
  | eqn_abs_beta : ∀ {Γ t1 t2}
    {e1 : term (context_cons t1 Γ) t2}
    {e2 : term Γ t1},
    eqn_in_context
      (app_term (abs_term e1) e2)
      (app e1 e2)
  | eqn_abs_eta : ∀ {Γ t1 t2} (e : term Γ (arrow_type t1 t2)),
    eqn_in_context
      (abs_term (app_term (shift_one e) (var_term var_zero)))
      e
  | eqn_prod_beta1 : ∀ {Γ t1 t2} (e1 : term Γ t1) (e2 : term Γ t2),
    eqn_in_context
      (fst_term (pair_term e1 e2))
      e1
  | eqn_prod_beta2 : ∀ {Γ t1 t2} (e1 : term Γ t1) (e2 : term Γ t2),
    eqn_in_context
      (snd_term (pair_term e1 e2))
      e2
  | eqn_prod_eta : ∀ {Γ t1 t2} (e : term Γ (prod_type t1 t2)),
    eqn_in_context
      (pair_term (fst_term e) (snd_term e))
      e.

Example fst_unit_pair: ∀ {Γ},
  eqn_in_context (fst_term (pair_term unit_term unit_term)) (@unit_term Γ).
Proof.
  intro Γ.
  eapply eqn_prod_beta1.
Qed.

Example ctx2 : context := context_cons (arrow_type unit_type unit_type) empty_context.

Example eqn2 :
  @eqn_in_context ctx2 _
    (app_term (var_term var_zero) (fst_term (pair_term unit_term unit_term)))
    (app_term (var_term var_zero) unit_term).
Proof.
  eapply eqn_app_cong.
  + eapply eqn_refl.
  + apply fst_unit_pair.
Qed.

Definition pair_cons : ∀ {Γ t1 t2}, term Γ (arrow_type t1 (arrow_type t2 (prod_type t1 t2))) :=
  λ (Γ : context) (t1 t2 : type),
  abs_term
    (abs_term
      (pair_term (var_term (var_succ var_zero))
      (var_term var_zero))).

Lemma subst_id {Γ : context}
(ρ : ∀ t, contains Γ t → term Γ t):
(∀ t x, ρ t x = var_term x) →
∀ t (e : term Γ t), subst ρ e = e.
Proof.
  intros.
  dependent induction e; cbn; try (f_equal; eauto).
  simpl.
  f_equal.
  apply IHe.
  intros.
  dependent destruction x; simpl.
  + reflexivity.
  + rewrite H.
    reflexivity. 
Qed.

Definition exts_eq
{Γ Ω: context}
(ρ1 ρ2 : ∀ t, contains Γ t → term Ω t) :
(∀ t (x : contains Γ t), ρ1 t x = ρ2 t x) →
∀ t t' (x : contains (context_cons t' Γ) t), exts ρ1 x = exts ρ2 x.
Proof.
  intros.
  dependent destruction x.
  + reflexivity.
  + simpl.
    f_equal.
    apply H.
Qed.

Fixpoint subst_eq {Γ Ω: context}
(ρ1 ρ2 : ∀ t, contains Γ t → term Ω t)
(H: ∀ t x, ρ1 t x = ρ2 t x)
t (e : term Γ t):
subst ρ1 e = subst ρ2 e.
Proof.
  intros.
  dependent destruction e; cbn; try (f_equal; eauto).
  apply subst_eq.
  intros.
  apply exts_eq.
  apply H.
Qed.

Definition exts_trivial
{Γ : context}
(ρ : ∀ t, contains Γ t → term Γ t) :
(∀ t (x : contains Γ t), ρ t x = var_term x) →
∀ t t' (x : contains (context_cons t' Γ) t), exts ρ x = var_term x.
Proof.
  intros.
  dependent destruction x.
  + reflexivity.
  + simpl.
    rewrite H.
    reflexivity.
Qed.

Fixpoint subst_rename
{Γ}
{t}
{Δ Ω : context}
(var_to_var : ∀ t, contains Γ t → contains Δ t)
(var_to_term : ∀ t, contains Δ t → term Ω t)
(e : term Γ t) {struct e}
 :
  subst var_to_term (rename var_to_var e) =
  subst (fun _ var => var_to_term _ (var_to_var _ var)) e.
Proof.
  dependent destruction e; cbn; try (f_equal; eauto).
  f_equal.
  rewrite subst_rename.
  eapply subst_eq.
  intros.
  dependent destruction x; reflexivity.
Qed.

Lemma app_shift1 {Γ t1 t2} (e1 : term Γ t1) (e2 : term Γ t2) :
  (app (rename (λ (t : type) (x : contains Γ t), var_succ x) e1) e2) = e1.
Proof.
  dependent induction e1; cbn; try (f_equal; eauto).
  rewrite subst_rename.
  apply subst_id.
  intros.
  dependent destruction x; reflexivity.
Qed.

Definition pair_cons_app {Γ t1 t2} (e1 : term Γ t1) (e2 : term Γ t2) :
  eqn_in_context
  (app_term
    (app_term pair_cons e1)
    e2)
  (@pair_term Γ _ _ e1 e2).
Proof.
  unfold pair_cons.
  eapply eqn_trans.
  + eapply eqn_app_cong.
    2:{
      apply eqn_refl.
    }
    eapply eqn_abs_beta.
  + cbn.
    eapply eqn_trans.
    - eapply eqn_abs_beta.
    - erewrite app_pair_cong.
      cbn.
      rewrite app_shift1.
      apply eqn_refl.
Qed.

Theorem pair_intro_cong : ∀ {Γ t1 t2}
  (e1 e1' : term Γ t1)
  (e2 e2' : term Γ t2),
  eqn_in_context e1 e1' →
  eqn_in_context e2 e2' →
  eqn_in_context
    (pair_term e1 e2)
    (pair_term e1' e2').
Proof.
  intros Γ t1 t2 e1 e1' e2 e2' H1 H2.
  eapply eqn_trans.
  + eapply eqn_sym.
    apply pair_cons_app.
  + eapply eqn_trans.
    eapply eqn_app_cong.
    2:{
      apply H2.
    }
    eapply eqn_app_cong.
    2:{
      apply H1.
    }
    apply eqn_refl.
    apply pair_cons_app.
Qed.
