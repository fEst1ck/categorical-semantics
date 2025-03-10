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

Inductive contains : context → type → Set :=
  | var_zero : ∀ {Γ t}, contains (context_cons t Γ) t
  | var_succ : ∀ {Γ t t'}, contains Γ t → contains (context_cons t' Γ) t.

Example var1 : contains ctx1 unit_type := var_zero.

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
Print rename.
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

  (* Fixpoint subst {Γ Δ : context} (ρ : ∀ {t}, contains Γ t → term Δ t)
  {t} (e : term Γ t) {struct e} : term Δ t. *)

(* Program Fixpoint subst_one {Γ t t'} (f : term (context_cons t' Γ) t) (a: term Γ t') : term Γ t :=
  match f with
  | unit_term => unit_term
  | pair_term e1 e2 => pair_term (subst_one e1 a) (subst_one e2 a)
  | fst_term e => fst_term (subst_one e a)
  | snd_term e => snd_term (subst_one e a)
  | var_term var_zero => a
  | var_term (var_succ var) => var_term var
  | abs_term e => abs_term (subst_one e a)
  | app_term e1 e2 => app_term (subst_one e1 a) (subst_one e2 a)
  end.
Next Obligation.
  destruct a.
  + apply unit_term.
  + apply pair_term.
    - eapply subst_one.
      + eassumption.
      + eassumption. *)

(* Fixpoint subst1
{Γ t1 t2}
(var_to_term : ∀ t, contains (context_cons t1 Γ) t → term Γ t)


(e1 : term (context_cons t1 Γ) t2) (e2 : term Γ t1) : term Γ t2.
Proof.
  dependent destruction e1.
  + exact unit_term.
  + apply pair_term.
    - eapply subst1; eassumption.
    - eapply subst1; eassumption.
  + eapply fst_term.
    eapply subst1; eassumption.
  + eapply snd_term.
    eapply subst1; eassumption.
  + dependent destruction c.
    - exact e2.
    - refine (var_term c).
  + eapply abs_term.
    admit.
  + eapply app_term; eapply subst1; eassumption.
Admitted. *)

  (* match e1 with
  | unit_term => unit_term
  | pair_term e1_1 e1_2 => pair_term (subst1 e1_1 e2) (subst1 e1_2 e2)
  | fst_term e1 => fst_term (subst1 e1 e2)
  | snd_term e1 => snd_term (subst1 e1 e2)
  | var_term x => _
  (* | var_term (var_succ var) => var_term var *)
  | abs_term e1 => abs_term (subst1 e1 e2)
  | app_term e1_1 e1_2 => app_term (subst1 e1_1 e2) (subst1 e1_2 e2)
  end.
Next Obligation. *)

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


Lemma foo {Γ Δ Ω t t'}

(var_to_var : ∀ t, contains Γ t → contains Δ t)
(var_to_term : ∀ t, contains Δ t → term Ω t)
(var : contains (context_cons t' Γ) t) :
      exts var_to_term (ext var_to_var var) =
      exts (λ t x,
      var_to_term t (var_to_var t x)) var.
Proof.
  dependent destruction var.
  + reflexivity.
  + simpl ext.
    cbn.
    reflexivity.
Qed.

Lemma subst_rename
{Γ}
{t}
(e : term Γ t)
{Δ Ω : context}
(var_to_var : ∀ t, contains Γ t → contains Δ t)
(var_to_term : ∀ t, contains Δ t → term Ω t)
 :
  subst var_to_term (rename var_to_var e) =
  subst (fun _ var => var_to_term _ (var_to_var _ var)) e.
Proof.
  (* generalize Δ, Ω. *)
  generalize var_to_var, var_to_term.
  generalize Δ.
  generalize Ω.
  induction e; intros; auto.
  + simpl.
    f_equal.
    - apply IHe1; auto.
    - apply IHe2; auto.
  + simpl.
    f_equal.
    apply IHe; auto.
  + simpl.
    f_equal.
    apply IHe; auto.
  + cbn.
    f_equal.
    erewrite IHe.
    f_equal.
Admitted.

Lemma stupid_helper {Γ t1}:
∀ t (x : contains (context_cons t1 Γ) t),
exts (λ (t : type) (var : contains Γ t), var_term var) x = var_term x.
Proof.
  intros.
  dependent destruction x; reflexivity.
Qed.

Lemma subst_id {Γ : context}
(ρ : ∀ t, contains Γ t → term Γ t):
(∀ t x, ρ t x = var_term x) →
∀ t (e : term Γ t), subst ρ e = e.
Proof.
  intros.
  induction e.
  + reflexivity.
  + simpl.
    f_equal.
    - eapply IHe1.
      eassumption.
    - eapply IHe2.
      eassumption.
  + simpl.
    f_equal.
    erewrite IHe.
    reflexivity.
    eassumption.
  + simpl.
    f_equal.
    erewrite IHe.
    reflexivity.
    eassumption.
  + apply H.
  + simpl.
    f_equal.
    apply IHe.
    intros.
    dependent destruction x; simpl.
    - reflexivity.
    - rewrite H.
      reflexivity. 
  + simpl.
    f_equal.
    - apply IHe1. assumption.
    - apply IHe2. assumption.
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

Fixpoint stupid {Γ t0 t1} (e1 : term (context_cons t1 Γ) t0) {struct e1} :
subst
(λ (t : type) (H : contains (context_cons t1 Γ) t),
exts (λ (t3 : type) (var : contains Γ t3), var_term var) H) e1 = e1.
Proof.
  intros.
  dependent destruction e1.
  + reflexivity.
  + simpl.
    f_equal.
    - apply stupid.
    - apply stupid.
  + simpl. f_equal. apply stupid.
  + simpl. f_equal. apply stupid.
  + simpl.
    dependent destruction c; reflexivity.
  + simpl. f_equal.
    rewrite subst_id.
    reflexivity.
    intros.
    dependent destruction x.
    - reflexivity.
    - rewrite exts_trivial.
      reflexivity.
      intros.
      rewrite exts_trivial.
      reflexivity.
      intros.
      reflexivity.
  + simpl. f_equal; apply stupid.  
Qed.

Lemma app_shift1 {Γ t1 t2} (e1 : term Γ t1) (e2 : term Γ t2) :
  (app (rename (λ (t : type) (x : contains Γ t), var_succ x) e1) e2) = e1.
Proof.
  dependent induction e1; auto.
  + cbn.
    f_equal.
    - apply IHe1_1.
    - apply IHe1_2.
  + cbn.
    f_equal.
    apply IHe1.
  + cbn.
    f_equal.
    apply IHe1.
  + cbn.
    rewrite subst_rename.
    apply f_equal.
    apply subst_id.
    intros.
    dependent destruction x; simpl ext.
    - reflexivity.
    - reflexivity.
  + cbn.
    f_equal.
    - rewrite subst_rename.
      apply subst_id.
      intros.
      reflexivity.
    - rewrite subst_rename.
      apply subst_id.
      intros.
      reflexivity.
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

Lemma pair_intro_cong : ∀ {Γ t1 t2}
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
    eapply pair_cons_app.
  + eapply eqn_prod_cong.
    - eapply H1.
    - eapply H2.
Qed.
