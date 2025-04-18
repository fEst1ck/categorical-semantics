Require Import Utf8.
Require Import Program.

Class Category C : Type := {
  Hom : C → C → Type;
  id : ∀ (A : C), Hom A A;
  compose : ∀ {X Y Z : C}, Hom Y Z → Hom X Y → Hom X Z;
  compose_assoc : ∀ {X Y Z W : C} (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y),
    compose (compose f g) h = compose f (compose g h);
  compose_id_l : ∀ {X Y : C} {f : Hom X Y}, compose (id Y) f = f;
  compose_id_r : ∀ {X Y : C} {f : Hom X Y}, compose f (id X) = f;
}.

Program Instance empty_category : Category Empty_set := {
  Hom A B := Empty_set;
  id := fun x => match x with end;
  compose _ _ _ f := fun x => match x with end;
  compose_assoc _ _ _ _ := fun x => match x with end;
  compose_id_l _ _ := fun x => match x with end;
  compose_id_r _ _ := fun x => match x with end;
}.

Program Instance unit_category : Category unit := {
  Hom A B := unit;
  id := fun x => tt;
  compose _ _ _ f g := tt;
  compose_assoc _ _ _ _ _ _ _ := eq_refl;
  compose_id_l _ _ f := match f with | tt => eq_refl end;
  compose_id_r _ _ f := match f with | tt => eq_refl end;
}.

Program Instance set_category : Category Set := {
  Hom X Y := X -> Y;
  id X := fun x => x;
  compose _ _ _ g f := fun x => g (f x);
  compose_assoc _ _ _ _ _ _ _ := eq_refl;
  compose_id_l _ _ _ := eq_refl;
  compose_id_r _ _ _ := eq_refl;
}.

Class Initial C `{Category C} := {
  initial : C;
  initial_map : ∀ {X : C}, Hom initial X;
  initial_unique : ∀ {X : C} {g1 g2 : Hom initial X}, g1 = g2;
}.

Program Instance set_initial : Initial Set := {
  initial := Empty_set;
  initial_unique := _;
}.

Next Obligation.
  destruct H.
Defined.

Next Obligation.
  extensionality x.
  destruct x.
Defined.

Class HasTerminal C `{Category C} := {
  terminal_obj : C;
  terminal_map : ∀ {X}, Hom X terminal_obj;
  terminal_uniq : ∀ {X : C} {g1 g2 : Hom X terminal_obj}, g1 = g2;
}.

Lemma terminal_obj_map : ∀ {C} `{HasTerminal C},
@terminal_map _ _ _ terminal_obj = id terminal_obj.
Proof.
  intros.
  apply terminal_uniq.
Qed.

Program Instance set_HasTerminal : HasTerminal Set := {
  terminal_obj := unit;
  terminal_map := _;
  terminal_uniq := _;
}.

Next Obligation.
  refine tt.
Defined.

Next Obligation.
  extensionality x.
  destruct (g1 x).
  destruct (g2 x).
  reflexivity.
Defined.

Definition prod_fst {X Y : Type} (xy : X * Y) : X := fst xy.
Definition prod_snd {X Y : Type} (xy : X * Y) : Y := snd xy.

Class HasProduct C `{Category C} := {
  product : C → C → C;
  fst : ∀ {X Y : C}, Hom (product X Y) X;
  snd : ∀ {X Y : C}, Hom (product X Y) Y;
  f_prod : ∀ {X Y Z : C} (f : Hom Z X) (g : Hom Z Y), Hom Z (product X Y);
  f_prod_comm1 : ∀ {X Y Z : C} (f : Hom Z X) (g : Hom Z Y),
    compose fst (f_prod f g) = f;
  f_prod_comm2 : ∀ {X Y Z : C} (f : Hom Z X) (g : Hom Z Y),
    compose snd (f_prod f g) = g;
  f_prod_uniq : ∀ {X Y Z : C} (f : Hom Z X) (g : Hom Z Y) (h : Hom Z (product X Y)),
    compose fst h = f → compose snd h = g → h = f_prod f g;
}.

Ltac prove_f_prod_eq :=
  match goal with
  | |- f_prod _ _ = _ =>
    symmetry;
    apply f_prod_uniq
  | |- _ = f_prod _ _ =>
      apply f_prod_uniq
  | _ => idtac "Goal is not an equation involving f_prod"
  end.

Lemma f_prod_uniq1 {C} `{HasProduct C}
  {X Y Z}
  (f g : Hom Z (product X Y)) :
  compose fst f = compose fst g ->
  compose snd f = compose snd g ->
  f = g.
Proof.
  intros.
  apply (eq_trans (f_prod_uniq (compose fst f) (compose snd f) f eq_refl eq_refl)).
  prove_f_prod_eq; auto.
Qed.

Definition prod_map {C} `{HasProduct C} {X Y Z W : C}
(f : Hom X Y) (g : Hom Z W) : Hom (product X Z) (product Y W) :=
  f_prod (compose f fst) (compose g snd).

  Ltac bubble_fst_to_fprod :=
  match goal with
  | |- context [compose fst ?e] =>
    match e with
    | f_prod _ _ => idtac "already at f_prod"
    | compose ?f ?g =>
      match f with
      | f_prod _ _ => 
        rewrite <- compose_assoc;
        idtac "rewrote compose_assoc"
      | _ =>
        idtac "inner f not f_prod"
      end
    | _ => idtac "not a compose"
    end
  | |- context [compose (compose _ fst) (f_prod _ _)] =>
    rewrite compose_assoc
  | _ => idtac "didn't match context"
  end.

  Ltac bubble_snd_to_fprod :=
  match goal with
  | |- context [compose snd ?e] =>
    match e with
    | f_prod _ _ => idtac "already at f_prod"
    | compose ?f ?g =>
      match f with
      | f_prod _ _ => 
        rewrite <- compose_assoc;
        idtac "rewrote compose_assoc"
      end
    | _ =>
      idtac "inner f not f_prod"
    end
  | _ => idtac "not a compose"
  end.

Ltac simplify_id :=
  match goal with
  | |- compose ?f (id _) = _ => rewrite compose_id_r
  | |- compose (id _) ?f = _ => rewrite compose_id_l
  | |- _ = compose ?f (id _) => rewrite compose_id_r
  | |- _ = compose (id _) ?f => rewrite compose_id_l
  | |- context [compose ?f (id _)] => rewrite compose_id_r
  | |- context [compose (id _) ?f] => rewrite compose_id_l
  | _ => idtac
  end.

Ltac simplify_terms :=
  simpl;
  repeat simplify_id;
  bubble_fst_to_fprod; try rewrite f_prod_comm1;
  bubble_snd_to_fprod; try rewrite f_prod_comm2.

Ltac terminal_eq :=
  match goal with
  | |- terminal_map = _=>
    apply terminal_uniq
  | |- _ = terminal_map _ =>
    symmetry; apply terminal_uniq
  | _ => idtac
  end.

Ltac solve_category_eq :=
  simplify_terms;
  terminal_eq;
  try reflexivity.

Lemma prod_map_comp_distr :
∀ {C} `{HasProduct C} {W X Y Z: C}
{f : Hom X Y} {g : Hom X Z} {h : Hom W X},
f_prod (compose f h) (compose g h) = compose (f_prod f g) h.
Proof.
  intros.
  erewrite f_prod_uniq with (f := compose f h) (g := compose g h) by solve_category_eq.
  reflexivity.
Qed.

Lemma comp_prod_map_distr :
∀ {C} `{HasProduct C} {X X' Y Y' Z Z': C}
{f : Hom X Y} {f' : Hom X' Y'} {g : Hom Y Z} {g' : Hom Y' Z'},
prod_map (compose g f) (compose g' f') = compose (prod_map g g') (prod_map f f').
Proof.
  intros.
  symmetry.
  eapply f_prod_uniq.
  + rewrite <- compose_assoc.
    unfold prod_map.
    simplify_terms.
    rewrite compose_assoc.
    rewrite f_prod_comm1.
    rewrite compose_assoc.
    reflexivity.
  + rewrite <- compose_assoc.
    unfold prod_map.
    rewrite f_prod_comm2.
    rewrite compose_assoc.
    rewrite f_prod_comm2.
    rewrite compose_assoc.
    reflexivity.
Qed.

Lemma comp_prod_map_distr1 :
∀ {C} `{HasProduct C} {X Y Z W : C}
{f : Hom X Y} {g : Hom Y Z},
prod_map (compose g f) (id W) = compose (prod_map g (id W)) (prod_map f (id W)).
Proof.
  intros.
  rewrite <- comp_prod_map_distr.
  rewrite compose_id_l.
  reflexivity.
Qed.

Open Scope type_scope.

Program Instance set_has_product : HasProduct Set := {
  product X Y := X * Y;
  fst X Y := prod_fst;
  snd X Y := prod_snd;
  f_prod _ _ _ f g := fun x => ( f x , g x );
  f_prod_comm1 _ _ _ f g := eq_refl;
  f_prod_comm2 _ _ _ f g := eq_refl;
  f_prod_uniq _ _ _ f g h H1 H2 := _;
}.

Next Obligation.
  extensionality x.
  destruct (h x).
  reflexivity.
Defined.

Class HasExponential C `{HasProduct C} := {
  exponential : C → C → C;
  eval : ∀ {X Y : C}, Hom (product (exponential X Y) X) Y;
  curry : ∀ {X Y Z : C}, Hom (product Z X) Y → Hom Z (exponential X Y);
  exponential_comm : ∀ {X Y Z : C} (f : Hom (product Z X) Y),
    compose (@eval X Y) (prod_map (curry f) (id X)) = f;
  curry_uniq : ∀ {X Y Z : C} (f : Hom (product Z X) Y) (g : Hom Z (exponential X Y)),
    compose (@eval X Y) (prod_map g (id X)) = f → g = curry f;
}.

Program Instance set_has_exponential : HasExponential Set := {
  exponential X Y := X -> Y;
  eval X Y := fun x => (prod_fst x) (prod_snd x);
  curry X Y Z f := fun x y => f (pair x y);
  exponential_comm _ _ _ _ := eq_refl;
  curry_uniq := _;
}.

Next Obligation.
  extensionality x.
  destruct x.
  reflexivity.
Defined.

Class CartesianClosed C `{Hc : Category C} `{@HasTerminal C Hc} `{Hp : @HasProduct C Hc} `{@HasExponential C Hc Hp} := {
}.

Instance set_cartesian_closed : CartesianClosed Set := {}.

Lemma curry_subst :
∀ {C} `{CartesianClosed C}
{W X Y Z : C}
{f : Hom (product X Y) Z}
{g : Hom W X},
curry (compose f (prod_map g (id Y))) = compose (curry f) g.
Proof.
  intros.
  symmetry.
  apply curry_uniq.
  rewrite comp_prod_map_distr1.
  rewrite <- compose_assoc.
  rewrite exponential_comm.
  reflexivity.
Qed.

Lemma curry_prop :
∀ {C} `{CartesianClosed C}
{X Y Z : C}
{f : Hom (product X Y) Z}
{g : Hom X Y},
compose eval (f_prod (curry f) g) =
compose f (f_prod (id _) g).
Proof.
  intros.
  replace (f_prod (curry f) g) with (compose (prod_map (curry f) (id _)) (f_prod (id _) g)).
  rewrite <- compose_assoc.
  f_equal.
  apply exponential_comm.
  apply f_prod_uniq.
  + rewrite <- compose_assoc.
    unfold prod_map.
    rewrite compose_id_l.
    rewrite f_prod_comm1.
    rewrite compose_assoc.
    rewrite f_prod_comm1.
    rewrite compose_id_r.
    reflexivity.
  + rewrite <- compose_assoc.
    unfold prod_map.
    rewrite compose_id_l.
    rewrite f_prod_comm2.
    rewrite f_prod_comm2.
    reflexivity.
Qed.