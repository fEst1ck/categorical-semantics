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
  initial_unique : ∀ {X : C} {g1 g2 : Hom initial X}, g1 = g2;
}.

Program Instance set_initial : Initial Set := {
  initial := Empty_set;
  initial_unique := _;
}.
Next Obligation.
  extensionality x.
  destruct x.
Defined.

Class Terminal C `{Category C} := {
  terminal : C;
  terminal_unique : ∀ {X : C} {g1 g2 : Hom X terminal}, g1 = g2;
}.

Program Instance set_terminal : Terminal Set := {
  terminal := unit;
  terminal_unique := _;
}.

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

Definition prod_map {C} `{HasProduct C} {X Y Z W : C}
(f : Hom X Y) (g : Hom Z W) : Hom (product X Z) (product Y W) :=
  f_prod (compose f fst) (compose g snd).

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

Class CartesianClosed C `{Terminal C} `{HasProduct C} `{HasExponential C} := {
}.

Instance set_cartesian_closed : CartesianClosed Set := {}.