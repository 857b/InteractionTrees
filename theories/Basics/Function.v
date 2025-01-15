(** * The Category of Functions *)

(** Definitions to work with Coq functions [A -> B] categorically.
 *)

(* begin hide *)
From ITree Require Import
     Basics.Basics
     Basics.CategoryOps.

Import CatNotations.
#[local] Open Scope cat_scope.
(* end hide *)

Universes u_Fun_obj u_Fun_hom.
(** The following universe constraints are used to prevents
    unwanted unifications, in particular when using tactics. *)
Constraint Function.u_Fun_obj < Datatypes.sum.u0.
Constraint Function.u_Fun_obj < Datatypes.sum.u1.
Constraint Function.u_Fun_obj < Datatypes.prod.u0.
Constraint Function.u_Fun_obj < Datatypes.prod.u1.

(** The name of the category. *)
Definition Fun (A B : Type@{u_Fun_obj}) : Type@{u_Fun_hom} := A -> B.

(** The identity function, but can sometimes help type inference. *)
Definition apply_Fun {A B : Type} (f : Fun A B) : A -> B := f.

(** Extensional function equality *)
#[global] Instance eeq : Eq2 Fun :=
  fun A B f g => forall a : A, f a = g a.

(** Identity function *)
#[global] Instance Id_Fun : Id_ Fun :=
  fun A => fun a => a.

(** Function composition *)
#[global] Instance Cat_Fun : Cat Fun :=
  fun A B C f g => fun a => g (f a).

(** [void] as an initial object. *)
#[global] Instance Initial_void : Initial Fun void :=
  fun _ v => match v : void with end.

(** [unit] as a final object. *)
#[global] Instance Terminal_unit : Terminal Fun unit :=
  fun _ x => tt.

(** ** The [sum] coproduct. *)

(** In order to avoid putting upper bounds on the template universes of [Datatypes.sum]
    ([sum.u0] and [sum.u1]), it needs to be eta-expanded to introduce fresh universes
    names. This is done automatically because of the constraints above, but the following
    specialized version makes it explicit. It is defined as [Local], but can be refered
    outside of this module as [Function.sum]. *)
Local Definition sum (A B : Type) : Type := A + B.

(** Coproduct elimination *)
#[global] Instance case_sum : Case Fun sum :=
  fun {A B C} (f : A -> C) (g : B -> C) (x : A + B) =>
    match x with
    | inl a => f a
    | inr b => g b
    end.

(** Injections *)

#[global] Instance sum_inl : Inl Fun sum := fun A B => @inl A B.
#[global] Instance sum_inr : Inr Fun sum := fun A B => @inr A B.

(** ** The [pair] product. *)

(** Specialized version, for the same reason as for [sum]. *)
Local Definition prod (A B : Type) : Type := A * B.

#[global] Instance Pair_Fun : Pair Fun prod :=
  fun {A B C} l r c => (l c, r c).

#[global] Instance Fst_Fun : Fst Fun prod := @fst.
#[global] Instance Snd_Fun : Snd Fun prod := @snd.


(** ** Cartesian closure. *)
(** The [exponential] is just [_ -> _], which is a just another name for [Fun] *)
#[global] Instance Apply_Fun : Apply Fun prod Fun :=
    fun {A B} '(f, b) => f b.
  
#[global] Instance Curry_Fun : Curry Fun prod Fun :=
  fun {A B C} f => fun c a => f (c, a).
