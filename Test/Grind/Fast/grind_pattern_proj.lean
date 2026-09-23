import Lynth.Grind.Tactic
universe v v₁ v₂ u u₁ u₂

public section
namespace CategoryTheory

class Quiver (V : Type u) where
  Hom : V → V → Sort v

infixr:10 " ⟶ " => Quiver.Hom

class CategoryStruct (obj : Type u) : Type max u (v + 1) extends Quiver.{v + 1} obj where
  /-- The identity morphism on an object. -/
  id : ∀ X : obj, Hom X X
  /-- Composition of morphisms in a category, written `f ≫ g`. -/
  comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

notation "𝟙" => CategoryStruct.id  -- type as \b1

infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h

structure Prefunctor (V : Type u₁) [Quiver.{v₁} V] (W : Type u₂) [Quiver.{v₂} W] where
  obj : V → W
  map : ∀ {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y)

structure Functor (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] : Type max v₁ v₂ u₁ u₂
    extends Prefunctor C D where
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g


set_option trace.grind.ematch.pattern true

/--
trace: [grind.ematch.pattern] Functor.map_id: [@Prefunctor.map #5 _ #3 _ (@Functor.toPrefunctor _ #4 _ #2 #1) #0 #0 (@CategoryStruct.id _ _ #0)]
-/
#guard_msgs in
grind_pattern Functor.map_id => self.map (𝟙 X)

/--
trace: [grind.ematch.pattern] Functor.map_comp: [@Prefunctor.map #9 _ #7 _ (@Functor.toPrefunctor _ #8 _ #6 #5) #4 #2 (@CategoryStruct.comp _ _ #4 #3 #2 #1 #0)]
-/
#guard_msgs in
grind_pattern Functor.map_comp => self.map (f ≫ g)
