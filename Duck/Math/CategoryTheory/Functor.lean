import Duck.Math.CategoryTheory.Category
import Duck.Math.CategoryTheory.Bundled

namespace Math.CategoryTheory

universe u v

class Functor {C D : Type u} [Category C] [Category D] (F : C → D) where
  map : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  id : ∀ (X : C), map (𝟙 X) = 𝟙 (F X)
  comp : (∀ {X Y Z : C} (g : Y ⟶ Z) (f : X ⟶ Y), map (g ≫ f) = map g ≫ map f)

instance {C D E : Type u} [Category C] [Category D] [Category E] (F : C → D) [cF : Functor F] (G : D → E) [cG : Functor G] : Functor (G ∘ F) where
  map := by intro _ _ a; apply cG.map (cF.map a);
  id := by intros; unfold Function.comp; rw [cF.id, cG.id];
  comp := by intros; rw [cF.comp, cG.comp];

instance {C : Type u} [Category C] : Functor (id : C → C) where
  map := by intros _ _ f; exact f;
  id := by intros; rfl; 
  comp := by intros; rfl;

class ContraFunctor {C D : Type u} [Category C] [Category D] (F : C → D) where
  map : ∀ {X Y : C}, (X ⟶ Y) → (F Y ⟶ F X)
  id : ∀ (X : C), map (𝟙 X) = 𝟙 (F X)
  comp : (∀ {X Y Z : C} (g : Y ⟶ Z) (f : X ⟶ Y), map (g ≫ f) = map f ≫ map g)

variable {C D : Type u} [Category C] [Category D]

def faithful (F : C → D) [c : Functor F] : Prop := ∀ {X Y : C} (f g : X ⟶ Y), Functor.map f = c.map g → f = g
def full (F : C → D) [Functor F] : Prop := ∀ {X Y : C} (g : F X ⟶ F Y), ∃ (f : X ⟶ Y), Functor.map f = g
def essentially_surjective (F : C → D) [Functor F] : Prop := ∀ (Y : D), ∃ (X : C) (f : F X ⟶ Y), f.isomorphism

structure NaturalTransformation (F G : C → D) [Functor F] [Functor G] :=
  μ (X : C) : F X ⟶ G X
  natural {X Y : C} (f : X ⟶ Y) : (μ Y) ≫ (Functor.map f) = (Functor.map f) ≫ (μ X)

infix:50 " ⇒ " => NaturalTransformation

end Math.CategoryTheory
