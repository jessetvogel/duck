import Duck.Math.CategoryTheory.Category
import Duck.Math.CategoryTheory.Functor

universe u v

namespace Math.CategoryTheory

variable {C D : Type u} [Category C] [Category D]

structure Adjunction (F : C → D) [Functor F] (G : D → C) [Functor G] :=
  m {X : C} {Y : D} : (F X ⟶ Y) → (X ⟶ G Y)
  minv {X : C} {Y : D} : (X ⟶ G Y) → (F X ⟶ Y)
  bijection₁ {X : C} {Y : D} (g : X ⟶ G Y) : m (minv g) = g
  bijection₂ (X : C) (Y : D) (f : F X ⟶ Y) : minv (m f) = f
  natural {X X': C} {Y Y': D} (f : X ⟶ X') (g : Y' ⟶ Y) (h : F X' ⟶ Y') : m (g ≫ h ≫ Functor.map f) = Functor.map g ≫ (m h) ≫ f

def adjunction_unit {F : C → D} [Functor F] {G : D → C} [Functor G] (a : Adjunction F G) : NaturalTransformation id (G ∘ F) where
  μ X := by apply a.m; rw [id]; exact Category.id _;
  natural {X Y : C} f := by {
    unfold Eq.mpr;
    simp;
    unfold Functor.map;
    unfold instFunctorId;
    unfold instFunctorComp;
    simp;
    let q₁ := a.natural f (𝟙 _) (𝟙 (F Y));
    rw [Category.id_comp, Category.id_comp, Functor.id, Category.id_comp ] at q₁;
    let q₂ := a.natural (𝟙 _) (Functor.map f) (𝟙 (F X));
    rw [Category.id_comp, Category.comp_id, Functor.id, Category.comp_id ] at q₂;
    rw [← q₁, ← q₂];
  }

-- def adjunction_counit {F : C → D} [Functor F] {G : D → C} [Functor G] (a : Adjunction F G) : NaturalTransformation (F ∘ G) id where
--   μ X := by apply a.minv; rw [id]; exact Category.id _;
--   natural {X Y : D} f := by {
--     unfold Eq.mpr;
--     simp;
--     unfold Functor.map;
--     unfold instFunctorId;
--     unfold instFunctorComp;
--     simp;
--     -- let q₁ := a.natural f (𝟙 _) (𝟙 (G X));
--     -- rw [Category.id_comp, Category.id_comp, Functor.id, Category.id_comp ] at q₁;
--     -- let q₂ := a.natural (𝟙 _) (Functor.map f) (𝟙 (F X));
--     -- rw [Category.id_comp, Category.comp_id, Functor.id, Category.comp_id ] at q₂;
--     -- rw [← q₁, ← q₂];
--     sorry;
--   }

end Math.CategoryTheory
