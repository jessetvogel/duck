import Duck.Math.CategoryTheory.Category

namespace Math.CategoryTheory

variable {C : Type} [Category C] {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

theorem mono_id : (𝟙 X).mono := by {
  intro _ _ _;
  rw [Category.id_comp, Category.id_comp];
  intro t;
  exact t;
}

theorem epi_id : (𝟙 X).epi := by {
  intro _ _ _;
  rw [Category.comp_id, Category.comp_id];
  intro t;
  exact t;
}

theorem mono_comp (h₁ : f.mono) (h₂ : g.mono) : (g ≫ f).mono := by {
  intro _ _ _ a;
  rw [Category.comp_assoc, Category.comp_assoc] at a;
  exact h₁ (h₂ a);
}

theorem epi_comp (h₁ : f.epi) (h₂ : g.epi) : (g ≫ f).epi := by {
  intro _ _ _ a;
  rw [← Category.comp_assoc, ← Category.comp_assoc] at a;
  exact h₂ (h₁ a);
}

theorem mono_of_mono (h : (g ≫ f).mono) : f.mono := by {
  intro _ _ _ a;
  exact h (by rw [Category.comp_assoc, Category.comp_assoc, a]);
}

theorem epi_of_epi (h : (g ≫ f).epi) : g.epi := by {
  intro _ _ _ a;
  exact h (by rw [← Category.comp_assoc, ← Category.comp_assoc, a]);
}

theorem initial_iso (h₁ : initial X) (h₂ : initial Y) : ∃ (f : X ⟶ Y), f.isomorphism := by {
  match (h₁ Y) with
  | Exists.intro f hf => {
    apply Exists.intro f;
    match (h₂ X) with
    | Exists.intro g hg => {
      apply Exists.intro g;
      apply And.intro;
      match (h₁ X) with
      | Exists.intro i hi => rw [← hi (g ≫ f), hi (𝟙 X)];
      match (h₂ Y) with
      | Exists.intro i hi => rw [← hi (f ≫ g), hi (𝟙 Y)];
    }
  }
}

theorem final_iso (h₁ : final X) (h₂ : final Y) : ∃ (f : X ⟶ Y), f.isomorphism := by {
  match (h₂ X) with
  | Exists.intro f hf => {
    apply Exists.intro f;
    match (h₁ Y) with
    | Exists.intro g hg => {
      apply Exists.intro g;
      apply And.intro;
      match (h₁ X) with
      | Exists.intro i hi => rw [← hi (g ≫ f), hi (𝟙 X)];
      match (h₂ Y) with
      | Exists.intro i hi => rw [← hi (f ≫ g), hi (𝟙 Y)];
    }
  }
}

end Math.CategoryTheory
