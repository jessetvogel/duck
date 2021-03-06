import Duck.Math.CategoryTheory.Category

namespace Math.CategoryTheory

variable {C : Type} [Category C] {X Y Z : C} {f : X â¶ Y} {g : Y â¶ Z}

theorem mono_id : (ð X).mono := by {
  intro _ _ _;
  rw [Category.id_comp, Category.id_comp];
  intro t;
  exact t;
}

theorem epi_id : (ð X).epi := by {
  intro _ _ _;
  rw [Category.comp_id, Category.comp_id];
  intro t;
  exact t;
}

theorem mono_comp (hâ : f.mono) (hâ : g.mono) : (g â« f).mono := by {
  intro _ _ _ a;
  rw [Category.comp_assoc, Category.comp_assoc] at a;
  exact hâ (hâ a);
}

theorem epi_comp (hâ : f.epi) (hâ : g.epi) : (g â« f).epi := by {
  intro _ _ _ a;
  rw [â Category.comp_assoc, â Category.comp_assoc] at a;
  exact hâ (hâ a);
}

theorem mono_of_mono (h : (g â« f).mono) : f.mono := by {
  intro _ _ _ a;
  exact h (by rw [Category.comp_assoc, Category.comp_assoc, a]);
}

theorem epi_of_epi (h : (g â« f).epi) : g.epi := by {
  intro _ _ _ a;
  exact h (by rw [â Category.comp_assoc, â Category.comp_assoc, a]);
}

theorem initial_iso (hâ : initial X) (hâ : initial Y) : â (f : X â¶ Y), f.isomorphism := by {
  match (hâ Y) with
  | Exists.intro f hf => {
    apply Exists.intro f;
    match (hâ X) with
    | Exists.intro g hg => {
      apply Exists.intro g;
      apply And.intro;
      match (hâ X) with
      | Exists.intro i hi => rw [â hi (g â« f), hi (ð X)];
      match (hâ Y) with
      | Exists.intro i hi => rw [â hi (f â« g), hi (ð Y)];
    }
  }
}

theorem final_iso (hâ : final X) (hâ : final Y) : â (f : X â¶ Y), f.isomorphism := by {
  match (hâ X) with
  | Exists.intro f hf => {
    apply Exists.intro f;
    match (hâ Y) with
    | Exists.intro g hg => {
      apply Exists.intro g;
      apply And.intro;
      match (hâ X) with
      | Exists.intro i hi => rw [â hi (g â« f), hi (ð X)];
      match (hâ Y) with
      | Exists.intro i hi => rw [â hi (f â« g), hi (ð Y)];
    }
  }
}

end Math.CategoryTheory
