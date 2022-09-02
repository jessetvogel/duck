import Duck

open Math.CommutativeAlgebra
open Math.AlgebraicGeometry
open Math.CategoryTheory

set_option trace.debug true
-- set_option trace.aesop.steps true          -- displays all the steps Aesop takes
-- set_option trace.aesop.steps.tree true -- displays the search tree after each step

-- PASSING
#query : (A : Ring) (f : ZZ ⟶ ZZ)
#query : (A : Ring) (f : A ⟶ ZZ)
#query : (A : Ring) (f : RingHom A A)
#query : (R : Ring) (h : R.domain)
#query : (X : Scheme) (h : X.affine)
#query (X : Scheme) (h : X.affine) : (q : X.quasi_compact)
#query (X : Scheme) (h : X.affine) : (q : X.quasi_separated)
#query (X : Scheme) (h : X.affine) : (q : SchemeHom.affine (SchemeId X))
#query (X : Scheme) (h : X.affine) : (q : SchemeHom.quasi_compact (𝟙 X))
#query (X Y : Scheme) (f : X ⟶ Y) (h : SchemeHom.closed_immersion f) : (q : SchemeHom.locally_finite_type f)
#query (X Y: Scheme) (f : X ⟶ Y) (h : SchemeHom.etale f) : (h : SchemeHom.unramified f)
#query (X Y Z : Scheme) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : SchemeHom.proper f) (hg : SchemeHom.proper g) : (h : SchemeHom.proper (g ≫ f))
#query (X Y : Scheme) (f : X ⟶ Y) (hf : SchemeHom.finite f) : (h : SchemeHom.proper f)
#query (X Y Z : Scheme) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : SchemeHom.proper f) (hg : SchemeHom.proper g) : (h : SchemeHom.proper (g ≫ f))
#query (X Y Z : Scheme) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : SchemeHom.finite f) (hg : SchemeHom.finite g) : (h : SchemeHom.proper (g ≫ f))
#query (A B : Prop) (h : A → B) (a : A) : (b : B)
#query (A B : Prop) (h : A → B) (a₁ a₂ : A) : (b : B)
#query : (h : (affine_line (Spec QQ)).locally_noetherian)
#query : (X : Scheme) (h : X.integral)
#query : (R : Ring) (h : (Spec R).integral)
#query : (X Y : Scheme) (f : X ⟶ Y)
#query (U V W : Scheme) (g : U ⟶ V) (h : V ⟶ W) (hg : SchemeHom.closed_immersion g) (hh : SchemeHom.closed_immersion h) : (hc : SchemeHom.proper (h ≫ g))
#query : (R : Ring) (M N : Module R) (f : M ⟶ N)
#query : (X Y : Scheme) (f : X ⟶ Y) (h : ¬ SchemeHom.zariski_cover f)
#query : (P : {A B : Prop} → (h : A → B) → (x : A) → B)
#query : (P : {A B : Prop} → (h : A → B) → (a1 : A) → (a2 : A) →  B)
#query : (P : {A B : Prop} → (h : A → B) → (hb : ¬ B) → ¬ A)
#query (A B : Prop) (h : A → B) (hb : ¬ B) : (h : ¬ A)

-- FAILING

#query : (T : Type) (t : T)

-- FAILING

#query : (X : Scheme) (h₁ : X.affine) (h₂ : X.affine)

example : ∃ (X : Scheme) (h₁ : X.affine) (h₂ : X.affine), True := by {
  aesop;
}

example : ∃ (X : Scheme) (h₁ : X.affine) (h₂ : X.affine), True := by {
  apply Exists.intro (Spec ZZ);
  apply Exists.intro (spec_affine ZZ);
  apply Exists.intro (spec_affine ZZ);
  apply True.intro;
}

-- Fail for the same reason
-- #query : (X : Scheme) (h₁ : X.affine) (h₂ : X.quasi_compact)

-- FAILING

#query (X : Scheme) (h₁ : ¬ X.quasi_compact) : (h₂ : ¬ X.affine)

example : ∀ (X : Scheme) (h₁ : ¬ X.quasi_compact) , ∃ (h₂ : ¬ X.affine), True := by {
  aesop;
}

example : ∀ (X : Scheme) (h₁ : ¬ X.quasi_compact) , ∃ (h₂ : ¬ X.affine), True := by {
  intro X h₁;
  apply Exists.intro;
  apply True.intro;
  apply mt; -- modus tollens
  apply qc_of_af;
  apply h₁;
}

-- Fail for the same reason
-- #query (X Y : Scheme) (f : X ⟶ Y) (h : ¬ SchemeHom.universally_closed f) : (h : ¬ SchemeHom.proper f)
-- #query (X Y: Scheme) (f : X ⟶ Y) (h : ¬ SchemeHom.unramified f) : (h : ¬ SchemeHom.etale f)

-- FAILING
#query : (h : ¬ (Scheme.zariski_local Scheme.connected))

example : ∃ (h : ¬ (Scheme.zariski_local Scheme.connected)), True := by {
  aesop;
}

example : ∃ (h : ¬ (Scheme.zariski_local Scheme.connected)), True := by {
  apply Exists.intro;
  apply True.intro;
  apply mt; -- modus tollens
  intro arg;
  apply du_zar_lc;
  apply cn_of_int;
  apply spec_integral;
  apply ZZ_domain;
  apply cn_of_int;
  apply spec_integral;
  apply ZZ_domain;
  apply arg;
  apply du_not_cn;
  apply spec_not_empty;
  apply ZZ_not_trivial;
  apply spec_not_empty;
  apply ZZ_not_trivial;
}

-- FAILING (aesop: the goal contains metavariables, which is not currently supported.)

#query : (h : ¬ (SchemeHom.formally_etale (ec_to_P1 QQ_is_field)))

example : ∃ (h : ¬ (SchemeHom.formally_etale (ec_to_P1 QQ_is_field))), True := by {
  aesop;
}

example : ∃ (h : ¬ (SchemeHom.formally_etale (ec_to_P1 QQ_is_field))), True := by {
  apply Exists.intro;
  apply True.intro;
  apply mt; -- modus tollens
  intro arg;
  apply et_of_fet_lfp;
  apply arg;
  apply lfp_of_fp;
  apply ec_to_P1_fp;
  apply ec_to_P1_not_et;
}

-- Failing for the same reason
-- #query : (h : ¬ (scheme_map.open_immersion (ec_to_P1 QQ_is_field)))
-- #query : (h : ¬ (scheme_map.open_immersion (mSpec QQ_to_QQ_sqrt2)))

-- Failing for lack of examples
#query : (R : Ring) (M : Module R) (h₁ : M.flat) (h₂ : ¬ M.free)
