import Duck

open Math.CommutativeAlgebra
open Math.AlgebraicGeometry
open Math.CategoryTheory

-- PASSING
#query : (A : Ring) (f : ZZ ⟶ ZZ)
#query : (A : Ring) (f : A ⟶ ZZ)
#query : (R : Ring)
#query : (X : Scheme) (h : X.affine)
#query : (X : Scheme) (h₁ : X.affine) (h₂ : X.quasi_compact)
#query (X : Scheme) (h : X.affine) : (h : X.quasi_compact)
#query (X : Scheme) (h : X.affine) : (h : X.quasi_separated)
#query (X : Scheme) (h : X.affine) : (h : SchemeHom.affine (SchemeId X))
#query (X : Scheme) (h : X.affine) : (h : SchemeHom.quasi_compact (𝟙 X))
#query (X Y : Scheme) (f : X ⟶ Y) (h : SchemeHom.closed_immersion f) : (h : SchemeHom.locally_finite_type f)

#query : (P : {A B : Prop} → (h : A → B) → (x : A) → B)
#query : (P : {A B : Prop} → (h : A → B) → (a1 : A) → (a2 : A) →  B)

#query (X Y: Scheme) (f : X ⟶ Y) (h : SchemeHom.etale f) : (h : SchemeHom.unramified f)

-- FAILING
#query : (A : Ring) (f : RingHom A A)
-- example : ∃ (A : Ring) (f : A ⟶ A), True := by {
--   apply Exists.intro ZZ;
--   apply Exists.intro (RingId ZZ);
--   exact True.intro;
-- }

#query (X Y Z : Scheme) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : SchemeHom.proper f) (hg : SchemeHom.proper g) : (h : SchemeHom.proper (g ≫ f))
#query (X Y : Scheme) (f : X ⟶ Y) (hf : SchemeHom.finite f) : (h : SchemeHom.proper f)

#query (X Y Z : Scheme) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : SchemeHom.proper f) (hg : SchemeHom.proper g) : (h : SchemeHom.proper (g ≫ f))
#query (X Y Z : Scheme) (f : X ⟶ Y) (g : Y ⟶ Z) (hf : SchemeHom.finite f) (hg : SchemeHom.finite g) : (h : SchemeHom.proper (g ≫ f))

#query (A B : Prop) (h : A → B) (a : A) : (b : B)
#query (A B : Prop) (h : A → B) (a₁ a₂ : A) : (b : B)
-- #query : (P : {A B : Prop} → (h : A → B) → (hb : ¬ B) → ¬ A)

@[aesop 99%] axiom modus_tollens {P Q : Prop} (h : P → Q) (hq : ¬ Q) : ¬ P
#query (X : Scheme) (h : ¬ X.quasi_compact) : (h : ¬ X.affine)

#query (X Y : Scheme) (f : X ⟶ Y) (h : ¬ SchemeHom.universally_closed f) : (h : ¬ SchemeHom.proper f)
#query (X Y: Scheme) (f : X ⟶ Y) (h : ¬ SchemeHom.unramified f) : (h : ¬ SchemeHom.etale f)


#query : (h : (affine_line (Spec QQ)).locally_noetherian)
#query : (X : Scheme) (h₁ : X.affine) (h₂ : X.quasi_compact)
#query : (X : Scheme) (h : X.integral)
#query : (R : Ring) (h : (Spec R).integral)
#query : (X Y : Scheme) (f : X ⟶ Y)
#query : (R : Ring) (M N : Module R) (f : M ⟶ N)
#query : (R : Ring) (M : Module R) (h₁ : M.flat) (h₂ : ¬ M.free)
#query (U V W : Scheme) (g : U ⟶ V) (h : V ⟶ W) (hg : SchemeHom.closed_immersion g) (hh : SchemeHom.closed_immersion h) : (hc : SchemeHom.proper (h ≫ g))
#query : (X Y : Scheme) (f : X ⟶ Y) (h : ¬ SchemeHom.zariski_cover f)
-- #query : (h1 : not (scheme_map.formally_etale (ec_to_P1 QQ_is_field))) (h2 : not (scheme_map.open_immersion (ec_to_P1 QQ_is_field)))
-- #query : (h : not (scheme_map.open_immersion (mSpec QQ_to_QQ_sqrt2)))

-- #query (T S : Type) (F : T → S) (h : functor F) (X Y : T) (f : Morphism X_ Y_) : Morphism (F_ X_) (F_ Y_))
-- #query : (h : not (zariski_local scheme.connected))
