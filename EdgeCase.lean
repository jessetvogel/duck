import Aesop

axiom Ring : Type
axiom Scheme : Type
axiom affine (X : Scheme) : Prop
axiom quasi_compact (X : Scheme) : Prop

@[aesop 99%] axiom Spec : Ring → Scheme
@[aesop 99%] axiom qc_of_af {X : Scheme} (h : affine X) : quasi_compact X
@[aesop 99%] axiom ZZ : Ring
@[aesop 99%] axiom spec_affine (R : Ring) : affine (Spec R)

theorem thm : ∃ (X : Scheme) (h₁ : affine X) (h₂ : quasi_compact X), True := by {
  aesop;
}

#print thm

-- example : ∃ (X : Scheme) (h₁ : P X) (h₂ : Q X), True := by {
--   apply Exists.intro (Spec ZZ);
--   apply Exists.intro (spec_affine ZZ);
--   apply Exists.intro (qc_of_af (spec_affine ZZ));
--   apply True.intro;
-- }
