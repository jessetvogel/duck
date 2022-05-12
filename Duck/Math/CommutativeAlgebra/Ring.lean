import Aesop
import Duck.Math.CategoryTheory
open Math.CategoryTheory

namespace Math.CommutativeAlgebra

universe u v

-- The type of commutative rings.
-- class Ring (R : Type u) where
--   mul : G → G → G
--   unit : G
--   mul_assoc : ∀ (x y z : G), mul x (mul y z) = mul (mul x y) z
--   mul_unit : ∀ (x : G), mul x unit = x
--   unit_mul : ∀ (x : G), mul unit x = x
--   inv : G → G
--   mul_inv : ∀ (x : G), mul x (inv x) = unit
--   inv_mul : ∀ (x : G), mul (inv x) x = unit

axiom Ring : Type
axiom RingHom (R S : Ring) : Type
@[aesop 99%] axiom RingId (R : Ring) : RingHom R R
axiom RingComp {X Y Z : Ring} (f : RingHom Y Z) (g : RingHom X Y) : RingHom X Z
axiom RingAssoc {X Y Z W : Ring} (f : RingHom Z W) (g : RingHom Y Z) (h : RingHom X Y) : RingComp (RingComp f g) h = RingComp f (RingComp g h)
axiom RingCompId {X Y : Ring} (f : RingHom X Y) : RingComp f (RingId X) = f
axiom RingIdComp {X Y : Ring} (f : RingHom X Y) : RingComp (RingId Y) f = f

-- Category structure
noncomputable instance : Category Ring where
  Hom := RingHom
  id := RingId
  comp := RingComp
  comp_assoc := RingAssoc
  comp_id := RingCompId
  id_comp := RingIdComp

namespace Ring

-- A ring $R$ is trivial if it consists of a single element, that is, $R \simeq \{ 0 \}$.
axiom trivial (R : Ring) : Prop
-- A non-trivial ring $R$ is a domain if it has no zero-divisors. That is, $ab = 0$ implies $a = 0$ or $b = 0$ for all $a, b \in R$.
axiom domain (R : Ring) : Prop
-- A ring $R$ is a field if $1 \ne 0$ and every non-zero element is invertible.
axiom field (R : Ring) : Prop
/- A ring $R$ is artin if it satsifies the descending chain condition: for any decreasing sequence of ideals
\[ I_1 \supset I_2 \supset I_3 \supset \cdots \]
there exists some $N \in \NN$ such that $I_n = I_N$ for all $n \ge N$. -/
axiom artin (R : Ring) : Prop
/- A ring $R$ is noetherian if it satisfies the ascending chain condition: for any increasing sequence of ideals
\[ I_1 \subset I_2 \subset I_3 \subset \cdots \]
there exists $N \in \NN$ such that $I_n = I_N$ for any $n \ge N$.
Equivalently, $R$ is noetherian if all its ideals are finitely generated. -/
axiom noetherian (R : Ring) : Prop
axiom is_local (R : Ring) : Prop
axiom gorenstein (R : Ring) : Prop
axiom euclidean (R : Ring) : Prop
-- A ring is reduced if it has no non-zero nilpotent elements.
axiom reduced (R : Ring) : Prop
axiom valuation (R : Ring) : Prop
axiom dvr (R : Ring) : Prop
-- A ring is finite if it contains finitely many elements.
axiom finite (R : Ring) : Prop
axiom dedekind (R : Ring) : Prop
-- A ring $R$ is integrally closed if it contains all elements in its field of fraction that are integral over $R$.
axiom integrally_closed (R : Ring) : Prop
axiom ufd (R : Ring) : Prop
-- A ring $R$ is a PID if every ideal in $R$ is of the form $(x)$ for an element $x \in R$.
axiom pid (R : Ring) : Prop
axiom jacobson (R : Ring) : Prop
axiom complete (R : Ring) : Prop
axiom excellent (R : Ring) : Prop

-- axiom ideal (R : Ring) : Type -- define as a submodule of module_self R ? 

-- -- An ideal $I$ of a ring $R$ is maximal if $I \ne R$ and if $I \subset J \subsetneq R$ implies $I = J$ for any other ideal $J \subset R$.
-- axiom maximal_ideal {R : Ring} (I : ideal R) : Prop
-- -- An ideal $I$ of a ring $R$ is prime if $I \ne R$ and $xy \in I$ implies $a \in I$ or $b \in I$.
-- axiom prime_ideal {R : Ring} (I : ideal R) : Prop
-- -- An ideal $I$ of a ring $R$ is radical if $x^n \in I$ for some $x \in R$ and $n \ge 1$ implies $x \in I$.
-- axiom radical_ideal {R : Ring} (I : ideal R) : Prop
-- axiom nilradical zero_ideal unit_ideal jacobson_radical (R : Ring) : ideal R

end Ring

end Math.CommutativeAlgebra
