import Aesop
import Duck.Math.CategoryTheory
open Math.CategoryTheory

namespace Math.CommutativeAlgebra

-- The type of commutative monoids.
axiom Monoid : Type
axiom MonoidHom (M N : Monoid) : Type

-- Category structure
instance : Category Monoid where
  Hom := MonoidHom
  id := sorryAx
  comp := sorryAx
  comp_assoc := sorryAx
  comp_id := sorryAx
  id_comp := sorryAx

namespace Monoid
-- The underlying set of a monoid.
-- axiom set_of_monoid (M : Monoid) : Set
-- axiom set_of_monoid_is_functor : functor set_of_monoid
-- A monoid $M$ is finitely generated if there exists a finite set of elements $m_1, m_2, \ldots, m_n \in M$ such that any $m \in M$ is the sum of various $m_i$.
axiom finitely_generated (M : Monoid) : Prop
-- A monoid $M$ is finitely presented if there exists a surjection $\NN^n \to M$ whose kernel is finitely generated.
axiom finitely_presented (M : Monoid) : Prop
-- A monoid $M$ is integral if the map to its groupification $M \to M^\textup{gp}$ is injective.
axiom integral (M : Monoid) : Prop
-- A monoid $M$ is saturated if for all $x \in M^\textup{gp}$ with $x^n \in M$ for some $n \ge 1$, we have $x \in M$.
axiom saturated (M : Monoid) : Prop
-- A monoid $M$ is sharp if $0 \in M$ is its only unit.
axiom sharp (M : Monoid) : Prop
-- A monoid $M$ is fine if it is finitely generated and integral.
axiom fine (M : Monoid) : Prop
-- A monoid $M$ is fs if it is fine and saturated.
axiom fs (M : Monoid) : Prop
-- A monoid $M$ is dull if it is a group.
axiom dull (M : Monoid) : Prop
end Monoid

namespace MonoidHom
variable {M N : Monoid}
-- A morphism of monoids is integral if [...]
axiom integral (f : M ⟶ N) : Prop
-- A morphism of monoids is local if [...]
axiom is_local (f : M ⟶ N) : Prop
-- A morphism of monoids is exact if [...]
axiom exact (f : M ⟶ N) : Prop
-- A morphism of monoids is smooth if [...]
axiom smooth (f : M ⟶ N) : Prop
-- A morphism of monoids is etale if [...]
axiom etale (f : M ⟶ N) : Prop
-- A morphism of monoids is injective if the underlying map of sets is injective.
-- def injective (f : M ⟶ N) := set_map.injective (fmap set_of_monoid_is_functor f)
-- A morphism of monoids is surjective if the underlying map of sets is surjective.
-- def surjective (f : M ⟶ N) := set_map.surjective (fmap set_of_monoid_is_functor f) 
end MonoidHom

end Math.CommutativeAlgebra
