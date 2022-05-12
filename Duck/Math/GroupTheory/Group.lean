import Aesop
import Duck.Math.CategoryTheory
open Math.CategoryTheory

namespace Math.GroupTheory

universe u v

class Group (G : Type u) where
  mul : G → G → G
  unit : G
  mul_assoc : ∀ (x y z : G), mul x (mul y z) = mul (mul x y) z
  mul_unit : ∀ (x : G), mul x unit = x
  unit_mul : ∀ (x : G), mul unit x = x
  inv : G → G
  mul_inv : ∀ (x : G), mul x (inv x) = unit
  inv_mul : ∀ (x : G), mul (inv x) x = unit

infixr:80 " ⬝ " => Group.mul

structure GroupHom (G H : Type u) (cG : Group G) (cH : Group H) where
  f : G → H
  hf : ∀ (x y : G), f (x ⬝ y) = (f x) ⬝ (f y)

instance : Category (Bundle Group) where
  Hom B₁ B₂ := GroupHom B₁.α B₂.α B₁.str B₂.str;
  id B := { f := id, hf := by intros; unfold id; rfl; }
  comp f g := { f := f.f ∘ g.f, hf := by intros; unfold Function.comp; rw [g.hf, f.hf]; }
  comp_assoc f g h := by rfl;
  comp_id f := by rfl;
  id_comp f := by rfl;

namespace Group
-- A group is trivial if it has one element.
def trivial (G : Type u) [Group G] := ∀ (x : G), x = unit
-- A group is abelian if $xy = yx$ for all $x, y \in G$.
def abelian (G : Type u) [Group G] := ∀ (x y : G), x ⬝ y = y ⬝ x
axiom solvable (G : Type u) [Group G] : Prop
axiom finitely_generated (G : Type u) [Group G] : Prop
-- A group is a torsion group if every element has finite order.
axiom torsion (G : Type u) [Group G] : Prop
-- A group $G$ is simple if its only normal subgroups are $\{ 1 \}$ and $G$ itself.
axiom simple (G : Type u) [Group G] : Prop
-- A subgroup $H \subset G$ is normal if $g H g^{-1} = H$ for all $g \in G$.
-- axiom normal {G H : Type u} [Group G] [Group H] (i : H ⟶ G) : Prop
-- A subgroup $H \subset G$ is central if it lies in the center of $G$.
-- axiom central {G H : Group} (i : H ⟶ G) : Prop
-- Whenever $N \subset G$ is a normal subgroup, one can form the quotient group $G/N$.
-- axiom quotient {G N : Group} {i : N ⟶ G} (h : normal i) : Group
end Group

variable {G : Type u} [Group G]

theorem mul_right {x y : G} (z : G) (h : x = y) : x ⬝ z = y ⬝ z := by rw [h];
theorem mul_left {x y : G} (z : G) (h : x = y) : z ⬝ x = z ⬝ y := by rw [h];

theorem inv_inv (x : G) : Group.inv (Group.inv x) = x := by {
  have q := mul_right x $ Group.inv_mul (Group.inv x);
  rw [← Group.mul_assoc, Group.inv_mul, Group.mul_unit, Group.unit_mul] at q;
  exact q;
}

end Math.GroupTheory
