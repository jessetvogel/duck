namespace Math.CategoryTheory

universe u v

class Category (C : Type u) where
  Hom (X Y : C) : Type v
  id (X : C) : Hom X X
  comp {X Y Z : C} (f : Hom Y Z) (g : Hom X Y) : Hom X Z
  comp_assoc {X Y Z W : C} (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y) : comp (comp f g) h = comp f (comp g h)
  comp_id {X Y : C} (f : Hom X Y) : comp f (id X) = f
  id_comp {X Y : C} (f : Hom X Y) : comp (id Y) f = f

infix:50 " ⟶ " => Category.Hom
notation:80 "𝟙" arg:100 => Category.id arg
infixr:80 " ≫ " => Category.comp

variable {C : Type u} [Category C]

section objects

def initial (X : C) := ∀ (Y : C), ∃ (f : X ⟶ Y), ∀ (g : X ⟶ Y), f = g
def final (X : C) := ∀ (Y : C), ∃ (f : Y ⟶ X), ∀ (g : Y ⟶ X), f = g

end objects

namespace Category

namespace Hom

variable {X Y : C} {f : X ⟶ Y}

def mono (f : X ⟶ Y) := ∀ {Z : C} {g h : Z ⟶ X}, (f ≫ g) = (f ≫ h) → g = h
def epi (f : X ⟶ Y) := ∀ {Z : C} {g h : Y ⟶ Z}, (g ≫ f) = (h ≫ f) → g = h
def isomorphism (f : X ⟶ Y) := ∃ (g : Y ⟶ X), (g ≫ f) = id X ∧ (f ≫ g) = id Y
abbrev endomorphism (X : C) := X ⟶ X
structure automorphism (X : C) where
  map : X ⟶ X
  iso : isomorphism map

end Hom

end Category

structure Subobject (X : C) where
  obj : C
  map : obj ⟶ X
  mono : map.mono

end Math.CategoryTheory
