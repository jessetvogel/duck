import Duck.Math.CategoryTheory.Category

namespace Math.CategoryTheory

universe u v

structure Bundle (c : Type u → Type v) where
  α : Type u
  str : c α

end Math.CategoryTheory
