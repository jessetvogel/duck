import Aesop
import Duck.Math.CategoryTheory
import Duck.Math.CommutativeAlgebra
open Math.CategoryTheory
open Math.CommutativeAlgebra

namespace Math.LinearAlgebra

variable {k : Ring}

-- The type of vector spaces
abbrev VectorSpace (h : k.field) := Module k

namespace VectorSpace

end VectorSpace

end Math.LinearAlgebra
