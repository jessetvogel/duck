import Aesop
import Duck.Math.CommutativeAlgebra.Ring
import Duck.Math.CommutativeAlgebra.Module

namespace Math.CommutativeAlgebra
variable {R : Ring} {M : Module R}

namespace Ring
-- Every field is a domain, because if $xy = 0$ with $x \ne 0$, then $y = 0 \cdot x^{-1} = 0$.
@[aesop 99%] axiom domain_of_field (h : R.field) : R.domain
-- Every field is noetherian, because the only (maximal) ideal is $(0)$.
@[aesop 99%] axiom noetherian_of_field (h : R.field) : R.noetherian
-- Every domain is reduced, because if $x^n = 0$ then $x = 0$.
@[aesop 99%] axiom reduced_of_domain (h : R.domain) : R.reduced
-- Every field is a local ring, since $(0)$ is the only (maximal) ideal.
@[aesop 99%] axiom local_of_field (h : R.field) : R.is_local
-- Every domain is non-trivial.
@[aesop 99%] axiom not_trivial_of_domain (h : R.domain) : ¬R.trivial
-- Every finite domain is a field.
@[aesop 99%] axiom field_of_finite_domain (h₁ : R.domain) (h₂ : R.finite) : R.field
-- Every PID is a UFD.
@[aesop 99%] axiom ufd_of_pid (h : R.pid) : R.ufd
-- Every UFD is integrally closed.
@[aesop 99%] axiom integrally_closed_of_ufd (h : R.ufd) : R.integrally_closed
-- Every integrally closed ring is a domain.
@[aesop 99%] axiom domain_of_integrally_closed (h : R.integrally_closed) : R.domain
-- Every Euclidean ring is a PID.
@[aesop 99%] axiom pid_of_euclidean (h : R.euclidean) : R.pid
-- Every field is a Euclidean ring.
@[aesop 99%] axiom euclidean_of_field (h : R.field) : R.euclidean
-- Every artin ring is noetherian.
@[aesop 99%] axiom noetherian_of_artin (h : R.artin) : R.noetherian
-- Every field is excellent.
@[aesop 99%] axiom excellent_of_field (h : R.field) : R.excellent
-- Every noetherian complete local ring is excellent.
@[aesop 99%] axiom excellent_of_noetherian_complete_local (h1 : R.noetherian) (h2 : R.complete) (h3 : R.is_local) : R.excellent
-- Every field is Jacobson.
@[aesop 99%] axiom jcb_of_field (h : R.field) : R.jacobson
end Ring

namespace Module
-- Any free module is projective.
@[aesop 99%] axiom projective_of_free (h : M.free) : M.projective
-- Any projective module is flat.
@[aesop 99%] axiom flat_of_projective (h : M.projective) : M.flat
-- Any free module is flat.
@[aesop 99%] def flat_of_free (h : M.free) := flat_of_projective (projective_of_free h)
-- Every ring $R$ is a cyclic module over itself.
@[aesop 99%] axiom cyclic_self (R : Ring) : (module_self R).cyclic
-- Every ring $R$ is a free module over itself.
@[aesop 99%] axiom free_self (R : Ring) : (module_self R).free
end Module

end Math.CommutativeAlgebra
