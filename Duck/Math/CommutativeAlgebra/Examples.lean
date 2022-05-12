import Aesop
import Duck.Math.CommutativeAlgebra.Ring
import Duck.Math.CommutativeAlgebra.Module
import Duck.Math.CommutativeAlgebra.Theorems

namespace Math.CommutativeAlgebra
open Ring

-- The ring of integers $\ZZ$.
@[aesop 99%] axiom ZZ : Ring
-- The ring $\ZZ$ is not trivial.
@[aesop 99%] axiom ZZ_not_trivial : ¬ZZ.trivial
-- The ring $\ZZ$ is a domain.
@[aesop 99%] axiom ZZ_domain : ZZ.domain
-- The ring $\ZZ$ is a PID.
@[aesop 99%] axiom ZZ_pid : ZZ.pid
-- The ring $\ZZ$ is not a field. For example, $2 \in \ZZ$ is not invertible.
@[aesop 99%] axiom ZZ_not_field : ¬ZZ.field
-- The ring $\ZZ$ is noetherian.
@[aesop 99%] axiom ZZ_noetherian : ZZ.noetherian
-- The ring $\ZZ$ is excellent.
@[aesop 99%] axiom ZZ_excellent : ZZ.excellent
-- The ring $\ZZ$ is not artin.
@[aesop 99%] axiom ZZ_not_artin : ¬ZZ.artin
-- The ring $\ZZ$ is not local. For example, $(2)$ and $(3)$ are both maximal ideals.
@[aesop 99%] axiom ZZ_not_local : ¬ZZ.is_local

-- The zero ring $\{ 0 \}$.
@[aesop 99%] axiom zero_ring : Ring
-- The zero ring is trivial.
@[aesop 99%] axiom zero_trivial : zero_ring.trivial
-- The zero ring is not a field, since $1 = 0$.
@[aesop 99%] axiom zero_not_field : ¬zero_ring.field
-- The zero ring is not a domain.
@[aesop 99%] axiom zero_not_domain : ¬zero_ring.domain
-- The zero ring is noetherian.
@[aesop 99%] axiom zero_noetherian : zero_ring.noetherian
-- The zero ring is reduced.
@[aesop 99%] axiom zero_reduced : zero_ring.reduced 
-- The zero ring is not local, since it does not have any maximal ideals.
@[aesop 99%] axiom zero_not_local : ¬zero_ring.is_local
-- The zero ring is finite, since it contains a single element.
@[aesop 99%] axiom zero_finite : zero_ring.finite

-- The ring of rational numbers $\QQ$.
@[aesop 99%] axiom QQ : Ring
-- The ring $\QQ$ is a field.
@[aesop 99%] axiom QQ_field : QQ.field
-- The ring $\QQ$ is not trivial.
@[aesop 99%] def QQ_not_trivial := not_trivial_of_domain (domain_of_field QQ_field)
-- The ring of real numbers $\RR$.
@[aesop 99%] axiom RR : Ring
-- The ring $\RR$ is not trivial.
@[aesop 99%] axiom RR_not_trivial : ¬RR.trivial
-- The ring $\RR$ is a field.
@[aesop 99%] axiom RR_is_field : RR.field
-- The ring of complex numbers $\CC$.
@[aesop 99%] axiom CC : Ring
-- The ring $\CC$ is not trivial.
@[aesop 99%] axiom CC_not_trivial : ¬CC.trivial
-- The ring $\CC$ is a field.
@[aesop 99%] axiom CC_is_field : CC.field

-- The inclusion of rings $\ZZ \to \QQ$.
@[aesop 99%] axiom ZZ_to_QQ : ZZ ⟶ QQ
-- The inclusion of rings $\QQ \to \RR$.
@[aesop 99%] axiom QQ_to_RR : QQ ⟶ RR
-- The inclusion of rings $\RR \to \CC$.
@[aesop 99%] axiom RR_to_CC : RR ⟶ CC
-- The inclusion of rings $\ZZ \to \RR$.
@[aesop 99%] noncomputable def ZZ_to_RR := QQ_to_RR ≫ ZZ_to_QQ
-- The inclusion of rings $\QQ \to \CC$.
@[aesop 99%] noncomputable def QQ_to_CC := RR_to_CC ≫ QQ_to_RR


@[aesop 99%] axiom cyclic_ring (n : Nat) : Ring

-- The field $\FF_2$ consisting of 2 elements.
@[aesop 99%] noncomputable def FF2 := cyclic_ring 2
-- The ring $\FF_2$ is not trivial.
@[aesop 99%] axiom FF2_not_trivial : ¬FF2.trivial
-- The ring $\FF_2$ is a field.
@[aesop 99%] axiom FF2_is_field : FF2.field
-- The ring $\FF_2$ is finite.
@[aesop 99%] axiom FF2_is_finite : FF2.finite
-- The quotient map $\ZZ \to \FF_2$.
@[aesop 99%] axiom ZZ_to_FF2 : ZZ ⟶ FF2

/- The $\ZZ$-module $\FF_2 = \ZZ/2\ZZ$ is not flat, since tensoring
\[ 0 \to \ZZ \xrightarrow{\cdot 2} \to \ZZ \to \ZZ/2\ZZ \to 0 \]
with $\ZZ/2\ZZ$ gives
\[ 0 \to \ZZ/2\ZZ \xrightarrow{0} \ZZ/2\ZZ \xrightarrow{\id} \ZZ/2\ZZ \to 0 \]
is not exact on the left. -/
@[aesop 99%] axiom FF2_over_ZZ_not_flat : ¬(module_of_ring_hom ZZ_to_FF2).flat
-- The $\ZZ$-module $\QQ$ is injective.
@[aesop 99%] axiom QQ_over_ZZ_injective : (module_of_ring_hom ZZ_to_QQ).injective
-- The ring $\ZZ[(1 + \sqrt{19}) / 2]$.
@[aesop 99%] axiom ZZ_quadr_19 : Ring
-- The ring $\ZZ[(1 + \sqrt{19}) / 2]$ is a PID.
@[aesop 99%] axiom ZZ_quadr_19_pid : ZZ_quadr_19.pid
-- The ring $\ZZ[(1 + \sqrt{19}) / 2]$ is not a Euclidean domain.
@[aesop 99%] axiom ZZ_quadr_19_not_eucl : ¬ZZ_quadr_19.euclidean

@[aesop 99%] axiom ufd_xy {R : Ring} (h : ufd R) : Ring
@[aesop 99%] axiom ufd_xy_of_ufd {R : Ring} (h : ufd R) : (ufd_xy h).ufd
@[aesop 99%] axiom ufd_xy_not_pid {R : Ring} (h : ufd R) : ¬(ufd_xy h).pid

-- Integral closure ZZ in \bar{QQ}
@[aesop 99%] axiom ZZ_bar : Ring

-- The field $\QQ(\sqrt{2})$.
@[aesop 99%] axiom QQ_sqrt2 : Ring
-- The ring $\QQ(\sqrt{2})$ is a field.
@[aesop 99%] axiom QQ_sqrt2_field : field QQ_sqrt2
-- The ring $\QQ(\sqrt{2})$ is noetherian.
@[aesop 99%] axiom QQ_sqrt2_nt : QQ_sqrt2.noetherian 
-- The inclusion $\QQ \to \QQ(\sqrt{2})$.
@[aesop 99%] axiom QQ_to_QQ_sqrt2 : QQ ⟶ QQ_sqrt2

-- The ring $k[x, y] / (x^2 - y^3)$ for a given field $k$.
@[aesop 99%] axiom cusp_ring {k : Ring} (h : field k) : Ring
-- The ring $k[x, y] / (x^2 - y^3)$ is not integrally closed. The element $x/y$ in the field of fractions is integral since $(x/y)^2 = y$, but does not live in the ring. 
@[aesop 99%] axiom cusp_ring_not_ic {k : Ring} (h : field k) : ¬(cusp_ring h).integrally_closed
-- The ring $k[x, y] / (x^2 - y^3)$ is a domain.
@[aesop 99%] axiom cusp_ring_dm {k : Ring} (h : field k) : domain (cusp_ring h)
-- The ring $k[x, y] / (x^2 - y^3)$ is noetherian.
@[aesop 99%] axiom cusp_ring_nt {k : Ring} (h : field k) : (cusp_ring h).noetherian
-- The ring $k[x, y] / (x^2 - y^3)$ is not artin.
@[aesop 99%] axiom cusp_ring_not_art {k : Ring} (h : field k) : ¬(cusp_ring h).artin
-- The ring $k[x, y] / (x^2 - y^3)$ not local. For example, both $(x, y)$ and $(x - 1, y - 1)$ are maximal ideals.
@[aesop 99%] axiom cusp_ring_not_lc  {k : Ring} (h : field k) : ¬(cusp_ring h).is_local

-- The natural numbers $\NN$.
-- @[aesop 99%] axiom NN : Monoid
-- The natural numbers $\NN$ are a fs monoid
-- @[aesop 99%] axiom NN_is_fs : fs NN

-- Polynomial ring $R[x]$ over a given ring $R$.
@[aesop 99%] axiom polynomial_ring (R : Ring) : Ring
@[aesop 99%] axiom polynomial_ring_ufd {R : Ring} (h : ufd R) : ufd (polynomial_ring R)
@[aesop 99%] axiom polynomial_ring_nt {R : Ring} (h : R.noetherian) : (polynomial_ring R).noetherian
@[aesop 99%] axiom polynomial_ring_dm {R : Ring} (h : R.domain) : (polynomial_ring R).domain
@[aesop 99%] axiom polynomial_ring_rd {R : Ring} (h : R.reduced) : (polynomial_ring R).reduced
@[aesop 99%] axiom polynomial_ring_not_lc (R : Ring) : ¬(polynomial_ring R).is_local

end Math.CommutativeAlgebra
