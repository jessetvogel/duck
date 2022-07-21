import Duck.Math.AlgebraicGeometry.Scheme
import Duck.Math.AlgebraicGeometry.Theorems
import Duck.Math.CategoryTheory.Functor
open Math.CategoryTheory
open Math.CommutativeAlgebra
open Math.AlgebraicGeometry.SchemeHom

namespace Math.AlgebraicGeometry

@[aesop 99%] axiom Spec : Ring → Scheme
@[aesop 99%] axiom SpecMap {R S : Ring} (f : R ⟶ S) : Spec S ⟶ Spec R
noncomputable instance : ContraFunctor Spec where
  map := SpecMap
  id := sorry
  comp := sorry

-- The empty scheme $\varnothing = \Spec(\{ 0 \})$.
@[aesop 99%] noncomputable def empty_scheme := Spec zero_ring
-- The empty scheme is empty.
@[aesop 99%] axiom empty_empty: empty_scheme.empty
-- The empty scheme is ¬irreducible.
@[aesop 99%] axiom empty_not_irreducible : ¬empty_scheme.irreducible
-- The empty scheme is ¬integral.
@[aesop 99%] axiom empty_not_integral : ¬empty_scheme.integral
-- The empty scheme is ¬connected.
@[aesop 99%] axiom empty_not_connected : ¬empty_scheme.connected

-- The scheme $\Spec(R)$ is non-empty whenever $R$ is ¬the zero ring.
@[aesop 99%] axiom spec_not_empty {R : Ring} (h : ¬R.trivial) : ¬(Spec R).empty
-- The scheme $\Spec(R)$ is affine for any ring $R$.
@[aesop 99%] axiom spec_affine (R : Ring) : (Spec R).affine
-- The scheme $\Spec(R)$ is integral whenever $R$ is a domain.
@[aesop 99%] axiom spec_integral {R : Ring} (h : R.domain) : (Spec R).integral
-- The scheme $\Spec(R)$ is noetherian whenever $R$ is noetherian.
@[aesop 99%] axiom spec_noetherian {R : Ring} (h : R.noetherian) : (Spec R).noetherian
-- The scheme $\Spec(k)$ is regular whenever $k$ is field.
@[aesop 99%] axiom spec_regular {k : Ring} (h : k.field) : (Spec k).regular
-- axiom spec_irreducible {R : Ring} (h : prime_ideal (nilradical R)) : irreducible (Spec R)
@[aesop 99%] axiom spec_normal {R : Ring} (h : R.integrally_closed) : (Spec R).normal
@[aesop 99%] axiom spec_not_normal {R : Ring} (h : ¬R.integrally_closed) : ¬(Spec R).normal
@[aesop 99%] axiom spec_excellent {R : Ring} (h : R.excellent) : (Spec R).excellent
@[aesop 99%] axiom spec_jacobson {R : Ring} (h : R.jacobson) : (Spec R).jacobson 
-- The scheme $\Spec(R)$ is reduced whenever $R$ is reduced.
@[aesop 99%] axiom spec_reduced {R : Ring} (h : R.reduced) : (Spec R).reduced

-- The affine line $\AA^1_X = \AA^1 \times X$ over a given scheme $X$.
@[aesop 99%] axiom affine_line (X : Scheme) : Scheme
@[aesop 99%] axiom affine_line_af (R : Ring) : (affine_line (Spec R)).affine
@[aesop 99%] axiom hilbert_basis_thm {X : Scheme} (h : X.locally_noetherian) : (affine_line X).locally_noetherian
@[aesop 99%] axiom affine_line_rd {X : Scheme} (h : X.reduced) : (affine_line X).reduced
@[aesop 99%] axiom affine_line_sp {X : Scheme} (h : X.separated) : (affine_line X).separated
@[aesop 99%] axiom affine_line_qsp {X : Scheme} (h : X.quasi_separated) : (affine_line X).quasi_separated
@[aesop 99%] axiom affine_line_jcb {X : Scheme} (h : X.jacobson) : (affine_line X).jacobson
@[aesop 99%] axiom affine_line_int {X : Scheme} (h : X.integral) : (affine_line X).integral
@[aesop 99%] axiom affine_line_nm {X : Scheme} (h : X.normal) : (affine_line X).normal
-- axiom affine_line_cn {X : Scheme} (h : scheme.connected X) : scheme.connected (affine_line X)

-- AA^1_X \to X
@[aesop 99%] axiom affine_line_to_base (X : Scheme) : (affine_line X) ⟶ X
@[aesop 99%] axiom affine_line_to_base_ff (X : Scheme) : faithfully_flat (affine_line_to_base X)
@[aesop 99%] axiom affine_line_to_base_sm (X : Scheme) : smooth (affine_line_to_base X)
@[aesop 99%] axiom affine_line_to_base_fp (X : Scheme) : finitely_presented (affine_line_to_base X)
@[aesop 99%] def affine_line_rg {X : Scheme} (h : X.regular) := src_rg_of_sm_trg_rg h (affine_line_to_base_sm X)

-- The projective line over a given scheme $X$.
@[aesop 99%] axiom proj_line (X : Scheme) : Scheme
-- axiom proj_line_not_affine (X : Scheme) : ¬(proj_line X).affine -- only if X is non-empty ..
-- axiom proj_line_integral {X : Scheme} (h : integral X) : integral (proj_line X)
-- axiom proj_line_separated {X : Scheme} (h : scheme.separated X) : scheme.separated (proj_line X)

-- The scheme $X \times \Spec(\ZZ[x]/(x^2))$ for a given scheme $X$.
@[aesop 99%] axiom thick (X : Scheme) : Scheme
@[aesop 99%] axiom thick_af {X : Scheme} (h : X.affine) : (thick X).affine
@[aesop 99%] axiom thick_cn {X : Scheme} (h : X.connected) : (thick X).connected
@[aesop 99%] axiom thick_lnt {X : Scheme} (h : X.locally_noetherian) : (thick X).locally_noetherian
@[aesop 99%] axiom thick_not_rd (X : Scheme) : ¬(thick X).reduced -- TODO: only if X is non-empty ..
@[aesop 99%] axiom thick_sp {X : Scheme} (h : X.separated) : (thick X).separated
@[aesop 99%] axiom thick_qsp {X : Scheme} (h : X.quasi_separated) : (thick X).quasi_separated

-- (thick X) \to X
@[aesop 99%] axiom thick_to_base (X : Scheme) : (thick X) ⟶ X
@[aesop 99%] axiom thick_to_base_fn (X : Scheme) : finite (thick_to_base X) 
@[aesop 99%] axiom thick_to_base_fp (X : Scheme) : finitely_presented (thick_to_base X)
@[aesop 99%] axiom thick_to_base_not_ci (X : Scheme) : ¬(closed_immersion (thick_to_base X)) -- only if X is non-empty
@[aesop 99%] axiom thick_to_base_fl (X : Scheme) : flat (thick_to_base X)
@[aesop 99%] axiom thick_to_base_sj (X : Scheme) : surjective (thick_to_base X)

-- Elliptic curve over a field
@[aesop 99%] axiom ec {k : Ring} (h : k.field) : Scheme
@[aesop 99%] axiom ec_not_af {k : Ring} (h : k.field) : ¬(ec h).affine
@[aesop 99%] axiom ec_sp {k : Ring} (h : k.field) : (ec h).separated
@[aesop 99%] axiom ec_qc {k : Ring} (h : k.field) : (ec h).quasi_compact
@[aesop 99%] axiom ec_int {k : Ring} (h : k.field) : (ec h).integral
@[aesop 99%] axiom ec_rg {k : Ring} (h : k.field) : (ec h).regular

-- Elliptic curve --> P1 by x coordinate
@[aesop 99%] axiom ec_to_P1 {k : Ring} (h : k.field) : (ec h) ⟶ (proj_line (Spec k))
@[aesop 99%] axiom ec_to_P1_not_et {k : Ring} (h : k.field) : ¬etale (ec_to_P1 h)
@[aesop 99%] axiom ec_to_P1_fn {k : Ring} (h : k.field) : finite (ec_to_P1 h)
@[aesop 99%] axiom ec_to_P1_fl {k : Ring} (h : k.field) : flat (ec_to_P1 h)
@[aesop 99%] axiom ec_to_P1_sj {k : Ring} (h : k.field) : surjective (ec_to_P1 h)
@[aesop 99%] axiom ec_to_P1_fp {k : Ring} (h : k.field) : finitely_presented (ec_to_P1 h)

-- Integral closure of $\ZZ$ in $\bar{\QQ}$.
@[aesop 99%] noncomputable def Spec_ZZ_bar := Spec ZZ_bar
@[aesop 99%] axiom ZZ_bar_not_cm : ¬Spec_ZZ_bar.cohen_macaulay
@[aesop 99%] axiom ZZ_bar_int : Spec_ZZ_bar.integral
@[aesop 99%] axiom ZZ_bar_not_lnt : ¬Spec_ZZ_bar.locally_noetherian
@[aesop 99%] axiom ZZ_bar_nm : Spec_ZZ_bar.normal

-- Spec CC \to Spec RR
@[aesop 99%] noncomputable def Spec_CC_to_Spec_RR : Spec CC ⟶ Spec RR := by exact ContraFunctor.map RR_to_CC; -- TODO: why cannot remove `by exact` ?
@[aesop 99%] axiom Spec_CC_to_Spec_RR_not_ci : ¬ closed_immersion Spec_CC_to_Spec_RR
@[aesop 99%] axiom Spec_CC_to_Spec_RR_et : etale Spec_CC_to_Spec_RR
@[aesop 99%] axiom Spec_CC_to_Spec_RR_fn : finite Spec_CC_to_Spec_RR
@[aesop 99%] axiom Spec_CC_to_Spec_RR_fl : flat Spec_CC_to_Spec_RR
@[aesop 99%] axiom Spec_CC_to_Spec_RR_not_imm : ¬ immersion Spec_CC_to_Spec_RR
@[aesop 99%] axiom Spec_CC_to_Spec_RR_fp : finitely_presented Spec_CC_to_Spec_RR
@[aesop 99%] axiom Spec_CC_to_Spec_RR_af : finitely_presented Spec_CC_to_Spec_RR
@[aesop 99%] axiom Spec_CC_to_Spec_RR_sj : surjective Spec_CC_to_Spec_RR

-- Spec QQ \sqcup Spec QQ = Spec (QQ x QQ)
@[aesop 99%] axiom two_pts {k : Ring} (h : k.field) : Scheme
@[aesop 99%] axiom two_pts_af {k : Ring} (h : k.field) : (two_pts h).affine
@[aesop 99%] axiom two_pts_not_cn {k : Ring} (h : k.field) : ¬(two_pts h).connected
@[aesop 99%] axiom two_pts_rg {k : Ring} (h : k.field) : (two_pts h).regular
@[aesop 99%] axiom two_pts_nt {k : Ring} (h : k.field) : (two_pts h).noetherian

-- infinite union of points over a field
@[aesop 99%] axiom inf_points {k : Ring} (h : k.field) : Scheme
@[aesop 99%] axiom inf_points_not_qc {k : Ring} (h : k.field) : ¬ (inf_points h).quasi_compact
@[aesop 99%] axiom inf_points_not_nt {k : Ring} (h : k.field) : ¬ (inf_points h).noetherian
@[aesop 99%] axiom inf_points_lnt {k : Ring} (h : k.field) : (inf_points h).locally_noetherian
@[aesop 99%] axiom inf_points_rg {k : Ring} (h : k.field) : (inf_points h).regular
@[aesop 99%] axiom inf_points_sp {k : Ring} (h : k.field) : (inf_points h).separated
@[aesop 99%] axiom inf_points_not_cn {k : Ring} (h : k.field) : ¬ (inf_points h).connected

-- infinite union of points to point
@[aesop 99%] axiom int_pts_to_pt {k : Ring} (h : k.field) : (inf_points h) ⟶ (Spec k)

@[aesop 99%] axiom open_complement {X Z : Scheme} {i : Z ⟶ X} (h : closed_immersion i) : Scheme
@[aesop 99%] axiom open_complement_inclusion {X Z : Scheme} {i : Z ⟶ X} (h : closed_immersion i) : (open_complement h) ⟶ X

-- Spec QQ[sqrt{2}]
@[aesop 99%] noncomputable def Spec_QQ_sqrt2 := Spec QQ_sqrt2

-- Spec QQ[sqrt{2}] \to Spec QQ
@[aesop 99%] noncomputable def Spec_QQ_sqrt2_to_Spec_QQ : Spec QQ_sqrt2 ⟶ Spec QQ  := by exact ContraFunctor.map QQ_to_QQ_sqrt2
@[aesop 99%] axiom Spec_QQ_sqrt2_to_Spec_QQ_not_zrc : ¬ (zariski_cover Spec_QQ_sqrt2_to_Spec_QQ)
@[aesop 99%] axiom Spec_QQ_sqrt2_to_Spec_QQ_etc : etale_cover Spec_QQ_sqrt2_to_Spec_QQ
@[aesop 99%] axiom Spec_QQ_sqrt2_to_Spec_QQ_fn : finite Spec_QQ_sqrt2_to_Spec_QQ
@[aesop 99%] axiom Spec_QQ_sqrt2_to_Spec_QQ_not_ci : ¬ closed_immersion Spec_QQ_sqrt2_to_Spec_QQ

-- Plane minus origin
@[aesop 99%] axiom plane_no_origin {k : Ring} (h : k.field) : Scheme
@[aesop 99%] axiom plane_no_origin_not_af {k : Ring} (h : k.field) : ¬(plane_no_origin h).affine
@[aesop 99%] axiom plane_no_origin_int {k : Ring} (h : k.field) : (plane_no_origin h).integral 
@[aesop 99%] axiom plane_no_origin_qc {k : Ring} (h : k.field) : (plane_no_origin h).quasi_compact
@[aesop 99%] axiom plane_no_origin_rg {k : Ring} (h : k.field) : (plane_no_origin h).regular
@[aesop 99%] axiom plane_no_origin_sp {k : Ring} (h : k.field) : (plane_no_origin h).separated

-- Plane minus origin to Spec k
@[aesop 99%] axiom plane_no_origin_to_Spec_k {k : Ring} (h : k.field) : (plane_no_origin h) ⟶ (Spec k)
@[aesop 99%] axiom plane_no_origin_to_Spec_k_not_et {k : Ring} (h : k.field) : ¬ (etale (plane_no_origin_to_Spec_k h))
@[aesop 99%] axiom plane_no_origin_to_Spec_k_ffl {k : Ring} (h : k.field) : faithfully_flat (plane_no_origin_to_Spec_k h)
@[aesop 99%] axiom plane_no_origin_to_Spec_k_not_ff {k : Ring} (h : k.field) : ¬ (finite_fibers (plane_no_origin_to_Spec_k h))
@[aesop 99%] axiom plane_no_origin_to_Spec_k_fp {k : Ring} (h : k.field) : finitely_presented (plane_no_origin_to_Spec_k h)
@[aesop 99%] axiom plane_no_origin_to_Spec_k_not_pr {k : Ring} (h : k.field) : ¬ (proper (plane_no_origin_to_Spec_k h))
@[aesop 99%] axiom plane_no_origin_to_Spec_k_sm {k : Ring} (h : k.field) : smooth (plane_no_origin_to_Spec_k h)
@[aesop 99%] axiom plane_no_origin_to_Spec_k_sp {k : Ring} (h : k.field) : separated (plane_no_origin_to_Spec_k h) 
@[aesop 99%] axiom plane_no_origin_to_Spec_k_not_ur {k : Ring} (h : k.field) : ¬ (unramified (plane_no_origin_to_Spec_k h))
-- axiom plane_no_origin_to_Spec_k_not_ci {k : Ring} (h : k.field) : ¬(closed_immersion (plane_no_origin_to_Spec_k h))

-- The disjoint union $X \sqcup Y$ of two schemes $X$ and $Y$.
@[aesop 99%] axiom disjoint_union (X Y : Scheme) : Scheme
-- The disjoint union $X \sqcup Y$ is ¬connected whenever $X$ and $Y$ are non-empty.
@[aesop 99%] axiom du_not_cn {X Y : Scheme} (h₁ : ¬ X.empty) (h₂ : ¬ Y.empty) : ¬(disjoint_union X Y).connected
-- Whenever a local property of schemes $P$ holds for $X$ and $Y$, it also holds for the disjoint union $X \sqcup Y$.
@[aesop 10%] axiom du_zar_lc {X Y : Scheme} {P : Scheme → Prop} (h₁ : P X) (h₂ : P Y) (h₃ : Scheme.zariski_local P) : P (disjoint_union X Y)
-- Whenever $X$ is non-empty, the disjoint union $X \sqcup Y$ is also non-empty
@[aesop 99%] axiom du_empty_X {X : Scheme} (Y : Scheme) (h : ¬X.empty) : ¬((disjoint_union X Y).empty)
-- Whenever $Y$ is non-empty, the disjoint union $X \sqcup Y$ is also non-empty
@[aesop 99%] axiom du_empty_Y (X : Scheme) {Y : Scheme} (h : ¬Y.empty) : ¬((disjoint_union X Y).empty)

-- The line with double origin over a field $k$.
@[aesop 99%] axiom line_double_origin {k : Ring} (h : k.field) : Scheme
-- The line with double origin is ¬separated.
@[aesop 99%] axiom line_double_origin_not_separated {k : Ring} (h : k.field) : ¬(line_double_origin h).separated

end Math.AlgebraicGeometry
