import Aesop
import Duck.Math.CommutativeAlgebra
import Duck.Math.CategoryTheory

open Math.CommutativeAlgebra
open Math.CategoryTheory

namespace Math.AlgebraicGeometry

-- The type of schemes.
axiom Scheme : Type
axiom SchemeHom (X Y : Scheme) : Type
axiom SchemeId (X : Scheme) : SchemeHom X X
axiom SchemeComp {X Y Z : Scheme} (f : SchemeHom Y Z) (g : SchemeHom X Y) : SchemeHom X Z
axiom SchemeAssoc {X Y Z W : Scheme} (f : SchemeHom Z W) (g : SchemeHom Y Z) (h : SchemeHom X Y) : SchemeComp (SchemeComp f g) h = SchemeComp f (SchemeComp g h)
axiom SchemeCompId {X Y : Scheme} (f : SchemeHom X Y) : SchemeComp f (SchemeId X) = f
axiom SchemeIdComp {X Y : Scheme} (f : SchemeHom X Y) : SchemeComp (SchemeId Y) f = f

-- Category structure
noncomputable instance : Category Scheme where
  Hom := SchemeHom
  id := SchemeId
  comp := SchemeComp
  comp_assoc := SchemeAssoc
  comp_id := SchemeCompId
  id_comp := SchemeIdComp

namespace Scheme

-- A scheme is empty if it does not have points.
axiom empty (X : Scheme) : Prop
-- A scheme is affine if it is isomorphic to $\Spec(R)$ for some ring $R$.
axiom affine (X : Scheme) : Prop
-- A scheme is quasi-compact if its underlying topological space is quasi-compact. That is, for every open cover $\{ U_i \}_{i \in I}$ of $X$, there exists a finite subcover.
axiom quasi_compact (X : Scheme) : Prop
-- A scheme is regular if it is locally noetherian and all of its stalks are regular local rings.
axiom regular (X : Scheme) : Prop
-- A scheme is locally noetherian if it can be covered by affine open subsets $\Spec A_i$, where each $A_i$ is a noetherian ring.
axiom locally_noetherian (X : Scheme) : Prop
-- A scheme is noetherian if it is locally noetherian and quasi-compact.
axiom noetherian (X : Scheme) : Prop
-- A scheme $X$ is reduced if $\mathcal{O}_X(U)$ is a reduced ring for all open $U \subset X$.
axiom reduced (X : Scheme) : Prop
-- A scheme $X$ is irreducible if its underlying topological space is irreducible. That is, if $X = Z_1 \sqcup Z_2$ for some closed subsets $Z_1, Z_2 \subset X$, then $Z_1 = X$ or $Z_2 = X$.
axiom irreducible (X : Scheme) : Prop
axiom cohen_macaulay (X : Scheme) : Prop
axiom excellent (X : Scheme) : Prop
-- A scheme is separated if the morphism $X \to \Spec \ZZ$ is separated.
axiom separated (X : Scheme) : Prop
-- A scheme is quasi-separated if the morphism $X \to \Spec \ZZ$ is quasi-separated.
axiom quasi_separated (X : Scheme) : Prop
axiom jacobson (X : Scheme) : Prop
axiom normal (X : Scheme) : Prop
-- A scheme $X$ is integral if it is non-empty and for every non-empty open subset $U \subset X$, the ring $\mathcal{O}_X(U)$ is a domain.
def integral (X : Scheme) := reduced X ∧ irreducible X
axiom finite_dimensional (X : Scheme) : Prop
-- A scheme is connected if its underlying topological space is connected.
axiom connected (X : Scheme) : Prop -- := topology.connected (top_of_scheme X)

-- A property $P$ is Zariski-local if for every scheme $X$ and open cover $X = \bigcup_{i \in I} U_i$, we have that $P$ holds for $X$ if and only if $P$ holds for all $U_i$.
axiom zariski_local (P : Scheme → Prop) : Prop
-- Being reduced is a Zariski-local property.
@[aesop 99%] axiom zariski_local_rd : zariski_local reduced
-- Being separated is a Zariski-local property.
@[aesop 99%] axiom zariski_local_sp : zariski_local separated
-- Being quasi-separated is a Zariski-local property.
@[aesop 99%] axiom zariski_local_qsp : zariski_local quasi_separated
-- Being noetherian is a Zariski-local property.
@[aesop 99%] axiom zariski_local_nt : zariski_local noetherian
-- Being regular is a Zariski-local property.
@[aesop 99%] axiom zariski_local_rg : zariski_local regular

end Scheme
open Scheme

namespace SchemeHom

variable {X Y : Scheme}

-- A morphism $f : X \to Y$ is affine if for every affine open $V \subset Y$, the inverse image $f^{-1}(V)$ is an affine open of $X$.
axiom affine (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is flat if for every $x \in X$, the local ring $\mathcal{O}_{X, x}$ is flat as an $\mathcal{O}_{Y, f(x)}$-module.
axiom flat (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is separated if the diagonal map $\Delta_X : X \to X \times X$ is a closed immersion.
axiom separated (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is quasi-separated if the diagonal map $\Delta_X : X \to X \times X$ is quasi-compact.
axiom quasi_separated (f : X ⟶ Y) : Prop
/- A morphism $f : X \to Y$ is of finite presentation at $x \in X$ if there exists affine opens $U = \Spec S \subset X$ containing $x$ and $V = \Spec R \subset Y$ with $f(U) \subset V$ such that $S$ is a finitely presented $R$-algebra (via the induced map $R \to S$). That is, $S \simeq R[x_1, \ldots, x_n] / (f_1, \ldots, f_m)$ for some integer $n$ and some $f_i \in R[x_1, \ldots, x_n]$.
The morphism $f$ is locally of finite presentation if it is of finite presentation at all $x \in X$. -/
axiom locally_finitely_presented (f : X ⟶ Y) : Prop
/- A morphism $f : X \to Y$ is of finite type at $x \in X$ if there exists affine opens $U = \Spec S \subset X$ containing $x$ and $V = \Spec R \subset Y$ with $f(U) \subset V$ such that $S$ is a finitely generated $R$-algebra (via the induced map $R \to S$). That is, $S \simeq R[x_1, \ldots, x_n] / I$ for some integer $n$ and some ideal $I \subset R[x_1, \ldots, x_n]$.
The morphism $f$ is locally of finite type if it is of finite type at all $x \in X$. -/
axiom locally_finite_type (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is of finite presentation if it is locally of finite presentation, quasi-compact and quasi-separated.
axiom finitely_presented (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is regular if [...].
axiom regular (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is quasi-compact if the pre-image $f^{-1}(K)$ of every quasi-compact subset $K \subset Y$ is quasi-compact.
axiom quasi_compact (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is quasi-finite if it is of finite type and every point $x \in X$ is isolated in its fiber $f^{-1}(f(x))$, i.e. every fiber is a discrete finite set.
axiom quasi_finite (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is finite if there exists a covering of $Y$ by open affine subsets $V_i = \Spec B_i$, such that for each $i$, $f^{-1}(V_i)$ is affine, equal to $\Spec A_i$, where $A_i$ is a $B_i$-algebra which is a finitely generated $B_i$-module.
axiom finite (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is of finite type if it is locally of finite type and quasi-compact.
axiom finite_type (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is universally closed if for every $g : Z \to Y$, the pullback $X \times_Y Z \to Z$ is closed.
axiom universally_closed (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is proper if it is separated, of finite type and universally closed.
def proper (f : X ⟶ Y) := separated f ∧ finite_type f ∧ universally_closed f
-- A morphism $f : X \to Y$ is projective if it factors as $X \xrightarrow{i} \PP_Y^n \xrightarrow{p} Y$, with $i$ a closed immersion and $p$ the natural projection.
axiom projective (f : X ⟶ Y) : Prop

axiom formally_smooth (f : X ⟶ Y) : Prop
axiom formally_unramified (f : X ⟶ Y) : Prop
axiom formally_etale (f : X ⟶ Y) : Prop

axiom unramified (f : X ⟶ Y) : Prop
axiom smooth (f : X ⟶ Y) : Prop
axiom etale (f : X ⟶ Y) : Prop

-- A morphism $f : X \to Y$ is open if for every open $U \subset X$, the image $f(U) \subset Y$ is open.
axiom open_morphism (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is an immersion if it factors as $j \circ i$, where $i : X \to U$ is a closed immersion and $j : U \to Y$ is an open immersion.
axiom immersion (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is an open immersion if it induces an isomorphism between $X$ and an open subscheme of $Y$.
axiom open_immersion (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is a closed immersion if it induces a homeomorphism between the underlying space of $X$ and a closed subset of that of $Y$, and furthermore the induced map $i^\# : \mathcal{O}_Y \to i_*\mathcal{O}_X$ of sheaves on $Y$ is surjective.
axiom closed_immersion (f : X ⟶ Y) : Prop
axiom finite_fibers (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is surjective if the underlying map of topological spaces is surjective.
axiom surjective (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is faithfully flat if it is flat and surjective.
axiom faithfully_flat (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is a locally complete intersection if [...].
axiom lci (f : X ⟶ Y) : Prop
-- A morphism $f : X \to Y$ is syntomic if [...].
axiom syntomic (f : X ⟶ Y) : Prop

axiom zariski_cover (f : X ⟶ Y) : Prop
axiom etale_cover (f : X ⟶ Y) : Prop
axiom smooth_cover (f : X ⟶ Y) : Prop
axiom syntomic_cover (f : X ⟶ Y) : Prop
axiom fppf_cover (f : X ⟶ Y) : Prop
axiom fpqc_cover (f : X ⟶ Y) : Prop

axiom stable_composition (h : {X Y : Scheme} → (f : X ⟶ Y) → Prop) : Prop
axiom stable_left (h : {X Y : Scheme} → (f : X ⟶ Y) → Prop) : Prop
axiom stable_base_change (h : {X Y : Scheme} → (f : X ⟶ Y) → Prop) : Prop

end SchemeHom
open SchemeHom

end Math.AlgebraicGeometry
