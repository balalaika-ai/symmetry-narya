export "508-stabilizer-subgroups"
export "1000-prime-numbers"

{` Chapter 10 (fingp.tex), sec:Lagrangecounting: finite groups
   (def:finitegrd), the set of symmetries fixing a point and the sets of
   symmetries moving one point to another, and the counting identity behind
   Lagrange's theorem: for a finite group G and a finite G-set X in which
   every point is reachable from x, |G| = |X(sh_G)| · |{g | g · x = x}|.
   Finiteness of the subgroups of a finite group: for a subgroup (X, pt)
   the conditions "H finite", "X(sh_G) finite" and "X decidable"
   (def:decidable-subgroup) are equivalent. `}

{` def:finitegrd. Finite groups and their cardinality |G| are IsFiniteGroup
   and group_card of the chapter-4 core; this is the parenthetical
   "USym G : FinSet_{|G|}". `}
def finite_group_usym_component (G : Group) (hG : IsFiniteGroup G) : BookFiniteSetsAt (group_card G hG)
  ≔ let n ≔ group_card G hG in
    let F : SetTypes ≔ (Fin n, fin_set n) in
    let U : SetTypes ≔ (USym G, usym_set G) in
    (U, mere_rec (Id Type (USym G) (Fin n)) (Mere (Id SetTypes F U)) (mere_isprop (Id SetTypes F U))
          (p ↦ mere (Id SetTypes F U)
            (set_types_path F U (id_to_equiv (Fin n) (USym G) (inverse Type (USym G) (Fin n) p))))
          (cardinality_spec (USym G) hG))

def finite_group_decidable_equality (G : Group) (hG : IsFiniteGroup G) : DecidableEquality (USym G)
  ≔ finite_decidable_equality (USym G) hG

{` A decidable family of propositions on a type with decidable equality
   whose total type is finite is decidable pointwise ("membership in a
   finite subset is decidable"). `}
def finite_subset_decidable (A : Type) (dA : DecidableEquality A) (P : A → Type)
  (hP : (a : A) → isProp (P a)) (hS : IsFinite (Σ A P)) (a : A) : Decidable (P a)
  ≔ let Q : Σ A P → Type ≔ s ↦ Id A (s .fst) a in
    match finite_quantifiers (Σ A P) hS Q (s ↦ hedberg A dA (s .fst) a .fst) (s ↦ dA (s .fst) a) .snd [
    | inl. t ↦ inl. (mere_rec (Σ (Σ A P) Q) (P a) (hP a)
        (u ↦ transport A P (u .fst .fst) a (u .snd) (u .fst .snd)) t)
    | inr. no ↦ inr. (p ↦ no (mere (Σ (Σ A P) Q) ((a, p), refl a))) ]

{` The symmetries fixing x, {g : USym G | g · x = x}; for x = pt of a
   subgroup this is the underlying set of the subgroup (see
   subgroup_usym_stabilizer_equiv). Definitionally ActionTypePath at (sh_G, x). `}
def GSetStabilizer (G : Group) (X : GSet G) (x : gset_underlying G X) : Type
  ≔ Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)

def gset_orbit_map (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G) : gset_underlying G X
  ≔ gset_usym_act G X g x

{` The symmetries moving x to y: the fiber Σ_g (y = g · x) of g ↦ g · x. `}
def GSetTransporter (G : Group) (X : GSet G) (x y : gset_underlying G X) : Type
  ≔ BookFiber (USym G) (gset_underlying G X) (gset_orbit_map G X x) y

def gset_stabilizer_shift_to (G : Group) (X : GSet G) (x y : gset_underlying G X) (g0 : USym G)
  (e0 : Id (gset_underlying G X) y (gset_usym_act G X g0 x)) (h : USym G)
  (r : Id (gset_underlying G X) (gset_usym_act G X h x) x)
  : Id (gset_underlying G X) y (gset_usym_act G X (usym_mul G g0 h) x)
  ≔ let Y ≔ gset_underlying G X in
    calc
      y
      = gset_usym_act G X g0 x by e0
      = gset_usym_act G X g0 (gset_usym_act G X h x)
        by refl (gset_usym_act G X g0) (inverse Y (gset_usym_act G X h x) x r)
      = gset_usym_act G X (usym_mul G g0 h) x
        by inverse Y (gset_usym_act G X (usym_mul G g0 h) x) (gset_usym_act G X g0 (gset_usym_act G X h x))
          (gset_act_mul G X g0 h x) ∎

def gset_stabilizer_shift_from (G : Group) (X : GSet G) (x y : gset_underlying G X) (g0 : USym G)
  (e0 : Id (gset_underlying G X) y (gset_usym_act G X g0 x)) (h : USym G)
  (q : Id (gset_underlying G X) y (gset_usym_act G X (usym_mul G g0 h) x))
  : Id (gset_underlying G X) (gset_usym_act G X h x) x
  ≔ let Y ≔ gset_underlying G X in
    let back : Y → Y ≔ gset_usym_act G X (usym_inv G g0) in
    calc
      gset_usym_act G X h x
      = back (gset_usym_act G X g0 (gset_usym_act G X h x))
        by inverse Y (back (gset_usym_act G X g0 (gset_usym_act G X h x))) (gset_usym_act G X h x)
          (gset_act_inv_left G X g0 (gset_usym_act G X h x))
      = back (gset_usym_act G X (usym_mul G g0 h) x)
        by refl back (inverse Y (gset_usym_act G X (usym_mul G g0 h) x) (gset_usym_act G X g0 (gset_usym_act G X h x))
          (gset_act_mul G X g0 h x))
      = back y by refl back (inverse Y y (gset_usym_act G X (usym_mul G g0 h) x) q)
      = back (gset_usym_act G X g0 x) by refl back e0
      = x by gset_act_inv_left G X g0 x ∎

{` Given g0 with y = g0 · x, left multiplication by g0 identifies the
   stabilizer of x with the transporter from x to y. `}
def gset_stabilizer_transporter_equiv (G : Group) (X : GSet G) (x y : gset_underlying G X) (g0 : USym G)
  (e0 : Id (gset_underlying G X) y (gset_usym_act G X g0 x))
  : Equiv (GSetStabilizer G X x) (GSetTransporter G X x y)
  ≔ let Y ≔ gset_underlying G X in
    let P : USym G → Type ≔ g ↦ Id Y y (gset_usym_act G X g x) in
    let L : Equiv (USym G) (USym G) ≔ loop_concat_right_equiv (BG G .carrier) (shape G) (shape G) g0 in
    compose_equiv (GSetStabilizer G X x) (Σ (USym G) (h ↦ P (L .map h))) (GSetTransporter G X x y)
      (family_equiv (USym G) (h ↦ Id Y (gset_usym_act G X h x) x) (h ↦ P (L .map h))
        (h ↦ iff_equiv (Id Y (gset_usym_act G X h x) x) (P (L .map h))
          (gset_underlying_set G X (gset_usym_act G X h x) x)
          (gset_underlying_set G X y (gset_usym_act G X (L .map h) x))
          (gset_stabilizer_shift_to G X x y g0 e0 h) (gset_stabilizer_shift_from G X x y g0 e0 h)))
      (sigma_pullback_equiv (USym G) (USym G) L P)

def gset_stabilizer_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G)
  (dX : DecidableEquality (gset_underlying G X)) (x : gset_underlying G X)
  : IsFinite (GSetStabilizer G X x)
  ≔ finite_decidable_subset (USym G) hG (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)
      (g ↦ gset_underlying_set G X (gset_usym_act G X g x) x) (g ↦ dX (gset_usym_act G X g x) x)

{` The counting identity |G| = |X(sh_G)| · |G_x| when every point of the
   finite set X(sh_G) is reachable from x (the orbit–stabilizer count).
   The fibers of g ↦ g · x are merely equivalent to the stabilizer; finite
   choice over X(sh_G) turns this into a family of equivalences inside the
   proof of a proposition. `}
def gset_orbit_card_identity (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (x : gset_underlying G X) (reach : (y : gset_underlying G X) → Mere (GSetTransporter G X x y))
  : Id Nat (group_card G hG)
      (mul (gset_card G X hX) (cardinality (GSetStabilizer G X x)
        (gset_stabilizer_finite G hG X (finite_decidable_equality (gset_underlying G X) hX) x)))
  ≔ let Y ≔ gset_underlying G X in
    let S ≔ GSetStabilizer G X x in
    let hS ≔ gset_stabilizer_finite G hG X (finite_decidable_equality Y hX) x in
    let F : Y → Type ≔ y ↦ GSetTransporter G X x y in
    let E ≔ sum_of_fibers_equiv (USym G) Y (gset_orbit_map G X x) in
    let hT ≔ finite_of_equiv (Σ Y F) (USym G) E hG in
    mere_rec ((y : Y) → Equiv (F y) S)
      (Id Nat (group_card G hG) (mul (gset_card G X hX) (cardinality S hS)))
      (nat_set (group_card G hG) (mul (gset_card G X hX) (cardinality S hS)))
      (e ↦ concat Nat (group_card G hG) (cardinality (Σ Y F) hT) (mul (gset_card G X hX) (cardinality S hS))
        (cardinality_equiv (USym G) (Σ Y F) (canonical_inverse_equiv (Σ Y F) (USym G) E) hG hT)
        (cardinality_equinumerous_sum Y S F hX hS e hT))
      (finite_choice Y hX (y ↦ Equiv (F y) S)
        (y ↦ mere_rec (F y) (Mere (Equiv (F y) S)) (mere_isprop (Equiv (F y) S))
          (w ↦ mere (Equiv (F y) S)
            (canonical_inverse_equiv S (F y) (gset_stabilizer_transporter_equiv G X x y (w .fst) (w .snd))))
          (reach y)))

{` For a subgroup (X, pt), every point of X(sh_G) is merely g · pt
   (transitivity; the orbit map is surjective). `}
def subgroup_point_reach (G : Group) (S : Subgroups G) : Surjective (USym G) (gset_underlying G (S .gset))
  (gset_orbit_map G (S .gset) (S .point))
  ≔ y ↦
    let X ≔ S .gset in
    let T ≔ ActionType G X in
    mere_rec (Id T (shape G, S .point) (shape G, y)) (Mere (GSetTransporter G X (S .point) y))
      (mere_isprop (GSetTransporter G X (S .point) y))
      (r ↦ let a ≔ action_type_path_equiv G X (shape G, S .point) (shape G, y) .map r in
        mere (GSetTransporter G X (S .point) y)
          (a .fst, inverse (gset_underlying G X) (gset_usym_act G X (a .fst) (S .point)) y (a .snd)))
      (transitive_action_type_connected G X (S .transitive) .snd (shape G, S .point) (shape G, y))

{` USym of the underlying group of a subgroup is the stabilizer set of pt
   (rem:path-in-action-type at (sh_G, pt)). `}
def subgroup_usym_stabilizer_equiv (G : Group) (S : Subgroups G)
  : Equiv (USym (subgroup_group G S)) (GSetStabilizer G (S .gset) (S .point))
  ≔ action_type_path_equiv G (S .gset) (shape G, S .point) (shape G, S .point)

{` H finite ⇒ X(sh_G) finite. Each transporter set is merely equivalent to
   the finite stabilizer, so membership in it is decidable; hence X(sh_G)
   has decidable equality, and it is the image of the finite set USym G. `}
def subgroup_transporter_finite (G : Group) (S : Subgroups G) (hH : IsFiniteGroup (subgroup_group G S))
  (y : gset_underlying G (S .gset)) : IsFinite (GSetTransporter G (S .gset) (S .point) y)
  ≔ let X ≔ S .gset in
    let St ≔ GSetStabilizer G X (S .point) in
    let hSt ≔ finite_of_equiv St (USym (subgroup_group G S))
      (canonical_inverse_equiv (USym (subgroup_group G S)) St (subgroup_usym_stabilizer_equiv G S)) hH in
    mere_rec (GSetTransporter G X (S .point) y) (IsFinite (GSetTransporter G X (S .point) y))
      (isfinite_prop (GSetTransporter G X (S .point) y))
      (w ↦ finite_of_equiv (GSetTransporter G X (S .point) y) St
        (canonical_inverse_equiv St (GSetTransporter G X (S .point) y)
          (gset_stabilizer_transporter_equiv G X (S .point) y (w .fst) (w .snd))) hSt)
      (subgroup_point_reach G S y)

def subgroup_gset_decidable_equality (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hH : IsFiniteGroup (subgroup_group G S)) : DecidableEquality (gset_underlying G (S .gset))
  ≔ x y ↦
    let X ≔ S .gset in
    let Y ≔ gset_underlying G X in
    let pt ≔ S .point in
    let member : (g : USym G) → Decidable (Id Y y (gset_usym_act G X g pt))
      ≔ finite_subset_decidable (USym G) (finite_group_decidable_equality G hG)
          (g ↦ Id Y y (gset_usym_act G X g pt)) (g ↦ gset_underlying_set G X y (gset_usym_act G X g pt))
          (subgroup_transporter_finite G S hH y) in
    mere_rec (GSetTransporter G X pt x) (Decidable (Id Y x y))
      (decidability_prop (Id Y x y) (gset_underlying_set G X x y))
      (w ↦ match member (w .fst) [
        | inl. q ↦ inl. (concat Y x (gset_usym_act G X (w .fst) pt) y (w .snd)
            (inverse Y y (gset_usym_act G X (w .fst) pt) q))
        | inr. no ↦ inr. (r ↦ no (concat Y y x (gset_usym_act G X (w .fst) pt) (inverse Y x y r) (w .snd))) ])
      (subgroup_point_reach G S x)

def subgroup_gset_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hH : IsFiniteGroup (subgroup_group G S)) : IsFiniteGSet G (S .gset)
  ≔ finite_surjection_target (USym G) (gset_underlying G (S .gset)) hG
      (subgroup_gset_decidable_equality G hG S hH) (gset_orbit_map G (S .gset) (S .point))
      (subgroup_point_reach G S)

{` X(sh_G) finite (equivalently, by finite_decidable_equality, X a
   decidable subgroup) ⇒ H finite. `}
def subgroup_group_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (dX : IsDecidableSubgroup G S) : IsFiniteGroup (subgroup_group G S)
  ≔ finite_of_equiv (USym (subgroup_group G S)) (GSetStabilizer G (S .gset) (S .point))
      (subgroup_usym_stabilizer_equiv G S) (gset_stabilizer_finite G hG (S .gset) dX (S .point))

{` For a subgroup of a finite group the three finiteness conditions agree. `}
def subgroup_finiteness_conditions (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  : Product (Product (IsFiniteGroup (subgroup_group G S) → IsFiniteGSet G (S .gset))
                     (IsFiniteGSet G (S .gset) → IsDecidableSubgroup G S))
            (IsDecidableSubgroup G S → IsFiniteGroup (subgroup_group G S))
  ≔ ((subgroup_gset_finite G hG S, finite_decidable_equality (gset_underlying G (S .gset))),
     subgroup_group_finite G hG S)
