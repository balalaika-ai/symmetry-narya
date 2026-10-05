export "1023-p-group-fixed-points"

{` Chapter 10, supporting material for the Sylow theorems (fingp.tex
   227-307): containment of subgroups. For subgroups S = (X, x) and
   T = (Y, y) of G, "S is contained in T" (S ⊆ T) is the proposition that
   every symmetry fixing x fixes y, i.e. the symmetries of S (the
   stabilizer of x) are symmetries of T. It holds exactly when there is a
   map of G-sets X → Y sending x to y (subgroup_fixed_gset_hom), and
   containment both ways identifies the subgroups (subgroup_le_antisym).
   For a finite group, a containment between finite subgroups with the
   same number of symmetries is an identification (subgroup_le_card_eq).
   The same subgroup G-set with another point y gives the subgroup
   (X, y) (subgroup_at); in a finite group all of these have the same
   cardinality. `}

{` S fixes y ∈ Y(sh_G): every symmetry fixing the point of S fixes y. `}
def SubgroupFixes (G : Group) (S : Subgroups G) (Y : GSet G) (y : gset_underlying G Y) : Type
  ≔ (g : USym G) → Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point)
      → Id (gset_underlying G Y) (gset_usym_act G Y g y) y

def subgroup_fixes_prop (G : Group) (S : Subgroups G) (Y : GSet G) (y : gset_underlying G Y)
  : isProp (SubgroupFixes G S Y y)
  ≔ pi_prop (USym G)
      (g ↦ Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point)
        → Id (gset_underlying G Y) (gset_usym_act G Y g y) y)
      (g ↦ pi_prop (Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point))
        (_ ↦ Id (gset_underlying G Y) (gset_usym_act G Y g y) y)
        (_ ↦ gset_underlying_set G Y (gset_usym_act G Y g y) y))

{` Containment S ⊆ T of subgroups: the stabilizer of the point of S is
   contained in the stabilizer of the point of T. `}
def SubgroupLe (G : Group) (S T : Subgroups G) : Type ≔ SubgroupFixes G S (T .gset) (T .point)

def subgroup_le_prop (G : Group) (S T : Subgroups G) : isProp (SubgroupLe G S T)
  ≔ subgroup_fixes_prop G S (T .gset) (T .point)

def subgroup_le_refl (G : Group) (S : Subgroups G) : SubgroupLe G S S ≔ g r ↦ r

def subgroup_le_trans (G : Group) (S T U : Subgroups G) (c : SubgroupLe G S T) (d : SubgroupLe G T U)
  : SubgroupLe G S U
  ≔ g r ↦ d g (c g r)

{` Restriction of a G-set Y to the underlying group of S: u ↦ Y(u.1),
   which is gset_restrict along subgroup_inclusion (the book's i^*Y). `}
def subgroup_restricted_gset (G : Group) (S : Subgroups G) (Y : GSet G) : GSet (subgroup_group G S)
  ≔ u ↦ Y (u .fst)

def subgroup_restricted_gset_path (G : Group) (S : Subgroups G) (Y : GSet G)
  : Id (GSet (subgroup_group G S)) (subgroup_restricted_gset G S Y)
      (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) Y)
  ≔ refl (subgroup_restricted_gset G S Y)

{` A symmetry h of S acts on Y(sh_G) through its image in USym G. `}
def subgroup_restricted_act (G : Group) (S : Subgroups G) (Y : GSet G) (h : USym (subgroup_group G S))
  (y : gset_underlying G Y)
  : Id (gset_underlying G Y) (gset_usym_act (subgroup_group G S) (subgroup_restricted_gset G S Y) h y)
      (gset_usym_act G Y (subgroup_usym_stabilizer_equiv G S .map h .fst) y)
  ≔ refl (gset_usym_act G Y (subgroup_usym_stabilizer_equiv G S .map h .fst) y)

{` The fixed points of the restricted action are the points fixed by S. `}
def subgroup_fixes_restricted (G : Group) (S : Subgroups G) (Y : GSet G) (y : gset_underlying G Y)
  (f : SubgroupFixes G S Y y) (h : USym (subgroup_group G S))
  : Id (gset_underlying G Y) (gset_usym_act (subgroup_group G S) (subgroup_restricted_gset G S Y) h y) y
  ≔ let a ≔ subgroup_usym_stabilizer_equiv G S .map h in
    concat (gset_underlying G Y) (gset_usym_act (subgroup_group G S) (subgroup_restricted_gset G S Y) h y)
      (gset_usym_act G Y (a .fst) y) y (subgroup_restricted_act G S Y h y) (f (a .fst) (a .snd))

def subgroup_stabilizer_act_at (G : Group) (X : GSet G) (x : gset_underlying G X) (Y : GSet G)
  (y : gset_underlying G Y) (a : GSetStabilizer G X x) : gset_underlying G Y
  ≔ gset_usym_act G Y (a .fst) y

def subgroup_restricted_fixes (G : Group) (S : Subgroups G) (Y : GSet G) (y : gset_underlying G Y)
  (f : (h : USym (subgroup_group G S))
     → Id (gset_underlying G Y) (gset_usym_act (subgroup_group G S) (subgroup_restricted_gset G S Y) h y) y)
  : SubgroupFixes G S Y y
  ≔ g r ↦
    let St ≔ GSetStabilizer G (S .gset) (S .point) in
    let E ≔ subgroup_usym_stabilizer_equiv G S in
    let h ≔ equiv_inverse_map (USym (subgroup_group G S)) St E (g, r) in
    let Yu ≔ gset_underlying G Y in
    let k ≔ subgroup_stabilizer_act_at G (S .gset) (S .point) Y y in
    concat Yu (k (g, r)) (k (E .map h)) y
      (map_path St Yu k (g, r) (E .map h)
        (inverse St (E .map h) (g, r) (equiv_counit (USym (subgroup_group G S)) St E (g, r))))
      (concat Yu (k (E .map h)) (gset_usym_act (subgroup_group G S) (subgroup_restricted_gset G S Y) h y) y
        (inverse Yu (gset_usym_act (subgroup_group G S) (subgroup_restricted_gset G S Y) h y) (k (E .map h))
          (subgroup_restricted_act G S Y h y))
        (f h))

{` A point y fixed by S determines a map of G-sets X → Y with x ↦ y
   (extension of the invariant point of the restricted action). `}
def subgroup_fixed_gset_hom (G : Group) (S : Subgroups G) (Y : GSet G) (y : gset_underlying G Y)
  (f : SubgroupFixes G S Y y) : GSetHom G (S .gset) Y
  ≔ let s : InvariantMaps (subgroup_group G S) (subgroup_restricted_gset G S Y)
      ≔ gset_fixed_point_extension (subgroup_group G S) (subgroup_restricted_gset G S Y) y
          (subgroup_fixes_restricted G S Y y f) in
    z x ↦ s (z, x)

def subgroup_fixed_gset_hom_point (G : Group) (S : Subgroups G) (Y : GSet G) (y : gset_underlying G Y)
  (f : SubgroupFixes G S Y y)
  : Id (gset_underlying G Y) (subgroup_fixed_gset_hom G S Y y f (shape G) (S .point)) y
  ≔ gset_fixed_point_extension_beta (subgroup_group G S) (subgroup_restricted_gset G S Y) y
      (subgroup_fixes_restricted G S Y y f)

{` Conversely a map of G-sets sending the point of S to y shows that S fixes y. `}
def gset_hom_subgroup_fixes (G : Group) (S : Subgroups G) (Y : GSet G) (y : gset_underlying G Y)
  (f : GSetHom G (S .gset) Y) (e : Id (gset_underlying G Y) (f (shape G) (S .point)) y)
  : SubgroupFixes G S Y y
  ≔ g r ↦
    let Yu ≔ gset_underlying G Y in
    let x ≔ S .point in
    calc
      gset_usym_act G Y g y
      = gset_usym_act G Y g (f (shape G) x)
        by map_path Yu Yu (gset_usym_act G Y g) y (f (shape G) x) (inverse Yu (f (shape G) x) y e)
      = f (shape G) (gset_usym_act G (S .gset) g x)
        by inverse Yu (f (shape G) (gset_usym_act G (S .gset) g x)) (gset_usym_act G Y g (f (shape G) x))
          (gset_hom_equivariant G (S .gset) Y f g x)
      = f (shape G) x by map_path (gset_underlying G (S .gset)) Yu (f (shape G)) (gset_usym_act G (S .gset) g x) x r
      = y by e ∎

{` Containment both ways identifies the subgroups: the two maps of G-sets
   are inverse to each other because maps out of a transitive G-set are
   determined by their value at one point. `}
def subgroup_le_antisym (G : Group) (S T : Subgroups G) (c : SubgroupLe G S T) (d : SubgroupLe G T S)
  : Id (Subgroups G) S T
  ≔ let B ≔ BG G .carrier in
    let X ≔ S .gset in
    let Y ≔ T .gset in
    let f ≔ subgroup_fixed_gset_hom G S Y (T .point) c in
    let f' ≔ subgroup_fixed_gset_hom G T X (S .point) d in
    let fp ≔ subgroup_fixed_gset_hom_point G S Y (T .point) c in
    let fp' ≔ subgroup_fixed_gset_hom_point G T X (S .point) d in
    let ff : Id (GSetHom G X X) (gset_hom_compose G X Y X f f') (gset_hom_id G X)
      ≔ gset_hom_eval_reflects G X X (shape G) (S .point) (S .transitive) (gset_hom_compose G X Y X f f')
          (gset_hom_id G X)
          (concat (gset_underlying G X) (f' (shape G) (f (shape G) (S .point))) (f' (shape G) (T .point)) (S .point)
            (map_path (gset_underlying G Y) (gset_underlying G X) (f' (shape G)) (f (shape G) (S .point)) (T .point) fp)
            fp') in
    let gg : Id (GSetHom G Y Y) (gset_hom_compose G Y X Y f' f) (gset_hom_id G Y)
      ≔ gset_hom_eval_reflects G Y Y (shape G) (T .point) (T .transitive) (gset_hom_compose G Y X Y f' f)
          (gset_hom_id G Y)
          (concat (gset_underlying G Y) (f (shape G) (f' (shape G) (T .point))) (f (shape G) (S .point)) (T .point)
            (map_path (gset_underlying G X) (gset_underlying G Y) (f (shape G)) (f' (shape G) (T .point)) (S .point) fp')
            fp) in
    let e : (z : B) → Equiv (X z .fst) (Y z .fst)
      ≔ z ↦ quasi_inverse_equiv (X z .fst) (Y z .fst) (f z) (f' z)
          (happly (X z .fst) (_ ↦ X z .fst) (gset_hom_compose G X Y X f f' z) (gset_hom_id G X z)
            (happly B (w ↦ X w .fst → X w .fst) (gset_hom_compose G X Y X f f') (gset_hom_id G X) ff z))
          (happly (Y z .fst) (_ ↦ Y z .fst) (gset_hom_compose G Y X Y f' f z) (gset_hom_id G Y z)
            (happly B (w ↦ Y w .fst → Y w .fst) (gset_hom_compose G Y X Y f' f) (gset_hom_id G Y) gg z)) in
    subgroup_path G S T (pointed_gset_path G X Y (S .point) (T .point) e fp)

{` A decidable subset P of a finite subset Q (P ⊆ Q) with as many
   elements as Q is all of Q. `}
def finite_subset_card_eq_contra (U : Type) (P Q : U → Type) (hP : (u : U) → isProp (P u))
  (hQ : (u : U) → isProp (Q u)) (dP : (u : U) → Decidable (P u)) (inc : (u : U) → P u → Q u)
  (fP : IsFinite (Σ U P)) (fQ : IsFinite (Σ U Q))
  (e : Id Nat (cardinality (Σ U P) fP) (cardinality (Σ U Q) fQ)) (u : U) (q : Q u) (np : Not (P u)) : Empty
  ≔ let A ≔ Σ U Q in
    let P' : A → Type ≔ w ↦ P (w .fst) in
    let N' : A → Type ≔ w ↦ Not (P (w .fst)) in
    let dN : (w : A) → Decidable (N' w)
      ≔ w ↦ match dP (w .fst) [ inl. p ↦ inr. (n ↦ n p) | inr. n ↦ inl. n ] in
    let fP' : IsFinite (Σ A P') ≔ finite_decidable_subset A fQ P' (w ↦ hP (w .fst)) (w ↦ dP (w .fst)) in
    let fN' : IsFinite (Σ A N') ≔ finite_decidable_subset A fQ N' (w ↦ negation_prop (P (w .fst))) dN in
    let sp ≔ fingp_decidable_split_equiv A P' (w ↦ hP (w .fst)) (w ↦ dP (w .fst)) in
    let fS : IsFinite (Sum (Σ A P') (Σ A N')) ≔ finite_sum (Σ A P') (Σ A N') fP' fN' in
    let toP : Σ A P' → Σ U P ≔ w ↦ (w .fst .fst, w .snd) in
    let fromP : Σ U P → Σ A P' ≔ v ↦ ((v .fst, inc (v .fst) (v .snd)), v .snd) in
    let eqP : Equiv (Σ A P') (Σ U P)
      ≔ quasi_inverse_equiv (Σ A P') (Σ U P) toP fromP
          (w ↦ subtype_equal A P' (w' ↦ hP (w' .fst)) (fromP (toP w)) w
            (subtype_equal U Q hQ (fromP (toP w) .fst) (w .fst) (refl (w .fst .fst))))
          (v ↦ refl v) in
    let a ≔ cardinality (Σ A P') fP' in
    let b ≔ cardinality (Σ A N') fN' in
    let sumeq : Id Nat (add a b) (add a zero.)
      ≔ calc
          add a b
          = cardinality (Sum (Σ A P') (Σ A N')) fS
            by inverse Nat (cardinality (Sum (Σ A P') (Σ A N')) fS) (add a b)
              (cardinality_sum (Σ A P') (Σ A N') fP' fN' fS)
          = cardinality A fQ
            by inverse Nat (cardinality A fQ) (cardinality (Sum (Σ A P') (Σ A N')) fS)
              (cardinality_equiv A (Sum (Σ A P') (Σ A N')) sp fQ fS)
          = cardinality (Σ U P) fP by inverse Nat (cardinality (Σ U P) fP) (cardinality A fQ) e
          = a by inverse Nat a (cardinality (Σ U P) fP) (cardinality_equiv (Σ A P') (Σ U P) eqP fP' fP) ∎ in
    let bz : Id Nat b zero. ≔ add_cancel_left a b zero. sumeq in
    lt_irrefl zero.
      (transport Nat (k ↦ Lt zero. k) b zero. bz (finite_inhabited_card_positive (Σ A N') fN' ((u, q), np)))

def finite_subset_card_eq_full (U : Type) (P Q : U → Type) (hP : (u : U) → isProp (P u))
  (hQ : (u : U) → isProp (Q u)) (dP : (u : U) → Decidable (P u)) (inc : (u : U) → P u → Q u)
  (fP : IsFinite (Σ U P)) (fQ : IsFinite (Σ U Q))
  (e : Id Nat (cardinality (Σ U P) fP) (cardinality (Σ U Q) fQ)) (u : U) (q : Q u) : P u
  ≔ match dP u [
    | inl. p ↦ p
    | inr. np ↦ absurd (P u) (finite_subset_card_eq_contra U P Q hP hQ dP inc fP fQ e u q np) ]

{` The stabilizer of the point of a finite subgroup, with its cardinality. `}
def subgroup_stabilizer_finite (G : Group) (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  : IsFinite (GSetStabilizer G (S .gset) (S .point))
  ≔ finite_of_equiv (GSetStabilizer G (S .gset) (S .point)) (USym (subgroup_group G S))
      (canonical_inverse_equiv (USym (subgroup_group G S)) (GSetStabilizer G (S .gset) (S .point))
        (subgroup_usym_stabilizer_equiv G S)) hS

def subgroup_stabilizer_card (G : Group) (S : Subgroups G) (hS : IsFiniteGroup (subgroup_group G S))
  : Id Nat (cardinality (GSetStabilizer G (S .gset) (S .point)) (subgroup_stabilizer_finite G S hS))
      (group_card (subgroup_group G S) hS)
  ≔ cardinality_equiv (GSetStabilizer G (S .gset) (S .point)) (USym (subgroup_group G S))
      (canonical_inverse_equiv (USym (subgroup_group G S)) (GSetStabilizer G (S .gset) (S .point))
        (subgroup_usym_stabilizer_equiv G S))
      (subgroup_stabilizer_finite G S hS) hS

{` In a finite group, S ⊆ T with |S| = |T| (both finite) gives S = T. `}
def subgroup_le_card_eq (G : Group) (hG : IsFiniteGroup G) (S T : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (hT : IsFiniteGroup (subgroup_group G T))
  (c : SubgroupLe G S T)
  (e : Id Nat (group_card (subgroup_group G S) hS) (group_card (subgroup_group G T) hT))
  : Id (Subgroups G) S T
  ≔ let U ≔ USym G in
    let XS ≔ gset_underlying G (S .gset) in
    let XT ≔ gset_underlying G (T .gset) in
    let P : U → Type ≔ g ↦ Id XS (gset_usym_act G (S .gset) g (S .point)) (S .point) in
    let Q : U → Type ≔ g ↦ Id XT (gset_usym_act G (T .gset) g (T .point)) (T .point) in
    let dS ≔ subgroup_gset_decidable_equality G hG S hS in
    let fP ≔ subgroup_stabilizer_finite G S hS in
    let fQ ≔ subgroup_stabilizer_finite G T hT in
    let ce : Id Nat (cardinality (Σ U P) fP) (cardinality (Σ U Q) fQ)
      ≔ calc
          cardinality (Σ U P) fP
          = group_card (subgroup_group G S) hS by subgroup_stabilizer_card G S hS
          = group_card (subgroup_group G T) hT by e
          = cardinality (Σ U Q) fQ
            by inverse Nat (cardinality (Σ U Q) fQ) (group_card (subgroup_group G T) hT)
              (subgroup_stabilizer_card G T hT) ∎ in
    subgroup_le_antisym G S T c
      (g q ↦ finite_subset_card_eq_full U P Q
        (g' ↦ gset_underlying_set G (S .gset) (gset_usym_act G (S .gset) g' (S .point)) (S .point))
        (g' ↦ gset_underlying_set G (T .gset) (gset_usym_act G (T .gset) g' (T .point)) (T .point))
        (g' ↦ dS (gset_usym_act G (S .gset) g' (S .point)) (S .point)) c fP fQ ce g q)

{` Containment between finite subgroups of a finite group is decidable. `}
def subgroup_fixes_decidable (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (dX : DecidableEquality (gset_underlying G (S .gset))) (Y : GSet G) (dY : DecidableEquality (gset_underlying G Y))
  (y : gset_underlying G Y) : Decidable (SubgroupFixes G S Y y)
  ≔ let XS ≔ gset_underlying G (S .gset) in
    let Yu ≔ gset_underlying G Y in
    let R : USym G → Type
      ≔ g ↦ Id XS (gset_usym_act G (S .gset) g (S .point)) (S .point) → Id Yu (gset_usym_act G Y g y) y in
    finite_quantifiers (USym G) hG R
      (g ↦ pi_prop (Id XS (gset_usym_act G (S .gset) g (S .point)) (S .point))
        (_ ↦ Id Yu (gset_usym_act G Y g y) y) (_ ↦ gset_underlying_set G Y (gset_usym_act G Y g y) y))
      (g ↦ match dX (gset_usym_act G (S .gset) g (S .point)) (S .point) [
        | inl. r ↦ match dY (gset_usym_act G Y g y) y [
          | inl. q ↦ inl. (_ ↦ q)
          | inr. nq ↦ inr. (k ↦ nq (k r)) ]
        | inr. nr ↦ inl. (r ↦ absurd (Id Yu (gset_usym_act G Y g y) y) (nr r)) ])
      .fst

{` The subgroup (X, y): the same subgroup G-set with another point. For
   y = g · x this is the conjugate g · S (subgroups_move of module 902). `}
def subgroup_at (G : Group) (S : Subgroups G) (y : gset_underlying G (S .gset)) : Subgroups G
  ≔ (S .gset, y, S .transitive)

def subgroup_at_point (G : Group) (S : Subgroups G)
  : Id (Subgroups G) (subgroup_at G S (S .point)) S
  ≔ refl S

{` In a finite group, the stabilizers of all points of a finite transitive
   G-set have the same cardinality |G| / |X|. `}
def fingp_mul_cancel_left (c x y : Nat) (hc : Lt zero. c) (e : Id Nat (mul c x) (mul c y)) : Id Nat x y
  ≔ nat_mul_cancel_positive c x y hc
      (concat Nat (mul x c) (mul c x) (mul y c) (mul_comm x c)
        (concat Nat (mul c x) (mul c y) (mul y c) e (mul_comm c y)))

{` The cardinality does not depend on the proof of finiteness. `}
def fingp_card_irrel (A : Type) (h h' : IsFinite A) : Id Nat (cardinality A h) (cardinality A h')
  ≔ map_path (IsFinite A) Nat (cardinality A) h h' (isfinite_prop A h h')

def subgroup_at_stabilizer_card (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (y : gset_underlying G (S .gset))
  : Id Nat (cardinality (GSetStabilizer G (S .gset) y) (subgroup_stabilizer_finite G (subgroup_at G S y)
        (subgroup_group_finite G hG (subgroup_at G S y) (subgroup_gset_decidable_equality G hG S hS))))
      (cardinality (GSetStabilizer G (S .gset) (S .point)) (subgroup_stabilizer_finite G S hS))
  ≔ let X ≔ S .gset in
    let hX ≔ subgroup_gset_finite G hG S hS in
    let dX ≔ finite_decidable_equality (gset_underlying G X) hX in
    let n ≔ gset_card G X hX in
    let a ≔ cardinality (GSetStabilizer G X y) (gset_stabilizer_finite G hG X dX y) in
    let b ≔ cardinality (GSetStabilizer G X (S .point)) (gset_stabilizer_finite G hG X dX (S .point)) in
    let ab : Id Nat a b
      ≔ fingp_mul_cancel_left n a b (finite_inhabited_card_positive (gset_underlying G X) hX y)
          (concat Nat (mul n a) (group_card G hG) (mul n b)
            (inverse Nat (group_card G hG) (mul n a)
              (gset_orbit_card_identity G hG X hX y (subgroup_point_reach G (subgroup_at G S y))))
            (gset_orbit_card_identity G hG X hX (S .point) (subgroup_point_reach G S))) in
    concat Nat (cardinality (GSetStabilizer G X y) (subgroup_stabilizer_finite G (subgroup_at G S y)
        (subgroup_group_finite G hG (subgroup_at G S y) (subgroup_gset_decidable_equality G hG S hS)))) a
      (cardinality (GSetStabilizer G X (S .point)) (subgroup_stabilizer_finite G S hS))
      (fingp_card_irrel (GSetStabilizer G X y) (subgroup_stabilizer_finite G (subgroup_at G S y)
        (subgroup_group_finite G hG (subgroup_at G S y) (subgroup_gset_decidable_equality G hG S hS)))
        (gset_stabilizer_finite G hG X dX y))
      (concat Nat a b (cardinality (GSetStabilizer G X (S .point)) (subgroup_stabilizer_finite G S hS)) ab
        (fingp_card_irrel (GSetStabilizer G X (S .point)) (gset_stabilizer_finite G hG X dX (S .point))
          (subgroup_stabilizer_finite G S hS)))

def subgroup_at_finite (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (y : gset_underlying G (S .gset))
  : IsFiniteGroup (subgroup_group G (subgroup_at G S y))
  ≔ subgroup_group_finite G hG (subgroup_at G S y) (subgroup_gset_decidable_equality G hG S hS)

def subgroup_at_card (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (y : gset_underlying G (S .gset))
  : Id Nat (group_card (subgroup_group G (subgroup_at G S y)) (subgroup_at_finite G hG S hS y))
      (group_card (subgroup_group G S) hS)
  ≔ let X ≔ S .gset in
    let Sy ≔ subgroup_at G S y in
    let hSy ≔ subgroup_at_finite G hG S hS y in
    calc
      group_card (subgroup_group G Sy) hSy
      = cardinality (GSetStabilizer G X y) (subgroup_stabilizer_finite G Sy hSy)
        by inverse Nat (cardinality (GSetStabilizer G X y) (subgroup_stabilizer_finite G Sy hSy))
          (group_card (subgroup_group G Sy) hSy) (subgroup_stabilizer_card G Sy hSy)
      = cardinality (GSetStabilizer G X (S .point)) (subgroup_stabilizer_finite G S hS)
        by subgroup_at_stabilizer_card G hG S hS y
      = group_card (subgroup_group G S) hS by subgroup_stabilizer_card G S hS ∎

{` For a finite subgroup S = (X, x) of a finite group: S fixes y exactly
   when (X, y) = S. `}
def subgroup_at_path_of_fixes (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (y : gset_underlying G (S .gset))
  (f : SubgroupFixes G S (S .gset) y) : Id (Subgroups G) S (subgroup_at G S y)
  ≔ subgroup_le_card_eq G hG S (subgroup_at G S y) hS (subgroup_at_finite G hG S hS y) f
      (inverse Nat (group_card (subgroup_group G (subgroup_at G S y)) (subgroup_at_finite G hG S hS y))
        (group_card (subgroup_group G S) hS) (subgroup_at_card G hG S hS y))

def subgroup_path_fixes (G : Group) (S T : Subgroups G) (p : Id (Subgroups G) S T)
  : SubgroupLe G S T
  ≔ transport (Subgroups G) (T' ↦ SubgroupLe G S T') S T p (subgroup_le_refl G S)
