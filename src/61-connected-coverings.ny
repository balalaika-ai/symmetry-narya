export "60-circle-orbit-components"

def book_contractibility_equiv (A B : Type) (e : Equiv A B) : Equiv (BookIsContr A) (BookIsContr B)
  ≔ id_to_equiv (BookIsContr A) (BookIsContr B) (refl BookIsContr (ua A B e))

def connected_equiv (A B : Type) (e : Equiv A B) : Equiv (Connected A) (Connected B)
  ≔ id_to_equiv (Connected A) (Connected B) (refl Connected (ua A B e))

def circle_total_connected_cyclic (C : CircleSignature) (R : C .carrier → Type)
  : Equiv (Connected (Σ (C .carrier) R)) (Cyclic (R (C .base)) (family_monodromy C R))
  ≔ compose_equiv (Connected (Σ (C .carrier) R)) (BookIsContr (SetTrunc (Σ (C .carrier) R)))
      (Cyclic (R (C .base)) (family_monodromy C R))
      (connected_set_trunc_equiv (Σ (C .carrier) R))
      (compose_equiv (BookIsContr (SetTrunc (Σ (C .carrier) R)))
        (BookIsContr (OrbitQuotient (R (C .base)) (family_monodromy C R)))
        (Cyclic (R (C .base)) (family_monodromy C R))
        (book_contractibility_equiv (SetTrunc (Σ (C .carrier) R))
          (OrbitQuotient (R (C .base)) (family_monodromy C R)) (circle_components_orbits_equiv C R))
        (canonical_inverse_equiv (Cyclic (R (C .base)) (family_monodromy C R))
          (BookIsContr (OrbitQuotient (R (C .base)) (family_monodromy C R)))
          (cyclic_quotient_equiv (R (C .base)) (family_monodromy C R))))

def ConnectedCoverings (B : Type) : Type ≔ Σ (Coverings B) (c ↦ Connected (c .fst))
def cyclic_permutation (p : Permutations) : Type ≔ Cyclic (p .fst .fst) (p .snd)

def circle_covering_connected_cyclic (C : CircleSignature) (c : Coverings (C .carrier))
  : Equiv (Connected (c .fst)) (cyclic_permutation (circle_coverings_permutations C .map c))
  ≔ compose_equiv (Connected (c .fst))
      (Connected (Σ (C .carrier) (b ↦ BookFiber (c .fst) (C .carrier) (c .snd .fst) b)))
      (cyclic_permutation (circle_coverings_permutations C .map c))
      (connected_equiv (c .fst) (Σ (C .carrier) (b ↦ BookFiber (c .fst) (C .carrier) (c .snd .fst) b))
        (canonical_inverse_equiv (Σ (C .carrier) (b ↦ BookFiber (c .fst) (C .carrier) (c .snd .fst) b))
          (c .fst) (sum_of_fibers_equiv (c .fst) (C .carrier) (c .snd .fst))))
      (circle_total_connected_cyclic C (b ↦ BookFiber (c .fst) (C .carrier) (c .snd .fst) b))

{` Restriction of an equivalence to propositions, with the forward map
   literally given by the original map on the first coordinate. `}
def propositional_subtype_equiv (A B : Type) (P : A → Type) (Q : B → Type)
  (hp : (a : A) → isProp (P a)) (hq : (b : B) → isProp (Q b))
  (e : Equiv A B) (d : (a : A) → Equiv (P a) (Q (e .map a))) : Equiv (Σ A P) (Σ B Q)
  ≔ let f : Σ A P → Σ B Q ≔ (a ↦ (e .map (a .fst), d (a .fst) .map (a .snd))) in
    let g : Σ B Q → Σ A P ≔ (b ↦
      let a ≔ equiv_inverse_map A B e (b .fst) in
      (a, equiv_inverse_map (P a) (Q (e .map a)) (d a)
        (transport B Q (b .fst) (e .map a) (inverse B (e .map a) (b .fst) (equiv_counit A B e (b .fst))) (b .snd)))) in
    quasi_inverse_equiv (Σ A P) (Σ B Q) f g
      (a ↦ subtype_equal A P hp (g (f a)) a (equiv_retraction A B e (a .fst)))
      (b ↦ subtype_equal B Q hq (f (g b)) b (equiv_counit A B e (b .fst)))

{` thm:cycset-connS1cover, for every CircleSignature (instantiated at constructed_circle in module 250). `}
def circle_connected_coverings_cycles (C : CircleSignature) : BookEquiv (ConnectedCoverings (C .carrier)) Cycles
  ≔ book_equivalence (ConnectedCoverings (C .carrier)) Cycles
      (propositional_subtype_equiv (Coverings (C .carrier)) Permutations
        (c ↦ Connected (c .fst)) cyclic_permutation (c ↦ connected_isprop (c .fst))
        (p ↦ cyclic_prop (p .fst .fst) (p .snd))
        (circle_coverings_permutations C) (circle_covering_connected_cyclic C))

def connected_coverings_classification_underlying (C : CircleSignature) (c : ConnectedCoverings (C .carrier))
  : Id Permutations (circle_connected_coverings_cycles C .map c .fst)
      (circle_coverings_permutations C .map (c .fst))
  ≔ refl (circle_coverings_permutations C .map (c .fst))

def permutation_family (C : CircleSignature) (p : Permutations) : C .carrier → SetTypes
  ≔ equiv_inverse_map (C .carrier → SetTypes) Permutations (circle_setfamilies_permutations C) p

def permutation_family_monodromy (C : CircleSignature) (p : Permutations)
  : Id Permutations (circle_setfamilies_permutations C .map (permutation_family C p)) p
  ≔ equiv_counit (C .carrier → SetTypes) Permutations (circle_setfamilies_permutations C) p

def permutation_orbits (p : Permutations) : Type ≔ OrbitQuotient (p .fst .fst) (p .snd)

{` The source formulation starts with a given permutation.  This transports
   the actual-family comparison along the verified reconstruction counit. `}
def permutation_cover_components (C : CircleSignature) (p : Permutations)
  : BookEquiv (SetTrunc (Σ (C .carrier) (z ↦ permutation_family C p z .fst))) (permutation_orbits p)
  ≔ book_equivalence (SetTrunc (Σ (C .carrier) (z ↦ permutation_family C p z .fst))) (permutation_orbits p)
      (compose_equiv (SetTrunc (Σ (C .carrier) (z ↦ permutation_family C p z .fst)))
        (permutation_orbits (circle_setfamilies_permutations C .map (permutation_family C p)))
        (permutation_orbits p)
        (circle_components_orbits_equiv C (z ↦ permutation_family C p z .fst))
        (id_to_equiv (permutation_orbits (circle_setfamilies_permutations C .map (permutation_family C p)))
          (permutation_orbits p) (refl permutation_orbits (permutation_family_monodromy C p))))
