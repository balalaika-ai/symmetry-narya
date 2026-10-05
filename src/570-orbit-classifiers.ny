export "521-orbits-set-truncation"

{` Chapter 5: computing a set of orbits X/G from an invariant classifier.
   A map of G-sets c : X → triv_G B (an "invariant" with values in a set B)
   with representatives r : B → X(sh_G) such that c(r b) = b and every x is
   related to r(c x) by the action gives X/G ≃ B (through cor:orbit-equiv:
   X/G is the quotient of X(sh_G) by ∃_g (g · x = y)). Used to determine
   sets of orbits in examples (xca:Gset-A->B). `}

{` c is constant on orbits: c(g · x) = c(x). `}
def orbit_classifier_invariant (G : Group) (X : GSet G) (B : SetTypes) (c : GSetHom G X (gset_trivial G B))
  (g : USym G) (x : gset_underlying G X)
  : Id (B .fst) (c (shape G) (gset_usym_act G X g x)) (c (shape G) x)
  ≔ concat (B .fst) (c (shape G) (gset_usym_act G X g x))
      (gset_act G (gset_trivial G B) (shape G) (shape G) g (c (shape G) x)) (c (shape G) x)
      (gset_hom_natural G X (gset_trivial G B) c (shape G) (shape G) g x)
      (gset_trivial_act G B (shape G) (shape G) g (c (shape G) x))

def orbit_classifier_respects (G : Group) (X : GSet G) (B : SetTypes) (c : GSetHom G X (gset_trivial G B))
  : Respects (gset_underlying G X) (B .fst) (orbit_equivalence_relation G X) (c (shape G))
  ≔ x y r ↦
      mere_rec (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) y))
        (Id (B .fst) (c (shape G) x) (c (shape G) y)) (B .snd (c (shape G) x) (c (shape G) y))
        (t ↦ concat (B .fst) (c (shape G) x) (c (shape G) (gset_usym_act G X (t .fst) x)) (c (shape G) y)
          (inverse (B .fst) (c (shape G) (gset_usym_act G X (t .fst) x)) (c (shape G) x)
            (orbit_classifier_invariant G X B c (t .fst) x))
          (refl (c (shape G)) (t .snd)))
        r

def orbits_classifier_equiv (G : Group) (X : GSet G) (B : SetTypes) (c : GSetHom G X (gset_trivial G B))
  (r : B .fst → gset_underlying G X) (hr : (b : B .fst) → Id (B .fst) (c (shape G) (r b)) b)
  (hx : (x : gset_underlying G X) → OrbitRelation G X x (r (c (shape G) x)))
  : Equiv (Orbits G X) (B .fst)
  ≔ let S ≔ gset_underlying G X in
    let R ≔ orbit_equivalence_relation G X in
    let f ≔ c (shape G) in
    let Q ≔ Quotient S R in
    let back : (x y : S) → Id (B .fst) (f x) (f y) → Rel S R x y
      ≔ x y e ↦ R .transitive x (r (f x)) y (hx x)
          (transport (B .fst) (b ↦ Rel S R (r b) y) (f y) (f x) (inverse (B .fst) (f x) (f y) e)
            (R .symmetric y (r (f y)) (hx y))) in
    let hf : Surjective S (B .fst) f
      ≔ b ↦ mere (BookFiber S (B .fst) f b) (r b, inverse (B .fst) (f (r b)) b (hr b)) in
    compose_equiv (Orbits G X) Q (B .fst)
      (canonical_inverse_equiv Q (Orbits G X) (native_equivalence Q (Orbits G X) (orbit_quotient_equiv G X)))
      (native_equivalence Q (B .fst)
        (surjection_quotient_equiv S (B .fst) (B .snd) R f hf (orbit_classifier_respects G X B c) back))

{` The equivalence sends the orbit [x] to c(x). `}
def orbits_classifier_equiv_class (G : Group) (X : GSet G) (B : SetTypes) (c : GSetHom G X (gset_trivial G B))
  (r : B .fst → gset_underlying G X) (hr : (b : B .fst) → Id (B .fst) (c (shape G) (r b)) b)
  (hx : (x : gset_underlying G X) → OrbitRelation G X x (r (c (shape G) x))) (x : gset_underlying G X)
  : Id (B .fst) (orbits_classifier_equiv G X B c r hr hx .map (orbit_of_point G X x)) (c (shape G) x)
  ≔ let S ≔ gset_underlying G X in
    let R ≔ orbit_equivalence_relation G X in
    let Q ≔ Quotient S R in
    let qe ≔ native_equivalence Q (Orbits G X) (orbit_quotient_equiv G X) in
    refl (quotient_rec S (B .fst) R (B .snd) (c (shape G)) (orbit_classifier_respects G X B c))
      (equiv_retraction Q (Orbits G X) qe (quotient_class S R x))
