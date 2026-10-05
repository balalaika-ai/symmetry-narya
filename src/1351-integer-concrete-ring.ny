export "1350-concrete-rings"
export "1361-integer-mixed-ring"

{` Chapter 13 (fields.tex 1177-1219), the example after def:ring: the
   integers as a concrete ring, for an arbitrary circle C (ℤ = circle_group
   C, the abelian group circle_abelian_group C), with 1_ℤ ≔ id_ℤ.

   Route. The book gives Bμ explicitly as the curried map
   z ↦ ve(sh_BBℤ, (e_z, !)) (formalized in module 1352). Here μ : Hom(ℤ,
   Hom(ℤ, ℤ)) is the homomorphism sending loop to the symmetry σ of
   Hom(ℤ, ℤ) that corresponds to id_ℤ under USym Hom(ℤ, ℤ) ≃ Hom(ℤ, ℤ)
   (abelian_hom_usym_equiv, module 1207), i.e. μ is determined by
   ev ∘ USym μ (loop) = id_ℤ, which is the printed unit law. We show
   ℓ_a ≔ ev ∘ USym μ (a) is the homomorphism ℓ_a of the integers as a mixed
   ring (integer_mixed_left, module 1361): ℓ_a(loop) = a, because a ↦ ℓ_a(loop)
   is an abstract endomorphism of abstr(ℤ) fixing loop, hence the identity
   (deloop_hom, module 710). So the field left of the concrete ring is
   integer_mixed_left C with left_spec from zring_left_spec, and the laws,
   commutativity and non-triviality follow from the mixed ring of module
   1361. The book's computation Bμ(loop^j, loop^k) = s^{jk} appears on
   symmetries as loop^j · loop^k = loop^{jk}.

   The argument ℓ_a = integer_mixed_left a is given for an arbitrary
   evaluation ev : USym H → Hom(ℤ, ℤ) with ev(σ) = id and the pointwise
   product law (zring_* lemmas) and then instantiated with
   ev = hom_of_symmetry, so that only Hom-level types involving
   hom_of_symmetry are ever compared (performance, see module 1350). `}

{` An abstract endomorphism of abstr(ℤ) fixing loop is the identity. `}
def circle_abstract_endo_fixing_loop (C : CircleSignature)
  (φ : AbstractHom (abstr (circle_group C)) (abstr (circle_group C)))
  (e : Id (USym (circle_group C)) (φ .fst (C .loop)) (C .loop)) (a : USym (circle_group C))
  : Id (USym (circle_group C)) (φ .fst a) a
  ≔ let Z ≔ circle_group C in let U ≔ USym Z in
    let D ≔ deloop_hom Z Z φ in
    let ev : U → AbstractHom (abstr Z) (abstr Z) → U ≔ x ψ ↦ ψ .fst x in
    calc
      φ .fst a = usym_hom Z Z D a
        by inverse U (usym_hom Z Z D a) (φ .fst a) (refl (ev a) (deloop_hom_section Z Z φ))
      = usym_hom Z Z (group_hom_id Z) a
        by refl ((f ↦ usym_hom Z Z f a) : GroupHom Z Z → U)
          (circle_hom_from_loop_agreement C Z D (group_hom_id Z)
            (calc
               usym_hom Z Z D (C .loop) = φ .fst (C .loop) by refl (ev (C .loop)) (deloop_hom_section Z Z φ)
               = C .loop by e
               = usym_hom Z Z (group_hom_id Z) (C .loop)
                 by inverse U (usym_hom Z Z (group_hom_id Z) (C .loop)) (C .loop) (usym_hom_id Z (C .loop)) ∎))
      = a by usym_hom_id Z a ∎

{` Generic part: L : USym ℤ → Hom(ℤ, ℤ) (a · b ≔ USym(L a)(b)) such that
   (a + a') · b = a · b + a' · b and loop · loop = loop. `}
def zring_right_hom (C : CircleSignature) (L : USym (circle_group C) → GroupHom (circle_group C) (circle_group C))
  (rd : (a a' b : USym (circle_group C))
    → Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (L (usym_mul (circle_group C) a a')) b)
        (usym_mul (circle_group C) (usym_hom (circle_group C) (circle_group C) (L a) b) (usym_hom (circle_group C) (circle_group C) (L a') b)))
  (ll : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (L (C .loop)) (C .loop)) (C .loop))
  (b : USym (circle_group C)) : AbstractHom (abstr (circle_group C)) (abstr (circle_group C))
  ≔ (a ↦ usym_hom (circle_group C) (circle_group C) (L a) b, a a' ↦ rd a a' b)

def zring_left_loop (C : CircleSignature) (L : USym (circle_group C) → GroupHom (circle_group C) (circle_group C))
  (rd : (a a' b : USym (circle_group C))
    → Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (L (usym_mul (circle_group C) a a')) b)
        (usym_mul (circle_group C) (usym_hom (circle_group C) (circle_group C) (L a) b) (usym_hom (circle_group C) (circle_group C) (L a') b)))
  (ll : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (L (C .loop)) (C .loop)) (C .loop))
  (a : USym (circle_group C))
  : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (L a) (C .loop)) a
  ≔ circle_abstract_endo_fixing_loop C (zring_right_hom C L rd ll (C .loop)) ll a

def zring_left_mixed (C : CircleSignature) (L : USym (circle_group C) → GroupHom (circle_group C) (circle_group C))
  (rd : (a a' b : USym (circle_group C))
    → Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (L (usym_mul (circle_group C) a a')) b)
        (usym_mul (circle_group C) (usym_hom (circle_group C) (circle_group C) (L a) b) (usym_hom (circle_group C) (circle_group C) (L a') b)))
  (ll : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (L (C .loop)) (C .loop)) (C .loop))
  (a : USym (circle_group C))
  : Id (GroupHom (circle_group C) (circle_group C)) (L a) (integer_mixed_left C a)
  ≔ let Z ≔ circle_group C in
    circle_hom_from_loop_agreement C Z (L a) (integer_mixed_left C a)
      (concat (USym Z) (usym_hom Z Z (L a) (C .loop)) a (usym_hom Z Z (integer_mixed_left C a) (C .loop))
        (zring_left_loop C L rd ll a)
        (inverse (USym Z) (usym_hom Z Z (integer_mixed_left C a) (C .loop)) a (circle_group_hom_from_symmetry_loop C Z a)))

{` Generic: for ev : USym H → Hom(ℤ, ℤ), σ with ev(σ) = id and μ with
   USym μ (loop) = σ: the printed unit law and loop · loop = loop. `}
def zring_unit_law (C : CircleSignature) (H : Group) (ev : USym H → GroupHom (circle_group C) (circle_group C)) (σ : USym H)
  (hσ : Id (GroupHom (circle_group C) (circle_group C)) (ev σ) (group_hom_id (circle_group C))) (μ : GroupHom (circle_group C) H)
  (hμ : Id (USym H) (usym_hom (circle_group C) H μ (C .loop)) σ)
  : Id (GroupHom (circle_group C) (circle_group C))
      (ev (usym_hom (circle_group C) H (group_hom_compose (circle_group C) (circle_group C) H (group_hom_id (circle_group C)) μ) (circle_group_loop C)))
      (group_hom_id (circle_group C))
  ≔ let Z ≔ circle_group C in
    calc
      ev (usym_hom Z H (group_hom_compose Z Z H (group_hom_id Z) μ) (C .loop))
      = ev (usym_hom Z H μ (usym_hom Z Z (group_hom_id Z) (C .loop)))
        by map_path (USym H) (GroupHom Z Z) ev (usym_hom Z H (group_hom_compose Z Z H (group_hom_id Z) μ) (C .loop))
          (usym_hom Z H μ (usym_hom Z Z (group_hom_id Z) (C .loop)))
          (refl ((φ ↦ φ (C .loop)) : (USym Z → USym H) → USym H) (usym_hom_compose Z Z H (group_hom_id Z) μ))
      = ev (usym_hom Z H μ (C .loop))
        by map_path (USym Z) (GroupHom Z Z) (x ↦ ev (usym_hom Z H μ x)) (usym_hom Z Z (group_hom_id Z) (C .loop)) (C .loop)
          (usym_hom_id Z (C .loop))
      = ev σ by map_path (USym H) (GroupHom Z Z) ev (usym_hom Z H μ (C .loop)) σ hμ
      = group_hom_id Z by hσ ∎

def zring_loop_loop (C : CircleSignature) (H : Group) (ev : USym H → GroupHom (circle_group C) (circle_group C)) (σ : USym H)
  (hσ : Id (GroupHom (circle_group C) (circle_group C)) (ev σ) (group_hom_id (circle_group C))) (μ : GroupHom (circle_group C) H)
  (hμ : Id (USym H) (usym_hom (circle_group C) H μ (C .loop)) σ)
  : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (ev (usym_hom (circle_group C) H μ (C .loop))) (C .loop)) (C .loop)
  ≔ let Z ≔ circle_group C in let U ≔ USym Z in
    calc
      usym_hom Z Z (ev (usym_hom Z H μ (C .loop))) (C .loop) = usym_hom Z Z (ev σ) (C .loop)
        by map_path (USym H) U (p ↦ usym_hom Z Z (ev p) (C .loop)) (usym_hom Z H μ (C .loop)) σ hμ
      = usym_hom Z Z (group_hom_id Z) (C .loop)
        by map_path (GroupHom Z Z) U (f ↦ usym_hom Z Z f (C .loop)) (ev σ) (group_hom_id Z) hσ
      = C .loop by usym_hom_id Z (C .loop) ∎

{` The integer instance: H = Hom(ℤ, ℤ), ev = hom_of_symmetry, σ ↔ id_ℤ. `}
def integer_mu_symmetry (C : CircleSignature)
  : USym (abelian_hom_group (circle_group C) (circle_abelian_group C))
  ≔ equiv_inverse_map (USym (abelian_hom_group (circle_group C) (circle_abelian_group C)))
      (GroupHom (circle_group C) (circle_group C)) (abelian_hom_usym_equiv (circle_group C) (circle_abelian_group C))
      (group_hom_id (circle_group C))

def integer_mu_symmetry_hom (C : CircleSignature)
  : Id (GroupHom (circle_group C) (circle_group C))
      (hom_of_symmetry (circle_group C) (circle_abelian_group C) (integer_mu_symmetry C)) (group_hom_id (circle_group C))
  ≔ equiv_counit (USym (abelian_hom_group (circle_group C) (circle_abelian_group C)))
      (GroupHom (circle_group C) (circle_group C)) (abelian_hom_usym_equiv (circle_group C) (circle_abelian_group C))
      (group_hom_id (circle_group C))

def integer_concrete_mu (C : CircleSignature)
  : GroupHom (circle_group C) (abelian_hom_group (circle_group C) (circle_abelian_group C))
  ≔ circle_group_hom_from_symmetry C (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_mu_symmetry C)

{` USym μ (loop^j) = σ^j. `}
def integer_concrete_mu_power (C : CircleSignature) (j : Int)
  : Id (USym (abelian_hom_group (circle_group C) (circle_abelian_group C)))
      (usym_hom (circle_group C) (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_concrete_mu C)
        (circle_power C j))
      (loop_power (BG (abelian_hom_group (circle_group C) (circle_abelian_group C)) .carrier)
        (shape (abelian_hom_group (circle_group C) (circle_abelian_group C))) (integer_mu_symmetry C) j)
  ≔ let Z ≔ circle_group C in let H ≔ abelian_hom_group Z (circle_abelian_group C) in
    concat (USym H) (usym_hom Z H (integer_concrete_mu C) (circle_power C j))
      (loop_power (BG H .carrier) (shape H) (usym_hom Z H (integer_concrete_mu C) (C .loop)) j)
      (loop_power (BG H .carrier) (shape H) (integer_mu_symmetry C) j)
      (loops_map_power (BG Z) (BG H) (hom_B Z H (integer_concrete_mu C)) (C .loop) j)
      (refl ((x ↦ loop_power (BG H .carrier) (shape H) x j) : USym H → USym H)
        (circle_group_hom_from_symmetry_loop C H (integer_mu_symmetry C)))

{` Generic: for ev, σ, μ as above, ev(USym μ (a)) is the mixed-ring ℓ_a. `}
def zring_left_spec (C : CircleSignature) (H : Group) (ev : USym H → GroupHom (circle_group C) (circle_group C))
  (hmul : (p q : USym H) (b : USym (circle_group C))
    → Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (ev (usym_mul H p q)) b)
        (usym_mul (circle_group C) (usym_hom (circle_group C) (circle_group C) (ev p) b) (usym_hom (circle_group C) (circle_group C) (ev q) b)))
  (σ : USym H) (hσ : Id (GroupHom (circle_group C) (circle_group C)) (ev σ) (group_hom_id (circle_group C))) (μ : GroupHom (circle_group C) H)
  (hμ : Id (USym H) (usym_hom (circle_group C) H μ (C .loop)) σ) (a : USym (circle_group C))
  : Id (GroupHom (circle_group C) (circle_group C)) (ev (usym_hom (circle_group C) H μ a)) (integer_mixed_left C a)
  ≔ let Z ≔ circle_group C in
    zring_left_mixed C (x ↦ ev (usym_hom Z H μ x))
      (evaluation_rdistr Z H μ ev hmul (x ↦ ev (usym_hom Z H μ x)) (x ↦ refl (ev (usym_hom Z H μ x))))
      (zring_loop_loop C H ev σ hσ μ hμ) a

{` ℓ_a = ev ∘ USym μ (a) is the mixed-ring ℓ_a (module 1361). `}
def integer_concrete_left_spec (C : CircleSignature)
  : ConcreteRingLeftSpec (circle_abelian_group C) (integer_concrete_mu C) (integer_mixed_left C)
  ≔ a ↦ inverse (GroupHom (circle_group C) (circle_group C))
      (hom_of_symmetry (circle_group C) (circle_abelian_group C) (usym_hom (circle_group C) (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_concrete_mu C) a)) (integer_mixed_left C a)
      (zring_left_spec C (abelian_hom_group (circle_group C) (circle_abelian_group C)) (hom_of_symmetry (circle_group C) (circle_abelian_group C)) (abelian_hom_usym_mul (circle_group C) (circle_abelian_group C)) (integer_mu_symmetry C)
        (integer_mu_symmetry_hom C) (integer_concrete_mu C)
        (circle_group_hom_from_symmetry_loop C (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_mu_symmetry C)) a)

def integer_concrete_mul_one_right (C : CircleSignature) (a : USym (circle_group C))
  : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (integer_mixed_left C a) (usym_hom (circle_group C) (circle_group C) (group_hom_id (circle_group C)) (C .loop))) a
  ≔ let Z ≔ circle_group C in
    concat (USym Z) (usym_hom Z Z (integer_mixed_left C a) (usym_hom Z Z (group_hom_id Z) (C .loop)))
      (usym_hom Z Z (integer_mixed_left C a) (C .loop)) a
      (map_path (USym Z) (USym Z) (usym_hom Z Z (integer_mixed_left C a)) (usym_hom Z Z (group_hom_id Z) (C .loop)) (C .loop)
        (usym_hom_id Z (C .loop)))
      (circle_group_hom_from_symmetry_loop C Z a)

{` The example: (ℤ, 1_ℤ = id, μ) is a ring … `}
def integer_concrete_ring (C : CircleSignature) : ConcreteRing C
  ≔ ((circle_abelian_group C), group_hom_id (circle_group C), integer_concrete_mu C, integer_mixed_left C, integer_concrete_left_spec C,
     ((zring_unit_law C (abelian_hom_group (circle_group C) (circle_abelian_group C)) (hom_of_symmetry (circle_group C) (circle_abelian_group C)) (integer_mu_symmetry C) (integer_mu_symmetry_hom C)
         (integer_concrete_mu C) (circle_group_hom_from_symmetry_loop C (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_mu_symmetry C)),
       integer_concrete_mul_one_right C),
      mixed_mul_assoc (integer_mixed_ring C)))

{` … which is commutative … `}
def integer_concrete_ring_commutative (C : CircleSignature) : IsCommutativeConcreteRing C (integer_concrete_ring C)
  ≔ mixed_commutative_to_mul_comm (integer_mixed_ring C) (integer_mixed_ring_commutative C)

{` … and non-trivial: id_ℤ is not the trivial homomorphism. `}
def integer_concrete_ring_non_trivial (C : CircleSignature) : IsNonTrivialConcreteRing C (integer_concrete_ring C)
  ≔ p ↦
    let Z ≔ circle_group C in let U ≔ USym Z in
    circle_loop_not_refl C
      (calc
         C .loop = usym_hom Z Z (group_hom_id Z) (C .loop)
           by inverse U (usym_hom Z Z (group_hom_id Z) (C .loop)) (C .loop) (usym_hom_id Z (C .loop))
         = usym_hom Z Z (concrete_trivial_hom Z Z) (C .loop)
           by refl ((f ↦ usym_hom Z Z f (C .loop)) : GroupHom Z Z → U) p
         = refl (C .base) by circle_group_hom_ev_trivial C Z ∎)

def integer_concrete_abstract_ring (C : CircleSignature) : AbstractRing
  ≔ concrete_ring_abstract_ring C (integer_concrete_ring C)

def integer_concrete_abstract_commutative (C : CircleSignature) : IsCommutativeRing (integer_concrete_abstract_ring C)
  ≔ concrete_ring_abstract_commutative C (integer_concrete_ring C) (integer_concrete_ring_commutative C)

def integer_concrete_abstract_non_trivial (C : CircleSignature) : IsNonTrivialRing (integer_concrete_abstract_ring C)
  ≔ concrete_ring_abstract_non_trivial C (integer_concrete_ring C) (integer_concrete_ring_non_trivial C)

{` The symmetry-level form of Bμ(loop^j, loop^k) = s^{jk}:
   loop^j · loop^k = loop^{jk}; litmus w(loop² · loop³) = 6. `}
def integer_concrete_mul_powers (C : CircleSignature) (j k : Int)
  : Id (USym (circle_group C)) (concrete_ring_mul C (integer_concrete_ring C) (circle_power C j) (circle_power C k))
      (circle_power C (int_mul j k))
  ≔ circle_symmetry_from_winding C (mixed_mul (integer_mixed_ring C) (circle_power C j) (circle_power C k))
      (circle_power C (int_mul j k))
      (calc
         circle_winding C (mixed_mul (integer_mixed_ring C) (circle_power C j) (circle_power C k))
         = int_mul (circle_winding C (circle_power C j)) (circle_winding C (circle_power C k))
           by integer_mixed_winding C (circle_power C j) (circle_power C k)
         = int_mul j k by refl int_mul (circle_winding_power C j) (circle_winding_power C k)
         = circle_winding C (circle_power C (int_mul j k))
           by inverse Int (circle_winding C (circle_power C (int_mul j k))) (int_mul j k)
             (circle_winding_power C (int_mul j k)) ∎)

def integer_concrete_two_times_three (C : CircleSignature)
  : Id Int (circle_winding C (concrete_ring_mul C (integer_concrete_ring C) (circle_power C (pos. 2)) (circle_power C (pos. 3))))
      (pos. 6)
  ≔ concat Int (circle_winding C (concrete_ring_mul C (integer_concrete_ring C) (circle_power C (pos. 2)) (circle_power C (pos. 3))))
      (circle_winding C (circle_power C (pos. 6))) (pos. 6)
      (map_path (USym (circle_group C)) Int (circle_winding C)
        (concrete_ring_mul C (integer_concrete_ring C) (circle_power C (pos. 2)) (circle_power C (pos. 3)))
        (circle_power C (pos. 6)) (integer_concrete_mul_powers C (pos. 2) (pos. 3)))
      (circle_winding_power C (pos. 6))
