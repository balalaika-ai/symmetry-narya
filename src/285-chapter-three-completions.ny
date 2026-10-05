export "272-quotient-fiber-equivalence"

{` Additional chapter-3 results:
   (a) xca:cancel-surjection in its n-connected form; (b) the k-cycle count
   for k = 0 and k = 1; (c) the decidable part of the corollary after
   prop:ump-cycn-into-groupoids; (d) the n = -2 instances; (e) the printed
   step of thm:image-Z-to-Cm; (f) universality of the constant Unit
   covering; (g) the printed map of con:fibcomp=fibfib; (h) thm:n-im-univ-prop
   in one statement over all n >= -2. `}

{` (a) HoTT book Lemma 7.5.7, used below for xca:cancel-surjection
   (circle.tex:3104).  If p : A → B is n-connected (n = k-1 >= -1) and P is
   a family of n-types over B, restriction of sections along p is an
   equivalence.  The extension of s at b applies the extension of
   (a,q) ↦ trp_{q⁻¹}(s a) along |_|_n to the center of ||p⁻¹(b)||_n.  Level 0
   with set families is connected_map_sections_equiv (module 109). `}
def n_connected_extend (k : Nat) (A B : Type) (p : A → B) (hp : NConnectedMap k A B p)
  (P : B → Type) (hP : (b : B) → HLevel (suc. k) (P b)) (s : (a : A) → P (p a)) (b : B) : P b
  ≔ trunc_extend k (BookFiber A B p b) (truncation k (BookFiber A B p b)) (P b) (hP b)
      (section_on_fiber A B p P s b) (hp b .center)

def n_connected_extend_beta (k : Nat) (A B : Type) (p : A → B) (hp : NConnectedMap k A B p)
  (P : B → Type) (hP : (b : B) → HLevel (suc. k) (P b)) (s : (a : A) → P (p a)) (a : A)
  : Id (P (p a)) (n_connected_extend k A B p hp P hP s (p a)) (s a)
  ≔ let F ≔ BookFiber A B p (p a) in
    let g ≔ section_on_fiber A B p P s (p a) in
    let E ≔ trunc_extend k F (truncation k F) (P (p a)) (hP (p a)) g in
    let u ≔ trunc_unit k F (a, refl (p a)) in
    concat (P (p a)) (E (hp (p a) .center)) (E u) (s a)
      (refl E (hp (p a) .contract u))
      (concat (P (p a)) (E u) (g (a, refl (p a))) (s a)
        (inverse (P (p a)) (g (a, refl (p a))) (E u)
          (trunc_extend_beta k F (truncation k F) (P (p a)) (hP (p a)) g (a, refl (p a))))
        (concat (P (p a)) (g (a, refl (p a))) (transport B P (p a) (p a) (refl (p a)) (s a)) (s a)
          (refl ((q ↦ transport B P (p a) (p a) q (s a)) : Id B (p a) (p a) → P (p a))
            (inverse_refl B (p a)))
          (transport_refl B P (p a) (s a))))

def n_connected_extend_eta (k : Nat) (A B : Type) (p : A → B) (hp : NConnectedMap k A B p)
  (P : B → Type) (hP : (b : B) → HLevel (suc. k) (P b)) (s : (b : B) → P b) (b : B)
  : Id (P b) (n_connected_extend k A B p hp P hP (restrict_sections A B p P s) b) (s b)
  ≔ let F ≔ BookFiber A B p b in
    let g ≔ section_on_fiber A B p P (restrict_sections A B p P s) b in
    let E ≔ trunc_extend k F (truncation k F) (P b) (hP b) g in
    trunc_ind k F (truncation k F) (t ↦ Id (P b) (E t) (s b))
      (t ↦ hlevel_raise k (Id (P b) (E t) (s b)) (hP b (E t) (s b)))
      (w ↦ concat (P b) (E (trunc_unit k F w)) (g w) (s b)
        (inverse (P b) (g w) (E (trunc_unit k F w))
          (trunc_extend_beta k F (truncation k F) (P b) (hP b) g w))
        (pathover_transport_equiv B P (p (w .fst)) b (inverse B b (p (w .fst)) (w .snd))
          (s (p (w .fst))) (s b) .map (refl s (inverse B b (p (w .fst)) (w .snd)))))
      (hp b .center)

def n_connected_sections_equiv (k : Nat) (A B : Type) (p : A → B) (hp : NConnectedMap k A B p)
  (P : B → Type) (hP : (b : B) → HLevel (suc. k) (P b))
  : Equiv ((b : B) → P b) ((a : A) → P (p a))
  ≔ quasi_inverse_equiv ((b : B) → P b) ((a : A) → P (p a)) (restrict_sections A B p P)
      (n_connected_extend k A B p hp P hP)
      (s ↦ funext B P (n_connected_extend k A B p hp P hP (restrict_sections A B p P s)) s
        (n_connected_extend_eta k A B p hp P hP s))
      (s ↦ funext A (a ↦ P (p a)) (restrict_sections A B p P (n_connected_extend k A B p hp P hP s)) s
        (n_connected_extend_beta k A B p hp P hP s))

{` (a) xca:cancel-surjection (circle.tex:3104), the n-connected form
   for p : A → B n-connected (n = k-1 >= -1) and Y an
   (n+1)-type (HLevel k+2), ap_{-p} : (f = g) → (fp = gp) is an equivalence
   for all f g : B → Y.  Lemma 7.5.7 applies to b ↦ (f b = g b), a family
   of n-types.  The map of the equivalence is literally ap_{-p}. `}
def cancel_n_connected (k : Nat) (A B Y : Type) (p : A → B) (hp : NConnectedMap k A B p)
  (hY : HLevel (suc. (suc. k)) Y) (f g : B → Y)
  : Equiv (Id (B → Y) f g) (Id (A → Y) (precompose A B Y p f) (precompose A B Y p g))
  ≔ let F ≔ precompose A B Y p f in let G ≔ precompose A B Y p g in
    let e ≔ compose_equiv (Id (B → Y) f g) (Homotopy B (_ ↦ Y) f g) (Id (A → Y) F G)
      (function_extensionality B (_ ↦ Y) f g)
      (compose_equiv (Homotopy B (_ ↦ Y) f g) (Homotopy A (_ ↦ Y) F G) (Id (A → Y) F G)
        (n_connected_sections_equiv k A B p hp (b ↦ Id Y (f b) (g b)) (b ↦ hY (f b) (g b)))
        (funext_equiv A (_ ↦ Y) F G)) in
    equiv_change_map (Id (B → Y) f g) (Id (A → Y) F G) e
      (map_path (B → Y) (A → Y) (precompose A B Y p) f g)
      (r ↦ funext_eta A (_ ↦ Y) F G (map_path (B → Y) (A → Y) (precompose A B Y p) f g r))

{` Surjections are the (-1)-connected maps. `}
def surjection_minus_one_connected (A B : Type) (p : A → B) (hp : Surjective A B p) : NConnectedMap zero. A B p
  ≔ equiv_inverse_map (NConnectedMap zero. A B p) (Surjective A B p) (minus_one_connected_map_surjective A B p) hp

{` (a) The case n = -1 is cancel_surjection_into_set (module 40): p a
   surjection, Y a set (0-type).  Both equivalences have the map ap_{-p},
   so they are equal. `}
def cancel_surjection_into_set_minus_one_case (A B Y : Type) (p : A → B) (hp : Surjective A B p) (hy : isSet Y)
  (f g : B → Y)
  : Id (Equiv (Id (B → Y) f g) (Id (A → Y) (precompose A B Y p f) (precompose A B Y p g)))
      (cancel_surjection_into_set A B Y p hp hy f g)
      (cancel_n_connected zero. A B Y p (surjection_minus_one_connected A B p hp) (set_to_hlevel_two Y hy) f g)
  ≔ equiv_path (Id (B → Y) f g) (Id (A → Y) (precompose A B Y p f) (precompose A B Y p g))
      (cancel_surjection_into_set A B Y p hp hy f g)
      (cancel_n_connected zero. A B Y p (surjection_minus_one_connected A B p hp) (set_to_hlevel_two Y hy) f g)
      (refl (map_path (B → Y) (A → Y) (precompose A B Y p) f g))

{` (d) the n = -2 instances.  The (-2)-truncation is
   Unit, as in module 108. `}
def MinusTwoTrunc (A : Type) : Type ≔ Unit
def minus_two_trunc_unit (A : Type) : A → MinusTwoTrunc A ≔ _ ↦ star.
def MinusTwoConnectedType (A : Type) : Type ≔ BookIsContr (MinusTwoTrunc A)

{` def:n-connected, remark (circle.tex:3136): any type is (-2)-connected,
   since its (-2)-truncation is contractible. `}
def minus_two_connected_type (A : Type) : MinusTwoConnectedType A ≔ book_contraction Unit unit_contractible

{` The map notion of module 108 is literally "all fibers are (-2)-connected". `}
def minus_two_connected_map_fibers (A B : Type) (f : A → B)
  : Id Type (MinusTwoConnectedMap A B f) ((b : B) → MinusTwoConnectedType (BookFiber A B f b))
  ≔ refl (MinusTwoConnectedMap A B f)

{` lem:trunc-n-connected at n = -2: |_|_{-2} : A → ||A||_{-2} is (-2)-connected. `}
def minus_two_trunc_unit_connected (A : Type) : MinusTwoConnectedMap A (MinusTwoTrunc A) (minus_two_trunc_unit A)
  ≔ minus_two_connected_map A (MinusTwoTrunc A) (minus_two_trunc_unit A)

{` xca:trunc-sum-type+fam at n = -2: ||Σ_x Y(x)||_{-2} ≃ ||Σ_x ||Y(x)||_{-2}||_{-2}. `}
def minus_two_trunc_sum_equiv (X : Type) (Y : X → Type)
  : Equiv (MinusTwoTrunc (Σ X Y)) (MinusTwoTrunc (Σ X (x ↦ MinusTwoTrunc (Y x))))
  ≔ identity_equiv Unit

{` The form used in the proof of thm:n-im-univ-prop, at n = -2: over a
   (-2)-type (contractible) base only the summands need truncating. `}
def minus_two_trunc_sum_level_base_equiv (X : Type) (hX : HLevel zero. X) (Y : X → Type)
  : Equiv (MinusTwoTrunc (Σ X Y)) (Σ X (x ↦ MinusTwoTrunc (Y x)))
  ≔ let c ≔ sigma_contractible X (_ ↦ Unit) hX (_ ↦ unit_contractible) in
    iff_equiv Unit (Σ X (_ ↦ Unit)) unit_prop (contractible_prop (Σ X (_ ↦ Unit)) c)
      (_ ↦ c .center) (_ ↦ star.)

{` (f) audit E finding 8, def:universalcover / def:univ-cover (circle.tex:762,
   787): the constant Unit map with pointing path refl(b0) is a pointed
   covering over a pointed groupoid, and it is universal because its domain
   is contractible (lem:univ-cover-of-groupoid, via contractible_cover_universal).
   With the path projection and the constant Fin 1 map (module 99) all three
   pointed presentations of def:universalcover are universal. `}
def constant_unit_pointed_cover (B : Pointed) (groupoid : isGroupoid (B .carrier)) : BookPointedCoverings B
  ≔ (pointed_unit, (book_pointed_constant pointed_unit B, constant_pointed_unit_cover B groupoid))

def constant_unit_cover_universal (B : Pointed)
  : IsUniversalPointedCover pointed_unit B (book_pointed_constant pointed_unit B)
  ≔ contractible_cover_universal pointed_unit B (book_pointed_constant pointed_unit B)
      (book_contraction Unit unit_contractible)

{` (g) con:fibcomp=fibfib and xca:fibcomp=fibfib (circle.tex:3197-3225),
   the printed map e(b)(a,p) = ((g a, p), (a, q)), where
   q : (b, g a, p) = (h(g a), g a, refl) = g̃(a) is given componentwise by p,
   refl (g a) and the easy path over p from p to refl in the family
   y ↦ (y = h(g a)), which is the connection square conn. `}
def composite_double_fiber_printed_map (A X B : Type) (g : A → X) (h : X → B) (b : B)
  (w : BookFiber A B (compose A X B h g) b)
  : Σ (BookFiber X B h b) (u ↦ BookFiber A (Σ B (BookFiber X B h)) (composite_fiber_decomposition A X B g h) (b, u))
  ≔ ((g (w .fst), w .snd), (w .fst, (w .snd, (refl (g (w .fst)), conn B b (h (g (w .fst))) (w .snd)))))

{` The contract-away equivalence of module 104 sends the printed image of
   (a,p) back to (a,p), judgmentally. `}
def composite_double_fiber_printed_section (A X B : Type) (g : A → X) (h : X → B) (b : B)
  (w : BookFiber A B (compose A X B h g) b)
  : Id (BookFiber A B (compose A X B h g) b)
      (projection_composite_fiber_equiv A B (BookFiber X B h) (composite_fiber_decomposition A X B g h) b .map
        (composite_double_fiber_printed_map A X B g h b w)) w
  ≔ refl w

{` Hence composite_double_fiber_equiv (module 104) has the printed map. `}
def composite_double_fiber_equiv_is_printed (A X B : Type) (g : A → X) (h : X → B) (b : B)
  (w : BookFiber A B (compose A X B h g) b)
  : Id (Σ (BookFiber X B h b) (u ↦ BookFiber A (Σ B (BookFiber X B h)) (composite_fiber_decomposition A X B g h) (b, u)))
      (composite_double_fiber_equiv A X B g h b .map w) (composite_double_fiber_printed_map A X B g h b w)
  ≔ let S ≔ Σ (BookFiber X B h b) (u ↦ BookFiber A (Σ B (BookFiber X B h)) (composite_fiber_decomposition A X B g h) (b, u)) in
    let Fib ≔ BookFiber A B (compose A X B h g) b in
    let F ≔ projection_composite_fiber_equiv A B (BookFiber X B h) (composite_fiber_decomposition A X B g h) b in
    equivalence_injective S Fib F (composite_double_fiber_equiv A X B g h b .map w)
      (composite_double_fiber_printed_map A X B g h b w) (equiv_counit S Fib F w)

{` xca:fibcomp=fibfib: the printed e(b) is a fiberwise equivalence. `}
def composite_double_fiber_printed_equiv (A X B : Type) (g : A → X) (h : X → B) (b : B)
  : Equiv (BookFiber A B (compose A X B h g) b)
      (Σ (BookFiber X B h b) (u ↦ BookFiber A (Σ B (BookFiber X B h)) (composite_fiber_decomposition A X B g h) (b, u)))
  ≔ equiv_change_map (BookFiber A B (compose A X B h g) b)
      (Σ (BookFiber X B h b) (u ↦ BookFiber A (Σ B (BookFiber X B h)) (composite_fiber_decomposition A X B g h) (b, u)))
      (composite_double_fiber_equiv A X B g h b) (composite_double_fiber_printed_map A X B g h b)
      (composite_double_fiber_equiv_is_printed A X B g h b)

{` (h) thm:n-im-univ-prop (circle.tex:3251) as one
   statement for all n >= -2, indexed by m = n + 2 : Nat (m = 0 is n = -2,
   m = suc k is n = k - 1).  n-connected maps are MinusTwoConnectedMap at
   n = -2 and NConnectedMap k otherwise; n-truncated maps are TruncatedMap m
   (h-level n + 2 of every fiber) at every level. `}
def NConnectedMapFrom (m : Nat) (A B : Type) (f : A → B) : Type
  ≔ match m [ zero. ↦ MinusTwoConnectedMap A B f | suc. k ↦ NConnectedMap k A B f ]

def NFactorizationPropertiesFrom (m : Nat) (A B : Type) (f : A → B) (t : Factorizations A B f) : Type
  ≔ Product (NConnectedMapFrom m A (t .fst) (t .snd .fst)) (TruncatedMap m (t .fst) B (t .snd .snd .fst))

def MinusTwoFactorizationProperties (A B : Type) (f : A → B) (t : Factorizations A B f) : Type
  ≔ Product (MinusTwoConnectedMap A (t .fst) (t .snd .fst)) (BookIsEquiv (t .fst) B (t .snd .snd .fst))

def minus_two_factorization_regroup (A B : Type) (f : A → B)
  : Equiv (MinusTwoImageFactorizations A B f) (Σ (Factorizations A B f) (MinusTwoFactorizationProperties A B f))
  ≔ quasi_inverse_equiv (MinusTwoImageFactorizations A B f) (Σ (Factorizations A B f) (MinusTwoFactorizationProperties A B f))
      (t ↦ ((t .fst, (t .snd .fst, (t .snd .snd .fst, t .snd .snd .snd .fst))), t .snd .snd .snd .snd))
      (t ↦ (t .fst .fst, (t .fst .snd .fst, (t .fst .snd .snd .fst, (t .fst .snd .snd .snd, t .snd)))))
      (t ↦ refl t) (t ↦ refl t)

def minus_two_properties_equiv (A B : Type) (f : A → B) (t : Factorizations A B f)
  : Equiv (MinusTwoFactorizationProperties A B f t) (NFactorizationPropertiesFrom zero. A B f t)
  ≔ family_equiv (MinusTwoConnectedMap A (t .fst) (t .snd .fst)) (_ ↦ BookIsEquiv (t .fst) B (t .snd .snd .fst))
      (_ ↦ TruncatedMap zero. (t .fst) B (t .snd .snd .fst))
      (_ ↦ canonical_inverse_equiv (TruncatedMap zero. (t .fst) B (t .snd .snd .fst)) (BookIsEquiv (t .fst) B (t .snd .snd .fst))
        (minus_two_truncated_map_equiv (t .fst) B (t .snd .snd .fst)))

{` thm:n-im-univ-prop at n = -2 in the Σ_{(C,g,h,r):Fact(f)} form. `}
def minus_two_image_book_universal_property (A B : Type) (f : A → B)
  : BookIsContr (Σ (Factorizations A B f) (NFactorizationPropertiesFrom zero. A B f))
  ≔ book_contractibility_equiv (MinusTwoImageFactorizations A B f)
      (Σ (Factorizations A B f) (NFactorizationPropertiesFrom zero. A B f))
      (compose_equiv (MinusTwoImageFactorizations A B f) (Σ (Factorizations A B f) (MinusTwoFactorizationProperties A B f))
        (Σ (Factorizations A B f) (NFactorizationPropertiesFrom zero. A B f))
        (minus_two_factorization_regroup A B f)
        (family_equiv (Factorizations A B f) (MinusTwoFactorizationProperties A B f)
          (NFactorizationPropertiesFrom zero. A B f) (minus_two_properties_equiv A B f)))
      .map (minus_two_image_universal_property A B f)

{` thm:n-im-univ-prop for every n >= -2 (n = m - 2). `}
def n_image_universal_property_all (m : Nat) (A B : Type) (f : A → B)
  : BookIsContr (Σ (Factorizations A B f) (NFactorizationPropertiesFrom m A B f))
  ≔ match m [
  | zero. ↦ minus_two_image_book_universal_property A B f
  | suc. k ↦ n_image_book_universal_property k A B f ]

{` (e) thm:image-Z-to-Cm (circle.tex:3386-3419), the
   printed step "to show that q is 0-connected, it suffices to consider the
   fiber at the standard m-cycle".  Cyc_m is connected and connectedness of
   a fiber is a proposition, so the connectedness of q⁻¹(pt_m), obtained
   from φ/ψ (quotient_fiber_connected, module 272), transports to every
   fiber.  Module 143 proves the same fact by a different route. `}
def quotient_connected_fibers_from_standard (n : Nat)
  : ConnectedFibers (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n)
  ≔ let D ≔ CycleComponent zero. in let Cm ≔ CycleComponent (suc. n) in
    let q ≔ infinite_quotient_cycle n in
    let pt ≔ principal_component_point (suc. n) in
    w ↦ mere_rec (Id Cm pt w) (Connected (BookFiber D Cm q w)) (connected_prop (BookFiber D Cm q w))
      (r ↦ transport Cm (v ↦ Connected (BookFiber D Cm q v)) pt w r (quotient_fiber_connected n))
      (principal_cycle_components_connected (suc. n) .snd pt w)

def quotient_zero_connected_from_standard (n : Nat)
  : ZeroConnectedMap (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n)
  ≔ connected_fibers_zero_map (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n)
      (quotient_connected_fibers_from_standard n)

def quotient_n_connected_from_standard (n : Nat)
  : NConnectedMap (suc. zero.) (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n)
  ≔ equiv_inverse_map (NConnectedMap (suc. zero.) (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n))
      (ZeroConnectedMap (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n))
      (zero_connected_map_compare (CycleComponent zero.) (CycleComponent (suc. n)) (infinite_quotient_cycle n))
      (quotient_zero_connected_from_standard n)

{` thm:image-Z-to-Cm with the printed proof of 0-connectedness. `}
def infinite_quotient_factorization_via_standard_fiber (n : Nat)
  : ZeroImageFactorizations (CycleComponent zero.) SetTypes (infinite_quotient_set n)
  ≔ (CycleComponent (suc. n), (infinite_quotient_cycle n, (cycle_component_set (suc. n),
      (quotient_set_triangle n, (quotient_zero_connected_from_standard n, cycle_component_set_covering (suc. n))))))

{` (b) The unlabeled exercise after xca:factorial (circle.tex:2590) allows
   0 <= k <= n, but binom(n,k)·(k-1)! is only correct for k >= 2
   (k_cycle_permutations_cardinality, module 244).  The book's k-cycle
   (a_1 ... a_k) for every k : Nat: pairwise distinct entries a : Z/k → A
   with σ(a_i) = a_{i+1}, σ(a_k) = a_1, fixing every other element.  Z/k is
   Remainder k with the modular successor; for k = 0 it is empty and the
   successor condition is vacuous.  For k = j+2 this is KCycleEnumeration
   (module 243) judgmentally. `}
def remainder_successor (k : Nat) : Remainder k → Remainder k
  ≔ match k [ zero. ↦ r ↦ r | suc. n ↦ modular_successor n ]

def BookKCycleEnumeration (A : Type) (k : Nat) (σ : Equiv A A) : Type
  ≔ Σ (Remainder k → A) (a ↦ Product (PathReflecting (Remainder k) A a)
      (Product ((i : Remainder k) → Id A (σ .map (a i)) (a (remainder_successor k i)))
        ((x : A) → ((i : Remainder k) → Not (Id A x (a i))) → Id A (σ .map x) x)))

def IsBookKCycle (A : Type) (k : Nat) (σ : Equiv A A) : Type ≔ Mere (BookKCycleEnumeration A k σ)
def BookKCyclePermutations (A : Type) (k : Nat) : Type ≔ Σ (Equiv A A) (IsBookKCycle A k)

def book_kcycle_enumeration_agrees (A : Type) (j : Nat) (σ : Equiv A A)
  : Id Type (BookKCycleEnumeration A (suc. (suc. j)) σ) (KCycleEnumeration A j σ)
  ≔ refl (KCycleEnumeration A j σ)

def book_kcycle_permutations_agree (A : Type) (j : Nat)
  : Id Type (BookKCyclePermutations A (suc. (suc. j))) (KCyclePermutations A j)
  ≔ refl (KCyclePermutations A j)

def remainder_zero_empty (i : Remainder zero.) : Empty ≔ lt_from_book (i .fst) zero. (i .snd)

{` k = 0: the empty cycle () fixes everything, and the identity is one. `}
def empty_cycle_fixes (A : Type) (σ : Equiv A A) (E : BookKCycleEnumeration A zero. σ) (x : A)
  : Id A (σ .map x) x
  ≔ E .snd .snd .snd x (i _ ↦ remainder_zero_empty i)

def empty_cycle_enumeration (A : Type) : BookKCycleEnumeration A zero. (identity_equiv A)
  ≔ ((i ↦ absurd A (remainder_zero_empty i)),
     ((i i' _ ↦ absurd (Id (Remainder zero.) i i') (remainder_zero_empty i)),
      ((i ↦ match remainder_zero_empty i [ ]), (x _ ↦ refl x))))

def contractible_fin_one_equiv (P : Type) (h : isContr P) : Equiv P (Fin (suc. zero.))
  ≔ compose_equiv P Unit (Fin (suc. zero.))
      (iff_equiv P Unit (contractible_prop P h) unit_prop (_ ↦ star.) (_ ↦ h .center))
      (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv)

{` On a set, the identity is the only 0-cycle. `}
def zero_cycle_permutations_contractible (A : Type) (hA : isSet A) : isContr (BookKCyclePermutations A zero.)
  ≔ let c : BookKCyclePermutations A zero.
      ≔ (identity_equiv A, mere (BookKCycleEnumeration A zero. (identity_equiv A)) (empty_cycle_enumeration A)) in
    (c, u ↦ subtype_equal (Equiv A A) (IsBookKCycle A zero.) (σ ↦ mere_isprop (BookKCycleEnumeration A zero. σ)) u c
      (equiv_path A A (u .fst) (identity_equiv A)
        (funext A (_ ↦ A) (u .fst .map) (identity A)
          (x ↦ mere_rec (BookKCycleEnumeration A zero. (u .fst)) (Id A (u .fst .map x) x) (hA (u .fst .map x) x)
            (E ↦ empty_cycle_fixes A (u .fst) E x) (u .snd)))))

def zero_cycle_permutations_finite (A : Type) (ha : IsFinite A) : IsFinite (BookKCyclePermutations A zero.)
  ≔ finite_from_equiv (BookKCyclePermutations A zero.) (suc. zero.)
      (contractible_fin_one_equiv (BookKCyclePermutations A zero.)
        (zero_cycle_permutations_contractible A (finite_sethood A ha)))

{` The exercise at k = 0: exactly one 0-cycle permutation, for every n.
   (The printed binom(n,0)·(0-1)! involves (-1)!, which is undefined.) `}
def zero_cycle_count (A : Type) (ha : IsFinite A) (hf : IsFinite (BookKCyclePermutations A zero.))
  : Id Nat (cardinality (BookKCyclePermutations A zero.) hf) (suc. zero.)
  ≔ concat Nat (cardinality (BookKCyclePermutations A zero.) hf)
      (cardinality (Fin (suc. zero.)) (fin_is_finite (suc. zero.))) (suc. zero.)
      (cardinality_equiv (BookKCyclePermutations A zero.) (Fin (suc. zero.))
        (contractible_fin_one_equiv (BookKCyclePermutations A zero.)
          (zero_cycle_permutations_contractible A (finite_sethood A ha)))
        hf (fin_is_finite (suc. zero.)))
      (fin_cardinality (suc. zero.))

{` k = 1: Z/1 has one element. `}
def lt_one_zero (m : Nat) : Lt m (suc. zero.) → Id Nat m zero.
  ≔ match m [ zero. ↦ _ ↦ refl (zero. : Nat) | suc. m ↦ h ↦ absurd (Id Nat (suc. m) zero.) h ]

def remainder_one_prop (r s : Remainder (suc. zero.)) : Id (Remainder (suc. zero.)) r s
  ≔ remainder_equal (suc. zero.) r s
      (concat Nat (r .fst) zero. (s .fst) (lt_one_zero (r .fst) (lt_from_book (r .fst) (suc. zero.) (r .snd)))
        (inverse Nat (s .fst) zero. (lt_one_zero (s .fst) (lt_from_book (s .fst) (suc. zero.) (s .snd)))))

def remainder_one_origin : Remainder (suc. zero.) ≔ remainder_at zero. zero. star.

{` Every 1-cycle (a_1) of a decidable set is the identity permutation. `}
def one_cycle_fixes (A : Type) (d : DecidableEquality A) (σ : Equiv A A)
  (E : BookKCycleEnumeration A (suc. zero.) σ) (x : A) : Id A (σ .map x) x
  ≔ let a ≔ E .fst in let o ≔ remainder_one_origin in
    let so ≔ remainder_successor (suc. zero.) o in
    match d x (a o) [
    | inl. p ↦ concat A (σ .map x) (σ .map (a o)) x (refl (σ .map) p)
        (concat A (σ .map (a o)) (a so) x (E .snd .snd .fst o)
          (concat A (a so) (a o) x (refl a (remainder_one_prop so o)) (inverse A x (a o) p)))
    | inr. np ↦ E .snd .snd .snd x (i q ↦ np (concat A x (a i) (a o) q (refl a (remainder_one_prop i o)))) ]

def one_cycle_is_identity (A : Type) (hA : isSet A) (d : DecidableEquality A) (u : BookKCyclePermutations A (suc. zero.))
  : Id (Equiv A A) (u .fst) (identity_equiv A)
  ≔ equiv_path A A (u .fst) (identity_equiv A)
      (funext A (_ ↦ A) (u .fst .map) (identity A)
        (x ↦ mere_rec (BookKCycleEnumeration A (suc. zero.) (u .fst)) (Id A (u .fst .map x) x) (hA (u .fst .map x) x)
          (E ↦ one_cycle_fixes A d (u .fst) E x) (u .snd)))

{` Conversely (a_0) is a 1-cycle for every a_0 : A. `}
def one_cycle_at (A : Type) (a0 : A) : BookKCycleEnumeration A (suc. zero.) (identity_equiv A)
  ≔ ((_ ↦ a0), ((i i' _ ↦ remainder_one_prop i i'), ((_ ↦ refl a0), (x _ ↦ refl x))))

def one_cycle_permutations_prop (A : Type) (hA : isSet A) (d : DecidableEquality A)
  : isProp (BookKCyclePermutations A (suc. zero.))
  ≔ u v ↦ subtype_equal (Equiv A A) (IsBookKCycle A (suc. zero.))
      (σ ↦ mere_isprop (BookKCycleEnumeration A (suc. zero.) σ)) u v
      (concat (Equiv A A) (u .fst) (identity_equiv A) (v .fst) (one_cycle_is_identity A hA d u)
        (inverse (Equiv A A) (v .fst) (identity_equiv A) (one_cycle_is_identity A hA d v)))

{` A decidable set has a 1-cycle permutation iff it is nonempty. `}
def one_cycle_permutations_mere_equiv (A : Type) (hA : isSet A) (d : DecidableEquality A)
  : Equiv (BookKCyclePermutations A (suc. zero.)) (Mere A)
  ≔ iff_equiv (BookKCyclePermutations A (suc. zero.)) (Mere A) (one_cycle_permutations_prop A hA d) (mere_isprop A)
      (u ↦ mere_rec (BookKCycleEnumeration A (suc. zero.) (u .fst)) (Mere A) (mere_isprop A)
        (E ↦ mere A (E .fst remainder_one_origin)) (u .snd))
      (m ↦ (identity_equiv A,
        trunc_map native_truncation A (BookKCycleEnumeration A (suc. zero.) (identity_equiv A)) (one_cycle_at A) m))

{` On a nonempty decidable set there is exactly one 1-cycle, the identity. `}
def one_cycle_permutations_contractible (A : Type) (hA : isSet A) (d : DecidableEquality A) (m : Mere A)
  : isContr (BookKCyclePermutations A (suc. zero.))
  ≔ let c ≔ equiv_inverse_map (BookKCyclePermutations A (suc. zero.)) (Mere A)
      (one_cycle_permutations_mere_equiv A hA d) m in
    (c, u ↦ one_cycle_permutations_prop A hA d u c)

{` The exercise at k = 1 <= n: exactly one 1-cycle permutation. `}
def one_cycle_count_nonempty (A : Type) (ha : IsFinite A) (m : Mere A)
  (hf : IsFinite (BookKCyclePermutations A (suc. zero.)))
  : Id Nat (cardinality (BookKCyclePermutations A (suc. zero.)) hf) (suc. zero.)
  ≔ concat Nat (cardinality (BookKCyclePermutations A (suc. zero.)) hf)
      (cardinality (Fin (suc. zero.)) (fin_is_finite (suc. zero.))) (suc. zero.)
      (cardinality_equiv (BookKCyclePermutations A (suc. zero.)) (Fin (suc. zero.))
        (contractible_fin_one_equiv (BookKCyclePermutations A (suc. zero.))
          (one_cycle_permutations_contractible A (finite_sethood A ha) (finite_decidable_equality A ha) m))
        hf (fin_is_finite (suc. zero.)))
      (fin_cardinality (suc. zero.))

{` Outside the printed range (n = 0 < k = 1) there is none. `}
def one_cycle_count_empty (A : Type) (ha : IsFinite A) (e : Not A)
  (hf : IsFinite (BookKCyclePermutations A (suc. zero.)))
  : Id Nat (cardinality (BookKCyclePermutations A (suc. zero.)) hf) zero.
  ≔ let P ≔ BookKCyclePermutations A (suc. zero.) in
    let hA ≔ finite_sethood A ha in let d ≔ finite_decidable_equality A ha in
    concat Nat (cardinality P hf) (cardinality (Fin zero.) (fin_is_finite zero.)) zero.
      (cardinality_equiv P (Fin zero.)
        (iff_equiv P (Fin zero.) (one_cycle_permutations_prop A hA d) empty_prop
          (u ↦ mere_rec A Empty empty_prop e (one_cycle_permutations_mere_equiv A hA d .map u))
          (z ↦ absurd P z))
        hf (fin_is_finite zero.))
      (fin_cardinality zero.)

def binomial_one (n : Nat) : Id Nat (binomial n (suc. zero.)) n
  ≔ match n [
  | zero. ↦ refl (zero. : Nat)
  | suc. m ↦ match m [
    | zero. ↦ refl (suc. zero. : Nat)
    | suc. l ↦ refl ((x ↦ suc. x) : Nat → Nat) (binomial_one (suc. l)) ] ]

{` The printed formula at k = 1: binom(n,1)·0! = n. `}
def one_cycle_printed_formula (n : Nat) : Id Nat (mul (binomial n (suc. zero.)) (factorial zero.)) n
  ≔ concat Nat (mul (binomial n (suc. zero.)) (factorial zero.)) (binomial n (suc. zero.)) n
      (add_zero_left (binomial n (suc. zero.))) (binomial_one n)

def finite_positive_nonempty (A : Type) (ha : IsFinite A) (n : Nat) (hc : Id Nat (cardinality A ha) (suc. n)) : Mere A
  ≔ mere_rec (Id Type A (Fin (cardinality A ha))) (Mere A) (mere_isprop A)
      (p ↦ mere A (transport Type (X ↦ X) (Fin (cardinality A ha)) A (inverse Type A (Fin (cardinality A ha)) p)
        (transport Nat Fin (suc. n) (cardinality A ha) (inverse Nat (cardinality A ha) (suc. n) hc) (inr. star.))))
      (cardinality_spec A ha)

{` Hence the printed count fails at k = 1 for every n >= 2. `}
def one_cycle_count_formula_fails (A : Type) (ha : IsFinite A) (j : Nat)
  (hc : Id Nat (cardinality A ha) (suc. (suc. j))) (hf : IsFinite (BookKCyclePermutations A (suc. zero.)))
  : Not (Id Nat (cardinality (BookKCyclePermutations A (suc. zero.)) hf)
      (mul (binomial (cardinality A ha) (suc. zero.)) (factorial zero.)))
  ≔ q ↦ let P ≔ BookKCyclePermutations A (suc. zero.) in
    let n ≔ cardinality A ha in
    nat_encode (suc. zero.) (suc. (suc. j))
      (concat Nat (suc. zero.) (cardinality P hf) (suc. (suc. j))
        (inverse Nat (cardinality P hf) (suc. zero.)
          (one_cycle_count_nonempty A ha (finite_positive_nonempty A ha (suc. j) hc) hf))
        (concat Nat (cardinality P hf) (mul (binomial n (suc. zero.)) (factorial zero.)) (suc. (suc. j)) q
          (concat Nat (mul (binomial n (suc. zero.)) (factorial zero.)) n (suc. (suc. j))
            (one_cycle_printed_formula n) hc)))

{` (c) The corollary after prop:ump-cycn-into-groupoids (circle.tex:3601-3606),
   last sentence, "if we restrict to decidable connected
   coverings, equivalently, decidable cycles, these are the usual finite
   cycles with order dividing n".  Here n = suc b; decidable coverings are
   families S : Cyc_n → Set of decidable sets (module 79's CoveringDecidable
   for families), connected ones have connected total space (module 184). `}
def CyclePowerPeriod (b : Nat) (c : Cycles) : Type ≔ PowerPeriod (c .fst .fst .fst) (c .fst .snd) (pos. (suc. b))

def cycle_power_period_prop (b : Nat) (c : Cycles) : isProp (CyclePowerPeriod b c)
  ≔ power_period_prop (c .fst .fst .fst) (c .fst .fst .snd) (c .fst .snd) (pos. (suc. b))

{` Decidable cycles with t^n = id. `}
def DecidableCyclesDividing (b : Nat) : Type
  ≔ Σ Cycles (c ↦ Product (CyclePowerPeriod b c) (DecidableEquality (c .fst .fst .fst)))

{` Over the connected Cyc_n, decidability of all fibers is decidability of the fiber over pt_n. `}
def cyc_family_decidable_at_point (b : Nat) (S : CycleComponent (suc. b) → SetTypes)
  : Equiv ((x : CycleComponent (suc. b)) → DecidableEquality (S x .fst))
      (DecidableEquality (S (principal_component_point (suc. b)) .fst))
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    iff_equiv ((x : C) → DecidableEquality (S x .fst)) (DecidableEquality (S pt .fst))
      (pi_prop C (x ↦ DecidableEquality (S x .fst)) (x ↦ decidable_equality_prop (S x .fst) (S x .snd)))
      (decidable_equality_prop (S pt .fst) (S pt .snd))
      (h ↦ h pt)
      (d x ↦ mere_rec (Id C pt x) (DecidableEquality (S x .fst)) (decidable_equality_prop (S x .fst) (S x .snd))
        (r ↦ transport C (y ↦ DecidableEquality (S y .fst)) pt x r d)
        (principal_cycle_components_connected (suc. b) .snd pt x))

{` "decidable connected coverings, equivalently, decidable cycles": the
   equivalence of module 184 (S ↦ (S(pt_n), transport along σ_n)) restricts
   to decidable families and decidable cycles with t^n = id. `}
def cyc_decidable_connected_families_cycles (b : Nat)
  : Equiv (Σ (CycleComponent (suc. b) → SetTypes) (S ↦ Product (Connected (Σ (CycleComponent (suc. b)) (x ↦ S x .fst)))
        ((x : CycleComponent (suc. b)) → DecidableEquality (S x .fst))))
      (DecidableCyclesDividing b)
  ≔ let C ≔ CycleComponent (suc. b) in let pt ≔ principal_component_point (suc. b) in
    let Conn ≔ ((S ↦ Connected (Σ C (x ↦ S x .fst))) : (C → SetTypes) → Type) in
    let T0 ≔ Σ (C → SetTypes) (S ↦ Product (Conn S) ((x : C) → DecidableEquality (S x .fst))) in
    let T1 ≔ Σ (C → SetTypes) (S ↦ Product (Conn S) (DecidableEquality (S pt .fst))) in
    let G ≔ ((d ↦ Product (Cyclic (d .fst .fst) (d .snd .fst)) (DecidableEquality (d .fst .fst)))
      : CycPermutationData b → Type) in
    let T2 ≔ Σ (CycPermutationData b) G in
    compose_equiv T0 T1 (DecidableCyclesDividing b)
      (family_equiv (C → SetTypes) (S ↦ Product (Conn S) ((x : C) → DecidableEquality (S x .fst)))
        (S ↦ Product (Conn S) (DecidableEquality (S pt .fst)))
        (S ↦ family_equiv (Conn S) (_ ↦ (x : C) → DecidableEquality (S x .fst)) (_ ↦ DecidableEquality (S pt .fst))
          (_ ↦ cyc_family_decidable_at_point b S)))
      (compose_equiv T1 T2 (DecidableCyclesDividing b)
        (sigma_equivalences (C → SetTypes) (CycPermutationData b)
          (S ↦ Product (Conn S) (DecidableEquality (S pt .fst))) G
          (native_equivalence (C → SetTypes) (CycPermutationData b) (cyc_set_families_permutations b))
          (S ↦ let e ≔ cyc_family_connected_cyclic b S in
            iff_equiv (Product (Conn S) (DecidableEquality (S pt .fst)))
              (Product (Cyclic (S pt .fst) (cyc_family_monodromy b S)) (DecidableEquality (S pt .fst)))
              (product_prop (Conn S) (DecidableEquality (S pt .fst)) (connected_prop (Σ C (x ↦ S x .fst)))
                (decidable_equality_prop (S pt .fst) (S pt .snd)))
              (product_prop (Cyclic (S pt .fst) (cyc_family_monodromy b S)) (DecidableEquality (S pt .fst))
                (cyclic_prop (S pt .fst) (cyc_family_monodromy b S)) (decidable_equality_prop (S pt .fst) (S pt .snd)))
              (v ↦ (e .map (v .fst), v .snd))
              (v ↦ (equiv_inverse_map (Conn S) (Cyclic (S pt .fst) (cyc_family_monodromy b S)) e (v .fst), v .snd))))
        (quasi_inverse_equiv T2 (DecidableCyclesDividing b)
          (v ↦ (((v .fst .fst, v .fst .snd .fst), v .snd .fst), (v .fst .snd .snd, v .snd .snd)))
          (w ↦ ((w .fst .fst .fst, (w .fst .fst .snd, w .snd .fst)), (w .fst .snd, w .snd .snd)))
          (v ↦ refl v) (w ↦ refl w)))

{` A decidable cycle with t^n = id is finite: its least positive period
   exists by decidability, and the carrier is enumerated by it (module 74). `}
def decidable_dividing_cycle_finite (b : Nat) (c : Cycles) (pp : CyclePowerPeriod b c)
  (d : DecidableEquality (c .fst .fst .fst)) : IsFinite (c .fst .fst .fst)
  ≔ let minimum ≔ least_number (PositiveCyclePeriod c) (k ↦ CyclePeriods c (pos. (suc. k)) .snd)
      (k ↦ cycle_period_decidable c d (pos. (suc. k))) (mere (Σ Nat (PositiveCyclePeriod c)) (b, pp)) in
    cycle_least_period_finite c (minimum .fst) (minimum .snd)

def dividing_cycle_decidable_finite (b : Nat) (c : Cycles) (pp : CyclePowerPeriod b c)
  : Equiv (DecidableEquality (c .fst .fst .fst)) (IsFinite (c .fst .fst .fst))
  ≔ iff_equiv (DecidableEquality (c .fst .fst .fst)) (IsFinite (c .fst .fst .fst))
      (decidable_equality_prop (c .fst .fst .fst) (c .fst .fst .snd)) (isfinite_prop (c .fst .fst .fst))
      (d ↦ decidable_dividing_cycle_finite b c pp d) (h ↦ finite_decidable_equality (c .fst .fst .fst) h)

{` For the standard cycle of size m+1, t^n = id iff m+1 divides n. `}
def standard_cycle_power_period_divides (b m : Nat)
  : Equiv (CyclePowerPeriod b (finite_standard_cycle m)) (NatDivides (suc. m) (suc. b))
  ≔ compose_equiv (CyclePowerPeriod b (finite_standard_cycle m))
      (OrderDivides (cycle_order (finite_standard_cycle m)) (principal_order (suc. b))) (NatDivides (suc. m) (suc. b))
      (cycle_period_order_divides b (finite_standard_cycle m))
      (principal_divides_equiv (suc. m) (suc. b))

def component_power_period_divides (b m : Nat) (c : Cycles) (h : Mere (Id Cycles c (finite_standard_cycle m)))
  : Equiv (CyclePowerPeriod b c) (NatDivides (suc. m) (suc. b))
  ≔ let std ≔ finite_standard_cycle m in let E ≔ standard_cycle_power_period_divides b m in
    iff_equiv (CyclePowerPeriod b c) (NatDivides (suc. m) (suc. b)) (cycle_power_period_prop b c)
      (nat_divides_prop (suc. m) (suc. b))
      (pc ↦ mere_rec (Id Cycles c std) (NatDivides (suc. m) (suc. b)) (nat_divides_prop (suc. m) (suc. b))
        (r ↦ E .map (transport Cycles (CyclePowerPeriod b) c std r pc)) h)
      (dv ↦ mere_rec (Id Cycles c std) (CyclePowerPeriod b c) (cycle_power_period_prop b c)
        (r ↦ transport Cycles (CyclePowerPeriod b) std c (inverse Cycles c std r)
          (equiv_inverse_map (CyclePowerPeriod b std) (NatDivides (suc. m) (suc. b)) E dv)) h)

{` "these are the usual finite cycles with order dividing n": decidable
   cycles with t^n = id are the sum, over m with m+1 | n, of the components
   of the standard cycles (Z/(m+1), s) (no LPO needed). `}
def decidable_dividing_cycles_classification (b : Nat)
  : Equiv (DecidableCyclesDividing b)
      (Σ Nat (m ↦ Product (NatDivides (suc. m) (suc. b)) (NativeComponent Cycles (finite_standard_cycle m))))
  ≔ let PP ≔ CyclePowerPeriod b in
    let T4 ≔ Σ Cycles (c ↦ Product (PP c) (IsFinite (c .fst .fst .fst))) in
    let T5 ≔ Σ FiniteCycles (c ↦ PP (c .fst)) in
    let T6 ≔ Σ (Σ Nat FiniteCyclesAt) (w ↦ PP (w .snd .fst .fst)) in
    let T7 ≔ Σ Nat (m ↦ Σ (FiniteCyclesAt m) (w ↦ PP (w .fst .fst))) in
    let T8 ≔ Σ Nat (m ↦ Product (NatDivides (suc. m) (suc. b)) (FiniteCyclesAt m)) in
    let T9 ≔ Σ Nat (m ↦ Product (NatDivides (suc. m) (suc. b)) (NativeComponent Cycles (finite_standard_cycle m))) in
    compose_equiv (DecidableCyclesDividing b) T4 T9
      (family_equiv Cycles (c ↦ Product (PP c) (DecidableEquality (c .fst .fst .fst)))
        (c ↦ Product (PP c) (IsFinite (c .fst .fst .fst)))
        (c ↦ iff_equiv (Product (PP c) (DecidableEquality (c .fst .fst .fst))) (Product (PP c) (IsFinite (c .fst .fst .fst)))
          (product_prop (PP c) (DecidableEquality (c .fst .fst .fst)) (cycle_power_period_prop b c)
            (decidable_equality_prop (c .fst .fst .fst) (c .fst .fst .snd)))
          (product_prop (PP c) (IsFinite (c .fst .fst .fst)) (cycle_power_period_prop b c) (isfinite_prop (c .fst .fst .fst)))
          (v ↦ (v .fst, decidable_dividing_cycle_finite b c (v .fst) (v .snd)))
          (v ↦ (v .fst, finite_decidable_equality (c .fst .fst .fst) (v .snd)))))
      (compose_equiv T4 T5 T9
        (quasi_inverse_equiv T4 T5 (v ↦ ((v .fst, v .snd .snd), v .snd .fst)) (w ↦ (w .fst .fst, (w .snd, w .fst .snd)))
          (v ↦ refl v) (w ↦ refl w))
        (compose_equiv T5 T6 T9
          (canonical_inverse_equiv T6 T5 (sigma_pullback_equiv (Σ Nat FiniteCyclesAt) FiniteCycles finite_cycles_at_total
            (c ↦ PP (c .fst))))
          (compose_equiv T6 T7 T9
            (quasi_inverse_equiv T6 T7 (v ↦ (v .fst .fst, (v .fst .snd, v .snd))) (w ↦ ((w .fst, w .snd .fst), w .snd .snd))
              (v ↦ refl v) (w ↦ refl w))
            (compose_equiv T7 T8 T9
              (family_equiv Nat (m ↦ Σ (FiniteCyclesAt m) (w ↦ PP (w .fst .fst)))
                (m ↦ Product (NatDivides (suc. m) (suc. b)) (FiniteCyclesAt m))
                (m ↦ compose_equiv (Σ (FiniteCyclesAt m) (w ↦ PP (w .fst .fst)))
                  (Σ (FiniteCyclesAt m) (_ ↦ NatDivides (suc. m) (suc. b)))
                  (Product (NatDivides (suc. m) (suc. b)) (FiniteCyclesAt m))
                  (family_equiv (FiniteCyclesAt m) (w ↦ PP (w .fst .fst)) (_ ↦ NatDivides (suc. m) (suc. b))
                    (w ↦ component_power_period_divides b m (w .fst .fst) (w .snd)))
                  (quasi_inverse_equiv (Σ (FiniteCyclesAt m) (_ ↦ NatDivides (suc. m) (suc. b)))
                    (Product (NatDivides (suc. m) (suc. b)) (FiniteCyclesAt m))
                    (v ↦ (v .snd, v .fst)) (w ↦ (w .snd, w .fst)) (v ↦ refl v) (w ↦ refl w))))
              (family_equiv Nat (m ↦ Product (NatDivides (suc. m) (suc. b)) (FiniteCyclesAt m))
                (m ↦ Product (NatDivides (suc. m) (suc. b)) (NativeComponent Cycles (finite_standard_cycle m)))
                (m ↦ family_equiv (NatDivides (suc. m) (suc. b)) (_ ↦ FiniteCyclesAt m)
                  (_ ↦ NativeComponent Cycles (finite_standard_cycle m)) (_ ↦ finite_cycles_at_full_component m)))))))

{` The whole sentence: decidable connected coverings over Cyc_n are the
   finite cycles (Z/(m+1), s) with m+1 dividing n, component by component. `}
def cyc_decidable_connected_coverings_classification (b : Nat)
  : Equiv (Σ (CycleComponent (suc. b) → SetTypes) (S ↦ Product (Connected (Σ (CycleComponent (suc. b)) (x ↦ S x .fst)))
        ((x : CycleComponent (suc. b)) → DecidableEquality (S x .fst))))
      (Σ Nat (m ↦ Product (NatDivides (suc. m) (suc. b)) (NativeComponent Cycles (finite_standard_cycle m))))
  ≔ compose_equiv
      (Σ (CycleComponent (suc. b) → SetTypes) (S ↦ Product (Connected (Σ (CycleComponent (suc. b)) (x ↦ S x .fst)))
        ((x : CycleComponent (suc. b)) → DecidableEquality (S x .fst))))
      (DecidableCyclesDividing b)
      (Σ Nat (m ↦ Product (NatDivides (suc. m) (suc. b)) (NativeComponent Cycles (finite_standard_cycle m))))
      (cyc_decidable_connected_families_cycles b) (decidable_dividing_cycles_classification b)
