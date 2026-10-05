export "452-sign-two-loops"

{` Chapter 4, sec:sign-homomorphism: def:mu_E, the homomorphism
   μ_E : Hom(Σ_2^E, Σ_2), and the exercise after it (group.tex:1570): under
   function extensionality USym μ_E sends s : E → {±1} to the product of its
   values. BΣ_2^E is E → BΣ_2 pointed at the constant family (power_group of
   module 407). `}

def power_sigma_two (E : Type) (hE : IsFinite E) : Group ≔ power_group E hE sign_sigma_two

{` For E nonempty: Bμ_E(P) ≔ (Π_{e:E} P(e))/∼, pointed by the identification
   Fin 2 ≃ (E → Fin 2)/∼ sending 0 (= +1) to the class of the constant section
   at 0 (the "all +1" function); its inverse is the parity of the number of
   points where a section takes the value 1. `}
def sign_mu_base_section (E : Type) : LocalSections E (_ ↦ shape sign_sigma_two) ≔ _ ↦ inr. star.

def sign_mu_point_equiv (E : Type) (hE : IsFinite E) (ne : Mere E)
  : Equiv (Fin two) (ParityQuotient E hE (_ ↦ shape sign_sigma_two))
  ≔ compose_equiv (Fin two) Bool (ParityQuotient E hE (_ ↦ shape sign_sigma_two)) fin_two_parity_equiv
      (canonical_inverse_equiv (ParityQuotient E hE (_ ↦ shape sign_sigma_two)) Bool
        (parity_quotient_equiv E hE (_ ↦ shape sign_sigma_two) (sign_mu_base_section E) ne))

def sign_mu_point (E : Type) (hE : IsFinite E) (ne : Mere E)
  : Id (BookFiniteSetsAt two) (shape sign_sigma_two) (parity_quotient_bsigma_two E hE (_ ↦ shape sign_sigma_two) ne)
  ≔ component_path SetTypes (Fin two, fin_set two) (shape sign_sigma_two)
      (parity_quotient_bsigma_two E hE (_ ↦ shape sign_sigma_two) ne)
      (set_types_path (Fin two, fin_set two) (ParityQuotient E hE (_ ↦ shape sign_sigma_two), parity_quotient_set E hE (_ ↦ shape sign_sigma_two))
        (sign_mu_point_equiv E hE ne))

{` The pointing sends 0 = +1 to the class of the all-(+1) section. `}
def sign_mu_point_zero (E : Type) (hE : IsFinite E) (ne : Mere E)
  : Id (ParityQuotient E hE (_ ↦ shape sign_sigma_two)) (sign_mu_point_equiv E hE ne .map (inr. star.))
      (parity_class E hE (_ ↦ shape sign_sigma_two) (sign_mu_base_section E))
  ≔ let Q ≔ ParityQuotient E hE (_ ↦ shape sign_sigma_two) in
    let phi ≔ parity_quotient_equiv E hE (_ ↦ shape sign_sigma_two) (sign_mu_base_section E) ne in
    equiv_injective_path Q Bool phi (sign_mu_point_equiv E hE ne .map (inr. star.))
      (parity_class E hE (_ ↦ shape sign_sigma_two) (sign_mu_base_section E))
      (concat Bool (phi .map (equiv_inverse_map Q Bool phi false.)) false.
        (parity_odd E hE (_ ↦ shape sign_sigma_two) (sign_mu_base_section E) (sign_mu_base_section E))
        (equiv_counit Q Bool phi false.)
        (inverse Bool (parity_odd E hE (_ ↦ shape sign_sigma_two) (sign_mu_base_section E) (sign_mu_base_section E)) false.
          (parity_odd_refl E hE (_ ↦ shape sign_sigma_two) (sign_mu_base_section E))))

{` def:mu_E, given a decision whether E is nonempty: the quotient construction
   for E nonempty, and the constant map (with refl pointing) for E empty. `}
def sign_mu_pointed (E : Type) (hE : IsFinite E) (d : Decidable (Mere E))
  : BookPointedMap (BG (power_sigma_two E hE)) (BG sign_sigma_two)
  ≔ match d [
  | inl. ne ↦ (P ↦ parity_quotient_bsigma_two E hE P ne, sign_mu_point E hE ne)
  | inr. _ ↦ (_ ↦ shape sign_sigma_two, refl (shape sign_sigma_two)) ]

{` def:mu_E. Finite sets have decidable inhabitedness (module 36). `}
def sign_mu (E : Type) (hE : IsFinite E) : GroupHom (power_sigma_two E hE) sign_sigma_two
  ≔ mkhom (power_sigma_two E hE) sign_sigma_two (sign_mu_pointed E hE (finite_inhabited_decidable E hE))

def sign_mu_classifying (E : Type) (hE : IsFinite E) : (E → BookFiniteSetsAt two) → BookFiniteSetsAt two
  ≔ hom_function (power_sigma_two E hE) sign_sigma_two (sign_mu E hE)

{` For E empty, BΣ_2^E is contractible (Σ_2^E is trivial) and the homomorphism
   out of it is unique; μ_E is that homomorphism. `}
def power_sigma_two_empty_contractible (E : Type) (hE : IsFinite E) (no : Not (Mere E))
  : BookIsContr (BG (power_sigma_two E hE) .carrier)
  ≔ (_ ↦ shape sign_sigma_two,
      P ↦ funext E (_ ↦ BookFiniteSetsAt two) (_ ↦ shape sign_sigma_two) P
        (e ↦ absurd (Id (BookFiniteSetsAt two) (shape sign_sigma_two) (P e)) (no (mere E e))))

def sign_mu_empty_unique (E : Type) (hE : IsFinite E) (no : Not (Mere E))
  : BookIsContr (GroupHom (power_sigma_two E hE) sign_sigma_two)
  ≔ book_contractibility_equiv (BookPointedMap (BG (power_sigma_two E hE)) (BG sign_sigma_two)) (GroupHom (power_sigma_two E hE) sign_sigma_two)
      (canonical_inverse_equiv (GroupHom (power_sigma_two E hE) sign_sigma_two) (BookPointedMap (BG (power_sigma_two E hE)) (BG sign_sigma_two))
        (group_hom_classifying_equiv (power_sigma_two E hE) sign_sigma_two))
      .map (contractible_domain_pointed_maps (BG (power_sigma_two E hE)) (BG sign_sigma_two)
        (power_sigma_two_empty_contractible E hE no))

{` Transport in the quotient family is induced by transport of representatives. `}
def quotient_family_transport (X : Type) (L : X → Type) (R : (x : X) → EquivalenceRelation (L x)) (x y : X) (p : Id X x y) (a : L x)
  : Id (Quotient (L y) (R y)) (transport X (z ↦ Quotient (L z) (R z)) x y p (quotient_class (L x) (R x) a))
      (quotient_class (L y) (R y) (transport X L x y p a))
  ≔ J X x (y p ↦ Id (Quotient (L y) (R y)) (transport X (z ↦ Quotient (L z) (R z)) x y p (quotient_class (L x) (R x) a))
        (quotient_class (L y) (R y) (transport X L x y p a)))
      (concat (Quotient (L x) (R x)) (transport X (z ↦ Quotient (L z) (R z)) x x (refl x) (quotient_class (L x) (R x) a))
        (quotient_class (L x) (R x) a) (quotient_class (L x) (R x) (transport X L x x (refl x) a))
        (transport_refl X (z ↦ Quotient (L z) (R z)) x (quotient_class (L x) (R x) a))
        (inverse (Quotient (L x) (R x)) (quotient_class (L x) (R x) (transport X L x x (refl x) a)) (quotient_class (L x) (R x) a)
          (refl (quotient_class (L x) (R x)) (transport_refl X L x a))))
      y p

{` Transport of local sections along an identification of families is pointwise. `}
def local_sections_transport (E : Type) (P P' : E → BookFiniteSetsAt two) (g : Id (E → BookFiniteSetsAt two) P P')
  (f : LocalSections E P) (e : E)
  : Id (P' e .fst .fst) (transport (E → BookFiniteSetsAt two) (LocalSections E) P P' g f e)
      (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (P e) (P' e) (g (refl e)) (f e))
  ≔ J (E → BookFiniteSetsAt two) P
      (P' g ↦ Id (P' e .fst .fst) (transport (E → BookFiniteSetsAt two) (LocalSections E) P P' g f e)
        (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (P e) (P' e) (g (refl e)) (f e)))
      (concat (P e .fst .fst) (transport (E → BookFiniteSetsAt two) (LocalSections E) P P (refl P) f e) (f e)
        (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (P e) (P e) (refl (P e)) (f e))
        (refl ((k ↦ k e) : LocalSections E P → P e .fst .fst) (transport_refl (E → BookFiniteSetsAt two) (LocalSections E) P f))
        (inverse (P e .fst .fst) (transport (BookFiniteSetsAt two) (T ↦ T .fst .fst) (P e) (P e) (refl (P e)) (f e)) (f e)
          (transport_refl (BookFiniteSetsAt two) (T ↦ T .fst .fst) (P e) (f e))))
      P' g

{` The product of the values of s : E → {±1}: −1 to the number of points
   where s is −1. On standard finite sets it is the iterated product, and the
   empty product is +1 (footnote). `}
def sign_product (E : Type) (hE : IsFinite E) (s : E → Sign) : Sign
  ≔ bool_sign (nat_odd (finite_true_count E hE (e ↦ sign_is_minus (s e))))

def sign_is_minus_bool_sign (b : Bool) : Id Bool (sign_is_minus (bool_sign b)) b
  ≔ match b [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

def sign_product_empty (E : Type) (hE : IsFinite E) (no : Not (Mere E)) (s : E → Sign) : Id Sign (sign_product E hE s) plus.
  ≔ refl ((n ↦ bool_sign (nat_odd n)) : Nat → Sign)
      (finite_true_count_false E hE (e ↦ sign_is_minus (s e)) (e ↦ absurd (Id Bool (sign_is_minus (s e)) false.) (no (mere E e))))

def sign_product_fin_zero (hE : IsFinite (Fin zero.)) (s : Fin zero. → Sign) : Id Sign (sign_product (Fin zero.) hE s) plus.
  ≔ sign_product_empty (Fin zero.) hE (mere_rec (Fin zero.) Empty empty_prop (x ↦ x)) s

def sign_product_fin_succ (n : Nat) (hE : IsFinite (Fin (suc. n))) (hE' : IsFinite (Fin n)) (s : Fin (suc. n) → Sign)
  : Id Sign (sign_product (Fin (suc. n)) hE s) (sign_mul (sign_product (Fin n) hE' (a ↦ s (inl. a))) (s (inr. star.)))
  ≔ let b : Fin (suc. n) → Bool ≔ e ↦ sign_is_minus (s e) in
    calc sign_product (Fin (suc. n)) hE s
      = bool_sign (nat_odd (true_count (suc. n) b)) by refl ((m ↦ bool_sign (nat_odd m)) : Nat → Sign) (finite_true_count_fin (suc. n) hE b)
      = bool_sign (bool_xor (nat_odd (true_count n (a ↦ b (inl. a)))) (b (inr. star.)))
        by refl bool_sign (nat_odd_true_count_step n b)
      = sign_mul (bool_sign (nat_odd (true_count n (a ↦ b (inl. a))))) (bool_sign (b (inr. star.)))
        by bool_sign_xor (nat_odd (true_count n (a ↦ b (inl. a)))) (b (inr. star.))
      = sign_mul (sign_product (Fin n) hE' (a ↦ s (inl. a))) (s (inr. star.))
        by refl sign_mul
          (refl ((m ↦ bool_sign (nat_odd m)) : Nat → Sign)
            (inverse Nat (finite_true_count (Fin n) hE' (a ↦ b (inl. a))) (true_count n (a ↦ b (inl. a)))
              (finite_true_count_fin n hE' (a ↦ b (inl. a)))))
          (sign_bool_roundtrip (s (inr. star.))) ∎

{` The values of a symmetry of Σ_2^E at the points of E (happly, the map of
   power_group_usym_equiv). `}
def power_sigma_two_component (E : Type) (hE : IsFinite E) (g : USym (power_sigma_two E hE)) (e : E) : USym sign_sigma_two
  ≔ g (refl e)

def two_differ_bool_false (h : TwoElement Bool) (b : Bool) : Id Bool (two_differ Bool h false. b) b
  ≔ match b [
  | false. ↦ two_differ_refl Bool h false.
  | true. ↦ two_differ_ne Bool h false. true. (q ↦ bool_encode false. true. q) ]

{` The class of f1 differs from the class of f0 exactly when f1 and f0 are
   in odd parity (any two-element witness for the quotient). `}
def parity_class_differ (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (ne : Mere E)
  (h : TwoElement (ParityQuotient E hE P)) (f0 f1 : LocalSections E P)
  : Id Bool (two_differ (ParityQuotient E hE P) h (parity_class E hE P f0) (parity_class E hE P f1)) (parity_odd E hE P f1 f0)
  ≔ let Q ≔ ParityQuotient E hE P in
    let phi ≔ parity_quotient_equiv E hE P f0 ne in
    calc two_differ Q h (parity_class E hE P f0) (parity_class E hE P f1)
      = two_differ Bool bool_two_element (phi .map (parity_class E hE P f0)) (phi .map (parity_class E hE P f1))
        by inverse Bool (two_differ Bool bool_two_element (phi .map (parity_class E hE P f0)) (phi .map (parity_class E hE P f1)))
          (two_differ Q h (parity_class E hE P f0) (parity_class E hE P f1))
          (two_differ_equiv Q Bool h bool_two_element phi (parity_class E hE P f0) (parity_class E hE P f1))
      = two_differ Bool bool_two_element false. (parity_odd E hE P f1 f0)
        by refl ((b ↦ two_differ Bool bool_two_element b (parity_odd E hE P f1 f0)) : Bool → Bool)
          (parity_odd_refl E hE P f0)
      = parity_odd E hE P f1 f0 by two_differ_bool_false bool_two_element (parity_odd E hE P f1 f0) ∎

{` Whether the loop Bμ_E(g) swaps: the parity of the transported all-(+1) section. `}
def sign_mu_moves_ne (E : Type) (hE : IsFinite E) (ne : Mere E) (g : USym (power_sigma_two E hE))
  : Id Bool (two_loop_moves (parity_quotient_bsigma_two E hE (_ ↦ shape sign_sigma_two) ne)
        (refl ((P ↦ parity_quotient_bsigma_two E hE P ne) : (E → BookFiniteSetsAt two) → BookFiniteSetsAt two) g))
      (parity_odd E hE (_ ↦ shape sign_sigma_two)
        (transport (E → BookFiniteSetsAt two) (LocalSections E) (_ ↦ shape sign_sigma_two) (_ ↦ shape sign_sigma_two) g (sign_mu_base_section E))
        (sign_mu_base_section E))
  ≔ let B2 ≔ BookFiniteSetsAt two in
    let c : E → B2 ≔ _ ↦ shape sign_sigma_two in
    let Bmu : (E → B2) → B2 ≔ P ↦ parity_quotient_bsigma_two E hE P ne in
    let Q ≔ ParityQuotient E hE c in
    let hQ ≔ two_set_two_element (Bmu c) in
    let f0 ≔ sign_mu_base_section E in
    let f1 ≔ transport (E → B2) (LocalSections E) c c g f0 in
    let z0 ≔ parity_class E hE c f0 in
    let tz ≔ bsigma_two_transport (Bmu c) (Bmu c) (refl Bmu g) in
    calc two_loop_moves (Bmu c) (refl Bmu g)
      = two_differ Q hQ z0 (tz .map z0) by two_moves_value Q hQ tz z0
      = two_differ Q hQ z0 (parity_class E hE c f1)
        by refl (two_differ Q hQ z0) (quotient_family_transport (E → B2) (LocalSections E) (parity_relation E hE) c c g f0)
      = parity_odd E hE c f1 f0 by parity_class_differ E hE c ne hQ f0 f1 ∎

{` At each point e, the transported base section differs from it exactly when
   the component g(e) of g is the swap. `}
def sign_mu_component_differ (E : Type) (hE : IsFinite E) (g : USym (power_sigma_two E hE)) (e : E)
  : Id Bool (parity_differ E (_ ↦ shape sign_sigma_two)
        (transport (E → BookFiniteSetsAt two) (LocalSections E) (_ ↦ shape sign_sigma_two) (_ ↦ shape sign_sigma_two) g (sign_mu_base_section E))
        (sign_mu_base_section E) e)
      (sign_is_minus (sigma_two_sign (power_sigma_two_component E hE g e)))
  ≔ let B2 ≔ BookFiniteSetsAt two in
    let c : E → B2 ≔ _ ↦ shape sign_sigma_two in
    let ge ≔ power_sigma_two_component E hE g e in
    let f0 ≔ sign_mu_base_section E in
    let f1 ≔ transport (E → B2) (LocalSections E) c c g f0 in
    let A ≔ Fin two in let hA ≔ two_set_two_element (shape sign_sigma_two) in
    calc two_differ A hA (f1 e) (f0 e)
      = two_differ A hA (f0 e) (f1 e) by two_differ_symm A hA (f1 e) (f0 e)
      = two_differ A hA (f0 e) (transport B2 (T ↦ T .fst .fst) (shape sign_sigma_two) (shape sign_sigma_two) ge (f0 e))
        by refl (two_differ A hA (f0 e)) (local_sections_transport E c c g f0 e)
      = two_loop_moves (shape sign_sigma_two) ge
        by inverse Bool (two_loop_moves (shape sign_sigma_two) ge)
          (two_differ A hA (f0 e) (transport B2 (T ↦ T .fst .fst) (shape sign_sigma_two) (shape sign_sigma_two) ge (f0 e)))
          (two_moves_value A hA (bsigma_two_transport (shape sign_sigma_two) (shape sign_sigma_two) ge) (f0 e))
      = sign_is_minus (sigma_two_sign ge)
        by inverse Bool (sign_is_minus (bool_sign (two_loop_moves (shape sign_sigma_two) ge)))
          (two_loop_moves (shape sign_sigma_two) ge) (sign_is_minus_bool_sign (two_loop_moves (shape sign_sigma_two) ge)) ∎

{` The exercise for a given decision whether E is nonempty. `}
def sign_mu_usym_product_dec (E : Type) (hE : IsFinite E) (d : Decidable (Mere E)) (g : USym (power_sigma_two E hE))
  : Id Sign (sigma_two_sign (loops_map (BG (power_sigma_two E hE)) (BG sign_sigma_two) (sign_mu_pointed E hE d) g))
      (sign_product E hE (e ↦ sigma_two_sign (power_sigma_two_component E hE g e)))
  ≔ let B2 ≔ BookFiniteSetsAt two in
    let c : E → B2 ≔ _ ↦ shape sign_sigma_two in
    let ge ≔ power_sigma_two_component E hE g in
    match d [
    | inl. ne ↦
        let Bmu : (E → B2) → B2 ≔ P ↦ parity_quotient_bsigma_two E hE P ne in
        let f0 ≔ sign_mu_base_section E in
        let f1 ≔ transport (E → B2) (LocalSections E) c c g f0 in
        calc sigma_two_sign (loops_map (BG (power_sigma_two E hE)) (BG sign_sigma_two) (sign_mu_pointed E hE (inl. ne)) g)
          = two_loop_sign (Bmu c) (refl Bmu g)
            by two_loop_sign_conjugate (shape sign_sigma_two) (Bmu c) (sign_mu_point E hE ne) (refl Bmu g)
          = bool_sign (parity_odd E hE c f1 f0) by refl bool_sign (sign_mu_moves_ne E hE ne g)
          = bool_sign (nat_odd (finite_true_count E hE (parity_differ E c f1 f0)))
            by refl bool_sign (parity_odd_count E hE c f1 f0)
          = sign_product E hE (e ↦ sigma_two_sign (ge e))
            by refl ((b ↦ bool_sign (nat_odd (finite_true_count E hE b))) : (E → Bool) → Sign)
              (funext E (_ ↦ Bool) (parity_differ E c f1 f0) (e ↦ sign_is_minus (sigma_two_sign (ge e)))
                (sign_mu_component_differ E hE g)) ∎
    | inr. no ↦
        calc sigma_two_sign (loops_map (BG (power_sigma_two E hE)) (BG sign_sigma_two) (sign_mu_pointed E hE (inr. no)) g)
          = two_loop_sign (shape sign_sigma_two) (refl ((_ ↦ shape sign_sigma_two) : (E → B2) → B2) g)
            by two_loop_sign_conjugate (shape sign_sigma_two) (shape sign_sigma_two) (refl (shape sign_sigma_two))
              (refl ((_ ↦ shape sign_sigma_two) : (E → B2) → B2) g)
          = plus. by refl bool_sign (two_loop_moves_refl (shape sign_sigma_two))
          = sign_product E hE (e ↦ sigma_two_sign (ge e))
            by inverse Sign (sign_product E hE (e ↦ sigma_two_sign (ge e))) plus.
              (sign_product_empty E hE no (e ↦ sigma_two_sign (ge e))) ∎ ]

{` The exercise (group.tex:1570): USym μ_E maps a symmetry with components
   s(e) ∈ {±1} to the product of the s(e). `}
def sign_mu_usym_product (E : Type) (hE : IsFinite E) (g : USym (power_sigma_two E hE))
  : Id Sign (sigma_two_sign (usym_hom (power_sigma_two E hE) sign_sigma_two (sign_mu E hE) g))
      (sign_product E hE (e ↦ sigma_two_sign (power_sigma_two_component E hE g e)))
  ≔ sign_mu_usym_product_dec E hE (finite_inhabited_decidable E hE) g

{` The identification USym(Σ_2^E) ≃ {±1}^E (function extensionality and the
   footnote identification), and the statement for s : E → {±1}. `}
def power_sigma_two_sign_equiv (E : Type) (hE : IsFinite E) : Equiv (USym (power_sigma_two E hE)) (E → Sign)
  ≔ compose_equiv (USym (power_sigma_two E hE)) (E → USym sign_sigma_two) (E → Sign)
      (power_group_usym_equiv E hE sign_sigma_two)
      (pi_equiv E (_ ↦ USym sign_sigma_two) (_ ↦ Sign) (_ ↦ sigma_two_sign_equiv))

def sign_mu_product (E : Type) (hE : IsFinite E) (s : E → Sign)
  : Id Sign (sigma_two_sign (usym_hom (power_sigma_two E hE) sign_sigma_two (sign_mu E hE)
        (equiv_inverse_map (USym (power_sigma_two E hE)) (E → Sign) (power_sigma_two_sign_equiv E hE) s)))
      (sign_product E hE s)
  ≔ let e ≔ power_sigma_two_sign_equiv E hE in
    let g ≔ equiv_inverse_map (USym (power_sigma_two E hE)) (E → Sign) e s in
    concat Sign (sigma_two_sign (usym_hom (power_sigma_two E hE) sign_sigma_two (sign_mu E hE) g))
      (sign_product E hE (x ↦ sigma_two_sign (power_sigma_two_component E hE g x)))
      (sign_product E hE s)
      (sign_mu_usym_product E hE g)
      (refl ((t ↦ sign_product E hE t) : (E → Sign) → Sign) (equiv_counit (USym (power_sigma_two E hE)) (E → Sign) e s))
