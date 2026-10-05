export "1522-polynomial-root-bound"
export "1502-restriction-bundle"
export "1506-conjugate-roots"
export "70-classical-principles"
export "46-natural-arithmetic"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms,
   first claim: when the extension (K, i) is algebraic (corrected
   definition of module 1503: every element is a root of a polynomial over
   k with nonzero leading coefficient), every k-algebra endomorphism
   φ : hom_k(K, K) is an equivalence. The proof needs to decide equality
   of elements of K: algebraic_kalg_endo_is_equiv_dec assumes decidable
   equality of K (DecidableEquality, true e.g. for finite fields and
   rational function fields over them), and algebraic_kalg_endo_is_equiv
   assumes excluded middle (which implies it). Excluded middle was
   originally used only for this decision.

   φ is injective (field_hom_injective, module 1520). For surjectivity
   onto β (a proposition, since fibers of an injective map into a set are
   propositions), take a polynomial p with p(β) = 0; φ maps roots of p to
   roots of p (φ fixes i(k)), and p has at most n distinct roots
   (poly_root_bound, module 1522). The general step is
   bounded_injective_surjective: an injective self-map f of a set
   preserving a predicate P that has at most N distinct witnesses reaches
   every witness β. Starting from the empty list, while β is not f of an
   entry of the current duplicate-free list r of witnesses (decided by
   a finite search with decidable equality, fin_fiber_decidable), replace r by (f ∘ r, β), again duplicate-free and one
   longer; the length bound N stops this after at most N + 1 steps
   (structural recursion on the fuel d, invariant N + 1 ≤ fuel_shift d m). `}

{` fuel_shift d m = d + m, with the recursion that makes the search step
   definitional. `}
def fuel_shift (d m : Nat) : Nat ≔ match d [ zero. ↦ m | suc. d ↦ fuel_shift d (suc. m) ]

def fuel_shift_suc (d m : Nat) : Id Nat (fuel_shift d (suc. m)) (suc. (fuel_shift d m))
  ≔ match d [ zero. ↦ refl (suc. m : Nat) | suc. d ↦ fuel_shift_suc d (suc. m) ]

def fuel_shift_ge (d m : Nat) : Le d (fuel_shift d m)
  ≔ match d [
  | zero. ↦ star.
  | suc. d ↦ transport Nat (Le (suc. d)) (suc. (fuel_shift d m)) (fuel_shift d (suc. m))
      (inverse Nat (fuel_shift d (suc. m)) (suc. (fuel_shift d m)) (fuel_shift_suc d m)) (fuel_shift_ge d m) ]

{` The list r followed by β. `}
def root_list_extend (A : Type) (m : Nat) (r : Fin m → A) (β : A) : Fin (suc. m) → A
  ≔ [ inl. j ↦ r j | inr. _ ↦ β ]

def root_list_extend_injective (A : Type) (m : Nat) (r : Fin m → A) (rinj : PathReflecting (Fin m) A r) (β : A)
  (no : Not (Fiber (Fin m) A r β))
  : PathReflecting (Fin (suc. m)) A (root_list_extend A m r β)
  ≔ x y e ↦ match x [
  | inl. j1 ↦ match y [
    | inl. j2 ↦ refl ((j : Fin m) ↦ (inl. j : Sum (Fin m) Unit)) (rinj j1 j2 e)
    | inr. _ ↦ match no (j1, e) [] ]
  | inr. s1 ↦ match y [
    | inl. j2 ↦ match no (j2, inverse A β (r j2) e) []
    | inr. s2 ↦ match s1, s2 [ star., star. ↦ refl (inr. star. : Sum (Fin m) Unit) ] ] ]

{` Whether β is a value of a finite list r, decided with decidable equality. `}
def fin_fiber_absent (A : Type) (m : Nat) (r : Fin (suc. m) → A) (β : A)
  (np : Not (Id A (r (inr. star.)) β)) (nu : Not (Fiber (Fin m) A (j ↦ r (inl. j)) β))
  (x : Fin (suc. m)) (e : Id A (r x) β) : Empty
  ≔ match x [ inl. j ↦ nu (j, e) | inr. u ↦ match u [ star. ↦ np e ] ]

def fin_fiber_decidable (A : Type) (dec : DecidableEquality A) (m : Nat) (r : Fin m → A) (β : A)
  : Decidable (Fiber (Fin m) A r β)
  ≔ match m [
  | zero. ↦ inr. (u ↦ match u .fst [ ])
  | suc. m ↦ match dec (r (inr. star.)) β [
    | inl. p ↦ inl. (inr. star., p)
    | inr. np ↦ match fin_fiber_decidable A dec m (j ↦ r (inl. j)) β [
      | inl. u ↦ inl. (inl. (u .fst), u .snd)
      | inr. nu ↦ inr. (u ↦ fin_fiber_absent A m r β np nu (u .fst) (u .snd)) ] ] ]

{` Excluded middle decides equality in a set. `}
def lem_set_decidable_equality (lem : ExcludedMiddle) (A : Type) (hA : isSet A) : DecidableEquality A
  ≔ x y ↦ lem (Id A x y) (hA x y)

def bounded_injective_search_dec (A : Type) (dec : DecidableEquality A) (P : A → Type) (N : Nat)
  (bound : (m : Nat) (r : Fin m → A) → PathReflecting (Fin m) A r → ((j : Fin m) → P (r j)) → Le m N)
  (f : A → A) (finj : PathReflecting A A f) (fP : (x : A) → P x → P (f x)) (β : A) (hβ : P β)
  (d m : Nat) (hd : Le (suc. N) (fuel_shift d m))
  (r : Fin m → A) (rinj : PathReflecting (Fin m) A r) (rP : (j : Fin m) → P (r j))
  : Fiber A A f β
  ≔ match d [
  | zero. ↦ match lt_irrefl N (le_trans (suc. N) m N hd (bound m r rinj rP)) []
  | suc. d ↦
    let fr : Fin m → A ≔ j ↦ f (r j) in
    let frinj : PathReflecting (Fin m) A fr ≔ j1 j2 e ↦ rinj j1 j2 (finj (r j1) (r j2) e) in
    match fin_fiber_decidable A dec m fr β [
    | inl. u ↦ (r (u .fst), u .snd)
    | inr. no ↦
      bounded_injective_search_dec A dec P N bound f finj fP β hβ d (suc. m) hd
        (root_list_extend A m fr β) (root_list_extend_injective A m fr frinj β no)
        ([ inl. j ↦ fP (r j) (rP j) | inr. _ ↦ hβ ] : (j : Fin (suc. m)) → P (root_list_extend A m fr β j)) ] ]

{` An injective self-map of a set with decidable equality preserving P,
   where P has at most N distinct witnesses, reaches every witness of P. `}
def bounded_injective_surjective_dec (A : Type) (dec : DecidableEquality A) (P : A → Type) (N : Nat)
  (bound : (m : Nat) (r : Fin m → A) → PathReflecting (Fin m) A r → ((j : Fin m) → P (r j)) → Le m N)
  (f : A → A) (finj : PathReflecting A A f) (fP : (x : A) → P x → P (f x)) (β : A) (hβ : P β)
  : Fiber A A f β
  ≔ bounded_injective_search_dec A dec P N bound f finj fP β hβ (suc. N) zero. (fuel_shift_ge (suc. N) zero.)
      (j ↦ match j []) (j1 j2 e ↦ match j1 []) (j ↦ match j [])

{` The same with excluded middle. `}
def bounded_injective_surjective (lem : ExcludedMiddle) (A : Type) (hA : isSet A) (P : A → Type) (N : Nat)
  (bound : (m : Nat) (r : Fin m → A) → PathReflecting (Fin m) A r → ((j : Fin m) → P (r j)) → Le m N)
  (f : A → A) (finj : PathReflecting A A f) (fP : (x : A) → P x → P (f x)) (β : A) (hβ : P β)
  : Fiber A A f β
  ≔ bounded_injective_surjective_dec A (lem_set_decidable_equality lem A hA) P N bound f finj fP β hβ

{` A k-algebra endomorphism φ fixes i(k). `}
def kalg_endo_fixes (k : Field) (E : FieldExt k) (φ : KAlgHom k E E) (x : k .fst .carrier)
  : Id (ext_carrier k E) (ext_map k E x) (φ .fst .fst .fst (ext_map k E x))
  ≔ refl ((g : RingHom (k .fst) (E .fst .fst)) ↦ g .fst .fst x) (φ .snd)

{` β is in the image of φ once it is a root of a polynomial over k with
   nonzero leading coefficient. `}
def kalg_endo_fiber_from_poly_dec (k : Field) (E : FieldExt k) (dec : DecidableEquality (ext_carrier k E)) (φ : KAlgHom k E E)
  (β : ext_carrier k E) (n : Nat) (a : Fin (suc. n) → k .fst .carrier)
  (lead : Not (Id (k .fst .carrier) (a (inr. star.)) (k .fst .zero)))
  (root : Id (ext_carrier k E) (ext_poly_value k E β n a) (E .fst .fst .zero))
  : Fiber (ext_carrier k E) (ext_carrier k E) (φ .fst .fst .fst) β
  ≔ let K ≔ E .fst in let R ≔ K .fst in let A ≔ R .carrier in
    let ψ ≔ φ .fst .fst .fst in let i ≔ ext_map k E in
    let b : Fin (suc. n) → A ≔ m ↦ i (a m) in
    let leadK : Not (Id A (b (inr. star.)) (R .zero))
      ≔ e ↦ lead (field_hom_injective k K (E .snd) (a (inr. star.)) (k .fst .zero)
              (concat A (i (a (inr. star.))) (R .zero) (i (k .fst .zero)) e
                (inverse A (i (k .fst .zero)) (R .zero) (ext_map_zero k E)))) in
    bounded_injective_surjective_dec A dec (x ↦ Id A (poly_value R x n b) (R .zero)) n
      (m r rinj rP ↦ poly_root_bound K n b leadK m r rinj rP)
      ψ (field_hom_injective K K (φ .fst))
      (x px ↦
        calc
          poly_value R (ψ x) n b = poly_value R (ψ x) n (m ↦ ψ (b m))
            by poly_value_coefficients R (ψ x) n b (m ↦ ψ (b m)) (m ↦ kalg_endo_fixes k E φ (a m))
          = ψ (poly_value R x n b)
            by inverse A (ψ (poly_value R x n b)) (poly_value R (ψ x) n (m ↦ ψ (b m))) (ring_hom_poly_value R R (φ .fst) x n b)
          = ψ (R .zero) by refl ψ px
          = R .zero by abstract_hom_preserves_unit (ring_additive_group R) (ring_additive_group R) ψ (φ .fst .fst .snd) ∎)
      β root

{` rem:algebraic-endomorphisms-are-automorphisms, first claim: for an
   algebraic extension (K, i) every k-algebra endomorphism of K is an
   equivalence (assuming decidable equality of K). `}
def algebraic_kalg_endo_is_equiv_dec (k : Field) (E : FieldExt k) (dec : DecidableEquality (ext_carrier k E))
  (h : IsAlgebraicExtension k E) (φ : KAlgHom k E E)
  : isEquiv (ext_carrier k E) (ext_carrier k E) (φ .fst .fst .fst)
  ≔ let A ≔ ext_carrier k E in let ψ ≔ φ .fst .fst .fst in
    let ψinj ≔ field_hom_injective (E .fst) (E .fst) (φ .fst) in
    let surj : (β : A) → Fiber A A ψ β
      ≔ β ↦ mere_rec (Σ Nat (n ↦ Σ (Fin (suc. n) → k .fst .carrier) (a ↦
                Product (Not (Id (k .fst .carrier) (a (inr. star.)) (k .fst .zero)))
                  (Id A (ext_poly_value k E β n a) (E .fst .fst .zero)))))
              (Fiber A A ψ β) (fiber_prop_of_injective A A (ring_set (E .fst .fst)) ψ ψinj β)
              (w ↦ kalg_endo_fiber_from_poly_dec k E dec φ β (w .fst) (w .snd .fst) (w .snd .snd .fst) (w .snd .snd .snd))
              (h β) in
    equiv_of_injective_section A A (ring_set (E .fst .fst)) ψ ψinj (β ↦ surj β .fst) (β ↦ surj β .snd) .equiv

{` The same assuming excluded middle. `}
def algebraic_kalg_endo_is_equiv (lem : ExcludedMiddle) (k : Field) (E : FieldExt k) (h : IsAlgebraicExtension k E)
  (φ : KAlgHom k E E)
  : isEquiv (ext_carrier k E) (ext_carrier k E) (φ .fst .fst .fst)
  ≔ algebraic_kalg_endo_is_equiv_dec k E (lem_set_decidable_equality lem (ext_carrier k E) (ring_set (E .fst .fst))) h φ

{` Litmus: the identity extension (K, id) is algebraic (module 1503), so its
   k-endomorphisms are equivalences. `}
def identity_extension_endo_is_equiv (lem : ExcludedMiddle) (K : Field) (φ : KAlgHom K (identity_extension K) (identity_extension K))
  : isEquiv (K .fst .carrier) (K .fst .carrier) (φ .fst .fst .fst)
  ≔ algebraic_kalg_endo_is_equiv lem K (identity_extension K) (identity_extension_algebraic K) φ
