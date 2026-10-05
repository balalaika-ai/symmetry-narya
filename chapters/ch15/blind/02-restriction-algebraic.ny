{` Blind statements for chapter 15 (galois.tex), section "Covering spaces and field extensions":
   the restriction map i^*, the map t, algebraic elements and extensions, finite extensions and degree. `}
export "01-galois-group"
export "../../../src/49-pigeonhole"

{` i^* : K\Fields → k\Fields, (L, j) ↦ (L, j i). `}
def blind_restr (k : Field) (E : BlindFieldExt k) : BlindFieldExt (E .fst) → BlindFieldExt k
  ≔ u ↦ (u .fst, ring_hom_compose (k .fst) (E .fst .fst) (u .fst .fst) (E .snd) (u .snd))

{` lem:field-ext-restriction-set-bundle. i^* is a set bundle (all its fibers are sets). `}
def blind_field_ext_restriction_set_bundle : Type
  ≔ (k : Field) (E : BlindFieldExt k) → IsCovering (BlindFieldExt (E .fst)) (BlindFieldExt k) (blind_restr k E)

{` The fiber of i^* over (K, i), and its point ((K, id_K), (K,i) = (K, id_K i)). `}
def BlindRestrFiber (k : Field) (E : BlindFieldExt k) (y : BlindFieldExt k) : Type
  ≔ BookFiber (BlindFieldExt (E .fst)) (BlindFieldExt k) (blind_restr k E) y

def blind_restr_id_path (k : Field) (E : BlindFieldExt k)
  : Id (BlindFieldExt k) E (blind_restr k E (E .fst, ring_hom_id (E .fst .fst)))
  ≔ refl ((h ↦ (E .fst, h)) : BlindFieldHom k (E .fst) → BlindFieldExt k)
      (ring_hom_ext (k .fst) (E .fst .fst) (E .snd)
        (ring_hom_compose (k .fst) (E .fst .fst) (E .fst .fst) (E .snd) (ring_hom_id (E .fst .fst)))
        (s ↦ refl (E .snd .fst .fst s)))

def blind_restr_fiber_id (k : Field) (E : BlindFieldExt k) : BlindRestrFiber k E E
  ≔ ((E .fst, ring_hom_id (E .fst .fst)), blind_restr_id_path k E)

{` t : USym Gal(K, i) → (i^*)^{-1}(K, i), g ↦ trp g (id_K) (running text before def:algebraic-element). `}
def blind_t (k : Field) (E : BlindFieldExt k) (g : USym (BlindGaloisGroup k E)) : BlindRestrFiber k E E
  ≔ transport (BlindFieldExt k) (BlindRestrFiber k E) E E
      (automorphism_group_usym_equiv (BlindFieldExt k) (blind_field_ext_groupoid k) E .map g)
      (blind_restr_fiber_id k E)

{` ---- defn:algebraic-element ---- `}

def blind_ring_pow (R : AbstractRing) (x : R .carrier) (n : Nat) : R .carrier
  ≔ match n [ zero. ↦ R .one | suc. n ↦ R .mul (blind_ring_pow R x n) x ]

{` Finite sums over Fin n in a ring (Fin (n+1) = Fin n + 1). `}
def blind_fin_sum (R : AbstractRing) (n : Nat) (f : Fin n → R .carrier) : R .carrier
  ≔ match n [ zero. ↦ R .zero | suc. n ↦ R .add (blind_fin_sum R n (s ↦ f (inl. s))) (f (inr. star.)) ]

{` i(a(0)) + i(a(1)) α + ... + i(a(n)) α^n for a : Fin (n+1) → k; the index of s : Fin (n+1) is
   fin_index (a bijection onto {0, ..., n}). `}
def blind_poly_eval (k : Field) (E : BlindFieldExt k) (n : Nat) (a : Fin (suc. n) → k .fst .carrier)
  (α : E .fst .fst .carrier) : E .fst .fst .carrier
  ≔ let K ≔ E .fst .fst in
    blind_fin_sum K (suc. n)
      (s ↦ K .mul (E .snd .fst .fst (a s)) (blind_ring_pow K α (fin_index (suc. n) s)))

{` As printed: α is algebraic if it is merely a root of SOME a : Fin (n+1) → k (no non-vanishing condition). `}
def BlindIsAlgebraicElement (k : Field) (E : BlindFieldExt k) (α : E .fst .fst .carrier) : Type
  ≔ Mere (Σ Nat (n ↦ Σ (Fin (suc. n) → k .fst .carrier) (a ↦
      Id (E .fst .fst .carrier) (blind_poly_eval k E n a α) (E .fst .fst .zero))))

{` As printed the definition is vacuous: a = 0 has every α as a root. Stated (not proved) as a claim. `}
def blind_algebraic_element_as_printed_vacuous : Type
  ≔ (k : Field) (E : BlindFieldExt k) (α : E .fst .fst .carrier) → BlindIsAlgebraicElement k E α

{` Corrected: α is merely a root of a polynomial that is not identically zero. `}
def BlindIsAlgebraicElementCorrected (k : Field) (E : BlindFieldExt k) (α : E .fst .fst .carrier) : Type
  ≔ Mere (Σ Nat (n ↦ Σ (Fin (suc. n) → k .fst .carrier) (a ↦
      Product (Not ((s : Fin (suc. n)) → Id (k .fst .carrier) (a s) (k .fst .zero)))
        (Id (E .fst .fst .carrier) (blind_poly_eval k E n a α) (E .fst .fst .zero)))))

{` ---- defn:algebraic-extension ---- `}
def BlindIsAlgebraicExt (k : Field) (E : BlindFieldExt k) : Type
  ≔ (a : E .fst .fst .carrier) → BlindIsAlgebraicElement k E a

def BlindIsAlgebraicExtCorrected (k : Field) (E : BlindFieldExt k) : Type
  ≔ (a : E .fst .fst .carrier) → BlindIsAlgebraicElementCorrected k E a

{` ---- rem:algebraic-endomorphisms-are-automorphisms ---- `}

{` (1) If (K, i) is algebraic, then t is an equivalence. Literal (with the printed, vacuous notion of
   algebraic this says t is always an equivalence, which fails e.g. for k(x) with the k-endomorphism x ↦ x²). `}
def blind_algebraic_t_equiv : Type
  ≔ (k : Field) (E : BlindFieldExt k) → BlindIsAlgebraicExt k E
    → BookIsEquiv (USym (BlindGaloisGroup k E)) (BlindRestrFiber k E E) (blind_t k E)

def blind_algebraic_t_equiv_corrected : Type
  ≔ (k : Field) (E : BlindFieldExt k) → BlindIsAlgebraicExtCorrected k E
    → BookIsEquiv (USym (BlindGaloisGroup k E)) (BlindRestrFiber k E E) (blind_t k E)

{` (2) The converse is false: some non-algebraic extension has t an equivalence. Literal (refutable:
   with the printed notion every extension is algebraic) and corrected. The book's witness Q ↪ R
   (every Q-endomorphism of R is the identity) is not stated: no reals/rationals as fields are available. `}
def blind_t_equiv_not_algebraic : Type
  ≔ Σ Field (k ↦ Σ (BlindFieldExt k) (E ↦
      Product (BookIsEquiv (USym (BlindGaloisGroup k E)) (BlindRestrFiber k E E) (blind_t k E))
        (Not (BlindIsAlgebraicExt k E))))

def blind_t_equiv_not_algebraic_corrected : Type
  ≔ Σ Field (k ↦ Σ (BlindFieldExt k) (E ↦
      Product (BookIsEquiv (USym (BlindGaloisGroup k E)) (BlindRestrFiber k E E) (blind_t k E))
        (Not (BlindIsAlgebraicExtCorrected k E))))

{` ---- defn:degree-field-extension ---- `}

{` K as a k-vector space via i: a · v ≔ i(a) v. `}
def blind_ext_vector_space (k : Field) (E : BlindFieldExt k) : VectorSpace k
  ≔ let K ≔ E .fst .fst in let i ≔ E .snd .fst .fst in
    (K .carrier, K .zero, K .add, K .neg, K .add_laws, ring_add_comm K,
     a v ↦ K .mul (i a) v,
     v ↦ concat (K .carrier) (K .mul (i (k .fst .one)) v) (K .mul (K .one) v) v
           (refl ((x ↦ K .mul x v) : K .carrier → K .carrier) (E .snd .snd .fst))
           (ring_mul_one_left K v),
     a b v ↦ concat (K .carrier) (K .mul (i (k .fst .mul a b)) v) (K .mul (K .mul (i a) (i b)) v)
               (K .mul (i a) (K .mul (i b) v))
               (refl ((x ↦ K .mul x v) : K .carrier → K .carrier) (E .snd .snd .snd a b))
               (inverse (K .carrier) (K .mul (i a) (K .mul (i b) v)) (K .mul (K .mul (i a) (i b)) v)
                 (ring_mul_assoc K (i a) (i b) v)),
     a b v ↦ concat (K .carrier) (K .mul (i (k .fst .add a b)) v) (K .mul (K .add (i a) (i b)) v)
               (K .add (K .mul (i a) v) (K .mul (i b) v))
               (refl ((x ↦ K .mul x v) : K .carrier → K .carrier) (E .snd .fst .snd a b))
               (ring_rdistr K (i a) (i b) v),
     a v w ↦ ring_ldistr K (i a) v w)

{` (K, i) is finite: K is a finite-dimensional k-vector space (some n with K of dimension n). `}
def BlindIsFiniteExt (k : Field) (E : BlindFieldExt k) : Type
  ≔ Σ Nat (n ↦ HasDimension k n (blind_ext_vector_space k E))

{` The degree [K : k] of a finite extension. `}
def blind_ext_degree (k : Field) (E : BlindFieldExt k) (h : BlindIsFiniteExt k E) : Nat ≔ h .fst
