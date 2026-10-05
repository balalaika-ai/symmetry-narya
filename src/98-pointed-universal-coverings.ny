export "97-representable-components"

{` The book points a map by b0 -> f(a0), whereas native PointedMap uses
   f(a0) -> b0.  The book convention is used throughout this module. `}
def BookPointedMap (A B : Pointed) : Type
  ≔ Σ (A .carrier → B .carrier) (f ↦ Id (B .carrier) (B .point) (f (A .point)))

def book_pointed_to_native (A B : Pointed) (f : BookPointedMap A B) : PointedMap A B
  ≔ (f .fst, inverse (B .carrier) (B .point) (f .fst (A .point)) (f .snd))
def native_pointed_to_book (A B : Pointed) (f : PointedMap A B) : BookPointedMap A B
  ≔ (f .map, inverse (B .carrier) (f .map (A .point)) (B .point) (f .point))

def pointed_map_conventions_equiv (A B : Pointed) : Equiv (BookPointedMap A B) (PointedMap A B)
  ≔ quasi_inverse_equiv (BookPointedMap A B) (PointedMap A B)
      (book_pointed_to_native A B) (native_pointed_to_book A B)
      (f ↦ (refl (f .fst), inverse_inverse (B .carrier) (B .point) (f .fst (A .point)) (f .snd)))
      (f ↦ (refl (f .map), inverse_inverse (B .carrier) (f .map (A .point)) (B .point) (f .point)))

def BookPointedCoverings (B : Pointed) : Type
  ≔ Σ Pointed (A ↦ Σ (BookPointedMap A B) (f ↦ IsCovering (A .carrier) (B .carrier) (f .fst)))

def book_pointed_identity (A : Pointed) : BookPointedMap A A ≔ (identity (A .carrier), refl (A .point))
def book_pointed_constant (A B : Pointed) : BookPointedMap A B ≔ (constant (A .carrier) (B .carrier) (B .point), refl (B .point))

def book_pointed_compose (A B C : Pointed) (f : BookPointedMap A B) (g : BookPointedMap B C) : BookPointedMap A C
  ≔ ((a ↦ g .fst (f .fst a)), concat (C .carrier) (C .point) (g .fst (B .point)) (g .fst (f .fst (A .point)))
      (g .snd) (refl (g .fst) (f .snd)))

def PointedCoverLifts (A B C : Pointed) (f : BookPointedMap A B) (g : BookPointedMap C B) : Type
  ≔ Σ (BookPointedMap A C) (h ↦ Id (BookPointedMap A B) f (book_pointed_compose A C B h g))

{` def:univ-cover, including equality in the full pointed-map type. `}
def IsUniversalPointedCover (A B : Pointed) (f : BookPointedMap A B) : Type
  ≔ (C : Pointed) (g : BookPointedMap C B) → IsCovering (C .carrier) (B .carrier) (g .fst)
      → BookIsContr (PointedCoverLifts A B C f g)

def universal_pointed_cover_prop (A B : Pointed) (f : BookPointedMap A B) : isProp (IsUniversalPointedCover A B f)
  ≔ pi_prop Pointed (C ↦ (g : BookPointedMap C B) → IsCovering (C .carrier) (B .carrier) (g .fst)
      → BookIsContr (PointedCoverLifts A B C f g))
      (C ↦ pi_prop (BookPointedMap C B) (g ↦ IsCovering (C .carrier) (B .carrier) (g .fst)
        → BookIsContr (PointedCoverLifts A B C f g))
        (g ↦ pi_prop (IsCovering (C .carrier) (B .carrier) (g .fst))
          (_ ↦ BookIsContr (PointedCoverLifts A B C f g)) (_ ↦ book_iscontr_isprop (PointedCoverLifts A B C f g))))

def contractible_domain_evaluation (A : Pointed) (Y : Type) (contr : BookIsContr (A .carrier))
  : Equiv (A .carrier → Y) Y
  ≔ quasi_inverse_equiv (A .carrier → Y) Y (f ↦ f (A .point)) (constant (A .carrier) Y)
      (f ↦ funext (A .carrier) (_ ↦ Y) (constant (A .carrier) Y (f (A .point))) f
        (a ↦ refl f (contractible_prop (A .carrier) (native_contraction (A .carrier) contr) (A .point) a)))
      (y ↦ refl y)

def contractible_domain_pointed_maps (A C : Pointed) (contr : BookIsContr (A .carrier))
  : BookIsContr (BookPointedMap A C)
  ≔ book_equivalence (A .carrier → C .carrier) (C .carrier)
      (contractible_domain_evaluation A (C .carrier) contr) .equiv (C .point)

def contractible_map_book_fiber (A B : Type) (f : A → B) (contr_A : BookIsContr A) (contr_B : BookIsContr B) (b : B)
  : BookIsContr (BookFiber A B f b)
  ≔ book_contraction (BookFiber A B f b)
      (sigma_contractible A (a ↦ Id B b (f a)) (native_contraction A contr_A)
        (a ↦ prop_paths_contractible B (contractible_prop B (native_contraction B contr_B)) b (f a)))

def contractible_cover_universal (A B : Pointed) (f : BookPointedMap A B) (contr : BookIsContr (A .carrier))
  : IsUniversalPointedCover A B f
  ≔ C g _ ↦ contractible_map_book_fiber (BookPointedMap A C) (BookPointedMap A B)
      (h ↦ book_pointed_compose A C B h g)
      (contractible_domain_pointed_maps A C contr) (contractible_domain_pointed_maps A B contr) f

def pointed_unit : Pointed ≔ (Unit, star.)

def constant_pointed_unit_cover (B : Pointed) (groupoid : isGroupoid (B .carrier))
  : IsCovering Unit (B .carrier) (book_pointed_constant pointed_unit B .fst)
  ≔ b ↦ sigma_set Unit (_ ↦ Id (B .carrier) b (B .point)) unit_set (_ ↦ groupoid b (B .point))

def book_pointed_identity_triangle (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap A B) f (book_pointed_compose A A B (book_pointed_identity A) f)
  ≔ (refl (f .fst), inverse (Id (B .carrier) (B .point) (f .fst (A .point)))
      (concat (B .carrier) (B .point) (f .fst (A .point)) (f .fst (A .point)) (f .snd) (refl (f .fst (A .point))))
      (f .snd) (concat_p1 (B .carrier) (B .point) (f .fst (A .point)) (f .snd)))

def book_pointed_constant_path (A B : Pointed) (b : B .carrier) (p : Id (B .carrier) (B .point) b)
  : Id (BookPointedMap A B) (book_pointed_constant A B) (constant (A .carrier) (B .carrier) b, p)
  ≔ J (B .carrier) (B .point)
      (b p ↦ Id (BookPointedMap A B) (book_pointed_constant A B) (constant (A .carrier) (B .carrier) b, p))
      (refl (book_pointed_constant A B)) b p

def book_pointed_constant_triangle (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap A B) (book_pointed_constant A B)
      (book_pointed_compose A A B (book_pointed_constant A A) f)
  ≔ concat (BookPointedMap A B) (book_pointed_constant A B)
      (constant (A .carrier) (B .carrier) (f .fst (A .point)), f .snd)
      (book_pointed_compose A A B (book_pointed_constant A A) f)
      (book_pointed_constant_path A B (f .fst (A .point)) (f .snd))
      (refl (constant (A .carrier) (B .carrier) (f .fst (A .point))),
        inverse (Id (B .carrier) (B .point) (f .fst (A .point)))
          (concat (B .carrier) (B .point) (f .fst (A .point)) (f .fst (A .point)) (f .snd) (refl (f .fst (A .point))))
          (f .snd) (concat_p1 (B .carrier) (B .point) (f .fst (A .point)) (f .snd)))

def book_pointed_unit_factor_constant (A B : Pointed) (h : BookPointedMap A pointed_unit)
  : Id (BookPointedMap A B) (book_pointed_compose A pointed_unit B h (book_pointed_constant pointed_unit B))
      (book_pointed_constant A B)
  ≔ (refl (constant (A .carrier) (B .carrier) (B .point)), concat_1p (B .carrier) (B .point) (B .point) (refl (B .point)))

{` For the converse, universality first supplies a factorization through
   the constant unit covering.  The resulting constant self-lift equals
   the identity self-lift by uniqueness in the full pointed lift type. `}
def universal_cover_contractible (A B : Pointed) (groupoid : isGroupoid (B .carrier)) (f : BookPointedMap A B)
  (covering : IsCovering (A .carrier) (B .carrier) (f .fst)) (universal : IsUniversalPointedCover A B f)
  : BookIsContr (A .carrier)
  ≔ let factor ≔ universal pointed_unit (book_pointed_constant pointed_unit B) (constant_pointed_unit_cover B groupoid) .center in
    let null ≔ concat (BookPointedMap A B) f
      (book_pointed_compose A pointed_unit B (factor .fst) (book_pointed_constant pointed_unit B))
      (book_pointed_constant A B) (factor .snd) (book_pointed_unit_factor_constant A B (factor .fst)) in
    let triangle ≔ concat (BookPointedMap A B) f (book_pointed_constant A B)
      (book_pointed_compose A A B (book_pointed_constant A A) f) null (book_pointed_constant_triangle A B f) in
    let lifts ≔ universal A f covering in
    let equality ≔ contractible_prop (PointedCoverLifts A B A f f)
      (native_contraction (PointedCoverLifts A B A f f) lifts)
      (book_pointed_constant A A, triangle) (book_pointed_identity A, book_pointed_identity_triangle A B f) in
    (A .point, a ↦ equality .fst .fst (refl a))

{` lem:univ-cover-of-groupoid, both directions and the exact pointed UP. `}
def universal_cover_contractibility_equiv (A B : Pointed) (groupoid : isGroupoid (B .carrier)) (f : BookPointedMap A B)
  (covering : IsCovering (A .carrier) (B .carrier) (f .fst))
  : BookEquiv (IsUniversalPointedCover A B f) (BookIsContr (A .carrier))
  ≔ book_equivalence (IsUniversalPointedCover A B f) (BookIsContr (A .carrier))
      (iff_equiv (IsUniversalPointedCover A B f) (BookIsContr (A .carrier))
        (universal_pointed_cover_prop A B f) (book_iscontr_isprop (A .carrier))
        (universal_cover_contractible A B groupoid f covering) (contractible_cover_universal A B f))
