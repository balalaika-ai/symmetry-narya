export "18-families-and-fibers"

{` A path of function domains can be discharged using the forward
   transport of that path. Its reflexive case uses typal transport beta. `}
def domain_pathover (X Y A : Type) (p : Id Type X Y) (f : X → A) (g : Y → A)
  (h : (x : X) → Id A (f x) (g (p .trr x)))
  : Id (T ↦ T → A) p f g
  ≔ J Type X
      (Y p ↦ (g : Y → A) → ((x : X) → Id A (f x) (g (p .trr x))) →
        Id (T ↦ T → A) p f g)
      (g h ↦ funext X (_ ↦ A) f g
        (x ↦ concat A (f x) (g (transport Type (T ↦ T) X X (refl X) x)) (g x)
          (h x) (refl g (transport_refl Type (T ↦ T) X x)))) Y p g h

def MapsInto (A : Type) : Type ≔ Σ Type (B ↦ B → A)

def fibers_of_map (A : Type) (t : MapsInto A) : A → Type
  ≔ a ↦ BookFiber (t .fst) A (t .snd) a

def map_of_family (A : Type) (F : A → Type) : MapsInto A
  ≔ (Σ A F, t ↦ t .fst)

def maps_families_eta (A : Type) (t : MapsInto A)
  : Id (MapsInto A) (map_of_family A (fibers_of_map A t)) t
  ≔ let e ≔ sum_of_fibers_equiv (t .fst) A (t .snd) in
    (ua (Σ A (fibers_of_map A t)) (t .fst) e,
      domain_pathover (Σ A (fibers_of_map A t)) (t .fst) A
        (ua (Σ A (fibers_of_map A t)) (t .fst) e)
        (s ↦ s .fst) (t .snd) (s ↦ s .snd .snd))

def maps_families_beta (A : Type) (F : A → Type)
  : Id (A → Type) (fibers_of_map A (map_of_family A F)) F
  ≔ funext A (_ ↦ Type) (fibers_of_map A (map_of_family A F)) F
      (a ↦ ua (BookFiber (Σ A F) A (t ↦ t .fst) a) (F a)
        (native_equivalence (BookFiber (Σ A F) A (t ↦ t .fst) a) (F a)
          (book_projection_fiber_equiv A F a)))

{` lem:typefamiliesandfibrations. This uses the constructed ua and its
   forward transport computation, not an assumed inverse law for ua. `}
def maps_families_equiv (A : Type) : BookEquiv (MapsInto A) (A → Type)
  ≔ book_quasi_inverse_equiv (MapsInto A) (A → Type)
      (fibers_of_map A) (map_of_family A) (maps_families_eta A) (maps_families_beta A)

def sigma_transport_equiv (X Y : Type) (p : Id Type X Y) (P : Y → Type)
  : Equiv (Σ X (x ↦ P (p .trr x))) (Σ Y P)
  ≔ J Type X
      (Y p ↦ (P : Y → Type) → Equiv (Σ X (x ↦ P (p .trr x))) (Σ Y P))
      (P ↦ family_equiv X (x ↦ P (transport Type (T ↦ T) X X (refl X) x)) P
        (x ↦ id_to_equiv (P (transport Type (T ↦ T) X X (refl X) x)) (P x)
          (refl P (transport_refl Type (T ↦ T) X x)))) Y p P

def sigma_pullback_equiv (X Y : Type) (e : Equiv X Y) (P : Y → Type)
  : Equiv (Σ X (x ↦ P (e .map x))) (Σ Y P)
  ≔ sigma_transport_equiv X Y (ua X Y e) P

{` xca:sum-base-path, using the book's path-to-equivalence function. `}
def sum_base_path (X Y : Type) (p : Id Type Y X) (P : X → Type)
  : Equiv (Σ X P) (Σ Y (y ↦ P (id_to_equiv Y X p .map y)))
  ≔ canonical_inverse_equiv (Σ Y (y ↦ P (id_to_equiv Y X p .map y))) (Σ X P)
      (sigma_pullback_equiv Y X (id_to_equiv Y X p) P)

{` xca:sum-equiv-base, with the canonical inverse of the given equivalence. `}
def sum_equiv_base (X Y : Type) (e : Equiv X Y) (P : X → Type)
  : Equiv (Σ X P) (Σ Y (y ↦ P (equiv_inverse_map X Y e y)))
  ≔ canonical_inverse_equiv (Σ Y (y ↦ P (equiv_inverse_map X Y e y))) (Σ X P)
      (sigma_pullback_equiv Y X (canonical_inverse_equiv X Y e) P)

def sum_families (X : Type) (S : Type → Type)
  : Equiv (X → Σ Type S) (Σ (X → Type) (F ↦ (x : X) → S (F x)))
  ≔ choice_equiv X (_ ↦ Type) (_ Y ↦ S Y)

{` lem:Prop-Set-pointed-families, general part. Narya efafad2 has a single
   universe Type : Type (levels are planned upstream), so this is stated for
   Type; the mathematical construction itself is explicit. `}
def structured_families_equiv (A : Type) (S : Type → Type)
  : Equiv (A → Σ Type S)
      (Σ Type (B ↦ Σ (B → A) (f ↦ (a : A) → S (BookFiber B A f a))))
  ≔ let F ≔ (Σ (A → Type) (C ↦ (a : A) → S (C a))) in
    let M ≔ (Σ (MapsInto A) (t ↦ (a : A) → S (fibers_of_map A t a))) in
    compose_equiv (A → Σ Type S) M
      (Σ Type (B ↦ Σ (B → A) (f ↦ (a : A) → S (BookFiber B A f a))))
      (compose_equiv (A → Σ Type S) F M (sum_families A S)
        (canonical_inverse_equiv M F
          (sigma_pullback_equiv (MapsInto A) (A → Type)
            (native_equivalence (MapsInto A) (A → Type) (maps_families_equiv A))
            (C ↦ (a : A) → S (C a)))))
      (sigma_assoc Type (B ↦ B → A) (B f ↦ (a : A) → S (BookFiber B A f a)))

def PropTypes : Type ≔ Σ Type isProp
def SetTypes : Type ≔ Σ Type isSet
def PointedTypes : Type ≔ Σ Type (A ↦ A)

def proposition_families_equiv (A : Type)
  : Equiv (A → PropTypes)
      (Σ Type (B ↦ Σ (B → A) (f ↦ (a : A) → isProp (BookFiber B A f a))))
  ≔ structured_families_equiv A isProp

def set_families_equiv (A : Type)
  : Equiv (A → SetTypes)
      (Σ Type (B ↦ Σ (B → A) (f ↦ (a : A) → isSet (BookFiber B A f a))))
  ≔ structured_families_equiv A isSet

def pointed_families_equiv (A : Type)
  : Equiv (A → PointedTypes)
      (Σ Type (B ↦ Σ (B → A) (f ↦ (a : A) → BookFiber B A f a)))
  ≔ structured_families_equiv A (B ↦ B)

{` xca:sum-equivalences, allowing both the base and the fibers to vary. `}
def sigma_equivalences (A B : Type) (F : A → Type) (G : B → Type)
  (e : Equiv A B) (d : (a : A) → Equiv (F a) (G (e .map a)))
  : Equiv (Σ A F) (Σ B G)
  ≔ compose_equiv (Σ A F) (Σ A (a ↦ G (e .map a))) (Σ B G)
      (family_equiv A F (a ↦ G (e .map a)) d) (sigma_pullback_equiv A B e G)

{` cor:subtype-same-level, including propositions (book n=-1). `}
def subtype_hlevel (n : Nat) (A : Type) (P : A → Type)
  (hA : HLevel (suc. n) A) (hP : (a : A) → isProp (P a))
  : HLevel (suc. n) (Σ A P)
  ≔ hlevel_sigma (suc. n) A P hA (a ↦ proposition_hlevel n (P a) (hP a))
