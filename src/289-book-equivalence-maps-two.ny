export "280-book-equivalence-maps"
export "150-paths-over-and-pairs"
export "223-constructed-circle"

{` More companions in the style of module 280: the book's precise claim "this
   specific map is an equivalence" for results whose original type only says
   that two types are equivalent (BookEquiv X Y or Equiv X Y). Except for
   con:identity-ptd-maps, the underlying map of the original declaration is
   definitionally the book's map, so each companion is the original followed
   by .equiv; native Equiv results are first converted with book_equivalence,
   which keeps the map. The map is written out in each companion's type, in
   the book's orientation. The map of pointed_map_path_equiv reindexes along
   function extensionality with sigma_pullback_equiv (defined by path
   induction on ua), so there it is proved homotopic to the book's ptw_* and
   the equivalence is transferred with equiv_change_map. At the end, one
   more circle instantiation in the style of module 250. `}

{` def:funext (intro-uf.tex:1413): ptw_{f,g} (happly, def:ptw) is an equivalence.
   This covers function_extensionality and book_function_extensionality. `}
def function_extensionality_book_map (A : Type) (B : A → Type) (f g : (x : A) → B x)
  : BookIsEquiv (Id ((x : A) → B x) f g) (Homotopy A B f g) (happly A B f g)
  ≔ book_function_extensionality A B f g .equiv

{` lem:contract-away (intro-uf.tex:1302): the book's f, defined by induction on i
   with f(a, refl a, b) ≔ b (contract_away_map), is an equivalence. `}
def contract_away_equiv_book_map (A : Type) (a : A) (B : (x : A) → Id A a x → Type)
  : BookIsEquiv (Σ A (x ↦ Σ (Id A a x) (B x))) (B a (refl a))
      (t ↦ contract_away_map A a B (t .fst) (t .snd .fst) (t .snd .snd))
  ≔ book_equivalence (Σ A (x ↦ Σ (Id A a x) (B x))) (B a (refl a))
      (contract_away_equiv A a B) .equiv

{` cor:contract-away (intro-uf.tex:1343): the same f, for B not depending on i. `}
def contract_away_simple_book_map (A : Type) (a : A) (B : A → Type)
  : BookIsEquiv (Σ A (x ↦ Product (Id A a x) (B x))) (B a)
      (t ↦ contract_away_map A a (x _ ↦ B x) (t .fst) (t .snd .fst) (t .snd .snd))
  ≔ book_equivalence (Σ A (x ↦ Product (Id A a x) (B x))) (B a)
      (contract_away_simple A a B) .equiv

{` lem:fiberwise (intro-uf.tex:1385): if every f(x) : B(x) → C(x) is an
   equivalence, then tot(f)(x, y) ≔ (x, f(x)(y)) (totalize) is an equivalence. `}
def family_equiv_book_map (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (h : (a : A) → BookIsEquiv (B a) (C a) (f a))
  : BookIsEquiv (Σ A B) (Σ A C) (totalize A B C f)
  ≔ book_equivalence (Σ A B) (Σ A C)
      (family_equiv A B C (a ↦ native_equivalence (B a) (C a) (f a, h a))) .equiv

{` lem:isEq-pair= (intro-uf.tex:1591): (p, q) ↦ pair=(p, q) ≔ apap pair p q
   (pair_path, def:pairtopath) is an equivalence. `}
def sigma_path_equiv_book_map (A : Type) (B : A → Type) (x x' : A) (y : B x) (y' : B x')
  : BookIsEquiv (Σ (Id A x x') (p ↦ Id B p y y')) (Id (Σ A B) (x, y) (x', y'))
      (pq ↦ pair_path A B x x' y y' (pq .fst) (pq .snd))
  ≔ book_equivalence (SigmaPath A B (x, y) (x', y')) (Id (Σ A B) (x, y) (x', y'))
      (sigma_path_equiv A B (x, y) (x', y')) .equiv

{` lem:subtype-eq-= (intro-uf.tex:3332): ap_fst is an equivalence. `}
def subtype_path_equiv_book_map (A : Type) (B : A → Type) (hB : (a : A) → isProp (B a))
  (u v : Σ A B)
  : BookIsEquiv (Id (Σ A B) u v) (Id A (u .fst) (v .fst)) (map_path (Σ A B) A (t ↦ t .fst) u v)
  ≔ book_equivalence (Id (Σ A B) u v) (Id A (u .fst) (v .fst))
      (subtype_path_equiv A B hB u v) .equiv

{` lem:fst-fiber(a)=B(a) (intro-uf.tex:4548): e_a(b) ≔ ((a, b), refl a). `}
def book_projection_inclusion_equiv_book_map (A : Type) (B : A → Type) (a : A)
  : BookIsEquiv (B a) (BookFiber (Σ A B) A (t ↦ t .fst) a) (b ↦ ((a, b), refl a))
  ≔ book_projection_inclusion_equiv A B a .equiv

{` lem:sum-of-fibers (intro-uf.tex:4564): e(b, a, p) ≔ a. `}
def book_sum_of_fibers_equiv_book_map (A B : Type) (f : A → B)
  : BookIsEquiv (Σ B (b ↦ BookFiber A B f b)) A (t ↦ t .snd .fst)
  ≔ book_sum_of_fibers_equiv A B f .equiv

{` lem:typefamiliesandfibrations (intro-uf.tex:4586): preim(B, f)(a) ≔ f⁻¹(a),
   with book fibers. `}
def maps_families_equiv_book_map (A : Type)
  : BookIsEquiv (MapsInto A) (A → Type) (t ↦ (a ↦ BookFiber (t .fst) A (t .snd) a))
  ≔ maps_families_equiv A .equiv

{` def:univalence (intro-uf.tex:2103): p ↦ ptoe p ≔ trp[id_U](p), transport in
   the identity family (def:idtoeq), is an equivalence; its equivalence
   component is the proof that transport functions are equivalences. First
   with native Equiv X Y as codomain (transport_univalence_equiv), then with
   the book's X ≃ Y (book_univalence). `}
def transport_univalence_equiv_book_map (A B : Type)
  : BookIsEquiv (Id Type A B) (Equiv A B)
      (p ↦ ((x ↦ transport Type (T ↦ T) A B p x), transport_equiv A B p .equiv))
  ≔ book_equivalence (Id Type A B) (Equiv A B) (transport_univalence_equiv A B) .equiv

def book_univalence_book_map (A B : Type)
  : BookIsEquiv (Id Type A B) (BookEquiv A B)
      (p ↦ ((x ↦ transport Type (T ↦ T) A B p x),
        book_equivalence A B (transport_equiv A B p) .equiv))
  ≔ book_univalence A B .equiv

{` xca:tabulation (intro-uf.tex:4471): lookup, x_1 … x_n ↦ (n, i ↦ x_i). `}
def lookup_equiv_book_map (A : Type) : BookIsEquiv (List A) (Table A) (lookup A)
  ≔ lookup_equiv A .equiv

{` xca:list-contr (intro-uf.tex:2032): len is an equivalence for contractible A. `}
def length_equiv_book_map (A : Type) (hA : isContr A) : BookIsEquiv (List A) Nat (length A)
  ≔ book_equivalence (List A) Nat (length_equiv A hA) .equiv

{` lem:Sub(T)=Inj(T) (intro-uf.tex:3437): P ↦ (T_P, fst, _), where the last
   component is the proof that fst is an injection. `}
def subtypes_injections_equiv_book_map (T : Type)
  : BookIsEquiv (Subtypes T) (InjectionsInto T)
      (P ↦ (SubtypeCarrier T P, ((t ↦ t .fst), subtype_to_bundled_injection T P .snd)))
  ≔ book_equivalence (Subtypes T) (InjectionsInto T) (subtypes_injections_equiv T) .equiv

{` xca:plusforgetadjoint (intro-uf.tex:3598). The book names no map; the
   equivalence (A → B÷) ≃ (A₊ →* B) is extension by the base point,
   plus_extend f ≔ ([inl a ↦ f a | inr _ ↦ pt_B], refl pt_B). `}
def plus_forget_adjunction_book_map (A : Type) (B : Pointed)
  : BookIsEquiv (A → B .carrier) (BookPointedMap (plus_pointed A) B) (plus_extend A B)
  ≔ book_equivalence (A → B .carrier) (BookPointedMap (plus_pointed A) B)
      (plus_forget_adjunction A B) .equiv

{` xca:pointedequiv (intro-uf.tex:3618): r ↦ ((ptoe r÷, q), _) with the
   carrier path r÷ = r .carrier, q : pt_Y = ptoe r÷ (pt_X) (pointed_path_point)
   and the proof that transport is an equivalence. `}
def pointed_path_equiv_book_map (X Y : Pointed)
  : BookIsEquiv (Id Pointed X Y) (BookPointedEquiv X Y)
      (r ↦ ((r .carrier .trr, pointed_path_point X Y r),
        book_equivalence (X .carrier) (Y .carrier)
          (transport_equiv (X .carrier) (Y .carrier) (r .carrier)) .equiv))
  ≔ book_equivalence (Id Pointed X Y) (BookPointedEquiv X Y) (pointed_path_equiv X Y) .equiv

{` The reindexing sigma_pullback_equiv X Y e P (xca:sum-equiv-base, defined by
   path induction on ua e) has underlying map (x, c) ↦ (e x, c), up to an
   identification. Proved by induction on the path, with the equivalence and
   the identification in one Σ-motive, so that the first component is
   sigma_transport_equiv itself. `}
def sigma_transport_equiv_map (X Y : Type) (p : Id Type X Y) (P : Y → Type)
  (u : Σ X (x ↦ P (p .trr x)))
  : Id (Σ Y P) (sigma_transport_equiv X Y p P .map u) (p .trr (u .fst), u .snd)
  ≔ J Type X
      (Y p ↦ Σ ((P : Y → Type) → Equiv (Σ X (x ↦ P (p .trr x))) (Σ Y P))
        (s ↦ (P : Y → Type) (u : Σ X (x ↦ P (p .trr x)))
          → Id (Σ Y P) (s P .map u) (p .trr (u .fst), u .snd)))
      ((P ↦ family_equiv X (x ↦ P (transport Type (T ↦ T) X X (refl X) x)) P
          (x ↦ id_to_equiv (P (transport Type (T ↦ T) X X (refl X) x)) (P x)
            (refl P (transport_refl Type (T ↦ T) X x)))),
       (P u ↦ concat (Σ X P)
          (u .fst, id_to_equiv (P (transport Type (T ↦ T) X X (refl X) (u .fst))) (P (u .fst))
            (refl P (transport_refl Type (T ↦ T) X (u .fst))) .map (u .snd))
          (u .fst, refl P (transport_refl Type (T ↦ T) X (u .fst)) .trr (u .snd))
          (transport Type (T ↦ T) X X (refl X) (u .fst), u .snd)
          (refl (u .fst), id_to_equiv_transport (P (transport Type (T ↦ T) X X (refl X) (u .fst)))
            (P (u .fst)) (refl P (transport_refl Type (T ↦ T) X (u .fst))) (u .snd))
          (inverse (Σ X P) (transport Type (T ↦ T) X X (refl X) (u .fst), u .snd)
            (u .fst, refl P (transport_refl Type (T ↦ T) X (u .fst)) .trr (u .snd))
            (transport_refl Type (T ↦ T) X (u .fst),
              refl P (transport_refl Type (T ↦ T) X (u .fst)) .liftr (u .snd)))))
      Y p .snd P u

def sigma_pullback_equiv_map (X Y : Type) (e : Equiv X Y) (P : Y → Type)
  (u : Σ X (x ↦ P (e .map x)))
  : Id (Σ Y P) (sigma_pullback_equiv X Y e P .map u) (e .map (u .fst), u .snd)
  ≔ sigma_transport_equiv_map X Y (ua X Y e) P u

{` con:identity-ptd-maps (intro-uf.tex:3632): the book's ptw_*, the composite
   of the displayed chain. On p : f = g it is (ptw(p₁), c), where p₁ : f÷ = g÷
   and c converts the path over p₂ by def:pathover-trp. Transport in
   T(k) ≔ (pt_Y = k(pt_X)) along p₁ is ptw(p₁)(pt_X)·f_pt by definition, so
   step (*) is judgmental, and reindexing along ptw itself (not its inverse)
   makes step (**) unnecessary. The map of pointed_map_path_equiv is
   identified with it pointwise (pointed_map_path_equiv_ptw), and the
   equivalence is transferred with equiv_change_map. `}
def pointed_map_path_equiv_ptw (X Y : Pointed) (f g : BookPointedMap X Y)
  (p : Id (BookPointedMap X Y) f g)
  : Id (PointedHomotopy X Y f g) (pointed_map_path_equiv X Y f g .map p)
      (happly (X .carrier) (_ ↦ Y .carrier) (f .fst) (g .fst) (p .fst),
        pathover_transport_equiv (X .carrier → Y .carrier)
          (k ↦ Id (Y .carrier) (Y .point) (k (X .point)))
          (f .fst) (g .fst) (p .fst) (f .snd) (g .snd) .map (p .snd))
  ≔ let A ≔ X .carrier in
    let B ≔ Y .carrier in
    let T : (A → B) → Type ≔ k ↦ Id B (Y .point) (k (X .point)) in
    sigma_pullback_equiv_map (Id (A → B) (f .fst) (g .fst)) (Homotopy A (_ ↦ B) (f .fst) (g .fst))
      (function_extensionality A (_ ↦ B) (f .fst) (g .fst))
      (h ↦ Id (Id B (Y .point) (g .fst (X .point)))
        (concat B (Y .point) (f .fst (X .point)) (g .fst (X .point)) (f .snd) (h (X .point))) (g .snd))
      (p .fst, pathover_transport_equiv (A → B) T (f .fst) (g .fst) (p .fst) (f .snd) (g .snd) .map (p .snd))

def pointed_map_path_equiv_book_map (X Y : Pointed) (f g : BookPointedMap X Y)
  : BookIsEquiv (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g)
      (p ↦ (happly (X .carrier) (_ ↦ Y .carrier) (f .fst) (g .fst) (p .fst),
        pathover_transport_equiv (X .carrier → Y .carrier)
          (k ↦ Id (Y .carrier) (Y .point) (k (X .point)))
          (f .fst) (g .fst) (p .fst) (f .snd) (g .snd) .map (p .snd)))
  ≔ book_equivalence (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g)
      (equiv_change_map (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g)
        (pointed_map_path_equiv X Y f g)
        (p ↦ (happly (X .carrier) (_ ↦ Y .carrier) (f .fst) (g .fst) (p .fst),
          pathover_transport_equiv (X .carrier → Y .carrier)
            (k ↦ Id (Y .carrier) (Y .point) (k (X .point)))
            (f .fst) (g .fst) (p .fst) (f .snd) (g .snd) .map (p .snd)))
        (pointed_map_path_equiv_ptw X Y f g)) .equiv

{` xca:twoS1coverings (circle.tex:609), part 1, second task, instantiated at
   the constructed circle (compare module 250; the type is written out):
   c_Bool = ve_Set(Bool, refl Bool). `}
def S1_constant_boolean_circle_rec_path
  : Id (constructed_circle .carrier → SetTypes) (constant_boolean_circle_family constructed_circle)
      (identity_boolean_circle_family constructed_circle)
  ≔ constant_boolean_circle_rec_path constructed_circle
