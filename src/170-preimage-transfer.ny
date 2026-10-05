export "136-roots-of-infinite-cycles"

{` xca:preim-eq.  Fibers use the book convention c = f(a), and h(a)p is
   the path p followed by h(a).  The forward map is exactly the displayed one. `}
def preimage_transfer (A B C : Type) (f : A → C) (g : B → C) (e : Equiv A B)
  (h : (x : A) → Id C (f x) (g (e .map x))) (c : C)
  (t : BookFiber A C f c) : BookFiber B C g c
  ≔ (e .map (t .fst), concat C c (f (t .fst)) (g (e .map (t .fst))) (t .snd) (h (t .fst)))

def preimage_transfer_is_equivalence (A B C : Type) (f : A → C) (g : B → C) (e : Equiv A B)
  (h : (x : A) → Id C (f x) (g (e .map x))) (c : C)
  : isEquiv (BookFiber A C f c) (BookFiber B C g c) (preimage_transfer A B C f g e h c)
  ≔ equivalence_induction A
      (B e ↦ (g : B → C) (h : (x : A) → Id C (f x) (g (e .map x)))
        → isEquiv (BookFiber A C f c) (BookFiber B C g c) (preimage_transfer A B C f g e h c))
      (g h ↦ family_equiv A (a ↦ Id C c (f a)) (a ↦ Id C c (g a))
        (a ↦ transport_equiv (Id C c (f a)) (Id C c (g a))
          (refl ((w ↦ Id C c w) : C → Type) (h a))) .equiv)
      B e g h

def preimage_transfer_equiv (A B C : Type) (f : A → C) (g : B → C) (e : Equiv A B)
  (h : (x : A) → Id C (f x) (g (e .map x))) (c : C)
  : BookEquiv (BookFiber A C f c) (BookFiber B C g c)
  ≔ book_equivalence (BookFiber A C f c) (BookFiber B C g c)
      (preimage_transfer A B C f g e h c, preimage_transfer_is_equivalence A B C f g e h c)

{` rem:flipthecircle, the general case in the margin: an equivalence
   e : A → A' identifies (A, fe) with (A', f) as maps into C. `}
def precompose_equivalence_path (A A' C : Type) (e : Equiv A A') (f : A' → C)
  : Id (MapsInto C) (A, compose A A' C f (e .map)) (A', f)
  ≔ (ua A A' e, domain_pathover A A' C (ua A A' e) (compose A A' C f (e .map)) f
      (x ↦ refl (f (e .map x))))

def precompose_equivalence_covering (A A' B : Type) (e : Equiv A A') (f : A' → B)
  (hf : IsCovering A' B f) : IsCovering A B (compose A A' B f (e .map))
  ≔ transport (MapsInto B) (CoveringProperty B) (A', f) (A, compose A A' B f (e .map))
      (inverse (MapsInto B) (A, compose A A' B f (e .map)) (A', f) (precompose_equivalence_path A A' B e f)) hf

def precompose_equivalence_covering_path (A A' B : Type) (e : Equiv A A') (f : A' → B)
  (hf : IsCovering A' B f)
  : Id (Coverings B) (A, (compose A A' B f (e .map), precompose_equivalence_covering A A' B e f hf)) (A', (f, hf))
  ≔ refl ((c ↦ (c .fst .fst, (c .fst .snd, c .snd))) : BundledCovering B → Coverings B)
      (subtype_equal (MapsInto B) (CoveringProperty B) (covering_property_prop B)
        ((A, compose A A' B f (e .map)), precompose_equivalence_covering A A' B e f hf) ((A', f), hf)
        (precompose_equivalence_path A A' B e f))

{` rem:subtype-diagram.  For an injection i₂ (propositional fibers) the
   type of fillers g with f i₁ = i₂ g is a proposition. `}
def subtype_diagram_fillers_prop (S X T Y : Type) (i1 : S → X) (f : X → Y) (i2 : T → Y)
  (hi : IsEmbedding T Y i2)
  : isProp (Σ (S → T) (g ↦ Id (S → Y) (compose S X Y f i1) (compose S T Y i2 g)))
  ≔ postcomposition_embedding S T Y i2 hi (compose S X Y f i1)

def subtype_projection_embedding (Y : Type) (Q : Y → Type) (hq : (y : Y) → isProp (Q y))
  : IsEmbedding (Σ Y Q) Y (t ↦ t .fst)
  ≔ subtype_to_bundled_injection Y (y ↦ (Q y, hq y)) .snd

def SubtypeDiagramFillers (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type) : Type
  ≔ Σ (Σ X P → Σ Y Q) (g ↦ Id (Σ X P → Y) (compose (Σ X P) X Y f (z ↦ z .fst))
      (compose (Σ X P) (Σ Y Q) Y (w ↦ w .fst) g))

def RespectsSubtypes (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type) : Type
  ≔ (x : X) → P x → Q (f x)

def RespectsSubtypesOnCarrier (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type) : Type
  ≔ (z : Σ X P) → Q (f (z .fst))

def respects_subtypes_prop (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (hq : (y : Y) → isProp (Q y)) : isProp (RespectsSubtypes X Y f P Q)
  ≔ pi_prop X (x ↦ P x → Q (f x)) (x ↦ pi_prop (P x) (_ ↦ Q (f x)) (_ ↦ hq (f x)))

def respects_subtypes_carrier_prop (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (hq : (y : Y) → isProp (Q y)) : isProp (RespectsSubtypesOnCarrier X Y f P Q)
  ≔ pi_prop (Σ X P) (z ↦ Q (f (z .fst))) (z ↦ hq (f (z .fst)))

def subtype_diagram_fillers_is_prop (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (hq : (y : Y) → isProp (Q y)) : isProp (SubtypeDiagramFillers X Y f P Q)
  ≔ subtype_diagram_fillers_prop (Σ X P) X (Σ Y Q) Y (z ↦ z .fst) f (w ↦ w .fst)
      (subtype_projection_embedding Y Q hq)

{` The function induced by f on subtypes; its triangle holds by reflexivity. `}
def subtype_induced_map (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (q : RespectsSubtypes X Y f P Q) : Σ X P → Σ Y Q
  ≔ z ↦ (f (z .fst), q (z .fst) (z .snd))

def subtype_induced_filler (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (q : RespectsSubtypes X Y f P Q) : SubtypeDiagramFillers X Y f P Q
  ≔ (subtype_induced_map X Y f P Q q, refl (compose (Σ X P) X Y f (z ↦ z .fst)))

def subtype_filler_respects (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (u : SubtypeDiagramFillers X Y f P Q) : RespectsSubtypesOnCarrier X Y f P Q
  ≔ z ↦ transport Y Q (u .fst z .fst) (f (z .fst))
      (inverse Y (f (z .fst)) (u .fst z .fst) (u .snd (refl z))) (u .fst z .snd)

{` The three propositions of rem:subtype-diagram are logically equivalent. `}
def subtype_diagram_carrier_to_pointwise (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (q : RespectsSubtypesOnCarrier X Y f P Q) : RespectsSubtypes X Y f P Q
  ≔ x p ↦ q (x, p)

def subtype_diagram_pointwise_to_carrier (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (q : RespectsSubtypes X Y f P Q) : RespectsSubtypesOnCarrier X Y f P Q
  ≔ z ↦ q (z .fst) (z .snd)

def subtype_diagram_pointwise_fillers_equiv (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (hq : (y : Y) → isProp (Q y))
  : Equiv (RespectsSubtypes X Y f P Q) (SubtypeDiagramFillers X Y f P Q)
  ≔ iff_equiv (RespectsSubtypes X Y f P Q) (SubtypeDiagramFillers X Y f P Q)
      (respects_subtypes_prop X Y f P Q hq) (subtype_diagram_fillers_is_prop X Y f P Q hq)
      (subtype_induced_filler X Y f P Q)
      (u ↦ subtype_diagram_carrier_to_pointwise X Y f P Q (subtype_filler_respects X Y f P Q u))

def subtype_diagram_carrier_pointwise_equiv (X Y : Type) (f : X → Y) (P : X → Type) (Q : Y → Type)
  (hq : (y : Y) → isProp (Q y))
  : Equiv (RespectsSubtypesOnCarrier X Y f P Q) (RespectsSubtypes X Y f P Q)
  ≔ iff_equiv (RespectsSubtypesOnCarrier X Y f P Q) (RespectsSubtypes X Y f P Q)
      (respects_subtypes_carrier_prop X Y f P Q hq) (respects_subtypes_prop X Y f P Q hq)
      (subtype_diagram_carrier_to_pointwise X Y f P Q)
      (subtype_diagram_pointwise_to_carrier X Y f P Q)

{` Equivalence case: if f and its inverse both respect the subtypes, the
   induced functions are mutually inverse. `}
def subtype_induced_equiv (X Y : Type) (e : Equiv X Y) (P : X → Type) (Q : Y → Type)
  (hp : (x : X) → isProp (P x)) (hq : (y : Y) → isProp (Q y))
  (q : RespectsSubtypes X Y (e .map) P Q)
  (r : RespectsSubtypes Y X (equiv_inverse_map X Y e) Q P)
  : Equiv (Σ X P) (Σ Y Q)
  ≔ quasi_inverse_equiv (Σ X P) (Σ Y Q) (subtype_induced_map X Y (e .map) P Q q)
      (subtype_induced_map Y X (equiv_inverse_map X Y e) Q P r)
      (z ↦ subtype_equal X P hp
        (subtype_induced_map Y X (equiv_inverse_map X Y e) Q P r (subtype_induced_map X Y (e .map) P Q q z)) z
        (equiv_retraction X Y e (z .fst)))
      (w ↦ subtype_equal Y Q hq
        (subtype_induced_map X Y (e .map) P Q q (subtype_induced_map Y X (equiv_inverse_map X Y e) Q P r w)) w
        (equiv_counit X Y e (w .fst)))
