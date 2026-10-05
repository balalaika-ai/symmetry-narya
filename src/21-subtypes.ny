export "20-univalence"

def equivalences_prop (A B : Type) (hB : isProp B) : isProp (Equiv A B)
  ≔ e d ↦ equiv_homotopy A B e d (a ↦ hB (e .map a) (d .map a))

def equiv_sigma_equiv (A B : Type) : Equiv (Equiv A B) (Σ (A → B) (isEquiv A B))
  ≔ quasi_inverse_equiv (Equiv A B) (Σ (A → B) (isEquiv A B))
      (e ↦ (e .map, e .equiv)) (t ↦ (t .fst, t .snd)) (e ↦ refl e) (t ↦ refl t)

def equivalences_set (A B : Type) (hB : isSet B) : isSet (Equiv A B)
  ≔ hlevel_two_to_set (Equiv A B)
      (hlevel_equiv (suc. (suc. zero.)) (Σ (A → B) (isEquiv A B)) (Equiv A B)
        (canonical_inverse_equiv (Equiv A B) (Σ (A → B) (isEquiv A B)) (equiv_sigma_equiv A B))
        (set_to_hlevel_two (Σ (A → B) (isEquiv A B))
          (sigma_set (A → B) (isEquiv A B) (pi_set A (_ ↦ B) (_ ↦ hB))
            (f ↦ prop_is_set (isEquiv A B f) (isequiv_isprop A B f)))))

def proposition_type_paths_prop (P Q : Type) (hQ : isProp Q) : isProp (Id Type P Q)
  ≔ retract_prop (Equiv P Q) (Id Type P Q) (equivalences_prop P Q hQ)
      (ua P Q) (id_to_equiv P Q) (ua_eta P Q)

def set_type_paths_set (A B : Type) (hB : isSet B) : isSet (Id Type A B)
  ≔ hlevel_two_to_set (Id Type A B)
      (hlevel_equiv (suc. (suc. zero.)) (Equiv A B) (Id Type A B)
        (canonical_inverse_equiv (Id Type A B) (Equiv A B) (univalence_equiv A B))
        (set_to_hlevel_two (Equiv A B) (equivalences_set A B hB)))

def proposition_paths_equiv (P Q : PropTypes)
  : Equiv (Id PropTypes P Q) (Equiv (P .fst) (Q .fst))
  ≔ compose_equiv (Id PropTypes P Q) (Id Type (P .fst) (Q .fst)) (Equiv (P .fst) (Q .fst))
      (subtype_path_equiv Type isProp isprop_isprop P Q) (univalence_equiv (P .fst) (Q .fst))

{` lem:Prop-in-Set `}
def propositions_set : isSet PropTypes
  ≔ P Q ↦ let e ≔ proposition_paths_equiv P Q in
    retract_prop (Equiv (P .fst) (Q .fst)) (Id PropTypes P Q)
      (equivalences_prop (P .fst) (Q .fst) (Q .snd))
      (equiv_inverse_map (Id PropTypes P Q) (Equiv (P .fst) (Q .fst)) e) (e .map)
      (equiv_retraction (Id PropTypes P Q) (Equiv (P .fst) (Q .fst)) e)

def set_paths_equiv (A B : SetTypes)
  : Equiv (Id SetTypes A B) (Equiv (A .fst) (B .fst))
  ≔ compose_equiv (Id SetTypes A B) (Id Type (A .fst) (B .fst)) (Equiv (A .fst) (B .fst))
      (subtype_path_equiv Type isSet isset_isprop A B) (univalence_equiv (A .fst) (B .fst))

{` lem:Set-is-groupoid `}
def sets_groupoid : isGroupoid SetTypes
  ≔ A B ↦ hlevel_two_to_set (Id SetTypes A B)
      (hlevel_equiv (suc. (suc. zero.)) (Equiv (A .fst) (B .fst)) (Id SetTypes A B)
        (canonical_inverse_equiv (Id SetTypes A B) (Equiv (A .fst) (B .fst)) (set_paths_equiv A B))
        (set_to_hlevel_two (Equiv (A .fst) (B .fst)) (equivalences_set (A .fst) (B .fst) (B .snd))))

def iff_equiv (P Q : Type) (hP : isProp P) (hQ : isProp Q) (f : P → Q) (g : Q → P)
  : Equiv P Q ≔ quasi_inverse_equiv P Q f g (p ↦ hP (g (f p)) p) (q ↦ hQ (f (g q)) q)

def proposition_extensionality (P Q : PropTypes) (f : P .fst → Q .fst) (g : Q .fst → P .fst)
  : Id PropTypes P Q
  ≔ equiv_inverse_map (Id PropTypes P Q) (Equiv (P .fst) (Q .fst)) (proposition_paths_equiv P Q)
      (iff_equiv (P .fst) (Q .fst) (P .snd) (Q .snd) f g)

{` def:predicate and def:subtype. `}
def Subtypes (T : Type) : Type ≔ T → PropTypes
def DecidablePredicate (T : Type) : Type ≔ Σ (Subtypes T) (P ↦ (t : T) → Decidable (P t .fst))
def SubtypeCarrier (T : Type) (P : Subtypes T) : Type ≔ Σ T (t ↦ P t .fst)
def subtypes_set (T : Type) : isSet (Subtypes T) ≔ pi_set T (_ ↦ PropTypes) (_ ↦ propositions_set)

def Inclusion (T : Type) (P Q : Subtypes T) : Type ≔ (t : T) → P t .fst → Q t .fst
def inclusion_prop (T : Type) (P Q : Subtypes T) : isProp (Inclusion T P Q)
  ≔ pi_prop T (t ↦ P t .fst → Q t .fst)
      (t ↦ pi_prop (P t .fst) (_ ↦ Q t .fst) (_ ↦ Q t .snd))
def inclusion_refl (T : Type) (P : Subtypes T) : Inclusion T P P ≔ t p ↦ p
def inclusion_trans (T : Type) (P Q R : Subtypes T)
  (f : Inclusion T P Q) (g : Inclusion T Q R) : Inclusion T P R ≔ t p ↦ g t (f t p)
def inclusion_antisym (T : Type) (P Q : Subtypes T)
  (f : Inclusion T P Q) (g : Inclusion T Q P) : Id (Subtypes T) P Q
  ≔ funext T (_ ↦ PropTypes) P Q (t ↦ proposition_extensionality (P t) (Q t) (f t) (g t))
def empty_subtype (T : Type) : Subtypes T ≔ _ ↦ (Empty, empty_prop)
def full_subtype (T : Type) : Subtypes T ≔ _ ↦ (Unit, unit_prop)
def empty_subtype_least (T : Type) (P : Subtypes T) : Inclusion T (empty_subtype T) P
  ≔ t e ↦ absurd (P t .fst) e
def full_subtype_greatest (T : Type) (P : Subtypes T) : Inclusion T P (full_subtype T) ≔ _ _ ↦ star.

{` A bundled map whose book-oriented fibers are propositions. `}
def HasPropFibers (T : Type) (t : MapsInto T) : Type
  ≔ (a : T) → isProp (fibers_of_map T t a)
def has_prop_fibers_prop (T : Type) (t : MapsInto T) : isProp (HasPropFibers T t)
  ≔ pi_prop T (a ↦ isProp (fibers_of_map T t a)) (a ↦ isprop_isprop (fibers_of_map T t a))
def BundledInjection (T : Type) : Type ≔ Σ (MapsInto T) (HasPropFibers T)

def subtype_to_bundled_injection (T : Type) (P : Subtypes T) : BundledInjection T
  ≔ (map_of_family T (t ↦ P t .fst), a ↦
      hlevel_one_to_prop (BookFiber (SubtypeCarrier T P) T (t ↦ t .fst) a)
        (hlevel_equiv (suc. zero.) (P a .fst)
          (BookFiber (SubtypeCarrier T P) T (t ↦ t .fst) a)
          (native_equivalence (P a .fst) (BookFiber (SubtypeCarrier T P) T (t ↦ t .fst) a)
            (book_projection_inclusion_equiv T (t ↦ P t .fst) a))
          (prop_to_hlevel_one (P a .fst) (P a .snd))))

def bundled_injection_to_subtype (T : Type) (i : BundledInjection T) : Subtypes T
  ≔ a ↦ (fibers_of_map T (i .fst) a, i .snd a)

def subtypes_injections_eta (T : Type) (P : Subtypes T)
  : Id (Subtypes T) (bundled_injection_to_subtype T (subtype_to_bundled_injection T P)) P
  ≔ funext T (_ ↦ PropTypes) (bundled_injection_to_subtype T (subtype_to_bundled_injection T P)) P
      (a ↦ let e ≔ native_equivalence
        (BookFiber (SubtypeCarrier T P) T (t ↦ t .fst) a) (P a .fst)
        (book_projection_fiber_equiv T (t ↦ P t .fst) a) in
        proposition_extensionality
          (bundled_injection_to_subtype T (subtype_to_bundled_injection T P) a) (P a)
          (e .map) (equiv_inverse_map (BookFiber (SubtypeCarrier T P) T (t ↦ t .fst) a) (P a .fst) e))

def subtypes_injections_beta (T : Type) (i : BundledInjection T)
  : Id (BundledInjection T) (subtype_to_bundled_injection T (bundled_injection_to_subtype T i)) i
  ≔ let j ≔ subtype_to_bundled_injection T (bundled_injection_to_subtype T i) in
    let p ≔ maps_families_eta T (i .fst) in
    (p, pathover_of_eq (MapsInto T) (HasPropFibers T) (j .fst) (i .fst) p (j .snd) (i .snd)
      (has_prop_fibers_prop T (i .fst)
        (transport (MapsInto T) (HasPropFibers T) (j .fst) (i .fst) p (j .snd)) (i .snd)))

def subtypes_bundled_injections_equiv (T : Type) : Equiv (Subtypes T) (BundledInjection T)
  ≔ quasi_inverse_equiv (Subtypes T) (BundledInjection T)
      (subtype_to_bundled_injection T) (bundled_injection_to_subtype T)
      (subtypes_injections_eta T) (subtypes_injections_beta T)

{` def:injtype and lem:Sub(T)=Inj(T), with the exact displayed sigma order
   and map P |-> (T_P,fst). `}
def InjectionsInto (T : Type) : Type
  ≔ Σ Type (S ↦ Σ (S → T) (f ↦ (t : T) → isProp (BookFiber S T f t)))
def subtypes_injections_equiv (T : Type) : Equiv (Subtypes T) (InjectionsInto T)
  ≔ compose_equiv (Subtypes T) (BundledInjection T) (InjectionsInto T)
      (subtypes_bundled_injections_equiv T)
      (sigma_assoc Type (S ↦ S → T) (S f ↦ (t : T) → isProp (BookFiber S T f t)))

def injections_into_set (T : Type) : isSet (InjectionsInto T)
  ≔ hlevel_two_to_set (InjectionsInto T)
      (hlevel_equiv (suc. (suc. zero.)) (Subtypes T) (InjectionsInto T)
        (subtypes_injections_equiv T) (set_to_hlevel_two (Subtypes T) (subtypes_set T)))
