export "190-universes"

def contr_small (U : Universe) (T : Type) (s : U .small T) : U .small (isContr T)
  ≔ small_equiv U (Σ T (c ↦ (a : T) → Id T a c)) (isContr T)
      (quasi_inverse_equiv (Σ T (c ↦ (a : T) → Id T a c)) (isContr T)
        (p ↦ (p .fst, p .snd)) (c ↦ (c .center, c .contract)) (p ↦ refl p) (c ↦ refl c))
      (U .sigma_small T (c ↦ (a : T) → Id T a c) s
        (c ↦ U .pi_small T (a ↦ Id T a c) s (a ↦ U .id_small T s a c)))

def native_fiber_small (U : Universe) (A B : Type) (f : A → B) (sA : U .small A) (sB : U .small B) (b : B)
  : U .small (Fiber A B f b)
  ≔ U .sigma_small A (a ↦ Id B (f a) b) sA (a ↦ U .id_small B sB (f a) b)

def equiv_small (U : Universe) (A B : Type) (sA : U .small A) (sB : U .small B) : U .small (Equiv A B)
  ≔ small_equiv U (Σ (A → B) (isEquiv A B)) (Equiv A B) (canonical_inverse_equiv (Equiv A B) (Σ (A → B) (isEquiv A B)) (equiv_sigma_equiv A B))
      (U .sigma_small (A → B) (isEquiv A B) (U .pi_small A (_ ↦ B) sA (_ ↦ sB))
        (f ↦ U .pi_small B (b ↦ isContr (Fiber A B f b)) sB
          (b ↦ contr_small U (Fiber A B f b) (native_fiber_small U A B f sA sB b))))

{` The unlabeled exercise after def:ess-loc-small: U is locally U-small. `}
def universe_path_equiv (U : Universe) (X Y : UniverseType U)
  : Equiv (Id (UniverseType U) X Y) (Equiv (X .fst) (Y .fst))
  ≔ compose_equiv (Id (UniverseType U) X Y) (Id Type (X .fst) (Y .fst)) (Equiv (X .fst) (Y .fst))
      (subtype_path_equiv Type (U .small) (U .small_prop) X Y) (univalence_equiv (X .fst) (Y .fst))

def universe_locally_small (U : Universe) : LocallySmall U (UniverseType U)
  ≔ X Y ↦ ((Equiv (X .fst) (Y .fst), equiv_small U (X .fst) (Y .fst) (X .snd) (Y .snd)), universe_path_equiv U X Y)

{` Closure properties of essentially and locally small types. `}
def pi_essentially_small (U : Universe) (A : Type) (sA : U .small A) (B : A → Type)
  (h : (a : A) → EssentiallySmall U (B a)) : EssentiallySmall U ((a : A) → B a)
  ≔ (((a : A) → h a .fst .fst, U .pi_small A (a ↦ h a .fst .fst) sA (a ↦ h a .fst .snd)),
      pi_family_equiv A B (a ↦ h a .fst .fst) (a ↦ h a .snd))

def sigma_essentially_small (U : Universe) (A : Type) (hA : EssentiallySmall U A) (B : A → Type)
  (h : (a : A) → EssentiallySmall U (B a)) : EssentiallySmall U (Σ A B)
  ≔ ((Σ A (a ↦ h a .fst .fst), U .sigma_small A (a ↦ h a .fst .fst) (essentially_small_is_small U A hA) (a ↦ h a .fst .snd)),
      family_equiv A B (a ↦ h a .fst .fst) (a ↦ h a .snd))

def product_essentially_small (U : Universe) (A B : Type) (hA : EssentiallySmall U A) (hB : EssentiallySmall U B)
  : EssentiallySmall U (Product A B)
  ≔ sigma_essentially_small U A hA (_ ↦ B) (_ ↦ hB)

def sum_essentially_small (U : Universe) (A B : Type) (hA : EssentiallySmall U A) (hB : EssentiallySmall U B)
  : EssentiallySmall U (Sum A B)
  ≔ small_essentially_small U (Sum A B)
      (U .sum_small A B (essentially_small_is_small U A hA) (essentially_small_is_small U B hB))

def mere_essentially_small (U : Universe) (A : Type) (hA : EssentiallySmall U A) : EssentiallySmall U (Mere A)
  ≔ small_essentially_small U (Mere A) (U .trunc_small A (essentially_small_is_small U A hA))

def equiv_essentially_small (U : Universe) (A B : Type) (hA : EssentiallySmall U A) (hB : EssentiallySmall U B)
  : EssentiallySmall U (Equiv A B)
  ≔ small_essentially_small U (Equiv A B)
      (equiv_small U A B (essentially_small_is_small U A hA) (essentially_small_is_small U B hB))

{` If A : U and each B(x) is locally U-small, then Π_{x:A} B(x) is locally U-small. `}
def pi_locally_small (U : Universe) (A : Type) (sA : U .small A) (B : A → Type)
  (h : (a : A) → LocallySmall U (B a)) : LocallySmall U ((a : A) → B a)
  ≔ f g ↦ essentially_small_equiv U (Homotopy A B f g) (Id ((a : A) → B a) f g)
      (funext_equiv A B f g)
      (pi_essentially_small U A sA (a ↦ Id (B a) (f a) (g a)) (a ↦ h a (f a) (g a)))

def sigma_locally_small (U : Universe) (A : Type) (B : A → Type) (hA : LocallySmall U A)
  (hB : (a : A) → LocallySmall U (B a)) : LocallySmall U (Σ A B)
  ≔ u v ↦
    let S1 ≔ Σ (Id A (u .fst) (v .fst)) (p ↦ Id (B (v .fst)) (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd)) in
    let e1 ≔ canonical_inverse_equiv (SigmaPath A B u v) S1
      (family_equiv (Id A (u .fst) (v .fst)) (p ↦ Id B p (u .snd) (v .snd))
        (p ↦ Id (B (v .fst)) (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd))
        (p ↦ pathover_transport_equiv A B (u .fst) (v .fst) p (u .snd) (v .snd))) in
    essentially_small_equiv U S1 (Id (Σ A B) u v)
      (compose_equiv S1 (SigmaPath A B u v) (Id (Σ A B) u v) e1 (sigma_path_equiv A B u v))
      (sigma_essentially_small U (Id A (u .fst) (v .fst)) (hA (u .fst) (v .fst))
        (p ↦ Id (B (v .fst)) (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd))
        (p ↦ hB (v .fst) (transport A B (u .fst) (v .fst) p (u .snd)) (v .snd)))

def product_locally_small (U : Universe) (A B : Type) (hA : LocallySmall U A) (hB : LocallySmall U B)
  : LocallySmall U (Product A B)
  ≔ sigma_locally_small U A (_ ↦ B) hA (_ ↦ hB)

def subtype_locally_small (U : Universe) (A : Type) (P : A → Type) (hP : (a : A) → isProp (P a))
  (hA : LocallySmall U A) : LocallySmall U (Σ A P)
  ≔ u v ↦ essentially_small_equiv U (Id A (u .fst) (v .fst)) (Id (Σ A P) u v)
      (canonical_inverse_equiv (Id (Σ A P) u v) (Id A (u .fst) (v .fst)) (subtype_path_equiv A P hP u v))
      (hA (u .fst) (v .fst))

def paths_locally_small (U : Universe) (A : Type) (hA : LocallySmall U A) (x y : A) : LocallySmall U (Id A x y)
  ≔ essentially_small_locally_small U (Id A x y) (hA x y)

def locally_small_equiv (U : Universe) (A B : Type) (e : Equiv A B) (hA : LocallySmall U A) : LocallySmall U B
  ≔ x y ↦ essentially_small_equiv U
      (Id A (equiv_inverse_map A B e x) (equiv_inverse_map A B e y)) (Id B x y)
      (compose_equiv (Id A (equiv_inverse_map A B e x) (equiv_inverse_map A B e y))
        (Id B (e .map (equiv_inverse_map A B e x)) (e .map (equiv_inverse_map A B e y))) (Id B x y)
        (equivalence_on_paths A B e (equiv_inverse_map A B e x) (equiv_inverse_map A B e y))
        (id_to_equiv (Id B (e .map (equiv_inverse_map A B e x)) (e .map (equiv_inverse_map A B e y))) (Id B x y)
          (refl ((u v ↦ Id B u v) : B → B → Type) (equiv_counit A B e x) (equiv_counit A B e y))))
      (hA (equiv_inverse_map A B e x) (equiv_inverse_map A B e y))

{` def:Prop-Set, relative to a universe. `}
def prop_type_small (U : Universe) (X : Type) (s : U .small X) : U .small (isProp X)
  ≔ U .pi_small X (x ↦ (y : X) → Id X x y) s (x ↦ U .pi_small X (y ↦ Id X x y) s (y ↦ U .id_small X s x y))

def set_type_small (U : Universe) (X : Type) (s : U .small X) : U .small (isSet X)
  ≔ U .pi_small X (x ↦ (y : X) → isProp (Id X x y)) s
      (x ↦ U .pi_small X (y ↦ isProp (Id X x y)) s (y ↦ prop_type_small U (Id X x y) (U .id_small X s x y)))

def PropU (U : Universe) : Type ≔ Σ (UniverseType U) (X ↦ isProp (X .fst))
def SetU (U : Universe) : Type ≔ Σ (UniverseType U) (X ↦ isSet (X .fst))

def prop_family_embedding (A : Type) (B : A → Type) (hB : (a : A) → isProp (B a))
  : IsEmbedding (Σ A B) A (u ↦ u .fst)
  ≔ a ↦ hlevel_one_to_prop (BookFiber (Σ A B) A (u ↦ u .fst) a)
      (hlevel_equiv (suc. zero.) (B a) (BookFiber (Σ A B) A (u ↦ u .fst) a)
        (canonical_inverse_equiv (BookFiber (Σ A B) A (u ↦ u .fst) a) (B a) (projection_book_fiber_equiv A B a))
        (prop_to_hlevel_one (B a) (hB a)))

{` Both are subtypes of U. `}
def prop_u_subtype (U : Universe) : IsEmbedding (PropU U) (UniverseType U) (P ↦ P .fst)
  ≔ prop_family_embedding (UniverseType U) (X ↦ isProp (X .fst)) (X ↦ isprop_isprop (X .fst))

def set_u_subtype (U : Universe) : IsEmbedding (SetU U) (UniverseType U) (P ↦ P .fst)
  ≔ prop_family_embedding (UniverseType U) (X ↦ isSet (X .fst)) (X ↦ isset_isprop (X .fst))

{` Both are types in the next universe. `}
def prop_u_in_upper (N : NestedUniverses) : N .upper .small (PropU (N .lower))
  ≔ N .upper .sigma_small (UniverseType (N .lower)) (X ↦ isProp (X .fst)) (N .lower_in_upper)
      (X ↦ prop_type_small (N .upper) (X .fst) (N .cumulative (X .fst) (X .snd)))

def set_u_in_upper (N : NestedUniverses) : N .upper .small (SetU (N .lower))
  ≔ N .upper .sigma_small (UniverseType (N .lower)) (X ↦ isSet (X .fst)) (N .lower_in_upper)
      (X ↦ set_type_small (N .upper) (X .fst) (N .cumulative (X .fst) (X .snd)))

def prop_u_path_equiv (U : Universe) (P Q : PropU U)
  : Equiv (Id (PropU U) P Q) (Id Type (P .fst .fst) (Q .fst .fst))
  ≔ compose_equiv (Id (PropU U) P Q) (Id (UniverseType U) (P .fst) (Q .fst)) (Id Type (P .fst .fst) (Q .fst .fst))
      (subtype_path_equiv (UniverseType U) (X ↦ isProp (X .fst)) (X ↦ isprop_isprop (X .fst)) P Q)
      (subtype_path_equiv Type (U .small) (U .small_prop) (P .fst) (Q .fst))

def prop_u_locally_small (U : Universe) : LocallySmall U (PropU U)
  ≔ subtype_locally_small U (UniverseType U) (X ↦ isProp (X .fst)) (X ↦ isprop_isprop (X .fst)) (universe_locally_small U)

def set_u_locally_small (U : Universe) : LocallySmall U (SetU U)
  ≔ subtype_locally_small U (UniverseType U) (X ↦ isSet (X .fst)) (X ↦ isset_isprop (X .fst)) (universe_locally_small U)
