export "814-dihedral-bicycle-map"

{` Identifications in BD_n (structure identity principle used for
   con:bidirectional-bicycle, congp.tex:109).

   A path (S, X, f) = (S', X', f') in BD_n = Σ_{S:BΣ_2} (T_S)_{(X_S,f)} is the
   same as a pair of equivalences σ : S ≃ S', g : X ≃ X' with
   g(f_s x) = f'_{σ s}(g x) (dihedral_classifying_paths_equiv). The
   propositional parts (S being merely Fin 2, (X, f) being in the component)
   are split off by reassociating BD_n as a subtype of the type DFrame of
   triples (S, X, f) of sets S, X with f : S → X → X. The equivalence sends a
   path ℓ to the transports along its two set components (judgmentally, see
   dihedral_classifying_paths_equiv_two / _set). `}

def dframe_family (u : Product SetTypes SetTypes) : Type ≔ u .fst .fst → u .snd .fst → u .snd .fst

def DFrame : Type ≔ Σ (Product SetTypes SetTypes) dframe_family

def DFrameCommutes (S X S' X' : Type) (f : S → X → X) (f' : S' → X' → X') (σ : S → S') (g : X → X') : Type
  ≔ (s : S) (x : X) → Id X' (g (f s x)) (f' (σ s) (g x))

def DFrameEquivs (u u' : Product SetTypes SetTypes) : Type
  ≔ Product (Equiv (u .fst .fst) (u' .fst .fst)) (Equiv (u .snd .fst) (u' .snd .fst))

def DFrameIsos (w w' : DFrame) : Type
  ≔ Σ (DFrameEquivs (w .fst) (w' .fst))
      (e ↦ DFrameCommutes (w .fst .fst .fst) (w .fst .snd .fst) (w' .fst .fst .fst) (w' .fst .snd .fst)
        (w .snd) (w' .snd) (e .fst .map) (e .snd .map))

def dbc_path_endpoints_equiv (A : Type) (x x' : A) (hx : Id A x x') (y y' : A) (hy : Id A y y')
  : Equiv (Id A x y) (Id A x' y')
  ≔ J A x (x' _ ↦ Equiv (Id A x y) (Id A x' y'))
      (J A y (y' _ ↦ Equiv (Id A x y) (Id A x y')) (identity_equiv (Id A x y)) y' hy) x' hx

def dframe_refl_point_equiv (S X : Type) (f f' : S → X → X) (s : S) (x : X)
  : Equiv (Id X (f s x) (f' s x)) (Id X (refl X .trr (f s x)) (f' (refl S .trr s) (refl X .trr x)))
  ≔ dbc_path_endpoints_equiv X (f s x) (refl X .trr (f s x))
      (inverse X (refl X .trr (f s x)) (f s x) (transport_refl Type (Y ↦ Y) X (f s x)))
      (f' s x) (f' (refl S .trr s) (refl X .trr x))
      (refl f' (inverse S (refl S .trr s) s (transport_refl Type (Y ↦ Y) S s))
        (inverse X (refl X .trr x) x (transport_refl Type (Y ↦ Y) X x)))

def dframe_refl_letter_equiv (S X : Type) (f f' : S → X → X) (s : S)
  : Equiv (Id (X → X) (f s) (f' s)) ((x : X) → Id X (refl X .trr (f s x)) (f' (refl S .trr s) (refl X .trr x)))
  ≔ compose_equiv (Id (X → X) (f s) (f' s)) ((x : X) → Id X (f s x) (f' s x))
      ((x : X) → Id X (refl X .trr (f s x)) (f' (refl S .trr s) (refl X .trr x)))
      (canonical_inverse_equiv ((x : X) → Id X (f s x) (f' s x)) (Id (X → X) (f s) (f' s))
        (funext_equiv X (_ ↦ X) (f s) (f' s)))
      (pi_family_equiv X (x ↦ Id X (f s x) (f' s x))
        (x ↦ Id X (refl X .trr (f s x)) (f' (refl S .trr s) (refl X .trr x)))
        (x ↦ dframe_refl_point_equiv S X f f' s x))

def dframe_refl_equiv (S X : Type) (f f' : S → X → X)
  : Equiv (Id (S → X → X) f f') (DFrameCommutes S X S X f f' (refl S .trr) (refl X .trr))
  ≔ compose_equiv (Id (S → X → X) f f') ((s : S) → Id (X → X) (f s) (f' s))
      (DFrameCommutes S X S X f f' (refl S .trr) (refl X .trr))
      (canonical_inverse_equiv ((s : S) → Id (X → X) (f s) (f' s)) (Id (S → X → X) f f')
        (funext_equiv S (_ ↦ X → X) f f'))
      (pi_family_equiv S (s ↦ Id (X → X) (f s) (f' s))
        (s ↦ (x : X) → Id X (refl X .trr (f s x)) (f' (refl S .trr s) (refl X .trr x)))
        (s ↦ dframe_refl_letter_equiv S X f f' s))

{` Paths over p in the family of maps S → X → X are commutation squares
   for the transports along p. `}
def dframe_pathover_equiv (u u' : Product SetTypes SetTypes) (p : Id (Product SetTypes SetTypes) u u')
  (f : dframe_family u) (f' : dframe_family u')
  : Equiv (Id dframe_family p f f')
      (DFrameCommutes (u .fst .fst) (u .snd .fst) (u' .fst .fst) (u' .snd .fst) f f' (p .fst .fst .trr) (p .snd .fst .trr))
  ≔ J (Product SetTypes SetTypes) u
      (u' p ↦ (f' : dframe_family u') → Equiv (Id dframe_family p f f')
        (DFrameCommutes (u .fst .fst) (u .snd .fst) (u' .fst .fst) (u' .snd .fst) f f' (p .fst .fst .trr) (p .snd .fst .trr)))
      (f' ↦ dframe_refl_equiv (u .fst .fst) (u .snd .fst) f f') u' p f'

def dframe_base_paths_equiv (u u' : Product SetTypes SetTypes)
  : Equiv (Id (Product SetTypes SetTypes) u u') (DFrameEquivs u u')
  ≔ compose_equiv (Id (Product SetTypes SetTypes) u u')
      (Product (Id SetTypes (u .fst) (u' .fst)) (Id SetTypes (u .snd) (u' .snd))) (DFrameEquivs u u')
      (quasi_inverse_equiv (Id (Product SetTypes SetTypes) u u')
        (Product (Id SetTypes (u .fst) (u' .fst)) (Id SetTypes (u .snd) (u' .snd)))
        (p ↦ (p .fst, p .snd)) (q ↦ (q .fst, q .snd)) (p ↦ refl p) (q ↦ refl q))
      (product_equiv (Id SetTypes (u .fst) (u' .fst)) (Id SetTypes (u .snd) (u' .snd))
        (Equiv (u .fst .fst) (u' .fst .fst)) (Equiv (u .snd .fst) (u' .snd .fst))
        (set_paths_transport_equiv (u .fst) (u' .fst)) (set_paths_transport_equiv (u .snd) (u' .snd)))

def dframe_commutes_family (w w' : DFrame) (e : DFrameEquivs (w .fst) (w' .fst)) : Type
  ≔ DFrameCommutes (w .fst .fst .fst) (w .fst .snd .fst) (w' .fst .fst .fst) (w' .fst .snd .fst)
      (w .snd) (w' .snd) (e .fst .map) (e .snd .map)

{` Structure identity principle for DFrame. `}
def dframe_paths_equiv (w w' : DFrame) : Equiv (Id DFrame w w') (DFrameIsos w w')
  ≔ let T ≔ dframe_base_paths_equiv (w .fst) (w' .fst) in
    let C ≔ dframe_commutes_family w w' in
    compose_equiv (Id DFrame w w') (SigmaPath (Product SetTypes SetTypes) dframe_family w w') (DFrameIsos w w')
      (canonical_inverse_equiv (SigmaPath (Product SetTypes SetTypes) dframe_family w w') (Id DFrame w w')
        (sigma_path_equiv (Product SetTypes SetTypes) dframe_family w w'))
      (compose_equiv (SigmaPath (Product SetTypes SetTypes) dframe_family w w')
        (Σ (Id (Product SetTypes SetTypes) (w .fst) (w' .fst)) (p ↦ C (T .map p)))
        (DFrameIsos w w')
        (family_equiv (Id (Product SetTypes SetTypes) (w .fst) (w' .fst))
          (p ↦ Id dframe_family p (w .snd) (w' .snd)) (p ↦ C (T .map p))
          (p ↦ dframe_pathover_equiv (w .fst) (w' .fst) p (w .snd) (w' .snd)))
        (sigma_reindex_equiv (Id (Product SetTypes SetTypes) (w .fst) (w' .fst)) (DFrameEquivs (w .fst) (w' .fst)) T C))

{` BD_n as a subtype of DFrame. `}
def dbc_frame (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h) : DFrame
  ≔ ((x .fst .fst, x .snd .fst .fst), x .snd .fst .snd)

def DihedralFrameProps (H : Subtypes Int) (h : IntegerSubgroupLaws H) (w : DFrame) : Type
  ≔ Σ (Mere (Id SetTypes (dihedral_two_shape .fst) (w .fst .fst)))
      (ms ↦ Mere (Id (S2C3Type (w .fst .fst, ms)) (dihedral_point (w .fst .fst, ms) H h) (w .fst .snd, w .snd)))

def dihedral_frame_props_prop (H : Subtypes Int) (h : IntegerSubgroupLaws H) (w : DFrame)
  : isProp (DihedralFrameProps H h w)
  ≔ sigma_prop (Mere (Id SetTypes (dihedral_two_shape .fst) (w .fst .fst)))
      (ms ↦ Mere (Id (S2C3Type (w .fst .fst, ms)) (dihedral_point (w .fst .fst, ms) H h) (w .fst .snd, w .snd)))
      (mere_isprop (Id SetTypes (dihedral_two_shape .fst) (w .fst .fst)))
      (ms ↦ mere_isprop (Id (S2C3Type (w .fst .fst, ms)) (dihedral_point (w .fst .fst, ms) H h) (w .fst .snd, w .snd)))

def DihedralFrameSubtype (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type ≔ Σ DFrame (DihedralFrameProps H h)

def dbc_regroup (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x : DihedralClassifyingType H h)
  : DihedralFrameSubtype H h
  ≔ (dbc_frame H h x, (x .fst .snd, x .snd .snd))

def dbc_ungroup (H : Subtypes Int) (h : IntegerSubgroupLaws H) (v : DihedralFrameSubtype H h)
  : DihedralClassifyingType H h
  ≔ ((v .fst .fst .fst, v .snd .fst), ((v .fst .fst .snd, v .fst .snd), v .snd .snd))

def dbc_regroup_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (DihedralClassifyingType H h) (DihedralFrameSubtype H h)
  ≔ quasi_inverse_equiv (DihedralClassifyingType H h) (DihedralFrameSubtype H h)
      (dbc_regroup H h) (dbc_ungroup H h) (x ↦ refl x) (v ↦ refl v)

{` Paths in BD_n ≃ pairs of equivalences commuting with f. `}
def dihedral_classifying_paths_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x y : DihedralClassifyingType H h)
  : Equiv (Id (DihedralClassifyingType H h) x y) (DFrameIsos (dbc_frame H h x) (dbc_frame H h y))
  ≔ compose_equiv (Id (DihedralClassifyingType H h) x y) (Id DFrame (dbc_frame H h x) (dbc_frame H h y))
      (DFrameIsos (dbc_frame H h x) (dbc_frame H h y))
      (compose_equiv (Id (DihedralClassifyingType H h) x y)
        (Id (DihedralFrameSubtype H h) (dbc_regroup H h x) (dbc_regroup H h y))
        (Id DFrame (dbc_frame H h x) (dbc_frame H h y))
        (equivalence_on_paths (DihedralClassifyingType H h) (DihedralFrameSubtype H h) (dbc_regroup_equiv H h) x y)
        (subtype_path_equiv DFrame (DihedralFrameProps H h) (dihedral_frame_props_prop H h)
          (dbc_regroup H h x) (dbc_regroup H h y)))
      (dframe_paths_equiv (dbc_frame H h x) (dbc_frame H h y))

{` The equivalence sends ℓ to the transports along its components. `}
def dihedral_classifying_paths_equiv_two (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x y : DihedralClassifyingType H h)
  (l : Id (DihedralClassifyingType H h) x y) (s : two_set_carrier (x .fst))
  : Id (two_set_carrier (y .fst)) (dihedral_classifying_paths_equiv H h x y .map l .fst .fst .map s) (l .fst .fst .fst .trr s)
  ≔ refl (l .fst .fst .fst .trr s)

def dihedral_classifying_paths_equiv_set (H : Subtypes Int) (h : IntegerSubgroupLaws H) (x y : DihedralClassifyingType H h)
  (l : Id (DihedralClassifyingType H h) x y) (u : x .snd .fst .fst .fst)
  : Id (y .snd .fst .fst .fst) (dihedral_classifying_paths_equiv H h x y .map l .fst .snd .map u) (l .snd .fst .fst .fst .trr u)
  ≔ refl (l .snd .fst .fst .fst .trr u)
