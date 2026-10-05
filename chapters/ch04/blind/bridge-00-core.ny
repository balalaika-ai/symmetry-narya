export "../../../src/410-pointed-connected-groupoids"
export "03-homs"

{` Bridges for group.tex: the definition bridges shared by all
   bridge files. The blind U^{=1}_* is a right-nested Σ-type, ours a
   four-field record; the blind Group and Hom are module 16's Copy data
   type, ours one-field records. All translations are inverse with refl
   round trips (for Copy after matching on copy.). BlindUSym G, the blind
   product, inverse and unit, and BlindIsAb agree with ours on the nose. `}

{` def:pt-conn-groupoid. `}
def bridge_pcg (X : BlindPtConnGroupoid) : PointedConnectedGroupoid
  ≔ (X .fst, X .snd .fst, X .snd .snd .fst, X .snd .snd .snd)

def bridge_pcg_inv (X : PointedConnectedGroupoid) : BlindPtConnGroupoid
  ≔ (X .carrier, (X .point, (X .connected, X .groupoid)))

def bridge_def_pt_conn_groupoid : Equiv BlindPtConnGroupoid PointedConnectedGroupoid
  ≔ quasi_inverse_equiv BlindPtConnGroupoid PointedConnectedGroupoid bridge_pcg bridge_pcg_inv
      (X ↦ refl X) (X ↦ refl X)

{` def:typegroup, def:classifying-type. `}
def bridge_g (G : BlindGroup) : Group ≔ mkgroup (bridge_pcg (blind_B G))

def bridge_g_inv (G : Group) : BlindGroup ≔ blind_mkgroup (bridge_pcg_inv (group_B G))

def bridge_g_eta : (G : BlindGroup) → Id BlindGroup (bridge_g_inv (bridge_g G)) G
  ≔ [ copy. X ↦ refl (blind_mkgroup X) ]

def bridge_def_group : Equiv BlindGroup Group
  ≔ quasi_inverse_equiv BlindGroup Group bridge_g bridge_g_inv bridge_g_eta (G ↦ refl G)

def bridge_def_mkgroup (X : BlindPtConnGroupoid) : Id Group (bridge_g (blind_mkgroup X)) (mkgroup (bridge_pcg X))
  ≔ refl (mkgroup (bridge_pcg X))

def bridge_def_bg (G : BlindGroup) : Id Pointed (blind_BG G) (BG (bridge_g G)) ≔ refl (blind_BG G)

def bridge_def_shape (G : BlindGroup) : Id (blind_B G .fst) (blind_shape G) (shape (bridge_g G))
  ≔ refl (blind_shape G)

{` def:looptype, def:group-symmetries, def:finite-group, def:abgp: ours on the nose. `}
def bridge_def_loops (X : Pointed) : Id Pointed (blind_loops X) (Omega X) ≔ refl (Omega X)

def bridge_def_usym (G : BlindGroup) : Id Type (BlindUSym G) (USym (bridge_g G)) ≔ refl (BlindUSym G)

def bridge_def_finite_group (G : BlindGroup) : Id Type (BlindIsFiniteGroup G) (IsFiniteGroup (bridge_g G))
  ≔ refl (BlindIsFiniteGroup G)

def bridge_def_group_card (G : BlindGroup) (h : BlindIsFiniteGroup G)
  : Id Nat (blind_group_card G h) (group_card (bridge_g G) h)
  ≔ refl (blind_group_card G h)

def bridge_def_isab (G : BlindGroup) : Id Type (BlindIsAb G) (IsAbelian (bridge_g G)) ≔ refl (BlindIsAb G)

def bridge_abg_eta (G : BlindGroup) (h : BlindIsAb G)
  : Id BlindAbGroup (bridge_g_inv (bridge_g G), h) (G, h)
  ≔ match G [ copy. X ↦ refl ((blind_mkgroup X, h) : BlindAbGroup) ]

def bridge_def_abgroup : Equiv BlindAbGroup AbelianGroup
  ≔ quasi_inverse_equiv BlindAbGroup AbelianGroup (A ↦ (bridge_g (A .fst), A .snd))
      (A ↦ (bridge_g_inv (A .fst), A .snd))
      (A ↦ bridge_abg_eta (A .fst) (A .snd)) (A ↦ refl A)

def bridge_def_usym_ops (G : BlindGroup) (g h : BlindUSym G)
  : Product (Id (BlindUSym G) (blind_usym_mul G g h) (usym_mul (bridge_g G) g h))
      (Product (Id (BlindUSym G) (blind_usym_inv G g) (usym_inv (bridge_g G) g))
        (Id (BlindUSym G) (blind_usym_unit G) (usym_unit (bridge_g G))))
  ≔ (refl (blind_usym_mul G g h), (refl (blind_usym_inv G g), refl (blind_usym_unit G)))

{` Paths of groups. `}
def bridge_group_paths (G H : BlindGroup) : Equiv (Id BlindGroup G H) (Id Group (bridge_g G) (bridge_g H))
  ≔ equivalence_on_paths BlindGroup Group bridge_def_group G H

def bridge_gpath (G H : BlindGroup) (p : Id Group (bridge_g G) (bridge_g H)) : Id BlindGroup G H
  ≔ match G [ copy. X ↦ match H [ copy. Y ↦
      refl bridge_g_inv p ] ]

{` def:automorphism-group: the blind groupoid witness of the component is
   a different proof term, so the groups agree up to a path. `}
def bridge_def_component_point (A : Type) (a : A)
  : Id (NativeComponent A a) (blind_component_point A a) (component_point A a)
  ≔ refl (component_point A a)

def bridge_aut (A : Type) (hA : isGroupoid A) (a : A)
  : Id Group (bridge_g (blind_Aut A hA a)) (automorphism_group A hA a)
  ≔ (classifying ≔ pcg_witnesses_unique (NativeComponent A a) (component_point A a)
      (native_component_connected A a) (native_component_connected A a)
      (blind_component_groupoid A hA a) (component_groupoid A hA a))

def bridge_def_aut (A : Type) (hA : isGroupoid A) (a : A)
  : Id BlindGroup (blind_Aut A hA a) (bridge_g_inv (automorphism_group A hA a))
  ≔ bridge_gpath (blind_Aut A hA a) (bridge_g_inv (automorphism_group A hA a)) (bridge_aut A hA a)

{` def:grouphomomorphism. blind_BG G is BG (bridge_g G) judgmentally. `}
def bridge_h (G H : BlindGroup) (f : BlindHom G H) : GroupHom (bridge_g G) (bridge_g H)
  ≔ mkhom (bridge_g G) (bridge_g H) (blind_Bhom G H f)

def bridge_h_inv (G H : BlindGroup) (f : GroupHom (bridge_g G) (bridge_g H)) : BlindHom G H
  ≔ blind_mkhom G H (hom_B (bridge_g G) (bridge_g H) f)

def bridge_def_hom (G H : BlindGroup) : Equiv (BlindHom G H) (GroupHom (bridge_g G) (bridge_g H))
  ≔ quasi_inverse_equiv (BlindHom G H) (GroupHom (bridge_g G) (bridge_g H)) (bridge_h G H) (bridge_h_inv G H)
      [ copy. k ↦ refl (blind_mkhom G H k) ] (f ↦ refl f)

{` def:loops-map: the blind bracketing (k_pt · ap k p) · k_pt⁻¹ versus
   ours k_pt · (ap k p · k_pt⁻¹). `}
def bridge_loops_map (X Y : Pointed) (k : BookPointedMap X Y) (l : Loop X)
  : Id (Loop Y) (blind_loops_map X Y k l) (loops_map X Y k l)
  ≔ concat_assoc (Y .carrier) (Y .point) (k .fst (X .point)) (k .fst (X .point)) (Y .point)
      (k .snd) (refl (k .fst) l) (inverse (Y .carrier) (Y .point) (k .fst (X .point)) (k .snd))

def bridge_def_loops_map (X Y : Pointed) (k : BookPointedMap X Y)
  : Id (Loop X → Loop Y) (blind_loops_map X Y k) (loops_map X Y k)
  ≔ funext (Loop X) (_ ↦ Loop Y) (blind_loops_map X Y k) (loops_map X Y k) (bridge_loops_map X Y k)

def bridge_usym_hom (G H : BlindGroup) (f : BlindHom G H) (g : BlindUSym G)
  : Id (BlindUSym H) (blind_usym_hom G H f g) (usym_hom (bridge_g G) (bridge_g H) (bridge_h G H f) g)
  ≔ bridge_loops_map (blind_BG G) (blind_BG H) (blind_Bhom G H f) g

def bridge_def_usym_hom (G H : BlindGroup) (f : BlindHom G H)
  : Id (BlindUSym G → BlindUSym H) (blind_usym_hom G H f) (usym_hom (bridge_g G) (bridge_g H) (bridge_h G H f))
  ≔ bridge_def_loops_map (blind_BG G) (blind_BG H) (blind_Bhom G H f)

{` def:groupisomorphism, def:identity-group-homomorphism,
   def:group-homomorphism-composition: ours on the nose. `}
def bridge_def_is_iso (G H : BlindGroup) (f : BlindHom G H)
  : Id Type (BlindIsIso G H f) (IsGroupIso (bridge_g G) (bridge_g H) (bridge_h G H f))
  ≔ refl (BlindIsIso G H f)

def bridge_iso_eta (G H : BlindGroup) (f : BlindHom G H) (i : BlindIsIso G H f)
  : Id (BlindIso G H) (bridge_h_inv G H (bridge_h G H f), i) (f, i)
  ≔ match f [ copy. k ↦ refl ((blind_mkhom G H k, i) : BlindIso G H) ]

def bridge_def_iso (G H : BlindGroup) : Equiv (BlindIso G H) (GroupIso (bridge_g G) (bridge_g H))
  ≔ quasi_inverse_equiv (BlindIso G H) (GroupIso (bridge_g G) (bridge_g H))
      (f ↦ (bridge_h G H (f .fst), f .snd)) (f ↦ (bridge_h_inv G H (f .fst), f .snd))
      (f ↦ bridge_iso_eta G H (f .fst) (f .snd)) (f ↦ refl f)

def bridge_def_id_hom (G : BlindGroup)
  : Id (GroupHom (bridge_g G) (bridge_g G)) (bridge_h G G (blind_id_hom G)) (group_hom_id (bridge_g G))
  ≔ refl (group_hom_id (bridge_g G))

def bridge_def_hom_compose (G G' G'' : BlindGroup) (f : BlindHom G G') (f' : BlindHom G' G'')
  : Id (GroupHom (bridge_g G) (bridge_g G''))
      (bridge_h G G'' (blind_hom_compose G G' G'' f f'))
      (group_hom_compose (bridge_g G) (bridge_g G') (bridge_g G'') (bridge_h G G' f) (bridge_h G' G'' f'))
  ≔ refl (bridge_h G G'' (blind_hom_compose G G' G'' f f'))

{` Paths of homomorphisms. `}
def bridge_hpath (G H : BlindGroup) (f f' : BlindHom G H)
  (p : Id (GroupHom (bridge_g G) (bridge_g H)) (bridge_h G H f) (bridge_h G H f')) : Id (BlindHom G H) f f'
  ≔ match f [ copy. k ↦ match f' [ copy. k' ↦ refl (bridge_h_inv G H) p ] ]

def bridge_gpath_inj (G H : BlindGroup) (p p' : Id Group (bridge_g G) (bridge_g H))
  (h : Id (Id BlindGroup G H) (bridge_gpath G H p) (bridge_gpath G H p'))
  : Id (Id Group (bridge_g G) (bridge_g H)) p p'
  ≔ match G [ copy. X ↦ match H [ copy. Y ↦
      map_path (Id BlindGroup (blind_mkgroup X) (blind_mkgroup Y)) (Id Group (bridge_g (blind_mkgroup X)) (bridge_g (blind_mkgroup Y)))
        (map_path BlindGroup Group bridge_g (blind_mkgroup X) (blind_mkgroup Y))
        (bridge_gpath (blind_mkgroup X) (blind_mkgroup Y) p) (bridge_gpath (blind_mkgroup X) (blind_mkgroup Y) p') h ] ]

{` Automorphism groups with possibly different groupoid witnesses. `}
def bridge_aut_any (A : Type) (hA hA' : isGroupoid A) (a : A)
  : Id Group (bridge_g (blind_Aut A hA a)) (automorphism_group A hA' a)
  ≔ (classifying ≔ pcg_witnesses_unique (NativeComponent A a) (component_point A a)
      (native_component_connected A a) (native_component_connected A a)
      (blind_component_groupoid A hA a) (component_groupoid A hA' a))

{` A blind group path from a zig-zag of our group paths. `}
def bridge_gpath_via (G H : BlindGroup) (A B : Group) (p : Id Group (bridge_g G) A) (q : Id Group A B)
  (r : Id Group (bridge_g H) B) : Id BlindGroup G H
  ≔ bridge_gpath G H (concat Group (bridge_g G) B (bridge_g H) (concat Group (bridge_g G) A B p q)
      (inverse Group (bridge_g H) B r))

{` A pointed path from an equivalence and a pointing path. `}
def bridge_pointed_path (A B : Type) (e : Equiv A B) (a : A) (b : B) (r : Id B (e .map a) b)
  : Id Pointed (A, a) (B, b)
  ≔ concat Pointed (A, a) (B, e .map a) (B, b) (ua A B e, ua A B e .liftr a)
      (map_path B Pointed (y ↦ (B, y)) (e .map a) b r)
