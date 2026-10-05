export "01-groups"

{` Blind statements, chapter 4, section "Infinity groups". `}

{` def:inftygps. `}
def BlindPtConnTypes : Type ≔ Σ Type (A ↦ Product A (Connected A))
def BlindInfGroup : Type ≔ Copy BlindPtConnTypes
def blind_inf_mkgroup (X : BlindPtConnTypes) : BlindInfGroup ≔ copy. X
def blind_inf_clf (G : BlindInfGroup) : BlindPtConnTypes ≔ copy_value BlindPtConnTypes G

{` def:classifyingspace. `}
def blind_inf_BG (G : BlindInfGroup) : Pointed ≔ (blind_inf_clf G .fst, blind_inf_clf G .snd .fst)
def blind_inf_shape (G : BlindInfGroup) : blind_inf_clf G .fst ≔ blind_inf_clf G .snd .fst

{` Definition (line 2378): the automorphism ∞-group. `}
def blind_inf_Aut (A : Type) (a : A) : BlindInfGroup
  ≔ blind_inf_mkgroup (NativeComponent A a, (blind_component_point A a, native_component_connected A a))

{` rem:autinfgp. `}
def blind_rem_universe_set_component_groupoid : Type
  ≔ (S : SetTypes) → isGroupoid (NativeComponent Type (S .fst))

def blind_group_to_infgroup (G : BlindGroup) : BlindInfGroup
  ≔ blind_inf_mkgroup (blind_B G .fst, (blind_shape G, blind_B G .snd .snd .fst))

def blind_rem_group_infgroup_injection : Type
  ≔ (G H : BlindGroup) →
    BookIsEquiv (Id BlindGroup G H) (Id BlindInfGroup (blind_group_to_infgroup G) (blind_group_to_infgroup H))
      (map_path BlindGroup BlindInfGroup blind_group_to_infgroup G H)

{` Definition (line 2400): homomorphisms of ∞-groups. `}
def BlindInfHom (G H : BlindInfGroup) : Type ≔ Copy (BookPointedMap (blind_inf_BG G) (blind_inf_BG H))
def blind_inf_mkhom (G H : BlindInfGroup) (k : BookPointedMap (blind_inf_BG G) (blind_inf_BG H)) : BlindInfHom G H ≔ copy. k
def blind_inf_Bhom (G H : BlindInfGroup) (f : BlindInfHom G H) : BookPointedMap (blind_inf_BG G) (blind_inf_BG H)
  ≔ copy_value (BookPointedMap (blind_inf_BG G) (blind_inf_BG H)) f

{` xca (line 779), "similarly for ∞-groups". `}
def blind_xca_change_basepoint_inf : Type
  ≔ (X : BlindPtConnTypes) (b : X .fst) →
    Mere (Id BlindInfGroup (blind_inf_mkgroup X) (blind_inf_mkgroup (X .fst, (b, X .snd .snd))))
