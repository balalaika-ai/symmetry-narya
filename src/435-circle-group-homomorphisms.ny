export "404-group-examples"

{` ex:Zinitial and lem:Znatural (group.tex 1270-1328), for an arbitrary
   circle C, Z ≔ circle_group C = mkgroup (S¹, base) (module 404). The
   constructed circle gives integer_group (module 405) as the instance
   C ≔ constructed_circle. "Z is a free group with one generator":
   homomorphisms Z → G correspond to elements of USym G via the image of
   loop. `}

{` ev_BG : ((S¹, base) →* BG) ≃ USym G, from cor:circle-loopspace
   (pointed_circle_universal_property, module 129); its map is literally
   (f÷, f_pt) ↦ Ω(f÷, f_pt)(loop). `}
def circle_hom_ev (C : CircleSignature) (G : Group) : Equiv (BookPointedMap (circle_pointed C) (BG G)) (USym G)
  ≔ pointed_circle_universal_property C (BG G .carrier) (shape G)

def circle_hom_ev_map (C : CircleSignature) (G : Group) (f : BookPointedMap (circle_pointed C) (BG G))
  : Id (USym G) (circle_hom_ev C G .map f) (loops_map (circle_pointed C) (BG G) f (C .loop))
  ≔ refl (loops_map (circle_pointed C) (BG G) f (C .loop))

def circle_hom_ev_book (C : CircleSignature) (G : Group) : BookEquiv (BookPointedMap (circle_pointed C) (BG G)) (USym G)
  ≔ book_equivalence (BookPointedMap (circle_pointed C) (BG G)) (USym G) (circle_hom_ev C G)

{` "an equivalence of sets": both sides are sets. `}
def circle_pointed_maps_set (C : CircleSignature) (G : Group) : isSet (BookPointedMap (circle_pointed C) (BG G))
  ≔ pointed_maps_set (circle_pointed C) (BG G) (native_circle_connected C) (bg_groupoid G)

{` "The domain of this equivalence classifies Hom(Z, G)": Hom(Z, G) ≃ USym G,
   evaluating USym f at loop : USym Z. `}
def circle_group_hom_ev (C : CircleSignature) (G : Group) : Equiv (GroupHom (circle_group C) G) (USym G)
  ≔ compose_equiv (GroupHom (circle_group C) G) (BookPointedMap (circle_pointed C) (BG G)) (USym G)
      (group_hom_classifying_equiv (circle_group C) G) (circle_hom_ev C G)

def circle_group_hom_ev_map (C : CircleSignature) (G : Group) (f : GroupHom (circle_group C) G)
  : Id (USym G) (circle_group_hom_ev C G .map f) (usym_hom (circle_group C) G f (circle_group_loop C))
  ≔ refl (usym_hom (circle_group C) G f (circle_group_loop C))

{` The inverse ve_BG (the footnote inverse of module 129): ve(g) is
   circle recursion on (sh_G, g). The book's judgmental ve(g)(base) ≡ sh_G
   and pointing path refl become the base identification of the circle
   signature and its inverse: ve(g) is pointed by (ve(g)(base) = sh_G)⁻¹,
   which is refl whenever the base computation is. ve(g)(loop) = g holds
   over the base identification (circle_hom_ve_loop_over), and as Ω ve(g)
   (loop) = g (circle_hom_ve_loop). `}
def circle_hom_ve (C : CircleSignature) (G : Group) (g : USym G) : BookPointedMap (circle_pointed C) (BG G)
  ≔ pointed_circle_loop_rec C (BG G .carrier) (shape G) g

def circle_hom_ve_base (C : CircleSignature) (G : Group) (g : USym G)
  : Id (BG G .carrier) (circle_hom_ve C G g .fst (C .base)) (shape G)
  ≔ circle_rec_beta C (BG G .carrier) (shape G, g) .fst

def circle_hom_ve_point (C : CircleSignature) (G : Group) (g : USym G)
  : Id (Id (BG G .carrier) (shape G) (circle_hom_ve C G g .fst (C .base))) (circle_hom_ve C G g .snd)
      (inverse (BG G .carrier) (circle_hom_ve C G g .fst (C .base)) (shape G) (circle_hom_ve_base C G g))
  ≔ refl (circle_hom_ve C G g .snd)

def circle_hom_ve_loop_over (C : CircleSignature) (G : Group) (g : USym G)
  : Id ((x ↦ Id (BG G .carrier) x x) : BG G .carrier → Type) (circle_hom_ve_base C G g)
      (refl (circle_hom_ve C G g .fst) (C .loop)) g
  ≔ circle_rec_beta C (BG G .carrier) (shape G, g) .snd

def circle_hom_ve_loop (C : CircleSignature) (G : Group) (g : USym G)
  : Id (USym G) (loops_map (circle_pointed C) (BG G) (circle_hom_ve C G g) (C .loop)) g
  ≔ pointed_circle_loop_rec_beta C (BG G .carrier) (shape G) g

def circle_hom_ve_ev (C : CircleSignature) (G : Group) (f : BookPointedMap (circle_pointed C) (BG G))
  : Id (BookPointedMap (circle_pointed C) (BG G)) (circle_hom_ve C G (circle_hom_ev C G .map f)) f
  ≔ pointed_circle_loop_rec_eta C (BG G .carrier) (shape G) f

{` The homomorphism Z → G sending loop to g. `}
def circle_group_hom_from_symmetry (C : CircleSignature) (G : Group) (g : USym G) : GroupHom (circle_group C) G
  ≔ mkhom (circle_group C) G (circle_hom_ve C G g)

def circle_group_hom_from_symmetry_loop (C : CircleSignature) (G : Group) (g : USym G)
  : Id (USym G) (usym_hom (circle_group C) G (circle_group_hom_from_symmetry C G g) (circle_group_loop C)) g
  ≔ circle_hom_ve_loop C G g

{` Litmus: the identity of Z evaluates to loop, the trivial homomorphism
   Z → G (constant at sh_G, pointed by refl) to e. `}
def circle_group_hom_ev_identity (C : CircleSignature)
  : Id (USym (circle_group C)) (circle_group_hom_ev C (circle_group C) .map (group_hom_id (circle_group C)))
      (circle_group_loop C)
  ≔ usym_hom_id (circle_group C) (circle_group_loop C)

def circle_group_hom_ev_trivial (C : CircleSignature) (G : Group)
  : Id (USym G) (circle_group_hom_ev C G .map (mkhom (circle_group C) G (_ ↦ shape G, refl (shape G)))) (usym_unit G)
  ≔ loop_conjugate_at_refl (BG G .carrier) (shape G) (refl (shape G))

{` lem:Znatural: ev_H(f ∘ k) = USym f (ev_G(k)) for f : Hom(G, H),
   k : Hom(Z, G), by cor:USym-compose; pointwise and as a commuting square. `}
def circle_group_hom_ev_natural (C : CircleSignature) (G H : Group) (f : GroupHom G H) (k : GroupHom (circle_group C) G)
  : Id (USym H) (circle_group_hom_ev C H .map (group_hom_compose (circle_group C) G H k f))
      (usym_hom G H f (circle_group_hom_ev C G .map k))
  ≔ loops_map_compose_pointwise (BG (circle_group C)) (BG G) (BG H) (hom_B (circle_group C) G k) (hom_B G H f) (C .loop)

def circle_group_hom_ev_natural_square (C : CircleSignature) (G H : Group) (f : GroupHom G H)
  : Id (GroupHom (circle_group C) G → USym H)
      (k ↦ circle_group_hom_ev C H .map (group_hom_compose (circle_group C) G H k f))
      (k ↦ usym_hom G H f (circle_group_hom_ev C G .map k))
  ≔ funext (GroupHom (circle_group C) G) (_ ↦ USym H)
      (k ↦ circle_group_hom_ev C H .map (group_hom_compose (circle_group C) G H k f))
      (k ↦ usym_hom G H f (circle_group_hom_ev C G .map k))
      (circle_group_hom_ev_natural C G H f)
