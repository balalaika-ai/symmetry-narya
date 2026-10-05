{` Blind statements for chapter 9 (symmetry.tex, input at the end of subgroups.tex), section
   "More about automorphisms": def:center and thm:hom-mod-conj (for groups, i.e. 1-groups). `}
export "01-epi-mono"

{` Bunch ≔ the type of connected groupoids. `}
def BlindBunch : Type ≔ Σ Type (A ↦ Product (Connected A) (isGroupoid A))

{` bunch(G) ≔ BG÷ : Bunch. `}
def blind_bunch (G : Group) : BlindBunch ≔ (BG G .carrier, (bg_connected G, bg_groupoid G))

{` def:center. Z(G) ≔ Π_{z:BG} (z = z). `}
def BlindCenter (G : Group) : Type ≔ (z : BG G .carrier) → Id (BG G .carrier) z z

{` def:center: Z(G) is the type of fixed points of the adjoint action of G on itself. `}
def blind_center_adjoint_fixed : Type
  ≔ (G : Group) → Id Type (BlindCenter G) (InvariantMaps G (adjoint_gset G))

{` def:center: Z(G) is equivalent to the automorphisms of the identity of bunch(G) (id = id in BG÷ → BG÷). `}
def blind_center_aut_id : Type
  ≔ (G : Group) → Equiv (BlindCenter G) (Id (BG G .carrier → BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier)))

{` BZ(G) ≔ Σ_{f : BG → BG} ‖f ~ id‖, pointed at (id, |refl|). `}
def BlindBZ (G : Group) : Type
  ≔ Σ (BG G .carrier → BG G .carrier)
      (f ↦ Mere (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) f (identity (BG G .carrier))))

def blind_BZ_point (G : Group) : BlindBZ G
  ≔ (identity (BG G .carrier),
     mere (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier))) (z ↦ refl z))

def blind_BZ_pointed (G : Group) : Pointed ≔ (BlindBZ G, blind_BZ_point G)

{` def:center: Z(G) (pointed at z ↦ refl z) is the loop type of BZ(G). `}
def blind_center_loops_BZ : Type
  ≔ (G : Group) → BookPointedEquiv (BlindCenter G, (z ↦ refl z)) (Omega (blind_BZ_pointed G))

{` B²Z(G) ≔ Σ_{X:Bunch} ‖bunch(G) = X‖₀, pointed at (bunch(G), |refl|₀). `}
def BlindB2Z (G : Group) : Type ≔ Σ BlindBunch (X ↦ SetTrunc (Id BlindBunch (blind_bunch G) X))

def blind_B2Z_pointed (G : Group) : Pointed
  ≔ (BlindB2Z G, (blind_bunch G, set_trunc (Id BlindBunch (blind_bunch G) (blind_bunch G)) (refl (blind_bunch G))))

{` def:center: BZ(G) is the loop type of the pointed, connected type B²Z(G). `}
def blind_BZ_loops_B2Z : Type
  ≔ (G : Group) → BookPointedEquiv (blind_BZ_pointed G) (Omega (blind_B2Z_pointed G))

def blind_B2Z_connected : Type ≔ (G : Group) → Connected (BlindB2Z G)

{` def:center: this gives Z(G) the structure of an abelian group (the center): BZ(G) is a connected groupoid
   and the resulting group mkgroup(BZ(G)) is abelian. `}
def blind_center_abelian_group : Type
  ≔ (G : Group)
    → Σ (Connected (BlindBZ G)) (c ↦
        Σ (isGroupoid (BlindBZ G)) (gpd ↦ IsAbelian (mkgroup (BlindBZ G, blind_BZ_point G, c, gpd))))

{` thm:hom-mod-conj. BInn(H) ≔ Σ_{K:Group} ‖bunch(H) = bunch(K)‖₀, pointed at (H, |refl|₀). `}
def BlindBInnSym (H : Group) : Type ≔ Σ Group (K ↦ SetTrunc (Id BlindBunch (blind_bunch H) (blind_bunch K)))

def blind_BInn_sym_point (H : Group) : BlindBInnSym H
  ≔ (H, set_trunc (Id BlindBunch (blind_bunch H) (blind_bunch H)) (refl (blind_bunch H)))

{` The action of Inn(H): X⟨K,φ⟩ ≔ ‖Hom(G,K)‖₀ (≡ ‖BG →* BK‖₀). `}
def blind_hom_mod_conj_family (G H : Group) (u : BlindBInnSym H) : Type ≔ SetTrunc (GroupHom G (u .fst))

{` thm:hom-mod-conj: the acted-on set at the shape is the set of homomorphisms ‖BG →* BH‖₀. `}
def blind_hom_mod_conj_fiber : Type
  ≔ (G H : Group)
    → Equiv (blind_hom_mod_conj_family G H (blind_BInn_sym_point H)) (SetTrunc (BookPointedMap (BG G) (BG H)))

{` thm:hom-mod-conj: ‖BG÷ → BH÷‖₀ ≃ ‖(‖BG →* BH‖₀)_{hInn(H)}‖₀. `}
def blind_hom_mod_conj : Type
  ≔ (G H : Group)
    → BookEquiv (SetTrunc (BG G .carrier → BG H .carrier))
        (SetTrunc (Σ (BlindBInnSym H) (blind_hom_mod_conj_family G H)))
