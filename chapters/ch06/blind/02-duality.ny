export "01-wild-cats"
export "../../../src/502-subgroups"

{` Blind statements, chapter 6, section "Abstract notions and duality",
   plus the categories of sets and of groups listed after def:category. `}

{` The category of sets (objects SetTypes, arrows functions). `}
def blind_set_precat : BlindPrecat
  ≔ ((SetTypes, (A B ↦ A .fst → B .fst), (A ↦ x ↦ x), (A B C g f ↦ x ↦ g (f x)),
      (A B f ↦ refl f), (A B f ↦ refl f), (A B C D f g h ↦ refl (x ↦ h (g (f x))))),
     (A B ↦ pi_set (A .fst) (_ ↦ B .fst) (_ ↦ B .snd)))

{` The category of groups (objects Group, arrows GroupHom; g ∘ f is
   group_hom_compose _ _ _ f g). `}
def blind_group_precat : BlindPrecat
  ≔ ((Group, GroupHom, group_hom_id, (G H K g f ↦ group_hom_compose G H K f g),
      (G H f ↦ group_hom_compose_id G H f), (G H f ↦ group_hom_id_compose G H f),
      (G H K L f g h ↦ group_hom_compose_assoc G H K L f g h)),
     group_hom_set)

{` def:terminal-obj. `}
def BlindIsTerminal (C : BlindWildPrecat) (t : C .ob) : Type ≔ (a : C .ob) → BookIsContr (C .hom a t)

{` xca:terminal-prop: the type of terminal objects Σ_t isTerminal(t) is a
   proposition when C is univalent. `}
def blind_xca_terminal_prop : Type
  ≔ (C : BlindWildPrecat) → BlindIsUnivalent C → isProp (Σ (C .ob) (BlindIsTerminal C))

{` def:initial-obj. `}
def BlindIsInitial (C : BlindWildPrecat) (i : C .ob) : Type ≔ (a : C .ob) → BookIsContr (C .hom i a)

{` xca:unit-ptd-types. `}
def blind_xca_unit_ptd_types : Type
  ≔ Product (BlindIsTerminal blind_pointed_wild_precat pointed_unit)
      (BlindIsInitial blind_pointed_wild_precat pointed_unit)

{` def:op-cat. λ and ρ swap; α^{-1} plays the role of α. `}
def blind_op (C : BlindWildPrecat) : BlindWildPrecat
  ≔ (C .ob, (a b ↦ C .hom b a), C .idn, (a b c g f ↦ C .comp c b a f g),
     (a b f ↦ C .runit b a f), (a b f ↦ C .lunit b a f),
     (a b c d f g h ↦ inverse (C .hom d a) (C .comp d b a f (C .comp d c b g h))
        (C .comp d c a (C .comp c b a f g) h) (C .assoc d c b a h g f)))

{` lem:op-idem. `}
def blind_lem_op_idem : Type
  ≔ Product (BookIsEquiv BlindWildPrecat BlindWildPrecat blind_op)
      ((C : BlindWildPrecat) → Id BlindWildPrecat (blind_op (blind_op C)) C)

{` def:mono-in-cat. Injection = embedding (IsEmbedding). `}
def BlindIsMono (C : BlindWildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ (c : C .ob) → IsEmbedding (C .hom c a) (C .hom c b) (C .comp c a b f)

{` def:epi-in-cat. `}
def BlindIsEpi (C : BlindWildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ (c : C .ob) → IsEmbedding (C .hom b c) (C .hom a c) (g ↦ C .comp a b c g f)

{` xca:mono-cat-grp: monos in the category of groups ⇔ def:typeofmono
   (IsGroupMono, ch. 5). Both sides are propositions. `}
def blind_xca_mono_cat_grp : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Product (BlindIsMono (blind_group_precat .fst) G H f → IsGroupMono G H f)
        (IsGroupMono G H f → BlindIsMono (blind_group_precat .fst) G H f)

{` xca:monos-epis-sets-types. `}
def blind_xca_monos_types : Type
  ≔ (A B : Type) (f : A → B)
    → Product (BlindIsMono blind_universe_wild_precat A B f → IsEmbedding A B f)
        (IsEmbedding A B f → BlindIsMono blind_universe_wild_precat A B f)

def blind_xca_epis_sets : Type
  ≔ (A B : SetTypes) (f : A .fst → B .fst)
    → Product (BlindIsEpi (blind_set_precat .fst) A B f → Surjective (A .fst) (B .fst) f)
        (Surjective (A .fst) (B .fst) f → BlindIsEpi (blind_set_precat .fst) A B f)

{` xca:monos-epis-preorder. `}
def blind_xca_monos_epis_preorder : Type
  ≔ (C : BlindPreorder) (a b : C .fst .fst .ob) (f : C .fst .fst .hom a b)
    → Product (BlindIsMono (C .fst .fst) a b f) (BlindIsEpi (C .fst .fst) a b f)
