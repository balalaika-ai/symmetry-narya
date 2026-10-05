export "10-hom-group"
export "../../../src/1336-hom-group-pointwise"

{` Bridges for def:AbHomgroup (902) and lem:grpHomOK (919). blind_grphom is our abelian_hom_group by refl.
   The blind chain uses the 162 form of ptw_* (pointed_map_path_equiv) where ours (constant_loops_pointed_equiv,
   module 1207) uses the explicit (happly, pathover) form; the two agree by pointed_map_path_equiv_ptw (module 289),
   so the blind chain is pointwise our abelian_hom_abstract_map. Both parts of the blind lemma then follow from
   hom_group_abstract_iso (equivalence) and abelian_hom_abstract_mul (multiplicativity). `}

def bridge_def_grphom (H : Group) (G : AbelianGroup) : Id Group (blind_grphom H G) (abelian_hom_group H G)
  ≔ refl (abelian_hom_group H G)

def b10_ptw_agree (X Y : Pointed) (p : Id (BookPointedMap X Y) (book_pointed_constant X Y) (book_pointed_constant X Y))
  : Id (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y .map p) (constant_loops_pointed_equiv X Y .map p)
  ≔ refl (constant_pointed_homotopy_equiv X Y .map)
      (pointed_map_path_equiv_ptw X Y (book_pointed_constant X Y) (book_pointed_constant X Y) p)

def b10_chain_tail (H : Group) (G : AbelianGroup) (k : BookPointedMap (BG H) (Omega (BB (G .fst))))
  : AbstractHom (abstr H) (abstr (G .fst))
  ≔ abstr_hom H (G .fst)
      (mkhom H (G .fst) (book_pointed_compose (BG H) (Omega (BB (G .fst))) (BG (G .fst)) k (bb_loops_evaluation_pointed (G .fst))))

def b10_chain_agree (H : Group) (G : AbelianGroup) (p : USym (abelian_hom_group H G))
  : Id (AbstractHom (abstr H) (abstr (G .fst))) (blind_grphom_chain H G p) (abelian_hom_abstract_map H G p)
  ≔ refl (b10_chain_tail H G) (b10_ptw_agree (BG H) (BB (G .fst)) (p .fst))

def b10_chain_equiv (H : Group) (G : AbelianGroup)
  : Equiv (USym (abelian_hom_group H G)) (AbstractHom (abstr H) (abstr (G .fst)))
  ≔ equiv_change_map (USym (abelian_hom_group H G)) (AbstractHom (abstr H) (abstr (G .fst)))
      (hom_group_abstract_iso H G .fst) (blind_grphom_chain H G)
      (p ↦ inverse (AbstractHom (abstr H) (abstr (G .fst))) (blind_grphom_chain H G p) (abelian_hom_abstract_map H G p)
             (b10_chain_agree H G p))

def b10_chain_value (H : Group) (G : AbelianGroup) (p : USym (abelian_hom_group H G)) (g : USym H)
  : Id (USym (G .fst)) (blind_grphom_chain H G p .fst g) (abelian_hom_abstract_map H G p .fst g)
  ≔ refl ((φ ↦ φ .fst g) : AbstractHom (abstr H) (abstr (G .fst)) → USym (G .fst)) (b10_chain_agree H G p)

def bridge_lem_grpHomOK : blind_lem_grpHomOK
  ≔ H G ↦
    let K ≔ G .fst in let U ≔ USym K in let A ≔ AbstractHom (abstr H) (abstr K) in
    let Hm ≔ abelian_hom_group H G in
    let F ≔ abelian_hom_abstract_map H G in
    (book_equivalence (USym Hm) A (b10_chain_equiv H G) .equiv,
     p q g ↦
       calc
         blind_grphom_chain H G (usym_mul Hm p q) .fst g = F (usym_mul Hm p q) .fst g
           by b10_chain_value H G (usym_mul Hm p q) g
         = pointwise_hom_mul H G (F p) (F q) .fst g
           by refl ((φ ↦ φ .fst g) : A → U) (abelian_hom_abstract_mul H G p q)
         = usym_mul K (blind_grphom_chain H G p .fst g) (blind_grphom_chain H G q .fst g)
           by refl (usym_mul K)
             (inverse U (blind_grphom_chain H G p .fst g) (F p .fst g) (b10_chain_value H G p g))
             (inverse U (blind_grphom_chain H G q .fst g) (F q .fst g) (b10_chain_value H G q g)) ∎)

{` Converse direction (ours from blind): the blind lemma gives that our map abelian_hom_abstract_map is an
   equivalence, since it is homotopic to the blind chain. `}
def bridge_lem_grpHomOK_converse (h : blind_lem_grpHomOK) (H : Group) (G : AbelianGroup)
  : Equiv (USym (abelian_hom_group H G)) (AbstractHom (abstr H) (abstr (G .fst)))
  ≔ equiv_change_map (USym (abelian_hom_group H G)) (AbstractHom (abstr H) (abstr (G .fst)))
      (native_equivalence (USym (abelian_hom_group H G)) (AbstractHom (abstr H) (abstr (G .fst)))
        (blind_grphom_chain H G, h H G .fst))
      (abelian_hom_abstract_map H G) (b10_chain_agree H G)
