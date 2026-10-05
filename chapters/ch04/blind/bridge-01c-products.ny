export "bridge-01b-group-examples"
export "../../../src/420-group-products-abelian"
export "../../../src/423-group-points-and-automorphisms"
export "../../../src/406-symmetric-group-three"

{` Bridges for group.tex lines 665-787 (blind file 01-groups.ny). `}

{` ex:productofgroups (line 665). The blind product differs from ours only
   in the connectedness and groupoid witnesses. `}
def bridge_prod (G H : BlindGroup)
  : Id Group (bridge_g (blind_group_product G H)) (product_group (bridge_g G) (bridge_g H))
  ≔ let A ≔ blind_B G in let B ≔ blind_B H in
    (classifying ≔ pcg_witnesses_unique (Product (A .fst) (B .fst)) (A .snd .fst, B .snd .fst)
      (blind_connected_product (A .fst) (B .fst) (A .snd .snd .fst) (B .snd .snd .fst))
      (connected_product (A .fst) (B .fst) (A .snd .snd .fst) (B .snd .snd .fst))
      (hlevel_to_groupoid (Product (A .fst) (B .fst))
        (hlevel_product blind_three (A .fst) (B .fst)
          (groupoid_to_hlevel (A .fst) (A .snd .snd .snd)) (groupoid_to_hlevel (B .fst) (B .snd .snd .snd))))
      (groupoid_product (A .fst) (B .fst) (A .snd .snd .snd) (B .snd .snd .snd)))

def bridge_klein : Id Group (bridge_g blind_klein) klein_four_group
  ≔ concat Group (bridge_g blind_klein) (product_group (bridge_g (blind_SG two)) (bridge_g (blind_SG two))) klein_four_group
      (bridge_prod (blind_SG two) (blind_SG two))
      (refl product_group (bridge_sg two) (bridge_sg two))

def bridge_ex_klein_four : blind_ex_klein_four
  ≔ mere (Id Type (Fin blind_four) (BlindUSym blind_klein))
      (inverse Type (USym klein_four_group) (Fin blind_four) (ua (USym klein_four_group) (Fin (mul two two)) klein_usym_equiv))

def bridge_ex_product_usym : blind_ex_product_usym
  ≔ G H ↦ book_equivalence (USym (product_group (bridge_g G) (bridge_g H))) (Product (USym (bridge_g G)) (USym (bridge_g H)))
      (product_group_usym_equiv (bridge_g G) (bridge_g H))

{` xca:klein-not-cyclic (line 680). `}
def bridge_xca_klein_not_cyclic : blind_xca_klein_not_cyclic
  ≔ p ↦ klein_not_cyclic
      (concat Group (cyclic_group_fin three_nat) (bridge_g blind_klein) klein_four_group
        (concat Group (cyclic_group_fin three_nat) (bridge_g (blind_CG blind_three)) (bridge_g blind_klein)
          (inverse Group (bridge_g (blind_CG blind_three)) (cyclic_group_fin three_nat) (bridge_cg blind_three))
          (map_path BlindGroup Group bridge_g (blind_CG blind_three) blind_klein p))
        bridge_klein)

{` xca:bigproductfunext (i) (line 704) and ex:bigproductofgroups (line 685). `}
def bridge_xca_bigproduct_connected : blind_xca_bigproduct_connected
  ≔ S Y c g ↦ connected_pi_finite (S .fst .fst) (S .snd) Y c

def bridge_bigproduct (h : blind_xca_bigproduct_connected) (S : FiniteSets) (G : S .fst .fst → BlindGroup)
  : Id Group (bridge_g (blind_group_bigproduct h S G)) (family_product_group (S .fst .fst) (S .snd) (s ↦ bridge_g (G s)))
  ≔ let F ≔ family_product_group (S .fst .fst) (S .snd) (s ↦ bridge_g (G s)) in
    (classifying ≔ pcg_witnesses_unique (BG F .carrier) (shape F)
      (h S (s ↦ blind_B (G s) .fst) (s ↦ blind_B (G s) .snd .snd .fst) (s ↦ blind_B (G s) .snd .snd .snd))
      (bg_connected F)
      (blind_groupoid_pi (S .fst .fst) (s ↦ blind_B (G s) .fst) (s ↦ blind_B (G s) .snd .snd .snd))
      (bg_groupoid F))

def bridge_ex_bigproduct_ptw : blind_ex_bigproduct_ptw
  ≔ h S G ↦ book_equivalence (BlindUSym (blind_group_bigproduct h S G)) ((s : S .fst .fst) → BlindUSym (G s))
      (family_product_usym_equiv (S .fst .fst) (S .snd) (s ↦ bridge_g (G s))) .equiv

{` xca:bigproductfunext (ii) for bn 2: the pointed equivalence
   f ↦ (f 0, f 1), as bool_family_product_path (module 420) for Bool. `}
def bridge_fin2_pair (B : Fin two → Type) (f : (i : Fin two) → B i) : Product (B blind_fin_two_zero) (B blind_fin_two_one)
  ≔ (f blind_fin_two_zero, f blind_fin_two_one)

def bridge_fin2_unpair (B : Fin two → Type) (u : Product (B blind_fin_two_zero) (B blind_fin_two_one)) : (i : Fin two) → B i
  ≔ [ inr. x ↦ match x [ star. ↦ u .snd ] | inl. y ↦ match y [ inr. x ↦ match x [ star. ↦ u .fst ] | inl. e ↦ match e [ ] ] ]

def bridge_fin2_unpair_pair (B : Fin two → Type) (f : (i : Fin two) → B i)
  : (i : Fin two) → Id (B i) (bridge_fin2_unpair B (bridge_fin2_pair B f) i) (f i)
  ≔ [ inr. x ↦ match x [ star. ↦ refl (f (inr. star.)) ]
    | inl. y ↦ match y [ inr. x ↦ match x [ star. ↦ refl (f (inl. (inr. star.))) ] | inl. e ↦ match e [ ] ] ]

def bridge_xca_bigproduct_binary : blind_xca_bigproduct_binary
  ≔ h G ↦
    let S ≔ standard_finite_set two in
    let B : Fin two → Type ≔ i ↦ blind_B (G i) .fst in
    let P ≔ bridge_g (blind_group_bigproduct h S G) in
    let Q ≔ product_group (bridge_g (G blind_fin_two_zero)) (bridge_g (G blind_fin_two_one)) in
    bridge_gpath_via (blind_group_bigproduct h S G) (blind_group_product (G blind_fin_two_zero) (G blind_fin_two_one))
      P Q (refl P)
      (group_path_from_pointed_equiv P Q
        ((bridge_fin2_pair B, refl (shape Q)),
         book_quasi_inverse_equiv ((i : Fin two) → B i) (Product (B blind_fin_two_zero) (B blind_fin_two_one))
           (bridge_fin2_pair B) (bridge_fin2_unpair B)
           (f ↦ funext (Fin two) B (bridge_fin2_unpair B (bridge_fin2_pair B f)) f (bridge_fin2_unpair_pair B f))
           (u ↦ refl u) .equiv))
      (bridge_prod (G blind_fin_two_zero) (G blind_fin_two_one))

{` def:abgp (line 734): BlindIsAb G is IsAbelian (bridge_g G) on the nose. `}
def bridge_isab_prop : blind_isab_prop ≔ G ↦ is_abelian_prop (bridge_g G)

{` exer:first examples (line 745). `}
def bridge_xca_S2_abelian : blind_xca_S2_abelian ≔ sigma2_abelian
def bridge_xca_S3_not_abelian : blind_xca_S3_not_abelian ≔ symmetric_group_three_not_abelian
def bridge_xca_product_abelian : blind_xca_product_abelian ≔ G H hG hH ↦ product_abelian (bridge_g G) (bridge_g H) hG hH

{` Line 779. `}
def bridge_xca_change_basepoint : blind_xca_change_basepoint
  ≔ X b ↦ let Y : BlindPtConnGroupoid ≔ (X .fst, (b, X .snd .snd)) in
    let T ≔ Id BlindGroup (blind_mkgroup X) (blind_mkgroup Y) in
    mere_rec (Id Group (mkgroup (bridge_pcg X)) (mkgroup (bridge_pcg Y))) (Mere T) (mere_isprop T)
      (p ↦ mere T (bridge_gpath (blind_mkgroup X) (blind_mkgroup Y) p))
      (mkgroup_points_merely_equal (X .fst) (X .snd .fst) b (X .snd .snd .fst) (X .snd .snd .snd))

{` xca:typegroupisgroupoid (line 787). `}
def bridge_xca_group_paths_set : blind_xca_group_paths_set
  ≔ G H ↦ hlevel_two_to_set (Id BlindGroup G H)
      (hlevel_equiv (suc. (suc. zero.)) (Id Group (bridge_g G) (bridge_g H)) (Id BlindGroup G H)
        (canonical_inverse_equiv (Id BlindGroup G H) (Id Group (bridge_g G) (bridge_g H)) (bridge_group_paths G H))
        (set_to_hlevel_two (Id Group (bridge_g G) (bridge_g H)) (group_paths_set (bridge_g G) (bridge_g H))))

def bridge_xca_typegroup_groupoid : blind_xca_typegroup_groupoid ≔ bridge_xca_group_paths_set

def bridge_def_aut_group (G : BlindGroup)
  : Id Group (bridge_g (blind_AutGroup bridge_xca_typegroup_groupoid G)) (automorphism_group BlindGroup bridge_xca_typegroup_groupoid G)
  ≔ bridge_aut BlindGroup bridge_xca_typegroup_groupoid G
