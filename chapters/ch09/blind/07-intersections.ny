{` Blind statements for chapter 9 (subgroups.tex), section "Intersecting with normal subgroups". `}
export "06-normal"
export "../../../src/822-pullback-group-symmetries"

{` The abstract subgroup associated with a monomorphism (abstr H, abstr(i), !); IsGroupMono is injectivity of USym i. `}
def blind_abs_of_mono (G : Group) (m : GroupMonos G) : BlindAbsMonos G
  ≔ (abstr (m .fst), (abstr_hom (m .fst) G (m .snd .fst), m .snd .snd))

{` g ∈ (H, φ): g is in the image of φ. `}
def BlindAbsMember (G : Group) (x : BlindAbsMonos G) (g : USym G) : Type
  ≔ Mere (BookFiber (x .fst .carrier) (USym G) (x .snd .fst .fst) g)

{` xca (subgroups.tex:1801). A definition of the intersection of abstract subgroups of (abstr G) whose elements are
   exactly the common elements and which agrees with the intersection (pullback) of monomorphisms
   (def:intersectionofgroups, chapter 8's group_mono_intersection). `}
def blind_abstract_intersection : Type
  ≔ Σ ((G : Group) → BlindAbsMonos G → BlindAbsMonos G → BlindAbsMonos G) (I ↦
      Product
        ((G : Group) (m m' : GroupMonos G)
          → Id (BlindAbsMonos G) (I G (blind_abs_of_mono G m) (blind_abs_of_mono G m'))
              (blind_abs_of_mono G (group_mono_intersection G m m')))
        ((G : Group) (x y : BlindAbsMonos G) (g : USym G)
          → BlindIff (BlindAbsMember G (I G x y) g) (Product (BlindAbsMember G x g) (BlindAbsMember G y g))))

{` lem:whatSylow2needs. N ≔ Ker(f) for (G', f, !) : Epi(G) and (H, i, !) : Mono(G). N ∩ H ≔ BN ×_BG BH (pointed
   component), a subgroup of H via the projection. `}
def BlindNcapH (G G' : Group) (f : GroupHom G G') (H : Group) (i : GroupHom H G) : Group
  ≔ pullback_group G (BlindKer G G' f) H (blind_kermap G G' f) i

def blind_NcapH_to_H (G G' : Group) (f : GroupHom G G') (H : Group) (i : GroupHom H G) : GroupMonos H
  ≔ (BlindNcapH G G' f H i,
     (pullback_group_proj_right G (BlindKer G G' f) H (blind_kermap G G' f) i,
      pullback_group_proj_right_mono G (BlindKer G G' f) H (blind_kermap G G' f) i (blind_kermap_mono G G' f)))

{` lem:whatSylow2needs (1). N ∩ H is the kernel of f i : Hom(H, G') (as subgroups of H). `}
def blind_whatSylow2needs_kernel : Type
  ≔ (G G' : Group) (f : GroupHom G G') (hf : BlindIsEpi G G' f) (m : GroupMonos G)
    → Id (GroupMonos (m .fst)) (blind_NcapH_to_H G G' f (m .fst) (m .snd .fst))
        (blind_ker (m .fst) G' (group_hom_compose (m .fst) G G' (m .snd .fst) f))

{` The same as subgroups of G: N ∩ H = (Ker(f i), i ker_{fi}, !). `}
def blind_whatSylow2needs_kernel_in_G : Type
  ≔ (G G' : Group) (f : GroupHom G G') (hf : BlindIsEpi G G' f) (m : GroupMonos G)
    → let fi ≔ group_hom_compose (m .fst) G G' (m .snd .fst) f in
      let K ≔ BlindKer (m .fst) G' fi in
      let j ≔ group_hom_compose K (m .fst) G (blind_kermap (m .fst) G' fi) (m .snd .fst) in
      Σ (IsGroupMono K G j) (mj ↦
        Id (GroupMonos G) (group_mono_intersection G (blind_ker G G' f) m) (K, (j, mj)))

{` lem:whatSylow2needs (2). N ∩ H is normal in H and the induced homomorphism H/(N ∩ H) → G' is a monomorphism. `}
def blind_whatSylow2needs_mono : Type
  ≔ (G G' : Group) (f : GroupHom G G') (hf : BlindIsEpi G G' f) (m : GroupMonos G)
    → let H ≔ m .fst in
      Σ (BlindNor H) (Nn ↦
      Σ (Id (Subgroups H) (blind_nor_incl H Nn) (mono_to_subgroup H (blind_NcapH_to_H G G' f H (m .snd .fst)))) (_ ↦
      Σ (GroupHom (BlindQuotientGroup H Nn) G') (k ↦
        Product (BlindIsMono (BlindQuotientGroup H Nn) G' k)
          (Id (GroupHom H G') (group_hom_compose H (BlindQuotientGroup H Nn) G' (blind_quotient_hom H Nn) k)
            (group_hom_compose H G G' (m .snd .fst) f)))))

{` xca (subgroups.tex:1825). The same in terms of Sub: for S : Sub(G) with underlying group H and inclusion i,
   N ∩ H is the H-orbit of pt_N in the restriction to H of the transitive G-set of N = E(ker f). `}
def blind_sub_NcapH (G G' : Group) (f : GroupHom G G') (S : Subgroups G) : Subgroups (subgroup_group G S)
  ≔ orbit_subgroup (subgroup_group G S)
      (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (mono_to_subgroup G (blind_ker G G' f) .gset))
      (mono_to_subgroup G (blind_ker G G' f) .point)

def blind_whatSylow2needs_sub : Type
  ≔ (G G' : Group) (f : GroupHom G G') (hf : BlindIsEpi G G' f) (S : Subgroups G)
    → let H ≔ subgroup_group G S in
      Product
        (Id (Subgroups H) (blind_sub_NcapH G G' f S)
          (mono_to_subgroup H (blind_ker H G' (group_hom_compose H G G' (subgroup_inclusion G S) f))))
        (Σ (BlindNor H) (Nn ↦
         Σ (Id (Subgroups H) (blind_nor_incl H Nn) (blind_sub_NcapH G G' f S)) (_ ↦
         Σ (GroupHom (BlindQuotientGroup H Nn) G') (k ↦
           Product (BlindIsMono (BlindQuotientGroup H Nn) G' k)
             (Id (GroupHom H G') (group_hom_compose H (BlindQuotientGroup H Nn) G' (blind_quotient_hom H Nn) k)
               (group_hom_compose H G G' (subgroup_inclusion G S) f))))))

{` Text before lem:thereisaconjugate: for F : Hom(H,G), x : X(sh_G) is an H-fixed point if there is
   f : Π_{v:BH} X(F(v)) with x = X(Bf_pt⁻¹)(f(sh_H)). `}
def BlindIsHFixed (G : Group) (X : GSet G) (H : Group) (F : GroupHom H G) (x : gset_underlying G X) : Type
  ≔ Σ ((v : BG H .carrier) → X (hom_function H G F v) .fst) (s ↦
      Id (gset_underlying G X) x
        (gset_act G X (hom_function H G F (shape H)) (shape G)
          (inverse (BG G .carrier) (shape G) (hom_function H G F (shape H)) (hom_point H G F)) (s (shape H))))

{` The conjugate g H ≔ (H, F, g⁻¹ Bf_pt, !), read with g⁻¹ first (the only well-typed reading of the juxtaposition). `}
def blind_conjugate_hom (G H : Group) (F : GroupHom H G) (g : USym G) : GroupHom H G
  ≔ mkhom H G (hom_function H G F,
      concat (BG G .carrier) (shape G) (shape G) (hom_function H G F (shape H)) (usym_inv G g) (hom_point H G F))

{` lem:thereisaconjugate, literal. g x is H-fixed iff x is (g H)-fixed. `}
def blind_thereisaconjugate : Type
  ≔ (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G) (m : GroupMonos G)
    → BlindIff (BlindIsHFixed G X (m .fst) (m .snd .fst) (gset_usym_act G X g x))
        (BlindIsHFixed G X (m .fst) (blind_conjugate_hom G (m .fst) (m .snd .fst) g) x)

{` Corrected: the proof computes x = X((g Bf_pt)⁻¹ ...) with g followed by Bf_pt, i.e. the conjugate by g⁻¹
   in the book's action; with g⁻¹ first the literal statement says g x is H-fixed iff g⁻¹ x is. `}
def blind_conjugate_hom_corrected (G H : Group) (F : GroupHom H G) (g : USym G) : GroupHom H G
  ≔ mkhom H G (hom_function H G F,
      concat (BG G .carrier) (shape G) (shape G) (hom_function H G F (shape H)) g (hom_point H G F))

def blind_thereisaconjugate_corrected : Type
  ≔ (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G) (m : GroupMonos G)
    → BlindIff (BlindIsHFixed G X (m .fst) (m .snd .fst) (gset_usym_act G X g x))
        (BlindIsHFixed G X (m .fst) (blind_conjugate_hom_corrected G (m .fst) (m .snd .fst) g) x)
