{` Blind statements for chapter 9 (subgroups.tex), section "Automorphisms of groups". inn : Hom(G, Aut(G)) is
   chapter 4's def:inner-autos (Binn(y) = mkgroup(BG÷, y), pointed by refl_G), restated in this section. `}
export "06-normal"

{` Remark (subgroups.tex:1887). USym inn(g), through univalence, is an isomorphism G ≅ G. `}
def blind_inn_iso (G : Group) (g : USym G) : GroupIso G G
  ≔ group_path_iso_equiv G G .map
      (automorphism_group_usym_equiv Group group_groupoid G .map (usym_hom G (group_aut G) (inn G) g))

{` Remark (subgroups.tex:1887). USym(USym inn(g)) : h ↦ g⁻¹ h g. `}
def blind_usym_inn : Type
  ≔ (G : Group) (g h : USym G)
    → Id (USym G) (usym_hom G G (blind_inn_iso G g .fst) h) (usym_mul G (usym_inv G g) (usym_mul G h g))

{` Definition (subgroups.tex:1938). out(G) ≔ coker(inn), an Aut(G)-set. `}
def blind_out (G : Group) : GSet (group_aut G) ≔ blind_coker G (group_aut G) (inn G)

{` lemma:coker-out-action. out(G) = (G' ↦ ‖BG'÷ = BG÷‖₀). `}
def blind_out_family (G : Group) : GSet (group_aut G)
  ≔ G' ↦ (SetTrunc (Id Type (BG (G' .fst) .carrier) (BG G .carrier)),
          set_trunc_set (Id Type (BG (G' .fst) .carrier) (BG G .carrier)))

def blind_coker_out_action : Type ≔ (G : Group) → Id (GSet (group_aut G)) (blind_out G) (blind_out_family G)

{` Definition (subgroups.tex:1956). Inn(G) ≔ Img(inn). `}
def BlindInn (G : Group) : Group ≔ BlindImage G (group_aut G) (inn G)

{` Text after the definition: BInn(G) ≃ Σ_{G':Group} ‖BG'÷ = BG÷‖₀. `}
def blind_Inn_classifying : Type
  ≔ (G : Group)
    → BookEquiv (BG (BlindInn G) .carrier) (Σ Group (G' ↦ SetTrunc (Id Type (BG G' .carrier) (BG G .carrier))))

{` Lemma (subgroups.tex:1967). Inn(G) is normal in Aut(G): there is N : Π_{G'} Sub_{Aut(G)}(G') with
   N(sh_{Aut(G)}) = E(img(inn)). `}
def blind_Inn_normal : Type
  ≔ (G : Group)
    → Σ (BlindNor (group_aut G)) (N ↦
        Id (Subgroups (group_aut G)) (blind_nor_incl (group_aut G) N)
          (mono_to_subgroup (group_aut G) (blind_img G (group_aut G) (inn G))))

{` Definition (subgroups.tex:2001). Out(G) ≔ Aut_{GSet[Aut(G)]}(out(G)). `}
def BlindOut (G : Group) : Group
  ≔ automorphism_group (GSet (group_aut G)) (gset_groupoid (group_aut G)) (blind_out G)

{` Definition (subgroups.tex:2001): Out(G) ≔ Aut(G)/Inn(G) for the normal subgroup Inn(G). `}
def blind_Out_is_quotient : Type
  ≔ (G : Group) (N : BlindNor (group_aut G))
    → Id (Subgroups (group_aut G)) (blind_nor_incl (group_aut G) N)
        (mono_to_subgroup (group_aut G) (blind_img G (group_aut G) (inn G)))
    → Id Group (BlindQuotientGroup (group_aut G) N) (BlindOut G)

{` cons:simpler-version-Out. Φ : Aut_{‖U‖₁}(|BG÷|₁) = Out(G). (‖-‖₁ is Trunc 2 in the repository's indexing.) `}
def BlindAutOneTrunc (G : Group) : Group
  ≔ automorphism_group (Trunc (suc. (suc. zero.)) Type)
      (hlevel_to_groupoid (Trunc (suc. (suc. zero.)) Type) (trunc_level (suc. (suc. zero.)) Type))
      (trunc_unit (suc. (suc. zero.)) Type (BG G .carrier))

def blind_simpler_version_Out : Type ≔ (G : Group) → Id Group (BlindAutOneTrunc G) (BlindOut G)

{` cons:simpler-version-Out, text and implementation: ‖a = b‖₀ ≃ (|a|₁ = |b|₁), and |X|₁ = |Y|₁ merely iff X = Y merely. `}
def blind_one_trunc_paths : Type
  ≔ (A : Type) (a b : A)
    → BookEquiv (SetTrunc (Id A a b))
        (Id (Trunc (suc. (suc. zero.)) A) (trunc_unit (suc. (suc. zero.)) A a) (trunc_unit (suc. (suc. zero.)) A b))

def blind_one_trunc_components : Type
  ≔ (X Y : Type)
    → BlindIff (Mere (Id (Trunc (suc. (suc. zero.)) Type) (trunc_unit (suc. (suc. zero.)) Type X) (trunc_unit (suc. (suc. zero.)) Type Y)))
        (Mere (Id Type X Y))
