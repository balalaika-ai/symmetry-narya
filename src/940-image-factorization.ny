export "938-mono-cover-kernels"
export "939-pointed-factorizations"
export "287-chapter-two-text-claims"

{` Chapter 9 (subgroups.tex), sec:image: def:Im-fact (line 869),
   lem:Im-fact-unique (line 879) and the maps img, prjim, ∘⁻¹ of def:image
   (line 978).

   Epi(G) ×_Group Mono(H) is the pullback Σ_{(Z,p):Epi(G)} Σ_{(Z',i):Mono(H)}
   (Z = Z') with categorical epis and monos (GroupEpis, module 900;
   GroupMonomorphismsInto, module 900). The composition map of the proof is
   ∘((Z,p,!),(Z',j,!),α) ≔ j ∘ ptoe(α) ∘ p; here ptoe(α) : Hom(Z, Z') is the
   transport of the identity homomorphism along α (the homomorphism
   corresponding to α by path induction; definitionally refl ↦ id only up
   to transport_refl). lem:Im-fact-unique is proved as in the book: ∘ is an
   equivalence (its fibers are contractible: they are equivalent to the
   type of pointed 0-image factorizations of Bf, rem:n-im-ptd-map, module
   939, with the factors a pointed connected groupoid, an epi = 0-connected
   map, lem:epi-surj, and a mono = covering, lem:eq-mono-cover) and Imfact
   is a section of ∘, hence its inverse. `}

def EpiMonoFactorizations (G H : Group) : Type
  ≔ Σ (GroupEpis G) (e ↦ Σ (GroupMonomorphismsInto H) (m ↦ Id Group (e .fst) (m .fst)))

{` def:image: img(f) ≔ (Img(f), incl_img(f), !) : Mono(G') and
   prjim(f) ≔ (Img(f), prj_img(f), !) : Epi(G). `}
def image_mono_categorical (G H : Group) (f : GroupHom G H) : GroupMonomorphismsInto H
  ≔ (image_group G H f, (image_inclusion G H f, eqmc_image_inclusion_monomorphism G H f))

def image_epi_projection (G H : Group) (f : GroupHom G H) : GroupEpis G
  ≔ (image_group G H f, (image_projection G H f, eqmc_image_projection_epi G H f))

{` def:Im-fact = ∘⁻¹ of def:image: f ↦ ((Img f, p f), (Img f, i f), refl). `}
def image_factorization_map (G H : Group) (f : GroupHom G H) : EpiMonoFactorizations G H
  ≔ (image_epi_projection G H f, (image_mono_categorical G H f, refl (image_group G H f)))

{` ptoe(α). `}
def imfact_idtoiso (Z Z' : Group) (α : Id Group Z Z') : GroupHom Z Z'
  ≔ transport Group (W ↦ GroupHom Z W) Z Z' α (group_hom_id Z)

def imfact_idtoiso_refl (Z : Group) : Id (GroupHom Z Z) (imfact_idtoiso Z Z (refl Z)) (group_hom_id Z)
  ≔ transport_refl Group (W ↦ GroupHom Z W) Z (group_hom_id Z)

{` ∘((Z,p,!),(Z',j,!),α) ≔ j ∘ ptoe(α) ∘ p. `}
def imfact_compose (G H : Group) (t : EpiMonoFactorizations G H) : GroupHom G H
  ≔ let Z ≔ t .fst .fst in
    let Z' ≔ t .snd .fst .fst in
    group_hom_compose G Z H (t .fst .snd .fst)
      (group_hom_compose Z Z' H (imfact_idtoiso Z Z' (t .snd .snd)) (t .snd .fst .snd .fst))

{` j ∘ ptoe(refl) ∘ p = j ∘ p. `}
def imfact_compose_refl_path (G Z H : Group) (p : GroupHom G Z) (j : GroupHom Z H)
  : Id (GroupHom G H) (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j))
      (group_hom_compose G Z H p j)
  ≔ refl (group_hom_compose G Z H p)
      (concat (GroupHom Z H) (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j)
         (group_hom_compose Z Z H (group_hom_id Z) j) j
         (refl ((x ↦ group_hom_compose Z Z H x j) : GroupHom Z Z → GroupHom Z H) (imfact_idtoiso_refl Z))
         (group_hom_id_compose Z H j))

{` ∘ ∘ Imfact = id. `}
def imfact_compose_section (G H : Group) (f : GroupHom G H)
  : Id (GroupHom G H) (imfact_compose G H (image_factorization_map G H f)) f
  ≔ let I ≔ image_group G H f in
    concat (GroupHom G H) (imfact_compose G H (image_factorization_map G H f))
      (group_hom_compose G I H (image_projection G H f) (image_inclusion G H f)) f
      (imfact_compose_refl_path G I H (image_projection G H f) (image_inclusion G H f))
      (inverse (GroupHom G H) f (group_hom_compose G I H (image_projection G H f) (image_inclusion G H f))
        (image_factorization_path G H f))

{` Helpers: a surjection out of a connected type has connected codomain;
   based path spaces are contractible with center (a, refl a). `}
def imfact_connected_surjection (A B : Type) (f : A → B) (hA : Connected A) (hf : Surjective A B f) : Connected B
  ≔ (trunc_map native_truncation A B f (hA .fst),
     b b' ↦ mere_rec (BookFiber A B f b) (Mere (Id B b b')) (mere_isprop (Id B b b'))
       (u ↦ mere_rec (BookFiber A B f b') (Mere (Id B b b')) (mere_isprop (Id B b b'))
          (v ↦ trunc_map native_truncation (Id A (u .fst) (v .fst)) (Id B b b')
             (q ↦ concat B b (f (u .fst)) b' (u .snd)
                (concat B (f (u .fst)) (f (v .fst)) b' (map_path A B f (u .fst) (v .fst) q)
                   (inverse B b' (f (v .fst)) (v .snd))))
             (hA .snd (u .fst) (v .fst)))
          (hf b'))
       (hf b))

def imfact_based_paths_contr (A : Type) (a : A) : isContr (Σ A (x ↦ Id A a x))
  ≔ ((a, refl a), u ↦ J A a (x q ↦ Id (Σ A (x ↦ Id A a x)) (x, q) (a, refl a))
       (refl ((a, refl a) : Σ A (x ↦ Id A a x))) (u .fst) (u .snd))

{` The properties of pointed factorizations of Bf that make the middle
   object a group: connected groupoid, 0-connected first factor, covering
   second factor. Given the last two (and BG connected, BH a groupoid) the
   first holds automatically. `}
def ImfactGroupProperties (A B : Type) (C : Type) (g : A → C) (h : C → B) : Type
  ≔ Product (Product (Connected C) (isGroupoid C)) (PfactZeroProperties A B C g h)

def imfact_group_properties_equiv (A B : Type) (hA : Connected A) (hB : isGroupoid B) (C : Type) (g : A → C) (h : C → B)
  : Equiv (ImfactGroupProperties A B C g h) (PfactZeroProperties A B C g h)
  ≔ let P0 ≔ PfactZeroProperties A B C g h in
    let pP0 : isProp P0 ≔ product_prop (ZeroConnectedMap A C g) (IsCovering C B h)
        (zero_connected_map_prop A C g) (covering_property_prop B (C, h)) in
    iff_equiv (ImfactGroupProperties A B C g h) P0
      (product_prop (Product (Connected C) (isGroupoid C)) P0
         (product_prop (Connected C) (isGroupoid C) (connected_isprop C) (isgroupoid_isprop C)) pP0)
      pP0
      (x ↦ x .snd)
      (x ↦ ((imfact_connected_surjection A C g hA (zero_connected_map_surjective A C g (x .fst)),
             covering_domain_groupoid C B h (x .snd) hB), x))

def imfact_group_factorizations_contractible (G H : Group) (f : GroupHom G H)
  : BookIsContr (PfactPointedWith (BG G) (BG H) (hom_B G H f) (ImfactGroupProperties (BG G .carrier) (BG H .carrier)))
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    pfact_contractible (BG G) (BG H) (hom_B G H f) (ImfactGroupProperties A B)
      (book_contractibility_equiv
         (Σ (Factorizations A B F) (t ↦ PfactZeroProperties A B (t .fst) (t .snd .fst) (t .snd .snd .fst)))
         (Σ (Factorizations A B F) (t ↦ ImfactGroupProperties A B (t .fst) (t .snd .fst) (t .snd .snd .fst)))
         (family_equiv (Factorizations A B F)
            (t ↦ PfactZeroProperties A B (t .fst) (t .snd .fst) (t .snd .snd .fst))
            (t ↦ ImfactGroupProperties A B (t .fst) (t .snd .fst) (t .snd .snd .fst))
            (t ↦ canonical_inverse_equiv (ImfactGroupProperties A B (t .fst) (t .snd .fst) (t .snd .snd .fst))
               (PfactZeroProperties A B (t .fst) (t .snd .fst) (t .snd .snd .fst))
               (imfact_group_properties_equiv A B (bg_connected G) (bg_groupoid H) (t .fst) (t .snd .fst) (t .snd .snd .fst))))
         .map (zero_image_book_universal_property A B F))

{` The fiber of ∘ over f, in four steps. F3: (Z, p, j, f = j ∘ p, epi, mono). `}
def ImfactF3 (G H : Group) (f : GroupHom G H) : Type
  ≔ Σ Group (Z ↦ Σ (GroupHom G Z) (p ↦ Σ (GroupHom Z H) (j ↦
      Product (Id (GroupHom G H) f (group_hom_compose G Z H p j))
        (Product (IsGroupEpi G Z p) (IsGroupMonomorphism Z H j)))))

def imfact_f3_pointed_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (ImfactF3 G H f) (PfactPointedWith (BG G) (BG H) (hom_B G H f) (ImfactGroupProperties (BG G .carrier) (BG H .carrier)))
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let W ≔ PfactPointedWith (BG G) (BG H) (hom_B G H f) (ImfactGroupProperties A B) in
    quasi_inverse_equiv (ImfactF3 G H f) W
      (t ↦
        let Z ≔ t .fst in let p ≔ t .snd .fst in let j ≔ t .snd .snd .fst in
        ((BG Z, (hom_B G Z p, (hom_B Z H j, t .snd .snd .snd .fst .classifying_map))),
         ((bg_connected Z, bg_groupoid Z),
          (eqmc_epi_cokernel_contractible_equiv G Z p .map (t .snd .snd .snd .snd .fst),
           eqmc_mono_covering_equiv Z H j .map (t .snd .snd .snd .snd .snd)))))
      (u ↦
        let Z ≔ mkgroup (u .fst .fst .carrier, u .fst .fst .point, u .snd .fst .fst, u .snd .fst .snd) in
        let p ≔ mkhom G Z (u .fst .snd .fst) in
        let j ≔ mkhom Z H (u .fst .snd .snd .fst) in
        (Z, (p, (j, ((classifying_map ≔ u .fst .snd .snd .snd),
          (equiv_inverse_map (IsGroupEpi G Z p) (EqmcCokernelContractible G Z p) (eqmc_epi_cokernel_contractible_equiv G Z p)
             (u .snd .snd .fst),
           equiv_inverse_map (IsGroupMonomorphism Z H j) (IsCovering (BG Z .carrier) B (hom_function Z H j))
             (eqmc_mono_covering_equiv Z H j) (u .snd .snd .snd)))))))
      (t ↦
        let Z ≔ t .fst in let p ≔ t .snd .fst in let j ≔ t .snd .snd .fst in
        let E ≔ Product (IsGroupEpi G Z p) (IsGroupMonomorphism Z H j) in
        refl ((w ↦ (Z, (p, (j, (t .snd .snd .snd .fst, w))))) : E → ImfactF3 G H f)
          (product_prop (IsGroupEpi G Z p) (IsGroupMonomorphism Z H j) (is_group_epi_prop G Z p)
             (is_group_monomorphism_prop Z H j)
             (equiv_inverse_map (IsGroupEpi G Z p) (EqmcCokernelContractible G Z p) (eqmc_epi_cokernel_contractible_equiv G Z p)
                (eqmc_epi_cokernel_contractible_equiv G Z p .map (t .snd .snd .snd .snd .fst)),
              equiv_inverse_map (IsGroupMonomorphism Z H j) (IsCovering (BG Z .carrier) B (hom_function Z H j))
                (eqmc_mono_covering_equiv Z H j) (eqmc_mono_covering_equiv Z H j .map (t .snd .snd .snd .snd .snd)))
             (t .snd .snd .snd .snd)))
      (u ↦
        let C ≔ u .fst .fst .carrier in
        let g ≔ u .fst .snd .fst .fst in
        let h ≔ u .fst .snd .snd .fst .fst in
        let P0 ≔ PfactZeroProperties A B C g h in
        let Z ≔ mkgroup (C, u .fst .fst .point, u .snd .fst .fst, u .snd .fst .snd) in
        let p ≔ mkhom G Z (u .fst .snd .fst) in
        let j ≔ mkhom Z H (u .fst .snd .snd .fst) in
        refl ((w ↦ (u .fst, (u .snd .fst, w))) : P0 → W)
          (product_prop (ZeroConnectedMap A C g) (IsCovering C B h) (zero_connected_map_prop A C g)
             (covering_property_prop B (C, h))
             (eqmc_epi_cokernel_contractible_equiv G Z p .map
                (equiv_inverse_map (IsGroupEpi G Z p) (EqmcCokernelContractible G Z p) (eqmc_epi_cokernel_contractible_equiv G Z p)
                   (u .snd .snd .fst)),
              eqmc_mono_covering_equiv Z H j .map
                (equiv_inverse_map (IsGroupMonomorphism Z H j) (IsCovering C B h) (eqmc_mono_covering_equiv Z H j)
                   (u .snd .snd .snd)))
             (u .snd .snd)))

{` F2: the fiber with Z' = Z and α = refl. `}
def ImfactF2 (G H : Group) (f : GroupHom G H) : Type
  ≔ Σ Group (Z ↦ Σ (GroupHom G Z) (p ↦ Σ (IsGroupEpi G Z p) (_ ↦ Σ (GroupHom Z H) (j ↦
      Σ (IsGroupMonomorphism Z H j) (_ ↦
        Id (GroupHom G H) f (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j)))))))

def imfact_f2_f3_equiv (G H : Group) (f : GroupHom G H) : Equiv (ImfactF2 G H f) (ImfactF3 G H f)
  ≔ let e : (Z : Group) (p : GroupHom G Z) (j : GroupHom Z H)
          → Equiv (Id (GroupHom G H) f (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j)))
              (Id (GroupHom G H) f (group_hom_compose G Z H p j))
      ≔ Z p j ↦ pfact_concat_right_equiv (GroupHom G H) f
          (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j))
          (group_hom_compose G Z H p j) (imfact_compose_refl_path G Z H p j) in
    quasi_inverse_equiv (ImfactF2 G H f) (ImfactF3 G H f)
      (t ↦
        let Z ≔ t .fst in let p ≔ t .snd .fst in let j ≔ t .snd .snd .snd .fst in
        (Z, (p, (j, (e Z p j .map (t .snd .snd .snd .snd .snd), (t .snd .snd .fst, t .snd .snd .snd .snd .fst))))))
      (u ↦
        let Z ≔ u .fst in let p ≔ u .snd .fst in let j ≔ u .snd .snd .fst in
        (Z, (p, (u .snd .snd .snd .snd .fst, (j, (u .snd .snd .snd .snd .snd,
          equiv_inverse_map (Id (GroupHom G H) f (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j)))
            (Id (GroupHom G H) f (group_hom_compose G Z H p j)) (e Z p j) (u .snd .snd .snd .fst)))))))
      (t ↦
        let Z ≔ t .fst in let p ≔ t .snd .fst in let j ≔ t .snd .snd .snd .fst in
        refl ((r ↦ (Z, (p, (t .snd .snd .fst, (j, (t .snd .snd .snd .snd .fst, r))))))
               : Id (GroupHom G H) f (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j))
                 → ImfactF2 G H f)
          (equiv_retraction (Id (GroupHom G H) f (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j)))
             (Id (GroupHom G H) f (group_hom_compose G Z H p j)) (e Z p j) (t .snd .snd .snd .snd .snd)))
      (u ↦
        let Z ≔ u .fst in let p ≔ u .snd .fst in let j ≔ u .snd .snd .fst in
        refl ((r ↦ (Z, (p, (j, (r, u .snd .snd .snd .snd))))) : Id (GroupHom G H) f (group_hom_compose G Z H p j) → ImfactF3 G H f)
          (equiv_counit (Id (GroupHom G H) f (group_hom_compose G Z H p (group_hom_compose Z Z H (imfact_idtoiso Z Z (refl Z)) j)))
             (Id (GroupHom G H) f (group_hom_compose G Z H p j)) (e Z p j) (u .snd .snd .snd .fst)))

{` F1: the fiber regrouped, with (Z', α) as one component. `}
def ImfactF1Tail (G H : Group) (f : GroupHom G H) (Z : Group) (p : GroupHom G Z) (w : Σ Group (Z' ↦ Id Group Z Z')) : Type
  ≔ Σ (GroupHom (w .fst) H) (j ↦ Σ (IsGroupMonomorphism (w .fst) H j) (_ ↦
      Id (GroupHom G H) f (group_hom_compose G Z H p (group_hom_compose Z (w .fst) H (imfact_idtoiso Z (w .fst) (w .snd)) j))))

def ImfactF1 (G H : Group) (f : GroupHom G H) : Type
  ≔ Σ Group (Z ↦ Σ (GroupHom G Z) (p ↦ Σ (IsGroupEpi G Z p) (_ ↦
      Σ (Σ Group (Z' ↦ Id Group Z Z')) (ImfactF1Tail G H f Z p))))

def imfact_f1_f2_equiv (G H : Group) (f : GroupHom G H) : Equiv (ImfactF1 G H f) (ImfactF2 G H f)
  ≔ family_equiv Group
      (Z ↦ Σ (GroupHom G Z) (p ↦ Σ (IsGroupEpi G Z p) (_ ↦ Σ (Σ Group (Z' ↦ Id Group Z Z')) (ImfactF1Tail G H f Z p))))
      (Z ↦ Σ (GroupHom G Z) (p ↦ Σ (IsGroupEpi G Z p) (_ ↦ ImfactF1Tail G H f Z p (Z, refl Z))))
      (Z ↦ family_equiv (GroupHom G Z)
         (p ↦ Σ (IsGroupEpi G Z p) (_ ↦ Σ (Σ Group (Z' ↦ Id Group Z Z')) (ImfactF1Tail G H f Z p)))
         (p ↦ Σ (IsGroupEpi G Z p) (_ ↦ ImfactF1Tail G H f Z p (Z, refl Z)))
         (p ↦ family_equiv (IsGroupEpi G Z p)
            (_ ↦ Σ (Σ Group (Z' ↦ Id Group Z Z')) (ImfactF1Tail G H f Z p))
            (_ ↦ ImfactF1Tail G H f Z p (Z, refl Z))
            (_ ↦ contractible_base_sigma_equiv (Σ Group (Z' ↦ Id Group Z Z')) (ImfactF1Tail G H f Z p)
               (imfact_based_paths_contr Group Z))))

{` F0: the fiber of ∘ over f. `}
def imfact_f0_f1_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (BookFiber (EpiMonoFactorizations G H) (GroupHom G H) (imfact_compose G H) f) (ImfactF1 G H f)
  ≔ quasi_inverse_equiv (BookFiber (EpiMonoFactorizations G H) (GroupHom G H) (imfact_compose G H) f) (ImfactF1 G H f)
      (t ↦ (t .fst .fst .fst, (t .fst .fst .snd .fst, (t .fst .fst .snd .snd,
             ((t .fst .snd .fst .fst, t .fst .snd .snd), (t .fst .snd .fst .snd .fst, (t .fst .snd .fst .snd .snd, t .snd)))))))
      (u ↦ (((u .fst, (u .snd .fst, u .snd .snd .fst)),
             ((u .snd .snd .snd .fst .fst, (u .snd .snd .snd .snd .fst, u .snd .snd .snd .snd .snd .fst)),
              u .snd .snd .snd .fst .snd)),
            u .snd .snd .snd .snd .snd .snd))
      (t ↦ refl t) (u ↦ refl u)

{` lem:Im-fact-unique, the composition map: every fiber is contractible. `}
def imfact_compose_fiber_contractible (G H : Group) (f : GroupHom G H)
  : BookIsContr (BookFiber (EpiMonoFactorizations G H) (GroupHom G H) (imfact_compose G H) f)
  ≔ let F0 ≔ BookFiber (EpiMonoFactorizations G H) (GroupHom G H) (imfact_compose G H) f in
    let W ≔ PfactPointedWith (BG G) (BG H) (hom_B G H f) (ImfactGroupProperties (BG G .carrier) (BG H .carrier)) in
    let e : Equiv F0 W
      ≔ compose_equiv F0 (ImfactF1 G H f) W (imfact_f0_f1_equiv G H f)
          (compose_equiv (ImfactF1 G H f) (ImfactF2 G H f) W (imfact_f1_f2_equiv G H f)
            (compose_equiv (ImfactF2 G H f) (ImfactF3 G H f) W (imfact_f2_f3_equiv G H f) (imfact_f3_pointed_equiv G H f))) in
    book_contractibility_equiv W F0 (canonical_inverse_equiv F0 W e) .map (imfact_group_factorizations_contractible G H f)

def imfact_compose_is_equiv (G H : Group)
  : BookIsEquiv (EpiMonoFactorizations G H) (GroupHom G H) (imfact_compose G H)
  ≔ f ↦ imfact_compose_fiber_contractible G H f

{` A section of an equivalence is an equivalence (it is homotopic to the
   inverse). `}
def imfact_section_is_equiv (A B : Type) (e : Equiv A B) (s : B → A) (h : (b : B) → Id B (e .map (s b)) b)
  : BookIsEquiv B A s
  ≔ let inv ≔ equiv_inverse_map A B e in
    let hom : (b : B) → Id A (inv b) (s b)
      ≔ b ↦ concat A (inv b) (inv (e .map (s b))) (s b)
          (refl inv (inverse B (e .map (s b)) b (h b)))
          (equiv_retraction A B e (s b)) in
    transport (B → A) (BookIsEquiv B A) inv s (funext B (_ ↦ A) inv s hom)
      (book_equivalence B A (canonical_inverse_equiv A B e) .equiv)

{` lem:Im-fact-unique: Imfact : Hom(G, H) → Epi(G) ×_Group Mono(H) is an
   equivalence. `}
def image_factorization_is_equiv (G H : Group)
  : BookIsEquiv (GroupHom G H) (EpiMonoFactorizations G H) (image_factorization_map G H)
  ≔ imfact_section_is_equiv (EpiMonoFactorizations G H) (GroupHom G H)
      (native_equivalence (EpiMonoFactorizations G H) (GroupHom G H) (imfact_compose G H, imfact_compose_is_equiv G H))
      (image_factorization_map G H) (imfact_compose_section G H)

def image_factorization_equiv (G H : Group) : BookEquiv (GroupHom G H) (EpiMonoFactorizations G H)
  ≔ (image_factorization_map G H, image_factorization_is_equiv G H)

{` Imfact ∘ ∘ = id (uniqueness of the factorization). `}
def imfact_retract (G H : Group) (t : EpiMonoFactorizations G H)
  : Id (EpiMonoFactorizations G H) (image_factorization_map G H (imfact_compose G H t)) t
  ≔ let E ≔ EpiMonoFactorizations G H in
    let ce ≔ native_equivalence E (GroupHom G H) (imfact_compose G H, imfact_compose_is_equiv G H) in
    let s ≔ image_factorization_map G H in
    let inv ≔ equiv_inverse_map E (GroupHom G H) ce in
    calc
      s (imfact_compose G H t)
      = inv (imfact_compose G H (s (imfact_compose G H t)))
        by inverse E (inv (imfact_compose G H (s (imfact_compose G H t)))) (s (imfact_compose G H t))
             (equiv_retraction E (GroupHom G H) ce (s (imfact_compose G H t)))
      = inv (imfact_compose G H t) by refl inv (imfact_compose_section G H (imfact_compose G H t))
      = t by equiv_retraction E (GroupHom G H) ce t ∎
