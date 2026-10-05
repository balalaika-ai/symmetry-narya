export "bridge-00-core"
export "../../../src/935-monos-are-equalizers"
export "../../../src/936-epi-mono-iso"
export "../../../src/938-mono-cover-kernels"

{` Bridges for subgroups.tex, sec:epis (blind file 01-epi-mono). `}

{` Helpers: an equivalence gives a logical equivalence; flipping the fiber orientation. `}
def bridge_iff_of_equiv (A B : Type) (e : Equiv A B) : BlindIff A B ≔ (e .map, equiv_inverse_map A B e)

def bridge_iff_compose (A B C : Type) (e : BlindIff A B) (e' : BlindIff B C) : BlindIff A C
  ≔ (a ↦ e' .fst (e .fst a), c ↦ e .snd (e' .snd c))

def bridge_flip_fiber_equiv (A B : Type) (f : A → B) (b : B)
  : Equiv (BookFiber A B f b) (Σ A (a ↦ Id B (f a) b))
  ≔ quasi_inverse_equiv (BookFiber A B f b) (Σ A (a ↦ Id B (f a) b))
      (t ↦ (t .fst, inverse B b (f (t .fst)) (t .snd)))
      (t ↦ (t .fst, inverse B (f (t .fst)) b (t .snd)))
      (t ↦ (refl (t .fst), inverse_inverse B b (f (t .fst)) (t .snd)))
      (t ↦ (refl (t .fst), inverse_inverse B (f (t .fst)) b (t .snd)))

{` lem:injmonosurjepiSet. `}
def bridge_injmono_set : blind_injmono_set
  ≔ B C f ↦ set_injection_iff_cancellation (B .fst) (C .fst) (B .snd) (C .snd) f

def bridge_surjepi_set : blind_surjepi_set
  ≔ B C f ↦ set_surjection_iff_cancellation (B .fst) (C .fst) (B .snd) (C .snd) f

{` def:monomorphism, def:epimorphism. `}
def bridge_is_mono_prop : blind_is_mono_prop ≔ G H f ↦ is_group_monomorphism_prop G H f
def bridge_is_epi_prop : blind_is_epi_prop ≔ G H f ↦ is_group_epi_prop G H f

def bridge_def_proper_mono (G H : Group) (f : GroupHom G H)
  : Id Type (BlindIsProperMono G H f) (IsProperGroupMonomorphism G H f) ≔ refl (BlindIsProperMono G H f)

def bridge_def_proper_epi (G H : Group) (f : GroupHom G H)
  : Id Type (BlindIsProperEpi G H f) (IsProperGroupEpi G H f) ≔ refl (BlindIsProperEpi G H f)

{` exa:projections-epi. `}
def bridge_projections_epi : blind_projections_epi ≔ G1 G2 ↦ (product_proj1_epi G1 G2, product_proj2_epi G1 G2)

{` xca:mono1st-epi2nd. `}
def bridge_mono_compose : blind_mono_compose ≔ G H K f g mf mg ↦ group_monomorphism_compose G H K f g mf mg
def bridge_epi_compose : blind_epi_compose ≔ G H K f g ef eg ↦ group_epi_compose G H K f g ef eg
def bridge_epi_second : blind_epi_second ≔ G0 G1 G2 f1 f2 e ↦ group_epi_cancel G0 G1 G2 f1 f2 e
def bridge_mono_first : blind_mono_first ≔ G0 G1 G2 f1 f2 m ↦ group_monomorphism_cancel G0 G1 G2 f1 f2 m

{` lem:eq-mono-cover. `}
def bridge_eq_mono_cover : blind_eq_mono_cover
  ≔ G H f ↦
    (bridge_iff_of_equiv (IsGroupMonomorphism G H f) (IsGroupMono G H f) (eqmc_mono_injection_equiv G H f),
     (bridge_iff_of_equiv (IsGroupMono G H f) (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
        (eqmc_injection_covering_equiv G H f),
      bridge_iff_of_equiv (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
        (TruncatedMap (suc. (suc. zero.)) (BG G .carrier) (BG H .carrier) (hom_function G H f))
        (eqmc_covering_zero_truncated_equiv G H f)))

{` lem:epi-surj. (3') ⇔ 0-connected: fiberwise zero_connected_connected. `}
def bridge_connected_fibers_zero_connected (A B : Type) (f : A → B)
  : BlindIff ((b : B) → Connected (BookFiber A B f b)) (NConnectedMap (suc. zero.) A B f)
  ≔ (h b ↦ equiv_inverse_map (NConnectedType (suc. zero.) (BookFiber A B f b)) (Connected (BookFiber A B f b))
              (zero_connected_connected (BookFiber A B f b)) (h b),
     h b ↦ zero_connected_connected (BookFiber A B f b) .map (h b))

def bridge_epi_surj : blind_epi_surj
  ≔ G H f ↦
    (bridge_iff_of_equiv (IsGroupEpi G H f) (Surjective (USym G) (USym H) (usym_hom G H f))
       (gepi_epi_usym_surjective_equiv G H f),
     (bridge_iff_of_equiv (Surjective (USym G) (USym H) (usym_hom G H f))
        (ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
        (gepi_surjective_connected_fibers_equiv G H f),
      bridge_connected_fibers_zero_connected (BG G .carrier) (BG H .carrier) (hom_function G H f)))

{` con:monos-are-equalizers: our fiber Σ_{k'} (k = i k') vs the blind Σ_{k'} (i k' = k). `}
def bridge_equalizer_of_ours (G H W : Group) (i : GroupHom H G) (φ ψ : GroupHom G W)
  (e : GepiIsEqualizer H G W i φ ψ) : BlindIsEqualizer G H W i φ ψ
  ≔ (e .fst,
     K k c ↦ book_contractibility_equiv
       (BookFiber (GroupHom K H) (GroupHom K G) (k' ↦ group_hom_compose K H G k' i) k)
       (Σ (GroupHom K H) (k' ↦ Id (GroupHom K G) (group_hom_compose K H G k' i) k))
       (bridge_flip_fiber_equiv (GroupHom K H) (GroupHom K G) (k' ↦ group_hom_compose K H G k' i) k)
       .map (e .snd K k c))

def bridge_monos_are_equalizers : blind_monos_are_equalizers
  ≔ G H i m ↦
    let r ≔ gepi_mono_equalizer H G i m in
    (r .fst, (r .snd .fst, (r .snd .snd .fst,
      bridge_equalizer_of_ours G H (r .fst) i (r .snd .fst) (r .snd .snd .fst) (r .snd .snd .snd))))

{` lem:epimonoiso. `}
def bridge_epimonoiso : blind_epimonoiso
  ≔ G H f ↦ bridge_iff_of_equiv (IsGroupIso G H f) (Product (IsGroupMonomorphism G H f) (IsGroupEpi G H f))
      (gepi_iso_mono_epi_equiv G H f)
