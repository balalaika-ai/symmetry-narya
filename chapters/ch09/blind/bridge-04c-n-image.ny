export "04-images"
export "../../../src/939-pointed-factorizations"
export "../../../src/607-terminal-initial-objects"
export "../../../src/991-n-image-groupoids"

{` Bridges for rem:n-im-ptd-map (subgroups.tex 889, blind file 04-images). `}

def bridge_def_ptd_fact (X Z : Pointed) (f : BookPointedMap X Z) : Id Type (BlindPtdFact X Z f) (PfactPointed X Z f)
  ≔ refl (BlindPtdFact X Z f)

def bridge_def_ptd_fact_n (k : Nat) (X Z : Pointed) (f : BookPointedMap X Z)
  : Id Type (BlindPtdFactN k X Z f) (PfactPointedN (suc. k) X Z f) ≔ refl (BlindPtdFactN k X Z f)

def bridge_def_ptd_fact_minus_two (X Z : Pointed) (f : BookPointedMap X Z)
  : Id Type (BlindPtdFactMinusTwo X Z f) (PfactPointedN zero. X Z f) ≔ refl (BlindPtdFactMinusTwo X Z f)

def bridge_ptd_n_image_contractible : blind_ptd_n_image_contractible
  ≔ k X Z f ↦ pfact_n_image_pointed_contractible (suc. k) X Z f

def bridge_ptd_minus_two_image_contractible : blind_ptd_minus_two_image_contractible
  ≔ X Z f ↦ pfact_n_image_pointed_contractible zero. X Z f

def bridge_n_image_factor_props : blind_n_image_factor_props
  ≔ k A B f ↦ (n_image_factor_connected k A B f, n_image_include_truncated k A B f)

{` Any factorization with n-connected left and n-truncated right factor is the n-image one
   (contractibility, thm:n-im-univ-prop), so i⁻¹(z) ≃ ‖f⁻¹(z)‖_n. `}
def bridge_n_image_fiber_equiv : blind_n_image_fiber_equiv
  ≔ k X Y Z f p i h hp hi z ↦
    let U ≔ Σ (Factorizations X Z f) (NFactorizationPropertiesFrom (suc. k) X Z f) in
    let c ≔ n_image_universal_property_all (suc. k) X Z f in
    let t0 : U ≔ ((NImage k X Z f, (n_image_factor k X Z f, (n_image_include k X Z f, n_image_triangle k X Z f))),
                  (n_image_factor_connected k X Z f, n_image_include_truncated k X Z f)) in
    let t1 : U ≔ ((Y, (p, (i, h))), (hp, hi)) in
    let F ≔ BookFiber X Z f z in
    let P ≔ (t ↦ BookEquiv (Trunc k F) (BookFiber (t .fst .fst) Z (t .fst .snd .snd .fst) z)) : U → Type in
    transport U P t0 t1 (book_contractible_paths U c t0 t1)
      (book_equivalence (Trunc k F) (BookFiber (NImage k X Z f) Z (n_image_include k X Z f) z)
        (canonical_inverse_equiv (BookFiber (NImage k X Z f) Z (n_image_include k X Z f) z) (Trunc k F)
          (n_image_include_fiber_equiv k X Z f z)))

def bridge_n_image_connected_groupoid : blind_n_image_connected_groupoid
  ≔ k X Z f hX gX hZ gZ ↦ n_image_connected_groupoid k X Z f hX gX gZ
