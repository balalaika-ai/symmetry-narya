export "903-normal-subgroups"
export "1202-group-center"
export "953-coker-of-composites-restriction"
export "956-outer-automorphisms"

{` Chapter 9 (symmetry.tex 490-514), thm:hom-mod-conj, stated for
   (1-)groups G, H (the book allows higher groups in this section).

   Inn(H) acts on the set ‖BG →* BH‖₀ = ‖Hom(G, H)‖₀ through the
   Inn(H)-set X⟨K, φ⟩ ≔ ‖Hom(G, K)‖₀; here BInn(H) is the classifying type
   of Inn(H) ≔ Img(inn) of subgroups.tex (module 956), which is
   Σ_{K:Group} ‖BK÷ = BH÷‖₀ (inner_aut_classifying_equiv_group; the book's
   symmetry.tex writes ‖bunch(H) = bunch(K)‖₀, the same up to inverting
   paths). The theorem: ‖BG÷ → BH÷‖₀ ≃ ‖X_{h Inn(H)}‖₀, by the printed
   chain of equivalences. `}

def hom_conj_gset (G H : Group) : GSet (inner_aut_group H)
  ≔ z ↦ (SetTrunc (GroupHom G (z .fst .fst)), set_trunc_set (GroupHom G (z .fst .fst)))

{` The underlying set of the action is ‖Hom(G, H)‖₀ = ‖BG →* BH‖₀. `}
def hom_conj_gset_underlying (G H : Group)
  : Id Type (gset_underlying (inner_aut_group H) (hom_conj_gset G H)) (SetTrunc (GroupHom G H))
  ≔ refl (SetTrunc (GroupHom G H))

{` The untruncated core of the chain:
   Σ_{K:Group} (BK÷ = BH÷) × Hom(G, K)
   ≃ Σ_{Y} Σ_{q : Y = BH÷} Σ_{(conn, grpd)} Σ_{f : BG÷ → Y} Σ_{k : Y} (k = f sh_G)
   ≃ Σ_{Y} Σ_{q} Σ_{(conn, grpd)} (BG÷ → Y)          (contract k with f(sh_G))
   ≃ BG÷ → BH÷                                      (contract Y with q). `}
def PcgStructure (Y : Type) : Type ≔ Product (Connected Y) (isGroupoid Y)

def HomConjTotal (G H : Group) : Type
  ≔ Σ Group (K ↦ Σ (Id Type (BG K .carrier) (BG H .carrier)) (_ ↦ GroupHom G K))

def HomConjUnfolded (G H : Group) : Type
  ≔ Σ Type (Y ↦ Σ (Id Type Y (BG H .carrier)) (_ ↦ Σ (PcgStructure Y) (_ ↦
      Σ (BG G .carrier → Y) (f ↦ Σ Y (k ↦ Id Y k (f (shape G)))))))

def hom_conj_unfold_equiv (G H : Group) : Equiv (HomConjTotal G H) (HomConjUnfolded G H)
  ≔ quasi_inverse_equiv (HomConjTotal G H) (HomConjUnfolded G H)
      (u ↦ (u .fst .classifying .carrier, (u .snd .fst, ((u .fst .classifying .connected, u .fst .classifying .groupoid),
             (hom_function G (u .fst) (u .snd .snd), (shape (u .fst), hom_point G (u .fst) (u .snd .snd)))))))
      (v ↦ (mkgroup (v .fst, v .snd .snd .snd .snd .fst, v .snd .snd .fst .fst, v .snd .snd .fst .snd),
            (v .snd .fst,
             mkhom G (mkgroup (v .fst, v .snd .snd .snd .snd .fst, v .snd .snd .fst .fst, v .snd .snd .fst .snd))
               (v .snd .snd .snd .fst, v .snd .snd .snd .snd .snd))))
      (u ↦ refl u) (v ↦ refl v)

def hom_conj_core_equiv (G H : Group) : Equiv (HomConjTotal G H) (BG G .carrier → BG H .carrier)
  ≔ let XG ≔ BG G .carrier in let XH ≔ BG H .carrier in
    let F : Type → Type ≔ Y ↦ Σ (PcgStructure Y) (_ ↦ XG → Y) in
    compose_equiv (HomConjTotal G H) (HomConjUnfolded G H) (XG → XH)
      (hom_conj_unfold_equiv G H)
      (compose_equiv (HomConjUnfolded G H) (Σ Type (Y ↦ Σ (Id Type Y XH) (_ ↦ F Y))) (XG → XH)
        (family_equiv Type
          (Y ↦ Σ (Id Type Y XH) (_ ↦ Σ (PcgStructure Y) (_ ↦ Σ (XG → Y) (f ↦ Σ Y (k ↦ Id Y k (f (shape G)))))))
          (Y ↦ Σ (Id Type Y XH) (_ ↦ F Y))
          (Y ↦ family_equiv (Id Type Y XH) (_ ↦ Σ (PcgStructure Y) (_ ↦ Σ (XG → Y) (f ↦ Σ Y (k ↦ Id Y k (f (shape G))))))
            (_ ↦ F Y)
            (_ ↦ family_equiv (PcgStructure Y) (_ ↦ Σ (XG → Y) (f ↦ Σ Y (k ↦ Id Y k (f (shape G))))) (_ ↦ XG → Y)
              (_ ↦ contractible_fiber_projection (XG → Y) (f ↦ Σ Y (k ↦ Id Y k (f (shape G))))
                (f ↦ path_to_contractible Y (f (shape G)))))))
        (compose_equiv (Σ Type (Y ↦ Σ (Id Type Y XH) (_ ↦ F Y))) (Σ Type (Y ↦ Σ (Id Type XH Y) (_ ↦ F Y))) (XG → XH)
          (family_equiv Type (Y ↦ Σ (Id Type Y XH) (_ ↦ F Y)) (Y ↦ Σ (Id Type XH Y) (_ ↦ F Y))
            (Y ↦ quasi_inverse_equiv (Σ (Id Type Y XH) (_ ↦ F Y)) (Σ (Id Type XH Y) (_ ↦ F Y))
              (w ↦ (inverse Type Y XH (w .fst), w .snd)) (w ↦ (inverse Type XH Y (w .fst), w .snd))
              (w ↦ (inverse_inverse Type Y XH (w .fst), refl (w .snd)))
              (w ↦ (inverse_inverse Type XH Y (w .fst), refl (w .snd)))))
          (compose_equiv (Σ Type (Y ↦ Σ (Id Type XH Y) (_ ↦ F Y))) (F XH) (XG → XH)
            (contract_away_equiv Type XH (Y _ ↦ F Y))
            (compose_equiv (F XH) (Σ (XG → XH) (_ ↦ PcgStructure XH)) (XG → XH)
              (quasi_inverse_equiv (F XH) (Σ (XG → XH) (_ ↦ PcgStructure XH)) (w ↦ (w .snd, w .fst)) (w ↦ (w .snd, w .fst))
                (w ↦ refl w) (w ↦ refl w))
              (ch9w2_drop_contractible_prop (XG → XH) (_ ↦ PcgStructure XH)
                (_ ↦ product_prop (Connected XH) (isGroupoid XH) (connected_prop XH) (isgroupoid_isprop XH))
                (_ ↦ (bg_connected H, bg_groupoid H)))))))

{` thm:hom-mod-conj. ‖X_{h Inn(H)}‖₀ ≃ ‖BG÷ → BH÷‖₀:
   ‖Σ_{z:BInn(H)} ‖Hom(G, z)‖₀‖₀ ≃ ‖Σ_z Hom(G, z)‖₀
   ≃ ‖Σ_{K:Group} ‖BK÷ = BH÷‖₀ × Hom(G, K)‖₀ ≃ ‖Σ_K (BK÷ = BH÷) × Hom(G, K)‖₀
   ≃ ‖BG÷ → BH÷‖₀. `}
def hom_mod_conj_orbit_equiv (G H : Group)
  : Equiv (SetTrunc (ActionType (inner_aut_group H) (hom_conj_gset G H))) (SetTrunc (BG G .carrier → BG H .carrier))
  ≔ let XH ≔ BG H .carrier in
    let BI ≔ BG (inner_aut_group H) .carrier in
    let W ≔ Σ Group (K ↦ SetTrunc (Id Type (BG K .carrier) XH)) in
    let P : W → Type ≔ w ↦ GroupHom G (w .fst) in
    let S2 ≔ Σ BI (z ↦ GroupHom G (z .fst .fst)) in
    let S3 ≔ Σ W P in
    let S4 ≔ Σ (Σ Group (K ↦ GroupHom G K)) (v ↦ SetTrunc (Id Type (BG (v .fst) .carrier) XH)) in
    let S5 ≔ Σ (Σ Group (K ↦ GroupHom G K)) (v ↦ Id Type (BG (v .fst) .carrier) XH) in
    compose_equiv (SetTrunc (ActionType (inner_aut_group H) (hom_conj_gset G H))) (SetTrunc S2) (SetTrunc (BG G .carrier → XH))
      (canonical_inverse_equiv (SetTrunc S2) (SetTrunc (ActionType (inner_aut_group H) (hom_conj_gset G H)))
        (truncated_sum_equiv BI (z ↦ GroupHom G (z .fst .fst))))
      (compose_equiv (SetTrunc S2) (SetTrunc S3) (SetTrunc (BG G .carrier → XH))
        (ch9w2_set_trunc_equiv S2 S3 (sigma_pullback_equiv BI W (inner_aut_classifying_equiv_group H) P))
        (compose_equiv (SetTrunc S3) (SetTrunc S4) (SetTrunc (BG G .carrier → XH))
          (ch9w2_set_trunc_equiv S3 S4
            (quasi_inverse_equiv S3 S4 (u ↦ ((u .fst .fst, u .snd), u .fst .snd)) (u ↦ ((u .fst .fst, u .snd), u .fst .snd))
              (u ↦ refl u) (u ↦ refl u)))
          (compose_equiv (SetTrunc S4) (SetTrunc S5) (SetTrunc (BG G .carrier → XH))
            (canonical_inverse_equiv (SetTrunc S5) (SetTrunc S4)
              (truncated_sum_equiv (Σ Group (K ↦ GroupHom G K)) (v ↦ Id Type (BG (v .fst) .carrier) XH)))
            (ch9w2_set_trunc_equiv S5 (BG G .carrier → XH)
              (compose_equiv S5 (HomConjTotal G H) (BG G .carrier → XH)
                (quasi_inverse_equiv S5 (HomConjTotal G H) (u ↦ (u .fst .fst, (u .snd, u .fst .snd)))
                  (u ↦ ((u .fst, u .snd .snd), u .snd .fst)) (u ↦ refl u) (u ↦ refl u))
                (hom_conj_core_equiv G H))))))

def hom_mod_conj_equiv (G H : Group)
  : Equiv (SetTrunc (BG G .carrier → BG H .carrier)) (SetTrunc (ActionType (inner_aut_group H) (hom_conj_gset G H)))
  ≔ canonical_inverse_equiv (SetTrunc (ActionType (inner_aut_group H) (hom_conj_gset G H))) (SetTrunc (BG G .carrier → BG H .carrier))
      (hom_mod_conj_orbit_equiv G H)
