export "740-abstract-restriction-induction"
export "709-groups-are-abstract-groups"
export "710-hom-delooping"

{` Chapter 7 (absgroup.tex), "Direct equivalence of categories": concr on
   morphisms. For φ : G → H, Bconcr(φ) is the restriction of φ_! to the
   torsors (φ_! maps G-torsors to H-torsors because φ_!(P_G) = P_H,
   xca:Bconcr-OK (1)), pointed by the inverse of that identification.

   Naturality of r (proof of thm:concr-equiv-cats): abstr(concr(φ)) sends the
   symmetry T_G(s) of P_G attached to s (r_G(s) = right multiplication by
   s⁻¹) to T_H(φ(s)). The book's footnote computes ap of φ_! on
   identifications; here agset_induce_ap_iso and the explicit isomorphism
   [t, x] ↦ t φ(x) do this. Functoriality (xca:Bconcr-OK (2)) then follows
   from faithfulness of abstr (lem:homomabstrconcr). `}

{` Pointwise consequence of an identification of isomorphisms. `}
def agset_iso_map_path (G : AbstractGroup) (X Y : AbstractGSet G) (f g : AbstractGSetIso G X Y)
  (e : Id (AbstractGSetIso G X Y) f g) (x : agset_carrier G X)
  : Id (agset_carrier G Y) (f .fst .map x) (g .fst .map x)
  ≔ refl ((i ↦ i .fst .map x) : AbstractGSetIso G X Y → agset_carrier G Y) e

def transport_cancel_inverse (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (b : B y)
  : Id (B y) (transport A B x y p (transport A B y x (inverse A x y p) b)) b
  ≔ J A x (y p ↦ (b : B y) → Id (B y) (transport A B x y p (transport A B y x (inverse A x y p) b)) b)
      (b ↦ concat (B x) (transport A B x x (refl x) (transport A B x x (inverse A x x (refl x)) b))
        (transport A B x x (inverse A x x (refl x)) b) b
        (transport_refl A B x (transport A B x x (inverse A x x (refl x)) b))
        (concat (B x) (transport A B x x (inverse A x x (refl x)) b) (transport A B x x (refl x) b) b
          (refl ((q ↦ transport A B x x q b) : Id A x x → B x) (inverse_refl A x))
          (transport_refl A B x b)))
      y p b

{` The pointing identification of Bconcr(φ): (φ_! P_G)-torsor = P_H, as an
   explicit pair so that its first component is definitionally
   (φ_! P_G = P_H)⁻¹. `}
def concr_hom_torsor (G H : AbstractGroup) (φ : AbstractHom G H) (X : AbstractTorsors G) : AbstractTorsors H
  ≔ let PG ≔ agset_principal G in let PH ≔ agset_principal H in
    let ipp ≔ induce_principal_path G H φ in
    (agset_induce G H φ (X .fst),
     mere_rec (Id (AbstractGSet G) PG (X .fst)) (Mere (Id (AbstractGSet H) PH (agset_induce G H φ (X .fst))))
       (mere_isprop (Id (AbstractGSet H) PH (agset_induce G H φ (X .fst))))
       (p ↦ mere (Id (AbstractGSet H) PH (agset_induce G H φ (X .fst)))
         (concat (AbstractGSet H) PH (agset_induce G H φ PG) (agset_induce G H φ (X .fst))
           (inverse (AbstractGSet H) (agset_induce G H φ PG) PH ipp) (refl (agset_induce G H φ) p)))
       (X .snd))

def concr_hom_point (G H : AbstractGroup) (φ : AbstractHom G H)
  : Id (AbstractTorsors H) (abstract_principal_torsor H) (concr_hom_torsor G H φ (abstract_principal_torsor G))
  ≔ let PH ≔ agset_principal H in let QH ≔ agset_induce G H φ (agset_principal G) in
    let k0 ≔ inverse (AbstractGSet H) QH PH (induce_principal_path G H φ) in
    (k0,
     pathover_hlevel zero. (AbstractGSet H) (X ↦ Mere (Id (AbstractGSet H) PH X))
       (X ↦ prop_to_hlevel_one (Mere (Id (AbstractGSet H) PH X)) (mere_isprop (Id (AbstractGSet H) PH X)))
       PH QH k0 (abstract_principal_torsor H .snd) (concr_hom_torsor G H φ (abstract_principal_torsor G) .snd) .center)

{` concr on morphisms: Bconcr(φ) is the restriction of φ_! to torsors. `}
def concr_hom (G H : AbstractGroup) (φ : AbstractHom G H) : GroupHom (concr G) (concr H)
  ≔ mkhom (concr G) (concr H) (concr_hom_torsor G H φ, concr_hom_point G H φ)

{` Transport in the family of underlying sets of torsors. `}
def TorsorCarrier (G : AbstractGroup) (U : AbstractTorsors G) : Type ≔ agset_carrier G (U .fst)

{` The isomorphism of P_H attached to a symmetry ρ of the principal torsor
   acts by transport. `}
def concr_usym_iso_map (G : AbstractGroup) (ρ : USym (concr G)) (t : G .carrier)
  : Id (G .carrier) (concr_usym_iso_equiv G .map ρ .fst .map t)
      (transport (AbstractTorsors G) (TorsorCarrier G) (abstract_principal_torsor G) (abstract_principal_torsor G) ρ t)
  ≔ refl (transport (AbstractTorsors G) (TorsorCarrier G) (abstract_principal_torsor G) (abstract_principal_torsor G) ρ t)

{` The map of φ_!(P_G) ≅ P_H is transport along φ_!(P_G) = P_H. `}
def induce_principal_transport (G H : AbstractGroup) (φ : AbstractHom G H) (y : AgsetInduceCarrier G H φ (agset_principal G))
  : Id (H .carrier)
      (transport (AbstractGSet H) (agset_carrier H) (agset_induce G H φ (agset_principal G)) (agset_principal H)
        (induce_principal_path G H φ) y)
      (induce_principal_map G H φ y)
  ≔ agset_iso_map_path H (agset_induce G H φ (agset_principal G)) (agset_principal H)
      (agset_path_to_iso H (agset_induce G H φ (agset_principal G)) (agset_principal H) (induce_principal_path G H φ))
      (induce_principal_iso G H φ)
      (agset_path_from_iso_section H (agset_induce G H φ (agset_principal G)) (agset_principal H) (induce_principal_iso G H φ)) y

{` c(φ_!(r_G s)(y)) = c(y) · φ(s)⁻¹ for c : [t, x] ↦ t φ(x). `}
def induce_principal_r_map (G H : AbstractGroup) (φ : AbstractHom G H) (s : G .carrier)
  (y : AgsetInduceCarrier G H φ (agset_principal G))
  : Id (H .carrier)
      (induce_principal_map G H φ
        (agset_induce_fun G H φ (agset_principal G) (agset_principal G) (abstract_r_map G s .fst .map) (abstract_r_map G s .snd) y))
      (H .mul (induce_principal_map G H φ y) (H .inv (φ .fst s)))
  ≔ let T ≔ H .carrier in let S ≔ G .carrier in let P ≔ agset_principal G in let f ≔ φ .fst in
    quotient_prop_induction (Product T S) (agset_induce_relation G H φ P)
      (y ↦ Id T (induce_principal_map G H φ (agset_induce_fun G H φ P P (abstract_r_map G s .fst .map) (abstract_r_map G s .snd) y))
        (H .mul (induce_principal_map G H φ y) (H .inv (f s))))
      (y ↦ abstract_group_set H
        (induce_principal_map G H φ (agset_induce_fun G H φ P P (abstract_r_map G s .fst .map) (abstract_r_map G s .snd) y))
        (H .mul (induce_principal_map G H φ y) (H .inv (f s))))
      (u ↦ calc
         H .mul (u .fst) (f (G .mul (u .snd) (G .inv s))) = H .mul (u .fst) (H .mul (f (u .snd)) (f (G .inv s)))
           by refl (H .mul (u .fst)) (φ .snd (u .snd) (G .inv s))
         = H .mul (u .fst) (H .mul (f (u .snd)) (H .inv (f s)))
           by refl ((v ↦ H .mul (u .fst) (H .mul (f (u .snd)) v)) : T → T) (abstract_hom_preserves_inv G H f (φ .snd) s)
         = H .mul (H .mul (u .fst) (f (u .snd))) (H .inv (f s)) by H .laws .assoc (u .fst) (f (u .snd)) (H .inv (f s)) ∎)
      y

{` Naturality of r (proof of thm:concr-equiv-cats): the symmetry
   abstr(concr φ)(T_G(s)) acts on P_H as right multiplication by φ(s)⁻¹. `}
def concr_hom_usym_action (G H : AbstractGroup) (φ : AbstractHom G H) (s : G .carrier) (t : H .carrier)
  : Id (H .carrier)
      (transport (AbstractTorsors H) (TorsorCarrier H) (abstract_principal_torsor H) (abstract_principal_torsor H)
        (usym_hom (concr G) (concr H) (concr_hom G H φ) (concr_usym_of G s)) t)
      (H .mul t (H .inv (φ .fst s)))
  ≔ let T ≔ H .carrier in
    let TorH ≔ AbstractTorsors H in let TorG ≔ AbstractTorsors G in
    let P0H ≔ abstract_principal_torsor H in let P0G ≔ abstract_principal_torsor G in
    let B ≔ concr_hom_torsor G H φ in
    let k ≔ concr_hom_point G H φ in
    let BP ≔ B P0G in
    let Ts ≔ concr_usym_of G s in
    let a ≔ refl B Ts in
    let PH ≔ agset_principal H in let PG ≔ agset_principal G in
    let QH ≔ agset_induce G H φ PG in
    let ipp ≔ induce_principal_path G H φ in
    let F ≔ TorsorCarrier H in
    let tr ≔ (U V : TorH) (p : Id TorH U V) (z : F U) ↦ transport TorH F U V p z in
    let y0 : F BP ≔ tr P0H BP k t in
    let A ≔ (y : F BP) ↦ agset_induce_fun G H φ PG PG (abstract_r_map G s .fst .map) (abstract_r_map G s .snd) y in
    let fs ≔ concr_usym_iso_equiv G .map Ts in
    let hs : (x : G .carrier) → Id (G .carrier) (fs .fst .map x) (abstract_r_map G s .fst .map x)
      ≔ agset_iso_map_path G PG PG fs (abstract_r_map G s) (concr_usym_of_iso G s) in
    let step_a : (y : F BP) → Id (F BP) (tr BP BP a y) (A y)
      ≔ y ↦ concat (F BP) (tr BP BP a y)
          (agset_induce_fun G H φ PG PG (fs .fst .map) (fs .snd) y) (A y)
          (agset_induce_ap_map G H φ PG PG (Ts .fst) y)
          (agset_induce_fun_homotopy G H φ PG PG (fs .fst .map) (abstract_r_map G s .fst .map) (fs .snd)
            (abstract_r_map G s .snd) hs y) in
    let y1 ≔ A y0 in
    let res ≔ tr BP P0H (inverse TorH P0H BP k) y1 in
    let back_res : Id (F BP) (tr P0H BP k res) y1 ≔ transport_cancel_inverse TorH F P0H BP k y1 in
    let c ≔ induce_principal_map G H φ in
    let res_c : Id T res (c y1)
      ≔ calc
          res = transport (AbstractGSet H) (agset_carrier H) QH PH ipp
                  (transport (AbstractGSet H) (agset_carrier H) PH QH (inverse (AbstractGSet H) QH PH ipp) res)
            by inverse T (transport (AbstractGSet H) (agset_carrier H) QH PH ipp
                  (transport (AbstractGSet H) (agset_carrier H) PH QH (inverse (AbstractGSet H) QH PH ipp) res)) res
              (transport_cancel_inverse (AbstractGSet H) (agset_carrier H) QH PH ipp res)
          = transport (AbstractGSet H) (agset_carrier H) QH PH ipp y1
            by refl (transport (AbstractGSet H) (agset_carrier H) QH PH ipp) back_res
          = c y1 by induce_principal_transport G H φ y1 ∎ in
    let y0_c : Id T (c y0) t
      ≔ calc
          c y0 = transport (AbstractGSet H) (agset_carrier H) QH PH ipp y0
            by inverse T (transport (AbstractGSet H) (agset_carrier H) QH PH ipp y0) (c y0) (induce_principal_transport G H φ y0)
          = t by transport_cancel_inverse (AbstractGSet H) (agset_carrier H) QH PH ipp t ∎ in
    calc
      tr P0H P0H (usym_hom (concr G) (concr H) (concr_hom G H φ) Ts) t
        = tr BP P0H (concat TorH BP BP P0H a (inverse TorH P0H BP k)) y0
        by transport_concat TorH F P0H BP P0H k (concat TorH BP BP P0H a (inverse TorH P0H BP k)) t
      = tr BP P0H (inverse TorH P0H BP k) (tr BP BP a y0)
        by transport_concat TorH F BP BP P0H a (inverse TorH P0H BP k) y0
      = res by refl (tr BP P0H (inverse TorH P0H BP k)) (step_a y0)
      = c y1 by res_c
      = H .mul (c y0) (H .inv (φ .fst s)) by induce_principal_r_map G H φ s y0
      = H .mul t (H .inv (φ .fst s)) by refl ((v ↦ H .mul v (H .inv (φ .fst s))) : T → T) y0_c ∎

{` Naturality of r: abstr(concr φ)(T_G(s)) = T_H(φ(s)). `}
def concr_hom_usym_natural (G H : AbstractGroup) (φ : AbstractHom G H) (s : G .carrier)
  : Id (USym (concr H)) (usym_hom (concr G) (concr H) (concr_hom G H φ) (concr_usym_of G s)) (concr_usym_of H (φ .fst s))
  ≔ let PH ≔ agset_principal H in
    let I ≔ AbstractGSetIso H PH PH in
    let E ≔ concr_usym_iso_equiv H in
    let lhs ≔ usym_hom (concr G) (concr H) (concr_hom G H φ) (concr_usym_of G s) in
    equivalence_injective (USym (concr H)) I E lhs (concr_usym_of H (φ .fst s))
      (concat I (E .map lhs) (abstract_r_map H (φ .fst s)) (E .map (concr_usym_of H (φ .fst s)))
        (agset_iso_path H PH PH (E .map lhs) (abstract_r_map H (φ .fst s)) (t ↦ concr_hom_usym_action G H φ s t))
        (inverse I (E .map (concr_usym_of H (φ .fst s))) (abstract_r_map H (φ .fst s)) (concr_usym_of_iso H (φ .fst s))))

{` abstr(concr φ) = T_H ∘ φ ∘ T_G⁻¹. `}
def concr_usym_of_inverse (G : AbstractGroup) (ρ : USym (concr G)) : G .carrier
  ≔ equiv_inverse_map (G .carrier) (USym (concr G)) (concr_abstr_carrier_equiv G) ρ

def concr_hom_abstr (G H : AbstractGroup) (φ : AbstractHom G H) (ρ : USym (concr G))
  : Id (USym (concr H)) (usym_hom (concr G) (concr H) (concr_hom G H φ) ρ) (concr_usym_of H (φ .fst (concr_usym_of_inverse G ρ)))
  ≔ let C ≔ USym (concr G) in
    concat (USym (concr H)) (usym_hom (concr G) (concr H) (concr_hom G H φ) ρ)
      (usym_hom (concr G) (concr H) (concr_hom G H φ) (concr_usym_of G (concr_usym_of_inverse G ρ)))
      (concr_usym_of H (φ .fst (concr_usym_of_inverse G ρ)))
      (refl (usym_hom (concr G) (concr H) (concr_hom G H φ))
        (inverse C (concr_usym_of G (concr_usym_of_inverse G ρ)) ρ
          (equiv_counit (G .carrier) C (concr_abstr_carrier_equiv G) ρ)))
      (concr_hom_usym_natural G H φ (concr_usym_of_inverse G ρ))

{` xca:Bconcr-OK (2): concr is a functor. `}
def concr_hom_id (G : AbstractGroup) : Id (GroupHom (concr G) (concr G)) (concr_hom G G (abstract_hom_id G)) (group_hom_id (concr G))
  ≔ let C ≔ USym (concr G) in
    equivalence_injective (GroupHom (concr G) (concr G)) (AbstractHom (abstr (concr G)) (abstr (concr G)))
      (abstr_hom_equiv (concr G) (concr G)) (concr_hom G G (abstract_hom_id G)) (group_hom_id (concr G))
      (abstract_hom_ext (abstr (concr G)) (abstr (concr G))
        (abstr_hom (concr G) (concr G) (concr_hom G G (abstract_hom_id G))) (abstr_hom (concr G) (concr G) (group_hom_id (concr G)))
        (ρ ↦ calc
           usym_hom (concr G) (concr G) (concr_hom G G (abstract_hom_id G)) ρ = concr_usym_of G (concr_usym_of_inverse G ρ)
             by concr_hom_abstr G G (abstract_hom_id G) ρ
           = ρ by equiv_counit (G .carrier) C (concr_abstr_carrier_equiv G) ρ
           = usym_hom (concr G) (concr G) (group_hom_id (concr G)) ρ
             by inverse C (usym_hom (concr G) (concr G) (group_hom_id (concr G)) ρ) ρ (usym_hom_id (concr G) ρ) ∎))

def concr_hom_compose (G H K : AbstractGroup) (φ : AbstractHom G H) (ψ : AbstractHom H K)
  : Id (GroupHom (concr G) (concr K)) (concr_hom G K (abstract_hom_compose G H K φ ψ))
      (group_hom_compose (concr G) (concr H) (concr K) (concr_hom G H φ) (concr_hom H K ψ))
  ≔ let CK ≔ USym (concr K) in
    let lhs ≔ concr_hom G K (abstract_hom_compose G H K φ ψ) in
    let rhs ≔ group_hom_compose (concr G) (concr H) (concr K) (concr_hom G H φ) (concr_hom H K ψ) in
    equivalence_injective (GroupHom (concr G) (concr K)) (AbstractHom (abstr (concr G)) (abstr (concr K)))
      (abstr_hom_equiv (concr G) (concr K)) lhs rhs
      (abstract_hom_ext (abstr (concr G)) (abstr (concr K)) (abstr_hom (concr G) (concr K) lhs) (abstr_hom (concr G) (concr K) rhs)
        (ρ ↦ let s ≔ concr_usym_of_inverse G ρ in
          calc
            usym_hom (concr G) (concr K) lhs ρ = concr_usym_of K (ψ .fst (φ .fst s))
              by concr_hom_abstr G K (abstract_hom_compose G H K φ ψ) ρ
            = concr_usym_of K (ψ .fst (concr_usym_of_inverse H (concr_usym_of H (φ .fst s))))
              by refl ((x ↦ concr_usym_of K (ψ .fst x)) : H .carrier → CK)
                (inverse (H .carrier) (concr_usym_of_inverse H (concr_usym_of H (φ .fst s))) (φ .fst s)
                  (equiv_retraction (H .carrier) (USym (concr H)) (concr_abstr_carrier_equiv H) (φ .fst s)))
            = usym_hom (concr H) (concr K) (concr_hom H K ψ) (concr_usym_of H (φ .fst s))
              by inverse CK (usym_hom (concr H) (concr K) (concr_hom H K ψ) (concr_usym_of H (φ .fst s)))
                (concr_usym_of K (ψ .fst (concr_usym_of_inverse H (concr_usym_of H (φ .fst s)))))
                (concr_hom_abstr H K ψ (concr_usym_of H (φ .fst s)))
            = usym_hom (concr H) (concr K) (concr_hom H K ψ) (usym_hom (concr G) (concr H) (concr_hom G H φ) ρ)
              by refl (usym_hom (concr H) (concr K) (concr_hom H K ψ))
                (inverse (USym (concr H)) (usym_hom (concr G) (concr H) (concr_hom G H φ) ρ) (concr_usym_of H (φ .fst s))
                  (concr_hom_abstr G H φ ρ))
            = usym_hom (concr G) (concr K) rhs ρ
              by inverse CK (usym_hom (concr G) (concr K) rhs ρ)
                (usym_hom (concr H) (concr K) (concr_hom H K ψ) (usym_hom (concr G) (concr H) (concr_hom G H φ) ρ))
                (loops_map_compose_pointwise (BG (concr G)) (BG (concr H)) (BG (concr K))
                  (hom_B (concr G) (concr H) (concr_hom G H φ)) (hom_B (concr H) (concr K) (concr_hom H K ψ)) ρ) ∎))
