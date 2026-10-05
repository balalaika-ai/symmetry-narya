export "742-concr-on-homomorphisms"
export "686-category-of-groups"
export "640-cat-equivalence-fully-faithful"
export "620-natural-isomorphisms"

{` Chapter 7 (absgroup.tex), thm:concr-equiv-cats: concr is a functor from
   abstract groups to groups and an equivalence of categories, with natural
   isomorphisms q : id ⇒ concr ∘ abstr and r : id ⇒ abstr ∘ concr. The
   categories are the wild precategories GroupWild (module 686) and
   AbstractGroupWild (below; hom-sets by abstract_hom_set). The equivalence
   is obtained with cat_equivalence_from_nat_isos (module 640), both for
   concr (as printed) and for abstr. `}

{` The (pre)category of abstract groups; comp G H K ψ φ is ψ ∘ φ. `}
def AbstractGroupWild : WildPrecat
  ≔ (ob ≔ AbstractGroup,
     hom ≔ AbstractHom,
     idn ≔ abstract_hom_id,
     comp ≔ G H K ψ φ ↦ abstract_hom_compose G H K φ ψ,
     lu ≔ G H φ ↦ abstract_hom_compose_id_right G H φ,
     ru ≔ G H φ ↦ abstract_hom_compose_id_left G H φ,
     assoc ≔ G H K L φ ψ χ ↦ abstract_hom_compose_assoc G H K L φ ψ χ)

def AbstractGroupPrecat : Precat ≔ (AbstractGroupWild, G H ↦ abstract_hom_set G H)

{` The functor abstr : Group → AbsGroup (def:abstrisfunctor, xca:abshomcomposition). `}
def abstr_functor : WildFunctor GroupWild AbstractGroupWild
  ≔ (obj ≔ abstr,
     mor ≔ abstr_hom,
     map_id ≔ abstr_hom_id,
     map_comp ≔ G H K f g ↦ abstr_hom_compose G H K f g)

{` The functor concr : AbsGroup → Group (xca:Bconcr-OK (2)). `}
def concr_functor : WildFunctor AbstractGroupWild GroupWild
  ≔ (obj ≔ concr,
     mor ≔ concr_hom,
     map_id ≔ concr_hom_id,
     map_comp ≔ G H K φ ψ ↦ concr_hom_compose G H K φ ψ)

{` Components of r and of its inverse. `}
def r_component (G : AbstractGroup) : AbstractHom G (abstr (concr G))
  ≔ abstract_iso_hom G (abstr (concr G)) (concr_abstr_iso G)

def r_inverse_component (G : AbstractGroup) : AbstractHom (abstr (concr G)) G
  ≔ abstract_iso_hom (abstr (concr G)) G (abstract_iso_inverse G (abstr (concr G)) (concr_abstr_iso G))

def r_component_is_iso (G : AbstractGroup) : CatIsIso AbstractGroupWild G (abstr (concr G)) (r_component G)
  ≔ let S ≔ G .carrier in let C ≔ USym (concr G) in let e ≔ concr_abstr_carrier_equiv G in
    ((r_inverse_component G,
      abstract_hom_ext (abstr (concr G)) (abstr (concr G))
        (abstract_hom_compose (abstr (concr G)) G (abstr (concr G)) (r_inverse_component G) (r_component G))
        (abstract_hom_id (abstr (concr G))) (y ↦ equiv_counit S C e y)),
     (r_inverse_component G,
      abstract_hom_ext G G (abstract_hom_compose G (abstr (concr G)) G (r_component G) (r_inverse_component G))
        (abstract_hom_id G) (x ↦ equiv_retraction S C e x)))

def r_inverse_component_is_iso (G : AbstractGroup) : CatIsIso AbstractGroupWild (abstr (concr G)) G (r_inverse_component G)
  ≔ let S ≔ G .carrier in let C ≔ USym (concr G) in let e ≔ concr_abstr_carrier_equiv G in
    ((r_component G,
      abstract_hom_ext G G (abstract_hom_compose G (abstr (concr G)) G (r_component G) (r_inverse_component G))
        (abstract_hom_id G) (x ↦ equiv_retraction S C e x)),
     (r_component G,
      abstract_hom_ext (abstr (concr G)) (abstr (concr G))
        (abstract_hom_compose (abstr (concr G)) G (abstr (concr G)) (r_inverse_component G) (r_component G))
        (abstract_hom_id (abstr (concr G))) (y ↦ equiv_counit S C e y)))

{` r : id ⇒ abstr ∘ concr is a natural isomorphism (naturality of r in
   the proof of thm:concr-equiv-cats). `}
def r_natural_iso
  : NatIso AbstractGroupWild AbstractGroupWild (functor_identity AbstractGroupWild)
      (functor_compose AbstractGroupWild GroupWild AbstractGroupWild abstr_functor concr_functor)
  ≔ ((component ≔ r_component,
      natural ≔ G H φ ↦ abstract_hom_ext G (abstr (concr H))
        (abstract_hom_compose G (abstr (concr G)) (abstr (concr H)) (r_component G) (abstr_hom (concr G) (concr H) (concr_hom G H φ)))
        (abstract_hom_compose G H (abstr (concr H)) φ (r_component H))
        (s ↦ concr_hom_usym_natural G H φ s)),
     r_component_is_iso)

def r_inverse_natural_iso
  : NatIso AbstractGroupWild AbstractGroupWild
      (functor_compose AbstractGroupWild GroupWild AbstractGroupWild abstr_functor concr_functor)
      (functor_identity AbstractGroupWild)
  ≔ ((component ≔ r_inverse_component,
      natural ≔ G H φ ↦ abstract_hom_ext (abstr (concr G)) H
        (abstract_hom_compose (abstr (concr G)) G H (r_inverse_component G) φ)
        (abstract_hom_compose (abstr (concr G)) (abstr (concr H)) H (abstr_hom (concr G) (concr H) (concr_hom G H φ)) (r_inverse_component H))
        (ρ ↦ inverse (H .carrier) (concr_usym_of_inverse H (usym_hom (concr G) (concr H) (concr_hom G H φ) ρ))
          (φ .fst (concr_usym_of_inverse G ρ))
          (concat (H .carrier) (concr_usym_of_inverse H (usym_hom (concr G) (concr H) (concr_hom G H φ) ρ))
            (concr_usym_of_inverse H (concr_usym_of H (φ .fst (concr_usym_of_inverse G ρ))))
            (φ .fst (concr_usym_of_inverse G ρ))
            (refl (concr_usym_of_inverse H) (concr_hom_abstr G H φ ρ))
            (equiv_retraction (H .carrier) (USym (concr H)) (concr_abstr_carrier_equiv H) (φ .fst (concr_usym_of_inverse G ρ)))))),
     r_inverse_component_is_iso)

{` abstr(q_G) is the isomorphism T_{abstr G} of thm:Groupsareidentitytypes:
   the symmetry ω of sh_G goes to the automorphism p ↦ p ω⁻¹ of P. `}
def q_hom_usym_action (G : Group) (ω : USym G) (p : USym G)
  : Id (USym G)
      (transport (AbstractTorsors (abstr G)) (TorsorCarrier (abstr G)) (abstract_principal_torsor (abstr G))
        (abstract_principal_torsor (abstr G)) (usym_hom G (concr (abstr G)) (q_hom G) ω) p)
      (concat (BG G .carrier) (shape G) (shape G) (shape G) (inverse (BG G .carrier) (shape G) (shape G) ω) p)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    let Tor ≔ AbstractTorsors (abstr G) in let F ≔ TorsorCarrier (abstr G) in
    let P0 ≔ abstract_principal_torsor (abstr G) in let Q ≔ bq_map G a in
    let k ≔ bq_point G in let apq ≔ refl (bq_map G) ω in
    let P ≔ agset_principal (abstr G) in
    let tr ≔ (U V : Tor) (r : Id Tor U V) (z : F U) ↦ transport Tor F U V r z in
    let p' ≔ tr P0 Q k p in
    let p'_eq : Id (USym G) p' p ≔ transport_refl (AbstractGSet (abstr G)) (agset_carrier (abstr G)) P p in
    let z ≔ tr Q Q apq p' in
    let back : Id (USym G) (tr Q P0 (inverse Tor P0 Q k) z) z
      ≔ concat (USym G) (tr Q P0 (inverse Tor P0 Q k) z) (tr P0 Q k (tr Q P0 (inverse Tor P0 Q k) z)) z
          (inverse (USym G) (tr P0 Q k (tr Q P0 (inverse Tor P0 Q k) z)) (tr Q P0 (inverse Tor P0 Q k) z)
            (transport_refl (AbstractGSet (abstr G)) (agset_carrier (abstr G)) P (tr Q P0 (inverse Tor P0 Q k) z)))
          (transport_cancel_inverse Tor F P0 Q k z) in
    calc
      tr P0 P0 (usym_hom G (concr (abstr G)) (q_hom G) ω) p
        = tr Q P0 (concat Tor Q Q P0 apq (inverse Tor P0 Q k)) p'
        by transport_concat Tor F P0 Q P0 k (concat Tor Q Q P0 apq (inverse Tor P0 Q k)) p
      = tr Q P0 (inverse Tor P0 Q k) z by transport_concat Tor F Q Q P0 apq (inverse Tor P0 Q k) p'
      = z by back
      = path_preinv A a a a ω p' by bq_ap_iso_map G a a ω p'
      = path_preinv A a a a ω p by refl (path_preinv A a a a ω) p'_eq ∎

def q_hom_usym (G : Group) (ω : USym G)
  : Id (USym (concr (abstr G))) (usym_hom G (concr (abstr G)) (q_hom G) ω) (concr_usym_of (abstr G) ω)
  ≔ let aG ≔ abstr G in let P ≔ agset_principal aG in
    let I ≔ AbstractGSetIso aG P P in
    let E ≔ concr_usym_iso_equiv aG in
    let lhs ≔ usym_hom G (concr aG) (q_hom G) ω in
    equivalence_injective (USym (concr aG)) I E lhs (concr_usym_of aG ω)
      (concat I (E .map lhs) (abstract_r_map aG ω) (E .map (concr_usym_of aG ω))
        (agset_iso_path aG P P (E .map lhs) (abstract_r_map aG ω) (p ↦ q_hom_usym_action G ω p))
        (inverse I (E .map (concr_usym_of aG ω)) (abstract_r_map aG ω) (concr_usym_of_iso aG ω)))

{` q : id ⇒ concr ∘ abstr is a natural isomorphism. The naturality square
   is proved for an arbitrary homomorphism c : concr(abstr G) → concr(abstr H)
   with the property of concr(abstr f) on the symmetries T(ω)
   (concr_hom_usym_natural), so that concr_hom is never unfolded while
   checking (a direct proof took more than 40 minutes to check). `}
def q_natural_generic (G H : Group) (f : GroupHom G H) (c : GroupHom (concr (abstr G)) (concr (abstr H)))
  (hc : (ω : USym G) → Id (USym (concr (abstr H)))
     (usym_hom (concr (abstr G)) (concr (abstr H)) c (concr_usym_of (abstr G) ω)) (concr_usym_of (abstr H) (usym_hom G H f ω)))
  : Id (GroupHom G (concr (abstr H)))
      (group_hom_compose G (concr (abstr G)) (concr (abstr H)) (q_hom G) c)
      (group_hom_compose G H (concr (abstr H)) f (q_hom H))
  ≔ let CH ≔ USym (concr (abstr H)) in
    let lhs ≔ group_hom_compose G (concr (abstr G)) (concr (abstr H)) (q_hom G) c in
    let rhs ≔ group_hom_compose G H (concr (abstr H)) f (q_hom H) in
    equivalence_injective (GroupHom G (concr (abstr H))) (AbstractHom (abstr G) (abstr (concr (abstr H))))
      (abstr_hom_equiv G (concr (abstr H))) lhs rhs
      (abstract_hom_ext (abstr G) (abstr (concr (abstr H))) (abstr_hom G (concr (abstr H)) lhs) (abstr_hom G (concr (abstr H)) rhs)
        (ω ↦ calc
           usym_hom G (concr (abstr H)) lhs ω
             = usym_hom (concr (abstr G)) (concr (abstr H)) c (usym_hom G (concr (abstr G)) (q_hom G) ω)
             by loops_map_compose_pointwise (BG G) (BG (concr (abstr G))) (BG (concr (abstr H)))
               (hom_B G (concr (abstr G)) (q_hom G)) (hom_B (concr (abstr G)) (concr (abstr H)) c) ω
           = usym_hom (concr (abstr G)) (concr (abstr H)) c (concr_usym_of (abstr G) ω)
             by refl (usym_hom (concr (abstr G)) (concr (abstr H)) c) (q_hom_usym G ω)
           = concr_usym_of (abstr H) (usym_hom G H f ω) by hc ω
           = usym_hom H (concr (abstr H)) (q_hom H) (usym_hom G H f ω)
             by inverse CH (usym_hom H (concr (abstr H)) (q_hom H) (usym_hom G H f ω)) (concr_usym_of (abstr H) (usym_hom G H f ω))
               (q_hom_usym H (usym_hom G H f ω))
           = usym_hom G (concr (abstr H)) rhs ω
             by inverse CH (usym_hom G (concr (abstr H)) rhs ω) (usym_hom H (concr (abstr H)) (q_hom H) (usym_hom G H f ω))
               (loops_map_compose_pointwise (BG G) (BG H) (BG (concr (abstr H)))
                 (hom_B G H f) (hom_B H (concr (abstr H)) (q_hom H)) ω) ∎))

def q_natural (G H : Group) (f : GroupHom G H)
  : Id (GroupHom G (concr (abstr H)))
      (group_hom_compose G (concr (abstr G)) (concr (abstr H)) (q_hom G) (concr_hom (abstr G) (abstr H) (abstr_hom G H f)))
      (group_hom_compose G H (concr (abstr H)) f (q_hom H))
  ≔ q_natural_generic G H f (concr_hom (abstr G) (abstr H) (abstr_hom G H f))
      (ω ↦ concr_hom_usym_natural (abstr G) (abstr H) (abstr_hom G H f) ω)

def q_natural_iso
  : NatIso GroupWild GroupWild (functor_identity GroupWild)
      (functor_compose GroupWild AbstractGroupWild GroupWild concr_functor abstr_functor)
  ≔ ((component ≔ q_hom, natural ≔ G H f ↦ q_natural G H f),
     G ↦ group_iso_cat_iso_equiv G (concr (abstr G)) .map (q_iso G) .snd)

{` The inverse of a natural isomorphism, generically (instantiating
   nat_iso_inverse directly at q made the check take many minutes). `}
def nat_iso_full_inverse (C D : WildPrecat) (F G : WildFunctor C D) (alpha : NatIso C D F G) : NatIso C D G F
  ≔ (nat_iso_inverse C D F G (alpha .fst) (alpha .snd),
     a ↦ cat_iso_inverse D (F .obj a) (G .obj a) (alpha .fst .component a, alpha .snd a) .snd)

def q_inverse_natural_iso
  : NatIso GroupWild GroupWild (functor_compose GroupWild AbstractGroupWild GroupWild concr_functor abstr_functor)
      (functor_identity GroupWild)
  ≔ nat_iso_full_inverse GroupWild GroupWild (functor_identity GroupWild)
      (functor_compose GroupWild AbstractGroupWild GroupWild concr_functor abstr_functor) q_natural_iso

{` thm:concr-equiv-cats: concr is an equivalence of categories (with
   right adjoint abstr), and so is abstr. `}
def concr_is_cat_equivalence : IsCatEquivalence AbstractGroupWild GroupWild concr_functor
  ≔ cat_equivalence_from_nat_isos AbstractGroupWild GroupWild concr_functor abstr_functor r_natural_iso q_inverse_natural_iso

def concr_cat_equivalence : CatEquivalence AbstractGroupWild GroupWild ≔ (concr_functor, concr_is_cat_equivalence)

def abstr_is_cat_equivalence : IsCatEquivalence GroupWild AbstractGroupWild abstr_functor
  ≔ cat_equivalence_from_nat_isos GroupWild AbstractGroupWild abstr_functor concr_functor q_natural_iso r_inverse_natural_iso

def abstr_cat_equivalence : CatEquivalence GroupWild AbstractGroupWild ≔ (abstr_functor, abstr_is_cat_equivalence)

{` Text after thm:concr-equiv-cats: lem:cat-equiv-ff applied to the
   equivalence gives again that abstr is fully faithful
   (lem:homomabstrconcr); in this formalization the theorem itself uses
   lem:homomabstrconcr, so this is a consistency check, not an independent
   proof. `}
def abstr_functor_fully_faithful : IsFullyFaithful GroupWild AbstractGroupWild abstr_functor
  ≔ cat_equivalence_ff (category_precat GroupCat) AbstractGroupPrecat abstr_functor abstr_is_cat_equivalence
