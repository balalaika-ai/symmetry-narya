export "907-normal-epis"
export "916-conjugation-abstract"

{` Chapter 9 (subgroups.tex), lem:characterizations of normal, item (5):
   the fixed points of the abstr(G)-set of abstract monomorphisms of
   lem:conj-abstract (module 916) form a set equivalent to Nor(G). Items
   (1)-(4) are characterizations_of_normal (module 907). The fixed points
   of an abstract G-set X are the x with s ·_X x = x for all s. `}

def AgsetFixedPoints (AG : AbstractGroup) (X : AbstractGSet AG) : Type
  ≔ Σ (agset_carrier AG X) (x ↦ (s : AG .carrier) → Id (agset_carrier AG X) (agset_act AG X s x) x)

def agset_fixed_points_prop (AG : AbstractGroup) (X : AbstractGSet AG) (x : agset_carrier AG X)
  : isProp ((s : AG .carrier) → Id (agset_carrier AG X) (agset_act AG X s x) x)
  ≔ pi_prop (AG .carrier) (s ↦ Id (agset_carrier AG X) (agset_act AG X s x) x)
      (s ↦ X .fst .snd (agset_act AG X s x) x)

{` Fixed points of ev_{sh_G}(X) are the fixed points of X(sh_G). `}
def ev_gset_fixed_points_equiv (G : Group) (X : GSet G)
  : Equiv (AgsetFixedPoints (abstr G) (ev_gset G X)) (GSetFixedPoints G X)
  ≔ let A ≔ gset_underlying G X in
    family_equiv A (x ↦ (s : USym G) → Id A (agset_act (abstr G) (ev_gset G X) s x) x)
      (x ↦ (g : USym G) → Id A (gset_usym_act G X g x) x)
      (x ↦ iff_equiv ((s : USym G) → Id A (agset_act (abstr G) (ev_gset G X) s x) x)
             ((g : USym G) → Id A (gset_usym_act G X g x) x)
             (agset_fixed_points_prop (abstr G) (ev_gset G X) x) (gset_fixed_points_prop G X x)
             (h g ↦ concat A (gset_usym_act G X g x) (agset_act (abstr G) (ev_gset G X) g x) x
                (inverse A (agset_act (abstr G) (ev_gset G X) g x) (gset_usym_act G X g x) (ev_gset_act G X g x)) (h g))
             (h g ↦ concat A (agset_act (abstr G) (ev_gset G X) g x) (gset_usym_act G X g x) x (ev_gset_act G X g x) (h g)))

def abstract_monos_fixed_points_equiv (G : Group)
  : Equiv (AgsetFixedPoints (abstr G) (conj_abstract_agset G)) (NormalSubgroups G)
  ≔ let AG ≔ abstr G in
    let F1 ≔ AgsetFixedPoints AG (conj_abstract_agset G) in
    let F2 ≔ AgsetFixedPoints AG (ev_gset G (monos_gset G)) in
    compose_equiv F1 F2 (NormalSubgroups G)
      (id_to_equiv F1 F2
        (map_path (AbstractGSet AG) Type (AgsetFixedPoints AG) (conj_abstract_agset G) (ev_gset G (monos_gset G))
          (inverse (AbstractGSet AG) (ev_gset G (monos_gset G)) (conj_abstract_agset G) (conj_abstract_path G))))
      (compose_equiv F2 (GSetFixedPoints G (monos_gset G)) (NormalSubgroups G)
        (ev_gset_fixed_points_equiv G (monos_gset G))
        (compose_equiv (GSetFixedPoints G (monos_gset G)) (InvariantMaps G (monos_gset G)) (NormalSubgroups G)
          (canonical_inverse_equiv (InvariantMaps G (monos_gset G)) (GSetFixedPoints G (monos_gset G))
            (invariant_maps_fixed_equiv G (monos_gset G)))
          (monos_fixed_points_equiv G)))
