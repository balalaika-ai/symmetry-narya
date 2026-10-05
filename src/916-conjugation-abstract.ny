export "902-subgroup-gsets"
export "751-hom-gset-conjugation"
export "709-groups-are-abstract-groups"
export "289-book-equivalence-maps-two"

{` Chapter 9 (subgroups.tex), lem:conj-abstract and xca:conj-abstract, and
   rem:typeofsubgpstrivifab. Under lem:actionsconcr2abstr (ev_gset, module
   750) the G-set Mono(G) corresponds to the abstr(G)-set of abstract
   monomorphisms Σ_{H : AbsGroup} Σ_{φ : absHom(H, abstr G)} ismono(φ) with
   g · (H, φ) ≔ (H, conj^g ∘ φ). An abstract monomorphism is a homomorphism
   whose underlying function is an injection. `}

def AbstractMonosInto (AG : AbstractGroup) : Type
  ≔ Σ AbstractGroup (Hh ↦ Σ (AbstractHom Hh AG) (φ ↦ IsEmbedding (Hh .carrier) (AG .carrier) (φ .fst)))

def concrete_to_abstract_mono (G : Group) (m : GroupMonos G) : AbstractMonosInto (abstr G)
  ≔ (abstr (m .fst), (abstr_hom (m .fst) G (m .snd .fst), m .snd .snd))

def conj_abstract_family (AG : AbstractGroup) (Hh : AbstractGroup) : Type
  ≔ Σ (AbstractHom Hh AG) (φ ↦ IsEmbedding (Hh .carrier) (AG .carrier) (φ .fst))

def concrete_abstract_monos_equiv (G : Group) : Equiv (GroupMonos G) (AbstractMonosInto (abstr G))
  ≔ let AG ≔ abstr G in
    let B ≔ conj_abstract_family AG in
    let inner : (H : Group) → Equiv (Σ (GroupHom H G) (f ↦ IsGroupMono H G f)) (B (abstr H))
      ≔ H ↦ sigma_pullback_equiv (GroupHom H G) (AbstractHom (abstr H) AG) (abstr_hom_equiv H G)
             (φ ↦ IsEmbedding (USym H) (USym G) (φ .fst)) in
    let outer ≔ sigma_pullback_equiv Group AbstractGroup group_abstract_group_equiv B in
    let e ≔ compose_equiv (GroupMonos G) (Σ Group (H ↦ B (abstr H))) (AbstractMonosInto AG)
      (family_equiv Group (H ↦ Σ (GroupHom H G) (f ↦ IsGroupMono H G f)) (H ↦ B (abstr H)) inner) outer in
    equiv_change_map (GroupMonos G) (AbstractMonosInto AG) e (concrete_to_abstract_mono G)
      (m ↦ concat (AbstractMonosInto AG) (e .map m) (outer .map (m .fst, (abstr_hom (m .fst) G (m .snd .fst), m .snd .snd)))
        (concrete_to_abstract_mono G m)
        (refl ((w ↦ outer .map (m .fst, w)) : B (abstr (m .fst)) → AbstractMonosInto AG)
          (sigma_pullback_equiv_map (GroupHom (m .fst) G) (AbstractHom (abstr (m .fst)) AG) (abstr_hom_equiv (m .fst) G)
            (φ ↦ IsEmbedding (USym (m .fst)) (USym G) (φ .fst)) (m .snd)))
        (sigma_pullback_equiv_map Group AbstractGroup group_abstract_group_equiv B
          (m .fst, (abstr_hom (m .fst) G (m .snd .fst), m .snd .snd))))

def abstract_monos_set (G : Group) : isSet (AbstractMonosInto (abstr G))
  ≔ hlevel_two_to_set (AbstractMonosInto (abstr G))
      (hlevel_equiv (suc. (suc. zero.)) (GroupMonos G) (AbstractMonosInto (abstr G)) (concrete_abstract_monos_equiv G)
        (set_to_hlevel_two (GroupMonos G) (group_monos_set G)))

{` The action g · (H, φ) ≔ (H, conj^g ∘ φ); conj^g is a bijection, so the
   composite is again injective. `}
def amono_embedding_reflects (A B : Type) (f : A → B) (h : IsEmbedding A B f) (x y : A) (e : Id B (f x) (f y)) : Id A x y
  ≔ refl ((t ↦ t .fst) : BookFiber A B f (f y) → A) (h (f y) (x, inverse B (f x) (f y) e) (y, refl (f y)))

def amono_conj_embedding (AG Hh : AbstractGroup) (g : AG .carrier) (u : conj_abstract_family AG Hh)
  : IsEmbedding (Hh .carrier) (AG .carrier) (hom_gset_conj_act Hh AG g (u .fst) .fst)
  ≔ path_reflecting_set_embedding (Hh .carrier) (AG .carrier) (abstract_group_set AG) (hom_gset_conj_act Hh AG g (u .fst) .fst)
      (x y e ↦ amono_embedding_reflects (Hh .carrier) (AG .carrier) (u .fst .fst) (u .snd) x y
        (equivalence_injective (AG .carrier) (AG .carrier) (abstract_conj_equiv AG g) (u .fst .fst x) (u .fst .fst y) e))

def amono_conj_act (AG : AbstractGroup) (g : AG .carrier) (u : AbstractMonosInto AG) : AbstractMonosInto AG
  ≔ (u .fst, (hom_gset_conj_act (u .fst) AG g (u .snd .fst), amono_conj_embedding AG (u .fst) g (u .snd)))

def amono_family_path (AG Hh : AbstractGroup) (u v : conj_abstract_family AG Hh) (p : Id (AbstractHom Hh AG) (u .fst) (v .fst))
  : Id (AbstractMonosInto AG) (Hh, u) (Hh, v)
  ≔ map_path (conj_abstract_family AG Hh) (AbstractMonosInto AG) (w ↦ (Hh, w)) u v
      (subtype_equal (AbstractHom Hh AG) (φ ↦ IsEmbedding (Hh .carrier) (AG .carrier) (φ .fst))
        (φ ↦ embedding_prop (Hh .carrier) (AG .carrier) (φ .fst)) u v p)

def conj_abstract_agset (G : Group) : AbstractGSet (abstr G)
  ≔ let AG ≔ abstr G in
    agset_from_action AG (AbstractMonosInto AG, abstract_monos_set G) (amono_conj_act AG)
      (g h u ↦ amono_family_path AG (u .fst) (amono_conj_act AG (AG .mul g h) u .snd)
        (amono_conj_act AG g (amono_conj_act AG h u) .snd)
        (hom_gset_conj_act_mul (u .fst) AG g h (u .snd .fst)))
      (u ↦ amono_family_path AG (u .fst) (amono_conj_act AG (AG .unit) u .snd) (u .snd)
        (hom_gset_conj_act_unit (u .fst) AG (u .snd .fst)))

{` lem:conj-abstract (and xca:conj-abstract): the identification. `}
def conj_abstract_equivariant (G : Group) (g : USym G) (m : GroupMonos G)
  : Id (AbstractMonosInto (abstr G))
      (concrete_to_abstract_mono G (agset_act (abstr G) (ev_gset G (monos_gset G)) g m))
      (agset_act (abstr G) (conj_abstract_agset G) g (concrete_to_abstract_mono G m))
  ≔ let AG ≔ abstr G in
    let H ≔ m .fst in
    let cg ≔ conj_hom G (shape G) g in
    let A ≔ AbstractMonosInto AG in
    calc
      concrete_to_abstract_mono G (agset_act AG (ev_gset G (monos_gset G)) g m)
      = concrete_to_abstract_mono G (monos_conjugate G (shape G) (shape G) g m)
        by refl (concrete_to_abstract_mono G)
             (concat (GroupMonos G) (agset_act AG (ev_gset G (monos_gset G)) g m) (gset_usym_act G (monos_gset G) g m)
               (monos_conjugate G (shape G) (shape G) g m)
               (ev_gset_act G (monos_gset G) g m) (monos_gset_usym_act G g m))
      = amono_conj_act AG g (concrete_to_abstract_mono G m)
        by amono_family_path AG (abstr H) (concrete_to_abstract_mono G (monos_conjugate G (shape G) (shape G) g m) .snd)
             (amono_conj_act AG g (concrete_to_abstract_mono G m) .snd)
             (calc
                abstr_hom H G (group_hom_compose H G G (m .snd .fst) cg)
                = abstract_hom_compose (abstr H) AG AG (abstr_hom H G (m .snd .fst)) (abstr_hom G G cg)
                  by abstr_hom_compose H G G (m .snd .fst) cg
                = abstract_hom_compose (abstr H) AG AG (abstr_hom H G (m .snd .fst)) (abstract_conj_hom AG g)
                  by refl (abstract_hom_compose (abstr H) AG AG (abstr_hom H G (m .snd .fst))) (abstr_conj_hom_is_abstract_conj G g) ∎)
      = agset_act AG (conj_abstract_agset G) g (concrete_to_abstract_mono G m)
        by inverse A (agset_act AG (conj_abstract_agset G) g (concrete_to_abstract_mono G m))
             (amono_conj_act AG g (concrete_to_abstract_mono G m))
             (agset_from_action_act AG (A, abstract_monos_set G) (amono_conj_act AG)
               (g h u ↦ amono_family_path AG (u .fst) (amono_conj_act AG (AG .mul g h) u .snd)
                 (amono_conj_act AG g (amono_conj_act AG h u) .snd)
                 (hom_gset_conj_act_mul (u .fst) AG g h (u .snd .fst)))
               (u ↦ amono_family_path AG (u .fst) (amono_conj_act AG (AG .unit) u .snd) (u .snd)
                 (hom_gset_conj_act_unit (u .fst) AG (u .snd .fst)))
               g (concrete_to_abstract_mono G m)) ∎

def conj_abstract_iso (G : Group) : AbstractGSetIso (abstr G) (ev_gset G (monos_gset G)) (conj_abstract_agset G)
  ≔ (concrete_abstract_monos_equiv G, g m ↦ conj_abstract_equivariant G g m)

def conj_abstract_path (G : Group)
  : Id (AbstractGSet (abstr G)) (gset_abstract_gset_equiv G .map (monos_gset G)) (conj_abstract_agset G)
  ≔ agset_path_from_iso (abstr G) (ev_gset G (monos_gset G)) (conj_abstract_agset G) (conj_abstract_iso G)
