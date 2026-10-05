export "bridge-06-normal"
export "../../../src/917-normal-characterizations"

{` Bridges bridge for lem:characterizations of normal (subgroups.tex 1539), item 4: the fixed points of the G-set
   Mono(G) and the blind fixed abstract monomorphisms (fixed on the data (H, φ)). `}

def bridge9_amono_reassoc (G : Group) (u : AbstractMonosInto (abstr G))
  : Σ (BlindAbsMonoData G) (d ↦ IsEmbedding (d .fst .carrier) (USym G) (d .snd .fst))
  ≔ ((u .fst, u .snd .fst), u .snd .snd)

def bridge9_amono_unreassoc (G : Group) (t : Σ (BlindAbsMonoData G) (d ↦ IsEmbedding (d .fst .carrier) (USym G) (d .snd .fst)))
  : AbstractMonosInto (abstr G)
  ≔ (t .fst .fst, (t .fst .snd, t .snd))

{` Paths of abstract monomorphisms are paths of their data (the mono condition is a proposition). `}
def bridge9_amono_data_path_equiv (G : Group) (u v : AbstractMonosInto (abstr G))
  : Equiv (Id (AbstractMonosInto (abstr G)) u v) (Id (BlindAbsMonoData G) (blind_abs_mono_data G u) (blind_abs_mono_data G v))
  ≔ let AM ≔ AbstractMonosInto (abstr G) in
    let D ≔ BlindAbsMonoData G in
    let Mo ≔ (d ↦ IsEmbedding (d .fst .carrier) (USym G) (d .snd .fst)) : D → Type in
    let hMo ≔ (d ↦ embedding_prop (d .fst .carrier) (USym G) (d .snd .fst)) : (d : D) → isProp (Mo d) in
    let SP ≔ subtype_path_equiv D Mo hMo (bridge9_amono_reassoc G u) (bridge9_amono_reassoc G v) in
    let back ≔ (p ↦ refl (bridge9_amono_unreassoc G)
                   (equiv_inverse_map (Id (Σ D Mo) (bridge9_amono_reassoc G u) (bridge9_amono_reassoc G v))
                     (Id D (blind_abs_mono_data G u) (blind_abs_mono_data G v)) SP p))
      : Id D (blind_abs_mono_data G u) (blind_abs_mono_data G v) → Id AM u v in
    quasi_inverse_equiv (Id AM u v) (Id D (blind_abs_mono_data G u) (blind_abs_mono_data G v))
      (map_path AM D (blind_abs_mono_data G) u v) back
      (q ↦ abstract_monos_set G u v (back (map_path AM D (blind_abs_mono_data G) u v q)) q)
      (p ↦ equiv_counit (Id (Σ D Mo) (bridge9_amono_reassoc G u) (bridge9_amono_reassoc G v))
             (Id D (blind_abs_mono_data G u) (blind_abs_mono_data G v)) SP p)

def bridge9_fixed_abs_monos_equiv (G : Group)
  : Equiv (AgsetFixedPoints (abstr G) (conj_abstract_agset G)) (BlindFixAbsMonos G)
  ≔ let AG ≔ abstr G in
    let AM ≔ AbstractMonosInto AG in
    let D ≔ BlindAbsMonoData G in
    family_equiv AM (x ↦ (s : USym G) → Id AM (amono_conj_act AG s x) x)
      (x ↦ (g : USym G) → Id D (blind_abs_conj_act G g (blind_abs_mono_data G x)) (blind_abs_mono_data G x))
      (x ↦ pi_family_equiv (USym G) (s ↦ Id AM (amono_conj_act AG s x) x)
             (g ↦ Id D (blind_abs_conj_act G g (blind_abs_mono_data G x)) (blind_abs_mono_data G x))
             (g ↦ bridge9_amono_data_path_equiv G (amono_conj_act AG g x) x))

def bridge_characterizations_of_normal : blind_characterizations_of_normal
  ≔ G ↦
    let r ≔ bridge_characterizations_of_normal_123 G in
    let F ≔ AgsetFixedPoints (abstr G) (conj_abstract_agset G) in
    (r .fst, (r .snd .fst, (r .snd .snd,
      compose_equiv (BlindFixMono G) (NormalSubgroups G) (BlindFixAbsMonos G)
        (monos_fixed_points_equiv G)
        (compose_equiv (NormalSubgroups G) F (BlindFixAbsMonos G)
          (canonical_inverse_equiv F (NormalSubgroups G) (abstract_monos_fixed_points_equiv G))
          (bridge9_fixed_abs_monos_equiv G)))))
