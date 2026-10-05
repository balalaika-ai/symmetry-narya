{` Blind statements for chapter 9 (subgroups.tex), section "The action on the set of subgroups". `}
export "01-epi-mono"
export "../../../src/437-conjugation-inner-automorphisms"
export "../../../src/750-abstract-concrete-gsets"
export "../../../src/723-abstract-conjugation"
export "../../../src/475-standard-bicycle-normality"
export "../../../src/70-classical-principles"

{` Definition (subgroups.tex:1200). The G-set Mono(G) : BG → Set, z ↦ Mono(mkgroup(BG÷, z)). `}
def BlindMonoGSet (G : Group) : GSet G
  ≔ z ↦ (GroupMonos (group_at G z), group_monos_set (group_at G z))

{` Text after the definition: the underlying set Mono(G)(sh_G) is (definitionally) Mono(G). `}
def blind_mono_gset_underlying : Type
  ≔ (G : Group) → Id Type (gset_underlying G (BlindMonoGSet G)) (GroupMonos G)

{` rem:action-Mono(G). For p : z = z', the homomorphism mkgroup(id_BG, p⁻¹) : Hom(mkgroup(BG÷,z), mkgroup(BG÷,z')). `}
def blind_shape_move (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') : GroupHom (group_at G z) (group_at G z')
  ≔ mkhom (group_at G z) (group_at G z') ((x ↦ x), inverse (BG G .carrier) z z' p)

{` rem:action-Mono(G). Mono(G)(p) maps (H, f) to (H, mkgroup(id_BG, p⁻¹) f) (conjugation). `}
def blind_action_mono : Type
  ≔ (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (x : GroupMonos (group_at G z))
    → Id (Σ Group (H ↦ GroupHom H (group_at G z')))
        (gset_act G (BlindMonoGSet G) z z' p x .fst, gset_act G (BlindMonoGSet G) z z' p x .snd .fst)
        (x .fst, group_hom_compose (x .fst) (group_at G z) (group_at G z') (x .snd .fst) (blind_shape_move G z z' p))

{` The abstract G-set of lem:conj-abstract: Σ_{H:absGroup} Σ_{φ:absHom(H, abstr(G))} ismono(φ), with ismono(φ) taken
   as injectivity of the underlying function. `}
def BlindAbsMonos (G : Group) : Type
  ≔ Σ AbstractGroup (H ↦ Σ (AbstractHom H (abstr G)) (φ ↦ IsEmbedding (H .carrier) (USym G) (φ .fst)))

def BlindAbsMonoData (G : Group) : Type ≔ Σ AbstractGroup (H ↦ AbstractHom H (abstr G))

def blind_abs_mono_data (G : Group) (x : BlindAbsMonos G) : BlindAbsMonoData G ≔ (x .fst, x .snd .fst)

{` g · (H, φ) ≔ (H, conj^g φ), conj^g(s) = g s g⁻¹ (ex:conjhom). `}
def blind_abs_conj_act (G : Group) (g : USym G) (d : BlindAbsMonoData G) : BlindAbsMonoData G
  ≔ (d .fst, abstract_hom_compose (d .fst) (abstr G) (abstr G) (d .snd) (abstract_conj_hom (abstr G) g))

{` lem:conj-abstract. Under GSet(G) ≃ abstr(G)-Set, Mono(G) corresponds to the abstract monomorphisms into abstr(G)
   with the action g · (H, φ) = (H, conj^g φ): an equivariant bijection Mono(G)(sh_G) ≃ abstract monos
   (equivariance stated on (H, φ); the mono component is a proposition). `}
def blind_conj_abstract : Type
  ≔ (G : Group)
    → Σ (Equiv (gset_underlying G (BlindMonoGSet G)) (BlindAbsMonos G)) (e ↦
        (g : USym G) (x : gset_underlying G (BlindMonoGSet G))
        → Id (BlindAbsMonoData G)
            (blind_abs_mono_data G (e .map (gset_usym_act G (BlindMonoGSet G) g x)))
            (blind_abs_conj_act G g (blind_abs_mono_data G (e .map x))))

{` A G-set is trivial if its action is the identity. `}
def BlindActsTrivially (G : Group) (X : GSet G) : Type
  ≔ (g : USym G) (x : gset_underlying G X) → Id (gset_underlying G X) (gset_usym_act G X g x) x

{` rem:typeofsubgpstrivifab. G abelian ⇔ conj^g = id for all g. `}
def blind_abelian_iff_conj_trivial : Type
  ≔ (G : Group)
    → BlindIff (IsAbelian G)
        ((g : USym G) → Id (AbstractHom (abstr G) (abstr G)) (abstract_conj_hom (abstr G) g) (abstract_hom_id (abstr G)))

{` rem:typeofsubgpstrivifab, literal: the abstract G-set of lem:conj-abstract, hence Mono(G), is trivial iff G is
   abelian. NOTE: only "abelian ⇒ trivial" holds; a non-abelian group all of whose subgroups are normal
   (the quaternion group Q8) acts trivially. See the corrected variants below. `}
def blind_abs_monos_trivial_iff_abelian : Type
  ≔ (G : Group)
    → BlindIff ((g : USym G) (x : BlindAbsMonos G)
                 → Id (BlindAbsMonoData G) (blind_abs_conj_act G g (blind_abs_mono_data G x)) (blind_abs_mono_data G x))
        (IsAbelian G)

def blind_mono_gset_trivial_iff_abelian : Type
  ≔ (G : Group) → BlindIff (BlindActsTrivially G (BlindMonoGSet G)) (IsAbelian G)

{` Corrected: abelian ⇒ the G-set Mono(G) is trivial; and Q8 is a counterexample to the converse. `}
def blind_mono_gset_trivial_iff_abelian_corrected : Type
  ≔ (G : Group) → IsAbelian G → BlindActsTrivially G (BlindMonoGSet G)

def blind_mono_gset_trivial_counterexample : Type
  ≔ Product (BlindActsTrivially quaternion_group (BlindMonoGSet quaternion_group)) (Not (IsAbelian quaternion_group))

{` Definition (subgroups.tex:1282). The G-set Sub(G) : BG → Set, z ↦ Sub(mkgroup(BG÷, z))
   (printed with "-" in place of z). `}
def BlindSubGSet (G : Group) : GSet G
  ≔ z ↦ (Subgroups (group_at G z), subgroups_set (group_at G z))

{` Text after the definition: Sub(G)(sh_G) ≡ Sub(G), and the action does nothing with X and acts on the point. `}
def blind_sub_gset_underlying : Type
  ≔ (G : Group) → Id Type (gset_underlying G (BlindSubGSet G)) (Subgroups G)

def blind_sub_gset_action : Type
  ≔ (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z') (S : Subgroups (group_at G z))
    → Id (Σ (GSet G) (X ↦ X z' .fst))
        (gset_act G (BlindSubGSet G) z z' p S .gset, gset_act G (BlindSubGSet G) z z' p S .point)
        (S .gset, gset_act G (S .gset) z z' p (S .point))

{` Definition (subgroups.tex:1295). E : Hom_G(Mono(G), Sub(G)), E_z(H, f) ≔ (Bf^{-1}, (sh_H, Bf_pt)). `}
def blind_E (G : Group) : GSetHom G (BlindMonoGSet G) (BlindSubGSet G) ≔ z ↦ mono_to_subgroup (group_at G z)

{` E is an equivalence of G-sets, and E_{sh_G} ≡ E. `}
def blind_E_equiv : Type
  ≔ (G : Group) (z : BG G .carrier)
    → BookIsEquiv (BlindMonoGSet G z .fst) (BlindSubGSet G z .fst) (blind_E G z)

def blind_E_at_shape : Type
  ≔ (G : Group) → Id (GroupMonos G → Subgroups G) (blind_E G (shape G)) (mono_to_subgroup G)

{` xca:Sub(Sigma3) (1). Sub(G) is a transitive G-set iff G is trivial. `}
def blind_sub_transitive_iff_trivial : Type
  ≔ (G : Group) → BlindIff (IsTransitive G (BlindSubGSet G)) (IsTrivialGroup G)

def blind_nat_four : Nat ≔ suc. (suc. (suc. (suc. zero.)))

{` xca:Sub(Sigma3) (2). The orbits of Sub(Σ3): {1}, A3, Σ3 and one orbit of the three subgroups of order 2. `}
def blind_sub_sigma3_orbits : Type
  ≔ Equiv (Orbits (symmetric_group three) (BlindSubGSet (symmetric_group three))) (Fin blind_nat_four)

{` Constructively Sub(Σ3) contains subgroups given by undecided propositions, so the count needs excluded middle. `}
def blind_sub_sigma3_orbits_corrected : Type
  ≔ ExcludedMiddle → Equiv (Orbits (symmetric_group three) (BlindSubGSet (symmetric_group three))) (Fin blind_nat_four)
