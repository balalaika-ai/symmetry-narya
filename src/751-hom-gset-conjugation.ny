export "750-abstract-concrete-gsets"
export "564-adjoint-principal-gsets"
export "730-inner-conjugation-abstr"

{` Chapter 7 (absgroup.tex), sec:Gsetsabstrconcr, ex:abstrandconj and
   lem:abstrandconj: the G-set Hom(H, G) (ex:HomHGasGset, group_hom_gset of
   module 564; Hom(H, G)(z) ≡ Hom(H, mkgroup(BG÷, z))) is sent by
   ev_{sh_G} to the abstr(G)-set absHom(abstr H, abstr G) on which g acts
   by postcomposition with conj^g (abstract_conj_hom of module 723).

   - Transport along p : sh_G = z in the family Hom(H, G)(z) is
     postcomposition with the isomorphism (id_BG, p⁻¹) : G → mkgroup(BG÷, z)
     (conj_hom of module 437; hom_gset_conj_transport, by path induction).
   - Hence the action a_X(g) of ev_{sh_G}(Hom(H, G)) is postcomposition with
     (id_BG, g⁻¹) (hom_gset_ev_act).
   - abstr(id_BG, g⁻¹) = conj^g (exa:conj-concrete; abstr_conj_hom_is_abstract_conj,
     module 730).
   - lem:abstrandconj: ev_{sh_G}(Hom(H, G)) = (absHom(abstr H, abstr G),
     g ↦ conj^g ∘ -) as abstr(G)-sets, the identification being given by the
     equivalence abstr : Hom(H, G) ≃ absHom(abstr H, abstr G) of
     lem:homomabstrconcr (hom_gset_conj_path). `}

{` At p ≡ refl: f followed by (id_BG, refl⁻¹) is f. `}
def hom_gset_conj_transport_refl (H G : Group) (f : GroupHom H G)
  : Id (GroupHom H G) (group_hom_compose H G G f (conj_hom G (shape G) (refl (shape G)))) f
  ≔ let B ≔ BG G .carrier in
    refl ((q ↦ mkhom H G (hom_function H G f, q)) : Id B (shape G) (hom_function H G f (shape H)) → GroupHom H G)
      (inverse_refl_concat B (shape G) (hom_function H G f (shape H)) (hom_point H G f))

{` ex:abstrandconj: transport along p : sh_G = z in Hom(H, G)(z) is
   postcomposition with (id_BG, p⁻¹). `}
def hom_gset_conj_transport (H G : Group) (z : BG G .carrier) (p : Id (BG G .carrier) (shape G) z) (f : GroupHom H G)
  : Id (GroupHom H (group_at G z)) (gset_act G (group_hom_gset H G) (shape G) z p f)
      (group_hom_compose H G (group_at G z) f (conj_hom G z p))
  ≔ J (BG G .carrier) (shape G)
      (z p ↦ Id (GroupHom H (group_at G z)) (gset_act G (group_hom_gset H G) (shape G) z p f)
        (group_hom_compose H G (group_at G z) f (conj_hom G z p)))
      (concat (GroupHom H G) (gset_act G (group_hom_gset H G) (shape G) (shape G) (refl (shape G)) f) f
        (group_hom_compose H G G f (conj_hom G (shape G) (refl (shape G))))
        (gset_act_refl G (group_hom_gset H G) (shape G) f)
        (inverse (GroupHom H G) (group_hom_compose H G G f (conj_hom G (shape G) (refl (shape G)))) f
          (hom_gset_conj_transport_refl H G f)))
      z p

{` The underlying set of ev_{sh_G}(Hom(H, G)) is Hom(H, G). `}
def hom_gset_ev_underlying (H G : Group)
  : Id Type (agset_carrier (abstr G) (ev_gset G (group_hom_gset H G))) (GroupHom H G)
  ≔ refl (GroupHom H G)

{` ex:abstrandconj, first question: g acts on Hom(H, G) by postcomposition
   with (id_BG, g⁻¹) (this action is the abstract homomorphism
   ev_gset_action G (group_hom_gset H G) : USym G → abstr(Σ_{Hom(H,G)})). `}
def hom_gset_ev_act (H G : Group) (g : USym G) (f : GroupHom H G)
  : Id (GroupHom H G) (agset_act (abstr G) (ev_gset G (group_hom_gset H G)) g f)
      (group_hom_compose H G G f (conj_hom G (shape G) g))
  ≔ concat (GroupHom H G) (agset_act (abstr G) (ev_gset G (group_hom_gset H G)) g f)
      (gset_usym_act G (group_hom_gset H G) g f) (group_hom_compose H G G f (conj_hom G (shape G) g))
      (ev_gset_act G (group_hom_gset H G) g f)
      (hom_gset_conj_transport H G (shape G) g f)

{` conj^{g·h} = conj^g ∘ conj^h and conj^e = id, pointwise. `}
def hom_gset_conj_mul_law (G : AbstractGroup) (g h x : G .carrier)
  : Id (G .carrier) (abstract_conj G (G .mul g h) x) (abstract_conj G g (abstract_conj G h x))
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in
    let ig ≔ G .inv g in let ih ≔ G .inv h in
    calc
      m (m (m g h) x) (G .inv (m g h)) = m (m (m g h) x) (m ih ig)
        by refl (m (m (m g h) x)) (ag_inv_mul G g h)
      = m (m (m (m g h) x) ih) ig by L .assoc (m (m g h) x) ih ig
      = m (m (m g (m h x)) ih) ig
        by refl ((y ↦ m (m y ih) ig) : S → S) (inverse S (m g (m h x)) (m (m g h) x) (L .assoc g h x))
      = m (m g (m (m h x) ih)) ig
        by refl ((y ↦ m y ig) : S → S) (inverse S (m g (m (m h x) ih)) (m (m g (m h x)) ih) (L .assoc g (m h x) ih)) ∎

def hom_gset_conj_unit_law (G : AbstractGroup) (x : G .carrier)
  : Id (G .carrier) (abstract_conj G (G .unit) x) x
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in
    calc
      m (m (G .unit) x) (G .inv (G .unit)) = m (m (G .unit) x) (G .unit) by refl (m (m (G .unit) x)) (ag_inv_unit G)
      = m (G .unit) x by L .unit_right (m (G .unit) x)
      = x by L .unit_left x ∎

{` The action g · φ ≔ conj^g ∘ φ on absHom(H, G), for abstract groups. `}
def hom_gset_conj_act (H G : AbstractGroup) (g : G .carrier) (φ : AbstractHom H G) : AbstractHom H G
  ≔ abstract_hom_compose H G G φ (abstract_conj_hom G g)

def hom_gset_conj_act_mul (H G : AbstractGroup) (g h : G .carrier) (φ : AbstractHom H G)
  : Id (AbstractHom H G) (hom_gset_conj_act H G (G .mul g h) φ) (hom_gset_conj_act H G g (hom_gset_conj_act H G h φ))
  ≔ abstract_hom_ext H G (hom_gset_conj_act H G (G .mul g h) φ) (hom_gset_conj_act H G g (hom_gset_conj_act H G h φ))
      (s ↦ hom_gset_conj_mul_law G g h (φ .fst s))

def hom_gset_conj_act_unit (H G : AbstractGroup) (φ : AbstractHom H G)
  : Id (AbstractHom H G) (hom_gset_conj_act H G (G .unit) φ) φ
  ≔ abstract_hom_ext H G (hom_gset_conj_act H G (G .unit) φ) φ (s ↦ hom_gset_conj_unit_law G (φ .fst s))

{` The G-set (absHom(H, G), g ↦ conj^g ∘ -) for abstract groups H and G. `}
def hom_gset_conj_agset (H G : AbstractGroup) : AbstractGSet G
  ≔ agset_from_action G (AbstractHom H G, abstract_hom_set H G) (hom_gset_conj_act H G)
      (hom_gset_conj_act_mul H G) (hom_gset_conj_act_unit H G)

def hom_gset_conj_agset_act (H G : AbstractGroup) (g : G .carrier) (φ : AbstractHom H G)
  : Id (AbstractHom H G) (agset_act G (hom_gset_conj_agset H G) g φ) (abstract_hom_compose H G G φ (abstract_conj_hom G g))
  ≔ refl (abstract_hom_compose H G G φ (abstract_conj_hom G g))

{` ex:abstrandconj, second question: abstr intertwines the two actions,
   abstr((id_BG, g⁻¹) ∘ f) = conj^g ∘ abstr(f). `}
def hom_gset_abstr_equivariant (H G : Group) (g : USym G) (f : GroupHom H G)
  : Id (AbstractHom (abstr H) (abstr G))
      (abstr_hom H G (agset_act (abstr G) (ev_gset G (group_hom_gset H G)) g f))
      (agset_act (abstr G) (hom_gset_conj_agset (abstr H) (abstr G)) g (abstr_hom H G f))
  ≔ let AH ≔ abstr H in let AG ≔ abstr G in
    let cg ≔ conj_hom G (shape G) g in
    calc
      abstr_hom H G (agset_act AG (ev_gset G (group_hom_gset H G)) g f)
      = abstr_hom H G (group_hom_compose H G G f cg)
        by refl (abstr_hom H G) (hom_gset_ev_act H G g f)
      = abstract_hom_compose AH AG AG (abstr_hom H G f) (abstr_hom G G cg)
        by abstr_hom_compose H G G f cg
      = abstract_hom_compose AH AG AG (abstr_hom H G f) (abstract_conj_hom AG g)
        by refl (abstract_hom_compose AH AG AG (abstr_hom H G f)) (abstr_conj_hom_is_abstract_conj G g) ∎

{` lem:abstrandconj: ev_{sh_G}(Hom(H, G)) ≅ (absHom(abstr H, abstr G), conj^g ∘ -),
   with underlying equivalence abstr of lem:homomabstrconcr. `}
def hom_gset_conj_iso (H G : Group)
  : AbstractGSetIso (abstr G) (ev_gset G (group_hom_gset H G)) (hom_gset_conj_agset (abstr H) (abstr G))
  ≔ (abstr_hom_equiv H G, g f ↦ hom_gset_abstr_equivariant H G g f)

def hom_gset_conj_path (H G : Group)
  : Id (AbstractGSet (abstr G)) (gset_abstract_gset_equiv G .map (group_hom_gset H G)) (hom_gset_conj_agset (abstr H) (abstr G))
  ≔ agset_path_from_iso (abstr G) (ev_gset G (group_hom_gset H G)) (hom_gset_conj_agset (abstr H) (abstr G))
      (hom_gset_conj_iso H G)

{` Litmus (Σ_3): conj^τ ∘ id ≠ id in absHom(abstr Σ_3, abstr Σ_3), so the
   action of τ on the abstract G-set is not trivial. `}
def hom_gset_conj_sigma3_moves_id
  (p : Id (AbstractHom (abstr (symmetric_group three)) (abstr (symmetric_group three)))
    (agset_act (abstr (symmetric_group three)) (hom_gset_conj_agset (abstr (symmetric_group three)) (abstr (symmetric_group three)))
      sigma3_tau (abstract_hom_id (abstr (symmetric_group three))))
    (abstract_hom_id (abstr (symmetric_group three))))
  : Empty
  ≔ let A ≔ abstr (symmetric_group three) in
    abstract_conj_sigma3_moves (refl ((φ ↦ φ .fst sigma3_sigma) : AbstractHom A A → USym (symmetric_group three)) p)
