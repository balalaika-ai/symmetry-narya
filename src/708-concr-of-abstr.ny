export "707-abstract-torsors"

{` Chapter 7 (absgroup.tex), sec:Gsetforabstract: the notation preinv and
   post, the map r_G of thm:Groupsareidentitytypes (automorphisms of the
   principal torsor are right multiplications), ex:BqG, def:qG-concr-abstr
   and lem:Groupsareidentitytypes (q_G : G → concr(abstr G) is an
   isomorphism). Book juxtaposition of paths is composition order: the
   book's p q (q first) is concat q p. `}

{` preinv(q)(p) ≔ p q⁻¹ and post(p)(q) ≔ p q (text before ex:BqG). `}
def path_preinv (A : Type) (x y z : A) (q : Id A y x) (p : Id A y z) : Id A x z
  ≔ concat A x y z (inverse A y x q) p

def path_post (A : Type) (x y z : A) (p : Id A y z) (q : Id A x y) : Id A x z
  ≔ concat A x y z q p

{` thm:Groupsareidentitytypes, first step: r_G(u) ≔ μ(-, u⁻¹) is an
   automorphism of the principal torsor P_G, and r_G : S ≃ Aut(P_G); the
   codomain is the book's Σ_{π : S ≃ S} Π_{s,t} π(μ(s, t)) = μ(s, π(t)). `}
def abstract_r_map (G : AbstractGroup) (u : G .carrier) : AbstractGSetIso G (agset_principal G) (agset_principal G)
  ≔ (ag_mul_right_equiv G (G .inv u),
     s x ↦ inverse (G .carrier) (G .mul s (G .mul x (G .inv u))) (G .mul (G .mul s x) (G .inv u))
       (G .laws .assoc s x (G .inv u)))

def abstract_r_inverse (G : AbstractGroup) (π : AbstractGSetIso G (agset_principal G) (agset_principal G)) : G .carrier
  ≔ G .inv (π .fst .map (G .unit))

def abstract_r_equiv (G : AbstractGroup) : Equiv (G .carrier) (AbstractGSetIso G (agset_principal G) (agset_principal G))
  ≔ let S ≔ G .carrier in let P ≔ agset_principal G in let m ≔ G .mul in
    quasi_inverse_equiv S (AbstractGSetIso G P P) (abstract_r_map G) (abstract_r_inverse G)
      (u ↦ calc
         G .inv (m (G .unit) (G .inv u)) = G .inv (G .inv u) by refl (G .inv) (G .laws .unit_left (G .inv u))
         = u by ag_inv_inv G u ∎)
      (π ↦ agset_iso_path G P P (abstract_r_map G (abstract_r_inverse G π)) π
        (x ↦ calc
           m x (G .inv (G .inv (π .fst .map (G .unit)))) = m x (π .fst .map (G .unit))
             by refl (m x) (ag_inv_inv G (π .fst .map (G .unit)))
           = π .fst .map (m x (G .unit))
             by inverse S (π .fst .map (m x (G .unit))) (m x (π .fst .map (G .unit))) (π .snd x (G .unit))
           = π .fst .map x by refl (π .fst .map) (G .laws .unit_right x) ∎))

{` r_G(μ(u, v)) = r_G(u) ∘ r_G(v). `}
def abstract_r_mul (G : AbstractGroup) (u v : G .carrier)
  : Id (AbstractGSetIso G (agset_principal G) (agset_principal G)) (abstract_r_map G (G .mul u v))
      (agset_iso_compose G (agset_principal G) (agset_principal G) (agset_principal G) (abstract_r_map G v) (abstract_r_map G u))
  ≔ let m ≔ G .mul in let P ≔ agset_principal G in
    agset_iso_path G P P (abstract_r_map G (m u v)) (agset_iso_compose G P P P (abstract_r_map G v) (abstract_r_map G u))
      (x ↦ calc
         m x (G .inv (m u v)) = m x (m (G .inv v) (G .inv u)) by refl (m x) (ag_inv_mul G u v)
         = m (m x (G .inv v)) (G .inv u) by G .laws .assoc x (G .inv v) (G .inv u) ∎)

{` ex:BqG. For z : BG, the set (z = sh_G) with post_z (left
   multiplication g ↦ (p ↦ g p)) is an abstr(G)-set; for z ≡ sh_G it is
   definitionally the principal abstr(G)-torsor (bq_gset_principal is refl). `}
def bq_gset (G : Group) (z : BG G .carrier) : AbstractGSet (abstr G)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    agset_from_action (abstr G) (Id A z a, bg_groupoid G z a) (g p ↦ concat A z a a p g)
      (g h p ↦ inverse (Id A z a) (concat A z a a (concat A z a a p h) g) (concat A z a a p (concat A a a a h g))
        (concat_assoc A z a a a p h g))
      (p ↦ concat_p1 A z a p)

def bq_gset_act (G : Group) (z : BG G .carrier) (g : USym G) (p : Id (BG G .carrier) z (shape G))
  : Id (Id (BG G .carrier) z (shape G)) (agset_act (abstr G) (bq_gset G z) g p) (path_post (BG G .carrier) z (shape G) (shape G) g p)
  ≔ refl (path_post (BG G .carrier) z (shape G) (shape G) g p)

def bq_gset_principal (G : Group) : Id (AbstractGSet (abstr G)) (bq_gset G (shape G)) (agset_principal (abstr G))
  ≔ refl (agset_principal (abstr G))

def bq_torsor_witness (G : Group) (z : BG G .carrier)
  : Mere (Id (AbstractGSet (abstr G)) (agset_principal (abstr G)) (bq_gset G z))
  ≔ let A ≔ BG G .carrier in let X ≔ AbstractGSet (abstr G) in
    mere_rec (Id A (shape G) z) (Mere (Id X (agset_principal (abstr G)) (bq_gset G z)))
      (mere_isprop (Id X (agset_principal (abstr G)) (bq_gset G z)))
      (p ↦ mere (Id X (agset_principal (abstr G)) (bq_gset G z)) (refl (bq_gset G) p))
      (bg_connected G .snd (shape G) z)

{` ex:BqG. Bq_G : BG →* (Tor_abstr(G), P). The book points it by
   reflexivity; here the torsor witnesses (elements of a proposition) are
   not definitionally equal, so the pointing path has first component refl
   and is completed by the subtype property. `}
def bq_map (G : Group) (z : BG G .carrier) : AbstractTorsors (abstr G) ≔ (bq_gset G z, bq_torsor_witness G z)

def bq_point (G : Group) : Id (AbstractTorsors (abstr G)) (abstract_principal_torsor (abstr G)) (bq_map G (shape G))
  ≔ let P ≔ agset_principal (abstr G) in let X ≔ AbstractGSet (abstr G) in
    (refl P,
     pathover_hlevel zero. X (Y ↦ Mere (Id X P Y)) (Y ↦ prop_to_hlevel_one (Mere (Id X P Y)) (mere_isprop (Id X P Y)))
       P P (refl P) (abstract_principal_torsor (abstr G) .snd) (bq_torsor_witness G (shape G)) .center)

def bq_pointed (G : Group) : BookPointedMap (BG G) (BG (concr (abstr G))) ≔ (bq_map G, bq_point G)

{` def:qG-concr-abstr. q_G : Hom(G, concr(abstr(G))) classified by Bq_G. `}
def q_hom (G : Group) : GroupHom G (concr (abstr G)) ≔ mkhom G (concr (abstr G)) (bq_pointed G)

{` Proof of lem:Groupsareidentitytypes: under the identification of
   (Bq x = Bq y) with Iso, Bq(r) for r : x = y is preinv_{sh}(r) = (p ↦ p r⁻¹). `}
def bq_ap_iso_map (G : Group) (x y : BG G .carrier) (r : Id (BG G .carrier) x y) (p : Id (BG G .carrier) x (shape G))
  : Id (Id (BG G .carrier) y (shape G))
      (agset_path_to_iso (abstr G) (bq_gset G x) (bq_gset G y) (refl (bq_gset G) r) .fst .map p)
      (path_preinv (BG G .carrier) y x (shape G) r p)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    J A x (y r ↦ (p : Id A x a) → Id (Id A y a)
        (agset_path_to_iso (abstr G) (bq_gset G x) (bq_gset G y) (refl (bq_gset G) r) .fst .map p)
        (path_preinv A y x a r p))
      (p ↦ concat (Id A x a)
        (agset_path_to_iso (abstr G) (bq_gset G x) (bq_gset G x) (refl (bq_gset G x)) .fst .map p) p
        (path_preinv A x x a (refl x) p)
        (agset_path_to_iso_refl_map (abstr G) (bq_gset G x) p)
        (inverse (Id A x a) (path_preinv A x x a (refl x) p) p
          (concat (Id A x a) (concat A x x a (inverse A x x (refl x)) p) (concat A x x a (refl x) p) p
            (refl ((q ↦ concat A x x a q p) : Id A x x → Id A x a) (inverse_refl A x))
            (concat_1p A x a p))))
      y r p

{` For a symmetry ω of sh_G, Bq(ω) is r_{abstr G}(ω) (right multiplication
   by ω⁻¹, i.e. preinv). `}
def bq_loops_iso (G : Group) (ω : USym G)
  : Id (AbstractGSetIso (abstr G) (agset_principal (abstr G)) (agset_principal (abstr G)))
      (agset_path_to_iso (abstr G) (bq_gset G (shape G)) (bq_gset G (shape G)) (refl (bq_gset G) ω))
      (abstract_r_map (abstr G) ω)
  ≔ agset_iso_path (abstr G) (agset_principal (abstr G)) (agset_principal (abstr G))
      (agset_path_to_iso (abstr G) (bq_gset G (shape G)) (bq_gset G (shape G)) (refl (bq_gset G) ω))
      (abstract_r_map (abstr G) ω)
      (p ↦ bq_ap_iso_map G (shape G) (shape G) ω p)

def bq_loops_comparison (G : Group)
  : Equiv (Id (AbstractTorsors (abstr G)) (bq_map G (shape G)) (bq_map G (shape G)))
      (AbstractGSetIso (abstr G) (agset_principal (abstr G)) (agset_principal (abstr G)))
  ≔ compose_equiv (Id (AbstractTorsors (abstr G)) (bq_map G (shape G)) (bq_map G (shape G)))
      (Id (AbstractGSet (abstr G)) (agset_principal (abstr G)) (agset_principal (abstr G)))
      (AbstractGSetIso (abstr G) (agset_principal (abstr G)) (agset_principal (abstr G)))
      (abstract_torsors_path_equiv (abstr G) (bq_map G (shape G)) (bq_map G (shape G)))
      (agset_path_iso_equiv (abstr G) (agset_principal (abstr G)) (agset_principal (abstr G)))

{` Bq_G induces an equivalence on symmetries of sh_G. `}
def bq_loops_equiv (G : Group)
  : Equiv (USym G) (Id (AbstractTorsors (abstr G)) (bq_map G (shape G)) (bq_map G (shape G)))
  ≔ let T ≔ Id (AbstractTorsors (abstr G)) (bq_map G (shape G)) (bq_map G (shape G)) in
    let I ≔ AbstractGSetIso (abstr G) (agset_principal (abstr G)) (agset_principal (abstr G)) in
    let E ≔ bq_loops_comparison G in
    let apw ≔ map_path (BG G .carrier) (AbstractTorsors (abstr G)) (bq_map G) (shape G) (shape G) in
    equiv_change_map (USym G) T
      (compose_equiv (USym G) I T (abstract_r_equiv (abstr G)) (canonical_inverse_equiv T I E))
      apw
      (ω ↦ concat T (equiv_inverse_map T I E (abstract_r_map (abstr G) ω)) (equiv_inverse_map T I E (E .map (apw ω))) (apw ω)
        (refl (equiv_inverse_map T I E) (inverse I (E .map (apw ω)) (abstract_r_map (abstr G) ω) (bq_loops_iso G ω)))
        (equiv_retraction T I E (apw ω)))

{` lem:Groupsareidentitytypes. q_G is an isomorphism: Bq_G is an
   equivalence (cor:fib-vs-path, via the loops at sh_G as in the book). `}
def q_hom_is_iso (G : Group) : IsGroupIso G (concr (abstr G)) (q_hom G)
  ≔ connected_map_equiv_from_loops native_truncation (BG G .carrier) (AbstractTorsors (abstr G)) (bq_map G)
      (bg_connected G) (abstract_torsors_connected (abstr G)) (shape G)
      (book_equivalence (USym G) (Id (AbstractTorsors (abstr G)) (bq_map G (shape G)) (bq_map G (shape G)))
        (bq_loops_equiv G) .equiv)
    .equiv

def q_iso (G : Group) : GroupIso G (concr (abstr G)) ≔ (q_hom G, q_hom_is_iso G)

{` concr(abstr(G)) = G. `}
def concr_abstr_path (G : Group) : Id Group (concr (abstr G)) G
  ≔ inverse Group G (concr (abstr G)) (group_path_from_iso G (concr (abstr G)) (q_iso G))
