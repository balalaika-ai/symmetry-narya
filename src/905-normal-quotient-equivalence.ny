export "904-normal-quotients"

{` Chapter 9 (subgroups.tex), sec:normal, part 3: lem:qeq. nor and q are
   inverse to each other. Stated here on ConnectedEpis G (homomorphisms out
   of G with connected fibers, condition (3') of lem:epi-surj); module 906
   transfers it to the book's Epi(G) via lem:epi-surj. `}

{` Homomorphisms out of G (Σ_{H:Group} Hom(G, H)); identifications from
   isomorphisms: (H, f) = (H', Q ∘ f) for Q : Iso(H, H') (iso induction,
   group_iso_total_contractible). `}
def HomsFrom (G : Group) : Type ≔ Σ Group (H ↦ GroupHom G H)

def qeq_iso_family (G H : Group) (f : GroupHom G H) (w : Σ Group (K ↦ GroupIso H K)) : Type
  ≔ Id (HomsFrom G) (H, f) (w .fst, group_hom_compose G H (w .fst) f (w .snd .fst))

def qeq_iso_base (G H : Group) (f : GroupHom G H) : qeq_iso_family G H f (H, group_iso_id H)
  ≔ map_path (GroupHom G H) (HomsFrom G) (k ↦ (H, k)) f (group_hom_compose G H H f (group_hom_id H))
      (inverse (GroupHom G H) (group_hom_compose G H H f (group_hom_id H)) f (group_hom_compose_id G H f))

def homs_from_iso_path (G H K : Group) (f : GroupHom G H) (Q : GroupIso H K)
  : Id (HomsFrom G) (H, f) (K, group_hom_compose G H K f (Q .fst))
  ≔ let T ≔ Σ Group (L ↦ GroupIso H L) in
    let c ≔ group_iso_total_contractible H in
    let i : T ≔ (H, group_iso_id H) in
    transport T (qeq_iso_family G H f) i (K, Q)
      (concat T i (c .center) (K, Q) (c .contract i) (inverse T (K, Q) (c .center) (c .contract (K, Q))))
      (qeq_iso_base G H f)

{` Homomorphisms into K (Σ_{H:Group} Hom(H, K)); (L, k ∘ Q) = (M, k) for an
   isomorphism Q : L ≅ M (iso induction). `}
def HomsInto (K : Group) : Type ≔ Σ Group (H ↦ GroupHom H K)

def homs_into_iso_family (K L : Group) (w : Σ Group (M ↦ GroupIso L M)) : Type
  ≔ (k : GroupHom (w .fst) K) → Id (HomsInto K) (L, group_hom_compose L (w .fst) K (w .snd .fst) k) (w .fst, k)

def homs_into_iso_base (K L : Group) : homs_into_iso_family K L (L, group_iso_id L)
  ≔ k ↦ map_path (GroupHom L K) (HomsInto K) (k' ↦ (L, k')) (group_hom_compose L L K (group_hom_id L) k) k
      (group_hom_id_compose L K k)

{` (L, k ∘ Q) = (M, k) in Σ_{H} Hom(H, K) for an isomorphism Q : L ≅ M. `}
def homs_into_iso_path (K L M : Group) (Q : GroupIso L M) (k : GroupHom M K)
  : Id (HomsInto K) (L, group_hom_compose L M K (Q .fst) k) (M, k)
  ≔ let T ≔ Σ Group (M' ↦ GroupIso L M') in
    let c ≔ group_iso_total_contractible L in
    let i : T ≔ (L, group_iso_id L) in
    transport T (homs_into_iso_family K L) i (M, Q)
      (concat T i (c .center) (M, Q) (c .contract i) (inverse T (M, Q) (c .center) (c .contract (M, Q))))
      (homs_into_iso_base K L) k

{` lem:qeq, first half: nor(q(N)) = N. At y : BG, nor(q N)(y) is the G-set
   z ↦ (Bq_N(y) = Bq_N(z)) ≃ (X_y = X_z) ≃ (X_z = X_y) ≃ X_y(z) (the last step
   is ev_zy of lem:evaliseqwhennormal), pointed at refl ↦ pt_y. `}
def qeq_nor_q_equiv (G : Group) (N : NormalSubgroups G) (y z : BG G .carrier)
  : Equiv (nor_gset G (normal_quotient_group G N) (normal_quotient_hom G N) y z .fst) (normal_family G N y z .fst)
  ≔ let C ≔ BG (normal_quotient_group G N) .carrier in
    let Bq ≔ normal_quotient_map G N in
    let X ≔ normal_family G N in
    compose_equiv (Id C (Bq y) (Bq z)) (Id (GSet G) (X y) (X z)) (X y z .fst)
      (component_path_equiv (GSet G) (X (shape G)) (Bq y) (Bq z))
      (compose_equiv (Id (GSet G) (X y) (X z)) (Id (GSet G) (X z) (X y)) (X y z .fst)
        (inverse_path_equiv (GSet G) (X y) (X z))
        (native_equivalence (Id (GSet G) (X z) (X y)) (X y z .fst) (normal_evaluation_equiv G N z y)))

def qeq_nor_q_point (G : Group) (N : NormalSubgroups G) (y : BG G .carrier)
  : Id (normal_family G N y y .fst)
      (qeq_nor_q_equiv G N y y .map (refl (normal_quotient_map G N y))) (normal_family_point G N y)
  ≔ let X ≔ normal_family G N in
    concat (X y y .fst) (qeq_nor_q_equiv G N y y .map (refl (normal_quotient_map G N y)))
      (normal_evaluation G N y y (refl (X y))) (normal_family_point G N y)
      (refl (normal_evaluation G N y y) (inverse_refl (GSet G) (X y)))
      (transport_refl (GSet G) (W ↦ W y .fst) (X y) (normal_family_point G N y))

def qeq_nor_q_at (G : Group) (N : NormalSubgroups G) (y : BG G .carrier)
  : Id (Subgroups (group_at G y))
      (nor_conn G (normal_quotient_connected_epis G N) y) (N y)
  ≔ let Gy ≔ group_at G y in
    let S ≔ nor_conn G (normal_quotient_connected_epis G N) y in
    subgroup_path Gy S (N y)
      (pointed_gset_path Gy (S .gset) (N y .gset) (S .point) (N y .point)
        (z ↦ qeq_nor_q_equiv G N y z) (qeq_nor_q_point G N y))

def nor_q_path (G : Group) (N : NormalSubgroups G)
  : Id (NormalSubgroups G) (nor_conn G (normal_quotient_connected_epis G N)) N
  ≔ funext (BG G .carrier) (y ↦ Subgroups (group_at G y))
      (nor_conn G (normal_quotient_connected_epis G N)) N (qeq_nor_q_at G N)

{` lem:qeq, second half. For f : Hom(G, H) with connected fibers, the
   homomorphism Q : Hom(H, G/nor f), BQ(z) ≔ P_z ∘ Bf (z ↦ (z = Bf(-)) as a
   G-set), pointed by Bf_pt, satisfies Q ∘ f = q_{nor f} and is an
   isomorphism (ap BQ is ap of restriction along f, an equivalence by
   lem:epifullyfaithful, after ap P_-, an equivalence by
   lem:pathsptransportiseq). `}
def qeq_restricted_paths (G H : Group) (f : GroupHom G H) (z : BG H .carrier) : GSet G
  ≔ gset_restrict G H f (gset_paths H z)

def qeq_nor_family_value (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f) (y : BG G .carrier)
  : Id (GSet G) (normal_family G (nor_conn G (H, (f, c))) y) (qeq_restricted_paths G H f (hom_function G H f y))
  ≔ refl (qeq_restricted_paths G H f (hom_function G H f y))

def qeq_Q_map (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : BG H .carrier → BG (normal_quotient_group G (nor_conn G (H, (f, c)))) .carrier
  ≔ let X0 ≔ qeq_restricted_paths G H f (hom_function G H f (shape G)) in
    let R ≔ qeq_restricted_paths G H f in
    let p ≔ hom_point G H f in
    w ↦ (R w,
         mere_rec (Id (BG H .carrier) (shape H) w) (Mere (Id (GSet G) X0 (R w)))
           (mere_isprop (Id (GSet G) X0 (R w)))
           (r ↦ mere (Id (GSet G) X0 (R w))
             (map_path (BG H .carrier) (GSet G) R (hom_function G H f (shape G)) w
               (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) w
                 (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) p) r)))
           (bg_connected H .snd (shape H) w))

def qeq_Q_point (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : Id (BG (normal_quotient_group G (nor_conn G (H, (f, c)))) .carrier)
      (shape (normal_quotient_group G (nor_conn G (H, (f, c))))) (qeq_Q_map G H f c (shape H))
  ≔ let X0 ≔ qeq_restricted_paths G H f (hom_function G H f (shape G)) in
    component_path (GSet G) X0 (shape (normal_quotient_group G (nor_conn G (H, (f, c))))) (qeq_Q_map G H f c (shape H))
      (map_path (BG H .carrier) (GSet G) (qeq_restricted_paths G H f) (hom_function G H f (shape G)) (shape H)
        (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)))

def qeq_Q (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : GroupHom H (normal_quotient_group G (nor_conn G (H, (f, c))))
  ≔ mkhom H (normal_quotient_group G (nor_conn G (H, (f, c)))) (qeq_Q_map G H f c, qeq_Q_point G H f c)

{` ap BQ is an equivalence at all pairs of points. `}
def qeq_Q_ap_is_equiv (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f) (w w' : BG H .carrier)
  : BookIsEquiv (Id (BG H .carrier) w w')
      (Id (BG (normal_quotient_group G (nor_conn G (H, (f, c)))) .carrier) (qeq_Q_map G H f c w) (qeq_Q_map G H f c w'))
      (map_path (BG H .carrier) (BG (normal_quotient_group G (nor_conn G (H, (f, c)))) .carrier) (qeq_Q_map G H f c) w w')
  ≔ let B ≔ BG H .carrier in
    let C ≔ BG (normal_quotient_group G (nor_conn G (H, (f, c)))) .carrier in
    let BQ ≔ qeq_Q_map G H f c in
    let R ≔ qeq_restricted_paths G H f in
    let X0 ≔ R (hom_function G H f (shape G)) in
    let PB ≔ Id B w w' in
    let PP ≔ Id (GSet H) (gset_paths H w) (gset_paths H w') in
    let PR ≔ Id (GSet G) (R w) (R w') in
    let PC ≔ Id C (BQ w) (BQ w') in
    let cpe ≔ component_path_equiv (GSet G) X0 (BQ w) (BQ w') in
    let e ≔ compose_equiv PB PP PC
      (native_equivalence PB PP (gset_paths_ap_equiv H w w'))
      (compose_equiv PP PR PC
        (native_equivalence PP PR
          (map_path (GSet H) (GSet G) (gset_restrict G H f) (gset_paths H w) (gset_paths H w'),
           restrict_paths_is_equiv G H f (gepi_connected_fibers_usym_surjective G H f c) (gset_paths H w) (gset_paths H w')))
        (canonical_inverse_equiv PC PR cpe)) in
    book_equivalence PB PC
      (equiv_change_map PB PC e (map_path B C BQ w w')
        (r ↦ equiv_retraction PC PR cpe (map_path B C BQ w w' r)))
    .equiv

def qeq_Q_iso (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : IsGroupIso H (normal_quotient_group G (nor_conn G (H, (f, c)))) (qeq_Q G H f c)
  ≔ let Q ≔ normal_quotient_group G (nor_conn G (H, (f, c))) in
    native_connected_map_equiv_from_paths (BG H .carrier) (BG Q .carrier) (qeq_Q_map G H f c)
      (bg_connected H) (bg_connected Q) (qeq_Q_ap_is_equiv G H f c) .equiv

{` Q ∘ f = q_{nor f}: the classifying maps agree (first components are
   both z ↦ P_{f z} ∘ f), and so do the pointings (first components
   ap_R(Bf_pt⁻¹) · ap_R(Bf_pt) and refl). `}
def qeq_point_algebra (A B : Type) (R : A → B) (a b : A) (p : Id A a b)
  : Id (Id B (R b) (R b))
      (concat B (R b) (R b) (R b)
        (concat B (R b) (R a) (R b) (map_path A B R b a (inverse A a b p)) (map_path A B R a b p)) (refl (R b)))
      (refl (R b))
  ≔ J A a
      (b p ↦ Id (Id B (R b) (R b))
        (concat B (R b) (R b) (R b)
          (concat B (R b) (R a) (R b) (map_path A B R b a (inverse A a b p)) (map_path A B R a b p)) (refl (R b)))
        (refl (R b)))
      (calc
        concat B (R a) (R a) (R a)
          (concat B (R a) (R a) (R a) (map_path A B R a a (inverse A a a (refl a))) (refl (R a))) (refl (R a))
        = concat B (R a) (R a) (R a) (map_path A B R a a (inverse A a a (refl a))) (refl (R a))
          by concat_p1 B (R a) (R a)
               (concat B (R a) (R a) (R a) (map_path A B R a a (inverse A a a (refl a))) (refl (R a)))
        = map_path A B R a a (inverse A a a (refl a))
          by concat_p1 B (R a) (R a) (map_path A B R a a (inverse A a a (refl a)))
        = refl (R a) by refl (map_path A B R a a) (inverse_refl A a) ∎)
      b p

def qeq_Q_compose_path (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : Id (GroupHom G (normal_quotient_group G (nor_conn G (H, (f, c)))))
      (group_hom_compose G H (normal_quotient_group G (nor_conn G (H, (f, c)))) f (qeq_Q G H f c))
      (normal_quotient_hom G (nor_conn G (H, (f, c))))
  ≔ let N ≔ nor_conn G (H, (f, c)) in
    let Qg ≔ normal_quotient_group G N in
    let C ≔ BG Qg .carrier in
    let A ≔ BG G .carrier in
    let BH ≔ BG H .carrier in
    let Bf ≔ hom_function G H f in
    let p ≔ hom_point G H f in
    let R ≔ qeq_restricted_paths G H f in
    let X0 ≔ R (Bf (shape G)) in
    let BQ ≔ qeq_Q_map G H f c in
    let Bq ≔ normal_quotient_map G N in
    let comp ≔ group_hom_compose G H Qg f (qeq_Q G H f c) in
    let h : (x : A) → Id C (BQ (Bf x)) (Bq x)
      ≔ x ↦ component_path (GSet G) X0 (BQ (Bf x)) (Bq x) (refl (R (Bf x))) in
    let c0 ≔ shape Qg in
    let lhs ≔ concat C c0 (BQ (Bf (shape G))) (Bq (shape G)) (hom_point G Qg comp) (h (shape G)) in
    let cpe ≔ component_path_equiv (GSet G) X0 c0 (Bq (shape G)) in
    let fst_eq : Id (Id (GSet G) X0 X0) (cpe .map lhs) (cpe .map (normal_quotient_point G N))
      ≔ calc
          cpe .map lhs
          = concat (GSet G) X0 (R (Bf (shape G))) X0 (hom_point G Qg comp .fst) (refl X0)
            by map_path_concat C (GSet G) (u ↦ u .fst) c0 (BQ (Bf (shape G))) (Bq (shape G))
                 (hom_point G Qg comp) (h (shape G))
          = concat (GSet G) X0 X0 X0
              (concat (GSet G) X0 (R (shape H)) X0
                (map_path BH (GSet G) R (Bf (shape G)) (shape H) (inverse BH (shape H) (Bf (shape G)) p))
                (map_path BH (GSet G) R (shape H) (Bf (shape G)) p))
              (refl X0)
            by refl ((r ↦ concat (GSet G) X0 X0 X0 r (refl X0)) : Id (GSet G) X0 X0 → Id (GSet G) X0 X0)
                 (map_path_concat C (GSet G) (u ↦ u .fst) c0 (BQ (shape H)) (BQ (Bf (shape G)))
                   (qeq_Q_point G H f c) (map_path BH C BQ (shape H) (Bf (shape G)) p))
          = refl X0 by qeq_point_algebra BH (GSet G) R (shape H) (Bf (shape G)) p
          = cpe .map (normal_quotient_point G N) by refl (refl X0) ∎ in
    equiv_inverse_map (Id (GroupHom G Qg) comp (normal_quotient_hom G N))
      (PointedHomotopy (BG G) (BG Qg) (hom_B G Qg comp) (hom_B G Qg (normal_quotient_hom G N)))
      (group_hom_path_equiv G Qg comp (normal_quotient_hom G N))
      (h, equivalence_injective (Id C c0 (Bq (shape G))) (Id (GSet G) X0 X0) cpe lhs (normal_quotient_point G N) fst_eq)

def qeq_q_nor_homs_path (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : Id (HomsFrom G) (H, f)
      (normal_quotient_group G (nor_conn G (H, (f, c))), normal_quotient_hom G (nor_conn G (H, (f, c))))
  ≔ let N ≔ nor_conn G (H, (f, c)) in
    let Qg ≔ normal_quotient_group G N in
    concat (HomsFrom G) (H, f) (Qg, group_hom_compose G H Qg f (qeq_Q G H f c)) (Qg, normal_quotient_hom G N)
      (homs_from_iso_path G H Qg f (qeq_Q G H f c, qeq_Q_iso G H f c))
      (map_path (GroupHom G Qg) (HomsFrom G) (k ↦ (Qg, k))
        (group_hom_compose G H Qg f (qeq_Q G H f c)) (normal_quotient_hom G N) (qeq_Q_compose_path G H f c))

{` ConnectedEpis G as a subtype of HomsFrom G. `}
def qeq_connected_epis_reassoc (G : Group) (e : Σ (HomsFrom G) (u ↦ IsConnectedHom G (u .fst) (u .snd)))
  : ConnectedEpis G ≔ (e .fst .fst, (e .fst .snd, e .snd))

def q_nor_path (G : Group) (e : ConnectedEpis G)
  : Id (ConnectedEpis G) (normal_quotient_connected_epis G (nor_conn G e)) e
  ≔ let H ≔ e .fst in let f ≔ e .snd .fst in let c ≔ e .snd .snd in
    let N ≔ nor_conn G e in
    let S ≔ Σ (HomsFrom G) (u ↦ IsConnectedHom G (u .fst) (u .snd)) in
    map_path S (ConnectedEpis G) (qeq_connected_epis_reassoc G)
      ((normal_quotient_group G N, normal_quotient_hom G N), normal_quotient_connected G N) ((H, f), c)
      (subtype_equal (HomsFrom G) (u ↦ IsConnectedHom G (u .fst) (u .snd)) (u ↦ is_connected_hom_prop G (u .fst) (u .snd))
        ((normal_quotient_group G N, normal_quotient_hom G N), normal_quotient_connected G N) ((H, f), c)
        (inverse (HomsFrom G) (H, f) (normal_quotient_group G N, normal_quotient_hom G N) (qeq_q_nor_homs_path G H f c)))

{` lem:qeq: nor is an equivalence with inverse q. `}
def nor_conn_equiv (G : Group) : Equiv (ConnectedEpis G) (NormalSubgroups G)
  ≔ quasi_inverse_equiv (ConnectedEpis G) (NormalSubgroups G) (nor_conn G) (normal_quotient_connected_epis G)
      (q_nor_path G) (nor_q_path G)
