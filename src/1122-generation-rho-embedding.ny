export "1120-cayley-graphs"

{` lem:gens-gp-iff (fggroups.tex:162), "only if" direction: if F_S → G has connected
   fibers (equivalently, by lem:epi-surj, is an epimorphism / is surjective on
   symmetries) then ρ_S : BG → Σ_X (S → X → X) is an embedding
   (rho_embedding_of_connected).  See the header of module 1120 for the proof idea;
   the "if" direction is refuted in module 1121. `}

{` ---------- lem:gens-gp-iff, "only if" ---------- `}

{` Ev : (B F_S → U) → Σ_X (S → X → X), evaluation at base and transport along the loops. `}
def ev_map (S : Type) (Fs : FreeGroupSignature S) (P : Fs .carrier → Type) : RhoTarget S
  ≔ (P (Fs .base), s ↦ refl P (Fs .loop s) .trr)

def bouquet_coe (S : Type) (u : BouquetData S Type) : RhoTarget S
  ≔ (u .fst, s ↦ u .snd s .trr)

def bouquet_coe_embedding (S : Type) : IsEmbedding (BouquetData S Type) (RhoTarget S) (bouquet_coe S)
  ≔ sigma_fiberwise_embedding Type (X ↦ S → Id Type X X) (X ↦ S → X → X) (X l s ↦ l s .trr)
      (X ↦ postcomposition_embedding S (Id Type X X) (X → X) (p ↦ p .trr) (coe_embedding X))

def ev_embedding (S : Type) (Fs : FreeGroupSignature S) : IsEmbedding (Fs .carrier → Type) (RhoTarget S) (ev_map S Fs)
  ≔ embedding_compose (Fs .carrier → Type) (BouquetData S Type) (RhoTarget S) (free_bouquet S Fs Type) (bouquet_coe S)
      (embedding_of_equiv (Fs .carrier → Type) (BouquetData S Type) (free_universal_property S Fs Type))
      (bouquet_coe_embedding S)

{` Y(t) ≔ (z ↦ t = Bφ(z)), the representable family restricted along Bφ. `}
def restricted_representable (G H : Group) (f : GroupHom H G) (t : BG G .carrier) : BG H .carrier → Type
  ≔ z ↦ Id (BG G .carrier) t (hom_function H G f z)

def restricted_representable_ap_equiv (G H : Group) (f : GroupHom H G)
  (hc : ConnectedFibers (BG H .carrier) (BG G .carrier) (hom_function H G f)) (t t' : BG G .carrier)
  : Equiv (Id (BG G .carrier) t t')
      (Id (BG H .carrier → Type) (restricted_representable G H f t) (restricted_representable G H f t'))
  ≔ let B ≔ BG G .carrier in
    let BH ≔ BG H .carrier in
    let Rt ≔ Representable B t in
    let Rt' ≔ Representable B t' in
    let Y ≔ restricted_representable G H f in
    compose_equiv (Id B t t') (Id (B → Type) Rt Rt') (Id (BH → Type) (Y t) (Y t'))
      (native_equivalence (Id B t t') (Id (B → Type) Rt Rt') (representable_ap_equiv B t t'))
      (compose_equiv (Id (B → Type) Rt Rt') ((u : B) → Equiv (Rt u) (Rt' u)) (Id (BH → Type) (Y t) (Y t'))
        (type_family_paths_equiv B Rt Rt')
        (compose_equiv ((u : B) → Equiv (Rt u) (Rt' u)) ((z : BH) → Equiv (Y t z) (Y t' z)) (Id (BH → Type) (Y t) (Y t'))
          (connected_map_sections_equiv BH B (hom_function H G f) hc (u ↦ Equiv (Rt u) (Rt' u))
            (u ↦ equivalences_set (Rt u) (Rt' u) (bg_groupoid G t' u)))
          (canonical_inverse_equiv (Id (BH → Type) (Y t) (Y t')) ((z : BH) → Equiv (Y t z) (Y t' z))
            (type_family_paths_equiv BH (Y t) (Y t')))))

def restricted_representable_embedding (G H : Group) (f : GroupHom H G)
  (hc : ConnectedFibers (BG H .carrier) (BG G .carrier) (hom_function H G f))
  : IsEmbedding (BG G .carrier) (BG H .carrier → Type) (restricted_representable G H f)
  ≔ let B ≔ BG G .carrier in
    let BH ≔ BG H .carrier in
    let Y ≔ restricted_representable G H f in
    path_equivalences_embedding B (BH → Type) Y
      (t t' ↦ book_equivalence (Id B t t') (Id (BH → Type) (Y t) (Y t'))
        (map_path B (BH → Type) Y t t',
         isequiv_of_homotopic (Id B t t') (Id (BH → Type) (Y t) (Y t'))
           (restricted_representable_ap_equiv G H f hc t t') (map_path B (BH → Type) Y t t')
           (q ↦ equiv_retraction (Id (BH → Type) (Y t) (Y t')) ((z : BH) → Equiv (Y t z) (Y t' z))
              (type_family_paths_equiv BH (Y t) (Y t')) (map_path B (BH → Type) Y t t' q))) .equiv)

{` ---------- ρ_S = Ev ∘ Y ---------- `}

{` An equivalence intertwining the endomaps identifies the structures. `}
def sigma_endo_path (S X : Type) (f : S → X → X)
  : (X' : Type) (e : Equiv X X') (g : S → X' → X')
    (h : (s : S) (x : X) → Id X' (e .map (f s x)) (g s (e .map x))) → Id (RhoTarget S) (X, f) (X', g)
  ≔ X' e ↦ equivalence_induction X
      (X' e ↦ (g : S → X' → X') (h : (s : S) (x : X) → Id X' (e .map (f s x)) (g s (e .map x))) → Id (RhoTarget S) (X, f) (X', g))
      (g h ↦ (refl X, funext2 S (_ ↦ X) (_ _ ↦ X) f g h)) X' e

def concat_right_equiv (B : Type) (t a b : B) (p0 : Id B a b) : Equiv (Id B t a) (Id B t b)
  ≔ quasi_inverse_equiv (Id B t a) (Id B t b) (q ↦ concat B t a b q p0) (r ↦ concat B t b a r (inverse B a b p0))
      (q ↦ concat (Id B t a) (concat B t b a (concat B t a b q p0) (inverse B a b p0)) (concat B t a a q (concat B a b a p0 (inverse B a b p0))) q
        (concat_assoc B t a b a q p0 (inverse B a b p0))
        (concat (Id B t a) (concat B t a a q (concat B a b a p0 (inverse B a b p0))) (concat B t a a q (refl a)) q
          (refl (concat B t a a q) (concat_inverse_right B a b p0)) (concat_p1 B t a q)))
      (r ↦ concat (Id B t b) (concat B t a b (concat B t b a r (inverse B a b p0)) p0) (concat B t b b r (concat B b a b (inverse B a b p0) p0)) r
        (concat_assoc B t b a b r (inverse B a b p0) p0)
        (concat (Id B t b) (concat B t b b r (concat B b a b (inverse B a b p0) p0)) (concat B t b b r (refl b)) r
          (refl (concat B t b b r) (concat_inverse_left B a b p0)) (concat_p1 B t b r)))

{` (p · m · p⁻¹) · p = p · m, in concat order. `}
def conjugate_concat_cancel (A : Type) (a x : A) (p : Id A a x) (m : Id A x x)
  : Id (Id A a x) (concat A a a x (pointed_loop_conjugate A a x p m) p) (concat A a x x p m)
  ≔ J A a (x p ↦ (m : Id A x x) → Id (Id A a x) (concat A a a x (pointed_loop_conjugate A a x p m) p) (concat A a x x p m))
      (m ↦ concat (Id A a a) (concat A a a a (pointed_loop_conjugate A a a (refl a) m) (refl a))
          (pointed_loop_conjugate A a a (refl a) m) (concat A a a a (refl a) m)
          (concat_p1 A a a (pointed_loop_conjugate A a a (refl a) m))
          (concat (Id A a a) (pointed_loop_conjugate A a a (refl a) m) m (concat A a a a (refl a) m)
            (loop_conjugate_at_refl A a m) (inverse (Id A a a) (concat A a a a (refl a) m) m (concat_1p A a a m))))
      x p m

def rho_ev_path (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G) (t : BG G .carrier)
  : Id (RhoTarget S) (rho_map G S iota t)
      (ev_map S (constructed_free_group_signature S dec)
        (restricted_representable G (constructed_free_group S dec) (free_induced_hom S dec G iota) t))
  ≔ let F ≔ constructed_free_group S dec in
    let Fs ≔ constructed_free_group_signature S dec in
    let phi ≔ free_induced_hom S dec G iota in
    let B ≔ BG G .carrier in
    let f ≔ hom_function F G phi in
    let b0 ≔ Fs .base in
    let sh ≔ shape G in
    let p0 ≔ hom_point F G phi in
    sigma_endo_path S (Id B t sh) (rho_map G S iota t .snd) (Id B t (f b0)) (concat_right_equiv B t sh (f b0) p0)
      (s q ↦ concat B t (f b0) (f b0) q (refl f (Fs .loop s)))
      (s q ↦
        let l ≔ refl f (Fs .loop s) in
        let i ≔ iota s in
        concat (Id B t (f b0)) (concat B t sh (f b0) (concat B t sh sh q i) p0) (concat B t sh (f b0) q (concat B sh sh (f b0) i p0))
          (concat B t (f b0) (f b0) (concat B t sh (f b0) q p0) l)
          (concat_assoc B t sh sh (f b0) q i p0)
          (concat (Id B t (f b0)) (concat B t sh (f b0) q (concat B sh sh (f b0) i p0)) (concat B t sh (f b0) q (concat B sh (f b0) (f b0) p0 l))
            (concat B t (f b0) (f b0) (concat B t sh (f b0) q p0) l)
            (refl (concat B t sh (f b0) q)
              (concat (Id B sh (f b0)) (concat B sh sh (f b0) i p0) (concat B sh sh (f b0) (pointed_loop_conjugate B sh (f b0) p0 l) p0)
                (concat B sh (f b0) (f b0) p0 l)
                (refl (x ↦ concat B sh sh (f b0) x p0)
                  (inverse (USym G) (usym_hom F G phi (constructed_free_group_generator S dec s)) i
                    (free_induced_hom_generator S dec G iota s)))
                (conjugate_concat_cancel B sh (f b0) p0 l)))
            (inverse (Id B t (f b0)) (concat B t (f b0) (f b0) (concat B t sh (f b0) q p0) l) (concat B t sh (f b0) q (concat B sh (f b0) (f b0) p0 l))
              (concat_assoc B t sh (f b0) (f b0) q p0 l))))

{` lem:gens-gp-iff, "only if" (connected-fibers form of generation, lem:epi-surj (3')). `}
def rho_embedding_of_connected (S : Type) (dec : DecidableEquality S) (G : Group) (iota : S → USym G)
  (hc : ConnectedFibers (BG (constructed_free_group S dec) .carrier) (BG G .carrier)
          (hom_function (constructed_free_group S dec) G (free_induced_hom S dec G iota)))
  : RhoEmbedding G S iota
  ≔ let F ≔ constructed_free_group S dec in
    let Fs ≔ constructed_free_group_signature S dec in
    let phi ≔ free_induced_hom S dec G iota in
    embedding_homotopic (BG G .carrier) (RhoTarget S)
      (t ↦ ev_map S Fs (restricted_representable G F phi t)) (rho_map G S iota)
      (t ↦ inverse (RhoTarget S) (rho_map G S iota t) (ev_map S Fs (restricted_representable G F phi t)) (rho_ev_path S dec G iota t))
      (embedding_compose (BG G .carrier) (Fs .carrier → Type) (RhoTarget S) (restricted_representable G F phi) (ev_map S Fs)
        (restricted_representable_embedding G F phi hc) (ev_embedding S Fs))
