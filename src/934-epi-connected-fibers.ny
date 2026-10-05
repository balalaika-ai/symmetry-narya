export "930-epi-surj-easy"
export "931-twisted-homomorphisms"
export "933-group-completion"

{` Chapter 9 (subgroups.tex), lem:epi-surj (line 161), the hard direction
   (1') ⇒ (3'), constructively (no excluded middle, no decidable equality),
   and the three equivalences of the lemma.

   The book derives (1') ⇒ (2') from con:monos-are-equalizers (a draft
   following Trimble) and the epi-mono factorization through the image
   (marked TBD in the book). We give a direct version of the same idea. For
   f : Hom(G, H) let S ≔ X(sh_H) with X the cokernel,
   X(w) = ‖(Bf)⁻¹(w)‖₀ (SetTrunc of BookFiber), and choose a set T with a
   faithful-at-t0 family of permutations τ_s, s : S (module 933, replacing
   the book's injection of the coset set into a free (abelian) group). Let
   Y(t) ≔ (sh_H = t) → T, an H-set, W ≔ Σ_{Y(sh_H)} its permutation group
   and φ ≔ the action homomorphism H → W (gset_to_action, module 500). The
   permutations σ_z(v)(g) ≔ τ_{[z, g]}(v(g)) of Y(Bf z), z : BG, form a
   section α over BG of loops of Bφ ∘ Bf; ψ is φ with the pointing twisted
   by α(sh_G) (module 931). Then φ ∘ f = ψ ∘ f always; if f is an
   epimorphism, φ = ψ, so α(sh_G) commutes with all loops of Bφ at
   Bf(sh_G); evaluating the permutations at the constant function t0 gives
   [sh_G, g] = [sh_G, g · m⁻¹] for all g and loops m, hence S is
   contractible and all fibers of Bf are connected. `}

def gepi_coker_fiber (G H : Group) (f : GroupHom G H) : Type
  ≔ BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape H)

{` S = X(sh_H) for the cokernel X(w) = ‖(Bf)⁻¹(w)‖₀. `}
def gepi_coker_set (G H : Group) (f : GroupHom G H) : Type ≔ SetTrunc (gepi_coker_fiber G H f)

def gepi_coker_class (G H : Group) (f : GroupHom G H) (z : BG G .carrier)
  (g : Id (BG H .carrier) (shape H) (hom_function G H f z)) : gepi_coker_set G H f
  ≔ set_trunc (gepi_coker_fiber G H f) (z, g)

{` The test H-set Y(t) = (sh_H = t) → T, its permutation group W and the
   action homomorphism φ : H → W. `}
def gepi_test_gset (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f)) : GSet H
  ≔ t ↦ ((Id (BG H .carrier) (shape H) t → rep .carrier),
         pi_set (Id (BG H .carrier) (shape H) t) (_ ↦ rep .carrier) (_ ↦ rep .carrier_set))

def gepi_test_group (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f)) : Group
  ≔ permutation_group (gepi_test_gset G H f rep (shape H))

def gepi_test_hom (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f))
  : GroupHom H (gepi_test_group G H f rep)
  ≔ gset_to_action H (gepi_test_gset G H f rep)

{` σ_z(v)(g) = τ_{[z, g]}(v(g)), a permutation of Y(Bf z). `}
def gepi_test_sigma (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f)) (z : BG G .carrier)
  : Equiv (Id (BG H .carrier) (shape H) (hom_function G H f z) → rep .carrier)
      (Id (BG H .carrier) (shape H) (hom_function G H f z) → rep .carrier)
  ≔ let T ≔ rep .carrier in
    let P ≔ Id (BG H .carrier) (shape H) (hom_function G H f z) in
    let τ : P → Equiv T T ≔ g ↦ rep .act (gepi_coker_class G H f z g) in
    quasi_inverse_equiv (P → T) (P → T)
      (v g ↦ τ g .map (v g))
      (v g ↦ equiv_inverse_map T T (τ g) (v g))
      (v ↦ funext P (_ ↦ T) (g ↦ equiv_inverse_map T T (τ g) (τ g .map (v g))) v
         (g ↦ equiv_retraction T T (τ g) (v g)))
      (v ↦ funext P (_ ↦ T) (g ↦ τ g .map (equiv_inverse_map T T (τ g) (v g))) v
         (g ↦ equiv_counit T T (τ g) (v g)))

{` α(z) : Bφ(Bf z) = Bφ(Bf z), the symmetry of σ_z. `}
def gepi_test_alpha (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f)) (z : BG G .carrier)
  : Id (BG (gepi_test_group G H f rep) .carrier)
      (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) (hom_function G H f z))
      (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) (hom_function G H f z))
  ≔ let Y ≔ gepi_test_gset G H f rep in
    let Φ ≔ hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) in
    component_path SetTypes (Y (shape H)) (Φ (hom_function G H f z)) (Φ (hom_function G H f z))
      (set_types_path (Y (hom_function G H f z)) (Y (hom_function G H f z)) (gepi_test_sigma G H f rep z))

{` ψ : H → W, the action homomorphism with twisted pointing. `}
def gepi_test_hom_twisted (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f))
  : GroupHom H (gepi_test_group G H f rep)
  ≔ let W ≔ gepi_test_group G H f rep in
    let φ ≔ gepi_test_hom G H f rep in
    mkhom H W (hom_function H W φ,
      gepi_twisted_point G H W f (hom_function H W φ) (hom_point H W φ) (gepi_test_alpha G H f rep))

{` φ ∘ f = ψ ∘ f. `}
def gepi_test_homs_agree (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f))
  : Id (GroupHom G (gepi_test_group G H f rep))
      (group_hom_compose G H (gepi_test_group G H f rep) f (gepi_test_hom G H f rep))
      (group_hom_compose G H (gepi_test_group G H f rep) f (gepi_test_hom_twisted G H f rep))
  ≔ let W ≔ gepi_test_group G H f rep in
    let φ ≔ gepi_test_hom G H f rep in
    gepi_twisted_compose_path G H W f (hom_function H W φ) (hom_point H W φ) (gepi_test_alpha G H f rep)

{` Transport in t ↦ ((b0 = t) → T): precomposition with g ↦ g · q⁻¹. `}
def gepi_path_fun_transport (B T : Type) (b0 x y : B) (q : Id B x y) (v : Id B b0 x → T) (g : Id B b0 y)
  : Id T (transport B (t ↦ Id B b0 t → T) x y q v g) (v (concat B b0 y x g (inverse B x y q)))
  ≔ J B x (y q ↦ (g : Id B b0 y) → Id T (transport B (t ↦ Id B b0 t → T) x y q v g) (v (concat B b0 y x g (inverse B x y q))))
      (g ↦ calc
         transport B (t ↦ Id B b0 t → T) x x (refl x) v g
         = v g
           by happly (Id B b0 x) (_ ↦ T) (transport B (t ↦ Id B b0 t → T) x x (refl x) v) v
                (transport_refl B (t ↦ Id B b0 t → T) x v) g
         = v (concat B b0 x x g (inverse B x x (refl x)))
           by refl v (inverse (Id B b0 x) (concat B b0 x x g (inverse B x x (refl x))) g
                (concat (Id B b0 x) (concat B b0 x x g (inverse B x x (refl x))) (concat B b0 x x g (refl x)) g
                  (refl (concat B b0 x x g) (inverse_refl B x)) (concat_p1 B b0 x g))) ∎)
      y q g

{` The key evaluation. Suppose γ is a loop at Bφ(y) with
   α(sh_G) · ap_φ(s) = ap_φ(s) · γ for some s : Bf(sh_G) = y, and γ commutes
   with ap_φ(m) for a loop m at y. Transporting the constant function t0
   along both sides and evaluating at g : sh_H = y gives
   τ_{[sh_G, g m⁻¹ s⁻¹]}(t0) = τ_{[sh_G, g s⁻¹]}(t0), hence equality in S. `}
def gepi_core (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f))
  (y : BG H .carrier) (s : Id (BG H .carrier) (hom_function G H f (shape G)) y)
  (γ : Id (BG (gepi_test_group G H f rep) .carrier)
         (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) y)
         (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) y))
  (n1 : Id (Id (BG (gepi_test_group G H f rep) .carrier)
              (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) (hom_function G H f (shape G)))
              (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) y))
          (concat (BG (gepi_test_group G H f rep) .carrier)
             (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) (hom_function G H f (shape G)))
             (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) (hom_function G H f (shape G)))
             (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) y)
             (gepi_test_alpha G H f rep (shape G))
             (map_path (BG H .carrier) (BG (gepi_test_group G H f rep) .carrier)
                (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep)) (hom_function G H f (shape G)) y s))
          (concat (BG (gepi_test_group G H f rep) .carrier)
             (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) (hom_function G H f (shape G)))
             (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) y)
             (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) y)
             (map_path (BG H .carrier) (BG (gepi_test_group G H f rep) .carrier)
                (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep)) (hom_function G H f (shape G)) y s)
             γ))
  (m : Id (BG H .carrier) y y)
  (n2 : GepiLoopsCommute (BG (gepi_test_group G H f rep) .carrier)
          (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep) y) γ
          (map_path (BG H .carrier) (BG (gepi_test_group G H f rep) .carrier)
             (hom_function H (gepi_test_group G H f rep) (gepi_test_hom G H f rep)) y y m))
  (g : Id (BG H .carrier) (shape H) y)
  : Id (gepi_coker_set G H f)
      (gepi_coker_class G H f (shape G)
         (concat (BG H .carrier) (shape H) y (hom_function G H f (shape G))
            (concat (BG H .carrier) (shape H) y y g (inverse (BG H .carrier) y y m))
            (inverse (BG H .carrier) (hom_function G H f (shape G)) y s)))
      (gepi_coker_class G H f (shape G)
         (concat (BG H .carrier) (shape H) y (hom_function G H f (shape G)) g
            (inverse (BG H .carrier) (hom_function G H f (shape G)) y s)))
  ≔ let B ≔ BG H .carrier in
    let W ≔ gepi_test_group G H f rep in
    let BW ≔ BG W .carrier in
    let Φ ≔ hom_function H W (gepi_test_hom G H f rep) in
    let T ≔ rep .carrier in
    let F ≔ hom_function G H f in
    let a0 ≔ shape G in
    let b0 ≔ shape H in
    let x0 ≔ F a0 in
    let P : BW → Type ≔ c ↦ c .fst .fst in
    let Yf : B → Type ≔ t ↦ Id B b0 t → T in
    let t0 ≔ rep .base in
    let cst : (x : B) → Yf x ≔ x _ ↦ t0 in
    let sinv ≔ inverse B x0 y s in
    let act : gepi_coker_set G H f → T → T ≔ c ↦ rep .act c .map in
    let α0 ≔ gepi_test_alpha G H f rep a0 in
    let as ≔ map_path B BW Φ x0 y s in
    let am ≔ map_path B BW Φ y y m in
    let ev ≔ transport BW P (Φ y) (Φ y) γ in
    let scst : Id (Yf y) (transport B Yf x0 y s (cst x0)) (cst y)
      ≔ funext (Id B b0 y) (_ ↦ T) (transport B Yf x0 y s (cst x0)) (cst y)
          (g' ↦ gepi_path_fun_transport B T b0 x0 y s (cst x0) g') in
    let mcst : Id (Yf y) (transport B Yf y y m (cst y)) (cst y)
      ≔ funext (Id B b0 y) (_ ↦ T) (transport B Yf y y m (cst y)) (cst y)
          (g' ↦ gepi_path_fun_transport B T b0 y y m (cst y) g') in
    let ap1 : Id (Yf y) (transport BW P (Φ x0) (Φ y) (concat BW (Φ x0) (Φ x0) (Φ y) α0 as) (cst x0))
        (transport BW P (Φ x0) (Φ y) (concat BW (Φ x0) (Φ y) (Φ y) as γ) (cst x0))
      ≔ refl ((e ↦ transport BW P (Φ x0) (Φ y) e (cst x0)) : Id BW (Φ x0) (Φ y) → Yf y) n1 in
    let E1fun : Id (Yf y) (ev (cst y)) (transport B Yf x0 y s (gepi_test_sigma G H f rep a0 .map (cst x0)))
      ≔ calc
          ev (cst y)
          = ev (transport BW P (Φ x0) (Φ y) as (cst x0))
            by refl ev (inverse (Yf y) (transport B Yf x0 y s (cst x0)) (cst y) scst)
          = transport BW P (Φ x0) (Φ y) (concat BW (Φ x0) (Φ y) (Φ y) as γ) (cst x0)
            by inverse (Yf y) (transport BW P (Φ x0) (Φ y) (concat BW (Φ x0) (Φ y) (Φ y) as γ) (cst x0))
                 (ev (transport BW P (Φ x0) (Φ y) as (cst x0)))
                 (transport_concat BW P (Φ x0) (Φ y) (Φ y) as γ (cst x0))
          = transport BW P (Φ x0) (Φ y) (concat BW (Φ x0) (Φ x0) (Φ y) α0 as) (cst x0)
            by inverse (Yf y) (transport BW P (Φ x0) (Φ y) (concat BW (Φ x0) (Φ x0) (Φ y) α0 as) (cst x0))
                 (transport BW P (Φ x0) (Φ y) (concat BW (Φ x0) (Φ y) (Φ y) as γ) (cst x0)) ap1
          = transport BW P (Φ x0) (Φ y) as (transport BW P (Φ x0) (Φ x0) α0 (cst x0))
            by transport_concat BW P (Φ x0) (Φ x0) (Φ y) α0 as (cst x0) ∎ in
    let E1 : (g' : Id B b0 y) → Id T (ev (cst y) g') (act (gepi_coker_class G H f a0 (concat B b0 y x0 g' sinv)) t0)
      ≔ g' ↦ concat T (ev (cst y) g')
          (transport B Yf x0 y s (gepi_test_sigma G H f rep a0 .map (cst x0)) g')
          (act (gepi_coker_class G H f a0 (concat B b0 y x0 g' sinv)) t0)
          (happly (Id B b0 y) (_ ↦ T) (ev (cst y))
             (transport B Yf x0 y s (gepi_test_sigma G H f rep a0 .map (cst x0))) E1fun g')
          (gepi_path_fun_transport B T b0 x0 y s (gepi_test_sigma G H f rep a0 .map (cst x0)) g') in
    let ap2 : Id (Yf y) (transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) γ am) (cst y))
        (transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) am γ) (cst y))
      ≔ refl ((e ↦ transport BW P (Φ y) (Φ y) e (cst y)) : Id BW (Φ y) (Φ y) → Yf y) n2 in
    let gm ≔ concat B b0 y y g (inverse B y y m) in
    let hp : (u v : Yf y) → Id (Yf y) u v → (x : Id B b0 y) → Id T (u x) (v x)
      ≔ u v e x ↦ happly (Id B b0 y) (_ ↦ T) u v e x in
    let key : Id T (act (gepi_coker_class G H f a0 (concat B b0 y x0 gm sinv)) t0)
        (act (gepi_coker_class G H f a0 (concat B b0 y x0 g sinv)) t0)
      ≔ calc
          act (gepi_coker_class G H f a0 (concat B b0 y x0 gm sinv)) t0
          = ev (cst y) gm
            by inverse T (ev (cst y) gm) (act (gepi_coker_class G H f a0 (concat B b0 y x0 gm sinv)) t0) (E1 gm)
          = transport B Yf y y m (ev (cst y)) g
            by inverse T (transport B Yf y y m (ev (cst y)) g) (ev (cst y) gm)
                 (gepi_path_fun_transport B T b0 y y m (ev (cst y)) g)
          = transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) γ am) (cst y) g
            by inverse T (transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) γ am) (cst y) g)
                 (transport B Yf y y m (ev (cst y)) g)
                 (hp (transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) γ am) (cst y))
                    (transport B Yf y y m (ev (cst y)))
                    (transport_concat BW P (Φ y) (Φ y) (Φ y) γ am (cst y)) g)
          = transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) am γ) (cst y) g
            by hp (transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) γ am) (cst y))
                 (transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) am γ) (cst y)) ap2 g
          = ev (transport B Yf y y m (cst y)) g
            by hp (transport BW P (Φ y) (Φ y) (concat BW (Φ y) (Φ y) (Φ y) am γ) (cst y))
                 (ev (transport B Yf y y m (cst y)))
                 (transport_concat BW P (Φ y) (Φ y) (Φ y) am γ (cst y)) g
          = ev (cst y) g
            by hp (ev (transport B Yf y y m (cst y))) (ev (cst y)) (refl ev mcst) g
          = act (gepi_coker_class G H f a0 (concat B b0 y x0 g sinv)) t0 by E1 g ∎ in
    rep .faithful (gepi_coker_class G H f a0 (concat B b0 y x0 gm sinv))
      (gepi_coker_class G H f a0 (concat B b0 y x0 g sinv)) key

{` Path algebra: (p · q) · q⁻¹ = p. `}
def gepi_concat_cancel_inverse (X : Type) (x y z : X) (p : Id X x y) (q : Id X y z)
  : Id (Id X x y) (concat X x z y (concat X x y z p q) (inverse X y z q)) p
  ≔ calc
      concat X x z y (concat X x y z p q) (inverse X y z q)
      = concat X x y y p (concat X y z y q (inverse X y z q)) by concat_assoc X x y z y p q (inverse X y z q)
      = concat X x y y p (refl y) by refl (concat X x y y p) (concat_inverse_right X y z q)
      = p by concat_p1 X x y p ∎

{` The data of module 931 at k = id_H, for an identification φ = ψ. `}
def gepi_twisted_self (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f))
  (r : Id (GroupHom H (gepi_test_group G H f rep)) (gepi_test_hom G H f rep) (gepi_test_hom_twisted G H f rep))
  (g2 : Id (BG H .carrier) (shape H) (hom_function G H f (shape G)))
  : Id (gepi_coker_set G H f)
      (gepi_coker_class G H f (shape G)
         (concat (BG H .carrier) (shape H) (shape H) (hom_function G H f (shape G)) (refl (shape H))
            (inverse (BG H .carrier) (hom_function G H f (shape G)) (shape H)
               (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) (shape H)
                  (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)) (refl (shape H))))))
      (gepi_coker_class G H f (shape G) g2)
  ≔ let B ≔ BG H .carrier in
    let W ≔ gepi_test_group G H f rep in
    let φ ≔ gepi_test_hom G H f rep in
    let Φ ≔ hom_function H W φ in
    let x0 ≔ hom_function G H f (shape G) in
    let b0 ≔ shape H in
    let idH ≔ group_hom_id H in
    let r' : Id (GroupHom H W) (group_hom_compose H H W idH φ) (group_hom_compose H H W idH (gepi_test_hom_twisted G H f rep))
      ≔ refl ((u ↦ group_hom_compose H H W idH u) : GroupHom H W → GroupHom H W) r in
    let w ≔ gepi_twisted_commute G H W f Φ (hom_point H W φ) (gepi_test_alpha G H f rep) H idH r' in
    let s ≔ concat B x0 b0 b0 (inverse B b0 x0 (hom_point G H f)) (refl b0) in
    let sinv ≔ inverse B x0 b0 s in
    let g ≔ concat B b0 x0 b0 g2 s in
    let c ≔ gepi_core G H f rep b0 s (w .fst) (w .snd .fst) g (w .snd .snd g) g in
    calc
      gepi_coker_class G H f (shape G) (concat B b0 b0 x0 (refl b0) sinv)
      = gepi_coker_class G H f (shape G) (concat B b0 b0 x0 (concat B b0 b0 b0 g (inverse B b0 b0 g)) sinv)
        by refl ((u ↦ gepi_coker_class G H f (shape G) (concat B b0 b0 x0 u sinv)) : Id B b0 b0 → gepi_coker_set G H f)
             (inverse (Id B b0 b0) (concat B b0 b0 b0 g (inverse B b0 b0 g)) (refl b0) (concat_inverse_right B b0 b0 g))
      = gepi_coker_class G H f (shape G) (concat B b0 b0 x0 g sinv) by c
      = gepi_coker_class G H f (shape G) g2
        by refl (gepi_coker_class G H f (shape G)) (gepi_concat_cancel_inverse B b0 x0 b0 g2 s) ∎

{` The test representation for f. `}
def gepi_default_rep (G H : Group) (f : GroupHom G H) : GepiPermRep (gepi_coker_set G H f)
  ≔ gepi_perm_rep (gepi_coker_set G H f) (set_trunc_set (gepi_coker_fiber G H f))

{` If φ = ψ then X(sh_H) is contractible. `}
def gepi_twisted_equal_coker_contractible (G H : Group) (f : GroupHom G H) (rep : GepiPermRep (gepi_coker_set G H f))
  (r : Id (GroupHom H (gepi_test_group G H f rep)) (gepi_test_hom G H f rep) (gepi_test_hom_twisted G H f rep))
  : BookIsContr (gepi_coker_set G H f)
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    let S ≔ gepi_coker_set G H f in
    let Fb ≔ gepi_coker_fiber G H f in
    let b0 ≔ shape H in
    let x0 ≔ F (shape G) in
    let center ≔ gepi_coker_class G H f (shape G)
        (concat B b0 b0 x0 (refl b0)
           (inverse B x0 b0 (concat B x0 b0 b0 (inverse B b0 x0 (hom_point G H f)) (refl b0)))) in
    let on_points : (z : A) (g : Id B b0 (F z)) → Id S center (gepi_coker_class G H f z g)
      ≔ connected_based_elim native_truncation A (bg_connected G) (shape G)
          (z ↦ (g : Id B b0 (F z)) → Id S center (gepi_coker_class G H f z g))
          (z ↦ pi_prop (Id B b0 (F z)) (g ↦ Id S center (gepi_coker_class G H f z g))
             (g ↦ set_trunc_set Fb center (gepi_coker_class G H f z g)))
          (g2 ↦ gepi_twisted_self G H f rep r g2) in
    (center,
     x ↦ quotient_prop_induction Fb (mere_path_relation Fb) (x ↦ Id S center x)
       (x ↦ set_trunc_set Fb center x) (u ↦ on_points (u .fst) (u .snd)) x)

{` lem:epi-surj, (1') ⇒ (3'): an epimorphism has connected fibers. The test
   object is the group W = Σ_{Y(sh_H)} built from f. `}
def gepi_epi_coker_contractible (G H : Group) (f : GroupHom G H) (e : IsEpi (GroupCat .wild) G H f)
  : BookIsContr (gepi_coker_set G H f)
  ≔ let rep ≔ gepi_default_rep G H f in
    let W ≔ gepi_test_group G H f rep in
    gepi_twisted_equal_coker_contractible G H f rep
      (embedding_reflects_paths (GroupHom H W) (GroupHom G W) (k ↦ GroupCat .wild .comp G H W k f) (e W)
         (gepi_test_hom G H f rep) (gepi_test_hom_twisted G H f rep) (gepi_test_homs_agree G H f rep))

def gepi_epi_connected_fibers (G H : Group) (f : GroupHom G H) (e : IsEpi (GroupCat .wild) G H f)
  : ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f)
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    connected_based_elim native_truncation B (bg_connected H) (shape H)
      (w ↦ Connected (BookFiber A B F w)) (w ↦ connected_isprop (BookFiber A B F w))
      (contractible_set_trunc_connected (gepi_coker_fiber G H f) (gepi_epi_coker_contractible G H f e))

{` lem:epi-surj, (1') ⇒ (2'). `}
def gepi_epi_usym_surjective (G H : Group) (f : GroupHom G H) (e : IsEpi (GroupCat .wild) G H f)
  : Surjective (USym G) (USym H) (usym_hom G H f)
  ≔ gepi_connected_fibers_usym_surjective G H f (gepi_epi_connected_fibers G H f e)

{` lem:epi-surj: the three propositions are equivalent. `}
def gepi_epi_connected_fibers_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsEpi (GroupCat .wild) G H f) (ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ iff_equiv (IsEpi (GroupCat .wild) G H f) (ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
      (is_epi_prop (GroupCat .wild) G H f) (gepi_connected_fibers_prop G H f)
      (gepi_epi_connected_fibers G H f) (gepi_connected_fibers_epi G H f)

def gepi_epi_usym_surjective_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsEpi (GroupCat .wild) G H f) (Surjective (USym G) (USym H) (usym_hom G H f))
  ≔ iff_equiv (IsEpi (GroupCat .wild) G H f) (Surjective (USym G) (USym H) (usym_hom G H f))
      (is_epi_prop (GroupCat .wild) G H f) (surjective_property_prop (USym G) (USym H) (usym_hom G H f))
      (gepi_epi_usym_surjective G H f) (gepi_usym_surjective_epi G H f)

{` "(or: is 0-connected)": (3') is the book's 0-connectedness of Bf
   (ZeroConnectedMap, module 105: all set-truncated fibers contractible). `}
def gepi_epi_zero_connected (G H : Group) (f : GroupHom G H) (e : IsEpi (GroupCat .wild) G H f)
  : ZeroConnectedMap (BG G .carrier) (BG H .carrier) (hom_function G H f)
  ≔ connected_fibers_zero_map (BG G .carrier) (BG H .carrier) (hom_function G H f) (gepi_epi_connected_fibers G H f e)
