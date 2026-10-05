export "930-epi-surj-easy"

{` Chapter 9 (subgroups.tex), helper for lem:epi-surj (line 161) and
   con:monos-are-equalizers (line 204): two homomorphisms H → W with the
   same classifying function Φ : BH → BW and different pointing paths, as in
   the book's draft implementation of con:monos-are-equalizers ("two
   homomorphisms φ, ψ with the same classifying map but with different
   pointing paths").

   Given f : Hom(G, H), Φ, a pointing p0 : sh_W = Φ(sh_H) and a section
   α : (z : BG) → Φ(Bf z) = Φ(Bf z), the twisted pointing is
   p0 · ap_Φ(Bf_pt) · α(sh_G) · ap_Φ(Bf_pt)⁻¹ (concatenation order). Then
   (i) the two homomorphisms agree after precomposition with f (α is the
       pointed homotopy), for every section α;
   (ii) if they agree after precomposition with k : Hom(K, H), then α(sh_G)
       transported to Φ(Bk sh_K) commutes with ap_Φ(ap_Bk κ) for all
       κ : USym K (the value at the shape of a pointed homotopy between two
       homomorphisms with the same classifying function commutes with all
       ap's, by naturality). `}

def GepiLoopsCommute (X : Type) (x : X) (l m : Id X x x) : Type
  ≔ Id (Id X x x) (concat X x x x l m) (concat X x x x m l)

{` An identification of mkhom(Ψ, p) and mkhom(Ψ, p') gives a loop γ at
   Ψ(sh_K) with p · γ = p' that commutes with ap_Ψ(κ) for every κ. `}
def gepi_same_function_section (K W : Group) (Ψ : BG K .carrier → BG W .carrier)
  (p p' : Id (BG W .carrier) (shape W) (Ψ (shape K)))
  (r : Id (GroupHom K W) (mkhom K W (Ψ, p)) (mkhom K W (Ψ, p')))
  : Σ (Id (BG W .carrier) (Ψ (shape K)) (Ψ (shape K))) (γ ↦ Product
      (Id (Id (BG W .carrier) (shape W) (Ψ (shape K)))
        (concat (BG W .carrier) (shape W) (Ψ (shape K)) (Ψ (shape K)) p γ) p')
      ((κ : USym K) → GepiLoopsCommute (BG W .carrier) (Ψ (shape K)) γ
         (map_path (BG K .carrier) (BG W .carrier) Ψ (shape K) (shape K) κ)))
  ≔ let C ≔ BG W .carrier in
    let k0 ≔ shape K in
    let h ≔ group_hom_path_equiv K W (mkhom K W (Ψ, p)) (mkhom K W (Ψ, p')) .map r in
    (h .fst k0,
     (h .snd,
      κ ↦ inverse (Id C (Ψ k0) (Ψ k0))
        (concat C (Ψ k0) (Ψ k0) (Ψ k0) (map_path (BG K .carrier) C Ψ k0 k0 κ) (h .fst k0))
        (concat C (Ψ k0) (Ψ k0) (Ψ k0) (h .fst k0) (map_path (BG K .carrier) C Ψ k0 k0 κ))
        (naturality (BG K .carrier) C Ψ Ψ (h .fst) k0 k0 κ)))

{` The twisted pointing p0 · (a · α(sh_G) · a⁻¹), a = ap_Φ(Bf_pt). `}
def gepi_twisted_point (G H W : Group) (f : GroupHom G H) (Φ : BG H .carrier → BG W .carrier)
  (p0 : Id (BG W .carrier) (shape W) (Φ (shape H)))
  (α : (z : BG G .carrier) → Id (BG W .carrier) (Φ (hom_function G H f z)) (Φ (hom_function G H f z)))
  : Id (BG W .carrier) (shape W) (Φ (shape H))
  ≔ let C ≔ BG W .carrier in
    let F ≔ hom_function G H f in
    concat C (shape W) (Φ (shape H)) (Φ (shape H)) p0
      (pointed_loop_conjugate C (Φ (shape H)) (Φ (F (shape G)))
        (map_path (BG H .carrier) C Φ (shape H) (F (shape G)) (hom_point G H f)) (α (shape G)))

{` Path algebra: (a · l · a⁻¹) · a = a · l. `}
def gepi_conjugate_concat (X : Type) (x y : X) (a : Id X x y) (l : Id X y y)
  : Id (Id X x y) (concat X x x y (pointed_loop_conjugate X x y a l) a) (concat X x y y a l)
  ≔ calc
      concat X x x y (concat X x y x a (concat X y y x l (inverse X x y a))) a
      = concat X x y y a (concat X y x y (concat X y y x l (inverse X x y a)) a)
        by concat_assoc X x y x y a (concat X y y x l (inverse X x y a)) a
      = concat X x y y a (concat X y y y l (concat X y x y (inverse X x y a) a))
        by refl (concat X x y y a) (concat_assoc X y y x y l (inverse X x y a) a)
      = concat X x y y a (concat X y y y l (refl y))
        by refl ((t ↦ concat X x y y a (concat X y y y l t)) : Id X y y → Id X x y) (concat_inverse_left X x y a)
      = concat X x y y a l by refl (concat X x y y a) (concat_p1 X y y l) ∎

{` (i): the two homomorphisms agree after precomposition with f. `}
def gepi_twisted_compose_path (G H W : Group) (f : GroupHom G H) (Φ : BG H .carrier → BG W .carrier)
  (p0 : Id (BG W .carrier) (shape W) (Φ (shape H)))
  (α : (z : BG G .carrier) → Id (BG W .carrier) (Φ (hom_function G H f z)) (Φ (hom_function G H f z)))
  : Id (GroupHom G W) (group_hom_compose G H W f (mkhom H W (Φ, p0)))
      (group_hom_compose G H W f (mkhom H W (Φ, gepi_twisted_point G H W f Φ p0 α)))
  ≔ let C ≔ BG W .carrier in
    let F ≔ hom_function G H f in
    let a0 ≔ shape G in
    let b0 ≔ shape H in
    let c0 ≔ shape W in
    let a ≔ map_path (BG H .carrier) C Φ b0 (F a0) (hom_point G H f) in
    let l ≔ pointed_loop_conjugate C (Φ b0) (Φ (F a0)) a (α a0) in
    let u ≔ group_hom_compose G H W f (mkhom H W (Φ, p0)) in
    let v ≔ group_hom_compose G H W f (mkhom H W (Φ, gepi_twisted_point G H W f Φ p0 α)) in
    equiv_inverse_map (Id (GroupHom G W) u v) (PointedHomotopy (BG G) (BG W) (hom_B G W u) (hom_B G W v))
      (group_hom_path_equiv G W u v)
      (α,
       calc
         concat C c0 (Φ (F a0)) (Φ (F a0)) (concat C c0 (Φ b0) (Φ (F a0)) p0 a) (α a0)
         = concat C c0 (Φ b0) (Φ (F a0)) p0 (concat C (Φ b0) (Φ (F a0)) (Φ (F a0)) a (α a0))
           by concat_assoc C c0 (Φ b0) (Φ (F a0)) (Φ (F a0)) p0 a (α a0)
         = concat C c0 (Φ b0) (Φ (F a0)) p0 (concat C (Φ b0) (Φ b0) (Φ (F a0)) l a)
           by refl (concat C c0 (Φ b0) (Φ (F a0)) p0)
                (inverse (Id C (Φ b0) (Φ (F a0))) (concat C (Φ b0) (Φ b0) (Φ (F a0)) l a)
                  (concat C (Φ b0) (Φ (F a0)) (Φ (F a0)) a (α a0)) (gepi_conjugate_concat C (Φ b0) (Φ (F a0)) a (α a0)))
         = concat C c0 (Φ b0) (Φ (F a0)) (concat C c0 (Φ b0) (Φ b0) p0 l) a
           by inverse (Id C c0 (Φ (F a0))) (concat C c0 (Φ b0) (Φ (F a0)) (concat C c0 (Φ b0) (Φ b0) p0 l) a)
                (concat C c0 (Φ b0) (Φ (F a0)) p0 (concat C (Φ b0) (Φ b0) (Φ (F a0)) l a))
                (concat_assoc C c0 (Φ b0) (Φ b0) (Φ (F a0)) p0 l a) ∎)

{` Path algebra for (ii): from (p0 · d) · γ = (p0 · (a · α0 · a⁻¹)) · d
   conclude α0 · (a⁻¹ · d) = (a⁻¹ · d) · γ. `}
def gepi_twist_algebra (X : Type) (c0 y0 x0 v0 : X) (p0 : Id X c0 y0) (a : Id X y0 x0) (d : Id X y0 v0)
  (α0 : Id X x0 x0) (γ : Id X v0 v0)
  (e1 : Id (Id X c0 v0) (concat X c0 v0 v0 (concat X c0 y0 v0 p0 d) γ)
          (concat X c0 y0 v0 (concat X c0 y0 y0 p0 (pointed_loop_conjugate X y0 x0 a α0)) d))
  : Id (Id X x0 v0) (concat X x0 x0 v0 α0 (concat X x0 y0 v0 (inverse X y0 x0 a) d))
      (concat X x0 v0 v0 (concat X x0 y0 v0 (inverse X y0 x0 a) d) γ)
  ≔ let l ≔ pointed_loop_conjugate X y0 x0 a α0 in
    let ai ≔ inverse X y0 x0 a in
    let E2 : Id (Id X y0 v0) (concat X y0 v0 v0 d γ) (concat X y0 y0 v0 l d)
      ≔ concat_cancel_left X c0 y0 v0 p0 (concat X y0 v0 v0 d γ) (concat X y0 y0 v0 l d)
          (calc
            concat X c0 y0 v0 p0 (concat X y0 v0 v0 d γ)
            = concat X c0 v0 v0 (concat X c0 y0 v0 p0 d) γ
              by inverse (Id X c0 v0) (concat X c0 v0 v0 (concat X c0 y0 v0 p0 d) γ)
                   (concat X c0 y0 v0 p0 (concat X y0 v0 v0 d γ)) (concat_assoc X c0 y0 v0 v0 p0 d γ)
            = concat X c0 y0 v0 (concat X c0 y0 y0 p0 l) d by e1
            = concat X c0 y0 v0 p0 (concat X y0 y0 v0 l d) by concat_assoc X c0 y0 y0 v0 p0 l d ∎) in
    calc
      concat X x0 x0 v0 α0 (concat X x0 y0 v0 ai d)
      = concat X x0 y0 v0 (concat X x0 x0 y0 α0 ai) d
        by inverse (Id X x0 v0) (concat X x0 y0 v0 (concat X x0 x0 y0 α0 ai) d)
             (concat X x0 x0 v0 α0 (concat X x0 y0 v0 ai d)) (concat_assoc X x0 x0 y0 v0 α0 ai d)
      = concat X x0 y0 v0 (concat X x0 y0 y0 ai l) d
        by refl ((t ↦ concat X x0 y0 v0 t d) : Id X x0 y0 → Id X x0 v0)
             (inverse (Id X x0 y0) (concat X x0 y0 y0 ai l) (concat X x0 x0 y0 α0 ai)
               (concat_left_inverse_cancel X y0 x0 y0 a (concat X x0 x0 y0 α0 ai)))
      = concat X x0 y0 v0 ai (concat X y0 y0 v0 l d) by concat_assoc X x0 y0 y0 v0 ai l d
      = concat X x0 y0 v0 ai (concat X y0 v0 v0 d γ)
        by refl (concat X x0 y0 v0 ai) (inverse (Id X y0 v0) (concat X y0 v0 v0 d γ) (concat X y0 y0 v0 l d) E2)
      = concat X x0 v0 v0 (concat X x0 y0 v0 ai d) γ
        by inverse (Id X x0 v0) (concat X x0 v0 v0 (concat X x0 y0 v0 ai d) γ)
             (concat X x0 y0 v0 ai (concat X y0 v0 v0 d γ)) (concat_assoc X x0 y0 v0 v0 ai d γ) ∎

{` (ii): if the two homomorphisms agree after precomposition with
   k : Hom(K, H), there is a loop γ at Φ(Bk sh_K) with
   α(sh_G) · ap_Φ(s) = ap_Φ(s) · γ for s ≔ Bf_pt⁻¹ · Bk_pt : Bf(sh_G) = Bk(sh_K),
   and γ commutes with ap_Φ(ap_Bk κ) for every κ : USym K. `}
def gepi_twisted_commute (G H W : Group) (f : GroupHom G H) (Φ : BG H .carrier → BG W .carrier)
  (p0 : Id (BG W .carrier) (shape W) (Φ (shape H)))
  (α : (z : BG G .carrier) → Id (BG W .carrier) (Φ (hom_function G H f z)) (Φ (hom_function G H f z)))
  (K : Group) (k : GroupHom K H)
  (r : Id (GroupHom K W) (group_hom_compose K H W k (mkhom H W (Φ, p0)))
         (group_hom_compose K H W k (mkhom H W (Φ, gepi_twisted_point G H W f Φ p0 α))))
  : Σ (Id (BG W .carrier) (Φ (hom_function K H k (shape K))) (Φ (hom_function K H k (shape K)))) (γ ↦ Product
      (Id (Id (BG W .carrier) (Φ (hom_function G H f (shape G))) (Φ (hom_function K H k (shape K))))
        (concat (BG W .carrier) (Φ (hom_function G H f (shape G))) (Φ (hom_function G H f (shape G)))
           (Φ (hom_function K H k (shape K))) (α (shape G))
           (map_path (BG H .carrier) (BG W .carrier) Φ (hom_function G H f (shape G)) (hom_function K H k (shape K))
             (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) (hom_function K H k (shape K))
               (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)) (hom_point K H k))))
        (concat (BG W .carrier) (Φ (hom_function G H f (shape G))) (Φ (hom_function K H k (shape K)))
           (Φ (hom_function K H k (shape K)))
           (map_path (BG H .carrier) (BG W .carrier) Φ (hom_function G H f (shape G)) (hom_function K H k (shape K))
             (concat (BG H .carrier) (hom_function G H f (shape G)) (shape H) (hom_function K H k (shape K))
               (inverse (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f)) (hom_point K H k)))
           γ))
      ((κ : USym K) → GepiLoopsCommute (BG W .carrier) (Φ (hom_function K H k (shape K))) γ
         (map_path (BG H .carrier) (BG W .carrier) Φ (hom_function K H k (shape K)) (hom_function K H k (shape K))
           (map_path (BG K .carrier) (BG H .carrier) (hom_function K H k) (shape K) (shape K) κ))))
  ≔ let B ≔ BG H .carrier in
    let C ≔ BG W .carrier in
    let F ≔ hom_function G H f in
    let Bk ≔ hom_function K H k in
    let a0 ≔ shape G in
    let b0 ≔ shape H in
    let c0 ≔ shape W in
    let k0 ≔ shape K in
    let fp ≔ hom_point G H f in
    let kp ≔ hom_point K H k in
    let a ≔ map_path B C Φ b0 (F a0) fp in
    let d ≔ map_path B C Φ b0 (Bk k0) kp in
    let tw ≔ gepi_twisted_point G H W f Φ p0 α in
    let w ≔ gepi_same_function_section K W (y ↦ Φ (Bk y)) (concat C c0 (Φ b0) (Φ (Bk k0)) p0 d)
        (concat C c0 (Φ b0) (Φ (Bk k0)) tw d) r in
    let γ ≔ w .fst in
    let s ≔ concat B (F a0) b0 (Bk k0) (inverse B b0 (F a0) fp) kp in
    let t ≔ map_path B C Φ (F a0) (Bk k0) s in
    let t' ≔ concat C (Φ (F a0)) (Φ b0) (Φ (Bk k0)) (inverse C (Φ b0) (Φ (F a0)) a) d in
    let tt : Id (Id C (Φ (F a0)) (Φ (Bk k0))) t t'
      ≔ calc
          t
          = concat C (Φ (F a0)) (Φ b0) (Φ (Bk k0)) (map_path B C Φ (F a0) b0 (inverse B b0 (F a0) fp)) d
            by map_path_concat B C Φ (F a0) b0 (Bk k0) (inverse B b0 (F a0) fp) kp
          = t' by refl ((u ↦ concat C (Φ (F a0)) (Φ b0) (Φ (Bk k0)) u d) : Id C (Φ (F a0)) (Φ b0) → Id C (Φ (F a0)) (Φ (Bk k0)))
                    (map_path_inverse B C Φ b0 (F a0) fp) ∎ in
    let alg ≔ gepi_twist_algebra C c0 (Φ b0) (Φ (F a0)) (Φ (Bk k0)) p0 a d (α a0) γ (w .snd .fst) in
    (γ,
     (calc
        concat C (Φ (F a0)) (Φ (F a0)) (Φ (Bk k0)) (α a0) t
        = concat C (Φ (F a0)) (Φ (F a0)) (Φ (Bk k0)) (α a0) t' by refl (concat C (Φ (F a0)) (Φ (F a0)) (Φ (Bk k0)) (α a0)) tt
        = concat C (Φ (F a0)) (Φ (Bk k0)) (Φ (Bk k0)) t' γ by alg
        = concat C (Φ (F a0)) (Φ (Bk k0)) (Φ (Bk k0)) t γ
          by refl ((u ↦ concat C (Φ (F a0)) (Φ (Bk k0)) (Φ (Bk k0)) u γ) : Id C (Φ (F a0)) (Φ (Bk k0)) → Id C (Φ (F a0)) (Φ (Bk k0)))
               (inverse (Id C (Φ (F a0)) (Φ (Bk k0))) t t' tt) ∎,
      w .snd .snd))
