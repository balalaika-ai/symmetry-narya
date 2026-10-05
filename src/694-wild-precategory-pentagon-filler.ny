export "693-wild-precategory-pentagon"

{` Chapter 6, xca:wildprecat-of-wildprecats, the adventurous part ("define
   the fillers for the pentagon diagram for four composable wild
   functors"), continued from module 693: the pentagon in
   WildPrecatWildYoneda for four composable wild functors F, G, H, K, with
   no hypothesis on C_4.

   The development is generic in an associator α with ap Φ α = β
   (YwfAssocImage), so that α is never unfolded. With P_0, ..., P_4 the
   vertices and a_1, ..., a_5 the edges of the pentagon, r_i is a path from
   the strict composite Φ K ∘ Φ H ∘ Φ G ∘ Φ F to Φ P_i, and each edge
   satisfies ap Φ a_k = r_i⁻¹ · r_j (ywf_edge1 ... ywf_edge5; edge 5 uses
   interchange to compare the two ways from the strict composite to
   Φ ((K ∘ H) ∘ (G ∘ F))). ywf_pentagon_reflect (module 693) concludes. `}

def ywf_P0 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : WildFunctor C0 C4
  ≔ functor_compose C0 C3 C4 K (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))

def ywf_P1 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : WildFunctor C0 C4
  ≔ functor_compose C0 C3 C4 K (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)

def ywf_P2 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : WildFunctor C0 C4
  ≔ functor_compose C0 C1 C4 (functor_compose C1 C3 C4 K (functor_compose C1 C2 C3 H G)) F

def ywf_P3 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : WildFunctor C0 C4
  ≔ functor_compose C0 C1 C4 (functor_compose C1 C2 C4 (functor_compose C2 C3 C4 K H) G) F

def ywf_P4 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : WildFunctor C0 C4
  ≔ functor_compose C0 C2 C4 (functor_compose C2 C3 C4 K H) (functor_compose C0 C1 C2 G F)

def ywf_a1 (alpha : YwfAssoc)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (WildFunctor C0 C4) (ywf_P0 C0 C1 C2 C3 C4 F G H K) (ywf_P1 C0 C1 C2 C3 C4 F G H K)
  ≔ cat_whisker_left (WildPrecatWildWith alpha) C0 C3 C4 K
      (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))
      (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)
      (alpha C0 C1 C2 C3 F G H)

def ywf_a2 (alpha : YwfAssoc)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (WildFunctor C0 C4) (ywf_P1 C0 C1 C2 C3 C4 F G H K) (ywf_P2 C0 C1 C2 C3 C4 F G H K)
  ≔ alpha C0 C1 C3 C4 F (functor_compose C1 C2 C3 H G) K

def ywf_a3 (alpha : YwfAssoc)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (WildFunctor C0 C4) (ywf_P2 C0 C1 C2 C3 C4 F G H K) (ywf_P3 C0 C1 C2 C3 C4 F G H K)
  ≔ cat_whisker_right (WildPrecatWildWith alpha) C0 C1 C4
      (functor_compose C1 C3 C4 K (functor_compose C1 C2 C3 H G))
      (functor_compose C1 C2 C4 (functor_compose C2 C3 C4 K H) G) F
      (alpha C1 C2 C3 C4 G H K)

def ywf_a4 (alpha : YwfAssoc)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (WildFunctor C0 C4) (ywf_P0 C0 C1 C2 C3 C4 F G H K) (ywf_P4 C0 C1 C2 C3 C4 F G H K)
  ≔ alpha C0 C2 C3 C4 (functor_compose C0 C1 C2 G F) H K

def ywf_a5 (alpha : YwfAssoc)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (WildFunctor C0 C4) (ywf_P4 C0 C1 C2 C3 C4 F G H K) (ywf_P3 C0 C1 C2 C3 C4 F G H K)
  ≔ alpha C0 C1 C2 C4 F G (functor_compose C2 C3 C4 K H)

{` The strict composite Φ K ∘ Φ H ∘ Φ G ∘ Φ F (all bracketings agree). `}
def ywf_word (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : YonedaWildFunctor C0 C4
  ≔ yoneda_wild_functor_compose C0 C3 C4 (wild_functor_yoneda C3 C4 K)
      (yoneda_wild_functor_compose C0 C2 C3 (wild_functor_yoneda C2 C3 H)
        (yoneda_wild_functor_compose C0 C1 C2 (wild_functor_yoneda C1 C2 G) (wild_functor_yoneda C0 C1 F)))

def ywf_r0 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K))
  ≔ concat (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K)
      (yoneda_wild_functor_compose C0 C3 C4 (wild_functor_yoneda C3 C4 K)
        (wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))))
      (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K))
      (refl (yoneda_wild_functor_compose C0 C3 C4 (wild_functor_yoneda C3 C4 K)) (ywf_rho_left C0 C1 C2 C3 F G H))
      (wild_functor_yoneda_compose C0 C3 C4 K (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F)))

def ywf_r1 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P1 C0 C1 C2 C3 C4 F G H K))
  ≔ concat (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K)
      (yoneda_wild_functor_compose C0 C3 C4 (wild_functor_yoneda C3 C4 K)
        (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)))
      (wild_functor_yoneda C0 C4 (ywf_P1 C0 C1 C2 C3 C4 F G H K))
      (refl (yoneda_wild_functor_compose C0 C3 C4 (wild_functor_yoneda C3 C4 K)) (ywf_rho_right C0 C1 C2 C3 F G H))
      (wild_functor_yoneda_compose C0 C3 C4 K (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F))

def ywf_r2 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P2 C0 C1 C2 C3 C4 F G H K))
  ≔ let yF ≔ wild_functor_yoneda C0 C1 F in
    concat (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K)
      (yoneda_wild_functor_compose C0 C1 C4
        (wild_functor_yoneda C1 C4 (functor_compose C1 C3 C4 K (functor_compose C1 C2 C3 H G))) yF)
      (wild_functor_yoneda C0 C4 (ywf_P2 C0 C1 C2 C3 C4 F G H K))
      (refl ((x ↦ yoneda_wild_functor_compose C0 C1 C4 x yF) : YonedaWildFunctor C1 C4 → YonedaWildFunctor C0 C4)
        (ywf_rho_left C1 C2 C3 C4 G H K))
      (wild_functor_yoneda_compose C0 C1 C4 (functor_compose C1 C3 C4 K (functor_compose C1 C2 C3 H G)) F)

def ywf_r3 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P3 C0 C1 C2 C3 C4 F G H K))
  ≔ let yF ≔ wild_functor_yoneda C0 C1 F in
    concat (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K)
      (yoneda_wild_functor_compose C0 C1 C4
        (wild_functor_yoneda C1 C4 (functor_compose C1 C2 C4 (functor_compose C2 C3 C4 K H) G)) yF)
      (wild_functor_yoneda C0 C4 (ywf_P3 C0 C1 C2 C3 C4 F G H K))
      (refl ((x ↦ yoneda_wild_functor_compose C0 C1 C4 x yF) : YonedaWildFunctor C1 C4 → YonedaWildFunctor C0 C4)
        (ywf_rho_right C1 C2 C3 C4 G H K))
      (wild_functor_yoneda_compose C0 C1 C4 (functor_compose C1 C2 C4 (functor_compose C2 C3 C4 K H) G) F)

def ywf_r4 (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4) : Id (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P4 C0 C1 C2 C3 C4 F G H K))
  ≔ let ykh ≔ yoneda_wild_functor_compose C2 C3 C4 (wild_functor_yoneda C3 C4 K) (wild_functor_yoneda C2 C3 H) in
    concat (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K)
      (yoneda_wild_functor_compose C0 C2 C4 ykh (wild_functor_yoneda C0 C2 (functor_compose C0 C1 C2 G F)))
      (wild_functor_yoneda C0 C4 (ywf_P4 C0 C1 C2 C3 C4 F G H K))
      (refl (yoneda_wild_functor_compose C0 C2 C4 ykh) (wild_functor_yoneda_compose C0 C1 C2 G F))
      (ywf_rho_right C0 C2 C3 C4 (functor_compose C0 C1 C2 G F) H K)

{` Edge 1: K whiskered with α at (F, G, H). `}
def ywf_edge1 (alpha : YwfAssoc) (img : YwfAssocImage alpha)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4)
  : Id (Id (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K)) (wild_functor_yoneda C0 C4 (ywf_P1 C0 C1 C2 C3 C4 F G H K)))
      (refl (wild_functor_yoneda C0 C4) (ywf_a1 alpha C0 C1 C2 C3 C4 F G H K))
      (concat (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K)) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P1 C0 C1 C2 C3 C4 F G H K))
        (inverse (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K)) (ywf_r0 C0 C1 C2 C3 C4 F G H K)) (ywf_r1 C0 C1 C2 C3 C4 F G H K))
  ≔ let T ≔ YonedaWildFunctor C0 C4 in
    let Phi ≔ wild_functor_yoneda C0 C4 in
    let yF ≔ wild_functor_yoneda C0 C1 F in
    let yG ≔ wild_functor_yoneda C1 C2 G in
    let yH ≔ wild_functor_yoneda C2 C3 H in
    let yK ≔ wild_functor_yoneda C3 C4 K in
    let gf ≔ functor_compose C0 C1 C2 G F in
    let hg ≔ functor_compose C1 C2 C3 H G in
    let yc04 ≔ yoneda_wild_functor_compose C0 C3 C4 yK in
    let mu_kx : (X : WildFunctor C0 C3) → Id T (yc04 (wild_functor_yoneda C0 C3 X)) (Phi (functor_compose C0 C3 C4 K X))
      ≔ X ↦ wild_functor_yoneda_compose C0 C3 C4 K X in
    let ygf ≔ yoneda_wild_functor_compose C0 C1 C2 yG yF in
    ywf_whisker_edge (WildFunctor C0 C3) (YonedaWildFunctor C0 C3) T (wild_functor_yoneda C0 C3) yc04
      (X ↦ Phi (functor_compose C0 C3 C4 K X)) mu_kx (functor_compose C0 C2 C3 H gf)
      (functor_compose C0 C1 C3 hg F) (alpha C0 C1 C2 C3 F G H)
      (yoneda_wild_functor_compose C0 C2 C3 yH ygf)
      (ywf_rho_left C0 C1 C2 C3 F G H) (ywf_rho_right C0 C1 C2 C3 F G H)
      (img C0 C1 C2 C3 F G H)

{` Edge 3: α at (G, H, K) whiskered with F. `}
def ywf_edge3 (alpha : YwfAssoc) (img : YwfAssocImage alpha)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4)
  : Id (Id (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P2 C0 C1 C2 C3 C4 F G H K)) (wild_functor_yoneda C0 C4 (ywf_P3 C0 C1 C2 C3 C4 F G H K)))
      (refl (wild_functor_yoneda C0 C4) (ywf_a3 alpha C0 C1 C2 C3 C4 F G H K))
      (concat (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P2 C0 C1 C2 C3 C4 F G H K)) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P3 C0 C1 C2 C3 C4 F G H K))
        (inverse (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P2 C0 C1 C2 C3 C4 F G H K)) (ywf_r2 C0 C1 C2 C3 C4 F G H K)) (ywf_r3 C0 C1 C2 C3 C4 F G H K))
  ≔ let T ≔ YonedaWildFunctor C0 C4 in
    let Phi ≔ wild_functor_yoneda C0 C4 in
    let yF ≔ wild_functor_yoneda C0 C1 F in
    let yG ≔ wild_functor_yoneda C1 C2 G in
    let yH ≔ wild_functor_yoneda C2 C3 H in
    let yK ≔ wild_functor_yoneda C3 C4 K in
    let hg ≔ functor_compose C1 C2 C3 H G in
    let kh ≔ functor_compose C2 C3 C4 K H in
    let ycF : YonedaWildFunctor C1 C4 → T ≔ x ↦ yoneda_wild_functor_compose C0 C1 C4 x yF in
    let mu_xf : (X : WildFunctor C1 C4) → Id T (ycF (wild_functor_yoneda C1 C4 X)) (Phi (functor_compose C0 C1 C4 X F))
      ≔ X ↦ wild_functor_yoneda_compose C0 C1 C4 X F in
    ywf_whisker_edge (WildFunctor C1 C4) (YonedaWildFunctor C1 C4) T (wild_functor_yoneda C1 C4) ycF
      (X ↦ Phi (functor_compose C0 C1 C4 X F)) mu_xf (functor_compose C1 C3 C4 K hg)
      (functor_compose C1 C2 C4 kh G) (alpha C1 C2 C3 C4 G H K)
      (yoneda_wild_functor_compose C1 C3 C4 yK (yoneda_wild_functor_compose C1 C2 C3 yH yG))
      (ywf_rho_left C1 C2 C3 C4 G H K) (ywf_rho_right C1 C2 C3 C4 G H K)
      (img C1 C2 C3 C4 G H K)

{` Edge 2: α at (F, H ∘ G, K). `}
def ywf_edge2 (alpha : YwfAssoc) (img : YwfAssocImage alpha)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4)
  : Id (Id (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P1 C0 C1 C2 C3 C4 F G H K)) (wild_functor_yoneda C0 C4 (ywf_P2 C0 C1 C2 C3 C4 F G H K)))
      (refl (wild_functor_yoneda C0 C4) (ywf_a2 alpha C0 C1 C2 C3 C4 F G H K))
      (concat (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P1 C0 C1 C2 C3 C4 F G H K)) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P2 C0 C1 C2 C3 C4 F G H K))
        (inverse (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P1 C0 C1 C2 C3 C4 F G H K)) (ywf_r1 C0 C1 C2 C3 C4 F G H K)) (ywf_r2 C0 C1 C2 C3 C4 F G H K))
  ≔ let T ≔ YonedaWildFunctor C0 C4 in
    let Phi ≔ wild_functor_yoneda C0 C4 in
    let yF ≔ wild_functor_yoneda C0 C1 F in
    let yG ≔ wild_functor_yoneda C1 C2 G in
    let yH ≔ wild_functor_yoneda C2 C3 H in
    let yK ≔ wild_functor_yoneda C3 C4 K in
    let hg ≔ functor_compose C1 C2 C3 H G in
    let P1 ≔ ywf_P1 C0 C1 C2 C3 C4 F G H K in
    let P2 ≔ ywf_P2 C0 C1 C2 C3 C4 F G H K in
    let V1 ≔ Phi P1 in
    let V2 ≔ Phi P2 in
    let a2 ≔ ywf_a2 alpha C0 C1 C2 C3 C4 F G H K in
    let yc04 ≔ yoneda_wild_functor_compose C0 C3 C4 yK in
    let ycF : YonedaWildFunctor C1 C4 → T ≔ x ↦ yoneda_wild_functor_compose C0 C1 C4 x yF in
    let wd ≔ ywf_word C0 C1 C2 C3 C4 F G H K in
    let mu_kx : (X : WildFunctor C0 C3) → Id T (yc04 (wild_functor_yoneda C0 C3 X)) (Phi (functor_compose C0 C3 C4 K X))
      ≔ X ↦ wild_functor_yoneda_compose C0 C3 C4 K X in
    let mu_xf : (X : WildFunctor C1 C4) → Id T (ycF (wild_functor_yoneda C1 C4 X)) (Phi (functor_compose C0 C1 C4 X F))
      ≔ X ↦ wild_functor_yoneda_compose C0 C1 C4 X F in
    let r1 ≔ ywf_r1 C0 C1 C2 C3 C4 F G H K in
    let r2 ≔ ywf_r2 C0 C1 C2 C3 C4 F G H K in
    let yhg ≔ wild_functor_yoneda C1 C3 hg in
    let m2 ≔ refl ((x ↦ yc04 (yoneda_wild_functor_compose C0 C1 C3 x yF)) : YonedaWildFunctor C1 C3 → T)
      (wild_functor_yoneda_compose C1 C2 C3 H G) in
    ywf_direct_edge T wd (yc04 (yoneda_wild_functor_compose C0 C1 C3 yhg yF)) V1 V2 m2
      (ywf_rho_left C0 C1 C3 C4 F hg K) (ywf_rho_right C0 C1 C3 C4 F hg K) r1 r2
      (ch6c_ap_concat_assoc (YonedaWildFunctor C0 C3) T yc04
        (yoneda_wild_functor_compose C0 C1 C3 (yoneda_wild_functor_compose C1 C2 C3 yH yG) yF)
        (yoneda_wild_functor_compose C0 C1 C3 yhg yF)
        (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 hg F)) V1
        (refl ((x ↦ yoneda_wild_functor_compose C0 C1 C3 x yF) : YonedaWildFunctor C1 C3 → YonedaWildFunctor C0 C3)
          (wild_functor_yoneda_compose C1 C2 C3 H G))
        (wild_functor_yoneda_compose C0 C1 C3 hg F) (mu_kx (functor_compose C0 C1 C3 hg F)))
      (ch6c_ap_concat_assoc (YonedaWildFunctor C1 C4) T ycF
        (yoneda_wild_functor_compose C1 C3 C4 yK (yoneda_wild_functor_compose C1 C2 C3 yH yG))
        (yoneda_wild_functor_compose C1 C3 C4 yK yhg)
        (wild_functor_yoneda C1 C4 (functor_compose C1 C3 C4 K hg)) V2
        (refl (yoneda_wild_functor_compose C1 C3 C4 yK) (wild_functor_yoneda_compose C1 C2 C3 H G))
        (wild_functor_yoneda_compose C1 C3 C4 K hg) (mu_xf (functor_compose C1 C3 C4 K hg)))
      (refl Phi a2)
      (inverse (Id T V1 V2) (ywf_beta C0 C1 C3 C4 F hg K) (refl Phi a2)
        (img C0 C1 C3 C4 F hg K))

{` Edge 4: α at (G ∘ F, H, K). `}
def ywf_edge4 (alpha : YwfAssoc) (img : YwfAssocImage alpha)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4)
  : Id (Id (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K)) (wild_functor_yoneda C0 C4 (ywf_P4 C0 C1 C2 C3 C4 F G H K)))
      (refl (wild_functor_yoneda C0 C4) (ywf_a4 alpha C0 C1 C2 C3 C4 F G H K))
      (concat (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K)) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P4 C0 C1 C2 C3 C4 F G H K))
        (inverse (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K)) (ywf_r0 C0 C1 C2 C3 C4 F G H K)) (ywf_r4 C0 C1 C2 C3 C4 F G H K))
  ≔ let T ≔ YonedaWildFunctor C0 C4 in
    let Phi ≔ wild_functor_yoneda C0 C4 in
    let yF ≔ wild_functor_yoneda C0 C1 F in
    let yG ≔ wild_functor_yoneda C1 C2 G in
    let yH ≔ wild_functor_yoneda C2 C3 H in
    let yK ≔ wild_functor_yoneda C3 C4 K in
    let gf ≔ functor_compose C0 C1 C2 G F in
    let P0 ≔ ywf_P0 C0 C1 C2 C3 C4 F G H K in
    let P4 ≔ ywf_P4 C0 C1 C2 C3 C4 F G H K in
    let V0 ≔ Phi P0 in
    let V4 ≔ Phi P4 in
    let a4 ≔ ywf_a4 alpha C0 C1 C2 C3 C4 F G H K in
    let yc04 ≔ yoneda_wild_functor_compose C0 C3 C4 yK in
    let wd ≔ ywf_word C0 C1 C2 C3 C4 F G H K in
    let mu_kx : (X : WildFunctor C0 C3) → Id T (yc04 (wild_functor_yoneda C0 C3 X)) (Phi (functor_compose C0 C3 C4 K X))
      ≔ X ↦ wild_functor_yoneda_compose C0 C3 C4 K X in
    let r0 ≔ ywf_r0 C0 C1 C2 C3 C4 F G H K in
    let r4 ≔ ywf_r4 C0 C1 C2 C3 C4 F G H K in
    let ykh ≔ yoneda_wild_functor_compose C2 C3 C4 yK yH in
    let ygf ≔ yoneda_wild_functor_compose C0 C1 C2 yG yF in
    let c ≔ yoneda_wild_functor_compose C0 C2 C4 in
    let mu_gf ≔ wild_functor_yoneda_compose C0 C1 C2 G F in
    let m4 ≔ refl (c ykh) mu_gf in
    let ygf' ≔ wild_functor_yoneda C0 C2 gf in
    ywf_direct_edge T wd (yc04 (yoneda_wild_functor_compose C0 C2 C3 yH ygf')) V0 V4 m4
      (ywf_rho_left C0 C2 C3 C4 gf H K) (ywf_rho_right C0 C2 C3 C4 gf H K) r0 r4
      (ch6c_ap_concat_assoc (YonedaWildFunctor C0 C3) T yc04
        (yoneda_wild_functor_compose C0 C2 C3 yH ygf)
        (yoneda_wild_functor_compose C0 C2 C3 yH ygf')
        (wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H gf)) V0
        (refl (yoneda_wild_functor_compose C0 C2 C3 yH) mu_gf)
        (wild_functor_yoneda_compose C0 C2 C3 H gf) (mu_kx (functor_compose C0 C2 C3 H gf)))
      (refl r4)
      (refl Phi a4)
      (inverse (Id T V0 V4) (ywf_beta C0 C2 C3 C4 gf H K) (refl Phi a4)
        (img C0 C2 C3 C4 gf H K))

{` Edge 5: α at (F, G, K ∘ H). `}
def ywf_edge5 (alpha : YwfAssoc) (img : YwfAssocImage alpha)
  (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  (K : WildFunctor C3 C4)
  : Id (Id (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P4 C0 C1 C2 C3 C4 F G H K)) (wild_functor_yoneda C0 C4 (ywf_P3 C0 C1 C2 C3 C4 F G H K)))
      (refl (wild_functor_yoneda C0 C4) (ywf_a5 alpha C0 C1 C2 C3 C4 F G H K))
      (concat (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P4 C0 C1 C2 C3 C4 F G H K)) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P3 C0 C1 C2 C3 C4 F G H K))
        (inverse (YonedaWildFunctor C0 C4) (ywf_word C0 C1 C2 C3 C4 F G H K) (wild_functor_yoneda C0 C4 (ywf_P4 C0 C1 C2 C3 C4 F G H K)) (ywf_r4 C0 C1 C2 C3 C4 F G H K)) (ywf_r3 C0 C1 C2 C3 C4 F G H K))
  ≔ let T ≔ YonedaWildFunctor C0 C4 in
    let Phi ≔ wild_functor_yoneda C0 C4 in
    let yF ≔ wild_functor_yoneda C0 C1 F in
    let yG ≔ wild_functor_yoneda C1 C2 G in
    let yH ≔ wild_functor_yoneda C2 C3 H in
    let yK ≔ wild_functor_yoneda C3 C4 K in
    let gf ≔ functor_compose C0 C1 C2 G F in
    let kh ≔ functor_compose C2 C3 C4 K H in
    let P3 ≔ ywf_P3 C0 C1 C2 C3 C4 F G H K in
    let P4 ≔ ywf_P4 C0 C1 C2 C3 C4 F G H K in
    let V3 ≔ Phi P3 in
    let V4 ≔ Phi P4 in
    let a5 ≔ ywf_a5 alpha C0 C1 C2 C3 C4 F G H K in
    let ycF : YonedaWildFunctor C1 C4 → T ≔ x ↦ yoneda_wild_functor_compose C0 C1 C4 x yF in
    let wd ≔ ywf_word C0 C1 C2 C3 C4 F G H K in
    let mu_xf : (X : WildFunctor C1 C4) → Id T (ycF (wild_functor_yoneda C1 C4 X)) (Phi (functor_compose C0 C1 C4 X F))
      ≔ X ↦ wild_functor_yoneda_compose C0 C1 C4 X F in
    let r3 ≔ ywf_r3 C0 C1 C2 C3 C4 F G H K in
    let r4 ≔ ywf_r4 C0 C1 C2 C3 C4 F G H K in
    let ykh ≔ yoneda_wild_functor_compose C2 C3 C4 yK yH in
    let ygf ≔ yoneda_wild_functor_compose C0 C1 C2 yG yF in
    let c ≔ yoneda_wild_functor_compose C0 C2 C4 in
    let mu_gf ≔ wild_functor_yoneda_compose C0 C1 C2 G F in
    let mu_kh ≔ wild_functor_yoneda_compose C2 C3 C4 K H in
    let m4 ≔ refl (c ykh) mu_gf in
    let ygf' ≔ wild_functor_yoneda C0 C2 gf in
    let ykh' ≔ wild_functor_yoneda C2 C4 kh in
    let m5 ≔ refl ((y ↦ c y ygf) : YonedaWildFunctor C2 C4 → T) mu_kh in
    let n4 ≔ refl ((y ↦ c y ygf') : YonedaWildFunctor C2 C4 → T) mu_kh in
    let n5 ≔ refl (c ykh') mu_gf in
    let muf ≔ wild_functor_yoneda_compose C0 C2 C4 kh gf in
    let c4 : Id (Id T wd V4) r4 (concat T wd (c ykh' ygf) V4 m5 (concat T (c ykh' ygf) (c ykh' ygf') V4 n5 muf))
      ≔ concat (Id T wd V4) r4 (concat T wd (c ykh' ygf') V4 (concat T wd (c ykh ygf') (c ykh' ygf') m4 n4) muf)
          (concat T wd (c ykh' ygf) V4 m5 (concat T (c ykh' ygf) (c ykh' ygf') V4 n5 muf))
          (inverse (Id T wd V4) (concat T wd (c ykh' ygf') V4 (concat T wd (c ykh ygf') (c ykh' ygf') m4 n4) muf) r4
            (concat_assoc T wd (c ykh ygf') (c ykh' ygf') V4 m4 n4 muf))
          (concat (Id T wd V4) (concat T wd (c ykh' ygf') V4 (concat T wd (c ykh ygf') (c ykh' ygf') m4 n4) muf)
            (concat T wd (c ykh' ygf') V4 (concat T wd (c ykh' ygf) (c ykh' ygf') m5 n5) muf)
            (concat T wd (c ykh' ygf) V4 m5 (concat T (c ykh' ygf) (c ykh' ygf') V4 n5 muf))
            (refl ((z ↦ concat T wd (c ykh' ygf') V4 z muf) : Id T wd (c ykh' ygf') → Id T wd V4)
              (ywf_interchange (YonedaWildFunctor C0 C2) (YonedaWildFunctor C2 C4) T c ykh ykh' mu_kh ygf ygf' mu_gf))
            (concat_assoc T wd (c ykh' ygf) (c ykh' ygf') V4 m5 n5 muf)) in
    ywf_direct_edge T wd (c ykh' ygf) V4 V3 m5
      (ywf_rho_left C0 C1 C2 C4 F G kh) (ywf_rho_right C0 C1 C2 C4 F G kh) r4 r3
      c4
      (ch6c_ap_concat_assoc (YonedaWildFunctor C1 C4) T ycF
        (yoneda_wild_functor_compose C1 C2 C4 ykh yG)
        (yoneda_wild_functor_compose C1 C2 C4 ykh' yG)
        (wild_functor_yoneda C1 C4 (functor_compose C1 C2 C4 kh G)) V3
        (refl ((x ↦ yoneda_wild_functor_compose C1 C2 C4 x yG) : YonedaWildFunctor C2 C4 → YonedaWildFunctor C1 C4)
          mu_kh)
        (wild_functor_yoneda_compose C1 C2 C4 kh G) (mu_xf (functor_compose C1 C2 C4 kh G)))
      (refl Phi a5)
      (inverse (Id T V4 V3) (ywf_beta C0 C1 C2 C4 F G kh) (refl Phi a5)
        (img C0 C1 C2 C4 F G kh))

{` The pentagon for any associator α with ap Φ α = β. `}
def ywf_pentagon_with (alpha : YwfAssoc) (img : YwfAssocImage alpha) (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1)
  (G : WildFunctor C1 C2) (H : WildFunctor C2 C3) (K : WildFunctor C3 C4)
  : WildPentagonFiller (WildPrecatWildWith alpha) C0 C1 C2 C3 C4 F G H K
  ≔ ywf_pentagon_reflect (WildFunctor C0 C4) (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4)
      (ywf_P0 C0 C1 C2 C3 C4 F G H K) (ywf_P1 C0 C1 C2 C3 C4 F G H K) (ywf_P2 C0 C1 C2 C3 C4 F G H K)
      (ywf_P3 C0 C1 C2 C3 C4 F G H K) (ywf_P4 C0 C1 C2 C3 C4 F G H K)
      (ywf_a1 alpha C0 C1 C2 C3 C4 F G H K) (ywf_a2 alpha C0 C1 C2 C3 C4 F G H K) (ywf_a3 alpha C0 C1 C2 C3 C4 F G H K)
      (ywf_a4 alpha C0 C1 C2 C3 C4 F G H K) (ywf_a5 alpha C0 C1 C2 C3 C4 F G H K)
      (ywf_word C0 C1 C2 C3 C4 F G H K)
      (ywf_r0 C0 C1 C2 C3 C4 F G H K) (ywf_r1 C0 C1 C2 C3 C4 F G H K) (ywf_r2 C0 C1 C2 C3 C4 F G H K)
      (ywf_r3 C0 C1 C2 C3 C4 F G H K) (ywf_r4 C0 C1 C2 C3 C4 F G H K)
      (ywf_edge1 alpha img C0 C1 C2 C3 C4 F G H K) (ywf_edge2 alpha img C0 C1 C2 C3 C4 F G H K) (ywf_edge3 alpha img C0 C1 C2 C3 C4 F G H K)
      (ywf_edge4 alpha img C0 C1 C2 C3 C4 F G H K) (ywf_edge5 alpha img C0 C1 C2 C3 C4 F G H K)
      (p q h ↦ ywf_book_equiv_injective (Id (WildFunctor C0 C4) (ywf_P0 C0 C1 C2 C3 C4 F G H K) (ywf_P3 C0 C1 C2 C3 C4 F G H K))
        (Id (YonedaWildFunctor C0 C4) (wild_functor_yoneda C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K))
          (wild_functor_yoneda C0 C4 (ywf_P3 C0 C1 C2 C3 C4 F G H K)))
        (wild_functor_yoneda_paths C0 C4 (ywf_P0 C0 C1 C2 C3 C4 F G H K) (ywf_P3 C0 C1 C2 C3 C4 F G H K)) p q h)

{` The pentagon fillers for the associator of module 693. `}
def wild_precat_yoneda_pentagon_filler (C0 C1 C2 C3 C4 : WildPrecat) (F : WildFunctor C0 C1)
  (G : WildFunctor C1 C2) (H : WildFunctor C2 C3) (K : WildFunctor C3 C4)
  : WildPentagonFiller WildPrecatWildYoneda C0 C1 C2 C3 C4 F G H K
  ≔ ywf_pentagon_with functor_assoc_yoneda functor_assoc_yoneda_image C0 C1 C2 C3 C4 F G H K

{` xca:wildprecat-of-wildprecats, the adventurous part: the wild
   precategory of wild precategories (with α of module 693) satisfies the
   pentagon for all four composable wild functors, whatever C_4 is. `}
def wild_precat_yoneda_pentagon : WildPentagon WildPrecatWildYoneda
  ≔ C0 C1 C2 C3 C4 F G H K ↦ wild_precat_yoneda_pentagon_filler C0 C1 C2 C3 C4 F G H K
