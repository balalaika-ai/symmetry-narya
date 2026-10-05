export "692-yoneda-wild-functors"

{` Chapter 6, xca:wildprecat-of-wildprecats, the optional ("if you're
   feeling adventurous") part in the general wild case: fillers for the
   pentagon eq:pentagon for four composable wild functors, with no
   hypothesis on C_4.

   The associator is chosen by strictification (module 692): Φ sends wild
   functors to Yoneda wild functors, whose composition is associative on
   the nose, and μ : Φ G ∘ Φ F = Φ (G ∘ F). Both sides of α are sent by Φ
   to the strict composite by μ's (ρ_left, ρ_right); α is the unique path
   with ap Φ α = ρ_left⁻¹ · ρ_right (ap Φ is an equivalence). For the
   pentagon, every edge is sent by ap Φ to r_i⁻¹ · r_j, where r_i is a path
   from the strict fourfold composite to the vertex i; the pentagon then
   holds by groupoid algebra, and ap Φ reflects it (module 694; this
   module has the groupoid lemmas, α and the final reflection step
   ywf_pentagon_reflect). The identity functors,
   composition, λ and ρ are those of WildPrecatWild (module 644); only α
   differs from functor_assoc (both are identifications of the same
   functors; the book lets the reader choose α). `}

{` Groupoid lemmas. `}
def ywf_conj_base (T : Type) (w a b y : T) (l : Id T w a) (r : Id T w b) (hy : Id T b y) (q : Id T a y)
  (N : Id (Id T a y) (concat T a b y (concat T a w b (inverse T w a l) r) hy) (concat T a a y (refl a) q))
  : Id (Id T a y) q (concat T a w y (inverse T w a (concat T w a a l (refl a))) (concat T w b y r hy))
  ≔ let s0 ≔ concat T a b y (concat T a w b (inverse T w a l) r) hy in
    let s1 ≔ concat T a w y (inverse T w a l) (concat T w b y r hy) in
    let s2 ≔ concat T a w y (inverse T w a (concat T w a a l (refl a))) (concat T w b y r hy) in
    let q1 ≔ concat T a a y (refl a) q in
    concat (Id T a y) q q1 s2 (inverse (Id T a y) q1 q (concat_1p T a y q))
      (concat (Id T a y) q1 s0 s2 (inverse (Id T a y) s0 q1 N)
        (concat (Id T a y) s0 s1 s2 (concat_assoc T a w b y (inverse T w a l) r hy)
          (refl ((s ↦ concat T a w y (inverse T w a s) (concat T w b y r hy)) : Id T w a → Id T a y)
            (inverse (Id T w a) (concat T w a a l (refl a)) l (concat_p1 T w a l)))))

{` From a naturality square (l⁻¹ · r) · h_y = h_x · q, q = (l · h_x)⁻¹ · (r · h_y). `}
def ywf_conj (T : Type) (w a b x y : T) (l : Id T w a) (r : Id T w b) (hx : Id T a x) (hy : Id T b y)
  (q : Id T x y)
  (N : Id (Id T a y) (concat T a b y (concat T a w b (inverse T w a l) r) hy) (concat T a x y hx q))
  : Id (Id T x y) q (concat T x w y (inverse T w x (concat T w a x l hx)) (concat T w b y r hy))
  ≔ J T a
      (x hx ↦ (q : Id T x y)
        → Id (Id T a y) (concat T a b y (concat T a w b (inverse T w a l) r) hy) (concat T a x y hx q)
        → Id (Id T x y) q (concat T x w y (inverse T w x (concat T w a x l hx)) (concat T w b y r hy)))
      (q N ↦ ywf_conj_base T w a b y l r hy q N) x hx q N

{` (m · x)⁻¹ · (m · y) = x⁻¹ · y. `}
def ywf_cancel (T : Type) (w0 w a b : T) (m : Id T w0 w) (x : Id T w a) (y : Id T w b)
  : Id (Id T a b) (concat T a w0 b (inverse T w0 a (concat T w0 w a m x)) (concat T w0 w b m y))
      (concat T a w b (inverse T w a x) y)
  ≔ J T w0
      (w m ↦ (x : Id T w a) (y : Id T w b)
        → Id (Id T a b) (concat T a w0 b (inverse T w0 a (concat T w0 w a m x)) (concat T w0 w b m y))
            (concat T a w b (inverse T w a x) y))
      (x y ↦ refl ((s t ↦ concat T a w0 b (inverse T w0 a s) t) : Id T w0 a → Id T w0 b → Id T a b)
        (concat_1p T w0 a x) (concat_1p T w0 b y))
      w m x y

{` An edge q = x⁻¹ · y, rewritten with r_0 = m · x and r_1 = m · y. `}
def ywf_direct_edge (T : Type) (w0 w a b : T) (m : Id T w0 w) (x : Id T w a) (y : Id T w b)
  (r0 : Id T w0 a) (r1 : Id T w0 b)
  (c0 : Id (Id T w0 a) r0 (concat T w0 w a m x)) (c1 : Id (Id T w0 b) r1 (concat T w0 w b m y))
  (q : Id T a b) (e : Id (Id T a b) q (concat T a w b (inverse T w a x) y))
  : Id (Id T a b) q (concat T a w0 b (inverse T w0 a r0) r1)
  ≔ let mx ≔ concat T w0 w a m x in
    let my ≔ concat T w0 w b m y in
    concat (Id T a b) q (concat T a w b (inverse T w a x) y) (concat T a w0 b (inverse T w0 a r0) r1) e
      (concat (Id T a b) (concat T a w b (inverse T w a x) y) (concat T a w0 b (inverse T w0 a mx) my)
        (concat T a w0 b (inverse T w0 a r0) r1)
        (inverse (Id T a b) (concat T a w0 b (inverse T w0 a mx) my) (concat T a w b (inverse T w a x) y)
          (ywf_cancel T w0 w a b m x y))
        (refl ((s t ↦ concat T a w0 b (inverse T w0 a s) t) : Id T w0 a → Id T w0 b → Id T a b)
          (inverse (Id T w0 a) r0 mx c0) (inverse (Id T w0 b) r1 my c1)))

{` A whiskered edge: if ap Φ α = l⁻¹ · r and h : s ∘ Φ ~ g, then
   ap g α = (ap s l · h X)⁻¹ · (ap s r · h X'). `}
def ywf_whisker_edge (A T U : Type) (Phi : A → T) (s : T → U) (g : A → U)
  (h : (X : A) → Id U (s (Phi X)) (g X)) (X X' : A) (al : Id A X X') (w : T)
  (l : Id T w (Phi X)) (r : Id T w (Phi X'))
  (e : Id (Id T (Phi X) (Phi X')) (concat T (Phi X) w (Phi X') (inverse T w (Phi X) l) r) (refl Phi al))
  : Id (Id U (g X) (g X')) (refl g al)
      (concat U (g X) (s w) (g X')
        (inverse U (s w) (g X) (concat U (s w) (s (Phi X)) (g X) (refl s l) (h X)))
        (concat U (s w) (s (Phi X')) (g X') (refl s r) (h X')))
  ≔ let a ≔ s (Phi X) in
    let b ≔ s (Phi X') in
    let sl ≔ refl s l in
    let sr ≔ refl s r in
    let lr ≔ concat T (Phi X) w (Phi X') (inverse T w (Phi X) l) r in
    let slr ≔ concat U a (s w) b (inverse U (s w) a sl) sr in
    let E : Id (Id U a b) (refl s (refl Phi al)) slr
      ≔ concat (Id U a b) (refl s (refl Phi al)) (refl s lr) slr
          (refl ((z ↦ refl s z) : Id T (Phi X) (Phi X') → Id U a b)
            (inverse (Id T (Phi X) (Phi X')) lr (refl Phi al) e))
          (concat (Id U a b) (refl s lr) (concat U a (s w) b (refl s (inverse T w (Phi X) l)) sr) slr
            (map_path_concat T U s (Phi X) w (Phi X') (inverse T w (Phi X) l) r)
            (refl ((z ↦ concat U a (s w) b z sr) : Id U a (s w) → Id U a b)
              (map_path_inverse T U s w (Phi X) l))) in
    let N : Id (Id U a (g X')) (concat U a b (g X') slr (h X')) (concat U a (g X) (g X') (h X) (refl g al))
      ≔ concat (Id U a (g X')) (concat U a b (g X') slr (h X'))
          (concat U a b (g X') (refl s (refl Phi al)) (h X'))
          (concat U a (g X) (g X') (h X) (refl g al))
          (refl ((z ↦ concat U a b (g X') z (h X')) : Id U a b → Id U a (g X'))
            (inverse (Id U a b) (refl s (refl Phi al)) slr E))
          (naturality A U (z ↦ s (Phi z)) g h X X' al) in
    ywf_conj U (s w) a b (g X) (g X') sl sr (h X) (h X') (refl g al) N

{` Interchange for a function of two variables. `}
def ywf_interchange (A B U : Type) (c : B → A → U) (y0 y1 : B) (u : Id B y0 y1) (x0 x1 : A) (v : Id A x0 x1)
  : Id (Id U (c y0 x0) (c y1 x1))
      (concat U (c y0 x0) (c y0 x1) (c y1 x1) (refl (c y0) v) (refl ((y ↦ c y x1) : B → U) u))
      (concat U (c y0 x0) (c y1 x0) (c y1 x1) (refl ((y ↦ c y x0) : B → U) u) (refl (c y1) v))
  ≔ let ux ≔ refl ((y ↦ c y x0) : B → U) u in
    J A x0
      (x1 v ↦ Id (Id U (c y0 x0) (c y1 x1))
        (concat U (c y0 x0) (c y0 x1) (c y1 x1) (refl (c y0) v) (refl ((y ↦ c y x1) : B → U) u))
        (concat U (c y0 x0) (c y1 x0) (c y1 x1) (refl ((y ↦ c y x0) : B → U) u) (refl (c y1) v)))
      (concat (Id U (c y0 x0) (c y1 x0)) (concat U (c y0 x0) (c y0 x0) (c y1 x0) (refl (c y0 x0)) ux) ux
        (concat U (c y0 x0) (c y1 x0) (c y1 x0) ux (refl (c y1 x0)))
        (concat_1p U (c y0 x0) (c y1 x0) ux)
        (inverse (Id U (c y0 x0) (c y1 x0)) (concat U (c y0 x0) (c y1 x0) (c y1 x0) ux (refl (c y1 x0))) ux
          (concat_p1 U (c y0 x0) (c y1 x0) ux)))
      x1 v

{` The pentagon of edges r_i⁻¹ · r_j between five points under w. `}
def ywf_pent_stmt (T : Type) (w V0 V1 V2 V3 V4 : T) (r0 : Id T w V0) (r1 : Id T w V1) (r2 : Id T w V2)
  (r3 : Id T w V3) (r4 : Id T w V4) : Type
  ≔ Id (Id T V0 V3)
      (concat T V0 V1 V3 (concat T V0 w V1 (inverse T w V0 r0) r1)
        (concat T V1 V2 V3 (concat T V1 w V2 (inverse T w V1 r1) r2) (concat T V2 w V3 (inverse T w V2 r2) r3)))
      (concat T V0 V4 V3 (concat T V0 w V4 (inverse T w V0 r0) r4) (concat T V4 w V3 (inverse T w V4 r4) r3))

def ywf_pent_base (T : Type) (w V0 V3 : T) (r0 : Id T w V0) (r3 : Id T w V3)
  : ywf_pent_stmt T w V0 w w V3 w r0 (refl w) (refl w) r3 (refl w)
  ≔ let X ≔ concat T V0 w w (inverse T w V0 r0) (refl w) in
    let cc ≔ concat T w w w (inverse T w w (refl w)) (refl w) in
    let d ≔ concat T w w V3 (inverse T w w (refl w)) r3 in
    refl ((z ↦ concat T V0 w V3 X z) : Id T w V3 → Id T V0 V3)
      (concat (Id T w V3) (concat T w w V3 cc d) (concat T w w V3 (refl w) d) d
        (refl ((z ↦ concat T w w V3 z d) : Id T w w → Id T w V3) (concat_inverse_left T w w (refl w)))
        (concat_1p T w V3 d))

def ywf_pent (T : Type) (w V0 V1 V2 V3 V4 : T) (r0 : Id T w V0) (r1 : Id T w V1) (r2 : Id T w V2)
  (r3 : Id T w V3) (r4 : Id T w V4)
  : ywf_pent_stmt T w V0 V1 V2 V3 V4 r0 r1 r2 r3 r4
  ≔ J T w (V4 r4 ↦ ywf_pent_stmt T w V0 V1 V2 V3 V4 r0 r1 r2 r3 r4)
      (J T w (V2 r2 ↦ ywf_pent_stmt T w V0 V1 V2 V3 w r0 r1 r2 r3 (refl w))
        (J T w (V1 r1 ↦ ywf_pent_stmt T w V0 V1 w V3 w r0 r1 (refl w) r3 (refl w))
          (ywf_pent_base T w V0 V3 r0 r3) V1 r1)
        V2 r2)
      V4 r4

{` ρ_left : Φ H ∘ (Φ G ∘ Φ F) = Φ (H ∘ (G ∘ F)). `}
def ywf_rho_left (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2)
  (H : WildFunctor C2 C3)
  : Id (YonedaWildFunctor C0 C3)
      (yoneda_wild_functor_compose C0 C2 C3 (wild_functor_yoneda C2 C3 H)
        (yoneda_wild_functor_compose C0 C1 C2 (wild_functor_yoneda C1 C2 G) (wild_functor_yoneda C0 C1 F)))
      (wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F)))
  ≔ let yH ≔ wild_functor_yoneda C2 C3 H in
    concat (YonedaWildFunctor C0 C3)
      (yoneda_wild_functor_compose C0 C2 C3 yH
        (yoneda_wild_functor_compose C0 C1 C2 (wild_functor_yoneda C1 C2 G) (wild_functor_yoneda C0 C1 F)))
      (yoneda_wild_functor_compose C0 C2 C3 yH (wild_functor_yoneda C0 C2 (functor_compose C0 C1 C2 G F)))
      (wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F)))
      (refl (yoneda_wild_functor_compose C0 C2 C3 yH) (wild_functor_yoneda_compose C0 C1 C2 G F))
      (wild_functor_yoneda_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))

{` ρ_right : (Φ H ∘ Φ G) ∘ Φ F = Φ ((H ∘ G) ∘ F); its source is the
   source of ρ_left on the nose. `}
def ywf_rho_right (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2)
  (H : WildFunctor C2 C3)
  : Id (YonedaWildFunctor C0 C3)
      (yoneda_wild_functor_compose C0 C2 C3 (wild_functor_yoneda C2 C3 H)
        (yoneda_wild_functor_compose C0 C1 C2 (wild_functor_yoneda C1 C2 G) (wild_functor_yoneda C0 C1 F)))
      (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F))
  ≔ let yF ≔ wild_functor_yoneda C0 C1 F in
    concat (YonedaWildFunctor C0 C3)
      (yoneda_wild_functor_compose C0 C1 C3
        (yoneda_wild_functor_compose C1 C2 C3 (wild_functor_yoneda C2 C3 H) (wild_functor_yoneda C1 C2 G)) yF)
      (yoneda_wild_functor_compose C0 C1 C3 (wild_functor_yoneda C1 C3 (functor_compose C1 C2 C3 H G)) yF)
      (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F))
      (refl ((x ↦ yoneda_wild_functor_compose C0 C1 C3 x yF) : YonedaWildFunctor C1 C3 → YonedaWildFunctor C0 C3)
        (wild_functor_yoneda_compose C1 C2 C3 H G))
      (wild_functor_yoneda_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)

def ywf_beta (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2)
  (H : WildFunctor C2 C3)
  : Id (YonedaWildFunctor C0 C3)
      (wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F)))
      (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F))
  ≔ let w ≔ yoneda_wild_functor_compose C0 C2 C3 (wild_functor_yoneda C2 C3 H)
        (yoneda_wild_functor_compose C0 C1 C2 (wild_functor_yoneda C1 C2 G) (wild_functor_yoneda C0 C1 F)) in
    let L ≔ wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F)) in
    concat (YonedaWildFunctor C0 C3) L w
      (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F))
      (inverse (YonedaWildFunctor C0 C3) w L (ywf_rho_left C0 C1 C2 C3 F G H))
      (ywf_rho_right C0 C1 C2 C3 F G H)

{` α : H ∘ (G ∘ F) = (H ∘ G) ∘ F, the unique path with ap Φ α = β. `}
def functor_assoc_yoneda (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2)
  (H : WildFunctor C2 C3)
  : Id (WildFunctor C0 C3) (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))
      (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)
  ≔ wild_functor_yoneda_paths C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))
      (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)
      .equiv (ywf_beta C0 C1 C2 C3 F G H) .center .fst

def functor_assoc_yoneda_image (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2)
  (H : WildFunctor C2 C3)
  : Id (Id (YonedaWildFunctor C0 C3)
        (wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F)))
        (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)))
      (ywf_beta C0 C1 C2 C3 F G H)
      (refl (wild_functor_yoneda C0 C3) (functor_assoc_yoneda C0 C1 C2 C3 F G H))
  ≔ wild_functor_yoneda_paths C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))
      (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)
      .equiv (ywf_beta C0 C1 C2 C3 F G H) .center .snd

{` The type of associators for composition of wild functors, and the
   property used for the pentagon: ap Φ α = β. `}
def YwfAssoc : Type
  ≔ (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
    → Id (WildFunctor C0 C3) (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))
        (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)

def YwfAssocImage (alpha : YwfAssoc) : Type
  ≔ (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
    → Id (Id (YonedaWildFunctor C0 C3)
          (wild_functor_yoneda C0 C3 (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F)))
          (wild_functor_yoneda C0 C3 (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)))
        (ywf_beta C0 C1 C2 C3 F G H) (refl (wild_functor_yoneda C0 C3) (alpha C0 C1 C2 C3 F G H))

{` The wild precategory of wild precategories with a given associator. `}
def WildPrecatWildWith (alpha : YwfAssoc) : WildPrecat
  ≔ (ob ≔ WildPrecat,
     hom ≔ C D ↦ WildFunctor C D,
     idn ≔ C ↦ functor_identity C,
     comp ≔ C D E G F ↦ functor_compose C D E G F,
     lu ≔ C D F ↦ functor_left_unit C D F,
     ru ≔ C D F ↦ functor_right_unit C D F,
     assoc ≔ C0 C1 C2 C3 F G H ↦ alpha C0 C1 C2 C3 F G H)

{` xca:wildprecat-of-wildprecats: the wild precategory of wild
   precategories with the associator α above. `}
def WildPrecatWildYoneda : WildPrecat ≔ WildPrecatWildWith functor_assoc_yoneda

{` The pentagon from its image: if ap Φ sends every edge a_k to r_i⁻¹ · r_j
   and ap Φ reflects identifications of paths P_0 = P_3, then
   a_1 · (a_2 · a_3) = a_4 · a_5. `}
def ywf_pentagon_reflect (A T : Type) (Phi : A → T) (P0 P1 P2 P3 P4 : A)
  (a1 : Id A P0 P1) (a2 : Id A P1 P2) (a3 : Id A P2 P3) (a4 : Id A P0 P4) (a5 : Id A P4 P3) (w : T)
  (r0 : Id T w (Phi P0)) (r1 : Id T w (Phi P1)) (r2 : Id T w (Phi P2)) (r3 : Id T w (Phi P3))
  (r4 : Id T w (Phi P4))
  (e1 : Id (Id T (Phi P0) (Phi P1)) (refl Phi a1)
    (concat T (Phi P0) w (Phi P1) (inverse T w (Phi P0) r0) r1))
  (e2 : Id (Id T (Phi P1) (Phi P2)) (refl Phi a2)
    (concat T (Phi P1) w (Phi P2) (inverse T w (Phi P1) r1) r2))
  (e3 : Id (Id T (Phi P2) (Phi P3)) (refl Phi a3)
    (concat T (Phi P2) w (Phi P3) (inverse T w (Phi P2) r2) r3))
  (e4 : Id (Id T (Phi P0) (Phi P4)) (refl Phi a4)
    (concat T (Phi P0) w (Phi P4) (inverse T w (Phi P0) r0) r4))
  (e5 : Id (Id T (Phi P4) (Phi P3)) (refl Phi a5)
    (concat T (Phi P4) w (Phi P3) (inverse T w (Phi P4) r4) r3))
  (inj : (p q : Id A P0 P3) → Id (Id T (Phi P0) (Phi P3)) (refl Phi p) (refl Phi q) → Id (Id A P0 P3) p q)
  : Id (Id A P0 P3) (concat A P0 P1 P3 a1 (concat A P1 P2 P3 a2 a3)) (concat A P0 P4 P3 a4 a5)
  ≔ let V0 ≔ Phi P0 in let V1 ≔ Phi P1 in let V2 ≔ Phi P2 in let V3 ≔ Phi P3 in let V4 ≔ Phi P4 in
    let lhs ≔ concat A P0 P1 P3 a1 (concat A P1 P2 P3 a2 a3) in
    let rhs ≔ concat A P0 P4 P3 a4 a5 in
    let q01 ≔ concat T V0 w V1 (inverse T w V0 r0) r1 in
    let q12 ≔ concat T V1 w V2 (inverse T w V1 r1) r2 in
    let q23 ≔ concat T V2 w V3 (inverse T w V2 r2) r3 in
    let q04 ≔ concat T V0 w V4 (inverse T w V0 r0) r4 in
    let q43 ≔ concat T V4 w V3 (inverse T w V4 r4) r3 in
    let t0 ≔ refl Phi lhs in
    let t1 ≔ concat T V0 V1 V3 (refl Phi a1) (refl Phi (concat A P1 P2 P3 a2 a3)) in
    let t2 ≔ concat T V0 V1 V3 (refl Phi a1) (concat T V1 V2 V3 (refl Phi a2) (refl Phi a3)) in
    let t3 ≔ concat T V0 V1 V3 q01 (concat T V1 V2 V3 q12 q23) in
    let t4 ≔ concat T V0 V4 V3 q04 q43 in
    let t5 ≔ concat T V0 V4 V3 (refl Phi a4) (refl Phi a5) in
    let t6 ≔ refl Phi rhs in
    inj lhs rhs
      (concat (Id T V0 V3) t0 t1 t6
        (map_path_concat A T Phi P0 P1 P3 a1 (concat A P1 P2 P3 a2 a3))
        (concat (Id T V0 V3) t1 t2 t6
          (refl ((z ↦ concat T V0 V1 V3 (refl Phi a1) z) : Id T V1 V3 → Id T V0 V3)
            (map_path_concat A T Phi P1 P2 P3 a2 a3))
          (concat (Id T V0 V3) t2 t3 t6
            (refl ((x y z ↦ concat T V0 V1 V3 x (concat T V1 V2 V3 y z))
                : Id T V0 V1 → Id T V1 V2 → Id T V2 V3 → Id T V0 V3) e1 e2 e3)
            (concat (Id T V0 V3) t3 t4 t6
              (ywf_pent T w V0 V1 V2 V3 V4 r0 r1 r2 r3 r4)
              (concat (Id T V0 V3) t4 t5 t6
                (inverse (Id T V0 V3) t5 t4
                  (refl ((x y ↦ concat T V0 V4 V3 x y) : Id T V0 V4 → Id T V4 V3 → Id T V0 V3) e4 e5))
                (inverse (Id T V0 V3) t6 t5 (map_path_concat A T Phi P0 P4 P3 a4 a5)))))))
