export "841-wedge-signatures"

{` Chapter 8 (congp.tex), section "Sums of groups": the paragraph after
   def:wedge and lem:univvee (congp.tex:540).

   For a pointed type B, the book's i^* sends a pointed map f : A1∨A2 →* B
   to (f i1, f i2), where i1 = (i1, refl) and i2 = (i2, g) are the pointed
   structure maps of module 841 (wedge_incl1_pointed, wedge_incl2_pointed)
   and composition is book_pointed_compose.  lem:univvee states that i^* is
   an equivalence (wedge_pointed_universal_property, and the book-notion
   version wedge_restrict_book_equiv).

   Proof: over a varying base point b of B, pointed maps out of the wedge are
   all maps out of the wedge (pointed_map_chosen_target_equiv), i.e. cocones
   (wedge_universal_property); pairs of pointed maps f1, f2 into (B, b) over
   a varying b are also cocones, via (f1, f2, f1_pt⁻¹ · f2_pt)
   (wedge_pointed_pairs_equiv).  The two composites agree, so i^* is a
   fiberwise equivalence (fiberwise_from_total).

   The running text "a pointed function f : A1∨A2 →* B is given by pointed
   functions f1, f2; the identity f1(a1) = f2(a2) which seems to be missing is
   provided by the pointedness" is wedge_pointed_extend: recursion on the
   cocone (f1, f2, f1_pt⁻¹ · f2_pt), pointed through the computation rule;
   wedge_restrict_extend shows i^*(extend(f1, f2)) = (f1, f2), so
   wedge_pointed_extend is the inverse of i^* (wedge_extend_restrict).  The
   computation rules of the wedge are identifications (module 841), so all
   these laws are proved, not judgmental. `}

{` The book's i^* (lem:univvee). `}
def wedge_restrict (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f : BookPointedMap (wedge_pointed A1 A2 W) B)
  : Product (BookPointedMap A1 B) (BookPointedMap A2 B)
  ≔ (book_pointed_compose A1 (wedge_pointed A1 A2 W) B (wedge_incl1_pointed A1 A2 W) f,
     book_pointed_compose A2 (wedge_pointed A1 A2 W) B (wedge_incl2_pointed A1 A2 W) f)

{` Pairs of pointed maps into (T, b) for a varying point b, and cocones. `}
def WedgePointedPairs (A1 A2 : Pointed) (T : Type) : Type
  ≔ Σ T (b ↦ Product (BookPointedMap A1 (T, b)) (BookPointedMap A2 (T, b)))

def wedge_pairs_to_cocone (A1 A2 : Pointed) (T : Type) (u : WedgePointedPairs A1 A2 T) : WedgeCocone A1 A2 T
  ≔ (u .snd .fst .fst, (u .snd .snd .fst,
      concat T (u .snd .fst .fst (A1 .point)) (u .fst) (u .snd .snd .fst (A2 .point))
        (inverse T (u .fst) (u .snd .fst .fst (A1 .point)) (u .snd .fst .snd)) (u .snd .snd .snd)))

def wedge_cocone_to_pairs (A1 A2 : Pointed) (T : Type) (d : WedgeCocone A1 A2 T) : WedgePointedPairs A1 A2 T
  ≔ (d .fst (A1 .point), ((d .fst, refl (d .fst (A1 .point))), (d .snd .fst, d .snd .snd)))

def wedge_pairs_cocone_section (A1 A2 : Pointed) (T : Type) (d : WedgeCocone A1 A2 T)
  : Id (WedgeCocone A1 A2 T) (wedge_pairs_to_cocone A1 A2 T (wedge_cocone_to_pairs A1 A2 T d)) d
  ≔ let x ≔ d .fst (A1 .point) in let y ≔ d .snd .fst (A2 .point) in
    (refl (d .fst), (refl (d .snd .fst),
      concat (Id T x y) (concat T x x y (inverse T x x (refl x)) (d .snd .snd))
        (concat T x x y (refl x) (d .snd .snd)) (d .snd .snd)
        (refl ((r ↦ concat T x x y r (d .snd .snd)) : Id T x x → Id T x y) (inverse_refl T x))
        (concat_1p T x y (d .snd .snd))))

def wedge_pairs_retraction_base (A1 A2 : Pointed) (T : Type) (f1 : A1 .carrier → T) (f2 : A2 .carrier → T)
  (p2 : Id T (f1 (A1 .point)) (f2 (A2 .point)))
  : Id (WedgePointedPairs A1 A2 T)
      (f1 (A1 .point), ((f1, refl (f1 (A1 .point))),
        (f2, concat T (f1 (A1 .point)) (f1 (A1 .point)) (f2 (A2 .point)) (refl (f1 (A1 .point))) p2)))
      (f1 (A1 .point), ((f1, inverse T (f1 (A1 .point)) (f1 (A1 .point)) (refl (f1 (A1 .point)))), (f2, p2)))
  ≔ let x ≔ f1 (A1 .point) in let y ≔ f2 (A2 .point) in
    (refl x, ((refl f1, inverse (Id T x x) (inverse T x x (refl x)) (refl x) (inverse_refl T x)),
      (refl f2, concat_1p T x y p2)))

def wedge_pairs_retraction_aux (A1 A2 : Pointed) (T : Type) (f1 : A1 .carrier → T) (f2 : A2 .carrier → T)
  (b : T) (q : Id T (f1 (A1 .point)) b) (p2 : Id T b (f2 (A2 .point)))
  : Id (WedgePointedPairs A1 A2 T)
      (f1 (A1 .point), ((f1, refl (f1 (A1 .point))), (f2, concat T (f1 (A1 .point)) b (f2 (A2 .point)) q p2)))
      (b, ((f1, inverse T (f1 (A1 .point)) b q), (f2, p2)))
  ≔ J T (f1 (A1 .point))
      (b q ↦ (p2 : Id T b (f2 (A2 .point))) → Id (WedgePointedPairs A1 A2 T)
        (f1 (A1 .point), ((f1, refl (f1 (A1 .point))), (f2, concat T (f1 (A1 .point)) b (f2 (A2 .point)) q p2)))
        (b, ((f1, inverse T (f1 (A1 .point)) b q), (f2, p2))))
      (wedge_pairs_retraction_base A1 A2 T f1 f2) b q p2

def wedge_pairs_retraction (A1 A2 : Pointed) (T : Type) (u : WedgePointedPairs A1 A2 T)
  : Id (WedgePointedPairs A1 A2 T) (wedge_cocone_to_pairs A1 A2 T (wedge_pairs_to_cocone A1 A2 T u)) u
  ≔ let f1 ≔ u .snd .fst .fst in let f2 ≔ u .snd .snd .fst in let b ≔ u .fst in
    let x ≔ f1 (A1 .point) in let p1 ≔ u .snd .fst .snd in let p2 ≔ u .snd .snd .snd in
    concat (WedgePointedPairs A1 A2 T)
      (x, ((f1, refl x), (f2, concat T x b (f2 (A2 .point)) (inverse T b x p1) p2)))
      (b, ((f1, inverse T x b (inverse T b x p1)), (f2, p2)))
      u
      (wedge_pairs_retraction_aux A1 A2 T f1 f2 b (inverse T b x p1) p2)
      (refl b, ((refl f1, inverse_inverse T b x p1), (refl f2, refl p2)))

def wedge_pointed_pairs_equiv (A1 A2 : Pointed) (T : Type)
  : Equiv (WedgePointedPairs A1 A2 T) (WedgeCocone A1 A2 T)
  ≔ quasi_inverse_equiv (WedgePointedPairs A1 A2 T) (WedgeCocone A1 A2 T)
      (wedge_pairs_to_cocone A1 A2 T) (wedge_cocone_to_pairs A1 A2 T)
      (wedge_pairs_retraction A1 A2 T) (wedge_pairs_cocone_section A1 A2 T)

{` i^* over a varying base point. `}
def wedge_restrict_total (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type)
  : Σ T (b ↦ BookPointedMap (wedge_pointed A1 A2 W) (T, b)) → WedgePointedPairs A1 A2 T
  ≔ totalize T (b ↦ BookPointedMap (wedge_pointed A1 A2 W) (T, b))
      (b ↦ Product (BookPointedMap A1 (T, b)) (BookPointedMap A2 (T, b)))
      (b ↦ wedge_restrict A1 A2 W (T, b))

def wsum_restrict_glue_algebra (T : Type) (b x y : T) (p : Id T b x) (q : Id T x y)
  : Id (Id T x y) (concat T x b y (inverse T b x (concat T b x x p (refl x))) (concat T b x y p q)) q
  ≔ concat (Id T x y) (concat T x b y (inverse T b x (concat T b x x p (refl x))) (concat T b x y p q))
      (concat T x b y (inverse T b x p) (concat T b x y p q)) q
      (refl ((r ↦ concat T x b y (inverse T b x r) (concat T b x y p q)) : Id T b x → Id T x y) (concat_p1 T b x p))
      (concat_left_inverse T b x y p q)

def wedge_restrict_total_cocone (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type)
  (u : Σ T (b ↦ BookPointedMap (wedge_pointed A1 A2 W) (T, b)))
  : Id (WedgeCocone A1 A2 T) (wedge_pairs_to_cocone A1 A2 T (wedge_restrict_total A1 A2 W T u))
      (wedge_cocone A1 A2 W T (u .snd .fst))
  ≔ (refl (a ↦ u .snd .fst (W .incl1 a)), (refl (a ↦ u .snd .fst (W .incl2 a)),
      wsum_restrict_glue_algebra T (u .fst) (u .snd .fst (W .incl1 (A1 .point))) (u .snd .fst (W .incl2 (A2 .point)))
        (u .snd .snd) (refl (u .snd .fst) (W .glue))))

def wedge_restrict_total_equiv (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (T : Type)
  : Equiv (Σ T (b ↦ BookPointedMap (wedge_pointed A1 A2 W) (T, b))) (WedgePointedPairs A1 A2 T)
  ≔ let S ≔ Σ T (b ↦ BookPointedMap (wedge_pointed A1 A2 W) (T, b)) in
    let P ≔ WedgePointedPairs A1 A2 T in
    let K ≔ WedgeCocone A1 A2 T in
    let e3 ≔ wedge_pointed_pairs_equiv A1 A2 T in
    equiv_change_map S P
      (compose_equiv S K P
        (compose_equiv S (W .carrier → T) K (pointed_map_chosen_target_equiv (wedge_pointed A1 A2 W) T)
          (wedge_universal_property A1 A2 W T))
        (canonical_inverse_equiv P K e3))
      (wedge_restrict_total A1 A2 W T)
      (u ↦ concat P (equiv_inverse_map P K e3 (wedge_cocone A1 A2 W T (u .snd .fst)))
          (equiv_inverse_map P K e3 (wedge_pairs_to_cocone A1 A2 T (wedge_restrict_total A1 A2 W T u)))
          (wedge_restrict_total A1 A2 W T u)
          (refl (equiv_inverse_map P K e3)
            (inverse K (wedge_pairs_to_cocone A1 A2 T (wedge_restrict_total A1 A2 W T u))
              (wedge_cocone A1 A2 W T (u .snd .fst)) (wedge_restrict_total_cocone A1 A2 W T u)))
          (equiv_retraction P K e3 (wedge_restrict_total A1 A2 W T u)))

{` lem:univvee: for every pointed type B, i^* is an equivalence. `}
def wedge_pointed_universal_property (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  : Equiv (BookPointedMap (wedge_pointed A1 A2 W) B) (Product (BookPointedMap A1 B) (BookPointedMap A2 B))
  ≔ (wedge_restrict A1 A2 W B,
     fiberwise_from_total (B .carrier) (b ↦ BookPointedMap (wedge_pointed A1 A2 W) (B .carrier, b))
       (b ↦ Product (BookPointedMap A1 (B .carrier, b)) (BookPointedMap A2 (B .carrier, b)))
       (b ↦ wedge_restrict A1 A2 W (B .carrier, b))
       (wedge_restrict_total_equiv A1 A2 W (B .carrier) .equiv) (B .point))

def wedge_restrict_book_equiv (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  : BookIsEquiv (BookPointedMap (wedge_pointed A1 A2 W) B) (Product (BookPointedMap A1 B) (BookPointedMap A2 B))
      (wedge_restrict A1 A2 W B)
  ≔ book_equivalence (BookPointedMap (wedge_pointed A1 A2 W) B) (Product (BookPointedMap A1 B) (BookPointedMap A2 B))
      (wedge_pointed_universal_property A1 A2 W B) .equiv

{` Path algebra: a square gives a commuting diagram of composites. `}
def wsum_square_concat_refl (T : Type) (x00 x10 : T) (x20 x21 : Id T x00 x10) (s : Id (Id T x00 x10) x20 x21)
  : Id (Id T x00 x10) (concat T x00 x10 x10 x20 (refl x10)) (concat T x00 x00 x10 (refl x00) x21)
  ≔ concat (Id T x00 x10) (concat T x00 x10 x10 x20 (refl x10)) x21 (concat T x00 x00 x10 (refl x00) x21)
      (concat (Id T x00 x10) (concat T x00 x10 x10 x20 (refl x10)) x20 x21 (concat_p1 T x00 x10 x20) s)
      (inverse (Id T x00 x10) (concat T x00 x00 x10 (refl x00) x21) x21 (concat_1p T x00 x10 x21))

def wsum_square_concat_base (T : Type) (x00 x10 x11 : T) (x12 : Id T x10 x11) (x20 : Id T x00 x10)
  (x21 : Id T x00 x11) (s : Id (Id T) (refl x00) x12 x20 x21)
  : Id (Id T x00 x11) (concat T x00 x10 x11 x20 x12) (concat T x00 x00 x11 (refl x00) x21)
  ≔ J T x10
      (x11 x12 ↦ (x20 : Id T x00 x10) (x21 : Id T x00 x11) (s : Id (Id T) (refl x00) x12 x20 x21)
        → Id (Id T x00 x11) (concat T x00 x10 x11 x20 x12) (concat T x00 x00 x11 (refl x00) x21))
      (wsum_square_concat_refl T x00 x10) x11 x12 x20 x21 s

def wsum_square_concat (T : Type) (x00 x01 : T) (x02 : Id T x00 x01) (x10 x11 : T) (x12 : Id T x10 x11)
  (x20 : Id T x00 x10) (x21 : Id T x01 x11) (s : Id (Id T) x02 x12 x20 x21)
  : Id (Id T x00 x11) (concat T x00 x10 x11 x20 x12) (concat T x00 x01 x11 x02 x21)
  ≔ J T x00
      (x01 x02 ↦ (x10 x11 : T) (x12 : Id T x10 x11) (x20 : Id T x00 x10) (x21 : Id T x01 x11)
        (s : Id (Id T) x02 x12 x20 x21)
        → Id (Id T x00 x11) (concat T x00 x10 x11 x20 x12) (concat T x00 x01 x11 x02 x21))
      (wsum_square_concat_base T x00) x01 x02 x10 x11 x12 x20 x21 s

def wsum_concat_inverse_cancel_right (A : Type) (x y z : A) (r : Id A x y) (p : Id A z y)
  : Id (Id A x y) (concat A x z y (concat A x y z r (inverse A z y p)) p) r
  ≔ calc
      concat A x z y (concat A x y z r (inverse A z y p)) p
      = concat A x y y r (concat A y z y (inverse A z y p) p) by concat_assoc A x y z y r (inverse A z y p) p
      = concat A x y y r (refl y) by refl (concat A x y y r) (concat_inverse_left A z y p)
      = r by concat_p1 A x y r ∎

{` The pointed function determined by two pointed functions: recursion on
   the cocone (f1, f2, f1_pt⁻¹ · f2_pt), pointed by f1_pt and the inverse of
   the computation rule at a1. `}
def wedge_pointed_cocone (A1 A2 : Pointed) (B : Pointed) (f1 : BookPointedMap A1 B) (f2 : BookPointedMap A2 B)
  : WedgeCocone A1 A2 (B .carrier)
  ≔ wedge_pairs_to_cocone A1 A2 (B .carrier) (B .point, (f1, f2))

def wedge_pointed_extend (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f1 : BookPointedMap A1 B) (f2 : BookPointedMap A2 B) : BookPointedMap (wedge_pointed A1 A2 W) B
  ≔ let T ≔ B .carrier in let d ≔ wedge_pointed_cocone A1 A2 B f1 f2 in
    let r ≔ wedge_rec A1 A2 W T d in
    (r, concat T (B .point) (f1 .fst (A1 .point)) (r (W .incl1 (A1 .point))) (f1 .snd)
      (inverse T (r (W .incl1 (A1 .point))) (f1 .fst (A1 .point)) (wedge_rec_incl1 A1 A2 W T d (A1 .point))))

def wedge_restrict_extend_fst (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f1 : BookPointedMap A1 B) (f2 : BookPointedMap A2 B)
  : Id (BookPointedMap A1 B) (wedge_restrict A1 A2 W B (wedge_pointed_extend A1 A2 W B f1 f2) .fst) f1
  ≔ let T ≔ B .carrier in let b ≔ B .point in
    let d ≔ wedge_pointed_cocone A1 A2 B f1 f2 in
    let r ≔ wedge_rec A1 A2 W T d in
    let x ≔ f1 .fst (A1 .point) in let ra ≔ r (W .incl1 (A1 .point)) in
    let e1 ≔ wedge_rec_incl1 A1 A2 W T d (A1 .point) in
    let k ≔ wedge_restrict A1 A2 W B (wedge_pointed_extend A1 A2 W B f1 f2) .fst in
    equiv_inverse_map (Id (BookPointedMap A1 B) k f1) (PointedHomotopy A1 B k f1) (pointed_map_path_equiv A1 B k f1)
      (a ↦ wedge_rec_incl1 A1 A2 W T d a,
       concat (Id T b x)
         (concat T b ra x (concat T b ra ra (concat T b x ra (f1 .snd) (inverse T ra x e1)) (refl ra)) e1)
         (concat T b ra x (concat T b x ra (f1 .snd) (inverse T ra x e1)) e1)
         (f1 .snd)
         (refl ((q ↦ concat T b ra x q e1) : Id T b ra → Id T b x)
           (concat_p1 T b ra (concat T b x ra (f1 .snd) (inverse T ra x e1))))
         (wsum_concat_inverse_cancel_right T b x ra (f1 .snd) e1))

def wedge_extend_glue_algebra (T : Type) (b x y ra rb : T) (p1 : Id T b x) (p2 : Id T b y)
  (e1 : Id T ra x) (e2 : Id T rb y) (q : Id T ra rb)
  (sq : Id (Id T ra y) (concat T ra rb y q e2) (concat T ra x y e1 (concat T x b y (inverse T b x p1) p2)))
  : Id (Id T b y) (concat T b rb y (concat T b ra rb (concat T b x ra p1 (inverse T ra x e1)) q) e2) p2
  ≔ let ext ≔ concat T b x ra p1 (inverse T ra x e1) in
    let c ≔ concat T x b y (inverse T b x p1) p2 in
    calc
      concat T b rb y (concat T b ra rb ext q) e2
      = concat T b ra y ext (concat T ra rb y q e2) by concat_assoc T b ra rb y ext q e2
      = concat T b ra y ext (concat T ra x y e1 c) by refl (concat T b ra y ext) sq
      = concat T b x y (concat T b ra x ext e1) c
        by inverse (Id T b y) (concat T b x y (concat T b ra x ext e1) c) (concat T b ra y ext (concat T ra x y e1 c))
          (concat_assoc T b ra x y ext e1 c)
      = concat T b x y p1 c
        by refl ((s ↦ concat T b x y s c) : Id T b x → Id T b y) (wsum_concat_inverse_cancel_right T b x ra p1 e1)
      = p2 by concat_left_right_inverse T b x y p1 p2 ∎

def wedge_restrict_extend_snd (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f1 : BookPointedMap A1 B) (f2 : BookPointedMap A2 B)
  : Id (BookPointedMap A2 B) (wedge_restrict A1 A2 W B (wedge_pointed_extend A1 A2 W B f1 f2) .snd) f2
  ≔ let T ≔ B .carrier in let b ≔ B .point in
    let d ≔ wedge_pointed_cocone A1 A2 B f1 f2 in
    let r ≔ wedge_rec A1 A2 W T d in
    let x ≔ f1 .fst (A1 .point) in let y ≔ f2 .fst (A2 .point) in
    let ra ≔ r (W .incl1 (A1 .point)) in let rb ≔ r (W .incl2 (A2 .point)) in
    let e1 ≔ wedge_rec_incl1 A1 A2 W T d (A1 .point) in
    let e2 ≔ wedge_rec_incl2 A1 A2 W T d (A2 .point) in
    let c ≔ concat T x b y (inverse T b x (f1 .snd)) (f2 .snd) in
    let k ≔ wedge_restrict A1 A2 W B (wedge_pointed_extend A1 A2 W B f1 f2) .snd in
    equiv_inverse_map (Id (BookPointedMap A2 B) k f2) (PointedHomotopy A2 B k f2) (pointed_map_path_equiv A2 B k f2)
      (a ↦ wedge_rec_incl2 A1 A2 W T d a,
       wedge_extend_glue_algebra T b x y ra rb (f1 .snd) (f2 .snd) e1 e2 (refl r (W .glue))
         (wsum_square_concat T ra x e1 rb y e2 (refl r (W .glue)) c (wedge_rec_beta A1 A2 W T d .snd .snd)))

def wedge_restrict_extend (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f1 : BookPointedMap A1 B) (f2 : BookPointedMap A2 B)
  : Id (Product (BookPointedMap A1 B) (BookPointedMap A2 B))
      (wedge_restrict A1 A2 W B (wedge_pointed_extend A1 A2 W B f1 f2)) (f1, f2)
  ≔ (wedge_restrict_extend_fst A1 A2 W B f1 f2, wedge_restrict_extend_snd A1 A2 W B f1 f2)

{` wedge_pointed_extend is the inverse of i^*. `}
def wedge_extend_restrict (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f : BookPointedMap (wedge_pointed A1 A2 W) B)
  : Id (BookPointedMap (wedge_pointed A1 A2 W) B)
      (wedge_pointed_extend A1 A2 W B (wedge_restrict A1 A2 W B f .fst) (wedge_restrict A1 A2 W B f .snd)) f
  ≔ equivalence_injective (BookPointedMap (wedge_pointed A1 A2 W) B) (Product (BookPointedMap A1 B) (BookPointedMap A2 B))
      (wedge_pointed_universal_property A1 A2 W B)
      (wedge_pointed_extend A1 A2 W B (wedge_restrict A1 A2 W B f .fst) (wedge_restrict A1 A2 W B f .snd)) f
      (wedge_restrict_extend A1 A2 W B (wedge_restrict A1 A2 W B f .fst) (wedge_restrict A1 A2 W B f .snd))

{` Litmus for def:wedge: the wedge of two points is contractible, for every
   wedge signature (each point is joined to a12 by refl, resp. g). `}
def wedge_unit_pointed : Pointed ≔ (Unit, star.)

def wedge_points_contractible (W : WedgeSignature wedge_unit_pointed wedge_unit_pointed)
  : BookIsContr (W .carrier)
  ≔ let X ≔ W .carrier in let a12 ≔ W .incl1 star. in
    (a12, wedge_ind wedge_unit_pointed wedge_unit_pointed W (x ↦ Id X a12 x)
      ((u ↦ match u [ star. ↦ refl a12 ]),
       ((u ↦ match u [ star. ↦ W .glue ]),
        pathover_from_triangle X a12 a12 (W .incl2 star.) (W .glue) (refl a12) (W .glue)
          (concat_1p X a12 (W .incl2 star.) (W .glue)))))
