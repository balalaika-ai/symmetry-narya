export "701-abstract-homomorphisms"

{` Chapter 7 (absgroup.tex), sec:delooping, lem:homomabstrconcr:
   abstr : Hom(G, H) → absHom(abstr G, abstr H) is an equivalence.

   The proof follows the book. For an abstract homomorphism f the family
   C(x) ≔ Σ_{y : BH} Σ_{p : (sh_G = x) → (sh_H = y)} Π_{ω, α} p(α ω) = p(α) f(ω)
   (book juxtaposition: α ω is ω followed by α, i.e. concat ω α) is
   contractible at sh_G (it is a retract of Σ_y (sh_H = y)), hence everywhere
   since BG is connected. Its centre gives the delooping Bg with pointing
   p(refl), and abstr(g) = f. The book leaves deloop ∘ abstr = id to the
   reader: for a homomorphism g, (Bg x, α ↦ Bg_pt · ap_Bg(α)) is another
   element of C(x), so it agrees with the centre, which gives a pointed
   homotopy between the delooping of abstr(g) and Bg. `}

def DeloopCond (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (x : BG G .carrier) (y : BG H .carrier)
  (p : Id (BG G .carrier) (shape G) x → Id (BG H .carrier) (shape H) y) : Type
  ≔ (ω : USym G) (α : Id (BG G .carrier) (shape G) x)
    → Id (Id (BG H .carrier) (shape H) y) (p (concat (BG G .carrier) (shape G) (shape G) x ω α))
        (concat (BG H .carrier) (shape H) (shape H) y (f .fst ω) (p α))

def DeloopFamily (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (x : BG G .carrier) : Type
  ≔ Σ (BG H .carrier) (y ↦ Σ (Id (BG G .carrier) (shape G) x → Id (BG H .carrier) (shape H) y) (p ↦ DeloopCond G H f x y p))

def deloop_cond_prop (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (x : BG G .carrier) (y : BG H .carrier)
  (p : Id (BG G .carrier) (shape G) x → Id (BG H .carrier) (shape H) y) : isProp (DeloopCond G H f x y p)
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let a ≔ shape G in let b ≔ shape H in
    pi_prop (USym G) (ω ↦ (α : Id A a x) → Id (Id B b y) (p (concat A a a x ω α)) (concat B b b y (f .fst ω) (p α)))
      (ω ↦ pi_prop (Id A a x) (α ↦ Id (Id B b y) (p (concat A a a x ω α)) (concat B b b y (f .fst ω) (p α)))
        (α ↦ bg_groupoid H b y (p (concat A a a x ω α)) (concat B b b y (f .fst ω) (p α))))

{` C(sh_G) is a retract of Σ_y (sh_H = y): p ↦ p(refl) and
   q ↦ (α ↦ q f(α)). `}
def deloop_base_cond (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (y : BG H .carrier) (q : Id (BG H .carrier) (shape H) y)
  : DeloopCond G H f (shape G) y (α ↦ concat (BG H .carrier) (shape H) (shape H) y (f .fst α) q)
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let a ≔ shape G in let b ≔ shape H in
    let F ≔ f .fst in
    ω α ↦ calc
      concat B b b y (F (concat A a a a ω α)) q = concat B b b y (concat B b b b (F ω) (F α)) q
        by refl ((r ↦ concat B b b y r q) : Id B b b → Id B b y) (f .snd α ω)
      = concat B b b y (F ω) (concat B b b y (F α) q) by concat_assoc B b b b y (F ω) (F α) q ∎

def deloop_base_from (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (v : Σ (BG H .carrier) (y ↦ Id (BG H .carrier) (shape H) y))
  : DeloopFamily G H f (shape G)
  ≔ (v .fst, (α ↦ concat (BG H .carrier) (shape H) (shape H) (v .fst) (f .fst α) (v .snd), deloop_base_cond G H f (v .fst) (v .snd)))

def deloop_base_to (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (u : DeloopFamily G H f (shape G))
  : Σ (BG H .carrier) (y ↦ Id (BG H .carrier) (shape H) y)
  ≔ (u .fst, u .snd .fst (refl (shape G)))

def deloop_base_retract (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (u : DeloopFamily G H f (shape G))
  : Id (DeloopFamily G H f (shape G)) (deloop_base_from G H f (deloop_base_to G H f u)) u
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let a ≔ shape G in let b ≔ shape H in
    let y ≔ u .fst in let p ≔ u .snd .fst in let h ≔ u .snd .snd in
    (refl y,
     subtype_equal (Id A a a → Id B b y) (DeloopCond G H f a y) (deloop_cond_prop G H f a y)
       (deloop_base_from G H f (deloop_base_to G H f u) .snd) (u .snd)
       (funext (Id A a a) (_ ↦ Id B b y) (α ↦ concat B b b y (f .fst α) (p (refl a))) p
         (α ↦ inverse (Id B b y) (p α) (concat B b b y (f .fst α) (p (refl a)))
           (concat (Id B b y) (p α) (p (concat A a a a α (refl a))) (concat B b b y (f .fst α) (p (refl a)))
             (refl p (inverse (Id A a a) (concat A a a a α (refl a)) α (concat_p1 A a a α)))
             (h α (refl a))))))

def deloop_family_base_contractible (G H : Group) (f : AbstractHom (abstr G) (abstr H))
  : isContr (DeloopFamily G H f (shape G))
  ≔ contractible_retract (Σ (BG H .carrier) (y ↦ Id (BG H .carrier) (shape H) y)) (DeloopFamily G H f (shape G))
      (iscontr_idfrom (BG H .carrier) (shape H)) (deloop_base_from G H f) (deloop_base_to G H f)
      (deloop_base_retract G H f)

{` C(x) is contractible for every x : BG (BG is connected). `}
def deloop_family_contractible (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (x : BG G .carrier)
  : isContr (DeloopFamily G H f x)
  ≔ connected_based_elim native_truncation (BG G .carrier) (bg_connected G) (shape G)
      (z ↦ isContr (DeloopFamily G H f z)) (z ↦ iscontr_isprop (DeloopFamily G H f z))
      (deloop_family_base_contractible G H f) x

def deloop_function (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (x : BG G .carrier) : BG H .carrier
  ≔ deloop_family_contractible G H f x .center .fst

def deloop_paths (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (x : BG G .carrier)
  : Id (BG G .carrier) (shape G) x → Id (BG H .carrier) (shape H) (deloop_function G H f x)
  ≔ deloop_family_contractible G H f x .center .snd .fst

def deloop_point (G H : Group) (f : AbstractHom (abstr G) (abstr H))
  : Id (BG H .carrier) (shape H) (deloop_function G H f (shape G))
  ≔ deloop_paths G H f (shape G) (refl (shape G))

{` The delooping deloop(f) : Hom(G, H). `}
def deloop_hom (G H : Group) (f : AbstractHom (abstr G) (abstr H)) : GroupHom G H
  ≔ mkhom G H (deloop_function G H f, deloop_point G H f)

{` p(λ α) = Bg(λ) p(α), by induction on λ. `}
def deloop_paths_natural (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (x x' : BG G .carrier)
  (l : Id (BG G .carrier) x x') (α : Id (BG G .carrier) (shape G) x)
  : Id (Id (BG H .carrier) (shape H) (deloop_function G H f x'))
      (deloop_paths G H f x' (concat (BG G .carrier) (shape G) x x' α l))
      (concat (BG H .carrier) (shape H) (deloop_function G H f x) (deloop_function G H f x')
        (deloop_paths G H f x α) (refl (deloop_function G H f) l))
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let a ≔ shape G in let b ≔ shape H in
    let Bg ≔ deloop_function G H f in let P ≔ deloop_paths G H f in
    J A x (x' l ↦ Id (Id B b (Bg x')) (P x' (concat A a x x' α l)) (concat B b (Bg x) (Bg x') (P x α) (refl Bg l)))
      (concat (Id B b (Bg x)) (P x (concat A a x x α (refl x))) (P x α) (concat B b (Bg x) (Bg x) (P x α) (refl (Bg x)))
        (refl (P x) (concat_p1 A a x α))
        (inverse (Id B b (Bg x)) (concat B b (Bg x) (Bg x) (P x α) (refl (Bg x))) (P x α) (concat_p1 B b (Bg x) (P x α))))
      x' l

{` The defining property of a delooping: f(ω) · Bg_pt = Bg_pt · Bg(ω)
   (book: p f(ω) = Bg(ω) p). `}
def deloop_square (G H : Group) (f : AbstractHom (abstr G) (abstr H)) (ω : USym G)
  : Id (Id (BG H .carrier) (shape H) (deloop_function G H f (shape G)))
      (concat (BG H .carrier) (shape H) (shape H) (deloop_function G H f (shape G)) (f .fst ω) (deloop_point G H f))
      (concat (BG H .carrier) (shape H) (deloop_function G H f (shape G)) (deloop_function G H f (shape G))
        (deloop_point G H f) (refl (deloop_function G H f) ω))
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let a ≔ shape G in let b ≔ shape H in
    let Bg ≔ deloop_function G H f in let P ≔ deloop_paths G H f in let k ≔ deloop_point G H f in
    let cond ≔ deloop_family_contractible G H f a .center .snd .snd in
    calc
      concat B b b (Bg a) (f .fst ω) k = P a (concat A a a a ω (refl a))
        by inverse (Id B b (Bg a)) (P a (concat A a a a ω (refl a))) (concat B b b (Bg a) (f .fst ω) k) (cond ω (refl a))
      = P a ω by refl (P a) (concat_p1 A a a ω)
      = P a (concat A a a a (refl a) ω) by refl (P a) (inverse (Id A a a) (concat A a a a (refl a) ω) ω (concat_1p A a a ω))
      = concat B b (Bg a) (Bg a) k (refl Bg ω) by deloop_paths_natural G H f a a ω (refl a) ∎

{` abstr(deloop(f)) = f: g is a delooping of f. `}
def deloop_hom_section (G H : Group) (f : AbstractHom (abstr G) (abstr H))
  : Id (AbstractHom (abstr G) (abstr H)) (abstr_hom G H (deloop_hom G H f)) f
  ≔ let B ≔ BG H .carrier in let b ≔ shape H in
    let Bg ≔ deloop_function G H f in let k ≔ deloop_point G H f in let c ≔ Bg (shape G) in
    abstract_hom_ext (abstr G) (abstr H) (abstr_hom G H (deloop_hom G H f)) f
      (ω ↦ let apw ≔ refl Bg ω in let ki ≔ inverse B b c k in
        calc
          concat B b c b k (concat B c c b apw ki) = concat B b c b (concat B b c c k apw) ki
            by inverse (Id B b b) (concat B b c b (concat B b c c k apw) ki) (concat B b c b k (concat B c c b apw ki))
              (concat_assoc B b c c b k apw ki)
          = concat B b c b (concat B b b c (f .fst ω) k) ki
            by refl ((r ↦ concat B b c b r ki) : Id B b c → Id B b b)
              (inverse (Id B b c) (concat B b b c (f .fst ω) k) (concat B b c c k apw) (deloop_square G H f ω))
          = concat B b b b (f .fst ω) (concat B b c b k ki) by concat_assoc B b b c b (f .fst ω) k ki
          = concat B b b b (f .fst ω) (refl b) by refl (concat B b b b (f .fst ω)) (concat_inverse_right B b c k)
          = f .fst ω by concat_p1 B b b (f .fst ω) ∎)

{` For a homomorphism g, the canonical element of C(x) for f = abstr(g). `}
def deloop_canonical_cond (G H : Group) (g : GroupHom G H) (x : BG G .carrier)
  : DeloopCond G H (abstr_hom G H g) x (hom_function G H g x)
      (α ↦ concat (BG H .carrier) (shape H) (hom_function G H g (shape G)) (hom_function G H g x)
        (hom_point G H g) (refl (hom_function G H g) α))
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let a ≔ shape G in let b ≔ shape H in
    let Bg ≔ hom_function G H g in let k ≔ hom_point G H g in let c ≔ Bg a in
    ω α ↦ let apw ≔ refl Bg ω in let apa ≔ refl Bg α in let ki ≔ inverse B b c k in
      inverse (Id B b (Bg x))
        (concat B b b (Bg x) (concat B b c b k (concat B c c b apw ki)) (concat B b c (Bg x) k apa))
        (concat B b c (Bg x) k (refl Bg (concat A a a x ω α)))
        (calc
           concat B b b (Bg x) (concat B b c b k (concat B c c b apw ki)) (concat B b c (Bg x) k apa)
             = concat B b c (Bg x) k (concat B c b (Bg x) (concat B c c b apw ki) (concat B b c (Bg x) k apa))
             by concat_assoc B b c b (Bg x) k (concat B c c b apw ki) (concat B b c (Bg x) k apa)
           = concat B b c (Bg x) k (concat B c c (Bg x) apw (concat B c b (Bg x) ki (concat B b c (Bg x) k apa)))
             by refl (concat B b c (Bg x) k) (concat_assoc B c c b (Bg x) apw ki (concat B b c (Bg x) k apa))
           = concat B b c (Bg x) k (concat B c c (Bg x) apw apa)
             by refl ((r ↦ concat B b c (Bg x) k (concat B c c (Bg x) apw r)) : Id B c (Bg x) → Id B b (Bg x))
               (concat_left_inverse_cancel B b c (Bg x) k apa)
           = concat B b c (Bg x) k (refl Bg (concat A a a x ω α))
             by refl (concat B b c (Bg x) k)
               (inverse (Id B c (Bg x)) (refl Bg (concat A a a x ω α)) (concat B c c (Bg x) apw apa)
                 (map_path_concat A B Bg a a x ω α)) ∎)

def deloop_canonical (G H : Group) (g : GroupHom G H) (x : BG G .carrier) : DeloopFamily G H (abstr_hom G H g) x
  ≔ (hom_function G H g x,
     (α ↦ concat (BG H .carrier) (shape H) (hom_function G H g (shape G)) (hom_function G H g x)
        (hom_point G H g) (refl (hom_function G H g) α),
      deloop_canonical_cond G H g x))

{` deloop(abstr(g)) = g. `}
def deloop_hom_retraction (G H : Group) (g : GroupHom G H)
  : Id (GroupHom G H) (deloop_hom G H (abstr_hom G H g)) g
  ≔ let A ≔ BG G .carrier in let B ≔ BG H .carrier in let a ≔ shape G in let b ≔ shape H in
    let f ≔ abstr_hom G H g in
    let C ≔ deloop_family_contractible G H f in
    let e : (x : A) → Id (DeloopFamily G H f x) (C x .center) (deloop_canonical G H g x)
      ≔ x ↦ inverse (DeloopFamily G H f x) (deloop_canonical G H g x) (C x .center) (C x .contract (deloop_canonical G H g x)) in
    let Bd ≔ deloop_function G H f in let Bg ≔ hom_function G H g in
    let ea ≔ e a in
    let tr : Id (Id B b (Bg a)) (concat B b (Bd a) (Bg a) (deloop_point G H f) (ea .fst))
               (concat B b (Bg a) (Bg a) (hom_point G H g) (refl Bg (refl a)))
      ≔ pathover_transport_equiv B (y ↦ Id B b y) (Bd a) (Bg a) (ea .fst) (deloop_point G H f)
          (concat B b (Bg a) (Bg a) (hom_point G H g) (refl Bg (refl a)))
          .map (ea .snd .fst (refl (refl a))) in
    let coh : Id (Id B b (Bg a)) (concat B b (Bd a) (Bg a) (deloop_point G H f) (ea .fst)) (hom_point G H g)
      ≔ concat (Id B b (Bg a)) (concat B b (Bd a) (Bg a) (deloop_point G H f) (ea .fst))
          (concat B b (Bg a) (Bg a) (hom_point G H g) (refl (Bg a))) (hom_point G H g)
          tr (concat_p1 B b (Bg a) (hom_point G H g)) in
    equiv_inverse_map (Id (GroupHom G H) (deloop_hom G H f) g)
      (PointedHomotopy (BG G) (BG H) (hom_B G H (deloop_hom G H f)) (hom_B G H g))
      (group_hom_path_equiv G H (deloop_hom G H f) g) ((x ↦ e x .fst), coh)

{` lem:homomabstrconcr. `}
def abstr_hom_book_equiv (G H : Group) : BookEquiv (GroupHom G H) (AbstractHom (abstr G) (abstr H))
  ≔ book_quasi_inverse_equiv (GroupHom G H) (AbstractHom (abstr G) (abstr H)) (abstr_hom G H) (deloop_hom G H)
      (deloop_hom_retraction G H) (deloop_hom_section G H)

def abstr_hom_is_equiv (G H : Group) : BookIsEquiv (GroupHom G H) (AbstractHom (abstr G) (abstr H)) (abstr_hom G H)
  ≔ abstr_hom_book_equiv G H .equiv

def abstr_hom_equiv (G H : Group) : Equiv (GroupHom G H) (AbstractHom (abstr G) (abstr H))
  ≔ quasi_inverse_equiv (GroupHom G H) (AbstractHom (abstr G) (abstr H)) (abstr_hom G H) (deloop_hom G H)
      (deloop_hom_retraction G H) (deloop_hom_section G H)
