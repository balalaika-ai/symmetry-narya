export "420-group-products-abelian"
export "406-symmetric-group-three"

{` Chapter 4, rem:whatAREabeliangroups (group.tex 759-777): G is abelian iff
   the fold map BG ∨ BG →* BG factors through the inclusion BG ∨ BG →* BG × BG,
   and the type of such factorizations is a proposition equivalent to isAb(G).

   Narya has no higher inductive types, so the one-point union X ∨ Y of
   def:wedge (the pushout of X ← 1 → Y) is a signature record with its
   dependent induction principle and its computation rule as an
   identification (PLAN rule 3a, as CircleSignature); every statement below
   holds for every inhabitant. `}

{` General path algebra. `}
def cancel_inverse_right_general (A : Type) (x y z : A) (r : Id A x y) (p : Id A z y)
  : Id (Id A x y) (concat A x z y (concat A x y z r (inverse A z y p)) p) r
  ≔ calc
      concat A x z y (concat A x y z r (inverse A z y p)) p
      = concat A x y y r (concat A y z y (inverse A z y p) p) by concat_assoc A x y z y r (inverse A z y p) p
      = concat A x y y r (refl y) by refl (concat A x y y r) (concat_inverse_left A z y p)
      = r by concat_p1 A x y r ∎

def cancel_right_general (A : Type) (x y z : A) (r : Id A x y) (p : Id A y z)
  : Id (Id A x y) (concat A x z y (concat A x y z r p) (inverse A y z p)) r
  ≔ calc
      concat A x z y (concat A x y z r p) (inverse A y z p)
      = concat A x y y r (concat A y z y p (inverse A y z p)) by concat_assoc A x y z y r p (inverse A y z p)
      = concat A x y y r (refl y) by refl (concat A x y y r) (concat_inverse_right A y z p)
      = r by concat_p1 A x y r ∎

def concat_inverse_cancel_left (A : Type) (x y z : A) (c : Id A x y) (q : Id A x z)
  : Id (Id A x z) (concat A x y z c (concat A y x z (inverse A x y c) q)) q
  ≔ calc
      concat A x y z c (concat A y x z (inverse A x y c) q)
      = concat A x x z (concat A x y x c (inverse A x y c)) q
        by inverse (Id A x z) (concat A x x z (concat A x y x c (inverse A x y c)) q)
          (concat A x y z c (concat A y x z (inverse A x y c) q)) (concat_assoc A x y x z c (inverse A x y c) q)
      = concat A x x z (refl x) q by refl ((r ↦ concat A x x z r q) : Id A x x → Id A x z) (concat_inverse_right A x y c)
      = q by concat_1p A x z q ∎

{` Ω of maps that agree up to a homotopy H: the pointing path changes by H. `}
def loops_homotopy (A C : Type) (a : A) (c : C) (f f' : A → C) (H : (x : A) → Id C (f x) (f' x))
  (fp : Id C c (f a)) (l : Id A a a)
  : Id (Id C c c) (pointed_loop_conjugate C c (f a) fp (refl f l))
      (pointed_loop_conjugate C c (f' a) (concat C c (f a) (f' a) fp (H a)) (refl f' l))
  ≔ let k ≔ H a in let α ≔ refl f l in let β ≔ refl f' l in
    let fa ≔ f a in let ga ≔ f' a in
    let nat : Id (Id C fa ga) (concat C fa fa ga α k) (concat C fa ga ga k β) ≔ naturality A C f f' H a a l in
    calc
      concat C c fa c fp (concat C fa fa c α (inverse C c fa fp))
      = concat C c fa c fp (concat C fa fa c (concat C fa ga fa (concat C fa ga ga k β) (inverse C fa ga k)) (inverse C c fa fp))
        by refl ((r ↦ concat C c fa c fp (concat C fa fa c r (inverse C c fa fp))) : Id C fa fa → Id C c c)
          (calc
            α = concat C fa ga fa (concat C fa fa ga α k) (inverse C fa ga k)
              by inverse (Id C fa fa) (concat C fa ga fa (concat C fa fa ga α k) (inverse C fa ga k)) α
                (cancel_right_general C fa fa ga α k)
            = concat C fa ga fa (concat C fa ga ga k β) (inverse C fa ga k)
              by refl ((r ↦ concat C fa ga fa r (inverse C fa ga k)) : Id C fa ga → Id C fa fa) nat ∎)
      = concat C c fa c fp (concat C fa ga c (concat C fa ga ga k β) (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp)))
        by refl (concat C c fa c fp)
          (concat_assoc C fa ga fa c (concat C fa ga ga k β) (inverse C fa ga k) (inverse C c fa fp))
      = concat C c fa c fp (concat C fa ga c k (concat C ga ga c β (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp))))
        by refl (concat C c fa c fp)
          (concat_assoc C fa ga ga c k β (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp)))
      = concat C c ga c (concat C c fa ga fp k) (concat C ga ga c β (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp)))
        by inverse (Id C c c)
          (concat C c ga c (concat C c fa ga fp k) (concat C ga ga c β (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp))))
          (concat C c fa c fp (concat C fa ga c k (concat C ga ga c β (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp)))))
          (concat_assoc C c fa ga c fp k (concat C ga ga c β (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp))))
      = concat C c ga c (concat C c fa ga fp k) (concat C ga ga c β (inverse C c ga (concat C c fa ga fp k)))
        by refl ((r ↦ concat C c ga c (concat C c fa ga fp k) (concat C ga ga c β r)) : Id C ga c → Id C c c)
          (inverse (Id C ga c) (inverse C c ga (concat C c fa ga fp k))
            (concat C ga fa c (inverse C fa ga k) (inverse C c fa fp)) (inverse_concat C c fa ga fp k)) ∎

{` If the pointing path is H(a)⁻¹, then Ω f = Ω f' on the nose. `}
def loops_homotopy_inverse (A C : Type) (a : A) (f f' : A → C) (H : (x : A) → Id C (f x) (f' x)) (l : Id A a a)
  : Id (Id C (f' a) (f' a)) (pointed_loop_conjugate C (f' a) (f a) (inverse C (f a) (f' a) (H a)) (refl f l)) (refl f' l)
  ≔ calc
      pointed_loop_conjugate C (f' a) (f a) (inverse C (f a) (f' a) (H a)) (refl f l)
      = pointed_loop_conjugate C (f' a) (f' a) (concat C (f' a) (f a) (f' a) (inverse C (f a) (f' a) (H a)) (H a)) (refl f' l)
        by loops_homotopy A C a (f' a) f f' H (inverse C (f a) (f' a) (H a)) l
      = pointed_loop_conjugate C (f' a) (f' a) (refl (f' a)) (refl f' l)
        by refl ((r ↦ pointed_loop_conjugate C (f' a) (f' a) r (refl f' l)) : Id C (f' a) (f' a) → Id C (f' a) (f' a))
          (concat_inverse_left C (f a) (f' a) (H a))
      = refl f' l by loop_conjugate_at_refl C (f' a) (refl f' l) ∎

{` Sections of a family of sets over a connected type, from a point of the
   fiber over a fixed by all loops. `}
def section_weakly_constant (A : Type) (a : A) (P : A → Type) (p0 : P a)
  (fix : (l : Id A a a) → Id (P a) (transport A P a a l p0) p0) (x : A)
  : WeaklyConstant (Id A a x) (P x) (r ↦ transport A P a x r p0)
  ≔ r r' ↦ calc
      transport A P a x r p0
      = transport A P a x (concat A a a x (concat A a x a r (inverse A a x r')) r') p0
        by refl ((q ↦ transport A P a x q p0) : Id A a x → P x)
          (inverse (Id A a x) (concat A a a x (concat A a x a r (inverse A a x r')) r') r
            (cancel_inverse_right_general A a x a r r'))
      = transport A P a x r' (transport A P a a (concat A a x a r (inverse A a x r')) p0)
        by transport_concat A P a a x (concat A a x a r (inverse A a x r')) r' p0
      = transport A P a x r' p0 by refl (transport A P a x r') (fix (concat A a x a r (inverse A a x r'))) ∎

def connected_set_section (A : Type) (a : A) (hA : Connected A) (P : A → Type) (hP : (x : A) → isSet (P x))
  (p0 : P a) (fix : (l : Id A a a) → Id (P a) (transport A P a a l p0) p0) : (x : A) → P x
  ≔ x ↦ weakly_constant_rec (Id A a x) (P x) (r ↦ transport A P a x r p0) (hP x)
      (section_weakly_constant A a P p0 fix x) (hA .snd a x)

def connected_set_section_beta (A : Type) (a : A) (hA : Connected A) (P : A → Type) (hP : (x : A) → isSet (P x))
  (p0 : P a) (fix : (l : Id A a a) → Id (P a) (transport A P a a l p0) p0)
  : Id (P a) (connected_set_section A a hA P hP p0 fix a) p0
  ≔ concat (P a) (connected_set_section A a hA P hP p0 fix a) (transport A P a a (refl a) p0) p0
      (weakly_constant_rec_value (Id A a a) (P a) (r ↦ transport A P a a r p0) (hP a)
        (section_weakly_constant A a P p0 fix a) (hA .snd a a) (refl a))
      (transport_refl A P a p0)

{` Pointed maps from a connected type into a groupoid are determined by
   their action on loops. `}
def conj_fix_algebra (B : Type) (b c d : B) (u : Id B b c) (v : Id B b d) (α : Id B c c) (β : Id B d d)
  (E : Id (Id B b b) (concat B b c b u (concat B c c b α (inverse B b c u))) (concat B b d b v (concat B d d b β (inverse B b d v))))
  : Id (Id B c d) (concat B c c d (inverse B c c α) (concat B c d d (concat B c b d (inverse B b c u) v) β))
      (concat B c b d (inverse B b c u) v)
  ≔ let w ≔ concat B c b d (inverse B b c u) v in
    let F : Id (Id B c d) (concat B c c d α w) (concat B c b d (inverse B b c u) (concat B b d d v β))
      ≔ calc
          concat B c c d α w
          = concat B c b d (inverse B b c u) (concat B b c d u (concat B c c d α w))
            by inverse (Id B c d) (concat B c b d (inverse B b c u) (concat B b c d u (concat B c c d α w)))
              (concat B c c d α w) (concat_left_inverse B b c d u (concat B c c d α w))
          = concat B c b d (inverse B b c u) (concat B b b d (concat B b c b u (concat B c c b α (inverse B b c u))) v)
            by refl (concat B c b d (inverse B b c u))
              (calc
                concat B b c d u (concat B c c d α w)
                = concat B b c d u (concat B c b d (concat B c c b α (inverse B b c u)) v)
                  by refl (concat B b c d u)
                    (inverse (Id B c d) (concat B c b d (concat B c c b α (inverse B b c u)) v) (concat B c c d α w)
                      (concat_assoc B c c b d α (inverse B b c u) v))
                = concat B b b d (concat B b c b u (concat B c c b α (inverse B b c u))) v
                  by inverse (Id B b d) (concat B b b d (concat B b c b u (concat B c c b α (inverse B b c u))) v)
                    (concat B b c d u (concat B c b d (concat B c c b α (inverse B b c u)) v))
                    (concat_assoc B b c b d u (concat B c c b α (inverse B b c u)) v) ∎)
          = concat B c b d (inverse B b c u) (concat B b b d (concat B b d b v (concat B d d b β (inverse B b d v))) v)
            by refl ((r ↦ concat B c b d (inverse B b c u) (concat B b b d r v)) : Id B b b → Id B c d) E
          = concat B c b d (inverse B b c u) (concat B b d d v β)
            by refl (concat B c b d (inverse B b c u))
              (calc
                concat B b b d (concat B b d b v (concat B d d b β (inverse B b d v))) v
                = concat B b d d v (concat B d b d (concat B d d b β (inverse B b d v)) v)
                  by concat_assoc B b d b d v (concat B d d b β (inverse B b d v)) v
                = concat B b d d v β by refl (concat B b d d v) (cancel_inverse_right_general B d d b β v) ∎) ∎ in
    calc
      concat B c c d (inverse B c c α) (concat B c d d w β)
      = concat B c c d (inverse B c c α) (concat B c b d (inverse B b c u) (concat B b d d v β))
        by refl (concat B c c d (inverse B c c α)) (concat_assoc B c b d d (inverse B b c u) v β)
      = concat B c c d (inverse B c c α) (concat B c c d α w)
        by refl (concat B c c d (inverse B c c α))
          (inverse (Id B c d) (concat B c c d α w) (concat B c b d (inverse B b c u) (concat B b d d v β)) F)
      = w by concat_left_inverse B c c d α w ∎

def pointed_maps_eq_from_loops (A B : Pointed) (hA : Connected (A .carrier)) (hB : isGroupoid (B .carrier))
  (f g : BookPointedMap A B) (h : (l : Loop A) → Id (Loop B) (loops_map A B f l) (loops_map A B g l))
  : Id (BookPointedMap A B) f g
  ≔ let X ≔ A .carrier in let Y ≔ B .carrier in let a ≔ A .point in let b ≔ B .point in
    let P ≔ ((x ↦ Id Y (f .fst x) (g .fst x)) : X → Type) in
    let p0 ≔ concat Y (f .fst a) b (g .fst a) (inverse Y b (f .fst a) (f .snd)) (g .snd) in
    let fix : (l : Id X a a) → Id (P a) (transport X P a a l p0) p0
      ≔ l ↦ concat (P a) (transport X P a a l p0)
          (concat Y (f .fst a) (f .fst a) (g .fst a) (inverse Y (f .fst a) (f .fst a) (refl (f .fst) l))
            (concat Y (f .fst a) (g .fst a) (g .fst a) p0 (refl (g .fst) l)))
          p0
          (transport_path_family X Y (f .fst) (g .fst) a a l p0)
          (conj_fix_algebra Y b (f .fst a) (g .fst a) (f .snd) (g .snd) (refl (f .fst) l) (refl (g .fst) l) (h l)) in
    let s ≔ connected_set_section X a hA P (x ↦ hB (f .fst x) (g .fst x)) p0 fix in
    equiv_inverse_map (Id (BookPointedMap A B) f g) (PointedHomotopy A B f g) (pointed_map_path_equiv A B f g)
      (s, concat (Id Y b (g .fst a)) (concat Y b (f .fst a) (g .fst a) (f .snd) (s a))
        (concat Y b (f .fst a) (g .fst a) (f .snd) p0) (g .snd)
        (refl (concat Y b (f .fst a) (g .fst a) (f .snd))
          (connected_set_section_beta X a hA P (x ↦ hB (f .fst x) (g .fst x)) p0 fix))
        (concat_inverse_cancel_left Y b (f .fst a) (g .fst a) (f .snd) (g .snd)))

{` For abelian G, a symmetry c of sh_G extends to a family Π(x : BG) x = x
   with value c at sh_G (c is central); consequently pointed maps into BG
   are equal as soon as their underlying functions are homotopic. `}
def central_fix (G : Group) (hab : IsAbelian G) (c : USym G) (l : USym G)
  : Id (USym G) (transport (BG G .carrier) (x ↦ Id (BG G .carrier) x x) (shape G) (shape G) l c) c
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in
    concat (Id B b b) (transport B (x ↦ Id B x x) b b l c)
      (concat B b b b (inverse B b b l) (concat B b b b c l)) c
      (transport_path_family B B (identity B) (identity B) b b l c)
      (calc
        concat B b b b (inverse B b b l) (concat B b b b c l)
        = concat B b b b (inverse B b b l) (concat B b b b l c) by refl (concat B b b b (inverse B b b l)) (hab l c)
        = c by concat_left_inverse B b b b l c ∎)

def central_family (G : Group) (hab : IsAbelian G) (c : USym G) : (x : BG G .carrier) → Id (BG G .carrier) x x
  ≔ connected_set_section (BG G .carrier) (shape G) (bg_connected G) (x ↦ Id (BG G .carrier) x x)
      (x ↦ bg_groupoid G x x) c (central_fix G hab c)

def central_family_beta (G : Group) (hab : IsAbelian G) (c : USym G)
  : Id (USym G) (central_family G hab c (shape G)) c
  ≔ connected_set_section_beta (BG G .carrier) (shape G) (bg_connected G) (x ↦ Id (BG G .carrier) x x)
      (x ↦ bg_groupoid G x x) c (central_fix G hab c)

def abelian_ext_algebra (B : Type) (b e d : B) (F : Id B b e) (K : Id B e d) (Fp : Id B b d)
  : Id (Id B b d)
      (concat B b e d F (concat B e d d K (concat B d b d (inverse B b d Fp)
        (concat B b b d (inverse B b b (concat B b d b (concat B b e d F K) (inverse B b d Fp))) Fp))))
      Fp
  ≔ let c ≔ concat B b d b (concat B b e d F K) (inverse B b d Fp) in
    calc
      concat B b e d F (concat B e d d K (concat B d b d (inverse B b d Fp) (concat B b b d (inverse B b b c) Fp)))
      = concat B b d d (concat B b e d F K) (concat B d b d (inverse B b d Fp) (concat B b b d (inverse B b b c) Fp))
        by inverse (Id B b d)
          (concat B b d d (concat B b e d F K) (concat B d b d (inverse B b d Fp) (concat B b b d (inverse B b b c) Fp)))
          (concat B b e d F (concat B e d d K (concat B d b d (inverse B b d Fp) (concat B b b d (inverse B b b c) Fp))))
          (concat_assoc B b e d d F K (concat B d b d (inverse B b d Fp) (concat B b b d (inverse B b b c) Fp)))
      = concat B b b d c (concat B b b d (inverse B b b c) Fp)
        by inverse (Id B b d) (concat B b b d c (concat B b b d (inverse B b b c) Fp))
          (concat B b d d (concat B b e d F K) (concat B d b d (inverse B b d Fp) (concat B b b d (inverse B b b c) Fp)))
          (concat_assoc B b d b d (concat B b e d F K) (inverse B b d Fp) (concat B b b d (inverse B b b c) Fp))
      = Fp by concat_inverse_cancel_left B b b d c Fp ∎

def abelian_pointed_maps_ext (A : Pointed) (G : Group) (hab : IsAbelian G) (f f' : BookPointedMap A (BG G))
  (H0 : (a : A .carrier) → Id (BG G .carrier) (f .fst a) (f' .fst a)) : Id (BookPointedMap A (BG G)) f f'
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in let a0 ≔ A .point in
    let c ≔ concat B b (f' .fst a0) b (concat B b (f .fst a0) (f' .fst a0) (f .snd) (H0 a0)) (inverse B b (f' .fst a0) (f' .snd)) in
    let z ≔ central_family G hab (inverse B b b c) in
    let H : (a : A .carrier) → Id B (f .fst a) (f' .fst a)
      ≔ a ↦ concat B (f .fst a) (f' .fst a) (f' .fst a) (H0 a) (z (f' .fst a)) in
    let zpt : Id (Id B (f' .fst a0) (f' .fst a0)) (z (f' .fst a0))
        (concat B (f' .fst a0) b (f' .fst a0) (inverse B b (f' .fst a0) (f' .snd))
          (concat B b b (f' .fst a0) (inverse B b b c) (f' .snd)))
      ≔ calc
          z (f' .fst a0) = transport B (x ↦ Id B x x) b (f' .fst a0) (f' .snd) (z b)
            by inverse (Id B (f' .fst a0) (f' .fst a0)) (transport B (x ↦ Id B x x) b (f' .fst a0) (f' .snd) (z b))
              (z (f' .fst a0))
              (pathover_transport_equiv B (x ↦ Id B x x) b (f' .fst a0) (f' .snd) (z b) (z (f' .fst a0)) .map
                (refl z (f' .snd)))
          = concat B (f' .fst a0) b (f' .fst a0) (inverse B b (f' .fst a0) (f' .snd))
              (concat B b b (f' .fst a0) (z b) (f' .snd))
            by transport_path_family B B (identity B) (identity B) b (f' .fst a0) (f' .snd) (z b)
          = concat B (f' .fst a0) b (f' .fst a0) (inverse B b (f' .fst a0) (f' .snd))
              (concat B b b (f' .fst a0) (inverse B b b c) (f' .snd))
            by refl ((r ↦ concat B (f' .fst a0) b (f' .fst a0) (inverse B b (f' .fst a0) (f' .snd))
                (concat B b b (f' .fst a0) r (f' .snd))) : Id B b b → Id B (f' .fst a0) (f' .fst a0))
              (central_family_beta G hab (inverse B b b c)) ∎ in
    equiv_inverse_map (Id (BookPointedMap A (BG G)) f f') (PointedHomotopy A (BG G) f f') (pointed_map_path_equiv A (BG G) f f')
      (H, concat (Id B b (f' .fst a0))
        (concat B b (f .fst a0) (f' .fst a0) (f .snd) (H a0))
        (concat B b (f .fst a0) (f' .fst a0) (f .snd)
          (concat B (f .fst a0) (f' .fst a0) (f' .fst a0) (H0 a0)
            (concat B (f' .fst a0) b (f' .fst a0) (inverse B b (f' .fst a0) (f' .snd))
              (concat B b b (f' .fst a0) (inverse B b b c) (f' .snd)))))
        (f' .snd)
        (refl ((r ↦ concat B b (f .fst a0) (f' .fst a0) (f .snd) (concat B (f .fst a0) (f' .fst a0) (f' .fst a0) (H0 a0) r))
            : Id B (f' .fst a0) (f' .fst a0) → Id B b (f' .fst a0)) zpt)
        (abelian_ext_algebra B b (f .fst a0) (f' .fst a0) (f .snd) (H0 a0) (f' .snd)))

{` For abelian G, conjugation in USym G is trivial. `}
def abelian_loop_conjugate_trivial (G : Group) (hab : IsAbelian G) (c x : USym G)
  : Id (USym G) (pointed_loop_conjugate (BG G .carrier) (shape G) (shape G) c x) x
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in
    calc
      concat B b b b c (concat B b b b x (inverse B b b c))
      = concat B b b b c (concat B b b b (inverse B b b c) x) by refl (concat B b b b c) (hab (inverse B b b c) x)
      = x by concat_inverse_cancel_left B b b b c x ∎

def conjugate_conjugate_inverse (B : Type) (b : B) (c q : Id B b b)
  : Id (Id B b b) (pointed_loop_conjugate B b b c (pointed_loop_conjugate B b b (inverse B b b c) q)) q
  ≔ let ci ≔ inverse B b b c in
    calc
      concat B b b b c (concat B b b b (concat B b b b ci (concat B b b b q (inverse B b b ci))) ci)
      = concat B b b b c (concat B b b b (concat B b b b ci (concat B b b b q c)) ci)
        by refl ((r ↦ concat B b b b c (concat B b b b (concat B b b b ci (concat B b b b q r)) ci)) : Id B b b → Id B b b)
          (inverse_inverse B b b c)
      = concat B b b b c (concat B b b b ci (concat B b b b (concat B b b b q c) ci))
        by refl (concat B b b b c) (concat_assoc B b b b b ci (concat B b b b q c) ci)
      = concat B b b b (concat B b b b q c) ci by concat_inverse_cancel_left B b b b c (concat B b b b (concat B b b b q c) ci)
      = q by cancel_right_general B b b b q c ∎

{` Loops of a product of pointed types are pairs of loops. `}
def product_loop_ext (A B : Type) (a : A) (b : B) (r s : Id (Product A B) (a, b) (a, b))
  (p : Id (Id A a a) (r .fst) (s .fst)) (q : Id (Id B b b) (r .snd) (s .snd)) : Id (Id (Product A B) (a, b) (a, b)) r s
  ≔ equivalence_injective (Id (Product A B) (a, b) (a, b)) (Product (Id A a a) (Id B b b))
      (quasi_inverse_equiv (Id (Product A B) (a, b) (a, b)) (Product (Id A a a) (Id B b b))
        (t ↦ (t .fst, t .snd)) (t ↦ (t .fst, t .snd)) (t ↦ refl t) (t ↦ refl t))
      r s (p, q)

def product_loop_concat_fst (A B : Type) (a : A) (b : B) (r s : Id (Product A B) (a, b) (a, b))
  : Id (Id A a a) (concat (Product A B) (a, b) (a, b) (a, b) r s .fst) (concat A a a a (r .fst) (s .fst))
  ≔ map_path_concat (Product A B) A (u ↦ u .fst) (a, b) (a, b) (a, b) r s

def product_loop_concat_snd (A B : Type) (a : A) (b : B) (r s : Id (Product A B) (a, b) (a, b))
  : Id (Id B b b) (concat (Product A B) (a, b) (a, b) (a, b) r s .snd) (concat B b b b (r .snd) (s .snd))
  ≔ map_path_concat (Product A B) B (u ↦ u .snd) (a, b) (a, b) (a, b) r s

{` The one-point union as a signature. `}
def OnePointUnionBoundary (X Y : Pointed) (W : Type) (i : X .carrier → W) (j : Y .carrier → W)
  (g : Id W (i (X .point)) (j (Y .point))) (P : W → Type) : Type
  ≔ Σ ((x : X .carrier) → P (i x)) (l ↦ Σ ((y : Y .carrier) → P (j y)) (r ↦ Id P g (l (X .point)) (r (Y .point))))

def one_point_union_evaluate (X Y : Pointed) (W : Type) (i : X .carrier → W) (j : Y .carrier → W)
  (g : Id W (i (X .point)) (j (Y .point))) (P : W → Type) (f : (w : W) → P w) : OnePointUnionBoundary X Y W i j g P
  ≔ (x ↦ f (i x), (y ↦ f (j y), refl f g))

def OnePointUnionSignature (X Y : Pointed) : Type ≔ sig (
  carrier : Type,
  inl : X .carrier → carrier,
  inr : Y .carrier → carrier,
  glue : Id carrier (inl (X .point)) (inr (Y .point)),
  induction : (P : carrier → Type) (d : OnePointUnionBoundary X Y carrier inl inr glue P)
    → Σ ((w : carrier) → P w)
        (f ↦ Id (OnePointUnionBoundary X Y carrier inl inr glue P) (one_point_union_evaluate X Y carrier inl inr glue P f) d))

def one_point_union_pointed (X Y : Pointed) (W : OnePointUnionSignature X Y) : Pointed ≔ (W .carrier, W .inl (X .point))

def wedge_inl_pointed (X Y : Pointed) (W : OnePointUnionSignature X Y) : BookPointedMap X (one_point_union_pointed X Y W)
  ≔ (W .inl, refl (W .inl (X .point)))

def wedge_inr_pointed (X Y : Pointed) (W : OnePointUnionSignature X Y) : BookPointedMap Y (one_point_union_pointed X Y W)
  ≔ (W .inr, W .glue)

def one_point_union_rec (X Y : Pointed) (W : OnePointUnionSignature X Y) (Z : Type) (l : X .carrier → Z) (r : Y .carrier → Z)
  (p : Id Z (l (X .point)) (r (Y .point))) : W .carrier → Z
  ≔ W .induction (_ ↦ Z) (l, (r, p)) .fst

def one_point_union_rec_beta (X Y : Pointed) (W : OnePointUnionSignature X Y) (Z : Type) (l : X .carrier → Z) (r : Y .carrier → Z)
  (p : Id Z (l (X .point)) (r (Y .point)))
  : Id (OnePointUnionBoundary X Y (W .carrier) (W .inl) (W .inr) (W .glue) (_ ↦ Z))
      (one_point_union_evaluate X Y (W .carrier) (W .inl) (W .inr) (W .glue) (_ ↦ Z) (one_point_union_rec X Y W Z l r p)) (l, (r, p))
  ≔ W .induction (_ ↦ Z) (l, (r, p)) .snd

{` The one-point union of connected types is connected. `}
def one_point_union_connected (X Y : Pointed) (W : OnePointUnionSignature X Y) (hX : Connected (X .carrier)) (hY : Connected (Y .carrier))
  : Connected (W .carrier)
  ≔ let w0 ≔ W .inl (X .point) in
    let P ≔ ((w ↦ Mere (Id (W .carrier) w0 w)) : W .carrier → Type) in
    let l : (x : X .carrier) → P (W .inl x)
      ≔ x ↦ mere_rec (Id (X .carrier) (X .point) x) (P (W .inl x)) (mere_isprop (Id (W .carrier) w0 (W .inl x)))
          (p ↦ mere (Id (W .carrier) w0 (W .inl x)) (refl (W .inl) p)) (hX .snd (X .point) x) in
    let r : (y : Y .carrier) → P (W .inr y)
      ≔ y ↦ mere_rec (Id (Y .carrier) (Y .point) y) (P (W .inr y)) (mere_isprop (Id (W .carrier) w0 (W .inr y)))
          (p ↦ mere (Id (W .carrier) w0 (W .inr y))
            (concat (W .carrier) w0 (W .inr (Y .point)) (W .inr y) (W .glue) (refl (W .inr) p)))
          (hY .snd (Y .point) y) in
    based_to_connected (W .carrier) w0
      (W .induction P (l, (r,
        pathover_of_eq (W .carrier) P w0 (W .inr (Y .point)) (W .glue) (l (X .point)) (r (Y .point))
          (mere_isprop (Id (W .carrier) w0 (W .inr (Y .point)))
            (transport (W .carrier) P w0 (W .inr (Y .point)) (W .glue) (l (X .point))) (r (Y .point)))))
      .fst)

{` Pointed maps out of the wedge are determined by their restrictions. `}
def wedge_glue_algebra (Z : Type) (z0 a a' d d' : Z) (kp : Id Z z0 a) (kp' : Id Z z0 a')
  (g1 : Id Z a d) (g2 : Id Z a' d') (q1 : Id Z a a') (q2 : Id Z d d')
  (c1 : Id (Id Z z0 a') (concat Z z0 a a' (concat Z z0 a a kp (refl a)) q1) (concat Z z0 a' a' kp' (refl a')))
  (c2 : Id (Id Z z0 d') (concat Z z0 d d' (concat Z z0 a d kp g1) q2) (concat Z z0 a' d' kp' g2))
  : Id (Id Z d d') (concat Z d a d' (inverse Z a d g1) (concat Z a a' d' q1 g2)) q2
  ≔ let c1' : Id (Id Z z0 a') (concat Z z0 a a' kp q1) kp'
      ≔ calc
          concat Z z0 a a' kp q1 = concat Z z0 a a' (concat Z z0 a a kp (refl a)) q1
            by refl ((r ↦ concat Z z0 a a' r q1) : Id Z z0 a → Id Z z0 a')
              (inverse (Id Z z0 a) (concat Z z0 a a kp (refl a)) kp (concat_p1 Z z0 a kp))
          = concat Z z0 a' a' kp' (refl a') by c1
          = kp' by concat_p1 Z z0 a' kp' ∎ in
    let c3 : Id (Id Z z0 d') (concat Z z0 a d' kp (concat Z a d d' g1 q2)) (concat Z z0 a d' kp (concat Z a a' d' q1 g2))
      ≔ calc
          concat Z z0 a d' kp (concat Z a d d' g1 q2) = concat Z z0 d d' (concat Z z0 a d kp g1) q2
            by inverse (Id Z z0 d') (concat Z z0 d d' (concat Z z0 a d kp g1) q2) (concat Z z0 a d' kp (concat Z a d d' g1 q2))
              (concat_assoc Z z0 a d d' kp g1 q2)
          = concat Z z0 a' d' kp' g2 by c2
          = concat Z z0 a' d' (concat Z z0 a a' kp q1) g2
            by refl ((r ↦ concat Z z0 a' d' r g2) : Id Z z0 a' → Id Z z0 d')
              (inverse (Id Z z0 a') (concat Z z0 a a' kp q1) kp' c1')
          = concat Z z0 a d' kp (concat Z a a' d' q1 g2) by concat_assoc Z z0 a a' d' kp q1 g2 ∎ in
    calc
      concat Z d a d' (inverse Z a d g1) (concat Z a a' d' q1 g2)
      = concat Z d a d' (inverse Z a d g1) (concat Z a d d' g1 q2)
        by refl (concat Z d a d' (inverse Z a d g1))
          (inverse (Id Z a d') (concat Z a d d' g1 q2) (concat Z a a' d' q1 g2)
            (concat_cancel_left Z z0 a d' kp (concat Z a d d' g1 q2) (concat Z a a' d' q1 g2) c3))
      = q2 by concat_left_inverse Z a d d' g1 q2 ∎

def wedge_pointed_ext (X Y : Pointed) (W : OnePointUnionSignature X Y) (Z : Pointed) (k k' : BookPointedMap (one_point_union_pointed X Y W) Z)
  (e1 : Id (BookPointedMap X Z)
    (book_pointed_compose X (one_point_union_pointed X Y W) Z (wedge_inl_pointed X Y W) k)
    (book_pointed_compose X (one_point_union_pointed X Y W) Z (wedge_inl_pointed X Y W) k'))
  (e2 : Id (BookPointedMap Y Z)
    (book_pointed_compose Y (one_point_union_pointed X Y W) Z (wedge_inr_pointed X Y W) k)
    (book_pointed_compose Y (one_point_union_pointed X Y W) Z (wedge_inr_pointed X Y W) k'))
  : Id (BookPointedMap (one_point_union_pointed X Y W) Z) k k'
  ≔ let V ≔ W .carrier in let C ≔ Z .carrier in let x0 ≔ X .point in let y0 ≔ Y .point in
    let i ≔ W .inl in let j ≔ W .inr in let g ≔ W .glue in
    let ph1 ≔ pointed_map_path_equiv X Z
      (book_pointed_compose X (one_point_union_pointed X Y W) Z (wedge_inl_pointed X Y W) k)
      (book_pointed_compose X (one_point_union_pointed X Y W) Z (wedge_inl_pointed X Y W) k') .map e1 in
    let ph2 ≔ pointed_map_path_equiv Y Z
      (book_pointed_compose Y (one_point_union_pointed X Y W) Z (wedge_inr_pointed X Y W) k)
      (book_pointed_compose Y (one_point_union_pointed X Y W) Z (wedge_inr_pointed X Y W) k') .map e2 in
    let P ≔ ((w ↦ Id C (k .fst w) (k' .fst w)) : V → Type) in
    let glue_po : Id P g (ph1 .fst x0) (ph2 .fst y0)
      ≔ pathover_of_eq V P (i x0) (j y0) g (ph1 .fst x0) (ph2 .fst y0)
          (concat (Id C (k .fst (j y0)) (k' .fst (j y0)))
            (transport V P (i x0) (j y0) g (ph1 .fst x0))
            (concat C (k .fst (j y0)) (k .fst (i x0)) (k' .fst (j y0)) (inverse C (k .fst (i x0)) (k .fst (j y0)) (refl (k .fst) g))
              (concat C (k .fst (i x0)) (k' .fst (i x0)) (k' .fst (j y0)) (ph1 .fst x0) (refl (k' .fst) g)))
            (ph2 .fst y0)
            (transport_path_family V C (k .fst) (k' .fst) (i x0) (j y0) g (ph1 .fst x0))
            (wedge_glue_algebra C (Z .point) (k .fst (i x0)) (k' .fst (i x0)) (k .fst (j y0)) (k' .fst (j y0))
              (k .snd) (k' .snd) (refl (k .fst) g) (refl (k' .fst) g) (ph1 .fst x0) (ph2 .fst y0)
              (ph1 .snd) (ph2 .snd))) in
    let ind ≔ W .induction P (ph1 .fst, (ph2 .fst, glue_po)) in
    let H ≔ ind .fst in
    let Hx0 : Id (Id C (k .fst (i x0)) (k' .fst (i x0))) (H (i x0)) (ph1 .fst x0)
      ≔ ind .snd .fst (refl x0) in
    equiv_inverse_map (Id (BookPointedMap (one_point_union_pointed X Y W) Z) k k')
      (PointedHomotopy (one_point_union_pointed X Y W) Z k k') (pointed_map_path_equiv (one_point_union_pointed X Y W) Z k k')
      (H, calc
        concat C (Z .point) (k .fst (i x0)) (k' .fst (i x0)) (k .snd) (H (i x0))
        = concat C (Z .point) (k .fst (i x0)) (k' .fst (i x0)) (k .snd) (ph1 .fst x0)
          by refl (concat C (Z .point) (k .fst (i x0)) (k' .fst (i x0)) (k .snd)) Hx0
        = concat C (Z .point) (k .fst (i x0)) (k' .fst (i x0))
            (concat C (Z .point) (k .fst (i x0)) (k .fst (i x0)) (k .snd) (refl (k .fst (i x0)))) (ph1 .fst x0)
          by refl ((r ↦ concat C (Z .point) (k .fst (i x0)) (k' .fst (i x0)) r (ph1 .fst x0))
              : Id C (Z .point) (k .fst (i x0)) → Id C (Z .point) (k' .fst (i x0)))
            (inverse (Id C (Z .point) (k .fst (i x0)))
              (concat C (Z .point) (k .fst (i x0)) (k .fst (i x0)) (k .snd) (refl (k .fst (i x0)))) (k .snd)
              (concat_p1 C (Z .point) (k .fst (i x0)) (k .snd)))
        = concat C (Z .point) (k' .fst (i x0)) (k' .fst (i x0)) (k' .snd) (refl (k' .fst (i x0))) by ph1 .snd
        = k' .snd by concat_p1 C (Z .point) (k' .fst (i x0)) (k' .snd) ∎)

{` The fold map BG ∨ BG →* BG (both summands by the identity) and the
   inclusion BG ∨ BG →* BG × BG (inl x ↦ (x, sh), inr x ↦ (sh, x)), for any
   wedge W of BG with itself; both are pointed by their computation rules. `}
def square_pointed (G : Group) : Pointed ≔ (Product (BG G .carrier) (BG G .carrier), (shape G, shape G))

def wedge_fold (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) : W .carrier → BG G .carrier
  ≔ one_point_union_rec (BG G) (BG G) W (BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier)) (refl (shape G))

def wedge_fold_beta (G : Group) (W : OnePointUnionSignature (BG G) (BG G))
  : Id (OnePointUnionBoundary (BG G) (BG G) (W .carrier) (W .inl) (W .inr) (W .glue) (_ ↦ BG G .carrier))
      (one_point_union_evaluate (BG G) (BG G) (W .carrier) (W .inl) (W .inr) (W .glue) (_ ↦ BG G .carrier) (wedge_fold G W))
      (identity (BG G .carrier), (identity (BG G .carrier), refl (shape G)))
  ≔ one_point_union_rec_beta (BG G) (BG G) W (BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier)) (refl (shape G))

def wedge_fold_left (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (x : BG G .carrier)
  : Id (BG G .carrier) (wedge_fold G W (W .inl x)) x
  ≔ happly (BG G .carrier) (_ ↦ BG G .carrier) (y ↦ wedge_fold G W (W .inl y)) (identity (BG G .carrier))
      (wedge_fold_beta G W .fst) x

def wedge_fold_right (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (y : BG G .carrier)
  : Id (BG G .carrier) (wedge_fold G W (W .inr y)) y
  ≔ happly (BG G .carrier) (_ ↦ BG G .carrier) (z ↦ wedge_fold G W (W .inr z)) (identity (BG G .carrier))
      (wedge_fold_beta G W .snd .fst) y

def wedge_fold_pointed (G : Group) (W : OnePointUnionSignature (BG G) (BG G))
  : BookPointedMap (one_point_union_pointed (BG G) (BG G) W) (BG G)
  ≔ (wedge_fold G W, inverse (BG G .carrier) (wedge_fold G W (W .inl (shape G))) (shape G) (wedge_fold_left G W (shape G)))

def wedge_incl (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) : W .carrier → Product (BG G .carrier) (BG G .carrier)
  ≔ one_point_union_rec (BG G) (BG G) W (Product (BG G .carrier) (BG G .carrier)) (x ↦ (x, shape G)) (y ↦ (shape G, y))
      (refl (shape G, shape G))

def wedge_incl_beta (G : Group) (W : OnePointUnionSignature (BG G) (BG G))
  : Id (OnePointUnionBoundary (BG G) (BG G) (W .carrier) (W .inl) (W .inr) (W .glue) (_ ↦ Product (BG G .carrier) (BG G .carrier)))
      (one_point_union_evaluate (BG G) (BG G) (W .carrier) (W .inl) (W .inr) (W .glue) (_ ↦ Product (BG G .carrier) (BG G .carrier))
        (wedge_incl G W))
      ((x ↦ (x, shape G)), ((y ↦ (shape G, y)), refl (shape G, shape G)))
  ≔ one_point_union_rec_beta (BG G) (BG G) W (Product (BG G .carrier) (BG G .carrier)) (x ↦ (x, shape G)) (y ↦ (shape G, y))
      (refl (shape G, shape G))

def wedge_incl_left (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (x : BG G .carrier)
  : Id (Product (BG G .carrier) (BG G .carrier)) (wedge_incl G W (W .inl x)) (x, shape G)
  ≔ happly (BG G .carrier) (_ ↦ Product (BG G .carrier) (BG G .carrier)) (y ↦ wedge_incl G W (W .inl y))
      (y ↦ (y, shape G)) (wedge_incl_beta G W .fst) x

def wedge_incl_right (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (y : BG G .carrier)
  : Id (Product (BG G .carrier) (BG G .carrier)) (wedge_incl G W (W .inr y)) (shape G, y)
  ≔ happly (BG G .carrier) (_ ↦ Product (BG G .carrier) (BG G .carrier)) (z ↦ wedge_incl G W (W .inr z))
      (z ↦ (shape G, z)) (wedge_incl_beta G W .snd .fst) y

def wedge_incl_pointed (G : Group) (W : OnePointUnionSignature (BG G) (BG G))
  : BookPointedMap (one_point_union_pointed (BG G) (BG G) W) (square_pointed G)
  ≔ (wedge_incl G W, inverse (Product (BG G .carrier) (BG G .carrier)) (wedge_incl G W (W .inl (shape G)))
      (shape G, shape G) (wedge_incl_left G W (shape G)))

{` The type of factorizations of the fold map through the inclusion. `}
def WedgeFoldFactorization (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) : Type
  ≔ Σ (BookPointedMap (square_pointed G) (BG G))
      (h ↦ Id (BookPointedMap (one_point_union_pointed (BG G) (BG G) W) (BG G))
        (book_pointed_compose (one_point_union_pointed (BG G) (BG G) W) (square_pointed G) (BG G) (wedge_incl_pointed G W) h)
        (wedge_fold_pointed G W))

{` Consequences of a factorization on symmetries. `}
def factorization_loops (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (F : WedgeFoldFactorization G W)
  (w : Loop (one_point_union_pointed (BG G) (BG G) W))
  : Id (USym G)
      (loops_map (square_pointed G) (BG G) (F .fst)
        (loops_map (one_point_union_pointed (BG G) (BG G) W) (square_pointed G) (wedge_incl_pointed G W) w))
      (loops_map (one_point_union_pointed (BG G) (BG G) W) (BG G) (wedge_fold_pointed G W) w)
  ≔ let V ≔ one_point_union_pointed (BG G) (BG G) W in
    concat (USym G)
      (loops_map (square_pointed G) (BG G) (F .fst) (loops_map V (square_pointed G) (wedge_incl_pointed G W) w))
      (loops_map V (BG G) (book_pointed_compose V (square_pointed G) (BG G) (wedge_incl_pointed G W) (F .fst)) w)
      (loops_map V (BG G) (wedge_fold_pointed G W) w)
      (inverse (USym G) (loops_map V (BG G) (book_pointed_compose V (square_pointed G) (BG G) (wedge_incl_pointed G W) (F .fst)) w)
        (loops_map (square_pointed G) (BG G) (F .fst) (loops_map V (square_pointed G) (wedge_incl_pointed G W) w))
        (loops_map_compose_pointwise V (square_pointed G) (BG G) (wedge_incl_pointed G W) (F .fst) w))
      (refl ((k ↦ loops_map V (BG G) k w) : BookPointedMap V (BG G) → USym G) (F .snd))

def incl_left_loop (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g : USym G)
  : Id (Loop (square_pointed G))
      (loops_map (one_point_union_pointed (BG G) (BG G) W) (square_pointed G) (wedge_incl_pointed G W) (refl (W .inl) g))
      (g, refl (shape G))
  ≔ loops_homotopy_inverse (BG G .carrier) (Product (BG G .carrier) (BG G .carrier)) (shape G)
      (x ↦ wedge_incl G W (W .inl x)) (x ↦ (x, shape G)) (wedge_incl_left G W) g

def fold_left_loop (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g : USym G)
  : Id (USym G) (loops_map (one_point_union_pointed (BG G) (BG G) W) (BG G) (wedge_fold_pointed G W) (refl (W .inl) g)) g
  ≔ loops_homotopy_inverse (BG G .carrier) (BG G .carrier) (shape G)
      (x ↦ wedge_fold G W (W .inl x)) (identity (BG G .carrier)) (wedge_fold_left G W) g

def factorization_left (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (F : WedgeFoldFactorization G W) (g : USym G)
  : Id (USym G) (loops_map (square_pointed G) (BG G) (F .fst) (g, refl (shape G))) g
  ≔ let V ≔ one_point_union_pointed (BG G) (BG G) W in
    calc
      loops_map (square_pointed G) (BG G) (F .fst) (g, refl (shape G))
      = loops_map (square_pointed G) (BG G) (F .fst) (loops_map V (square_pointed G) (wedge_incl_pointed G W) (refl (W .inl) g))
        by refl (loops_map (square_pointed G) (BG G) (F .fst))
          (inverse (Loop (square_pointed G)) (loops_map V (square_pointed G) (wedge_incl_pointed G W) (refl (W .inl) g))
            (g, refl (shape G)) (incl_left_loop G W g))
      = loops_map V (BG G) (wedge_fold_pointed G W) (refl (W .inl) g) by factorization_loops G W F (refl (W .inl) g)
      = g by fold_left_loop G W g ∎

{` The right summand: v(g') ≔ Ω incl (Ω inr g') has first component refl,
   second component a conjugate of g', and h sends it to a conjugate of g'. `}
def wedge_right_loop (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g : USym G) : Loop (one_point_union_pointed (BG G) (BG G) W)
  ≔ loops_map (BG G) (one_point_union_pointed (BG G) (BG G) W) (wedge_inr_pointed (BG G) (BG G) W) g

def incl_right_pointed (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) : BookPointedMap (BG G) (square_pointed G)
  ≔ book_pointed_compose (BG G) (one_point_union_pointed (BG G) (BG G) W) (square_pointed G)
      (wedge_inr_pointed (BG G) (BG G) W) (wedge_incl_pointed G W)

def incl_right_loop (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g : USym G) : Loop (square_pointed G)
  ≔ loops_map (one_point_union_pointed (BG G) (BG G) W) (square_pointed G) (wedge_incl_pointed G W) (wedge_right_loop G W g)

def incl_right_loop_compose (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g : USym G)
  : Id (Loop (square_pointed G)) (incl_right_loop G W g) (loops_map (BG G) (square_pointed G) (incl_right_pointed G W) g)
  ≔ inverse (Loop (square_pointed G)) (loops_map (BG G) (square_pointed G) (incl_right_pointed G W) g) (incl_right_loop G W g)
      (loops_map_compose_pointwise (BG G) (one_point_union_pointed (BG G) (BG G) W) (square_pointed G)
        (wedge_inr_pointed (BG G) (BG G) W) (wedge_incl_pointed G W) g)

def square_fst_pointed (G : Group) : BookPointedMap (square_pointed G) (BG G) ≔ (u ↦ u .fst, refl (shape G))

def square_snd_pointed (G : Group) : BookPointedMap (square_pointed G) (BG G) ≔ (u ↦ u .snd, refl (shape G))

def incl_right_loop_fst (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g : USym G)
  : Id (USym G) (incl_right_loop G W g .fst) (refl (shape G))
  ≔ let SQ ≔ square_pointed G in let B ≔ BG G .carrier in
    let J ≔ incl_right_pointed G W in
    calc
      incl_right_loop G W g .fst
      = loops_map SQ (BG G) (square_fst_pointed G) (incl_right_loop G W g)
        by inverse (USym G) (loops_map SQ (BG G) (square_fst_pointed G) (incl_right_loop G W g)) (incl_right_loop G W g .fst)
          (loop_conjugate_at_refl B (shape G) (incl_right_loop G W g .fst))
      = loops_map SQ (BG G) (square_fst_pointed G) (loops_map (BG G) SQ J g)
        by refl (loops_map SQ (BG G) (square_fst_pointed G)) (incl_right_loop_compose G W g)
      = loops_map (BG G) (BG G) (book_pointed_compose (BG G) SQ (BG G) J (square_fst_pointed G)) g
        by inverse (USym G) (loops_map (BG G) (BG G) (book_pointed_compose (BG G) SQ (BG G) J (square_fst_pointed G)) g)
          (loops_map SQ (BG G) (square_fst_pointed G) (loops_map (BG G) SQ J g))
          (loops_map_compose_pointwise (BG G) SQ (BG G) J (square_fst_pointed G) g)
      = pointed_loop_conjugate B (shape G) (shape G)
          (concat B (shape G) (wedge_incl G W (W .inr (shape G)) .fst) (shape G)
            (book_pointed_compose (BG G) SQ (BG G) J (square_fst_pointed G) .snd)
            (refl ((u ↦ u .fst) : Product B B → B) (wedge_incl_right G W (shape G))))
          (refl (shape G))
        by loops_homotopy B B (shape G) (shape G) (y ↦ wedge_incl G W (W .inr y) .fst) (_ ↦ shape G)
          (y ↦ refl ((u ↦ u .fst) : Product B B → B) (wedge_incl_right G W y))
          (book_pointed_compose (BG G) SQ (BG G) J (square_fst_pointed G) .snd) g
      = refl (shape G) by loop_conjugate_unit B (shape G) (shape G)
          (concat B (shape G) (wedge_incl G W (W .inr (shape G)) .fst) (shape G)
            (book_pointed_compose (BG G) SQ (BG G) J (square_fst_pointed G) .snd)
            (refl ((u ↦ u .fst) : Product B B → B) (wedge_incl_right G W (shape G)))) ∎

def incl_right_snd_conjugator (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) : USym G
  ≔ concat (BG G .carrier) (shape G) (wedge_incl G W (W .inr (shape G)) .snd) (shape G)
      (book_pointed_compose (BG G) (square_pointed G) (BG G) (incl_right_pointed G W) (square_snd_pointed G) .snd)
      (refl ((u ↦ u .snd) : Product (BG G .carrier) (BG G .carrier) → BG G .carrier) (wedge_incl_right G W (shape G)))

def incl_right_loop_snd (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g : USym G)
  : Id (USym G) (incl_right_loop G W g .snd)
      (pointed_loop_conjugate (BG G .carrier) (shape G) (shape G) (incl_right_snd_conjugator G W) g)
  ≔ let SQ ≔ square_pointed G in let B ≔ BG G .carrier in
    let J ≔ incl_right_pointed G W in
    calc
      incl_right_loop G W g .snd
      = loops_map SQ (BG G) (square_snd_pointed G) (incl_right_loop G W g)
        by inverse (USym G) (loops_map SQ (BG G) (square_snd_pointed G) (incl_right_loop G W g)) (incl_right_loop G W g .snd)
          (loop_conjugate_at_refl B (shape G) (incl_right_loop G W g .snd))
      = loops_map SQ (BG G) (square_snd_pointed G) (loops_map (BG G) SQ J g)
        by refl (loops_map SQ (BG G) (square_snd_pointed G)) (incl_right_loop_compose G W g)
      = loops_map (BG G) (BG G) (book_pointed_compose (BG G) SQ (BG G) J (square_snd_pointed G)) g
        by inverse (USym G) (loops_map (BG G) (BG G) (book_pointed_compose (BG G) SQ (BG G) J (square_snd_pointed G)) g)
          (loops_map SQ (BG G) (square_snd_pointed G) (loops_map (BG G) SQ J g))
          (loops_map_compose_pointwise (BG G) SQ (BG G) J (square_snd_pointed G) g)
      = pointed_loop_conjugate B (shape G) (shape G) (incl_right_snd_conjugator G W) (refl (identity B) g)
        by loops_homotopy B B (shape G) (shape G) (y ↦ wedge_incl G W (W .inr y) .snd) (identity B)
          (y ↦ refl ((u ↦ u .snd) : Product B B → B) (wedge_incl_right G W y))
          (book_pointed_compose (BG G) SQ (BG G) J (square_snd_pointed G) .snd) g ∎

def fold_right_conjugator (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) : USym G
  ≔ concat (BG G .carrier) (shape G) (wedge_fold G W (W .inr (shape G))) (shape G)
      (book_pointed_compose (BG G) (one_point_union_pointed (BG G) (BG G) W) (BG G) (wedge_inr_pointed (BG G) (BG G) W)
        (wedge_fold_pointed G W) .snd)
      (wedge_fold_right G W (shape G))

def factorization_right (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (F : WedgeFoldFactorization G W) (g : USym G)
  : Id (USym G) (loops_map (square_pointed G) (BG G) (F .fst) (incl_right_loop G W g))
      (pointed_loop_conjugate (BG G .carrier) (shape G) (shape G) (fold_right_conjugator G W) g)
  ≔ let V ≔ one_point_union_pointed (BG G) (BG G) W in let B ≔ BG G .carrier in
    calc
      loops_map (square_pointed G) (BG G) (F .fst) (incl_right_loop G W g)
      = loops_map V (BG G) (wedge_fold_pointed G W) (wedge_right_loop G W g) by factorization_loops G W F (wedge_right_loop G W g)
      = loops_map (BG G) (BG G)
          (book_pointed_compose (BG G) V (BG G) (wedge_inr_pointed (BG G) (BG G) W) (wedge_fold_pointed G W)) g
        by inverse (USym G)
          (loops_map (BG G) (BG G) (book_pointed_compose (BG G) V (BG G) (wedge_inr_pointed (BG G) (BG G) W) (wedge_fold_pointed G W)) g)
          (loops_map V (BG G) (wedge_fold_pointed G W) (wedge_right_loop G W g))
          (loops_map_compose_pointwise (BG G) V (BG G) (wedge_inr_pointed (BG G) (BG G) W) (wedge_fold_pointed G W) g)
      = pointed_loop_conjugate B (shape G) (shape G) (fold_right_conjugator G W) (refl (identity B) g)
        by loops_homotopy B B (shape G) (shape G) (y ↦ wedge_fold G W (W .inr y)) (identity B) (wedge_fold_right G W)
          (book_pointed_compose (BG G) V (BG G) (wedge_inr_pointed (BG G) (BG G) W) (wedge_fold_pointed G W) .snd) g ∎

{` (g, refl) commutes with v(g') in Ω(BG × BG). `}
def left_right_commute (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (g g' : USym G)
  : Id (Loop (square_pointed G))
      (concat (Product (BG G .carrier) (BG G .carrier)) (shape G, shape G) (shape G, shape G) (shape G, shape G)
        (g, refl (shape G)) (incl_right_loop G W g'))
      (concat (Product (BG G .carrier) (BG G .carrier)) (shape G, shape G) (shape G, shape G) (shape G, shape G)
        (incl_right_loop G W g') (g, refl (shape G)))
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in
    let v ≔ incl_right_loop G W g' in
    product_loop_ext B B b b
      (concat (Product B B) (b, b) (b, b) (b, b) (g, refl b) v) (concat (Product B B) (b, b) (b, b) (b, b) v (g, refl b))
      (calc
        concat (Product B B) (b, b) (b, b) (b, b) (g, refl b) v .fst = concat B b b b g (v .fst)
          by product_loop_concat_fst B B b b (g, refl b) v
        = concat B b b b g (refl b) by refl (concat B b b b g) (incl_right_loop_fst G W g')
        = g by concat_p1 B b b g
        = concat B b b b (refl b) g by inverse (Id B b b) (concat B b b b (refl b) g) g (concat_1p B b b g)
        = concat B b b b (v .fst) g
          by refl ((r ↦ concat B b b b r g) : Id B b b → Id B b b)
            (inverse (Id B b b) (v .fst) (refl b) (incl_right_loop_fst G W g'))
        = concat (Product B B) (b, b) (b, b) (b, b) v (g, refl b) .fst
          by inverse (Id B b b) (concat (Product B B) (b, b) (b, b) (b, b) v (g, refl b) .fst) (concat B b b b (v .fst) g)
            (product_loop_concat_fst B B b b v (g, refl b)) ∎)
      (calc
        concat (Product B B) (b, b) (b, b) (b, b) (g, refl b) v .snd = concat B b b b (refl b) (v .snd)
          by product_loop_concat_snd B B b b (g, refl b) v
        = v .snd by concat_1p B b b (v .snd)
        = concat B b b b (v .snd) (refl b) by inverse (Id B b b) (concat B b b b (v .snd) (refl b)) (v .snd) (concat_p1 B b b (v .snd))
        = concat (Product B B) (b, b) (b, b) (b, b) v (g, refl b) .snd
          by inverse (Id B b b) (concat (Product B B) (b, b) (b, b) (b, b) v (g, refl b) .snd) (concat B b b b (v .snd) (refl b))
            (product_loop_concat_snd B B b b v (g, refl b)) ∎)

{` First direction: a factorization makes G abelian. `}
def factorization_commute (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (F : WedgeFoldFactorization G W) (g g' : USym G)
  : Id (USym G)
      (concat (BG G .carrier) (shape G) (shape G) (shape G) g
        (pointed_loop_conjugate (BG G .carrier) (shape G) (shape G) (fold_right_conjugator G W) g'))
      (concat (BG G .carrier) (shape G) (shape G) (shape G)
        (pointed_loop_conjugate (BG G .carrier) (shape G) (shape G) (fold_right_conjugator G W) g') g)
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in let SQ ≔ square_pointed G in
    let h ≔ F .fst in let v ≔ incl_right_loop G W g' in
    let ψ ≔ pointed_loop_conjugate B b b (fold_right_conjugator G W) g' in
    calc
      concat B b b b g ψ
      = concat B b b b (loops_map SQ (BG G) h (g, refl b)) (loops_map SQ (BG G) h v)
        by inverse (Id B b b) (concat B b b b (loops_map SQ (BG G) h (g, refl b)) (loops_map SQ (BG G) h v)) (concat B b b b g ψ)
          (refl (concat B b b b) (factorization_left G W F g) (factorization_right G W F g'))
      = loops_map SQ (BG G) h (concat (Product B B) (b, b) (b, b) (b, b) (g, refl b) v)
        by inverse (Id B b b) (loops_map SQ (BG G) h (concat (Product B B) (b, b) (b, b) (b, b) (g, refl b) v))
          (concat B b b b (loops_map SQ (BG G) h (g, refl b)) (loops_map SQ (BG G) h v))
          (loops_map_concat SQ (BG G) h (g, refl b) v)
      = loops_map SQ (BG G) h (concat (Product B B) (b, b) (b, b) (b, b) v (g, refl b))
        by refl (loops_map SQ (BG G) h) (left_right_commute G W g g')
      = concat B b b b (loops_map SQ (BG G) h v) (loops_map SQ (BG G) h (g, refl b))
        by loops_map_concat SQ (BG G) h v (g, refl b)
      = concat B b b b ψ g by refl (concat B b b b) (factorization_right G W F g') (factorization_left G W F g) ∎

def factorization_abelian (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (F : WedgeFoldFactorization G W) : IsAbelian G
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in
    let c ≔ fold_right_conjugator G W in
    g q ↦
      let e ≔ conjugate_conjugate_inverse B b c q in
      let t ≔ factorization_commute G W F g (pointed_loop_conjugate B b b (inverse B b b c) q) in
      calc
        concat B b b b q g
        = concat B b b b (pointed_loop_conjugate B b b c (pointed_loop_conjugate B b b (inverse B b b c) q)) g
          by refl ((r ↦ concat B b b b r g) : Id B b b → Id B b b)
            (inverse (Id B b b) (pointed_loop_conjugate B b b c (pointed_loop_conjugate B b b (inverse B b b c) q)) q e)
        = concat B b b b g (pointed_loop_conjugate B b b c (pointed_loop_conjugate B b b (inverse B b b c) q))
          by inverse (Id B b b)
            (concat B b b b g (pointed_loop_conjugate B b b c (pointed_loop_conjugate B b b (inverse B b b c) q)))
            (concat B b b b (pointed_loop_conjugate B b b c (pointed_loop_conjugate B b b (inverse B b b c) q)) g) t
        = concat B b b b g q by refl (concat B b b b g) e ∎

{` Second direction: for abelian G the type of factorizations is a
   proposition (the factoring map is determined by its loops, which are
   (r₁, r₂) ↦ r₁ r₂). `}
def factorization_loops_formula (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (hab : IsAbelian G)
  (F : WedgeFoldFactorization G W) (r : Loop (square_pointed G))
  : Id (USym G) (loops_map (square_pointed G) (BG G) (F .fst) r)
      (concat (BG G .carrier) (shape G) (shape G) (shape G) (r .fst) (r .snd))
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in let SQ ≔ square_pointed G in
    let h ≔ F .fst in
    let v ≔ incl_right_loop G W (r .snd) in
    let decomp : Id (Loop SQ) r (concat (Product B B) (b, b) (b, b) (b, b) (r .fst, refl b) v)
      ≔ product_loop_ext B B b b r (concat (Product B B) (b, b) (b, b) (b, b) (r .fst, refl b) v)
          (calc
            r .fst = concat B b b b (r .fst) (refl b) by inverse (Id B b b) (concat B b b b (r .fst) (refl b)) (r .fst) (concat_p1 B b b (r .fst))
            = concat B b b b (r .fst) (v .fst)
              by refl (concat B b b b (r .fst)) (inverse (Id B b b) (v .fst) (refl b) (incl_right_loop_fst G W (r .snd)))
            = concat (Product B B) (b, b) (b, b) (b, b) (r .fst, refl b) v .fst
              by inverse (Id B b b) (concat (Product B B) (b, b) (b, b) (b, b) (r .fst, refl b) v .fst) (concat B b b b (r .fst) (v .fst))
                (product_loop_concat_fst B B b b (r .fst, refl b) v) ∎)
          (calc
            r .snd = pointed_loop_conjugate B b b (incl_right_snd_conjugator G W) (r .snd)
              by inverse (Id B b b) (pointed_loop_conjugate B b b (incl_right_snd_conjugator G W) (r .snd)) (r .snd)
                (abelian_loop_conjugate_trivial G hab (incl_right_snd_conjugator G W) (r .snd))
            = v .snd by inverse (Id B b b) (v .snd) (pointed_loop_conjugate B b b (incl_right_snd_conjugator G W) (r .snd))
                (incl_right_loop_snd G W (r .snd))
            = concat B b b b (refl b) (v .snd) by inverse (Id B b b) (concat B b b b (refl b) (v .snd)) (v .snd) (concat_1p B b b (v .snd))
            = concat (Product B B) (b, b) (b, b) (b, b) (r .fst, refl b) v .snd
              by inverse (Id B b b) (concat (Product B B) (b, b) (b, b) (b, b) (r .fst, refl b) v .snd) (concat B b b b (refl b) (v .snd))
                (product_loop_concat_snd B B b b (r .fst, refl b) v) ∎) in
    calc
      loops_map SQ (BG G) h r = loops_map SQ (BG G) h (concat (Product B B) (b, b) (b, b) (b, b) (r .fst, refl b) v)
        by refl (loops_map SQ (BG G) h) decomp
      = concat B b b b (loops_map SQ (BG G) h (r .fst, refl b)) (loops_map SQ (BG G) h v)
        by loops_map_concat SQ (BG G) h (r .fst, refl b) v
      = concat B b b b (r .fst) (pointed_loop_conjugate B b b (fold_right_conjugator G W) (r .snd))
        by refl (concat B b b b) (factorization_left G W F (r .fst)) (factorization_right G W F (r .snd))
      = concat B b b b (r .fst) (r .snd)
        by refl (concat B b b b (r .fst)) (abelian_loop_conjugate_trivial G hab (fold_right_conjugator G W) (r .snd)) ∎

def wedge_factorization_prop (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) : isProp (WedgeFoldFactorization G W)
  ≔ F F' ↦
    let hab ≔ factorization_abelian G W F in
    let V ≔ one_point_union_pointed (BG G) (BG G) W in
    let SQ ≔ square_pointed G in
    subtype_equal (BookPointedMap SQ (BG G))
      (k ↦ Id (BookPointedMap V (BG G)) (book_pointed_compose V SQ (BG G) (wedge_incl_pointed G W) k) (wedge_fold_pointed G W))
      (k ↦ pointed_maps_set V (BG G) (one_point_union_connected (BG G) (BG G) W (bg_connected G) (bg_connected G)) (bg_groupoid G)
        (book_pointed_compose V SQ (BG G) (wedge_incl_pointed G W) k) (wedge_fold_pointed G W))
      F F'
      (pointed_maps_eq_from_loops SQ (BG G)
        (connected_product (BG G .carrier) (BG G .carrier) (bg_connected G) (bg_connected G)) (bg_groupoid G)
        (F .fst) (F' .fst)
        (r ↦ concat (USym G) (loops_map SQ (BG G) (F .fst) r)
          (concat (BG G .carrier) (shape G) (shape G) (shape G) (r .fst) (r .snd)) (loops_map SQ (BG G) (F' .fst) r)
          (factorization_loops_formula G W hab F r)
          (inverse (USym G) (loops_map SQ (BG G) (F' .fst) r) (concat (BG G .carrier) (shape G) (shape G) (shape G) (r .fst) (r .snd))
            (factorization_loops_formula G W hab F' r))))

{` Third direction: if G is abelian, the fold map factors. For x : BG let
   s(x) : (BG, sh) →* (BG, x) be the section with s(sh) = id of the family of
   pointed maps (a family of sets over the connected BG; the identity is fixed
   by all loops because pointed maps into BG with homotopic underlying maps are
   equal when G is abelian), and h(x, y) ≔ s(x)(y). `}
def transport_pointed_map_fst (A : Pointed) (B : Type) (x y : B) (l : Id B x y) (u : BookPointedMap A (B, x))
  : Id (A .carrier → B) (transport B (z ↦ BookPointedMap A (B, z)) x y l u .fst) (u .fst)
  ≔ J B x (y l ↦ Id (A .carrier → B) (transport B (z ↦ BookPointedMap A (B, z)) x y l u .fst) (u .fst))
      (refl ((v ↦ v .fst) : BookPointedMap A (B, x) → A .carrier → B)
        (transport_refl B (z ↦ BookPointedMap A (B, z)) x u))
      y l

def abelian_endomap_fix (G : Group) (hab : IsAbelian G) (l : USym G)
  : Id (BookPointedMap (BG G) (BG G))
      (transport (BG G .carrier) (z ↦ BookPointedMap (BG G) (BG G .carrier, z)) (shape G) (shape G) l
        (identity (BG G .carrier), refl (shape G)))
      (identity (BG G .carrier), refl (shape G))
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in
    let P ≔ ((z ↦ BookPointedMap (BG G) (B, z)) : B → Type) in
    abelian_pointed_maps_ext (BG G) G hab (transport B P b b l (identity B, refl b)) (identity B, refl b)
      (a ↦ happly B (_ ↦ B) (transport B P b b l (identity B, refl b) .fst) (identity B)
        (transport_pointed_map_fst (BG G) B b b l (identity B, refl b)) a)

def abelian_endomap_section (G : Group) (hab : IsAbelian G) : (x : BG G .carrier) → BookPointedMap (BG G) (BG G .carrier, x)
  ≔ connected_set_section (BG G .carrier) (shape G) (bg_connected G) (z ↦ BookPointedMap (BG G) (BG G .carrier, z))
      (z ↦ pointed_maps_set (BG G) (BG G .carrier, z) (bg_connected G) (bg_groupoid G))
      (identity (BG G .carrier), refl (shape G)) (abelian_endomap_fix G hab)

def abelian_endomap_section_beta (G : Group) (hab : IsAbelian G)
  : Id (BookPointedMap (BG G) (BG G)) (abelian_endomap_section G hab (shape G)) (identity (BG G .carrier), refl (shape G))
  ≔ connected_set_section_beta (BG G .carrier) (shape G) (bg_connected G) (z ↦ BookPointedMap (BG G) (BG G .carrier, z))
      (z ↦ pointed_maps_set (BG G) (BG G .carrier, z) (bg_connected G) (bg_groupoid G))
      (identity (BG G .carrier), refl (shape G)) (abelian_endomap_fix G hab)

def abelian_multiplication_map (G : Group) (hab : IsAbelian G) (u : Product (BG G .carrier) (BG G .carrier)) : BG G .carrier
  ≔ abelian_endomap_section G hab (u .fst) .fst (u .snd)

def abelian_multiplication (G : Group) (hab : IsAbelian G) : BookPointedMap (square_pointed G) (BG G)
  ≔ (abelian_multiplication_map G hab, abelian_endomap_section G hab (shape G) .snd)

def abelian_factorization (G : Group) (W : OnePointUnionSignature (BG G) (BG G)) (hab : IsAbelian G) : WedgeFoldFactorization G W
  ≔ let B ≔ BG G .carrier in let b ≔ shape G in
    let V ≔ one_point_union_pointed (BG G) (BG G) W in
    let μ ≔ abelian_multiplication_map G hab in
    let s ≔ abelian_endomap_section G hab in
    let k ≔ book_pointed_compose V (square_pointed G) (BG G) (wedge_incl_pointed G W) (abelian_multiplication G hab) in
    (abelian_multiplication G hab,
     wedge_pointed_ext (BG G) (BG G) W (BG G) k (wedge_fold_pointed G W)
       (abelian_pointed_maps_ext (BG G) G hab
         (book_pointed_compose (BG G) V (BG G) (wedge_inl_pointed (BG G) (BG G) W) k)
         (book_pointed_compose (BG G) V (BG G) (wedge_inl_pointed (BG G) (BG G) W) (wedge_fold_pointed G W))
         (x ↦ calc
           μ (wedge_incl G W (W .inl x)) = μ (x, b) by refl μ (wedge_incl_left G W x)
           = x by inverse B x (s x .fst b) (s x .snd)
           = wedge_fold G W (W .inl x) by inverse B (wedge_fold G W (W .inl x)) x (wedge_fold_left G W x) ∎))
       (abelian_pointed_maps_ext (BG G) G hab
         (book_pointed_compose (BG G) V (BG G) (wedge_inr_pointed (BG G) (BG G) W) k)
         (book_pointed_compose (BG G) V (BG G) (wedge_inr_pointed (BG G) (BG G) W) (wedge_fold_pointed G W))
         (y ↦ calc
           μ (wedge_incl G W (W .inr y)) = μ (b, y) by refl μ (wedge_incl_right G W y)
           = y by happly B (_ ↦ B) (s b .fst) (identity B)
               (refl ((v ↦ v .fst) : BookPointedMap (BG G) (BG G) → B → B) (abelian_endomap_section_beta G hab)) y
           = wedge_fold G W (W .inr y) by inverse B (wedge_fold G W (W .inr y)) y (wedge_fold_right G W y) ∎)))

{` rem:whatAREabeliangroups: the type of factorizations of the fold map
   through the inclusion is a proposition equivalent to isAb(G). `}
def wedge_factorization_abelian_equiv (G : Group) (W : OnePointUnionSignature (BG G) (BG G))
  : Equiv (WedgeFoldFactorization G W) (IsAbelian G)
  ≔ iff_equiv (WedgeFoldFactorization G W) (IsAbelian G) (wedge_factorization_prop G W) (is_abelian_prop G)
      (factorization_abelian G W) (abelian_factorization G W)

{` Litmus: for every wedge of BΣ_2 with itself the fold map factors, and for
   BΣ_3 it does not. `}
def sigma2_fold_factorization (W : OnePointUnionSignature (BG (symmetric_group two)) (BG (symmetric_group two)))
  : WedgeFoldFactorization (symmetric_group two) W
  ≔ abelian_factorization (symmetric_group two) W sigma2_abelian

def sigma3_no_fold_factorization (W : OnePointUnionSignature (BG (symmetric_group three)) (BG (symmetric_group three)))
  (F : WedgeFoldFactorization (symmetric_group three) W) : Empty
  ≔ symmetric_group_three_not_abelian (factorization_abelian (symmetric_group three) W F)
