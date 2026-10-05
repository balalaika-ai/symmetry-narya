export "04-wedge"
export "../../../src/844-circle-wedge-homomorphisms"
export "../../../src/281-pathover-groupoid-laws"
export "../../../src/1333-pointed-circle-evaluation"

{` Bridges for congp.tex, sums of groups (def:wedge, lem:univvee,
   def:sumofgroup, lem:sumofgroupsISsum, cor:ZplusZuniv).

   Every blind wedge signature W (book boundary datum s(a1) = C(g⁻¹)s(a2),
   computation rule as one Σ-path) gives one of ours on the same carrier,
   constructors and glue (bridge_wedge_signature): the blind path datum is
   the image of our dependent path under bw_conv, which has the retraction
   bw_back, and the blind evaluation map is bw_conv applied to apd. On the
   result the blind i1^g, i2^g, (i1, refl), (i2, g), (A1 ∨ A2, a12) and i^*
   are ours by refl.

   The blind sum G1 ∨ G2 is the literal Aut_W(a12) (our
   wedge_automorphism_group, by refl), ours is mkgroup (W, a12)
   (sum_of_groups, identified by sum_of_groups_aut_path). Homomorphisms out
   of Aut_W(a12) are transferred along the pointed equivalence
   fst : (W_(a12), pt) → (W, a12) (W is connected); the blind structure maps
   followed by fst are our pointed structure maps up to concat with refl. `}

{` The book's path datum from a dependent path, and back. `}
def bw_conv (X : Type) (P : X → Type) (x y : X) (g : Id X x y) (u : P x) (v : P y) (q : Id P g u v)
  : Id (P x) u (transport X P y x (inverse X x y g) v)
  ≔ inverse (P x) (transport X P y x (inverse X x y g) v) u
      (pathover_transport_equiv X P y x (inverse X x y g) v u .map (pathover_inverse X P x y g u v q))

def bw_back_inner (X : Type) (P : X → Type) (x y : X) (g : Id X x y) (u : P x) (v : P y)
  (r : Id (P x) (transport X P y x (inverse X x y g) v) u) : Id P g u v
  ≔ transport (Id X x y) (t ↦ Id P t u v) (inverse X y x (inverse X x y g)) g (inverse_inverse X x y g)
      (pathover_inverse X P y x (inverse X x y g) v u
        (equiv_inverse_map (Id P (inverse X x y g) v u) (Id (P x) (transport X P y x (inverse X x y g) v) u)
          (pathover_transport_equiv X P y x (inverse X x y g) v u) r))

def bw_back (X : Type) (P : X → Type) (x y : X) (g : Id X x y) (u : P x) (v : P y)
  (r : Id (P x) u (transport X P y x (inverse X x y g) v)) : Id P g u v
  ≔ bw_back_inner X P x y g u v (inverse (P x) u (transport X P y x (inverse X x y g) v) r)

def bw_back_conv (X : Type) (P : X → Type) (x y : X) (g : Id X x y) (u : P x) (v : P y) (q : Id P g u v)
  : Id (Id P g u v) (bw_back X P x y g u v (bw_conv X P x y g u v q)) q
  ≔ let gi ≔ inverse X x y g in
    let tr ≔ transport X P y x gi v in
    let E ≔ pathover_transport_equiv X P y x gi v u in
    let pq ≔ pathover_inverse X P x y g u v q in
    let T ≔ transport (Id X x y) (t ↦ Id P t u v) (inverse X y x gi) g (inverse_inverse X x y g) in
    concat (Id P g u v) (bw_back X P x y g u v (bw_conv X P x y g u v q))
      (bw_back_inner X P x y g u v (E .map pq)) q
      (refl (bw_back_inner X P x y g u v) (inverse_inverse (P x) tr u (E .map pq)))
      (concat (Id P g u v) (bw_back_inner X P x y g u v (E .map pq))
        (T (pathover_inverse X P y x gi v u pq)) q
        (refl ((w ↦ T (pathover_inverse X P y x gi v u w)) : Id P gi v u → Id P g u v)
          (equiv_retraction (Id P gi v u) (Id (P x) tr u) E pq))
        (pathover_transport_equiv (Id X x y) (t ↦ Id P t u v) (inverse X y x gi) g (inverse_inverse X x y g)
          (pathover_inverse X P y x gi v u pq) q .map
          (pathover_inverse_inverse_strong X P x y g u v q)))

{` Our boundary data from the blind ones. `}
def bw_back_boundary (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) (b : BlindWedgeBoundary A1 A2 X i1 i2 g P)
  : WedgeBoundary A1 A2 X i1 i2 g P
  ≔ (a ↦ b .fst (inl. a),
     (a ↦ b .fst (inr. a),
      bw_back X P (i1 (A1 .point)) (i2 (A2 .point)) g (b .fst (inl. (A1 .point))) (b .fst (inr. (A2 .point))) (b .snd)))

def bw_to_boundary (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) (d : WedgeBoundary A1 A2 X i1 i2 g P)
  : BlindWedgeBoundary A1 A2 X i1 i2 g P
  ≔ ([ inl. a ↦ d .fst a | inr. a ↦ d .snd .fst a ],
     bw_conv X P (i1 (A1 .point)) (i2 (A2 .point)) g (d .fst (A1 .point)) (d .snd .fst (A2 .point)) (d .snd .snd))

def bw_back_to (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) (d : WedgeBoundary A1 A2 X i1 i2 g P)
  : Id (WedgeBoundary A1 A2 X i1 i2 g P) (bw_back_boundary A1 A2 X i1 i2 g P (bw_to_boundary A1 A2 X i1 i2 g P d)) d
  ≔ (refl (d .fst), (refl (d .snd .fst),
      bw_back_conv X P (i1 (A1 .point)) (i2 (A2 .point)) g (d .fst (A1 .point)) (d .snd .fst (A2 .point)) (d .snd .snd)))

def bw_eval_back (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) (f : (x : X) → P x)
  : Id (WedgeBoundary A1 A2 X i1 i2 g P) (wedge_evaluate A1 A2 X i1 i2 g P f)
      (bw_back_boundary A1 A2 X i1 i2 g P (blind_wedge_evaluate A1 A2 X i1 i2 g P f))
  ≔ (refl ((a ↦ f (i1 a)) : (a : A1 .carrier) → P (i1 a)), (refl ((a ↦ f (i2 a)) : (a : A2 .carrier) → P (i2 a)),
      inverse (Id P g (f (i1 (A1 .point))) (f (i2 (A2 .point))))
        (bw_back X P (i1 (A1 .point)) (i2 (A2 .point)) g (f (i1 (A1 .point))) (f (i2 (A2 .point)))
          (bw_conv X P (i1 (A1 .point)) (i2 (A2 .point)) g (f (i1 (A1 .point))) (f (i2 (A2 .point))) (refl f g)))
        (refl f g)
        (bw_back_conv X P (i1 (A1 .point)) (i2 (A2 .point)) g (f (i1 (A1 .point))) (f (i2 (A2 .point))) (refl f g))))

def bw_induction (A1 A2 : Pointed) (W : BlindWedge A1 A2) (P : W .fst → Type)
  (d : WedgeBoundary A1 A2 (W .fst) (W .snd .i1) (W .snd .i2) (W .snd .glue) P)
  : Σ ((x : W .fst) → P x) (h ↦
      Id (WedgeBoundary A1 A2 (W .fst) (W .snd .i1) (W .snd .i2) (W .snd .glue) P)
        (wedge_evaluate A1 A2 (W .fst) (W .snd .i1) (W .snd .i2) (W .snd .glue) P h) d)
  ≔ let X ≔ W .fst in let i1 ≔ W .snd .i1 in let i2 ≔ W .snd .i2 in let g ≔ W .snd .glue in
    let WB ≔ WedgeBoundary A1 A2 X i1 i2 g P in
    let back ≔ bw_back_boundary A1 A2 X i1 i2 g P in
    let db ≔ bw_to_boundary A1 A2 X i1 i2 g P d in
    let r ≔ W .snd .induction P db in
    (r .fst,
     concat WB (wedge_evaluate A1 A2 X i1 i2 g P (r .fst)) (back (blind_wedge_evaluate A1 A2 X i1 i2 g P (r .fst))) d
       (bw_eval_back A1 A2 X i1 i2 g P (r .fst))
       (concat WB (back (blind_wedge_evaluate A1 A2 X i1 i2 g P (r .fst))) (back db) d
         (refl back (r .snd)) (bw_back_to A1 A2 X i1 i2 g P d)))

{` def:wedge: every blind wedge is a wedge signature of ours. `}
def bridge_wedge_signature (A1 A2 : Pointed) (W : BlindWedge A1 A2) : WedgeSignature A1 A2
  ≔ (carrier ≔ W .fst, incl1 ≔ W .snd .i1, incl2 ≔ W .snd .i2, glue ≔ W .snd .glue,
     induction ≔ P d ↦ bw_induction A1 A2 W P d)

def bridge_def_wedge_pointed (A1 A2 : Pointed) (W : BlindWedge A1 A2)
  : Id Pointed (blind_wedge_pointed A1 A2 W) (wedge_pointed A1 A2 (bridge_wedge_signature A1 A2 W))
  ≔ refl (blind_wedge_pointed A1 A2 W)

def bridge_def_wedge_loops (A1 A2 : Pointed) (W : BlindWedge A1 A2) (p : Loop A1) (p' : Loop A2)
  : Product (Id (Loop (blind_wedge_pointed A1 A2 W)) (blind_wedge_i1g A1 A2 W p)
               (wedge_loop1 A1 A2 (bridge_wedge_signature A1 A2 W) p))
            (Id (Loop (blind_wedge_pointed A1 A2 W)) (blind_wedge_i2g A1 A2 W p')
               (wedge_loop2 A1 A2 (bridge_wedge_signature A1 A2 W) p'))
  ≔ (refl (blind_wedge_i1g A1 A2 W p), refl (blind_wedge_i2g A1 A2 W p'))

{` lem:univvee. `}
def bridge_lem_univvee : blind_lem_univvee
  ≔ A1 A2 W B ↦ wedge_restrict_book_equiv A1 A2 (bridge_wedge_signature A1 A2 W) B

{` def:sumofgroup. `}
def bridge_def_group_sum (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst))
  : Id Group (sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) (blind_group_sum G1 G2 W hW)
  ≔ sum_of_groups_aut_path G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW

{` A map r : B → C with r ∘ E = R for equivalences E : A ≃ B, R : A ≃ C is an equivalence. `}
def b8_two_of_three (A B C : Type) (E : Equiv A B) (R : Equiv A C) (r : B → C)
  (h : (a : A) → Id C (r (E .map a)) (R .map a)) : BookIsEquiv B C r
  ≔ let Ei ≔ equiv_inverse_map A B E in
    let Ri ≔ equiv_inverse_map A C R in
    book_equivalence B C (quasi_inverse_equiv B C r (c ↦ E .map (Ri c))
      (b ↦ concat B (E .map (Ri (r b))) (E .map (Ei b)) b
        (refl (E .map) (concat A (Ri (r b)) (Ri (R .map (Ei b))) (Ei b)
          (refl Ri (concat C (r b) (r (E .map (Ei b))) (R .map (Ei b))
            (inverse C (r (E .map (Ei b))) (r b) (refl r (equiv_counit A B E b)))
            (h (Ei b))))
          (equiv_retraction A C R (Ei b))))
        (equiv_counit A B E b))
      (c ↦ concat C (r (E .map (Ri c))) (R .map (Ri c)) c (h (Ri c)) (equiv_counit A C R c))) .equiv

{` First components of component_path. `}
def b8_component_path_fst (A : Type) (a : A) (u v : NativeComponent A a) (p : Id A (u .fst) (v .fst))
  : Id (Id A (u .fst) (v .fst)) (component_path A a u v p .fst) p
  ≔ equiv_counit (Id (NativeComponent A a) u v) (Id A (u .fst) (v .fst))
      (subtype_path_equiv A (x ↦ Mere (Id A a x)) (x ↦ mere_isprop (Id A a x)) u v) p

{` Precomposition with fst : B Aut_W(a12) → (W, a12). `}
def bw_sum_pre (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst)) (G : Group)
  : Equiv (GroupHom (sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) G)
      (GroupHom (blind_group_sum G1 G2 W hW) G)
  ≔ let W' ≔ bridge_wedge_signature (BG G1) (BG G2) W in
    let S ≔ sum_of_groups G1 G2 W' hW in
    let Sb ≔ blind_group_sum G1 G2 W hW in
    let fe ≔ connected_component_pointed_equiv (W .fst)
               (wedge_connected (BG G1) (BG G2) W' (bg_connected G1) (bg_connected G2)) (W .snd .i1 (shape G1)) in
    compose_equiv (GroupHom S G) (BookPointedMap (BG S) (BG G)) (GroupHom Sb G)
      (group_hom_classifying_equiv S G)
      (compose_equiv (BookPointedMap (BG S) (BG G)) (BookPointedMap (BG Sb) (BG G)) (GroupHom Sb G)
        ((k ↦ book_pointed_compose (BG Sb) (BG S) (BG G) (fe .fst) k),
         pointed_precompose_is_equiv (BG Sb) (BG G) (BG S) fe)
        (quasi_inverse_equiv (BookPointedMap (BG Sb) (BG G)) (GroupHom Sb G) (mkhom Sb G) (hom_B Sb G)
          (k ↦ refl k) (u ↦ refl u)))

{` The blind structure maps followed by fst are ours. `}
def bw_sum_in1_compat (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst)) (G : Group)
  (φ : GroupHom (sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) G)
  : Id (GroupHom G1 G)
      (group_hom_compose G1 (blind_group_sum G1 G2 W hW) G (blind_group_sum_in1 G1 G2 W hW)
        (bw_sum_pre G1 G2 W hW G .map φ))
      (group_hom_compose G1 (sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) G
        (sum_of_groups_incl1 G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) φ)
  ≔ let S ≔ sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW in
    let Sb ≔ blind_group_sum G1 G2 W hW in
    let f ≔ hom_B S G φ in
    let a12 ≔ W .snd .i1 (shape G1) in
    let Bc ≔ BG G .carrier in let b ≔ BG G .point in
    let q ≔ f .snd in
    let qr ≔ concat Bc b (f .fst a12) (f .fst a12) q (refl (f .fst) (refl a12)) in
    let j ≔ hom_B G1 Sb (blind_group_sum_in1 G1 G2 W hW) in
    (classifying_map ≔
      (refl ((x ↦ f .fst (W .snd .i1 x)) : BG G1 .carrier → Bc),
       concat (Id Bc b (f .fst a12))
         (concat Bc b (f .fst a12) (f .fst a12) qr (refl (f .fst) (j .snd .fst)))
         (concat Bc b (f .fst a12) (f .fst a12) qr (refl (f .fst) (refl a12)))
         qr
         (refl ((z ↦ concat Bc b (f .fst a12) (f .fst a12) qr (refl (f .fst) z))
                 : Id (W .fst) a12 a12 → Id Bc b (f .fst a12))
           (b8_component_path_fst (W .fst) a12 (component_point (W .fst) a12) (j .fst (shape G1)) (refl a12)))
         (concat_p1 Bc b (f .fst a12) qr)))

def bw_sum_in2_compat (G1 G2 : Group) (W : BlindWedge (BG G1) (BG G2)) (hW : isGroupoid (W .fst)) (G : Group)
  (φ : GroupHom (sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) G)
  : Id (GroupHom G2 G)
      (group_hom_compose G2 (blind_group_sum G1 G2 W hW) G (blind_group_sum_in2 G1 G2 W hW)
        (bw_sum_pre G1 G2 W hW G .map φ))
      (group_hom_compose G2 (sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) G
        (sum_of_groups_incl2 G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW) φ)
  ≔ let S ≔ sum_of_groups G1 G2 (bridge_wedge_signature (BG G1) (BG G2) W) hW in
    let Sb ≔ blind_group_sum G1 G2 W hW in
    let f ≔ hom_B S G φ in
    let a12 ≔ W .snd .i1 (shape G1) in
    let y ≔ W .snd .i2 (shape G2) in
    let gl ≔ W .snd .glue in
    let Bc ≔ BG G .carrier in let b ≔ BG G .point in
    let q ≔ f .snd in
    let qr ≔ concat Bc b (f .fst a12) (f .fst a12) q (refl (f .fst) (refl a12)) in
    let j ≔ hom_B G2 Sb (blind_group_sum_in2 G1 G2 W hW) in
    (classifying_map ≔
      (refl ((x ↦ f .fst (W .snd .i2 x)) : BG G2 .carrier → Bc),
       concat (Id Bc b (f .fst y))
         (concat Bc b (f .fst a12) (f .fst y) qr (refl (f .fst) (j .snd .fst)))
         (concat Bc b (f .fst a12) (f .fst y) qr (refl (f .fst) gl))
         (concat Bc b (f .fst a12) (f .fst y) q (refl (f .fst) gl))
         (refl ((z ↦ concat Bc b (f .fst a12) (f .fst y) qr (refl (f .fst) z))
                 : Id (W .fst) a12 y → Id Bc b (f .fst y))
           (b8_component_path_fst (W .fst) a12 (component_point (W .fst) a12) (j .fst (shape G2)) gl))
         (refl ((z ↦ concat Bc b (f .fst a12) (f .fst y) z (refl (f .fst) gl))
                 : Id Bc b (f .fst a12) → Id Bc b (f .fst y))
           (concat_p1 Bc b (f .fst a12) q))))

{` lem:sumofgroupsISsum. `}
def bridge_lem_sumofgroupsISsum : blind_lem_sumofgroupsISsum
  ≔ G1 G2 G W hW ↦
    let W' ≔ bridge_wedge_signature (BG G1) (BG G2) W in
    let Sb ≔ blind_group_sum G1 G2 W hW in
    b8_two_of_three (GroupHom (sum_of_groups G1 G2 W' hW) G) (GroupHom Sb G) (Product (GroupHom G1 G) (GroupHom G2 G))
      (bw_sum_pre G1 G2 W hW G) (sum_of_groups_hom_equiv G1 G2 W' hW G)
      (phi ↦ (group_hom_compose G1 Sb G (blind_group_sum_in1 G1 G2 W hW) phi,
              group_hom_compose G2 Sb G (blind_group_sum_in2 G1 G2 W hW) phi))
      (φ ↦ (bw_sum_in1_compat G1 G2 W hW G φ, bw_sum_in2_compat G1 G2 W hW G φ))

{` cor:ZplusZuniv. `}
def bridge_cor_ZplusZuniv : blind_cor_ZplusZuniv
  ≔ C W hW G ↦
    let Z ≔ circle_group C in
    let W' ≔ bridge_wedge_signature (BG Z) (BG Z) W in
    let Sb ≔ blind_group_sum Z Z W hW in
    b8_two_of_three (GroupHom (sum_of_groups Z Z W' hW) G) (GroupHom Sb G) (Product (USym G) (USym G))
      (bw_sum_pre Z Z W hW G) (circle_sum_hom_equiv C W' hW G)
      (phi ↦ (usym_hom Z G (group_hom_compose Z Sb G (blind_group_sum_in1 Z Z W hW) phi) (C .loop),
              usym_hom Z G (group_hom_compose Z Sb G (blind_group_sum_in2 Z Z W hW) phi) (C .loop)))
      (φ ↦ (refl ((k ↦ usym_hom Z G k (C .loop)) : GroupHom Z G → USym G) (bw_sum_in1_compat Z Z W hW G φ),
            refl ((k ↦ usym_hom Z G k (C .loop)) : GroupHom Z G → USym G) (bw_sum_in2_compat Z Z W hW G φ)))
