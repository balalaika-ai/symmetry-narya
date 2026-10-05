export "843-sums-of-groups"
export "435-circle-group-homomorphisms"
export "406-symmetric-group-three"

{` Chapter 8 (congp.tex), cor:ZplusZuniv (congp.tex:586) and the motivating
   text of section "Sums of groups".

   Z ≔ circle_group C for an arbitrary circle C (module 404), and S¹ ∨ S¹ is
   an arbitrary wedge signature W of (S¹, base) with itself
   (BG (circle_group C) ≡ circle_pointed C).  The two generators of
   S¹ ∨ S¹ are i1^g(loop) and i2^g(loop).

   - circle_wedge_pointed_maps_equiv: pointed maps S¹ ∨ S¹ →* B are pairs of
     loops of B (lem:univvee and cor:circle-loopspace), for every pointed B
     (the "two independent symmetries" of the motivation; no groupoid
     hypothesis is needed).
   - circle_wedge_generators_noncommuting: for EVERY wedge signature, the two
     generators do not commute; the witness is the pointed map to BΣ_3
     sending them to the transpositions τ = (0 1) and σ = (1 2).
   - cor:ZplusZuniv: for Z ∨ Z ≔ sum_of_groups Z Z W hW (hW: the wedge is a
     groupoid, discharged in module 849 for the constructed S¹ ∨ S¹ and 851
     for every wedge), Hom(Z ∨ Z, G) → Hom(Z, G) × Hom(Z, G) ≃ USym G ×
     USym G is an equivalence (circle_sum_hom_equiv; the first map is
     lem:sumofgroupsISsum, the second ev × ev of module 435); its map is
     evaluation at the two generators (circle_sum_hom_equiv_map). `}

{` Values of the extension of (f1, f2) on i1^g and i2^g, for pointed maps. `}
def wedge_extend_loop1 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f1 : BookPointedMap A1 B) (f2 : BookPointedMap A2 B) (l : Loop A1)
  : Id (Loop B) (loops_map (wedge_pointed A1 A2 W) B (wedge_pointed_extend A1 A2 W B f1 f2) (wedge_loop1 A1 A2 W l))
      (loops_map A1 B f1 l)
  ≔ let V ≔ wedge_pointed A1 A2 W in let F ≔ wedge_pointed_extend A1 A2 W B f1 f2 in
    calc
      loops_map V B F (wedge_loop1 A1 A2 W l)
      = loops_map V B F (loops_map A1 V (wedge_incl1_pointed A1 A2 W) l)
        by refl (loops_map V B F) (wedge_loop1_loops_map A1 A2 W l)
      = loops_map A1 B (book_pointed_compose A1 V B (wedge_incl1_pointed A1 A2 W) F) l
        by inverse (Loop B) (loops_map A1 B (book_pointed_compose A1 V B (wedge_incl1_pointed A1 A2 W) F) l)
          (loops_map V B F (loops_map A1 V (wedge_incl1_pointed A1 A2 W) l))
          (loops_map_compose_pointwise A1 V B (wedge_incl1_pointed A1 A2 W) F l)
      = loops_map A1 B f1 l
        by refl ((h ↦ loops_map A1 B h l) : BookPointedMap A1 B → Loop B) (wedge_restrict_extend_fst A1 A2 W B f1 f2) ∎

def wedge_extend_loop2 (A1 A2 : Pointed) (W : WedgeSignature A1 A2) (B : Pointed)
  (f1 : BookPointedMap A1 B) (f2 : BookPointedMap A2 B) (l : Loop A2)
  : Id (Loop B) (loops_map (wedge_pointed A1 A2 W) B (wedge_pointed_extend A1 A2 W B f1 f2) (wedge_loop2 A1 A2 W l))
      (loops_map A2 B f2 l)
  ≔ let V ≔ wedge_pointed A1 A2 W in let F ≔ wedge_pointed_extend A1 A2 W B f1 f2 in
    calc
      loops_map V B F (wedge_loop2 A1 A2 W l)
      = loops_map A2 B (book_pointed_compose A2 V B (wedge_incl2_pointed A1 A2 W) F) l
        by inverse (Loop B) (loops_map A2 B (book_pointed_compose A2 V B (wedge_incl2_pointed A1 A2 W) F) l)
          (loops_map V B F (loops_map A2 V (wedge_incl2_pointed A1 A2 W) l))
          (loops_map_compose_pointwise A2 V B (wedge_incl2_pointed A1 A2 W) F l)
      = loops_map A2 B f2 l
        by refl ((h ↦ loops_map A2 B h l) : BookPointedMap A2 B → Loop B) (wedge_restrict_extend_snd A1 A2 W B f1 f2) ∎

{` The generators i1^g(loop) and i2^g(loop) of S¹ ∨ S¹. `}
def circle_wedge_generator1 (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : Loop (wedge_pointed (circle_pointed C) (circle_pointed C) W)
  ≔ wedge_loop1 (circle_pointed C) (circle_pointed C) W (C .loop)

def circle_wedge_generator2 (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : Loop (wedge_pointed (circle_pointed C) (circle_pointed C) W)
  ≔ wedge_loop2 (circle_pointed C) (circle_pointed C) W (C .loop)

{` Pointed maps S¹ ∨ S¹ →* B are pairs of symmetries of pt_B. `}
def circle_wedge_pointed_maps_equiv (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (B : Pointed)
  : Equiv (BookPointedMap (wedge_pointed (circle_pointed C) (circle_pointed C) W) B) (Product (Loop B) (Loop B))
  ≔ let P ≔ BookPointedMap (circle_pointed C) B in
    compose_equiv (BookPointedMap (wedge_pointed (circle_pointed C) (circle_pointed C) W) B) (Product P P)
      (Product (Loop B) (Loop B))
      (wedge_pointed_universal_property (circle_pointed C) (circle_pointed C) W B)
      (product_equiv P P (Loop B) (Loop B)
        (pointed_circle_universal_property C (B .carrier) (B .point))
        (pointed_circle_universal_property C (B .carrier) (B .point)))

{` Its map is evaluation (Ω f) at the two generators. `}
def circle_wedge_pointed_maps_equiv_map (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (B : Pointed) (f : BookPointedMap (wedge_pointed (circle_pointed C) (circle_pointed C) W) B)
  : Id (Product (Loop B) (Loop B)) (circle_wedge_pointed_maps_equiv C W B .map f)
      (loops_map (wedge_pointed (circle_pointed C) (circle_pointed C) W) B f (circle_wedge_generator1 C W),
       loops_map (wedge_pointed (circle_pointed C) (circle_pointed C) W) B f (circle_wedge_generator2 C W))
  ≔ let S ≔ circle_pointed C in let V ≔ wedge_pointed S S W in
    (concat (Loop B) (loops_map S B (book_pointed_compose S V B (wedge_incl1_pointed S S W) f) (C .loop))
       (loops_map V B f (loops_map S V (wedge_incl1_pointed S S W) (C .loop)))
       (loops_map V B f (circle_wedge_generator1 C W))
       (loops_map_compose_pointwise S V B (wedge_incl1_pointed S S W) f (C .loop))
       (refl (loops_map V B f) (inverse (Loop V) (wedge_loop1 S S W (C .loop))
         (loops_map S V (wedge_incl1_pointed S S W) (C .loop)) (wedge_loop1_loops_map S S W (C .loop)))),
     loops_map_compose_pointwise S V B (wedge_incl2_pointed S S W) f (C .loop))

{` Litmus: the two generators of S¹ ∨ S¹ do not commute, for every wedge
   signature W (the order of the letters is not negotiable). `}
def circle_wedge_sigma3_map (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : BookPointedMap (wedge_pointed (circle_pointed C) (circle_pointed C) W) (BG (symmetric_group three))
  ≔ wedge_pointed_extend (circle_pointed C) (circle_pointed C) W (BG (symmetric_group three))
      (circle_hom_ve C (symmetric_group three) sigma3_tau) (circle_hom_ve C (symmetric_group three) sigma3_sigma)

def circle_wedge_sigma3_gen1 (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : Id (USym (symmetric_group three))
      (loops_map (wedge_pointed (circle_pointed C) (circle_pointed C) W) (BG (symmetric_group three))
        (circle_wedge_sigma3_map C W) (circle_wedge_generator1 C W)) sigma3_tau
  ≔ concat (USym (symmetric_group three))
      (loops_map (wedge_pointed (circle_pointed C) (circle_pointed C) W) (BG (symmetric_group three))
        (circle_wedge_sigma3_map C W) (circle_wedge_generator1 C W))
      (loops_map (circle_pointed C) (BG (symmetric_group three)) (circle_hom_ve C (symmetric_group three) sigma3_tau) (C .loop))
      sigma3_tau
      (wedge_extend_loop1 (circle_pointed C) (circle_pointed C) W (BG (symmetric_group three))
        (circle_hom_ve C (symmetric_group three) sigma3_tau) (circle_hom_ve C (symmetric_group three) sigma3_sigma) (C .loop))
      (circle_hom_ve_loop C (symmetric_group three) sigma3_tau)

def circle_wedge_sigma3_gen2 (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  : Id (USym (symmetric_group three))
      (loops_map (wedge_pointed (circle_pointed C) (circle_pointed C) W) (BG (symmetric_group three))
        (circle_wedge_sigma3_map C W) (circle_wedge_generator2 C W)) sigma3_sigma
  ≔ concat (USym (symmetric_group three))
      (loops_map (wedge_pointed (circle_pointed C) (circle_pointed C) W) (BG (symmetric_group three))
        (circle_wedge_sigma3_map C W) (circle_wedge_generator2 C W))
      (loops_map (circle_pointed C) (BG (symmetric_group three)) (circle_hom_ve C (symmetric_group three) sigma3_sigma) (C .loop))
      sigma3_sigma
      (wedge_extend_loop2 (circle_pointed C) (circle_pointed C) W (BG (symmetric_group three))
        (circle_hom_ve C (symmetric_group three) sigma3_tau) (circle_hom_ve C (symmetric_group three) sigma3_sigma) (C .loop))
      (circle_hom_ve_loop C (symmetric_group three) sigma3_sigma)

def circle_wedge_generators_noncommuting (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (e : Id (Loop (wedge_pointed (circle_pointed C) (circle_pointed C) W))
    (concat (W .carrier) (W .incl1 (C .base)) (W .incl1 (C .base)) (W .incl1 (C .base))
      (circle_wedge_generator1 C W) (circle_wedge_generator2 C W))
    (concat (W .carrier) (W .incl1 (C .base)) (W .incl1 (C .base)) (W .incl1 (C .base))
      (circle_wedge_generator2 C W) (circle_wedge_generator1 C W)))
  : Empty
  ≔ let V ≔ wedge_pointed (circle_pointed C) (circle_pointed C) W in
    let B ≔ BG (symmetric_group three) in
    let Bc ≔ B .carrier in let b ≔ shape (symmetric_group three) in
    let F ≔ circle_wedge_sigma3_map C W in
    let x ≔ W .incl1 (C .base) in
    let u ≔ circle_wedge_generator1 C W in let v ≔ circle_wedge_generator2 C W in
    let τ ≔ sigma3_tau in let σ ≔ sigma3_sigma in
    sigma3_tau_sigma_noncommuting
      (calc
        concat Bc b b b τ σ
        = concat Bc b b b (loops_map V B F u) (loops_map V B F v)
          by refl (concat Bc b b b)
            (inverse (Loop B) (loops_map V B F u) τ (circle_wedge_sigma3_gen1 C W))
            (inverse (Loop B) (loops_map V B F v) σ (circle_wedge_sigma3_gen2 C W))
        = loops_map V B F (concat (W .carrier) x x x u v)
          by inverse (Loop B) (loops_map V B F (concat (W .carrier) x x x u v))
            (concat Bc b b b (loops_map V B F u) (loops_map V B F v)) (loops_map_concat V B F u v)
        = loops_map V B F (concat (W .carrier) x x x v u) by refl (loops_map V B F) e
        = concat Bc b b b (loops_map V B F v) (loops_map V B F u) by loops_map_concat V B F v u
        = concat Bc b b b σ τ
          by refl (concat Bc b b b) (circle_wedge_sigma3_gen2 C W) (circle_wedge_sigma3_gen1 C W) ∎)

{` cor:ZplusZuniv, for a wedge W that is a groupoid. `}
def circle_sum_group (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) : Group
  ≔ sum_of_groups (circle_group C) (circle_group C) W hW

def circle_sum_hom_ev (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (G : Group) (f : GroupHom (circle_sum_group C W hW) G) : Product (USym G) (USym G)
  ≔ (circle_group_hom_ev C G .map (sum_of_groups_restrict (circle_group C) (circle_group C) W hW G f .fst),
     circle_group_hom_ev C G .map (sum_of_groups_restrict (circle_group C) (circle_group C) W hW G f .snd))

def circle_sum_hom_equiv (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (G : Group)
  : Equiv (GroupHom (circle_sum_group C W hW) G) (Product (USym G) (USym G))
  ≔ let Z ≔ circle_group C in
    equiv_change_map (GroupHom (circle_sum_group C W hW) G) (Product (USym G) (USym G))
      (compose_equiv (GroupHom (circle_sum_group C W hW) G) (Product (GroupHom Z G) (GroupHom Z G)) (Product (USym G) (USym G))
        (sum_of_groups_hom_equiv Z Z W hW G)
        (product_equiv (GroupHom Z G) (GroupHom Z G) (USym G) (USym G) (circle_group_hom_ev C G) (circle_group_hom_ev C G)))
      (circle_sum_hom_ev C W hW G)
      (f ↦ refl (circle_sum_hom_ev C W hW G f))

def circle_sum_hom_book_equiv (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (G : Group)
  : BookIsEquiv (GroupHom (circle_sum_group C W hW) G) (Product (USym G) (USym G)) (circle_sum_hom_ev C W hW G)
  ≔ book_equivalence (GroupHom (circle_sum_group C W hW) G) (Product (USym G) (USym G))
      (circle_sum_hom_equiv C W hW G) .equiv

{` The map of cor:ZplusZuniv is evaluation at the two generators. `}
def circle_sum_hom_equiv_map (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (G : Group) (f : GroupHom (circle_sum_group C W hW) G)
  : Id (Product (USym G) (USym G)) (circle_sum_hom_ev C W hW G f)
      (usym_hom (circle_sum_group C W hW) G f (circle_wedge_generator1 C W),
       usym_hom (circle_sum_group C W hW) G f (circle_wedge_generator2 C W))
  ≔ circle_wedge_pointed_maps_equiv_map C W (BG G) (hom_B (circle_sum_group C W hW) G f)

{` The inverse: the homomorphism sending the generators to g1 and g2. `}
def circle_sum_hom_from_symmetries (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (G : Group) (g1 g2 : USym G) : GroupHom (circle_sum_group C W hW) G
  ≔ sum_of_groups_hom_extend (circle_group C) (circle_group C) W hW G
      (circle_group_hom_from_symmetry C G g1) (circle_group_hom_from_symmetry C G g2)

def circle_sum_hom_from_symmetries_gen1 (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (G : Group) (g1 g2 : USym G)
  : Id (USym G) (usym_hom (circle_sum_group C W hW) G (circle_sum_hom_from_symmetries C W hW G g1 g2)
      (circle_wedge_generator1 C W)) g1
  ≔ concat (USym G)
      (usym_hom (circle_sum_group C W hW) G (circle_sum_hom_from_symmetries C W hW G g1 g2) (circle_wedge_generator1 C W))
      (usym_hom (circle_group C) G (circle_group_hom_from_symmetry C G g1) (circle_group_loop C)) g1
      (sum_of_groups_extend_loop1 (circle_group C) (circle_group C) W hW G
        (circle_group_hom_from_symmetry C G g1) (circle_group_hom_from_symmetry C G g2) (C .loop))
      (circle_group_hom_from_symmetry_loop C G g1)

def circle_sum_hom_from_symmetries_gen2 (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (G : Group) (g1 g2 : USym G)
  : Id (USym G) (usym_hom (circle_sum_group C W hW) G (circle_sum_hom_from_symmetries C W hW G g1 g2)
      (circle_wedge_generator2 C W)) g2
  ≔ concat (USym G)
      (usym_hom (circle_sum_group C W hW) G (circle_sum_hom_from_symmetries C W hW G g1 g2) (circle_wedge_generator2 C W))
      (usym_hom (circle_group C) G (circle_group_hom_from_symmetry C G g2) (circle_group_loop C)) g2
      (sum_of_groups_extend_loop2 (circle_group C) (circle_group C) W hW G
        (circle_group_hom_from_symmetry C G g1) (circle_group_hom_from_symmetry C G g2) (C .loop))
      (circle_group_hom_from_symmetry_loop C G g2)

{` Instance at Σ_3 with the transpositions τ = (0 1), σ = (1 2). `}
def circle_sum_sigma3_hom (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) : GroupHom (circle_sum_group C W hW) (symmetric_group three)
  ≔ circle_sum_hom_from_symmetries C W hW (symmetric_group three) sigma3_tau sigma3_sigma

{` In Z ∨ Z the two generators do not commute; Z ∨ Z is not abelian. `}
def circle_sum_generators_noncommuting (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier))
  (e : Id (USym (circle_sum_group C W hW))
    (usym_mul (circle_sum_group C W hW) (circle_wedge_generator1 C W) (circle_wedge_generator2 C W))
    (usym_mul (circle_sum_group C W hW) (circle_wedge_generator2 C W) (circle_wedge_generator1 C W)))
  : Empty
  ≔ circle_wedge_generators_noncommuting C W
      (inverse (USym (circle_sum_group C W hW))
        (usym_mul (circle_sum_group C W hW) (circle_wedge_generator1 C W) (circle_wedge_generator2 C W))
        (usym_mul (circle_sum_group C W hW) (circle_wedge_generator2 C W) (circle_wedge_generator1 C W)) e)

def circle_sum_not_abelian (C : CircleSignature) (W : WedgeSignature (circle_pointed C) (circle_pointed C))
  (hW : isGroupoid (W .carrier)) (h : IsAbelian (circle_sum_group C W hW)) : Empty
  ≔ circle_sum_generators_noncommuting C W hW (h (circle_wedge_generator1 C W) (circle_wedge_generator2 C W))
