export "908-fundamental-theorem-homs"
export "821-pullback-groups"

{` Chapter 9 (subgroups.tex), sec "Intersecting with normal subgroups":
   lem:whatSylow2needs. The pullback/intersection of groups is
   def:intersectionofgroups of congp.tex (chapter 8, line 457; the copy in
   subgroups.tex is commented out), formalized by chapter 8 as
   pullback_group G H H' f f' (module 821): the component of BH ×_{BG} BH'
   at (sh_H, sh_H', p_f⁻¹ · p_f'). For monomorphisms it is the intersection
   H ∩ H' (group_mono_intersection, module 822). `}

{` lem:whatSylow2needs. Let f : Hom(G, G') have connected fibers (an
   epimorphism, lem:epi-surj), N ≔ ker f and (H, i) a monomorphism. The
   pullback BN ×_BG BH is identified with the fiber of B(fi) at sh_{G'}
   (contracting away y : BG), compatibly with the base points. `}
def WsnPullback (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) : Type
  ≔ pbg_space G (kernel_group G G' f) H (kernel_inclusion G G' f) i

def wsn_to_fiber (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (t : WsnPullback G G' H f i)
  : HomFiber H G' (group_hom_compose H G G' i f) (shape G')
  ≔ (t .fst .snd,
     concat (BG G' .carrier) (shape G') (hom_function G G' f (t .fst .fst .fst .fst))
       (hom_function G G' f (hom_function H G i (t .fst .snd)))
       (t .fst .fst .fst .snd)
       (map_path (BG G .carrier) (BG G' .carrier) (hom_function G G' f) (t .fst .fst .fst .fst)
         (hom_function H G i (t .fst .snd)) (t .snd)))

def wsn_from_fiber (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  (u : HomFiber H G' (group_hom_compose H G G' i f) (shape G')) : WsnPullback G G' H f i
  ≔ let y ≔ hom_function H G i (u .fst) in
    ((((y, u .snd), c (shape G') .snd (kernel_shape G G' f) (y, u .snd)), u .fst), refl y)

def wsn_to_from (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  (u : HomFiber H G' (group_hom_compose H G G' i f) (shape G'))
  : Id (HomFiber H G' (group_hom_compose H G G' i f) (shape G'))
      (wsn_to_fiber G G' H f i (wsn_from_fiber G G' H f i c u)) u
  ≔ let B' ≔ BG G' .carrier in
    let y ≔ hom_function H G i (u .fst) in
    map_path (Id B' (shape G') (hom_function G G' f y)) (HomFiber H G' (group_hom_compose H G G' i f) (shape G'))
      (q ↦ (u .fst, q)) (concat B' (shape G') (hom_function G G' f y) (hom_function G G' f y) (u .snd) (refl (hom_function G G' f y)))
      (u .snd) (concat_p1 B' (shape G') (hom_function G G' f y) (u .snd))

{` from ∘ to = id, by contracting r : y = Bi(x) (based path space at Bi x). `}
def wsn_from_to (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  (t : WsnPullback G G' H f i)
  : Id (WsnPullback G G' H f i) (wsn_from_fiber G G' H f i c (wsn_to_fiber G G' H f i t)) t
  ≔ let B ≔ BG G .carrier in let B' ≔ BG G' .carrier in
    let Bf ≔ hom_function G G' f in
    let F ≔ HomFiber G G' f (shape G') in
    let BN ≔ BG (kernel_group G G' f) .carrier in
    let P ≔ WsnPullback G G' H f i in
    let x ≔ t .fst .snd in
    let b ≔ hom_function H G i x in
    let T ≔ Σ B (y ↦ Id B y b) in
    let ctr ≔ path_to_contractible B b in
    let Q : T → Type
      ≔ w ↦ (q : Id B' (shape G') (Bf (w .fst))) (m : Mere (Id F (kernel_shape G G' f) (w .fst, q)))
          → Id P (wsn_from_fiber G G' H f i c (wsn_to_fiber G G' H f i ((((w .fst, q), m), x), w .snd)))
                 ((((w .fst, q), m), x), w .snd) in
    let base : Q (b, refl b)
      ≔ q m ↦
        let q' ≔ concat B' (shape G') (Bf b) (Bf b) q (refl (Bf b)) in
        let S0 ≔ Σ (Id B' (shape G') (Bf b)) (r ↦ Mere (Id F (kernel_shape G G' f) (b, r))) in
        let g : S0 → P ≔ s ↦ ((((b, s .fst), s .snd), x), refl b) in
        map_path S0 P g (q', c (shape G') .snd (kernel_shape G G' f) (b, q')) (q, m)
          (subtype_equal (Id B' (shape G') (Bf b)) (r ↦ Mere (Id F (kernel_shape G G' f) (b, r)))
            (r ↦ mere_isprop (Id F (kernel_shape G G' f) (b, r)))
            (q', c (shape G') .snd (kernel_shape G G' f) (b, q')) (q, m) (concat_p1 B' (shape G') (Bf b) q)) in
    transport T Q (b, refl b) (t .fst .fst .fst .fst, t .snd)
      (concat T (b, refl b) (ctr .center) (t .fst .fst .fst .fst, t .snd) (ctr .contract (b, refl b))
        (inverse T (t .fst .fst .fst .fst, t .snd) (ctr .center) (ctr .contract (t .fst .fst .fst .fst, t .snd))))
      base (t .fst .fst .fst .snd) (t .fst .fst .snd)

def wsn_equiv (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : Equiv (WsnPullback G G' H f i) (HomFiber H G' (group_hom_compose H G G' i f) (shape G'))
  ≔ quasi_inverse_equiv (WsnPullback G G' H f i) (HomFiber H G' (group_hom_compose H G G' i f) (shape G'))
      (wsn_to_fiber G G' H f i) (wsn_from_fiber G G' H f i c) (wsn_from_to G G' H f i c) (wsn_to_from G G' H f i c)

{` The base point of the pullback goes to (sh_H, p_{fi}), p_{fi} = Bf(p_i)·Bf_pt
   (concatenation order: first Bf_pt). `}
def wsn_base_path (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G)
  : Id (HomFiber H G' (group_hom_compose H G G' i f) (shape G'))
      (kernel_shape H G' (group_hom_compose H G G' i f))
      (wsn_to_fiber G G' H f i (pbg_point G (kernel_group G G' f) H (kernel_inclusion G G' f) i))
  ≔ let B ≔ BG G .carrier in let B' ≔ BG G' .carrier in
    let Bf ≔ hom_function G G' f in
    let sH ≔ shape H in
    let y ≔ hom_function H G i sH in
    let pi ≔ hom_point H G i in
    let r0 ≔ concat B (shape G) (shape G) y (inverse B (shape G) (shape G) (refl (shape G))) pi in
    let e : Id (Id B (shape G) y) pi r0
      ≔ calc
          pi
          = concat B (shape G) (shape G) y (refl (shape G)) pi by inverse (Id B (shape G) y) (concat B (shape G) (shape G) y (refl (shape G)) pi) pi (concat_1p B (shape G) y pi)
          = r0 by refl ((s ↦ concat B (shape G) (shape G) y s pi) : Id B (shape G) (shape G) → Id B (shape G) y)
                    (inverse (Id B (shape G) (shape G)) (inverse B (shape G) (shape G) (refl (shape G))) (refl (shape G))
                      (inverse_refl B (shape G))) ∎ in
    map_path (Id B' (shape G') (Bf y)) (HomFiber H G' (group_hom_compose H G G' i f) (shape G')) (q ↦ (sH, q))
      (concat B' (shape G') (Bf (shape G)) (Bf y) (hom_point G G' f) (map_path B B' Bf (shape G) y pi))
      (concat B' (shape G') (Bf (shape G)) (Bf y) (hom_point G G' f) (map_path B B' Bf (shape G) y r0))
      (refl ((s ↦ concat B' (shape G') (Bf (shape G)) (Bf y) (hom_point G G' f) (map_path B B' Bf (shape G) y s))
               : Id B (shape G) y → Id B' (shape G') (Bf y)) e)

{` N ∩ H ≅ Ker(fi), compatibly with the maps to H. `}
def wsn_iso_map (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : BG (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i) .carrier
    → BG (kernel_group H G' (group_hom_compose H G G' i f)) .carrier
  ≔ let K ≔ group_hom_compose H G G' i f in
    let Fk ≔ HomFiber H G' K (shape G') in
    let P ≔ WsnPullback G G' H f i in
    let p0 ≔ pbg_point G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    u ↦ (wsn_to_fiber G G' H f i (u .fst),
         mere_rec (Id P p0 (u .fst)) (Mere (Id Fk (kernel_shape H G' K) (wsn_to_fiber G G' H f i (u .fst))))
           (mere_isprop (Id Fk (kernel_shape H G' K) (wsn_to_fiber G G' H f i (u .fst))))
           (r ↦ mere (Id Fk (kernel_shape H G' K) (wsn_to_fiber G G' H f i (u .fst)))
             (concat Fk (kernel_shape H G' K) (wsn_to_fiber G G' H f i p0) (wsn_to_fiber G G' H f i (u .fst))
               (wsn_base_path G G' H f i) (map_path P Fk (wsn_to_fiber G G' H f i) p0 (u .fst) r)))
           (u .snd))

def wsn_iso_point (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : Id (BG (kernel_group H G' (group_hom_compose H G G' i f)) .carrier)
      (shape (kernel_group H G' (group_hom_compose H G G' i f)))
      (wsn_iso_map G G' H f i c (shape (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i)))
  ≔ let K ≔ group_hom_compose H G G' i f in
    component_path (HomFiber H G' K (shape G')) (kernel_shape H G' K)
      (shape (kernel_group H G' K))
      (wsn_iso_map G G' H f i c (shape (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i)))
      (wsn_base_path G G' H f i)

def wsn_iso_hom (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : GroupHom (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
      (kernel_group H G' (group_hom_compose H G G' i f))
  ≔ mkhom (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
      (kernel_group H G' (group_hom_compose H G G' i f)) (wsn_iso_map G G' H f i c, wsn_iso_point G G' H f i c)

def wsn_iso (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : IsGroupIso (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
      (kernel_group H G' (group_hom_compose H G G' i f)) (wsn_iso_hom G G' H f i c)
  ≔ let I ≔ pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    let K ≔ kernel_group H G' (group_hom_compose H G G' i f) in
    let P ≔ WsnPullback G G' H f i in
    let Fk ≔ HomFiber H G' (group_hom_compose H G G' i f) (shape G') in
    let p0 ≔ pbg_point G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    let k0 ≔ kernel_shape H G' (group_hom_compose H G G' i f) in
    let Th ≔ wsn_iso_map G G' H f i c in
    let to ≔ wsn_to_fiber G G' H f i in
    native_connected_map_equiv_from_paths (BG I .carrier) (BG K .carrier) Th (bg_connected I) (bg_connected K)
      (u v ↦
        let cu ≔ component_path_equiv P p0 u v in
        let cv ≔ component_path_equiv Fk k0 (Th u) (Th v) in
        let e ≔ compose_equiv (Id (BG I .carrier) u v) (Id P (u .fst) (v .fst)) (Id (BG K .carrier) (Th u) (Th v)) cu
          (compose_equiv (Id P (u .fst) (v .fst)) (Id Fk (to (u .fst)) (to (v .fst))) (Id (BG K .carrier) (Th u) (Th v))
            (native_equivalence (Id P (u .fst) (v .fst)) (Id Fk (to (u .fst)) (to (v .fst)))
              (map_path P Fk to (u .fst) (v .fst),
               map_equiv_to_paths P Fk to (book_equivalence P Fk (wsn_equiv G G' H f i c) .equiv) (u .fst) (v .fst)))
            (canonical_inverse_equiv (Id (BG K .carrier) (Th u) (Th v)) (Id Fk (to (u .fst)) (to (v .fst))) cv)) in
        book_equivalence (Id (BG I .carrier) u v) (Id (BG K .carrier) (Th u) (Th v))
          (equiv_change_map (Id (BG I .carrier) u v) (Id (BG K .carrier) (Th u) (Th v)) e
            (map_path (BG I .carrier) (BG K .carrier) Th u v)
            (r ↦ equiv_retraction (Id (BG K .carrier) (Th u) (Th v)) (Id Fk (to (u .fst)) (to (v .fst))) cv
              (map_path (BG I .carrier) (BG K .carrier) Th u v r)))
        .equiv)
    .equiv

def wsn_iso_compose (G G' H : Group) (f : GroupHom G G') (i : GroupHom H G) (c : IsConnectedHom G G' f)
  : Id (GroupHom (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i) H)
      (group_hom_compose (pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
        (kernel_group H G' (group_hom_compose H G G' i f)) H (wsn_iso_hom G G' H f i c)
        (kernel_inclusion H G' (group_hom_compose H G G' i f)))
      (pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i)
  ≔ let I ≔ pullback_group G (kernel_group G G' f) H (kernel_inclusion G G' f) i in
    let BH ≔ BG H .carrier in
    let comp ≔ group_hom_compose I (kernel_group H G' (group_hom_compose H G G' i f)) H (wsn_iso_hom G G' H f i c)
      (kernel_inclusion H G' (group_hom_compose H G G' i f)) in
    equiv_inverse_map (Id (GroupHom I H) comp (pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i))
      (PointedHomotopy (BG I) (BG H) (hom_B I H comp) (hom_B I H (pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i)))
      (group_hom_path_equiv I H comp (pullback_group_proj_right G (kernel_group G G' f) H (kernel_inclusion G G' f) i))
      (u ↦ refl (u .fst .fst .snd),
       calc
         concat BH (shape H) (shape H) (shape H) (hom_point I H comp) (refl (shape H))
         = hom_point I H comp by concat_p1 BH (shape H) (shape H) (hom_point I H comp)
         = refl (shape H) by concat_p1 BH (shape H) (shape H) (refl (shape H)) ∎)
