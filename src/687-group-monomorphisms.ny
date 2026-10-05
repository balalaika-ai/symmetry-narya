export "686-category-of-groups"
export "609-monos-and-epis"
export "431-homomorphism-remarks"
export "405-integer-group"

{` Chapter 6 (cats.tex), xca:mono-cat-grp (line 545): the monomorphisms of
   the category of groups GroupCat (def:mono-in-cat: post-composition
   i ∘ - : Hom(K, H) → Hom(K, G) is an injection for every group K; IsMono
   of module 609) are exactly the monomorphisms of def:typeofmono
   (actions.tex 918): the homomorphisms i : Hom(H, G) such that
   USym i : USym H → USym G is an injection (all preimages are
   propositions). The chapter-5 predicate is not named here; its unfolded
   condition IsEmbedding (USym H) (USym G) (usym_hom H G i) is used.

   (⇐) If USym i is injective, then by connectedness of BH every
   ap_{Bi} : (y = y') → (Bi y = Bi y') is injective (cor:fib-vs-path), and
   post-composition with Bi on pointed maps out of the connected type BK
   reflects identifications.
   (⇒) Test with K = Z (integer_group, the group of the constructed
   circle): homomorphisms Z → H are the symmetries of H via
   f ↦ USym f (loop) (the pointed universal property of the circle), and
   this identification is natural in H (loops_map_compose). `}

{` Path algebra for the pointing of a pointed homotopy between composites
   k ∘ f and k ∘ f': if k_pt · ap_k(p) · w = k_pt · ap_k(p') (concatenation
   order), then w = ap_k(p⁻¹ · p'). First the case p = refl. `}
def grp_mono_pointing_base (Y Z : Type) (k : Y → Z) (y0 : Y) (z0 : Z) (kpt : Id Z z0 (k y0))
  (a' : Y) (p' : Id Y y0 a') (w : Id Z (k y0) (k a'))
  (hp : Id (Id Z z0 (k a')) (concat Z z0 (k y0) (k a') (concat Z z0 (k y0) (k y0) kpt (refl (k y0))) w)
          (concat Z z0 (k y0) (k a') kpt (map_path Y Z k y0 a' p')))
  : Id (Id Z (k y0) (k a')) w (map_path Y Z k y0 a' (concat Y y0 y0 a' (inverse Y y0 y0 (refl y0)) p'))
  ≔ let L ≔ Id Z z0 (k a') in
    let s : Id L (concat Z z0 (k y0) (k a') kpt w) (concat Z z0 (k y0) (k a') kpt (map_path Y Z k y0 a' p'))
      ≔ concat L (concat Z z0 (k y0) (k a') kpt w)
          (concat Z z0 (k y0) (k a') (concat Z z0 (k y0) (k y0) kpt (refl (k y0))) w)
          (concat Z z0 (k y0) (k a') kpt (map_path Y Z k y0 a' p'))
          (refl ((t ↦ concat Z z0 (k y0) (k a') t w) : Id Z z0 (k y0) → L)
            (inverse (Id Z z0 (k y0)) (concat Z z0 (k y0) (k y0) kpt (refl (k y0))) kpt
              (concat_p1 Z z0 (k y0) kpt)))
          hp in
    concat (Id Z (k y0) (k a')) w (map_path Y Z k y0 a' p')
      (map_path Y Z k y0 a' (concat Y y0 y0 a' (inverse Y y0 y0 (refl y0)) p'))
      (concat_cancel_left Z z0 (k y0) (k a') kpt w (map_path Y Z k y0 a' p') s)
      (refl (map_path Y Z k y0 a')
        (inverse (Id Y y0 a') (concat Y y0 y0 a' (inverse Y y0 y0 (refl y0)) p') p'
          (inverse_refl_concat Y y0 a' p')))

def grp_mono_pointing_lemma (Y Z : Type) (k : Y → Z) (y0 : Y) (z0 : Z) (kpt : Id Z z0 (k y0))
  (a : Y) (p : Id Y y0 a) (a' : Y) (p' : Id Y y0 a') (w : Id Z (k a) (k a'))
  (hp : Id (Id Z z0 (k a')) (concat Z z0 (k a) (k a') (concat Z z0 (k y0) (k a) kpt (map_path Y Z k y0 a p)) w)
          (concat Z z0 (k y0) (k a') kpt (map_path Y Z k y0 a' p')))
  : Id (Id Z (k a) (k a')) w (map_path Y Z k a a' (concat Y a y0 a' (inverse Y y0 a p) p'))
  ≔ J Y y0
      (a p ↦ (w : Id Z (k a) (k a')) →
        Id (Id Z z0 (k a')) (concat Z z0 (k a) (k a') (concat Z z0 (k y0) (k a) kpt (map_path Y Z k y0 a p)) w)
          (concat Z z0 (k y0) (k a') kpt (map_path Y Z k y0 a' p')) →
        Id (Id Z (k a) (k a')) w (map_path Y Z k a a' (concat Y a y0 a' (inverse Y y0 a p) p')))
      (w hp ↦ grp_mono_pointing_base Y Z k y0 z0 kpt a' p' w hp) a p w hp

{` Post-composition with a pointed map k : Y →* Z all of whose maps
   ap_k : (y = y') → (k y = k y') are injections reflects identifications of
   pointed maps out of a connected pointed type X: a pointed homotopy
   k ∘ f ~ k ∘ f' lifts to a pointed homotopy f ~ f'. The lift at x is the
   unique preimage of the given homotopy at x under ap_k (unique since ap_k is
   an injection; it exists at the base point by the path algebra above, hence
   everywhere by connectedness). `}
def pointed_postcompose_homotopy_lift (X Y Z : Pointed) (hX : Connected (X .carrier))
  (k : BookPointedMap Y Z)
  (E : (y y' : Y .carrier) → IsEmbedding (Id (Y .carrier) y y') (Id (Z .carrier) (k .fst y) (k .fst y'))
         (map_path (Y .carrier) (Z .carrier) (k .fst) y y'))
  (f f' : BookPointedMap X Y)
  (r : PointedHomotopy X Z (book_pointed_compose X Y Z f k) (book_pointed_compose X Y Z f' k))
  : PointedHomotopy X Y f f'
  ≔ let A ≔ X .carrier in let B ≔ Y .carrier in let C ≔ Z .carrier in let x0 ≔ X .point in
    let D : A → Type ≔ x ↦ BookFiber (Id B (f .fst x) (f' .fst x)) (Id C (k .fst (f .fst x)) (k .fst (f' .fst x)))
        (map_path B C (k .fst) (f .fst x) (f' .fst x)) (r .fst x) in
    let hD : (x : A) → isProp (D x) ≔ x ↦ E (f .fst x) (f' .fst x) (r .fst x) in
    let q0 : Id B (f .fst x0) (f' .fst x0)
      ≔ concat B (f .fst x0) (Y .point) (f' .fst x0) (inverse B (Y .point) (f .fst x0) (f .snd)) (f' .snd) in
    let d0 : D x0 ≔ (q0, grp_mono_pointing_lemma B C (k .fst) (Y .point) (Z .point) (k .snd)
        (f .fst x0) (f .snd) (f' .fst x0) (f' .snd) (r .fst x0) (r .snd)) in
    let d : (x : A) → D x ≔ connected_based_elim native_truncation A hX x0 D hD d0 in
    (x ↦ d x .fst,
     concat (Id B (Y .point) (f' .fst x0))
       (concat B (Y .point) (f .fst x0) (f' .fst x0) (f .snd) (d x0 .fst))
       (concat B (Y .point) (f .fst x0) (f' .fst x0) (f .snd) q0) (f' .snd)
       (refl (concat B (Y .point) (f .fst x0) (f' .fst x0) (f .snd)) (hD x0 (d x0) d0 .fst))
       (concat_left_right_inverse B (Y .point) (f .fst x0) (f' .fst x0) (f .snd) (f' .snd)))

{` If USym i = Ω(Bi) is injective, then ap_{Bi} at the shape is injective
   (Ω(Bi) is ap_{Bi} followed by conjugation with Bi_pt), and then, BH being
   connected, every ap_{Bi} : (y = y') → (Bi y = Bi y') is injective
   (cor:fib-vs-path: Bi has set fibers). `}
def usym_injective_base_ap_embedding (H G : Group) (i : GroupHom H G)
  (e : IsEmbedding (USym H) (USym G) (usym_hom H G i))
  : IsEmbedding (USym H) (Id (BG G .carrier) (hom_function H G i (shape H)) (hom_function H G i (shape H)))
      (map_path (BG H .carrier) (BG G .carrier) (hom_function H G i) (shape H) (shape H))
  ≔ let B ≔ BG G .carrier in let b ≔ hom_function H G i (shape H) in
    path_reflecting_set_embedding (USym H) (Id B b b) (bg_groupoid G b b)
      (map_path (BG H .carrier) B (hom_function H G i) (shape H) (shape H))
      (l l' s ↦ embedding_reflects_paths (USym H) (USym G) (usym_hom H G i) e l l'
        (refl (pointed_loop_conjugate B (shape G) b (hom_point H G i)) s))

def usym_injective_ap_embedding (H G : Group) (i : GroupHom H G)
  (e : IsEmbedding (USym H) (USym G) (usym_hom H G i))
  : (y y' : BG H .carrier) → IsEmbedding (Id (BG H .carrier) y y')
      (Id (BG G .carrier) (hom_function H G i y) (hom_function H G i y'))
      (map_path (BG H .carrier) (BG G .carrier) (hom_function H G i) y y')
  ≔ let A ≔ BG H .carrier in let B ≔ BG G .carrier in let k ≔ hom_function H G i in
    connected_pair_elim native_truncation A (bg_connected H) (shape H)
      (y y' ↦ IsEmbedding (Id A y y') (Id B (k y) (k y')) (map_path A B k y y'))
      (y y' ↦ embedding_prop (Id A y y') (Id B (k y) (k y')) (map_path A B k y y'))
      (usym_injective_base_ap_embedding H G i e)

{` xca:mono-cat-grp, (⇐): a monomorphism in the sense of def:typeofmono is
   a monomorphism of the category of groups. Hom-types are sets
   (group_hom_set), so it suffices that i ∘ - reflects identifications. `}
def usym_injective_group_mono (H G : Group) (i : GroupHom H G)
  (e : IsEmbedding (USym H) (USym G) (usym_hom H G i)) : IsMono (GroupCat .wild) H G i
  ≔ K ↦ path_reflecting_set_embedding (GroupHom K H) (GroupHom K G) (group_hom_set K G)
      (f ↦ group_hom_compose K H G f i)
      (f f' r ↦ equiv_inverse_map (Id (GroupHom K H) f f')
        (PointedHomotopy (BG K) (BG H) (hom_B K H f) (hom_B K H f'))
        (group_hom_path_equiv K H f f')
        (pointed_postcompose_homotopy_lift (BG K) (BG H) (BG G) (bg_connected K) (hom_B H G i)
          (usym_injective_ap_embedding H G i e) (hom_B K H f) (hom_B K H f')
          (group_hom_path_equiv K G (group_hom_compose K H G f i) (group_hom_compose K H G f' i) .map r)))

{` Homomorphisms out of Z = circle_group C correspond to symmetries:
   the homomorphism with Bf = the pointed map S¹ →* BH sending loop to g,
   and f ↦ USym f (loop) is injective (cor:circle-loopspace, module 129). `}
def circle_group_hom_from_loop (C : CircleSignature) (H : Group) (g : USym H) : GroupHom (circle_group C) H
  ≔ mkhom (circle_group C) H (pointed_circle_loop_rec C (BG H .carrier) (shape H) g)

def circle_group_hom_from_loop_beta (C : CircleSignature) (H : Group) (g : USym H)
  : Id (USym H) (usym_hom (circle_group C) H (circle_group_hom_from_loop C H g) (C .loop)) g
  ≔ pointed_circle_loop_rec_beta C (BG H .carrier) (shape H) g

def circle_group_hom_eval_reflects (C : CircleSignature) (G : Group) (f f' : GroupHom (circle_group C) G)
  (s : Id (USym G) (usym_hom (circle_group C) G f (C .loop)) (usym_hom (circle_group C) G f' (C .loop)))
  : Id (GroupHom (circle_group C) G) f f'
  ≔ refl (mkhom (circle_group C) G)
      (equivalence_injective (BookPointedMap (circle_pointed C) (BG G .carrier, shape G)) (USym G)
        (pointed_circle_universal_property C (BG G .carrier) (shape G)) (hom_B (circle_group C) G f)
        (hom_B (circle_group C) G f') s)

{` (⇒) with the test group Z = circle_group C: if USym i g = USym i g',
   the homomorphisms f, f' : Z → H classifying g, g' satisfy
   USym (i ∘ f) (loop) = USym i (g) = USym i (g') = USym (i ∘ f') (loop),
   hence i ∘ f = i ∘ f', hence f = f' (i is a mono), hence g = g'. `}
def group_mono_usym_reflects (C : CircleSignature) (H G : Group) (i : GroupHom H G)
  (m : IsMono (GroupCat .wild) H G i) (g g' : USym H)
  (s : Id (USym G) (usym_hom H G i g) (usym_hom H G i g')) : Id (USym H) g g'
  ≔ let Z ≔ circle_group C in
    let f ≔ circle_group_hom_from_loop C H g in
    let f' ≔ circle_group_hom_from_loop C H g' in
    let ev : GroupHom Z H → USym H ≔ u ↦ usym_hom Z H u (C .loop) in
    let t : Id (USym G) (usym_hom Z G (group_hom_compose Z H G f i) (C .loop))
        (usym_hom Z G (group_hom_compose Z H G f' i) (C .loop))
      ≔ calc
          usym_hom Z G (group_hom_compose Z H G f i) (C .loop)
          = usym_hom H G i (ev f)
            by loops_map_compose_pointwise (BG Z) (BG H) (BG G) (hom_B Z H f) (hom_B H G i) (C .loop)
          = usym_hom H G i g by refl (usym_hom H G i) (circle_group_hom_from_loop_beta C H g)
          = usym_hom H G i g' by s
          = usym_hom H G i (ev f')
            by refl (usym_hom H G i) (inverse (USym H) (ev f') g' (circle_group_hom_from_loop_beta C H g'))
          = usym_hom Z G (group_hom_compose Z H G f' i) (C .loop)
            by inverse (USym G) (usym_hom Z G (group_hom_compose Z H G f' i) (C .loop)) (usym_hom H G i (ev f'))
                 (loops_map_compose_pointwise (BG Z) (BG H) (BG G) (hom_B Z H f') (hom_B H G i) (C .loop)) ∎ in
    let q : Id (GroupHom Z H) f f'
      ≔ embedding_reflects_paths (GroupHom Z H) (GroupHom Z G) (u ↦ group_hom_compose Z H G u i) (m Z) f f'
          (circle_group_hom_eval_reflects C G (group_hom_compose Z H G f i) (group_hom_compose Z H G f' i) t) in
    calc
      g = ev f by inverse (USym H) (ev f) g (circle_group_hom_from_loop_beta C H g)
      = ev f' by refl ev q
      = g' by circle_group_hom_from_loop_beta C H g' ∎

{` xca:mono-cat-grp, (⇒), with K = integer_group = circle_group
   constructed_circle as the test object. USym G is a set, so path
   reflection suffices. `}
def group_mono_usym_injective (H G : Group) (i : GroupHom H G) (m : IsMono (GroupCat .wild) H G i)
  : IsEmbedding (USym H) (USym G) (usym_hom H G i)
  ≔ path_reflecting_set_embedding (USym H) (USym G) (usym_set G) (usym_hom H G i)
      (group_mono_usym_reflects constructed_circle H G i m)

{` xca:mono-cat-grp: the two notions of monomorphism coincide, as an
   equivalence of propositions for each homomorphism and on the types of
   monomorphisms from H to G. `}
def group_mono_iff_usym_injective (H G : Group) (i : GroupHom H G)
  : Product (IsMono (GroupCat .wild) H G i → IsEmbedding (USym H) (USym G) (usym_hom H G i))
      (IsEmbedding (USym H) (USym G) (usym_hom H G i) → IsMono (GroupCat .wild) H G i)
  ≔ (group_mono_usym_injective H G i, usym_injective_group_mono H G i)

def group_mono_usym_injective_equiv (H G : Group) (i : GroupHom H G)
  : Equiv (IsMono (GroupCat .wild) H G i) (IsEmbedding (USym H) (USym G) (usym_hom H G i))
  ≔ iff_equiv (IsMono (GroupCat .wild) H G i) (IsEmbedding (USym H) (USym G) (usym_hom H G i))
      (is_mono_prop (GroupCat .wild) H G i) (embedding_prop (USym H) (USym G) (usym_hom H G i))
      (group_mono_usym_injective H G i) (usym_injective_group_mono H G i)

def group_monos_total_equiv (H G : Group)
  : Equiv (Σ (GroupHom H G) (IsMono (GroupCat .wild) H G))
      (Σ (GroupHom H G) (i ↦ IsEmbedding (USym H) (USym G) (usym_hom H G i)))
  ≔ family_equiv (GroupHom H G) (IsMono (GroupCat .wild) H G)
      (i ↦ IsEmbedding (USym H) (USym G) (usym_hom H G i)) (group_mono_usym_injective_equiv H G)

{` Litmus checks. Identities and the inclusion G → G × H of a factor are
   monomorphisms (via (⇐)); the homomorphism Σ_3 → 1 is not (via (⇒):
   it would identify the non-commuting products σ·τ and τ·σ). `}
def group_identity_usym_injective (G : Group)
  : IsEmbedding (USym G) (USym G) (usym_hom G G (group_hom_id G))
  ≔ path_reflecting_set_embedding (USym G) (USym G) (usym_set G) (usym_hom G G (group_hom_id G))
      (g g' s ↦ calc
        g = usym_hom G G (group_hom_id G) g by inverse (USym G) (usym_hom G G (group_hom_id G) g) g (usym_hom_id G g)
        = usym_hom G G (group_hom_id G) g' by s
        = g' by usym_hom_id G g' ∎)

def sigma3_identity_group_mono
  : IsMono (GroupCat .wild) (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three))
  ≔ usym_injective_group_mono (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three))
      (group_identity_usym_injective (symmetric_group three))

def product_group_incl1_usym_injective (G H : Group)
  : IsEmbedding (USym G) (USym (product_group G H)) (usym_hom G (product_group G H) (product_group_incl1 G H))
  ≔ let P ≔ product_group G H in let u ≔ usym_hom G P (product_group_incl1 G H) in
    path_reflecting_set_embedding (USym G) (USym P) (usym_set P) u
      (g g' s ↦ refl ((r ↦ r .fst) : USym P → USym G)
        (concat (USym P) ((g, refl (shape H)) : USym P) (u g') ((g', refl (shape H)) : USym P)
          (concat (USym P) ((g, refl (shape H)) : USym P) (u g) (u g')
            (inverse (USym P) (u g) ((g, refl (shape H)) : USym P) (product_group_incl1_usym G H g)) s)
          (product_group_incl1_usym G H g')))

def product_group_incl1_mono (G H : Group)
  : IsMono (GroupCat .wild) G (product_group G H) (product_group_incl1 G H)
  ≔ usym_injective_group_mono G (product_group G H) (product_group_incl1 G H)
      (product_group_incl1_usym_injective G H)

def sigma3_incl_mono
  : IsMono (GroupCat .wild) (symmetric_group three) (product_group (symmetric_group three) (symmetric_group three))
      (product_group_incl1 (symmetric_group three) (symmetric_group three))
  ≔ product_group_incl1_mono (symmetric_group three) (symmetric_group three)

def sigma3_to_unit_not_mono
  (m : IsMono (GroupCat .wild) (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three)))
  : Empty
  ≔ let S ≔ symmetric_group three in
    sigma3_tau_sigma_noncommuting
      (embedding_reflects_paths (USym S) (USym unit_group) (usym_hom S unit_group (group_hom_to_unit S))
        (group_mono_usym_injective S unit_group (group_hom_to_unit S) m)
        (usym_mul S sigma3_sigma sigma3_tau) (usym_mul S sigma3_tau sigma3_sigma)
        (contractible_prop (USym unit_group) (native_contraction (USym unit_group) unit_group_usym_contractible)
          (usym_hom S unit_group (group_hom_to_unit S) (usym_mul S sigma3_sigma sigma3_tau))
          (usym_hom S unit_group (group_hom_to_unit S) (usym_mul S sigma3_tau sigma3_sigma))))
