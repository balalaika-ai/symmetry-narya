export "687-group-monomorphisms"
export "563-gset-fixed-points"
export "286-cycle-notation-equivalence"

{` Chapter 9 (subgroups.tex), lem:epi-surj (line 161), the directions that
   need no test group. For f : Hom(G, H) the three propositions are
   (1') f is an epimorphism: IsEpi (GroupCat .wild) G H f (module 609 in the
        category of groups of module 686; the book's def:monomorphism, i.e.
        pre-composition - ∘ f : Hom(H, K) → Hom(G, K) is an injection for
        every group K);
   (2') USym f : USym G → USym H is a surjection;
   (3') Bf÷ : BG÷ → BH÷ has connected fibers (ConnectedFibers, module 105).
   Here: (2') ⇔ (3') ("immediate": fibers of the loop map vs fibers of Bf,
   using that BG and BH are connected) and (3') ⇒ (1') (a pointed homotopy
   Bφ ∘ Bf ~ Bψ ∘ Bf extends along Bf, the family t ↦ (Bφ t = Bψ t) being
   set-valued). The hard direction (1') ⇒ (3') is module 934. `}

{` Path algebra: p · (p⁻¹ · h · p) · p⁻¹ = h (concatenation order), i.e.
   conjugating back. `}
def gepi_conjugate_cancel (B : Type) (b c : B) (p : Id B b c) (h : Id B b b)
  : Id (Id B b b) (pointed_loop_conjugate B b c p (concat B c b c (inverse B b c p) (concat B b b c h p))) h
  ≔ J B b (c p ↦ Id (Id B b b) (pointed_loop_conjugate B b c p (concat B c b c (inverse B b c p) (concat B b b c h p))) h)
      (calc
        pointed_loop_conjugate B b b (refl b) (concat B b b b (inverse B b b (refl b)) (concat B b b b h (refl b)))
        = concat B b b b (concat B b b b (inverse B b b (refl b)) (concat B b b b h (refl b))) (inverse B b b (refl b))
          by concat_1p B b b
               (concat B b b b (concat B b b b (inverse B b b (refl b)) (concat B b b b h (refl b))) (inverse B b b (refl b)))
        = concat B b b b (concat B b b b (inverse B b b (refl b)) (concat B b b b h (refl b))) (refl b)
          by refl (concat B b b b (concat B b b b (inverse B b b (refl b)) (concat B b b b h (refl b)))) (inverse_refl B b)
        = concat B b b b (inverse B b b (refl b)) (concat B b b b h (refl b))
          by concat_p1 B b b (concat B b b b (inverse B b b (refl b)) (concat B b b b h (refl b)))
        = concat B b b b h (refl b) by inverse_refl_concat B b b (concat B b b b h (refl b))
        = h by concat_p1 B b b h ∎)
      c p

{` lem:epi-surj, (3') ⇒ (2'): for h : USym H the points (sh_G, Bf_pt) and
   (sh_G, h · Bf_pt) of the connected fiber (Bf)⁻¹(sh_H) are merely equal; a
   path between them is a g : USym G with ap_Bf(g) = Bf_pt⁻¹ h Bf_pt, i.e.
   USym f (g) = h. `}
def gepi_connected_fibers_usym_surjective (G H : Group) (f : GroupHom G H)
  (c : ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
  : Surjective (USym G) (USym H) (usym_hom G H f)
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    let a0 ≔ shape G in
    let b0 ≔ shape H in
    let fp ≔ hom_point G H f in
    h ↦
      let u : BookFiber A B F b0 ≔ (a0, fp) in
      let v : BookFiber A B F b0 ≔ (a0, concat B b0 b0 (F a0) h fp) in
      let Goal ≔ BookFiber (USym G) (USym H) (usym_hom G H f) h in
      mere_rec (Id (BookFiber A B F b0) u v) (Mere Goal) (mere_isprop Goal)
        (r ↦
          let w ≔ fiber_path_equiv A B F b0 u v .map r in
          mere Goal
            (w .fst,
             calc
               h
               = pointed_loop_conjugate B b0 (F a0) fp
                   (concat B (F a0) b0 (F a0) (inverse B b0 (F a0) fp) (concat B b0 b0 (F a0) h fp))
                 by inverse (Id B b0 b0)
                      (pointed_loop_conjugate B b0 (F a0) fp
                        (concat B (F a0) b0 (F a0) (inverse B b0 (F a0) fp) (concat B b0 b0 (F a0) h fp))) h
                      (gepi_conjugate_cancel B b0 (F a0) fp h)
               = pointed_loop_conjugate B b0 (F a0) fp (map_path A B F a0 a0 (w .fst))
                 by refl (pointed_loop_conjugate B b0 (F a0) fp) (w .snd) ∎))
        (c b0 .snd u v)

{` lem:epi-surj, (2') ⇒ (3'): connectedness is a proposition and BH is
   connected, so it suffices to treat the fiber over sh_H; every point of it
   is merely of the form (sh_G, p) (BG is connected), and (sh_G, Bf_pt) =
   (sh_G, p) amounts to a g with ap_Bf(g) = Bf_pt⁻¹ p, which exists merely by
   surjectivity of USym f (conjugation by Bf_pt is injective). `}
def gepi_usym_surjective_connected_fibers (G H : Group) (f : GroupHom G H)
  (s : Surjective (USym G) (USym H) (usym_hom G H f))
  : ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f)
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    let a0 ≔ shape G in
    let b0 ≔ shape H in
    let fp ≔ hom_point G H f in
    let Fb ≔ BookFiber A B F b0 in
    let u0 : Fb ≔ (a0, fp) in
    let base : (p : Id B b0 (F a0)) → Mere (Id Fb u0 (a0, p))
      ≔ p ↦
        let l ≔ concat B (F a0) b0 (F a0) (inverse B b0 (F a0) fp) p in
        let h ≔ pointed_loop_conjugate B b0 (F a0) fp l in
        mere_rec (BookFiber (USym G) (USym H) (usym_hom G H f) h) (Mere (Id Fb u0 (a0, p)))
          (mere_isprop (Id Fb u0 (a0, p)))
          (w ↦ mere (Id Fb u0 (a0, p))
            (equiv_inverse_map (Id Fb u0 (a0, p))
              (BookFiber (Id A a0 a0) (Id B (F a0) (F a0)) (map_path A B F a0 a0) l)
              (fiber_path_equiv A B F b0 u0 (a0, p))
              (w .fst, mono_loop_conjugate_injective B b0 (F a0) fp l (map_path A B F a0 a0 (w .fst)) (w .snd))))
          (s h) in
    let all_points : (z : A) (p : Id B b0 (F z)) → Mere (Id Fb u0 (z, p))
      ≔ connected_based_elim native_truncation A (bg_connected G) a0
          (z ↦ (p : Id B b0 (F z)) → Mere (Id Fb u0 (z, p)))
          (z ↦ pi_prop (Id B b0 (F z)) (p ↦ Mere (Id Fb u0 (z, p))) (p ↦ mere_isprop (Id Fb u0 (z, p))))
          base in
    let conn0 : Connected Fb
      ≔ (mere Fb u0,
         x y ↦ merely_paths_compose native_truncation Fb u0 x y (all_points (x .fst) (x .snd))
           (all_points (y .fst) (y .snd))) in
    connected_based_elim native_truncation B (bg_connected H) b0
      (w ↦ Connected (BookFiber A B F w)) (w ↦ connected_isprop (BookFiber A B F w)) conn0

def gepi_connected_fibers_prop (G H : Group) (f : GroupHom G H)
  : isProp (ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ pi_prop (BG H .carrier) (w ↦ Connected (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w))
      (w ↦ connected_isprop (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w))

{` lem:epi-surj, (2') ⇔ (3') as an equivalence of propositions. `}
def gepi_surjective_connected_fibers_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (Surjective (USym G) (USym H) (usym_hom G H f))
      (ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ iff_equiv (Surjective (USym G) (USym H) (usym_hom G H f))
      (ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
      (surjective_property_prop (USym G) (USym H) (usym_hom G H f)) (gepi_connected_fibers_prop G H f)
      (gepi_usym_surjective_connected_fibers G H f) (gepi_connected_fibers_usym_surjective G H f)

{` lem:epi-surj, (3') ⇒ (1'), the cancellation form: if Bf has connected
   fibers and φ ∘ f = ψ ∘ f, then φ = ψ. The pointed homotopy
   α : Bφ ∘ Bf ~ Bψ ∘ Bf extends to β : Bφ ~ Bψ (extend_connected_sections,
   module 109; the family t ↦ (Bφ t = Bψ t) is set-valued since BK is a
   groupoid) and the pointing condition at sh_H follows from the one at sh_G
   by naturality of β along Bf_pt. `}
def gepi_connected_fibers_hom_cancel (G H K : Group) (f : GroupHom G H)
  (c : ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
  (φ ψ : GroupHom H K) (r : Id (GroupHom G K) (group_hom_compose G H K f φ) (group_hom_compose G H K f ψ))
  : Id (GroupHom H K) φ ψ
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let C ≔ BG K .carrier in
    let F ≔ hom_function G H f in
    let a0 ≔ shape G in
    let b0 ≔ shape H in
    let c0 ≔ shape K in
    let fp ≔ hom_point G H f in
    let Bφ ≔ hom_function H K φ in
    let Bψ ≔ hom_function H K ψ in
    let φp ≔ hom_point H K φ in
    let ψp ≔ hom_point H K ψ in
    let h ≔ group_hom_path_equiv G K (group_hom_compose G H K f φ) (group_hom_compose G H K f ψ) .map r in
    let P : B → Type ≔ t ↦ Id C (Bφ t) (Bψ t) in
    let hP : (t : B) → isSet (P t) ≔ t ↦ bg_groupoid K (Bφ t) (Bψ t) in
    let β : (t : B) → P t ≔ extend_connected_sections A B F c P hP (h .fst) in
    let βa : Id (P (F a0)) (β (F a0)) (h .fst a0) ≔ extend_connected_sections_beta A B F c P hP (h .fst) a0 in
    let aφ ≔ map_path B C Bφ b0 (F a0) fp in
    let aψ ≔ map_path B C Bψ b0 (F a0) fp in
    let nat : Id (Id C (Bφ b0) (Bψ (F a0)))
        (concat C (Bφ b0) (Bφ (F a0)) (Bψ (F a0)) aφ (β (F a0)))
        (concat C (Bφ b0) (Bψ b0) (Bψ (F a0)) (β b0) aψ)
      ≔ naturality B C Bφ Bψ β b0 (F a0) fp in
    let e : Id (Id C c0 (Bψ b0)) (concat C c0 (Bφ b0) (Bψ b0) φp (β b0)) ψp
      ≔ concat_cancel_right C c0 (Bψ b0) (Bψ (F a0)) (concat C c0 (Bφ b0) (Bψ b0) φp (β b0)) ψp aψ
          (calc
            concat C c0 (Bψ b0) (Bψ (F a0)) (concat C c0 (Bφ b0) (Bψ b0) φp (β b0)) aψ
            = concat C c0 (Bφ b0) (Bψ (F a0)) φp (concat C (Bφ b0) (Bψ b0) (Bψ (F a0)) (β b0) aψ)
              by concat_assoc C c0 (Bφ b0) (Bψ b0) (Bψ (F a0)) φp (β b0) aψ
            = concat C c0 (Bφ b0) (Bψ (F a0)) φp (concat C (Bφ b0) (Bφ (F a0)) (Bψ (F a0)) aφ (β (F a0)))
              by refl (concat C c0 (Bφ b0) (Bψ (F a0)) φp)
                   (inverse (Id C (Bφ b0) (Bψ (F a0)))
                     (concat C (Bφ b0) (Bφ (F a0)) (Bψ (F a0)) aφ (β (F a0)))
                     (concat C (Bφ b0) (Bψ b0) (Bψ (F a0)) (β b0) aψ) nat)
            = concat C c0 (Bφ b0) (Bψ (F a0)) φp (concat C (Bφ b0) (Bφ (F a0)) (Bψ (F a0)) aφ (h .fst a0))
              by refl ((x ↦ concat C c0 (Bφ b0) (Bψ (F a0)) φp (concat C (Bφ b0) (Bφ (F a0)) (Bψ (F a0)) aφ x))
                        : P (F a0) → Id C c0 (Bψ (F a0))) βa
            = concat C c0 (Bφ (F a0)) (Bψ (F a0)) (concat C c0 (Bφ b0) (Bφ (F a0)) φp aφ) (h .fst a0)
              by inverse (Id C c0 (Bψ (F a0)))
                   (concat C c0 (Bφ (F a0)) (Bψ (F a0)) (concat C c0 (Bφ b0) (Bφ (F a0)) φp aφ) (h .fst a0))
                   (concat C c0 (Bφ b0) (Bψ (F a0)) φp (concat C (Bφ b0) (Bφ (F a0)) (Bψ (F a0)) aφ (h .fst a0)))
                   (concat_assoc C c0 (Bφ b0) (Bφ (F a0)) (Bψ (F a0)) φp aφ (h .fst a0))
            = concat C c0 (Bψ b0) (Bψ (F a0)) ψp aψ by h .snd ∎) in
    equiv_inverse_map (Id (GroupHom H K) φ ψ) (PointedHomotopy (BG H) (BG K) (hom_B H K φ) (hom_B H K ψ))
      (group_hom_path_equiv H K φ ψ) (β, e)

{` lem:epi-surj, (3') ⇒ (1'). `}
def gepi_connected_fibers_epi (G H : Group) (f : GroupHom G H)
  (c : ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f))
  : IsEpi (GroupCat .wild) G H f
  ≔ K ↦ path_reflecting_set_embedding (GroupHom H K) (GroupHom G K) (group_hom_set G K)
      (k ↦ GroupCat .wild .comp G H K k f) (φ ψ r ↦ gepi_connected_fibers_hom_cancel G H K f c φ ψ r)

{` lem:epi-surj, (2') ⇒ (1'). `}
def gepi_usym_surjective_epi (G H : Group) (f : GroupHom G H)
  (s : Surjective (USym G) (USym H) (usym_hom G H f)) : IsEpi (GroupCat .wild) G H f
  ≔ gepi_connected_fibers_epi G H f (gepi_usym_surjective_connected_fibers G H f s)
