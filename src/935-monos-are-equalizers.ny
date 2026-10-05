export "934-epi-connected-fibers"

{` Chapter 9 (subgroups.tex), con:monos-are-equalizers (line 204): for a
   monomorphism i : Hom(H, G) there are a group W and φ, ψ : Hom(G, W) such
   that i is an equalizer of φ and ψ: φ ∘ i = ψ ∘ i, and every k : Hom(K, G)
   with φ ∘ k = ψ ∘ k factors uniquely as k = i ∘ k' (the type of such k' is
   contractible).

   Deviation: the book's draft takes W ≔ Aut_E(sh_G, cst) with
   E = Σ_{t:BG} ((sh_G = t) → BA) for an injection of the cosets into a
   group A; we take the same φ, ψ as in module 934 with f ≔ i: W is the
   permutation group of Y(sh_G) = (USym G → T), T the faithful set of module
   933 (instead of the group A), φ the action homomorphism and ψ the action
   homomorphism with twisted pointing. Uniqueness comes from i being a
   monomorphism; existence from the evaluation of module 934: φ ∘ k = ψ ∘ k
   forces the point (sh_H, s⁻¹) of the covering (Bi)⁻¹(Bk sh_K) to be fixed
   by all of K, so it extends to a section over BK, i.e. a lift k' with
   Bi ∘ Bk' = Bk. `}

def GepiEqualizes (H G W : Group) (i : GroupHom H G) (φ ψ : GroupHom G W) : Type
  ≔ Id (GroupHom H W) (group_hom_compose H G W i φ) (group_hom_compose H G W i ψ)

{` i is an equalizer of φ and ψ (in the category of groups). The fiber is
   Σ_{k'} (k = i ∘ k'). `}
def GepiIsEqualizer (H G W : Group) (i : GroupHom H G) (φ ψ : GroupHom G W) : Type
  ≔ Product (GepiEqualizes H G W i φ ψ)
      ((K : Group) (k : GroupHom K G) → GepiEqualizes K G W k φ ψ
        → BookIsContr (BookFiber (GroupHom K H) (GroupHom K G) (k' ↦ group_hom_compose K H G k' i) k))

{` Transport in the family of fibers of a map: (z, p) ↦ (z, q⁻¹ · p). `}
def gepi_fiber_transport (A B : Type) (I : A → B) (w1 w2 : B) (q : Id B w1 w2) (u : BookFiber A B I w1)
  : Id (BookFiber A B I w2) (transport B (w ↦ BookFiber A B I w) w1 w2 q u)
      (u .fst, concat B w2 w1 (I (u .fst)) (inverse B w1 w2 q) (u .snd))
  ≔ J B w1 (w2 q ↦ Id (BookFiber A B I w2) (transport B (w ↦ BookFiber A B I w) w1 w2 q u)
                     (u .fst, concat B w2 w1 (I (u .fst)) (inverse B w1 w2 q) (u .snd)))
      (concat (BookFiber A B I w1) (transport B (w ↦ BookFiber A B I w) w1 w1 (refl w1) u) u
         (u .fst, concat B w1 w1 (I (u .fst)) (inverse B w1 w1 (refl w1)) (u .snd))
         (transport_refl B (w ↦ BookFiber A B I w) w1 u)
         (refl ((p ↦ (u .fst, p)) : Id B w1 (I (u .fst)) → BookFiber A B I w1)
            (inverse (Id B w1 (I (u .fst))) (concat B w1 w1 (I (u .fst)) (inverse B w1 w1 (refl w1)) (u .snd)) (u .snd)
               (inverse_refl_concat B w1 (I (u .fst)) (u .snd)))))
      w2 q

{` The pointing of the lift: if k_pt · t0 = i_pt for the chosen point
   (sh_H, t0) and q connects it to u, then k_pt · u.2 = i_pt · ap_Bi(q.1). `}
def gepi_lift_pointing (A B : Type) (I : A → B) (a0 : A) (b0 y0 : B) (ip : Id B b0 (I a0)) (kp : Id B b0 y0)
  (t0 : Id B y0 (I a0)) (E : Id (Id B b0 (I a0)) (concat B b0 y0 (I a0) kp t0) ip)
  (u : BookFiber A B I y0) (q : Id (BookFiber A B I y0) (a0, t0) u)
  : Id (Id B b0 (I (u .fst))) (concat B b0 y0 (I (u .fst)) kp (u .snd))
      (concat B b0 (I a0) (I (u .fst)) ip (map_path A B I a0 (u .fst) (refl ((v ↦ v .fst) : BookFiber A B I y0 → A) q)))
  ≔ J (BookFiber A B I y0) (a0, t0)
      (u q ↦ Id (Id B b0 (I (u .fst))) (concat B b0 y0 (I (u .fst)) kp (u .snd))
        (concat B b0 (I a0) (I (u .fst)) ip (map_path A B I a0 (u .fst) (refl ((v ↦ v .fst) : BookFiber A B I y0 → A) q))))
      (concat (Id B b0 (I a0)) (concat B b0 y0 (I a0) kp t0) ip (concat B b0 (I a0) (I a0) ip (refl (I a0))) E
         (inverse (Id B b0 (I a0)) (concat B b0 (I a0) (I a0) ip (refl (I a0))) ip (concat_p1 B b0 (I a0) ip)))
      u q

{` Path algebra: k_pt · (i_pt⁻¹ · k_pt)⁻¹ = i_pt. `}
def gepi_lift_base_pointing (B : Type) (b0 y0 x0 : B) (ip : Id B b0 x0) (kp : Id B b0 y0)
  : Id (Id B b0 x0) (concat B b0 y0 x0 kp (inverse B x0 y0 (concat B x0 b0 y0 (inverse B b0 x0 ip) kp))) ip
  ≔ calc
      concat B b0 y0 x0 kp (inverse B x0 y0 (concat B x0 b0 y0 (inverse B b0 x0 ip) kp))
      = concat B b0 y0 x0 kp (concat B y0 b0 x0 (inverse B b0 y0 kp) (inverse B x0 b0 (inverse B b0 x0 ip)))
        by refl (concat B b0 y0 x0 kp) (inverse_concat B x0 b0 y0 (inverse B b0 x0 ip) kp)
      = concat B b0 y0 x0 kp (concat B y0 b0 x0 (inverse B b0 y0 kp) ip)
        by refl ((t ↦ concat B b0 y0 x0 kp (concat B y0 b0 x0 (inverse B b0 y0 kp) t)) : Id B b0 x0 → Id B b0 x0)
             (inverse_inverse B b0 x0 ip)
      = ip by concat_left_right_inverse B b0 y0 x0 kp ip ∎

{` The covering G-set w ↦ (Bi)⁻¹(w) of a monomorphism. `}
def gepi_mono_fiber_gset (H G : Group) (i : GroupHom H G) (m : IsGroupMono H G i) : GSet G
  ≔ w ↦ (BookFiber (BG H .carrier) (BG G .carrier) (hom_function H G i) w,
         group_mono_covering H G i m w)

{` The lift k' from a section of the fibers of Bi over Bk through a given
   point. (A separate definition: projecting the first component of the
   concrete path of gset_fixed_point_extension_beta raises Narya's
   bug[E0500]; here the path is a variable.) `}
def gepi_mono_lift_assemble (H G : Group) (i : GroupHom H G) (K : Group) (k : GroupHom K G)
  (t0 : Id (BG G .carrier) (hom_function K G k (shape K)) (hom_function H G i (shape H)))
  (E : Id (Id (BG G .carrier) (shape G) (hom_function H G i (shape H)))
         (concat (BG G .carrier) (shape G) (hom_function K G k (shape K)) (hom_function H G i (shape H)) (hom_point K G k) t0)
         (hom_point H G i))
  (sec : (y : BG K .carrier) → BookFiber (BG H .carrier) (BG G .carrier) (hom_function H G i) (hom_function K G k y))
  (q : Id (BookFiber (BG H .carrier) (BG G .carrier) (hom_function H G i) (hom_function K G k (shape K)))
         (shape H, t0) (sec (shape K)))
  : BookFiber (GroupHom K H) (GroupHom K G) (k' ↦ group_hom_compose K H G k' i) k
  ≔ let A ≔ BG H .carrier in
    let B ≔ BG G .carrier in
    let I ≔ hom_function H G i in
    let y0 ≔ hom_function K G k (shape K) in
    let Fib : B → Type ≔ w ↦ BookFiber A B I w in
    let kpt' : Id A (shape H) (sec (shape K) .fst) ≔ refl ((v ↦ v .fst) : Fib y0 → A) q in
    let k' : GroupHom K H ≔ mkhom K H ((y ↦ sec y .fst), kpt') in
    (k',
     equiv_inverse_map (Id (GroupHom K G) k (group_hom_compose K H G k' i))
       (PointedHomotopy (BG K) (BG G) (hom_B K G k) (hom_B K G (group_hom_compose K H G k' i)))
       (group_hom_path_equiv K G k (group_hom_compose K H G k' i))
       ((y ↦ sec y .snd),
        gepi_lift_pointing A B I (shape H) (shape G) y0 (hom_point H G i) (hom_point K G k) t0 E (sec (shape K)) q))

{` Existence of the factorization through i. `}
def gepi_mono_lift (H G : Group) (i : GroupHom H G) (m : IsGroupMono H G i)
  (rep : GepiPermRep (gepi_coker_set H G i)) (K : Group) (k : GroupHom K G)
  (r : GepiEqualizes K G (gepi_test_group H G i rep) k (gepi_test_hom H G i rep) (gepi_test_hom_twisted H G i rep))
  : BookFiber (GroupHom K H) (GroupHom K G) (k' ↦ group_hom_compose K H G k' i) k
  ≔ let A ≔ BG H .carrier in
    let B ≔ BG G .carrier in
    let BK ≔ BG K .carrier in
    let I ≔ hom_function H G i in
    let Bk ≔ hom_function K G k in
    let a0 ≔ shape H in
    let b0 ≔ shape G in
    let k0 ≔ shape K in
    let ip ≔ hom_point H G i in
    let kp ≔ hom_point K G k in
    let y0 ≔ Bk k0 in
    let W ≔ gepi_test_group H G i rep in
    let φ ≔ gepi_test_hom H G i rep in
    let Φ ≔ hom_function G W φ in
    let Fib : B → Type ≔ w ↦ BookFiber A B I w in
    let FibSet : (w : B) → isSet (Fib w) ≔ group_mono_covering H G i m in
    let S ≔ gepi_coker_set H G i in
    let w ≔ gepi_twisted_commute H G W i Φ (hom_point G W φ) (gepi_test_alpha H G i rep) K k r in
    let s ≔ concat B (I a0) b0 y0 (inverse B b0 (I a0) ip) kp in
    let sinv ≔ inverse B (I a0) y0 s in
    let pair : Id B y0 (I a0) → Fib y0 ≔ p ↦ (a0, p) in
    let tr : Fib b0 → Fib y0 ≔ u ↦ (u .fst, concat B y0 b0 (I (u .fst)) (inverse B b0 y0 kp) (u .snd)) in
    let fixed : (κ : USym K) → Id (Fib y0) (a0, concat B y0 y0 (I a0) (inverse B y0 y0 (map_path BK B Bk k0 k0 κ)) sinv) (a0, sinv)
      ≔ κ ↦
        let mκ ≔ map_path BK B Bk k0 k0 κ in
        let mi ≔ inverse B y0 y0 mκ in
        let x1 : Fib b0 ≔ (a0, concat B b0 y0 (I a0) (concat B b0 y0 y0 kp mi) sinv) in
        let x2 : Fib b0 ≔ (a0, concat B b0 y0 (I a0) kp sinv) in
        let c : Id S (set_trunc (Fib b0) x1) (set_trunc (Fib b0) x2)
          ≔ gepi_core H G i rep y0 s (w .fst) (w .snd .fst) mκ (w .snd .snd κ) kp in
        let P0 : Id (Fib b0) x1 x2
          ≔ mere_rec (Id (Fib b0) x1 x2) (Id (Fib b0) x1 x2) (FibSet b0 x1 x2) (q ↦ q)
              (set_trunc_paths (Fib b0) x1 x2 .map c) in
        let X1 : Id (Id B y0 (I a0)) (concat B y0 b0 (I a0) (inverse B b0 y0 kp) (concat B b0 y0 (I a0) (concat B b0 y0 y0 kp mi) sinv))
            (concat B y0 y0 (I a0) mi sinv)
          ≔ calc
              concat B y0 b0 (I a0) (inverse B b0 y0 kp) (concat B b0 y0 (I a0) (concat B b0 y0 y0 kp mi) sinv)
              = concat B y0 b0 (I a0) (inverse B b0 y0 kp) (concat B b0 y0 (I a0) kp (concat B y0 y0 (I a0) mi sinv))
                by refl (concat B y0 b0 (I a0) (inverse B b0 y0 kp)) (concat_assoc B b0 y0 y0 (I a0) kp mi sinv)
              = concat B y0 y0 (I a0) mi sinv
                by concat_left_inverse_cancel B b0 y0 (I a0) kp (concat B y0 y0 (I a0) mi sinv) ∎ in
        let X2 : Id (Id B y0 (I a0)) (concat B y0 b0 (I a0) (inverse B b0 y0 kp) (concat B b0 y0 (I a0) kp sinv)) sinv
          ≔ concat_left_inverse_cancel B b0 y0 (I a0) kp sinv in
        calc
          pair (concat B y0 y0 (I a0) mi sinv)
          = tr x1 by refl pair (inverse (Id B y0 (I a0))
                (concat B y0 b0 (I a0) (inverse B b0 y0 kp) (concat B b0 y0 (I a0) (concat B b0 y0 y0 kp mi) sinv))
                (concat B y0 y0 (I a0) mi sinv) X1)
          = tr x2 by refl tr P0
          = pair sinv by refl pair X2 ∎ in
    let FG ≔ gepi_mono_fiber_gset H G i m in
    let Z ≔ gset_restrict K G k FG in
    let x0 : gset_underlying K Z ≔ (a0, sinv) in
    let fix : (κ : USym K) → Id (gset_underlying K Z) (gset_usym_act K Z κ x0) x0
      ≔ κ ↦ concat (Fib y0) (gset_usym_act K Z κ x0)
          (a0, concat B y0 y0 (I a0) (inverse B y0 y0 (map_path BK B Bk k0 k0 κ)) sinv) x0
          (gepi_fiber_transport A B I y0 y0 (map_path BK B Bk k0 k0 κ) x0) (fixed κ) in
    let sec : (y : BK) → Fib (Bk y) ≔ gset_fixed_point_extension K Z x0 fix in
    let secβ : Id (Fib y0) (sec k0) x0 ≔ gset_fixed_point_extension_beta K Z x0 fix in
    gepi_mono_lift_assemble H G i K k sinv (gepi_lift_base_pointing B b0 y0 (I a0) ip kp) sec
      (inverse (Fib y0) (sec k0) x0 secβ)

{` con:monos-are-equalizers, for a monomorphism in the sense of chapter 5
   (USym i injective, IsGroupMono): uniqueness of the factorization via the
   categorical monomorphism property (module 687). `}
def gepi_mono_equalizer_contractible (H G : Group) (i : GroupHom H G) (m : IsGroupMono H G i)
  (rep : GepiPermRep (gepi_coker_set H G i)) (K : Group) (k : GroupHom K G)
  (r : GepiEqualizes K G (gepi_test_group H G i rep) k (gepi_test_hom H G i rep) (gepi_test_hom_twisted H G i rep))
  : BookIsContr (BookFiber (GroupHom K H) (GroupHom K G) (k' ↦ group_hom_compose K H G k' i) k)
  ≔ let c ≔ gepi_mono_lift H G i m rep K k r in
    (c, usym_injective_group_mono H G i m K k c)

def gepi_mono_equalizer_usym (H G : Group) (i : GroupHom H G) (m : IsGroupMono H G i)
  : Σ Group (W ↦ Σ (GroupHom G W) (φ ↦ Σ (GroupHom G W) (ψ ↦ GepiIsEqualizer H G W i φ ψ)))
  ≔ let rep ≔ gepi_default_rep H G i in
    (gepi_test_group H G i rep,
     (gepi_test_hom H G i rep,
      (gepi_test_hom_twisted H G i rep,
       (gepi_test_homs_agree H G i rep, K k r ↦ gepi_mono_equalizer_contractible H G i m rep K k r))))

{` con:monos-are-equalizers for a monomorphism of the category of groups
   (def:monomorphism of chapter 9; equivalent to IsGroupMono by module 687). `}
def gepi_mono_equalizer (H G : Group) (i : GroupHom H G) (m : IsMono (GroupCat .wild) H G i)
  : Σ Group (W ↦ Σ (GroupHom G W) (φ ↦ Σ (GroupHom G W) (ψ ↦ GepiIsEqualizer H G W i φ ψ)))
  ≔ gepi_mono_equalizer_usym H G i (group_mono_usym_injective H G i m)
