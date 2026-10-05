export "934-epi-connected-fibers"
export "901-kernels-cokernels-images"
export "523-free-elements"
export "435-circle-group-homomorphisms"
export "506-trivial-groups"
export "431-homomorphism-remarks"

{` Chapter 9 (subgroups.tex): lem:eq-mono-cover (line 129) with the
   running text before it (lines 106-127), the exercise after
   rem:imageandcokernel (line 409: monos and trivial kernels, epis and
   contractible cokernels, the universal property of the kernel), the
   epi/mono part of xca:p-epi-i-mono (line 845) and the footnote on the
   propositional image of Bf (line 795).

   Conventions as in modules 900-901: IsGroupMonomorphism / IsGroupEpi are
   the categorical notions of def:monomorphism, IsGroupMono (chapter 5,
   def:typeofmono) is "USym f is an injection" (IsEmbedding), IsCovering is
   the book's "covering" (set-valued book fibers). `}

{` lem:eq-mono-cover. (it:mono) ⇔ (it:injection) is module 687
   (group_monomorphism_mono_equiv, module 900); (it:injection) ⇔ (it:cover)
   is cor:fib-vs-path as proved in chapter 5 (group_mono_covering,
   covering_group_mono). `}
def eqmc_injection_covering_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMono G H f) (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ iff_equiv (IsGroupMono G H f) (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
      (is_group_mono_prop G H f) (covering_property_prop (BG H .carrier) (BG G .carrier, hom_function G H f))
      (group_mono_covering G H f) (covering_group_mono G H f)

def eqmc_mono_injection_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsGroupMono G H f)
  ≔ group_monomorphism_mono_equiv G H f

def eqmc_mono_covering_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ compose_equiv (IsGroupMonomorphism G H f) (IsGroupMono G H f)
      (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
      (group_monomorphism_mono_equiv G H f) (eqmc_injection_covering_equiv G H f)

{` "(or: is 0-truncated, see def:n-truncated)": TruncatedMap 2 (h-level 2
   fibers, book level 0). `}
def eqmc_covering_zero_truncated_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
      (TruncatedMap (suc. (suc. zero.)) (BG G .carrier) (BG H .carrier) (hom_function G H f))
  ≔ canonical_inverse_equiv (TruncatedMap (suc. (suc. zero.)) (BG G .carrier) (BG H .carrier) (hom_function G H f))
      (IsCovering (BG G .carrier) (BG H .carrier) (hom_function G H f))
      (zero_truncated_map_equiv (BG G .carrier) (BG H .carrier) (hom_function G H f))

{` Running text (lines 106-127, fig:Znatural): by ex:Zinitial and
   lem:Znatural (module 435), USym f is an injection iff post-composition
   f ∘ - : Hom(Z, G) → Hom(Z, H) is an injection (Z = circle_group C for any
   circle C). `}
def eqmc_usym_injective_post_circle_equiv (C : CircleSignature) (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMono G H f)
      (IsEmbedding (GroupHom (circle_group C) G) (GroupHom (circle_group C) H)
        (k ↦ group_hom_compose (circle_group C) G H k f))
  ≔ let Z ≔ circle_group C in
    let evG ≔ circle_group_hom_ev C G in
    let evH ≔ circle_group_hom_ev C H in
    let post : GroupHom Z G → GroupHom Z H ≔ k ↦ group_hom_compose Z G H k f in
    let nat ≔ circle_group_hom_ev_natural C G H f in
    let uf ≔ usym_hom G H f in
    iff_equiv (IsGroupMono G H f) (IsEmbedding (GroupHom Z G) (GroupHom Z H) post)
      (is_group_mono_prop G H f) (embedding_prop (GroupHom Z G) (GroupHom Z H) post)
      (m ↦ path_reflecting_set_embedding (GroupHom Z G) (GroupHom Z H) (group_hom_set Z H) post
         (k k' r ↦ equivalence_injective (GroupHom Z G) (USym G) evG k k'
            (embedding_reflects_paths (USym G) (USym H) uf m (evG .map k) (evG .map k')
               (calc
                  uf (evG .map k)
                  = evH .map (post k) by inverse (USym H) (evH .map (post k)) (uf (evG .map k)) (nat k)
                  = evH .map (post k') by refl (evH .map) r
                  = uf (evG .map k') by nat k' ∎))))
      (e ↦ path_reflecting_set_embedding (USym G) (USym H) (usym_set H) uf
         (g g' s ↦
            let k ≔ equiv_inverse_map (GroupHom Z G) (USym G) evG g in
            let k' ≔ equiv_inverse_map (GroupHom Z G) (USym G) evG g' in
            let cg ≔ equiv_counit (GroupHom Z G) (USym G) evG g in
            let cg' ≔ equiv_counit (GroupHom Z G) (USym G) evG g' in
            let kk : Id (GroupHom Z G) k k'
              ≔ embedding_reflects_paths (GroupHom Z G) (GroupHom Z H) post e k k'
                  (equivalence_injective (GroupHom Z H) (USym H) evH (post k) (post k')
                     (calc
                        evH .map (post k)
                        = uf (evG .map k) by nat k
                        = uf g by refl uf cg
                        = uf g' by s
                        = uf (evG .map k') by refl uf (inverse (USym G) (evG .map k') g' cg')
                        = evH .map (post k')
                          by inverse (USym H) (evH .map (post k')) (uf (evG .map k')) (nat k') ∎)) in
            calc
              g = evG .map k by inverse (USym G) (evG .map k) g cg
              = evG .map k' by refl (evG .map) kk
              = g' by cg' ∎))

{` xca (line 409), (1): f is a monomorphism iff the kernel is trivial
   (IsTrivialMono G (ker f), i.e. BKer(f) contractible). Ker(f) is the
   stabilizer of Bf_pt in f^*P_H (module 901), so "trivial kernel" is
   "Bf_pt is a free element". `}

{` Transport in z ↦ (b0 = F z) is post-composition with ap_F. `}
def eqmc_transport_path_family (A B : Type) (F : A → B) (b0 : B) (x y : A) (g : Id A x y) (p : Id B b0 (F x))
  : Id (Id B b0 (F y)) (transport A (z ↦ Id B b0 (F z)) x y g p) (concat B b0 (F x) (F y) p (map_path A B F x y g))
  ≔ J A x (y g ↦ Id (Id B b0 (F y)) (transport A (z ↦ Id B b0 (F z)) x y g p) (concat B b0 (F x) (F y) p (map_path A B F x y g)))
      (calc
         transport A (z ↦ Id B b0 (F z)) x x (refl x) p
         = p by transport_refl A (z ↦ Id B b0 (F z)) x p
         = concat B b0 (F x) (F x) p (refl (F x)) by inverse (Id B b0 (F x)) (concat B b0 (F x) (F x) p (refl (F x))) p (concat_p1 B b0 (F x) p) ∎)
      y g

{` g = (g · g'⁻¹) · g'. `}
def eqmc_concat_inverse_restore (A : Type) (a : A) (g g' : Id A a a)
  : Id (Id A a a) g (concat A a a a (concat A a a a g (inverse A a a g')) g')
  ≔ calc
      g
      = concat A a a a g (refl a) by inverse (Id A a a) (concat A a a a g (refl a)) g (concat_p1 A a a g)
      = concat A a a a g (concat A a a a (inverse A a a g') g')
        by refl (concat A a a a g) (inverse (Id A a a) (concat A a a a (inverse A a a g') g') (refl a) (concat_inverse_left A a a g'))
      = concat A a a a (concat A a a a g (inverse A a a g')) g'
        by inverse (Id A a a) (concat A a a a (concat A a a a g (inverse A a a g')) g')
             (concat A a a a g (concat A a a a (inverse A a a g') g')) (concat_assoc A a a a a g (inverse A a a g') g') ∎

{` If the loops g at a with g · p = p (transport) form a proposition, then
   ap_F at a is injective (the kernel of a homomorphism of loop groups). `}
def eqmc_ap_reflects_of_stabilizer_prop (A B : Type) (F : A → B) (b0 : B) (a : A) (p : Id B b0 (F a))
  (h : isProp (Σ (Id A a a) (g ↦ Id (Id B b0 (F a)) (transport A (z ↦ Id B b0 (F z)) a a g p) p)))
  : PathReflecting (Id A a a) (Id B (F a) (F a)) (map_path A B F a a)
  ≔ g g' e ↦
    let fa ≔ F a in
    let apF ≔ map_path A B F a a in
    let k ≔ concat A a a a g (inverse A a a g') in
    let apk : Id (Id B fa fa) (apF k) (refl fa)
      ≔ calc
          apF k
          = concat B fa fa fa (apF g) (map_path A B F a a (inverse A a a g')) by map_path_concat A B F a a a g (inverse A a a g')
          = concat B fa fa fa (apF g) (inverse B fa fa (apF g'))
            by refl (concat B fa fa fa (apF g)) (map_path_inverse A B F a a g')
          = concat B fa fa fa (apF g') (inverse B fa fa (apF g'))
            by refl ((t ↦ concat B fa fa fa t (inverse B fa fa (apF g'))) : Id B fa fa → Id B fa fa) e
          = refl fa by concat_inverse_right B fa fa (apF g') ∎ in
    let fixk : Id (Id B b0 fa) (transport A (z ↦ Id B b0 (F z)) a a k p) p
      ≔ calc
          transport A (z ↦ Id B b0 (F z)) a a k p
          = concat B b0 fa fa p (apF k) by eqmc_transport_path_family A B F b0 a a k p
          = concat B b0 fa fa p (refl fa) by refl (concat B b0 fa fa p) apk
          = p by concat_p1 B b0 fa p ∎ in
    let S ≔ Σ (Id A a a) (g ↦ Id (Id B b0 fa) (transport A (z ↦ Id B b0 (F z)) a a g p) p) in
    let kr : Id (Id A a a) k (refl a)
      ≔ refl ((u ↦ u .fst) : S → Id A a a) (h (k, fixk) (refl a, transport_refl A (z ↦ Id B b0 (F z)) a p)) in
    calc
      g = concat A a a a k g' by eqmc_concat_inverse_restore A a g g'
      = concat A a a a (refl a) g' by refl ((t ↦ concat A a a a t g') : Id A a a → Id A a a) kr
      = g' by concat_1p A a a g' ∎

def eqmc_kernel_trivial_mono (G H : Group) (f : GroupHom G H) (t : IsTrivialMono G (kernel G H f))
  : IsGroupMonomorphism G H f
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    usym_injective_group_mono G H f
      (path_reflecting_set_embedding (USym G) (USym H) (usym_set H) (usym_hom G H f)
        (g g' s ↦ eqmc_ap_reflects_of_stabilizer_prop A B F (shape H) (shape G) (hom_point G H f)
           (stabilizer_fixing_prop_of_free G (kernel_gset G H f) (hom_point G H f) t) g g'
           (mono_loop_conjugate_injective B (shape H) (F (shape G)) (hom_point G H f)
              (map_path A B F (shape G) (shape G) g) (map_path A B F (shape G) (shape G) g') s)))

{` Conversely the fiber (Bf)⁻¹(sh_H), the action type of f^*P_H, is a set,
   so every element (in particular Bf_pt) is free (module 523). `}
def eqmc_mono_kernel_trivial (G H : Group) (f : GroupHom G H) (m : IsGroupMonomorphism G H f)
  : IsTrivialMono G (kernel G H f)
  ≔ action_type_set_free G (kernel_gset G H f)
      (group_mono_covering G H f (group_mono_usym_injective G H f m) (shape H)) (hom_point G H f)

def eqmc_mono_kernel_trivial_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsTrivialMono G (kernel G H f))
  ≔ iff_equiv (IsGroupMonomorphism G H f) (IsTrivialMono G (kernel G H f))
      (is_group_monomorphism_prop G H f) (is_trivial_group_prop (kernel_group G H f))
      (eqmc_mono_kernel_trivial G H f) (eqmc_kernel_trivial_mono G H f)

{` xca (line 409), (2): f is an epimorphism iff the cokernel is
   contractible, i.e. coker(f)(w) = ‖(Bf)⁻¹(w)‖₀ is contractible for all w
   (ZeroConnectedMap, definitionally); equivalently at w = sh_H. `}
def EqmcCokernelContractible (G H : Group) (f : GroupHom G H) : Type
  ≔ (w : BG H .carrier) → BookIsContr (cokernel G H f w .fst)

def eqmc_epi_cokernel_contractible_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupEpi G H f) (EqmcCokernelContractible G H f)
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let F ≔ hom_function G H f in
    compose_equiv (IsGroupEpi G H f) (ConnectedFibers A B F) (EqmcCokernelContractible G H f)
      (gepi_epi_connected_fibers_equiv G H f)
      (iff_equiv (ConnectedFibers A B F) (ZeroConnectedMap A B F)
        (gepi_connected_fibers_prop G H f) (zero_connected_map_prop A B F)
        (connected_fibers_zero_map A B F) (zero_connected_map_fibers A B F))

def eqmc_epi_cokernel_point_contractible_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupEpi G H f) (BookIsContr (gset_underlying H (cokernel G H f)))
  ≔ iff_equiv (IsGroupEpi G H f) (BookIsContr (gset_underlying H (cokernel G H f)))
      (is_group_epi_prop G H f) (book_iscontr_isprop (gset_underlying H (cokernel G H f)))
      (e ↦ eqmc_epi_cokernel_contractible_equiv G H f .map e (shape H))
      (c ↦ equiv_inverse_map (IsGroupEpi G H f) (EqmcCokernelContractible G H f) (eqmc_epi_cokernel_contractible_equiv G H f)
         (connected_based_elim native_truncation (BG H .carrier) (bg_connected H) (shape H)
            (w ↦ BookIsContr (cokernel G H f w .fst)) (w ↦ book_iscontr_isprop (cokernel G H f w .fst)) c))

{` xca (line 409), (3): the universal property of the kernel. "fh is the
   trivial homomorphism" is fh = the homomorphism classified by the constant
   map at sh_H pointed by refl; equivalently fh factors through the trivial
   group (we use unit_group for the book's TG, both are trivial). `}
def EqmcTrivialHom (L H : Group) : GroupHom L H ≔ mkhom L H (_ ↦ shape H, refl (shape H))

def eqmc_unit_factor_trivial (L H : Group)
  : Id (GroupHom L H) (group_hom_compose L unit_group H (group_hom_to_unit L) (group_hom_from_unit H)) (EqmcTrivialHom L H)
  ≔ let B ≔ BG H .carrier in
    let r ≔ refl (shape H) in
    ch9_hom_path L H (group_hom_compose L unit_group H (group_hom_to_unit L) (group_hom_from_unit H)) (EqmcTrivialHom L H)
      ((_ ↦ r),
       calc
         concat B (shape H) (shape H) (shape H) (concat B (shape H) (shape H) (shape H) r r) r
         = concat B (shape H) (shape H) (shape H) r r by concat_p1 B (shape H) (shape H) (concat B (shape H) (shape H) (shape H) r r)
         = r by concat_p1 B (shape H) (shape H) r ∎)

def EqmcFactorsThroughUnit (L H : Group) (u : GroupHom L H) : Type
  ≔ Σ (GroupHom L unit_group) (t ↦ Σ (GroupHom unit_group H) (v ↦ Id (GroupHom L H) u (group_hom_compose L unit_group H t v)))

def eqmc_trivial_hom_factor_equiv (L H : Group) (u : GroupHom L H)
  : Equiv (Id (GroupHom L H) u (EqmcTrivialHom L H)) (EqmcFactorsThroughUnit L H u)
  ≔ let tu ≔ group_hom_to_unit_unique L in
    let fu ≔ group_hom_from_unit_unique H in
    let c ≔ group_hom_compose L unit_group H in
    let T ≔ EqmcTrivialHom L H in
    let c0 ≔ c (group_hom_to_unit L) (group_hom_from_unit H) in
    iff_equiv (Id (GroupHom L H) u T) (EqmcFactorsThroughUnit L H u)
      (group_hom_set L H u T)
      (sigma_prop (GroupHom L unit_group) (t ↦ Σ (GroupHom unit_group H) (v ↦ Id (GroupHom L H) u (c t v)))
         (contractible_prop (GroupHom L unit_group) (native_contraction (GroupHom L unit_group) tu))
         (t ↦ sigma_prop (GroupHom unit_group H) (v ↦ Id (GroupHom L H) u (c t v))
            (contractible_prop (GroupHom unit_group H) (native_contraction (GroupHom unit_group H) fu))
            (v ↦ group_hom_set L H u (c t v))))
      (r ↦ (group_hom_to_unit L, (group_hom_from_unit H,
             concat (GroupHom L H) u T c0 r (inverse (GroupHom L H) c0 T (eqmc_unit_factor_trivial L H)))))
      (w ↦
        let t ≔ w .fst in let v ≔ w .snd .fst in
        calc
          u = c t v by w .snd .snd
          = c (group_hom_to_unit L) v
            by refl ((x ↦ c x v) : GroupHom L unit_group → GroupHom L H)
                 (inverse (GroupHom L unit_group) (group_hom_to_unit L) t (tu .contract t))
          = c0 by refl (c (group_hom_to_unit L)) (inverse (GroupHom unit_group H) (group_hom_from_unit H) v (fu .contract v))
          = T by eqmc_unit_factor_trivial L H ∎)

{` From p · q = refl conclude p = q⁻¹. `}
def eqmc_concat_refl_inverse (A : Type) (x y : A) (p : Id A x y) (q : Id A y x)
  (e : Id (Id A x x) (concat A x y x p q) (refl x)) : Id (Id A x y) p (inverse A y x q)
  ≔ calc
      p
      = concat A x y y p (refl y) by inverse (Id A x y) (concat A x y y p (refl y)) p (concat_p1 A x y p)
      = concat A x y y p (concat A y x y q (inverse A y x q))
        by refl (concat A x y y p) (inverse (Id A y y) (concat A y x y q (inverse A y x q)) (refl y) (concat_inverse_right A y x q))
      = concat A x x y (concat A x y x p q) (inverse A y x q)
        by inverse (Id A x y) (concat A x x y (concat A x y x p q) (inverse A y x q))
             (concat A x y y p (concat A y x y q (inverse A y x q))) (concat_assoc A x y x y p q (inverse A y x q))
      = concat A x x y (refl x) (inverse A y x q) by refl ((t ↦ concat A x x y t (inverse A y x q)) : Id A x x → Id A x y) e
      = inverse A y x q by concat_1p A x y (inverse A y x q) ∎

{` Existence of the factorization: Bk(z) ≔ ((Bh z, α(z)⁻¹), !) where
   α : Bf ∘ Bh ~ const is the pointed homotopy of fh = trivial; the point of
   the kernel component is reached by (h_pt, ·), using the pointing
   condition of α. `}
def eqmc_kernel_lift (G H : Group) (f : GroupHom G H) (L : Group) (h : GroupHom L G)
  (r : Id (GroupHom L H) (group_hom_compose L G H h f) (EqmcTrivialHom L H))
  : BookFiber (GroupHom L (kernel_group G H f)) (GroupHom L G)
      (k ↦ group_hom_compose L (kernel_group G H f) G k (kernel_inclusion G H f)) h
  ≔ let BGc ≔ BG G .carrier in
    let BHc ≔ BG H .carrier in
    let BLc ≔ BG L .carrier in
    let F ≔ hom_function G H f in
    let Bh ≔ hom_function L G h in
    let fpt ≔ hom_point G H f in
    let hpt ≔ hom_point L G h in
    let sG ≔ shape G in let sH ≔ shape H in let sL ≔ shape L in
    let K ≔ kernel_group G H f in
    let X ≔ kernel_gset G H f in
    let T ≔ ActionType G X in
    let x0 : T ≔ (sG, fpt) in
    let ph ≔ group_hom_path_equiv L H (group_hom_compose L G H h f) (EqmcTrivialHom L H) .map r in
    let s : (z : BLc) → Id BHc sH (F (Bh z)) ≔ z ↦ inverse BHc (F (Bh z)) sH (ph .fst z) in
    let a ≔ map_path BGc BHc F sG (Bh sL) hpt in
    let e0 : Id (Id BHc sH (F (Bh sL))) (concat BHc sH (F sG) (F (Bh sL)) fpt a) (s sL)
      ≔ eqmc_concat_refl_inverse BHc sH (F (Bh sL)) (concat BHc sH (F sG) (F (Bh sL)) fpt a) (ph .fst sL) (ph .snd) in
    let eq0 : Id (Id BHc (F sG) (F (Bh sL))) (concat BHc (F sG) sH (F (Bh sL)) (inverse BHc sH (F sG) fpt) (s sL)) a
      ≔ calc
          concat BHc (F sG) sH (F (Bh sL)) (inverse BHc sH (F sG) fpt) (s sL)
          = concat BHc (F sG) sH (F (Bh sL)) (inverse BHc sH (F sG) fpt) (concat BHc sH (F sG) (F (Bh sL)) fpt a)
            by refl (concat BHc (F sG) sH (F (Bh sL)) (inverse BHc sH (F sG) fpt))
                 (inverse (Id BHc sH (F (Bh sL))) (concat BHc sH (F sG) (F (Bh sL)) fpt a) (s sL) e0)
          = a by concat_left_inverse_cancel BHc sH (F sG) (F (Bh sL)) fpt a ∎ in
    let d1 : Id (z ↦ Id BHc sH (F z)) hpt fpt (s sL)
      ≔ equiv_inverse_map (Id (z ↦ Id BHc sH (F z)) hpt fpt (s sL))
          (Id (Id BHc (F sG) (F (Bh sL))) (concat BHc (F sG) sH (F (Bh sL)) (inverse BHc sH (F sG) fpt) (s sL)) a)
          (fiber_path_triangle_equiv BGc BHc F sH sG (Bh sL) hpt fpt (s sL)) eq0 in
    let q1 : Id T x0 (Bh sL, s sL) ≔ (hpt, d1) in
    let memb : (z : BLc) → Mere (Id T x0 (Bh z, s z))
      ≔ connected_based_elim native_truncation BLc (bg_connected L) sL
          (z ↦ Mere (Id T x0 (Bh z, s z))) (z ↦ mere_isprop (Id T x0 (Bh z, s z)))
          (mere (Id T x0 (Bh sL, s sL)) q1) in
    let Bk : BLc → BG K .carrier ≔ z ↦ ((Bh z, s z), memb z) in
    let d2 ≔ pathover_hlevel zero. T (u ↦ Mere (Id T x0 u))
        (u ↦ prop_to_hlevel_one (Mere (Id T x0 u)) (mere_isprop (Id T x0 u)))
        x0 (Bh sL, s sL) q1 (mere (Id T x0 x0) (refl x0)) (memb sL) .center in
    let kpt : Id (BG K .carrier) (shape K) (Bk sL) ≔ (q1, d2) in
    let k : GroupHom L K ≔ mkhom L K (Bk, kpt) in
    (k,
     ch9_hom_path L G h (group_hom_compose L K G k (kernel_inclusion G H f))
       ((z ↦ refl (Bh z)),
        calc
          concat BGc sG (Bh sL) (Bh sL) hpt (refl (Bh sL))
          = hpt by concat_p1 BGc sG (Bh sL) hpt
          = concat BGc sG sG (Bh sL) (refl sG) hpt
            by inverse (Id BGc sG (Bh sL)) (concat BGc sG sG (Bh sL) (refl sG) hpt) hpt (concat_1p BGc sG (Bh sL) hpt) ∎))

def eqmc_kernel_universal_property (G H : Group) (f : GroupHom G H) (L : Group) (h : GroupHom L G)
  (r : Id (GroupHom L H) (group_hom_compose L G H h f) (EqmcTrivialHom L H))
  : BookIsContr (BookFiber (GroupHom L (kernel_group G H f)) (GroupHom L G)
      (k ↦ group_hom_compose L (kernel_group G H f) G k (kernel_inclusion G H f)) h)
  ≔ let c ≔ eqmc_kernel_lift G H f L h r in
    (c, usym_injective_group_mono (kernel_group G H f) G (kernel_inclusion G H f) (kernel_inclusion_mono G H f) L h c)

{` The same with the hypothesis "fh factors through the trivial group". `}
def eqmc_kernel_universal_property_factor (G H : Group) (f : GroupHom G H) (L : Group) (h : GroupHom L G)
  (w : EqmcFactorsThroughUnit L H (group_hom_compose L G H h f))
  : BookIsContr (BookFiber (GroupHom L (kernel_group G H f)) (GroupHom L G)
      (k ↦ group_hom_compose L (kernel_group G H f) G k (kernel_inclusion G H f)) h)
  ≔ eqmc_kernel_universal_property G H f L h
      (equiv_inverse_map (Id (GroupHom L H) (group_hom_compose L G H h f) (EqmcTrivialHom L H))
        (EqmcFactorsThroughUnit L H (group_hom_compose L G H h f))
        (eqmc_trivial_hom_factor_equiv L H (group_hom_compose L G H h f)) w)

{` xca:p-epi-i-mono (line 845), second part: p(f) is an epimorphism (its
   classifying map has connected fibers, module 901, and lem:epi-surj
   (3') ⇒ (1')) and i(f) a monomorphism (in the sense of def:monomorphism;
   USym i(f) is injective by module 901, then module 687). The book's hint
   (lem:trunc-n-connected) is replaced by module 901's connected fibers. `}
def eqmc_image_projection_epi (G H : Group) (f : GroupHom G H)
  : IsGroupEpi G (image_group G H f) (image_projection G H f)
  ≔ gepi_connected_fibers_epi G (image_group G H f) (image_projection G H f) (image_projection_connected_fibers G H f)

def eqmc_image_inclusion_monomorphism (G H : Group) (f : GroupHom G H)
  : IsGroupMonomorphism (image_group G H f) H (image_inclusion G H f)
  ≔ usym_injective_group_mono (image_group G H f) H (image_inclusion G H f) (image_inclusion_mono G H f)

{` Footnote at line 795: fst : im(Bf) → BH is an equivalence, since
   ‖(Bf)⁻¹(w)‖ is contractible for all w (Bf is surjective: BH is connected
   and (sh_G, Bf_pt) lies over sh_H). Here im(Bf) is the propositional image
   Image of module 39. `}
def eqmc_classifying_surjective (G H : Group) (f : GroupHom G H)
  : Surjective (BG G .carrier) (BG H .carrier) (hom_function G H f)
  ≔ connected_based_elim native_truncation (BG H .carrier) (bg_connected H) (shape H)
      (w ↦ Mere (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w))
      (w ↦ mere_isprop (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) w))
      (mere (BookFiber (BG G .carrier) (BG H .carrier) (hom_function G H f) (shape H)) (shape G, hom_point G H f))

def eqmc_prop_image_include_equiv (G H : Group) (f : GroupHom G H)
  : BookEquiv (Image (BG G .carrier) (BG H .carrier) (hom_function G H f)) (BG H .carrier)
  ≔ surjective_image_include_equiv (BG G .carrier) (BG H .carrier) (hom_function G H f) (eqmc_classifying_surjective G H f)

def eqmc_prop_image_include_map (G H : Group) (f : GroupHom G H)
  (u : Image (BG G .carrier) (BG H .carrier) (hom_function G H f))
  : Id (BG H .carrier) (eqmc_prop_image_include_equiv G H f .map u) (u .fst)
  ≔ refl (u .fst)
