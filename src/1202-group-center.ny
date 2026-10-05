export "1201-loop-algebra"

{` Chapter 12, sec:center-group (abelian.tex 20-229): the center Z(G) of a
   group, the inclusion z_G : Hom(Z(G), G), and the characterisation of
   abelian groups (def:abelian-groups).

   Throughout, A ≔ BG÷ and a ≔ sh_G. The identity types A = A are Narya's
   native Id Type A A; the evaluation of φ : A = A at a is the transport
   φ.trr(a) (the book's φ(sh_G) "coerced through univalence"). In the book
   ev(refl) ≡ sh_G holds by definition; here transport along refl does not
   reduce, so the pointing path of B z_G is the lifting path
   refl_A.liftr(sh_G) : sh_G = refl_A.trr(sh_G). `}

{` The center: Z(G) ≔ Aut_{(BG÷ = BG÷)}(refl_{BG÷}). `}
def center_space_groupoid (G : Group) : isGroupoid (Id Type (BG G .carrier) (BG G .carrier))
  ≔ universe_paths_groupoid (BG G .carrier) (BG G .carrier) (bg_groupoid G)

def group_center (G : Group) : Group
  ≔ automorphism_group (Id Type (BG G .carrier) (BG G .carrier)) (center_space_groupoid G) (refl (BG G .carrier))

{` ev_{sh_G} restricted to the component of refl, and its pointing path. `}
def center_evaluation (G : Group) (φ : BG (group_center G) .carrier) : BG G .carrier
  ≔ φ .fst .trr (shape G)

def center_evaluation_point (G : Group)
  : Id (BG G .carrier) (shape G) (center_evaluation G (shape (group_center G)))
  ≔ refl (BG G .carrier) .liftr (shape G)

{` z_G : Hom(Z(G), G) with B z_G ≔ ev_{sh_G}. `}
def center_inclusion (G : Group) : GroupHom (group_center G) G
  ≔ mkhom (group_center G) G (center_evaluation G, center_evaluation_point G)

{` Running text (abelian.tex 53-55): ap_{B z_G}(p) = p(sh_G), where a path
   p of identifications of BG÷ is read as a homotopy between transports.
   This holds by definition. `}
def center_ap_evaluation (G : Group) (u v : BG (group_center G) .carrier) (π : Id (BG (group_center G) .carrier) u v)
  : Id (Id (BG G .carrier) (center_evaluation G u) (center_evaluation G v))
      (refl (center_evaluation G) π)
      (universe_path_homotopy_equiv (BG G .carrier) (BG G .carrier) (u .fst) (v .fst) .map (π .fst) (shape G))
  ≔ refl (refl (center_evaluation G) π)

{` ap_{B z_G} is injective: two paths of identifications whose homotopies
   agree at sh_G agree everywhere (BG connected, BG a groupoid). `}
def center_ap_injective (G : Group) (u v : BG (group_center G) .carrier)
  : PathReflecting (Id (BG (group_center G) .carrier) u v)
      (Id (BG G .carrier) (center_evaluation G u) (center_evaluation G v))
      (map_path (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) u v)
  ≔ π π' e ↦
    let A ≔ BG G .carrier in
    let U ≔ universe_path_homotopy_equiv A A (u .fst) (v .fst) in
    let K ≔ connected_homotopy_determined A A (bg_connected G) (bg_groupoid G) (shape G) (u .fst .trr) (v .fst .trr)
      (U .map (π .fst)) (U .map (π' .fst)) e in
    let σ ≔ equivalence_injective (Id (Id Type A A) (u .fst) (v .fst)) (Homotopy A (_ ↦ A) (u .fst .trr) (v .fst .trr))
      U (π .fst) (π' .fst) K in
    equivalence_injective (Id (BG (group_center G) .carrier) u v) (Id (Id Type A A) (u .fst) (v .fst))
      (component_path_equiv (Id Type A A) (refl A) u v) π π' σ

def center_ap_embedding (G : Group) (u v : BG (group_center G) .carrier)
  : IsEmbedding (Id (BG (group_center G) .carrier) u v)
      (Id (BG G .carrier) (center_evaluation G u) (center_evaluation G v))
      (map_path (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) u v)
  ≔ path_reflecting_set_embedding (Id (BG (group_center G) .carrier) u v)
      (Id (BG G .carrier) (center_evaluation G u) (center_evaluation G v))
      (bg_groupoid G (center_evaluation G u) (center_evaluation G v))
      (map_path (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) u v)
      (center_ap_injective G u v)

{` lemma:center-is-subgroup. B z_G is a set bundle (covering) over BG. `}
def center_inclusion_covering (G : Group)
  : IsCovering (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G)
  ≔ b ↦ hlevel_two_to_set (BookFiber (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) b)
      (ap_hlevel_to_fibers (suc. zero.) (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G)
        (u v p ↦ prop_to_hlevel_one
          (BookFiber (Id (BG (group_center G) .carrier) u v)
            (Id (BG G .carrier) (center_evaluation G u) (center_evaluation G v))
            (map_path (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) u v) p)
          (center_ap_embedding G u v p)) b)

{` lemma:center-inc-inj-on-paths. abstr(z_G) is injective. `}
def center_inclusion_injective (G : Group)
  : IsEmbedding (USym (group_center G)) (USym G) (usym_hom (group_center G) G (center_inclusion G))
  ≔ path_reflecting_set_embedding (USym (group_center G)) (USym G) (usym_set G)
      (usym_hom (group_center G) G (center_inclusion G))
      (π π' e ↦ center_ap_injective G (shape (group_center G)) (shape (group_center G)) π π'
        (loop_conjugate_injective (BG G .carrier) (shape G) (center_evaluation G (shape (group_center G)))
          (center_evaluation_point G) (refl (center_evaluation G) π) (refl (center_evaluation G) π') e))

{` Central symmetries and the abstract center Σ(g : USym G) Π(h) gh = hg. `}
def CentralSymmetry (G : Group) (g : USym G) : Type
  ≔ (h : USym G) → Id (USym G) (usym_mul G g h) (usym_mul G h g)

def central_symmetry_prop (G : Group) (g : USym G) : isProp (CentralSymmetry G g)
  ≔ pi_prop (USym G) (h ↦ Id (USym G) (usym_mul G g h) (usym_mul G h g))
      (h ↦ usym_set G (usym_mul G g h) (usym_mul G h g))

def AbstractCenter (G : Group) : Type ≔ Σ (USym G) (CentralSymmetry G)

def abstract_center_set (G : Group) : isSet (AbstractCenter G)
  ≔ sigma_set (USym G) (CentralSymmetry G) (usym_set G)
      (g ↦ prop_is_set (CentralSymmetry G g) (central_symmetry_prop G g))

def abelian_all_central (G : Group) (h : IsAbelian G) (g : USym G) : CentralSymmetry G g ≔ h g

{` Running text (abelian.tex 67-76): every element p(sh_G) in the image of
   abstr(z_G) commutes with every g : USym G (naturality of the homotopy
   p, together with the triviality of transport along refl on loops). `}
def center_symmetry_central (G : Group) (p : USym (group_center G))
  : CentralSymmetry G (usym_hom (group_center G) G (center_inclusion G) p)
  ≔ h ↦
    let A ≔ BG G .carrier in let a ≔ shape G in
    let t ≔ refl A .trr in
    let ι ≔ (x ↦ refl A .liftr x) : (x : A) → Id A x (t x) in
    let K ≔ universe_path_homotopy_equiv A A (refl A) (refl A) .map (p .fst) in
    let z ≔ usym_hom (group_center G) G (center_inclusion G) p in
    calc
      usym_mul G z h = concat A a a a h z by refl (usym_mul G z h)
      = concat A a a a (pointed_loop_conjugate A a (t a) (ι a) (refl t h)) z
        by refl ((q ↦ concat A a a a q z) : Id A a a → Id A a a)
          (inverse (Id A a a) (pointed_loop_conjugate A a (t a) (ι a) (refl t h)) h
            (loops_map_homotopic_identity A t ι a h))
      = concat A a a a z (pointed_loop_conjugate A a (t a) (ι a) (refl t h))
        by loop_conjugate_commute A a (t a) (ι a) (refl t h) (K a) (naturality A A t t K a a h)
      = concat A a a a z h
        by refl (concat A a a a z) (loops_map_homotopic_identity A t ι a h)
      = usym_mul G h z by refl (usym_mul G h z) ∎

def center_to_abstract_center (G : Group) (p : USym (group_center G)) : AbstractCenter G
  ≔ (usym_hom (group_center G) G (center_inclusion G) p, center_symmetry_central G p)

{` lemma:center-inc-surj-on-paths. For central g, the family
   T_x(q) ≔ Π(p : sh_G = x) (p g = q p) has a contractible total space
   Σ(q : x = x) T_x(q) for every x; its centre gives ĝ(x) with ĝ(sh_G) = g. `}
def CentralExtensionFamily (G : Group) (g : USym G) (x : BG G .carrier) (q : Id (BG G .carrier) x x) : Type
  ≔ (p : Id (BG G .carrier) (shape G) x) → Id (Id (BG G .carrier) (shape G) x)
      (concat (BG G .carrier) (shape G) (shape G) x g p) (concat (BG G .carrier) (shape G) x x p q)

def central_extension_family_prop (G : Group) (g : USym G) (x : BG G .carrier) (q : Id (BG G .carrier) x x)
  : isProp (CentralExtensionFamily G g x q)
  ≔ pi_prop (Id (BG G .carrier) (shape G) x)
      (p ↦ Id (Id (BG G .carrier) (shape G) x)
        (concat (BG G .carrier) (shape G) (shape G) x g p) (concat (BG G .carrier) (shape G) x x p q))
      (p ↦ bg_groupoid G (shape G) x
        (concat (BG G .carrier) (shape G) (shape G) x g p) (concat (BG G .carrier) (shape G) x x p q))

def central_extension_witness (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : CentralExtensionFamily G g (shape G) g
  ≔ p ↦ inverse (USym G) (usym_mul G g p) (usym_mul G p g) (hg p)

def central_extension_contractible_base (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : BookIsContr (Σ (USym G) (CentralExtensionFamily G g (shape G)))
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    ((g, central_extension_witness G g hg), u ↦
      subtype_equal (USym G) (CentralExtensionFamily G g a) (central_extension_family_prop G g a)
        (g, central_extension_witness G g hg) u
        (calc
          g = concat A a a a g (refl a) by inverse (Id A a a) (concat A a a a g (refl a)) g (concat_p1 A a a g)
          = concat A a a a (refl a) (u .fst) by u .snd (refl a)
          = u .fst by concat_1p A a a (u .fst) ∎))

def central_extension_contractible (G : Group) (g : USym G) (hg : CentralSymmetry G g) (x : BG G .carrier)
  : BookIsContr (Σ (Id (BG G .carrier) x x) (CentralExtensionFamily G g x))
  ≔ connected_based_elim native_truncation (BG G .carrier) (bg_connected G) (shape G)
      (y ↦ BookIsContr (Σ (Id (BG G .carrier) y y) (CentralExtensionFamily G g y)))
      (y ↦ book_iscontr_isprop (Σ (Id (BG G .carrier) y y) (CentralExtensionFamily G g y)))
      (central_extension_contractible_base G g hg) x

def central_extension (G : Group) (g : USym G) (hg : CentralSymmetry G g) (x : BG G .carrier) : Id (BG G .carrier) x x
  ≔ central_extension_contractible G g hg x .center .fst

def central_extension_base (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : Id (USym G) (central_extension G g hg (shape G)) g
  ≔ central_extension_contractible G g hg (shape G) .contract (g, central_extension_witness G g hg) .fst

{` ĝ as a homotopy refl.trr ~ refl.trr, the corresponding loop at refl in
   BG÷ = BG÷, and its lift ĝ : USym Z(G). `}
def central_homotopy (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : Homotopy (BG G .carrier) (_ ↦ BG G .carrier) (refl (BG G .carrier) .trr) (refl (BG G .carrier) .trr)
  ≔ x ↦ pointed_loop_conjugate (BG G .carrier) (refl (BG G .carrier) .trr x) x
      (inverse (BG G .carrier) x (refl (BG G .carrier) .trr x) (refl (BG G .carrier) .liftr x))
      (central_extension G g hg x)

def central_universe_loop (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : Id (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier)) (refl (BG G .carrier))
  ≔ equiv_inverse_map (Id (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier)) (refl (BG G .carrier)))
      (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) (refl (BG G .carrier) .trr) (refl (BG G .carrier) .trr))
      (universe_path_homotopy_equiv (BG G .carrier) (BG G .carrier) (refl (BG G .carrier)) (refl (BG G .carrier)))
      (central_homotopy G g hg)

def central_lift (G : Group) (g : USym G) (hg : CentralSymmetry G g) : USym (group_center G)
  ≔ equiv_inverse_map (USym (group_center G)) (Id (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier)) (refl (BG G .carrier)))
      (component_path_equiv (Id Type (BG G .carrier) (BG G .carrier)) (refl (BG G .carrier))
        (shape (group_center G)) (shape (group_center G)))
      (central_universe_loop G g hg)

def central_lift_ap (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : Id (Id (BG G .carrier) (refl (BG G .carrier) .trr (shape G)) (refl (BG G .carrier) .trr (shape G)))
      (refl (center_evaluation G) (central_lift G g hg)) (central_homotopy G g hg (shape G))
  ≔ let A ≔ BG G .carrier in
    let L ≔ Id (Id Type A A) (refl A) (refl A) in
    let H ≔ Homotopy A (_ ↦ A) (refl A .trr) (refl A .trr) in
    let U ≔ universe_path_homotopy_equiv A A (refl A) (refl A) in
    let c1 : Id L (central_lift G g hg .fst) (central_universe_loop G g hg)
      ≔ equiv_counit (USym (group_center G)) L
          (component_path_equiv (Id Type A A) (refl A) (shape (group_center G)) (shape (group_center G)))
          (central_universe_loop G g hg) in
    let c2 : Id H (U .map (central_universe_loop G g hg)) (central_homotopy G g hg)
      ≔ equiv_counit L H U (central_homotopy G g hg) in
    calc
      refl (center_evaluation G) (central_lift G g hg) = U .map (central_lift G g hg .fst) (shape G)
        by refl (refl (center_evaluation G) (central_lift G g hg))
      = U .map (central_universe_loop G g hg) (shape G)
        by refl ((s ↦ U .map s (shape G)) : L → Id A (refl A .trr (shape G)) (refl A .trr (shape G))) c1
      = central_homotopy G g hg (shape G)
        by refl ((K ↦ K (shape G)) : H → Id A (refl A .trr (shape G)) (refl A .trr (shape G))) c2 ∎

def central_lift_value (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : Id (USym G) (usym_hom (group_center G) G (center_inclusion G) (central_lift G g hg)) g
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    let ι ≔ refl A .liftr a in
    calc
      usym_hom (group_center G) G (center_inclusion G) (central_lift G g hg)
        = pointed_loop_conjugate A a (refl A .trr a) ι (central_homotopy G g hg a)
        by refl (pointed_loop_conjugate A a (refl A .trr a) ι) (central_lift_ap G g hg)
      = central_extension G g hg a
        by loop_conjugate_inverse_cancel A a (refl A .trr a) ι (central_extension G g hg a)
      = g by central_extension_base G g hg ∎

def center_inclusion_central_fiber (G : Group) (g : USym G) (hg : CentralSymmetry G g)
  : BookFiber (USym (group_center G)) (USym G) (usym_hom (group_center G) G (center_inclusion G)) g
  ≔ (central_lift G g hg,
     inverse (USym G) (usym_hom (group_center G) G (center_inclusion G) (central_lift G g hg)) g
       (central_lift_value G g hg))

{` Fibers over central elements, as a family (used abstractly below so that
   the explicit lift never occurs inside a type). `}
def CentralFibers (G : Group) : Type
  ≔ (g : USym G) → CentralSymmetry G g
      → BookFiber (USym (group_center G)) (USym G) (usym_hom (group_center G) G (center_inclusion G)) g

{` The displayed equivalence after lemma:center-inc-surj-on-paths:
   USym Z(G) ≃ Σ(g : USym G) Π(h : USym G) gh = hg, given by abstr(z_G). `}
def center_usym_equiv_from_fibers (G : Group) (fibs : CentralFibers G)
  : BookEquiv (USym (group_center G)) (AbstractCenter G)
  ≔ embedding_surjection_equiv native_truncation (USym (group_center G)) (AbstractCenter G)
      (center_to_abstract_center G)
      (path_reflecting_set_embedding (USym (group_center G)) (AbstractCenter G) (abstract_center_set G)
        (center_to_abstract_center G)
        (π π' e ↦ embedding_reflects_paths (USym (group_center G)) (USym G)
          (usym_hom (group_center G) G (center_inclusion G)) (center_inclusion_injective G) π π' (e .fst)))
      (c ↦ mere (BookFiber (USym (group_center G)) (AbstractCenter G) (center_to_abstract_center G) c)
        (fibs (c .fst) (c .snd) .fst,
         subtype_equal (USym G) (CentralSymmetry G) (central_symmetry_prop G) c
           (center_to_abstract_center G (fibs (c .fst) (c .snd) .fst)) (fibs (c .fst) (c .snd) .snd)))

def center_usym_equiv (G : Group) : BookEquiv (USym (group_center G)) (AbstractCenter G)
  ≔ center_usym_equiv_from_fibers G (center_inclusion_central_fiber G)

{` def:abelian-groups (a lemma in the book): G is abelian iff z_G is an
   isomorphism of groups. `}
def center_ap_surjective_from_fibers (G : Group) (fibs : CentralFibers G) (h : IsAbelian G)
  : IsSurjection native_truncation (USym (group_center G))
      (Id (BG G .carrier) (center_evaluation G (shape (group_center G))) (center_evaluation G (shape (group_center G))))
      (map_path (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) (shape (group_center G)) (shape (group_center G)))
  ≔ m ↦
    let A ≔ BG G .carrier in let a ≔ shape G in
    let x ≔ center_evaluation G (shape (group_center G)) in
    let ι ≔ center_evaluation_point G in
    let f ≔ fibs (pointed_loop_conjugate A a x ι m) (h (pointed_loop_conjugate A a x ι m)) in
    mere (BookFiber (USym (group_center G)) (Id A x x)
        (map_path (BG (group_center G) .carrier) A (center_evaluation G) (shape (group_center G)) (shape (group_center G))) m)
      (f .fst, inverse (Id A x x) (refl (center_evaluation G) (f .fst)) m
        (loop_conjugate_injective A a x ι (refl (center_evaluation G) (f .fst)) m
          (inverse (USym G) (pointed_loop_conjugate A a x ι m) (usym_hom (group_center G) G (center_inclusion G) (f .fst))
            (f .snd))))

def abelian_center_inclusion_iso_from_fibers (G : Group) (fibs : CentralFibers G) (h : IsAbelian G)
  : IsGroupIso (group_center G) G (center_inclusion G)
  ≔ let C ≔ BG (group_center G) .carrier in let z0 ≔ shape (group_center G) in
    connected_map_equiv_from_loops native_truncation C (BG G .carrier) (center_evaluation G)
      (bg_connected (group_center G)) (bg_connected G) z0
      (embedding_surjection_equiv native_truncation (Id C z0 z0)
        (Id (BG G .carrier) (center_evaluation G z0) (center_evaluation G z0))
        (map_path C (BG G .carrier) (center_evaluation G) z0 z0)
        (center_ap_embedding G z0 z0) (center_ap_surjective_from_fibers G fibs h) .equiv) .equiv

def abelian_center_inclusion_iso (G : Group) (h : IsAbelian G) : IsGroupIso (group_center G) G (center_inclusion G)
  ≔ abelian_center_inclusion_iso_from_fibers G (center_inclusion_central_fiber G) h

{` Converse: if ap of B z_G is surjective at the base point (e.g. z_G an
   isomorphism), every symmetry is central. `}
def ApFibers (G : Group) : Type
  ≔ (m : Id (BG G .carrier) (center_evaluation G (shape (group_center G))) (center_evaluation G (shape (group_center G))))
      → BookFiber (USym (group_center G))
          (Id (BG G .carrier) (center_evaluation G (shape (group_center G))) (center_evaluation G (shape (group_center G))))
          (map_path (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) (shape (group_center G)) (shape (group_center G)))
          m

def center_ap_fibers_abelian (G : Group) (s : ApFibers G) : IsAbelian G
  ≔ g k ↦
    let A ≔ BG G .carrier in let a ≔ shape G in
    let x ≔ center_evaluation G (shape (group_center G)) in
    let ι ≔ center_evaluation_point G in
    let m ≔ pointed_loop_conjugate A x a (inverse A a x ι) g in
    let fib ≔ s m in
    let e : Id (USym G) (usym_hom (group_center G) G (center_inclusion G) (fib .fst)) g
      ≔ calc
          usym_hom (group_center G) G (center_inclusion G) (fib .fst)
            = pointed_loop_conjugate A a x ι m
            by refl (pointed_loop_conjugate A a x ι)
              (inverse (Id A x x) m (refl (center_evaluation G) (fib .fst)) (fib .snd))
          = g by loop_conjugate_inverse_cancel A a x ι g ∎ in
    transport (USym G) (CentralSymmetry G) (usym_hom (group_center G) G (center_inclusion G) (fib .fst)) g e
      (center_symmetry_central G (fib .fst)) k

def center_iso_abelian (G : Group) (i : IsGroupIso (group_center G) G (center_inclusion G)) : IsAbelian G
  ≔ center_ap_fibers_abelian G
      (m ↦ map_equiv_to_paths (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G) i
        (shape (group_center G)) (shape (group_center G)) m .center)

def abelian_iff_center_iso (G : Group)
  : BookEquiv (IsAbelian G) (IsGroupIso (group_center G) G (center_inclusion G))
  ≔ book_equivalence (IsAbelian G) (IsGroupIso (group_center G) G (center_inclusion G))
      (iff_equiv (IsAbelian G) (IsGroupIso (group_center G) G (center_inclusion G))
        (is_abelian_prop G) (is_group_iso_prop (group_center G) G (center_inclusion G))
        (abelian_center_inclusion_iso G) (center_iso_abelian G))

{` For abelian G, B z_G is an equivalence of pointed types and Z(G) = G. `}
def abelian_center_pointed_equiv (G : Group) (h : IsAbelian G) : BookPointedEquiv (BG (group_center G)) (BG G)
  ≔ (hom_B (group_center G) G (center_inclusion G), abelian_center_inclusion_iso G h)

def abelian_center_path (G : Group) (h : IsAbelian G) : Id Group (group_center G) G
  ≔ group_path_from_pointed_equiv (group_center G) G (abelian_center_pointed_equiv G h)
