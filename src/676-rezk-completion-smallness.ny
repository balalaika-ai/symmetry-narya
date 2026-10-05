export "673-rezk-completion"
export "606-category-sizes"
export "210-truncation-smallness"

{` Chapter 6, section 6.8: size of the Rezk completion (second half of
   thm:Rezk-completion and xca:Rezk-completion-locally-small). Universes
   are the smallness predicates of modules 190-193 (and 606, rem:cat-sizes);
   Replacement (pri:replacement) is an explicit hypothesis.

   Size convention. In Narya's single universe the presheaves of
   Set^{C^op} take values in all sets (SetTypes), not in a smaller Set_U,
   so Ob(Set^{C^op}) is not locally U-small. The proofs therefore work
   inside L(C) directly: hom-sets of L(C) are U-small because those between
   representables are (Yoneda), and Ob(L(C)) is the image of
   Ob(η) : Ob(C) → Ob(L(C)), whose codomain is locally U-small. The book's
   intermediate claims are formalized separately below for presheaves with
   U-small values. `}

{` thm:Rezk-completion: "C is essentially U-small, meaning that the type of
   objects Ob(C) and all hom-sets are essentially U-small". `}
def IsEssentiallySmallPrecat (U : Universe) (C : Precat) : Type
  ≔ Product (EssentiallySmall U (C .wild .ob)) ((a b : C .wild .ob) → EssentiallySmall U (C .wild .hom a b))

{` In the model the essential version agrees with IsSmallWildPrecat of
   rem:cat-sizes (module 606). `}
def essentially_small_precat_small (U : Universe) (C : Precat) (h : IsEssentiallySmallPrecat U C)
  : IsSmallWildPrecat U (C .wild)
  ≔ (essentially_small_is_small U (C .wild .ob) (h .fst),
     a b ↦ essentially_small_is_small U (C .wild .hom a b) (h .snd a b))

def small_precat_essentially_small (U : Universe) (C : Precat) (h : IsSmallWildPrecat U (C .wild))
  : IsEssentiallySmallPrecat U C
  ≔ (small_essentially_small U (C .wild .ob) (h .fst),
     a b ↦ small_essentially_small U (C .wild .hom a b) (h .snd a b))

{` Properties of pairs of objects of L(C) that are propositions can be
   checked on objects η(c), since Ob(η) is surjective. `}
def rezk_object_pair_induction (C : Precat)
  (Q : RezkCompletion C .wild .ob → RezkCompletion C .wild .ob → Type)
  (hQ : (x y : RezkCompletion C .wild .ob) → isProp (Q x y))
  (q : (c c' : C .wild .ob) → Q (rezk_unit C .obj c) (rezk_unit C .obj c'))
  (x y : RezkCompletion C .wild .ob) : Q x y
  ≔ let L ≔ RezkCompletion C .wild .ob in
    let u ≔ rezk_unit C .obj in
    mere_rec (BookFiber (C .wild .ob) L u x) (Q x y) (hQ x y)
      (sx ↦ mere_rec (BookFiber (C .wild .ob) L u y) (Q x y) (hQ x y)
        (sy ↦ transport L (z ↦ Q z y) (u (sx .fst)) x (inverse L x (u (sx .fst)) (sx .snd))
          (transport L (z ↦ Q (u (sx .fst)) z) (u (sy .fst)) y (inverse L y (u (sy .fst)) (sy .snd))
            (q (sx .fst) (sy .fst))))
        (rezk_unit_obj_surjective C y))
      (rezk_unit_obj_surjective C x)

{` The hom-sets of L(C) between η(c) and η(c') are those of C, by Yoneda
   (cor:yo-ff). `}
def rezk_unit_hom_equiv (C : Precat) (c c' : C .wild .ob)
  : Equiv (C .wild .hom c c') (RezkCompletion C .wild .hom (rezk_unit C .obj c) (rezk_unit C .obj c'))
  ≔ native_equivalence (C .wild .hom c c') (RezkCompletion C .wild .hom (rezk_unit C .obj c) (rezk_unit C .obj c'))
      (yoneda_functor C .mor c c', yoneda_mor_equiv C c c')

{` xca:Rezk-completion-locally-small: if C is locally U-small, so is L(C)
   ("by Yoneda, Hom(yo A, yo B) is U-small"); no smallness of Ob(C) and no
   Replacement is needed. Stated with the predicate of rem:cat-sizes
   (module 606) and, equivalently, with essential smallness. `}
def rezk_completion_locally_essentially_small (U : Universe) (C : Precat)
  (h : (a b : C .wild .ob) → EssentiallySmall U (C .wild .hom a b))
  (x y : RezkCompletion C .wild .ob) : EssentiallySmall U (RezkCompletion C .wild .hom x y)
  ≔ rezk_object_pair_induction C (x y ↦ EssentiallySmall U (RezkCompletion C .wild .hom x y))
      (x y ↦ essentially_small_prop U (RezkCompletion C .wild .hom x y))
      (c c' ↦ essentially_small_equiv U (C .wild .hom c c')
        (RezkCompletion C .wild .hom (rezk_unit C .obj c) (rezk_unit C .obj c'))
        (rezk_unit_hom_equiv C c c') (h c c'))
      x y

def rezk_completion_locally_small (U : Universe) (C : Precat) (h : IsLocallySmallWildPrecat U (C .wild))
  : IsLocallySmallWildPrecat U (RezkCompletion C .wild)
  ≔ x y ↦ essentially_small_is_small U (RezkCompletion C .wild .hom x y)
      (rezk_completion_locally_essentially_small U C
        (a b ↦ small_essentially_small U (C .wild .hom a b) (h a b)) x y)

{` In a univalent precategory with U-small hom types, the type of
   objects is locally U-small (identifications are isomorphisms). `}
def cat_iso_essentially_small (U : Universe) (C : WildPrecat)
  (hs : (a b : C .ob) → EssentiallySmall U (C .hom a b)) (a b : C .ob) : EssentiallySmall U (CatIso C a b)
  ≔ let small_ids : (x y : C .ob) (u v : C .hom x y) → EssentiallySmall U (Id (C .hom x y) u v)
      ≔ x y u v ↦ essentially_small_locally_small U (C .hom x y) (hs x y) u v in
    sigma_essentially_small U (C .hom a b) (hs a b) (CatIsIso C a b)
      (f ↦ product_essentially_small U
        (Σ (C .hom b a) (g ↦ Id (C .hom b b) (C .comp b a b f g) (C .idn b)))
        (Σ (C .hom b a) (k ↦ Id (C .hom a a) (C .comp a b a k f) (C .idn a)))
        (sigma_essentially_small U (C .hom b a) (hs b a) (g ↦ Id (C .hom b b) (C .comp b a b f g) (C .idn b))
          (g ↦ small_ids b b (C .comp b a b f g) (C .idn b)))
        (sigma_essentially_small U (C .hom b a) (hs b a) (k ↦ Id (C .hom a a) (C .comp a b a k f) (C .idn a))
          (k ↦ small_ids a a (C .comp a b a k f) (C .idn a))))

def univalent_objects_locally_small (U : Universe) (C : WildPrecat) (u : IsUnivalentCat C)
  (hs : (a b : C .ob) → EssentiallySmall U (C .hom a b)) : LocallySmall U (C .ob)
  ≔ a b ↦ essentially_small_equiv U (CatIso C a b) (Id (C .ob) a b)
      (canonical_inverse_equiv (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso_equiv C u a b))
      (cat_iso_essentially_small U C hs a b)

{` thm:Rezk-completion, second sentence: if C is essentially U-small then
   so is L(C), assuming Replacement for U. Ob(L(C)) is the image of
   Ob(η) (Ob(η) is surjective), and Replacement applies since Ob(C) is
   essentially small and Ob(L(C)) is locally small. `}
def rezk_completion_objects_essentially_small (U : Universe) (rep : Replacement U) (C : Precat)
  (h : IsEssentiallySmallPrecat U C) : EssentiallySmall U (RezkCompletion C .wild .ob)
  ≔ let L ≔ RezkCompletion C in
    essentially_small_equiv U (Image (C .wild .ob) (L .wild .ob) (rezk_unit C .obj)) (L .wild .ob)
      (surjection_image_equiv (C .wild .ob) (L .wild .ob) (rezk_unit C .obj) (rezk_unit_obj_surjective C))
      (rep (C .wild .ob) (L .wild .ob) (rezk_unit C .obj) (h .fst)
        (univalent_objects_locally_small U (L .wild) (L .univalent)
          (rezk_completion_locally_essentially_small U C (h .snd))))

def rezk_completion_essentially_small (U : Universe) (rep : Replacement U) (C : Precat)
  (h : IsEssentiallySmallPrecat U C) : IsEssentiallySmallPrecat U (category_precat (RezkCompletion C))
  ≔ (rezk_completion_objects_essentially_small U rep C h,
     rezk_completion_locally_essentially_small U C (h .snd))

{` The book's intermediate claims in the proof. (1) Ob(L(C)) is the image
   of Ob(yo) : Ob(C) → Ob(Set^{C^op}) (by univalence of Set^{C^op}, mere
   isomorphisms yo(c) ≅ F are mere identifications F = yo(c)). `}
def rezk_objects_image_equiv (C : Precat)
  : Equiv (RezkCompletion C .wild .ob)
      (Image (C .wild .ob) (PresheafCategory C .wild .ob) (yoneda_functor C .obj))
  ≔ let P ≔ PresheafCategory C in
    let yo ≔ yoneda_functor C in
    family_equiv (P .wild .ob) (F ↦ Mere (IsRepresentable C F))
      (F ↦ Mere (BookFiber (C .wild .ob) (P .wild .ob) (yo .obj) F))
      (F ↦ iff_equiv (Mere (IsRepresentable C F)) (Mere (BookFiber (C .wild .ob) (P .wild .ob) (yo .obj) F))
        (mere_isprop (IsRepresentable C F)) (mere_isprop (BookFiber (C .wild .ob) (P .wild .ob) (yo .obj) F))
        (trunc_map native_truncation (IsRepresentable C F) (BookFiber (C .wild .ob) (P .wild .ob) (yo .obj) F)
          (r ↦ (r .fst, inverse (P .wild .ob) (yo .obj (r .fst)) F
            (cat_isotoid (P .wild) (P .univalent) (yo .obj (r .fst)) F (r .snd)))))
        (trunc_map native_truncation (BookFiber (C .wild .ob) (P .wild .ob) (yo .obj) F) (IsRepresentable C F)
          (t ↦ (t .fst, cat_idtoiso (P .wild) (yo .obj (t .fst)) F (inverse (P .wild .ob) F (yo .obj (t .fst)) (t .snd))))))

{` (2) "We have the hom-functor C^op × C → Set_U": if C is locally U-small,
   every representable presheaf takes U-small values. `}
def representable_values_small (U : Universe) (C : Precat) (h : IsLocallySmallWildPrecat U (C .wild))
  (c x : C .wild .ob) : U .small (yoneda_functor C .obj c .obj x .fst)
  ≔ h x c

{` (3) "Since Ob(C) is essentially U-small, Set_U^{C^op} is locally
   U-small": natural transformations between presheaves with U-small
   values on an essentially U-small precategory form a U-small set. `}
def presheaf_hom_essentially_small (U : Universe) (C : Precat) (h : IsEssentiallySmallPrecat U C)
  (F G : PresheafCategory C .wild .ob)
  (hF : (x : C .wild .ob) → U .small (F .obj x .fst)) (hG : (x : C .wild .ob) → U .small (G .obj x .fst))
  : EssentiallySmall U (PresheafCategory C .wild .hom F G)
  ≔ let W ≔ OppositeWild (C .wild) in
    let sOb : U .small (C .wild .ob) ≔ essentially_small_is_small U (C .wild .ob) (h .fst) in
    let fun_small : (a b : C .wild .ob) → EssentiallySmall U (F .obj a .fst → G .obj b .fst)
      ≔ a b ↦ pi_essentially_small U (F .obj a .fst) (hF a) (_ ↦ G .obj b .fst)
          (_ ↦ small_essentially_small U (G .obj b .fst) (hG b)) in
    essentially_small_equiv U (Σ ((a : C .wild .ob) → F .obj a .fst → G .obj a .fst) (NatSquare W SetWild F G))
      (PresheafCategory C .wild .hom F G)
      (canonical_inverse_equiv (WildNatTrans W SetWild F G)
        (Σ ((a : C .wild .ob) → F .obj a .fst → G .obj a .fst) (NatSquare W SetWild F G))
        (nat_trans_sigma_equiv W SetWild F G))
      (sigma_essentially_small U ((a : C .wild .ob) → F .obj a .fst → G .obj a .fst)
        (pi_essentially_small U (C .wild .ob) sOb (a ↦ F .obj a .fst → G .obj a .fst) (a ↦ fun_small a a))
        (NatSquare W SetWild F G)
        (alpha ↦ pi_essentially_small U (C .wild .ob) sOb
          (a ↦ (b : C .wild .ob) (f : C .wild .hom b a)
            → Id (F .obj a .fst → G .obj b .fst)
                (SetWild .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
                (SetWild .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))
          (a ↦ pi_essentially_small U (C .wild .ob) sOb
            (b ↦ (f : C .wild .hom b a)
              → Id (F .obj a .fst → G .obj b .fst)
                  (SetWild .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
                  (SetWild .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))
            (b ↦ pi_essentially_small U (C .wild .hom b a)
              (essentially_small_is_small U (C .wild .hom b a) (h .snd b a))
              (f ↦ Id (F .obj a .fst → G .obj b .fst)
                  (SetWild .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
                  (SetWild .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))
              (f ↦ essentially_small_locally_small U (F .obj a .fst → G .obj b .fst) (fun_small a b)
                  (SetWild .comp (F .obj a) (G .obj a) (G .obj b) (G .mor a b f) (alpha a))
                  (SetWild .comp (F .obj a) (F .obj b) (G .obj b) (alpha b) (F .mor a b f)))))))

{` Litmus: for the universe of all types (which satisfies Replacement) the
   Rezk completion of any precategory is (essentially) small. `}
def rezk_completion_total_small (C : Precat)
  : IsEssentiallySmallPrecat total_universe (category_precat (RezkCompletion C))
  ≔ rezk_completion_essentially_small total_universe total_replacement C
      (small_essentially_small total_universe (C .wild .ob) star.,
       a b ↦ small_essentially_small total_universe (C .wild .hom a b) star.)
