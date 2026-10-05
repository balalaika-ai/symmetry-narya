export "544-restriction-injective"
export "437-conjugation-inner-automorphisms"
export "687-group-monomorphisms"
export "563-gset-fixed-points"

{` Chapter 9 (subgroups.tex), sec:epis, part 1: the introductory claims about
   injections and surjections of sets, lem:injmonosurjepiSet and its
   reformulation, def:monomorphism / def:epimorphism, exa:projections-epi and
   xca:mono1st-epi2nd. Categorical monos and epis are IsMono / IsEpi of
   module 609 in the category of groups GroupCat (module 686); chapter 5's
   IsGroupMono (USym i injective, def:typeofmono) is shown equivalent in
   module 687. `}

{` Helpers. A path of homomorphisms from a pointed homotopy of the
   classifying maps. `}
def ch9_hom_path (G H : Group) (f f' : GroupHom G H)
  (h : PointedHomotopy (BG G) (BG H) (hom_B G H f) (hom_B G H f')) : Id (GroupHom G H) f f'
  ≔ equiv_inverse_map (Id (GroupHom G H) f f') (PointedHomotopy (BG G) (BG H) (hom_B G H f) (hom_B G H f'))
      (group_hom_path_equiv G H f f') h

{` "Giving an element b : B is equivalent to giving a (necessarily
   constant) function 1 → B". `}
def unit_maps_point_equiv (B : Type) : Equiv (Unit → B) B
  ≔ quasi_inverse_equiv (Unit → B) B (c ↦ c star.) (b _ ↦ b)
      (c ↦ funext Unit (_ ↦ B) (_ ↦ c star.) c (u ↦ match u [ star. ↦ refl (c star.) ]))
      (b ↦ refl b)

{` lem:injmonosurjepiSet (it:injmono). For sets B, C, a function
   f : B → C is an injection iff for every set A and g, h : A → B,
   f ∘ g = f ∘ h implies g = h. `}
def SetPostCancellation (B C : Type) (f : B → C) : Type
  ≔ (A : SetTypes) (g h : A .fst → B)
    → Id (A .fst → C) (compose (A .fst) B C f g) (compose (A .fst) B C f h) → Id (A .fst → B) g h

def SetPreCancellation (B C : Type) (f : B → C) : Type
  ≔ (D : SetTypes) (g h : C → D .fst)
    → Id (B → D .fst) (compose B C (D .fst) g f) (compose B C (D .fst) h f) → Id (C → D .fst) g h

def injection_post_cancellation (B C : Type) (f : B → C) (hf : IsEmbedding B C f)
  : SetPostCancellation B C f
  ≔ A g h ↦ equiv_inverse_map (Id (A .fst → B) g h)
      (Id (A .fst → C) (compose (A .fst) B C f g) (compose (A .fst) B C f h))
      (cancel_injection B C (A .fst) f hf g h)

def post_cancellation_injection (B C : Type) (hC : isSet C) (f : B → C) (c : SetPostCancellation B C f)
  : IsEmbedding B C f
  ≔ path_reflecting_set_embedding B C hC f
      (x y p ↦ c (Unit, unit_set) (_ ↦ x) (_ ↦ y)
        (funext Unit (_ ↦ C) (_ ↦ f x) (_ ↦ f y) (_ ↦ p)) (refl (star. : Unit)))

def set_injection_iff_cancellation (B C : Type) (hB : isSet B) (hC : isSet C) (f : B → C)
  : Product (IsEmbedding B C f → SetPostCancellation B C f) (SetPostCancellation B C f → IsEmbedding B C f)
  ≔ (injection_post_cancellation B C f, post_cancellation_injection B C hC f)

{` lem:injmonosurjepiSet (it:surjepi). f is a surjection iff for every set
   D and g, h : C → D, g ∘ f = h ∘ f implies g = h (the test object for ⇐
   is the set of propositions, as in the second footnote of the section). `}
def surjection_pre_cancellation (B C : Type) (f : B → C) (hf : Surjective B C f) : SetPreCancellation B C f
  ≔ D g h ↦ equiv_inverse_map (Id (C → D .fst) g h)
      (Id (B → D .fst) (precompose B C (D .fst) f g) (precompose B C (D .fst) f h))
      (cancel_surjection_into_set B C (D .fst) f hf (D .snd) g h)

def pre_cancellation_surjection (B C : Type) (f : B → C) (c : SetPreCancellation B C f) : Surjective B C f
  ≔ surjective_from_prop_cancellation B C f
      (c (PropTypes, propositions_set) (surjectivity_predicate B C f) (_ ↦ (Unit, unit_prop))
        (surjectivity_predicate_restriction B C f))

def set_surjection_iff_cancellation (B C : Type) (hB : isSet B) (hC : isSet C) (f : B → C)
  : Product (Surjective B C f → SetPreCancellation B C f) (SetPreCancellation B C f → Surjective B C f)
  ≔ (surjection_pre_cancellation B C f, pre_cancellation_surjection B C f)

{` The reformulation after lem:injmonosurjepiSet: f is an injection iff for
   every set A post-composition (A → B) → (A → C) is an injection, i.e. f is
   a monomorphism of the category of sets (and dually, module 609,
   set_epi_iff_surjective, for surjections). `}
def set_injection_mono (B C : SetTypes) (f : B .fst → C .fst) (hf : IsEmbedding (B .fst) (C .fst) f)
  : IsMono (SetCat .wild) B C f
  ≔ A ↦ path_reflecting_set_embedding (A .fst → B .fst) (A .fst → C .fst) (pi_set (A .fst) (_ ↦ C .fst) (_ ↦ C .snd))
      (k ↦ x ↦ f (k x)) (injection_post_cancellation (B .fst) (C .fst) f hf A)

def set_mono_injection (B C : SetTypes) (f : B .fst → C .fst) (m : IsMono (SetCat .wild) B C f)
  : IsEmbedding (B .fst) (C .fst) f
  ≔ post_cancellation_injection (B .fst) (C .fst) (C .snd) f
      (A g h ↦ embedding_reflects_paths (A .fst → B .fst) (A .fst → C .fst) (k ↦ x ↦ f (k x)) (m A) g h)

def set_injection_iff_mono (B C : SetTypes) (f : B .fst → C .fst)
  : Product (IsEmbedding (B .fst) (C .fst) f → IsMono (SetCat .wild) B C f)
      (IsMono (SetCat .wild) B C f → IsEmbedding (B .fst) (C .fst) f)
  ≔ (set_injection_mono B C f, set_mono_injection B C f)

{` Running text of sec:epis: "f is surjective iff the first projection from
   the propositional image Σ_c ‖f⁻¹(c)‖ to C is an equivalence". `}
def surjective_image_include_equiv (B C : Type) (f : B → C) (hf : Surjective B C f) : BookEquiv (Image B C f) C
  ≔ native_embedding_surjection_equiv (Image B C f) C (image_include B C f) (image_include_embedding B C f)
      (c ↦ mere_rec (BookFiber B C f c) (Mere (BookFiber (Image B C f) C (image_include B C f) c))
        (mere_isprop (BookFiber (Image B C f) C (image_include B C f) c))
        (w ↦ mere (BookFiber (Image B C f) C (image_include B C f) c) (image_factor B C f (w .fst), w .snd))
        (hf c))

def image_include_equiv_surjective (B C : Type) (f : B → C)
  (e : BookIsEquiv (Image B C f) C (image_include B C f)) : Surjective B C f
  ≔ c ↦ transport C (x ↦ Mere (BookFiber B C f x)) (e c .center .fst .fst) c
      (inverse C c (e c .center .fst .fst) (e c .center .snd)) (e c .center .fst .snd)

{` Running text: for a surjection f : B → C and P : C → Prop, the
   propositions Π_c P(c) and Π_b P(f b) are equivalent. The first footnote
   says this "actually holds for any map f : B → C with B and C types";
   read literally (any map) it is false (counterexample below with
   f : Empty → Unit); it does hold for surjections between arbitrary types,
   which is what is proved here (no set hypothesis). `}
def surjection_all_prop_equiv (B C : Type) (f : B → C) (hf : Surjective B C f) (P : C → PropTypes)
  : Equiv ((c : C) → P c .fst) ((b : B) → P (f b) .fst)
  ≔ iff_equiv ((c : C) → P c .fst) ((b : B) → P (f b) .fst)
      (pi_prop C (c ↦ P c .fst) (c ↦ P c .snd)) (pi_prop B (b ↦ P (f b) .fst) (b ↦ P (f b) .snd))
      (k b ↦ k (f b))
      (k c ↦ mere_rec (BookFiber B C f c) (P c .fst) (P c .snd)
        (w ↦ transport C (x ↦ P x .fst) (f (w .fst)) c (inverse C c (f (w .fst)) (w .snd)) (k (w .fst))) (hf c))

def all_prop_any_map_counterexample
  (h : (B C : Type) (f : B → C) (P : C → PropTypes) → ((b : B) → P (f b) .fst) → (c : C) → P c .fst) : Empty
  ≔ h Empty Unit (x ↦ match x []) (_ ↦ (Empty, empty_prop)) (x ↦ match x []) star.

{` "In particular, if g, h : C → D are two functions into a set D the
   proposition Π_c (g c = h c) is equivalent to Π_b (g f b = h f b)." `}
def surjection_homotopy_equiv (B C D : Type) (hD : isSet D) (f : B → C) (hf : Surjective B C f) (g h : C → D)
  : Equiv ((c : C) → Id D (g c) (h c)) ((b : B) → Id D (g (f b)) (h (f b)))
  ≔ surjection_all_prop_equiv B C f hf (c ↦ (Id D (g c) (h c), hD (g c) (h c)))

{` The second footnote ("for the converse: take Prop for D, g(c) ≔ ‖f⁻¹(c)‖,
   h(c) ≔ true; then gf = hf, whereas g = h expresses surjectivity"):
   surjectivity_predicate_restriction and surjective_from_prop_cancellation
   (module 609) are exactly these two facts; pre_cancellation_surjection above
   uses them. `}

{` def:monomorphism. f : Hom(G, H) is a monomorphism if post-composition
   f ∘ - : Hom(F, G) → Hom(F, H) is an injection for every group F, and an
   epimorphism if pre-composition - ∘ f : Hom(H, I) → Hom(G, I) is an
   injection for every group I: the categorical notions of module 609 in
   GroupCat. The book uses the name ismono for both this notion and the one
   of def:typeofmono (USym f injective, chapter 5's IsGroupMono); the two are
   equivalent (module 687, group_mono_iff_usym_injective; lem:eq-mono-cover
   in module 938). `}
def IsGroupMonomorphism (G H : Group) (f : GroupHom G H) : Type ≔ IsMono (GroupCat .wild) G H f

def IsGroupEpi (G H : Group) (f : GroupHom G H) : Type ≔ IsEpi (GroupCat .wild) G H f

def is_group_monomorphism_prop (G H : Group) (f : GroupHom G H) : isProp (IsGroupMonomorphism G H f)
  ≔ is_mono_prop (GroupCat .wild) G H f

def is_group_epi_prop (G H : Group) (f : GroupHom G H) : isProp (IsGroupEpi G H f)
  ≔ is_epi_prop (GroupCat .wild) G H f

def group_monomorphism_mono_equiv (G H : Group) (f : GroupHom G H)
  : Equiv (IsGroupMonomorphism G H f) (IsGroupMono G H f)
  ≔ group_mono_usym_injective_equiv G H f

{` "A monomorphism (epimorphism) is called proper if it is not an
   isomorphism." `}
def IsProperGroupMonomorphism (G H : Group) (f : GroupHom G H) : Type
  ≔ Product (IsGroupMonomorphism G H f) (IsGroupIso G H f → Empty)

def IsProperGroupEpi (G H : Group) (f : GroupHom G H) : Type
  ≔ Product (IsGroupEpi G H f) (IsGroupIso G H f → Empty)

{` Mono(H) ≔ Σ_{G:Group} Σ_{i:Hom(G,H)} ismono(i) (categorical ismono), and
   its identification with chapter 5's Mono(H) (GroupMonos, USym-injective
   monomorphisms). `}
def GroupMonomorphismsInto (H : Group) : Type
  ≔ Σ Group (G ↦ Σ (GroupHom G H) (i ↦ IsGroupMonomorphism G H i))

def group_monomorphisms_into_equiv (H : Group) : Equiv (GroupMonomorphismsInto H) (GroupMonos H)
  ≔ family_equiv Group (G ↦ Σ (GroupHom G H) (i ↦ IsGroupMonomorphism G H i))
      (G ↦ Σ (GroupHom G H) (i ↦ IsGroupMono G H i))
      (G ↦ group_monos_total_equiv G H)

{` Epi(G) ≔ Σ_{H:Group} Σ_{f:Hom(G,H)} isepi(f). `}
def GroupEpis (G : Group) : Type ≔ Σ Group (H ↦ Σ (GroupHom G H) (f ↦ IsGroupEpi G H f))

{` xca:mono1st-epi2nd, in an arbitrary precategory (hom-sets give the
   cancellation form of module 609). `}
def precat_mono_compose (C : Precat) (a b c : C .wild .ob) (f : C .wild .hom a b) (g : C .wild .hom b c)
  (mf : IsMono (C .wild) a b f) (mg : IsMono (C .wild) b c g) : IsMono (C .wild) a c (C .wild .comp a b c g f)
  ≔ let W ≔ C .wild in
    precat_mono_iff_cancellation C a c (W .comp a b c g f) .snd
      (x u v e ↦
        precat_mono_iff_cancellation C a b f .fst mf x u v
          (precat_mono_iff_cancellation C b c g .fst mg x (W .comp x a b f u) (W .comp x a b f v)
            (calc
              W .comp x b c g (W .comp x a b f u)
              = W .comp x a c (W .comp a b c g f) u by W .assoc x a b c u f g
              = W .comp x a c (W .comp a b c g f) v by e
              = W .comp x b c g (W .comp x a b f v)
                by inverse (W .hom x c) (W .comp x b c g (W .comp x a b f v)) (W .comp x a c (W .comp a b c g f) v)
                     (W .assoc x a b c v f g) ∎)))

def precat_epi_compose (C : Precat) (a b c : C .wild .ob) (f : C .wild .hom a b) (g : C .wild .hom b c)
  (ef : IsEpi (C .wild) a b f) (eg : IsEpi (C .wild) b c g) : IsEpi (C .wild) a c (C .wild .comp a b c g f)
  ≔ let W ≔ C .wild in
    precat_epi_iff_cancellation C a c (W .comp a b c g f) .snd
      (x k k' e ↦
        precat_epi_iff_cancellation C b c g .fst eg x k k'
          (precat_epi_iff_cancellation C a b f .fst ef x (W .comp b c x k g) (W .comp b c x k' g)
            (calc
              W .comp a b x (W .comp b c x k g) f
              = W .comp a c x k (W .comp a b c g f)
                by inverse (W .hom a x) (W .comp a c x k (W .comp a b c g f)) (W .comp a b x (W .comp b c x k g) f)
                     (W .assoc a b c x f g k)
              = W .comp a c x k' (W .comp a b c g f) by e
              = W .comp a b x (W .comp b c x k' g) f by W .assoc a b c x f g k' ∎)))

def precat_epi_cancel_left (C : Precat) (a b c : C .wild .ob) (f1 : C .wild .hom a b) (f2 : C .wild .hom b c)
  (e : IsEpi (C .wild) a c (C .wild .comp a b c f2 f1)) : IsEpi (C .wild) b c f2
  ≔ let W ≔ C .wild in
    precat_epi_iff_cancellation C b c f2 .snd
      (x k k' r ↦ precat_epi_iff_cancellation C a c (W .comp a b c f2 f1) .fst e x k k'
        (calc
          W .comp a c x k (W .comp a b c f2 f1)
          = W .comp a b x (W .comp b c x k f2) f1 by W .assoc a b c x f1 f2 k
          = W .comp a b x (W .comp b c x k' f2) f1 by refl ((u ↦ W .comp a b x u f1) : W .hom b x → W .hom a x) r
          = W .comp a c x k' (W .comp a b c f2 f1)
            by inverse (W .hom a x) (W .comp a c x k' (W .comp a b c f2 f1)) (W .comp a b x (W .comp b c x k' f2) f1)
                 (W .assoc a b c x f1 f2 k') ∎))

def precat_mono_cancel_right (C : Precat) (a b c : C .wild .ob) (f1 : C .wild .hom a b) (f2 : C .wild .hom b c)
  (m : IsMono (C .wild) a c (C .wild .comp a b c f2 f1)) : IsMono (C .wild) a b f1
  ≔ let W ≔ C .wild in
    precat_mono_iff_cancellation C a b f1 .snd
      (x u v r ↦ precat_mono_iff_cancellation C a c (W .comp a b c f2 f1) .fst m x u v
        (calc
          W .comp x a c (W .comp a b c f2 f1) u
          = W .comp x b c f2 (W .comp x a b f1 u)
            by inverse (W .hom x c) (W .comp x b c f2 (W .comp x a b f1 u)) (W .comp x a c (W .comp a b c f2 f1) u)
                 (W .assoc x a b c u f1 f2)
          = W .comp x b c f2 (W .comp x a b f1 v) by refl ((w ↦ W .comp x b c f2 w) : W .hom x b → W .hom x c) r
          = W .comp x a c (W .comp a b c f2 f1) v by W .assoc x a b c v f1 f2 ∎))

{` xca:mono1st-epi2nd for groups (GroupCat is a category, hence a
   precategory). `}
def group_cat_precat : Precat ≔ category_precat GroupCat

def group_monomorphism_compose (G H K : Group) (f : GroupHom G H) (g : GroupHom H K)
  (mf : IsGroupMonomorphism G H f) (mg : IsGroupMonomorphism H K g)
  : IsGroupMonomorphism G K (group_hom_compose G H K f g)
  ≔ precat_mono_compose group_cat_precat G H K f g mf mg

def group_epi_compose (G H K : Group) (f : GroupHom G H) (g : GroupHom H K)
  (ef : IsGroupEpi G H f) (eg : IsGroupEpi H K g) : IsGroupEpi G K (group_hom_compose G H K f g)
  ≔ precat_epi_compose group_cat_precat G H K f g ef eg

def group_epi_cancel (G H K : Group) (f1 : GroupHom G H) (f2 : GroupHom H K)
  (e : IsGroupEpi G K (group_hom_compose G H K f1 f2)) : IsGroupEpi H K f2
  ≔ precat_epi_cancel_left group_cat_precat G H K f1 f2 e

def group_monomorphism_cancel (G H K : Group) (f1 : GroupHom G H) (f2 : GroupHom H K)
  (m : IsGroupMonomorphism G K (group_hom_compose G H K f1 f2)) : IsGroupMonomorphism G H f1
  ≔ precat_mono_cancel_right group_cat_precat G H K f1 f2 m

{` Split epimorphisms are epimorphisms: g = g ∘ (p ∘ s) = (g ∘ p) ∘ s. `}
def precat_split_epi (C : Precat) (a b : C .wild .ob) (p : C .wild .hom a b) (s : C .wild .hom b a)
  (r : Id (C .wild .hom b b) (C .wild .comp b a b p s) (C .wild .idn b)) : IsEpi (C .wild) a b p
  ≔ let W ≔ C .wild in
    precat_epi_iff_cancellation C a b p .snd
      (x k k' e ↦ calc
        k = W .comp b b x k (W .idn b) by inverse (W .hom b x) (W .comp b b x k (W .idn b)) k (W .ru b x k)
        = W .comp b b x k (W .comp b a b p s)
          by refl ((u ↦ W .comp b b x k u) : W .hom b b → W .hom b x)
               (inverse (W .hom b b) (W .comp b a b p s) (W .idn b) r)
        = W .comp b a x (W .comp a b x k p) s by W .assoc b a b x s p k
        = W .comp b a x (W .comp a b x k' p) s by refl ((u ↦ W .comp b a x u s) : W .hom a x → W .hom b x) e
        = W .comp b b x k' (W .comp b a b p s)
          by inverse (W .hom b x) (W .comp b b x k' (W .comp b a b p s)) (W .comp b a x (W .comp a b x k' p) s)
               (W .assoc b a b x s p k')
        = W .comp b b x k' (W .idn b) by refl ((u ↦ W .comp b b x k' u) : W .hom b b → W .hom b x) r
        = k' by W .ru b x k' ∎)

{` exa:projections-epi. The projections G1 × G2 → G1, G2 have the
   inclusions as sections, hence are epimorphisms. `}
def product_proj1_incl1_path (G H : Group)
  : Id (GroupHom G G) (group_hom_compose G (product_group G H) G (product_group_incl1 G H) (product_group_proj1 G H))
      (group_hom_id G)
  ≔ let B ≔ BG G .carrier in
    ch9_hom_path G G (group_hom_compose G (product_group G H) G (product_group_incl1 G H) (product_group_proj1 G H))
      (group_hom_id G)
      ((z ↦ refl z),
       calc
         concat B (shape G) (shape G) (shape G) (concat B (shape G) (shape G) (shape G) (refl (shape G)) (refl (shape G)))
           (refl (shape G))
         = concat B (shape G) (shape G) (shape G) (refl (shape G)) (refl (shape G))
           by concat_p1 B (shape G) (shape G) (concat B (shape G) (shape G) (shape G) (refl (shape G)) (refl (shape G)))
         = refl (shape G) by concat_p1 B (shape G) (shape G) (refl (shape G)) ∎)

def product_proj2_incl2_path (G H : Group)
  : Id (GroupHom H H) (group_hom_compose H (product_group G H) H (product_group_incl2 G H) (product_group_proj2 G H))
      (group_hom_id H)
  ≔ let B ≔ BG H .carrier in
    ch9_hom_path H H (group_hom_compose H (product_group G H) H (product_group_incl2 G H) (product_group_proj2 G H))
      (group_hom_id H)
      ((z ↦ refl z),
       calc
         concat B (shape H) (shape H) (shape H) (concat B (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H)))
           (refl (shape H))
         = concat B (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H))
           by concat_p1 B (shape H) (shape H) (concat B (shape H) (shape H) (shape H) (refl (shape H)) (refl (shape H)))
         = refl (shape H) by concat_p1 B (shape H) (shape H) (refl (shape H)) ∎)

def product_proj1_epi (G H : Group) : IsGroupEpi (product_group G H) G (product_group_proj1 G H)
  ≔ precat_split_epi group_cat_precat (product_group G H) G (product_group_proj1 G H) (product_group_incl1 G H)
      (product_proj1_incl1_path G H)

def product_proj2_epi (G H : Group) : IsGroupEpi (product_group G H) H (product_group_proj2 G H)
  ≔ precat_split_epi group_cat_precat (product_group G H) H (product_group_proj2 G H) (product_group_incl2 G H)
      (product_proj2_incl2_path G H)
