export "02-duality"
export "../../../src/202-higher-truncations"
export "../../../src/500-gsets"

{` Blind statements, chapter 6, section "Functors and natural transformations". `}

{` A five-step path composite (helper). `}
def blind_path5 (A : Type) (x0 x1 x2 x3 x4 x5 : A) (p1 : Id A x0 x1) (p2 : Id A x1 x2)
  (p3 : Id A x2 x3) (p4 : Id A x3 x4) (p5 : Id A x4 x5) : Id A x0 x5
  ≔ concat A x0 x1 x5 p1 (concat A x1 x2 x5 p2 (concat A x2 x3 x5 p3 (concat A x3 x4 x5 p4 p5)))

{` def:functor. F_id : F(id_A) = id_{F A}, F_∘ : F(g ∘ f) = F(g) ∘ F(f). `}
def BlindWildFunctor (C D : BlindWildPrecat) : Type ≔ sig (
  fob : C .ob → D .ob,
  fhom : (a b : C .ob) → C .hom a b → D .hom (fob a) (fob b),
  fid : (a : C .ob) → Id (D .hom (fob a) (fob a)) (fhom a a (C .idn a)) (D .idn (fob a)),
  fcomp : (a b c : C .ob) (f : C .hom a b) (g : C .hom b c)
    → Id (D .hom (fob a) (fob c)) (fhom a c (C .comp a b c g f))
        (D .comp (fob a) (fob b) (fob c) (fhom b c g) (fhom a b f)))

{` The laws for a given action on objects and arrows ("extends to a wild functor"). `}
def BlindWildFunctorLaws (C D : BlindWildPrecat) (fo : C .ob → D .ob)
  (fh : (a b : C .ob) → C .hom a b → D .hom (fo a) (fo b)) : Type
  ≔ Product ((a : C .ob) → Id (D .hom (fo a) (fo a)) (fh a a (C .idn a)) (D .idn (fo a)))
      ((a b c : C .ob) (f : C .hom a b) (g : C .hom b c)
        → Id (D .hom (fo a) (fo c)) (fh a c (C .comp a b c g f)) (D .comp (fo a) (fo b) (fo c) (fh b c g) (fh a b f)))

def blind_functor_of_laws (C D : BlindWildPrecat) (fo : C .ob → D .ob)
  (fh : (a b : C .ob) → C .hom a b → D .hom (fo a) (fo b)) (l : BlindWildFunctorLaws C D fo fh)
  : BlindWildFunctor C D
  ≔ (fo, fh, l .fst, l .snd)

{` "If D is a precategory, the types of F_id and F_∘ are propositions";
   then F is called a functor. `}
def blind_def_functor_laws_prop : Type
  ≔ (C : BlindWildPrecat) (D : BlindPrecat) (fo : C .ob → D .fst .ob)
    (fh : (a b : C .ob) → C .hom a b → D .fst .hom (fo a) (fo b))
    → isProp (BlindWildFunctorLaws C (D .fst) fo fh)

def BlindFunctor (C D : BlindPrecat) : Type ≔ BlindWildFunctor (C .fst) (D .fst)

{` xca:wild-functor-isos. `}
def blind_xca_wild_functor_isos : Type
  ≔ (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (a b : C .ob) (f : C .hom a b)
    → BlindIsIso C a b f → BlindIsIso D (F .fob a) (F .fob b) (F .fhom a b f)

{` ex:functor-preorders. `}
def blind_ex_functor_preorders : Type
  ≔ (P Q : BlindPreorder)
    → BookEquiv (BlindWildFunctor (P .fst .fst) (Q .fst .fst))
        (Σ (P .fst .fst .ob → Q .fst .fst .ob) (F ↦
          (p p' : P .fst .fst .ob) → P .fst .fst .hom p p' → Q .fst .fst .hom (F p) (F p')))

{` ex:USym-functor. `}
def blind_ex_usym_functor : Type
  ≔ BlindWildFunctorLaws (blind_group_precat .fst) (blind_set_precat .fst)
      (G ↦ (USym G, usym_set G)) (G H f ↦ usym_hom G H f)

{` ex:action-functors. The category of G-sets (def:map-of-Gsets). `}
def blind_gset_precat (G : Group) : BlindPrecat
  ≔ ((GSet G, GSetHom G, gset_hom_id G, (X Y Z g f ↦ gset_hom_compose G X Y Z f g),
      (X Y f ↦ refl f), (X Y f ↦ refl f), (X Y Z W f g h ↦ refl (z x ↦ h z (g z (f z x))))),
     gset_hom_set G)

def blind_restrict_hom (G H : Group) (f : GroupHom G H) (X Y : GSet H) (g : GSetHom H X Y)
  : GSetHom G (gset_restrict G H f X) (gset_restrict G H f Y)
  ≔ z ↦ g (hom_function G H f z)

def blind_induce_hom (G H : Group) (f : GroupHom G H) (X Y : GSet G) (g : GSetHom G X Y)
  : GSetHom H (gset_induce G H f X) (gset_induce G H f Y)
  ≔ w ↦ set_trunc_rec (GSetInducedSum G H f X w) (SetTrunc (GSetInducedSum G H f Y w))
      (set_trunc_set (GSetInducedSum G H f Y w))
      (u ↦ set_trunc (GSetInducedSum G H f Y w) (u .fst, (u .snd .fst, g (u .fst) (u .snd .snd))))

def blind_coinduce_hom (G H : Group) (f : GroupHom G H) (X Y : GSet G) (g : GSetHom G X Y)
  : GSetHom H (gset_coinduce G H f X) (gset_coinduce G H f Y)
  ≔ w s z p ↦ g z (s z p)

def blind_ex_action_functors : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Product (BlindWildFunctorLaws (blind_gset_precat H .fst) (blind_gset_precat G .fst)
                 (gset_restrict G H f) (blind_restrict_hom G H f))
        (Product (BlindWildFunctorLaws (blind_gset_precat G .fst) (blind_gset_precat H .fst)
                    (gset_induce G H f) (blind_induce_hom G H f))
           (BlindWildFunctorLaws (blind_gset_precat G .fst) (blind_gset_precat H .fst)
              (gset_coinduce G H f) (blind_coinduce_hom G H f)))

{` def:n-trunc-functor. Book n-truncation = Trunc k with k = n + 1 (n ≥ -1);
   U^{≤n} is the full subcategory on HLevel (k + 1) types. `}
def blind_truncated_universe (k : Nat) : BlindWildPrecat
  ≔ blind_full_subcat blind_universe_wild_precat (A ↦ (HLevel (suc. k) A, hlevel_isprop (suc. k) A))

def blind_trunc_hom (k : Nat) (A B : Type) (f : A → B) : Trunc k A → Trunc k B
  ≔ trunc_extend k A (truncation k A) (Trunc k B) (trunc_level k B) (a ↦ trunc_unit k B (f a))

def blind_ex_trunc_functor : Type
  ≔ (k : Nat) → BlindWildFunctorLaws blind_universe_wild_precat (blind_truncated_universe k)
      (A ↦ (Trunc k A, trunc_level k A)) (blind_trunc_hom k)

{` ex:add-remove-basepoint. A_+ = (A ⊔ 1, inr ⋆). `}
def blind_plus_ob (A : Type) : Pointed ≔ (Sum A Unit, inr. star.)

def blind_plus_fun (A B : Type) (f : A → B) : Sum A Unit → Sum B Unit
  ≔ x ↦ match x [ inl. a ↦ inl. (f a) | inr. u ↦ inr. u ]

def blind_plus_hom (A B : Type) (f : A → B) : BookPointedMap (blind_plus_ob A) (blind_plus_ob B)
  ≔ (blind_plus_fun A B f, refl (inr. star. : Sum B Unit))

def blind_ex_plus_functor : Type
  ≔ BlindWildFunctorLaws blind_universe_wild_precat blind_pointed_wild_precat blind_plus_ob blind_plus_hom

def blind_forget_functor : BlindWildFunctor blind_pointed_wild_precat blind_universe_wild_precat
  ≔ ((A ↦ A .carrier), (A B f ↦ f .fst), (A ↦ refl (x ↦ x)),
     (A B C f g ↦ refl (x ↦ g .fst (f .fst x))))

{` ex:loop-functor. Ω k with the pointing path refl = Ω k (refl) of ch. 4. `}
def blind_loops_hom (X Y : Pointed) (k : BookPointedMap X Y) : BookPointedMap (Omega X) (Omega Y)
  ≔ (loops_map X Y k, loops_map_point X Y k)

def blind_ex_loop_functor : Type
  ≔ BlindWildFunctorLaws blind_pointed_wild_precat blind_pointed_wild_precat Omega blind_loops_hom

{` ex:slice-projection. `}
def blind_slice_projection (C : BlindPrecat) (c : C .fst .ob)
  : BlindWildFunctor (blind_slice_precat C c .fst) (C .fst)
  ≔ ((u ↦ u .fst), (u v g ↦ g .fst), (u ↦ refl (C .fst .idn (u .fst))),
     (u v w f g ↦ refl (C .fst .comp (u .fst) (v .fst) (w .fst) (g .fst) (f .fst))))

{` ex:arrow-cat. Arrows (g, h) with f' ∘ g = h ∘ f. `}
def BlindArrowOb (C : BlindWildPrecat) : Type ≔ Σ (C .ob) (a ↦ Σ (C .ob) (b ↦ C .hom a b))

def BlindArrowSq (C : BlindWildPrecat) (u v : BlindArrowOb C)
  (gh : Product (C .hom (u .fst) (v .fst)) (C .hom (u .snd .fst) (v .snd .fst))) : Type
  ≔ Id (C .hom (u .fst) (v .snd .fst)) (C .comp (u .fst) (v .fst) (v .snd .fst) (v .snd .snd) (gh .fst))
      (C .comp (u .fst) (u .snd .fst) (v .snd .fst) (gh .snd) (u .snd .snd))

def BlindArrowHom (C : BlindWildPrecat) (u v : BlindArrowOb C) : Type
  ≔ Σ (Product (C .hom (u .fst) (v .fst)) (C .hom (u .snd .fst) (v .snd .fst))) (BlindArrowSq C u v)

def blind_arrow_hom_path (C : BlindPrecat) (u v : BlindArrowOb (C .fst)) (m n : BlindArrowHom (C .fst) u v)
  (p : Id (Product (C .fst .hom (u .fst) (v .fst)) (C .fst .hom (u .snd .fst) (v .snd .fst))) (m .fst) (n .fst))
  : Id (BlindArrowHom (C .fst) u v) m n
  ≔ equiv_inverse_map (Id (BlindArrowHom (C .fst) u v) m n)
      (Id (Product (C .fst .hom (u .fst) (v .fst)) (C .fst .hom (u .snd .fst) (v .snd .fst))) (m .fst) (n .fst))
      (subtype_path_equiv (Product (C .fst .hom (u .fst) (v .fst)) (C .fst .hom (u .snd .fst) (v .snd .fst)))
        (BlindArrowSq (C .fst) u v)
        (gh ↦ C .snd (u .fst) (v .snd .fst)
           (C .fst .comp (u .fst) (v .fst) (v .snd .fst) (v .snd .snd) (gh .fst))
           (C .fst .comp (u .fst) (u .snd .fst) (v .snd .fst) (gh .snd) (u .snd .snd))) m n) p

def blind_arrow_id (C : BlindWildPrecat) (u : BlindArrowOb C) : BlindArrowHom C u u
  ≔ let a ≔ u .fst in let b ≔ u .snd .fst in let f ≔ u .snd .snd in
    ((C .idn a, C .idn b),
     concat (C .hom a b) (C .comp a a b f (C .idn a)) f (C .comp a b b (C .idn b) f)
       (C .runit a b f) (inverse (C .hom a b) (C .comp a b b (C .idn b) f) f (C .lunit a b f)))

def blind_arrow_comp (C : BlindWildPrecat) (u v w : BlindArrowOb C)
  (m' : BlindArrowHom C v w) (m : BlindArrowHom C u v) : BlindArrowHom C u w
  ≔ let ua ≔ u .fst in let ub ≔ u .snd .fst in let uf ≔ u .snd .snd in
    let va ≔ v .fst in let vb ≔ v .snd .fst in let vf ≔ v .snd .snd in
    let wa ≔ w .fst in let wb ≔ w .snd .fst in let wf ≔ w .snd .snd in
    let g ≔ m .fst .fst in let h ≔ m .fst .snd in
    let g' ≔ m' .fst .fst in let h' ≔ m' .fst .snd in
    ((C .comp ua va wa g' g, C .comp ub vb wb h' h),
     blind_path5 (C .hom ua wb)
       (C .comp ua wa wb wf (C .comp ua va wa g' g))
       (C .comp ua va wb (C .comp va wa wb wf g') g)
       (C .comp ua va wb (C .comp va vb wb h' vf) g)
       (C .comp ua vb wb h' (C .comp ua va vb vf g))
       (C .comp ua vb wb h' (C .comp ua ub vb h uf))
       (C .comp ua ub wb (C .comp ub vb wb h' h) uf)
       (C .assoc ua va wa wb g g' wf)
       (refl (x ↦ C .comp ua va wb x g) (m' .snd))
       (inverse (C .hom ua wb) (C .comp ua vb wb h' (C .comp ua va vb vf g))
          (C .comp ua va wb (C .comp va vb wb h' vf) g) (C .assoc ua va vb wb g vf h'))
       (refl (C .comp ua vb wb h') (m .snd))
       (C .assoc ua ub vb wb uf h h'))

def blind_arrow_precat (C : BlindPrecat) : BlindPrecat
  ≔ let W ≔ C .fst in
    ((BlindArrowOb W, BlindArrowHom W, blind_arrow_id W, blind_arrow_comp W,
      (u v m ↦ blind_arrow_hom_path C u v (blind_arrow_comp W u v v (blind_arrow_id W v) m) m
         (W .lunit (u .fst) (v .fst) (m .fst .fst), W .lunit (u .snd .fst) (v .snd .fst) (m .fst .snd))),
      (u v m ↦ blind_arrow_hom_path C u v (blind_arrow_comp W u u v m (blind_arrow_id W u)) m
         (W .runit (u .fst) (v .fst) (m .fst .fst), W .runit (u .snd .fst) (v .snd .fst) (m .fst .snd))),
      (u v w x f g h ↦ blind_arrow_hom_path C u x
         (blind_arrow_comp W u w x h (blind_arrow_comp W u v w g f))
         (blind_arrow_comp W u v x (blind_arrow_comp W v w x h g) f)
         (W .assoc (u .fst) (v .fst) (w .fst) (x .fst) (f .fst .fst) (g .fst .fst) (h .fst .fst),
          W .assoc (u .snd .fst) (v .snd .fst) (w .snd .fst) (x .snd .fst) (f .fst .snd) (g .fst .snd) (h .fst .snd)))),
     (u v ↦ sigma_set (Product (W .hom (u .fst) (v .fst)) (W .hom (u .snd .fst) (v .snd .fst)))
        (BlindArrowSq W u v)
        (sigma_set (W .hom (u .fst) (v .fst)) (_ ↦ W .hom (u .snd .fst) (v .snd .fst))
           (C .snd (u .fst) (v .fst)) (_ ↦ C .snd (u .snd .fst) (v .snd .fst)))
        (gh ↦ prop_is_set (BlindArrowSq W u v gh)
           (C .snd (u .fst) (v .snd .fst)
             (W .comp (u .fst) (v .fst) (v .snd .fst) (v .snd .snd) (gh .fst))
             (W .comp (u .fst) (u .snd .fst) (v .snd .fst) (gh .snd) (u .snd .snd))))))

def blind_arrow_dom (C : BlindPrecat) : BlindWildFunctor (blind_arrow_precat C .fst) (C .fst)
  ≔ ((u ↦ u .fst), (u v m ↦ m .fst .fst), (u ↦ refl (C .fst .idn (u .fst))),
     (u v w f g ↦ refl (C .fst .comp (u .fst) (v .fst) (w .fst) (g .fst .fst) (f .fst .fst))))

def blind_arrow_cod (C : BlindPrecat) : BlindWildFunctor (blind_arrow_precat C .fst) (C .fst)
  ≔ ((u ↦ u .snd .fst), (u v m ↦ m .fst .snd), (u ↦ refl (C .fst .idn (u .snd .fst))),
     (u v w f g ↦ refl (C .fst .comp (u .snd .fst) (v .snd .fst) (w .snd .fst) (g .fst .snd) (f .fst .snd))))

{` "C^→ is a category if C is". `}
def blind_ex_arrow_univalent : Type
  ≔ (C : BlindCat) → BlindIsUnivalent (blind_arrow_precat (C .fst) .fst)

{` xca:wildprecat-of-wildprecats. Identity and composition (G ∘ F) of wild
   functors; the laws λ, ρ, α are the statement. `}
def blind_functor_id (C : BlindWildPrecat) : BlindWildFunctor C C
  ≔ ((a ↦ a), (a b f ↦ f), (a ↦ refl (C .idn a)), (a b c f g ↦ refl (C .comp a b c g f)))

def blind_functor_comp (C D E : BlindWildPrecat) (G : BlindWildFunctor D E) (F : BlindWildFunctor C D)
  : BlindWildFunctor C E
  ≔ ((a ↦ G .fob (F .fob a)),
     (a b f ↦ G .fhom (F .fob a) (F .fob b) (F .fhom a b f)),
     (a ↦ concat (E .hom (G .fob (F .fob a)) (G .fob (F .fob a)))
        (G .fhom (F .fob a) (F .fob a) (F .fhom a a (C .idn a)))
        (G .fhom (F .fob a) (F .fob a) (D .idn (F .fob a)))
        (E .idn (G .fob (F .fob a)))
        (refl (G .fhom (F .fob a) (F .fob a)) (F .fid a)) (G .fid (F .fob a))),
     (a b c f g ↦ concat (E .hom (G .fob (F .fob a)) (G .fob (F .fob c)))
        (G .fhom (F .fob a) (F .fob c) (F .fhom a c (C .comp a b c g f)))
        (G .fhom (F .fob a) (F .fob c) (D .comp (F .fob a) (F .fob b) (F .fob c) (F .fhom b c g) (F .fhom a b f)))
        (E .comp (G .fob (F .fob a)) (G .fob (F .fob b)) (G .fob (F .fob c))
           (G .fhom (F .fob b) (F .fob c) (F .fhom b c g)) (G .fhom (F .fob a) (F .fob b) (F .fhom a b f)))
        (refl (G .fhom (F .fob a) (F .fob c)) (F .fcomp a b c f g))
        (G .fcomp (F .fob a) (F .fob b) (F .fob c) (F .fhom a b f) (F .fhom b c g))))

def BlindFunctorLunit : Type
  ≔ (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
    → Id (BlindWildFunctor C D) (blind_functor_comp C D D (blind_functor_id D) F) F

def BlindFunctorRunit : Type
  ≔ (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
    → Id (BlindWildFunctor C D) (blind_functor_comp C C D F (blind_functor_id C)) F

def BlindFunctorAssoc : Type
  ≔ (C0 C1 C2 C3 : BlindWildPrecat) (F : BlindWildFunctor C0 C1) (G : BlindWildFunctor C1 C2)
    (H : BlindWildFunctor C2 C3)
    → Id (BlindWildFunctor C0 C3) (blind_functor_comp C0 C2 C3 H (blind_functor_comp C0 C1 C2 G F))
        (blind_functor_comp C0 C1 C3 (blind_functor_comp C1 C2 C3 H G) F)

def blind_xca_wildprecat_of_wildprecats : Type
  ≔ Product BlindFunctorLunit (Product BlindFunctorRunit BlindFunctorAssoc)

{` The wild precategory of wild precategories, for any choice of the laws. `}
def blind_wpc_of (l : BlindFunctorLunit) (r : BlindFunctorRunit) (a : BlindFunctorAssoc) : BlindWildPrecat
  ≔ (BlindWildPrecat, BlindWildFunctor, blind_functor_id, blind_functor_comp, l, r, a)

{` "If you're feeling adventurous": laws together with pentagon fillers. `}
def blind_xca_wildprecat_pentagon : Type
  ≔ Σ BlindFunctorLunit (l ↦ Σ BlindFunctorRunit (r ↦ Σ BlindFunctorAssoc (a ↦
      BlindPentagon (blind_wpc_of l r a))))

{` xca:wildcat-of-precats. PreCat and Cat as full subcategories. Univalence
   does not depend on the chosen λ (it is Σ_b Iso(a, b) contractible), so
   the statement quantifies over the laws. `}
def blind_is_precat_prop (C : BlindWildPrecat) : PropTypes
  ≔ ((a b : C .ob) → isSet (C .hom a b),
     pi_prop (C .ob) (a ↦ (b : C .ob) → isSet (C .hom a b))
       (a ↦ pi_prop (C .ob) (b ↦ isSet (C .hom a b)) (b ↦ isset_isprop (C .hom a b))))

def blind_univalent_prop (C : BlindWildPrecat) : isProp (BlindIsUnivalent C)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) → BookIsEquiv (Id (C .ob) a b) (BlindIso C a b) (blind_idtoiso C a b))
      (a ↦ pi_prop (C .ob) (b ↦ BookIsEquiv (Id (C .ob) a b) (BlindIso C a b) (blind_idtoiso C a b))
        (b ↦ book_isequiv_isprop (Id (C .ob) a b) (BlindIso C a b) (blind_idtoiso C a b)))

def blind_is_cat_prop (C : BlindWildPrecat) : PropTypes
  ≔ (Product (blind_is_precat_prop C .fst) (BlindIsUnivalent C),
     sigma_prop (blind_is_precat_prop C .fst) (_ ↦ BlindIsUnivalent C) (blind_is_precat_prop C .snd)
       (_ ↦ blind_univalent_prop C))

def blind_xca_wildcat_of_precats : Type
  ≔ (l : BlindFunctorLunit) (r : BlindFunctorRunit) (a : BlindFunctorAssoc)
    → Product (BlindIsUnivalent (blind_full_subcat (blind_wpc_of l r a) blind_is_precat_prop))
        (BlindIsUnivalent (blind_full_subcat (blind_wpc_of l r a) blind_is_cat_prop))

{` def:full-faithful. `}
def BlindIsFaithful (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ (a b : C .ob) → IsEmbedding (C .hom a b) (D .hom (F .fob a) (F .fob b)) (F .fhom a b)

def BlindIsFull (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ (a b : C .ob) → Surjective (C .hom a b) (D .hom (F .fob a) (F .fob b)) (F .fhom a b)

def BlindIsFullyFaithful (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ Product (BlindIsFull C D F) (BlindIsFaithful C D F)

{` "(and hence equivalences)". `}
def blind_def_fully_faithful_equiv : Type
  ≔ (C D : BlindWildPrecat) (F : BlindWildFunctor C D) → BlindIsFullyFaithful C D F
    → (a b : C .ob) → BookIsEquiv (C .hom a b) (D .hom (F .fob a) (F .fob b)) (F .fhom a b)

{` wip example: "full subcategory inclusions are fully faithful". `}
def blind_full_subcat_inclusion (C : BlindWildPrecat) (P : C .ob → PropTypes)
  : BlindWildFunctor (blind_full_subcat C P) C
  ≔ ((x ↦ x .fst), (x y f ↦ f), (x ↦ refl (C .idn (x .fst))),
     (x y z f g ↦ refl (C .comp (x .fst) (y .fst) (z .fst) g f)))

def blind_wip_full_subcat_inclusion_ff : Type
  ≔ (C : BlindWildPrecat) (P : C .ob → PropTypes)
    → BlindIsFullyFaithful (blind_full_subcat C P) C (blind_full_subcat_inclusion C P)

{` def:nat-trans. Square: G(f) ∘ α_A = α_B ∘ F(f). `}
def BlindNatSquares (C D : BlindWildPrecat) (F G : BlindWildFunctor C D)
  (al : (a : C .ob) → D .hom (F .fob a) (G .fob a)) : Type
  ≔ (a b : C .ob) (f : C .hom a b)
    → Id (D .hom (F .fob a) (G .fob b)) (D .comp (F .fob a) (G .fob a) (G .fob b) (G .fhom a b f) (al a))
        (D .comp (F .fob a) (F .fob b) (G .fob b) (al b) (F .fhom a b f))

def BlindNatTrans (C D : BlindWildPrecat) (F G : BlindWildFunctor C D) : Type
  ≔ Σ ((a : C .ob) → D .hom (F .fob a) (G .fob a)) (BlindNatSquares C D F G)

def blind_nat_squares_prop (C : BlindWildPrecat) (D : BlindPrecat) (F G : BlindWildFunctor C (D .fst))
  (al : (a : C .ob) → D .fst .hom (F .fob a) (G .fob a)) : isProp (BlindNatSquares C (D .fst) F G al)
  ≔ let W ≔ D .fst in
    pi_prop (C .ob) (a ↦ (b : C .ob) (f : C .hom a b)
        → Id (W .hom (F .fob a) (G .fob b)) (W .comp (F .fob a) (G .fob a) (G .fob b) (G .fhom a b f) (al a))
            (W .comp (F .fob a) (F .fob b) (G .fob b) (al b) (F .fhom a b f)))
      (a ↦ pi_prop (C .ob) (b ↦ (f : C .hom a b)
          → Id (W .hom (F .fob a) (G .fob b)) (W .comp (F .fob a) (G .fob a) (G .fob b) (G .fhom a b f) (al a))
              (W .comp (F .fob a) (F .fob b) (G .fob b) (al b) (F .fhom a b f)))
        (b ↦ pi_prop (C .hom a b) (f ↦ Id (W .hom (F .fob a) (G .fob b))
              (W .comp (F .fob a) (G .fob a) (G .fob b) (G .fhom a b f) (al a))
              (W .comp (F .fob a) (F .fob b) (G .fob b) (al b) (F .fhom a b f)))
          (f ↦ D .snd (F .fob a) (G .fob b) (W .comp (F .fob a) (G .fob a) (G .fob b) (G .fhom a b f) (al a))
              (W .comp (F .fob a) (F .fob b) (G .fob b) (al b) (F .fhom a b f)))))

{` "If D is a precategory, the types of the naturality squares are
   propositions." `}
def blind_def_nat_trans_squares_prop : Type
  ≔ (C : BlindWildPrecat) (D : BlindPrecat) (F G : BlindWildFunctor C (D .fst))
    (al : (a : C .ob) → D .fst .hom (F .fob a) (G .fob a)) (a b : C .ob) (f : C .hom a b)
    → isProp (Id (D .fst .hom (F .fob a) (G .fob b))
        (D .fst .comp (F .fob a) (G .fob a) (G .fob b) (G .fhom a b f) (al a))
        (D .fst .comp (F .fob a) (F .fob b) (G .fob b) (al b) (F .fhom a b f)))

{` ex:pt-unpt-unit. η : id_U → (−)_÷ ∘ (−)_+, components inl, squares refl.
   Parametrised by the functor laws of (−)_+ (ex:add-remove-basepoint),
   which the squares do not use. `}
def blind_ex_pt_unpt_unit
  (pl : BlindWildFunctorLaws blind_universe_wild_precat blind_pointed_wild_precat blind_plus_ob blind_plus_hom)
  : BlindNatTrans blind_universe_wild_precat blind_universe_wild_precat
      (blind_functor_id blind_universe_wild_precat)
      (blind_functor_comp blind_universe_wild_precat blind_pointed_wild_precat blind_universe_wild_precat
         blind_forget_functor
         (blind_functor_of_laws blind_universe_wild_precat blind_pointed_wild_precat blind_plus_ob blind_plus_hom pl))
  ≔ ((A ↦ x ↦ inl. x), (A B f ↦ refl ((x ↦ inl. (f x)) : A → Sum B Unit)))

{` ex:path-gpd-nat. ap f is a wild functor of path groupoids; a homotopy
   h : f ~ g gives naturality squares (statement). `}
def blind_path_functor (A B : Type) (f : A → B)
  : BlindWildFunctor (blind_path_wild_precat A) (blind_path_wild_precat B)
  ≔ (f, (x y p ↦ refl f p), (x ↦ refl (refl (f x))),
     (x y z p q ↦ map_path_concat A B f x y z p q))

def blind_ex_path_gpd_nat : Type
  ≔ (A B : Type) (f g : A → B) (h : (x : A) → Id B (f x) (g x))
    → BlindNatSquares (blind_path_wild_precat A) (blind_path_wild_precat B)
        (blind_path_functor A B f) (blind_path_functor A B g) h

{` def:functor-cat. `}
def blind_nat_path (C : BlindWildPrecat) (D : BlindPrecat) (F G : BlindWildFunctor C (D .fst))
  (al be : BlindNatTrans C (D .fst) F G)
  (p : (a : C .ob) → Id (D .fst .hom (F .fob a) (G .fob a)) (al .fst a) (be .fst a))
  : Id (BlindNatTrans C (D .fst) F G) al be
  ≔ equiv_inverse_map (Id (BlindNatTrans C (D .fst) F G) al be)
      (Id ((a : C .ob) → D .fst .hom (F .fob a) (G .fob a)) (al .fst) (be .fst))
      (subtype_path_equiv ((a : C .ob) → D .fst .hom (F .fob a) (G .fob a)) (BlindNatSquares C (D .fst) F G)
        (blind_nat_squares_prop C D F G) al be)
      (funext (C .ob) (a ↦ D .fst .hom (F .fob a) (G .fob a)) (al .fst) (be .fst) p)

def blind_nat_id (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : BlindNatTrans C D F F
  ≔ ((a ↦ D .idn (F .fob a)),
     (a b f ↦ concat (D .hom (F .fob a) (F .fob b))
        (D .comp (F .fob a) (F .fob a) (F .fob b) (F .fhom a b f) (D .idn (F .fob a)))
        (F .fhom a b f)
        (D .comp (F .fob a) (F .fob b) (F .fob b) (D .idn (F .fob b)) (F .fhom a b f))
        (D .runit (F .fob a) (F .fob b) (F .fhom a b f))
        (inverse (D .hom (F .fob a) (F .fob b))
           (D .comp (F .fob a) (F .fob b) (F .fob b) (D .idn (F .fob b)) (F .fhom a b f))
           (F .fhom a b f) (D .lunit (F .fob a) (F .fob b) (F .fhom a b f)))))

def blind_nat_comp (C D : BlindWildPrecat) (F G H : BlindWildFunctor C D)
  (be : BlindNatTrans C D G H) (al : BlindNatTrans C D F G) : BlindNatTrans C D F H
  ≔ ((a ↦ D .comp (F .fob a) (G .fob a) (H .fob a) (be .fst a) (al .fst a)),
     (a b f ↦
       let Fa ≔ F .fob a in let Fb ≔ F .fob b in let Ga ≔ G .fob a in let Gb ≔ G .fob b in
       let Ha ≔ H .fob a in let Hb ≔ H .fob b in
       let aa ≔ al .fst a in let ab ≔ al .fst b in let ba ≔ be .fst a in let bb ≔ be .fst b in
       let Ff ≔ F .fhom a b f in let Gf ≔ G .fhom a b f in let Hf ≔ H .fhom a b f in
       blind_path5 (D .hom Fa Hb)
         (D .comp Fa Ha Hb Hf (D .comp Fa Ga Ha ba aa))
         (D .comp Fa Ga Hb (D .comp Ga Ha Hb Hf ba) aa)
         (D .comp Fa Ga Hb (D .comp Ga Gb Hb bb Gf) aa)
         (D .comp Fa Gb Hb bb (D .comp Fa Ga Gb Gf aa))
         (D .comp Fa Gb Hb bb (D .comp Fa Fb Gb ab Ff))
         (D .comp Fa Fb Hb (D .comp Fb Gb Hb bb ab) Ff)
         (D .assoc Fa Ga Ha Hb aa ba Hf)
         (refl (x ↦ D .comp Fa Ga Hb x aa) (be .snd a b f))
         (inverse (D .hom Fa Hb) (D .comp Fa Gb Hb bb (D .comp Fa Ga Gb Gf aa))
            (D .comp Fa Ga Hb (D .comp Ga Gb Hb bb Gf) aa) (D .assoc Fa Ga Gb Hb aa Gf bb))
         (refl (D .comp Fa Gb Hb bb) (al .snd a b f))
         (D .assoc Fa Fb Gb Hb Ff ab bb)))

def blind_functor_precat (C : BlindWildPrecat) (D : BlindPrecat) : BlindPrecat
  ≔ let W ≔ D .fst in
    ((BlindWildFunctor C W, BlindNatTrans C W, blind_nat_id C W, blind_nat_comp C W,
      (F G al ↦ blind_nat_path C D F G (blind_nat_comp C W F G G (blind_nat_id C W G) al) al
         (a ↦ W .lunit (F .fob a) (G .fob a) (al .fst a))),
      (F G al ↦ blind_nat_path C D F G (blind_nat_comp C W F F G al (blind_nat_id C W F)) al
         (a ↦ W .runit (F .fob a) (G .fob a) (al .fst a))),
      (F G H K al be ga ↦ blind_nat_path C D F K
         (blind_nat_comp C W F H K ga (blind_nat_comp C W F G H be al))
         (blind_nat_comp C W F G K (blind_nat_comp C W G H K ga be) al)
         (a ↦ W .assoc (F .fob a) (G .fob a) (H .fob a) (K .fob a) (al .fst a) (be .fst a) (ga .fst a)))),
     (F G ↦ sigma_set ((a : C .ob) → W .hom (F .fob a) (G .fob a)) (BlindNatSquares C W F G)
        (pi_set (C .ob) (a ↦ W .hom (F .fob a) (G .fob a)) (a ↦ D .snd (F .fob a) (G .fob a)))
        (al ↦ prop_is_set (BlindNatSquares C W F G al) (blind_nat_squares_prop C D F G al))))

{` xca:funext-nat-trans. `}
def blind_xca_funext_nat_trans : Type
  ≔ (C : BlindWildPrecat) (D : BlindPrecat) (F G : BlindWildFunctor C (D .fst)) (al : BlindNatTrans C (D .fst) F G)
    → Product (BlindIsIso (blind_functor_precat C D .fst) F G al
                 → (a : C .ob) → BlindIsIso (D .fst) (F .fob a) (G .fob a) (al .fst a))
        (((a : C .ob) → BlindIsIso (D .fst) (F .fob a) (G .fob a) (al .fst a))
          → BlindIsIso (blind_functor_precat C D .fst) F G al)

{` xca:functor-cat-univalent. `}
def blind_xca_functor_cat_univalent : Type
  ≔ (C : BlindWildPrecat) (D : BlindPrecat) → BlindIsUnivalent (D .fst)
    → BlindIsUnivalent (blind_functor_precat C D .fst)

{` xca:path-core-adj. `}
def blind_xca_path_core_adj : Type
  ≔ (A : Type) (C : BlindCat)
    → BookIsEquiv (BlindWildFunctor (blind_path_wild_precat A) (C .fst .fst)) (A → C .fst .fst .ob)
        (F ↦ F .fob)

{` ex:repr-functors, for a locally U-small C, with values in the wild
   category of U-types. `}
def blind_repr_cov (U : Universe) (C : BlindWildPrecat) (s : BlindIsLocallyUSmall U C) (c : C .ob)
  : BlindWildFunctor C (blind_universe_wild_precat_in U)
  ≔ ((x ↦ (C .hom c x, s c x)), (x y f ↦ g ↦ C .comp c x y f g),
     (x ↦ funext (C .hom c x) (_ ↦ C .hom c x) (g ↦ C .comp c x x (C .idn x) g) (g ↦ g) (g ↦ C .lunit c x g)),
     (x y z f f' ↦ funext (C .hom c x) (_ ↦ C .hom c z)
        (g ↦ C .comp c x z (C .comp x y z f' f) g) (g ↦ C .comp c y z f' (C .comp c x y f g))
        (g ↦ inverse (C .hom c z) (C .comp c y z f' (C .comp c x y f g)) (C .comp c x z (C .comp x y z f' f) g)
           (C .assoc c x y z g f f'))))

def blind_repr_contra (U : Universe) (C : BlindWildPrecat) (s : BlindIsLocallyUSmall U C) (c : C .ob)
  : BlindWildFunctor (blind_op C) (blind_universe_wild_precat_in U)
  ≔ ((x ↦ (C .hom x c, s x c)), (x y f ↦ g ↦ C .comp y x c g f),
     (x ↦ funext (C .hom x c) (_ ↦ C .hom x c) (g ↦ C .comp x x c g (C .idn x)) (g ↦ g) (g ↦ C .runit x c g)),
     (x y z f f' ↦ funext (C .hom x c) (_ ↦ C .hom z c)
        (g ↦ C .comp z x c g (C .comp z y x f f')) (g ↦ C .comp z y c (C .comp y x c g f) f')
        (g ↦ C .assoc z y x c f' f g)))
