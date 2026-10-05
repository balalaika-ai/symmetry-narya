export "604-wild-pointed-types"

{` Chapter 6, xca:wildprecat-of-wildprecats. Identity and composite wild
   functors are functor_identity and functor_compose (module 602). Here:
   the identifications λ : id ∘ F = F, ρ : F ∘ id = F and
   α : H ∘ (G ∘ F) = (H ∘ G) ∘ F of wild functors, and the resulting wild
   precategory of wild precategories (its objects are WildPrecat, which
   lives in Narya's single universe like the objects Type of TypeWild).
   On objects and arrows these functors agree definitionally; only the
   functor-law components need path algebra. Then the pentagon of
   eq:pentagon (WildPentagonFiller, module 604) when the last
   category C_4 is a precategory. `}

{` ap h (p · q) · r = ap h p · (ap h q · r). `}
def ch6c_ap_concat_assoc (A B : Type) (h : A → B) (x y z : A) (w : B) (p : Id A x y) (q : Id A y z)
  (r : Id B (h z) w)
  : Id (Id B (h x) w) (concat B (h x) (h z) w (refl h (concat A x y z p q)) r)
      (concat B (h x) (h y) w (refl h p) (concat B (h y) (h z) w (refl h q) r))
  ≔ concat (Id B (h x) w) (concat B (h x) (h z) w (refl h (concat A x y z p q)) r)
      (concat B (h x) (h z) w (concat B (h x) (h y) (h z) (refl h p) (refl h q)) r)
      (concat B (h x) (h y) w (refl h p) (concat B (h y) (h z) w (refl h q) r))
      (refl ((s ↦ concat B (h x) (h z) w s r) : Id B (h x) (h z) → Id B (h x) w)
        (map_path_concat A B h x y z p q))
      (concat_assoc B (h x) (h y) (h z) w (refl h p) (refl h q) r)

{` λ : id_D ∘ F = F. `}
def functor_left_unit (C D : WildPrecat) (F : WildFunctor C D)
  : Id (WildFunctor C D) (functor_compose C D D (functor_identity D) F) F
  ≔ (obj ≔ refl (F .obj),
     mor ≔ refl (F .mor),
     map_id ≔ funext (C .ob) (a ↦ Id (D .hom (F .obj a) (F .obj a)) (F .mor a a (C .idn a)) (D .idn (F .obj a)))
       (functor_compose C D D (functor_identity D) F .map_id) (F .map_id)
       (a ↦ concat_p1 (D .hom (F .obj a) (F .obj a)) (F .mor a a (C .idn a)) (D .idn (F .obj a)) (F .map_id a)),
     map_comp ≔ funext3 (C .ob) (_ ↦ C .ob) (_ _ ↦ C .ob)
       (a b c ↦ (f : C .hom a b) (g : C .hom b c)
         → Id (D .hom (F .obj a) (F .obj c)) (F .mor a c (C .comp a b c g f))
             (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f)))
       (functor_compose C D D (functor_identity D) F .map_comp) (F .map_comp)
       (a b c ↦ funext2 (C .hom a b) (_ ↦ C .hom b c)
         (f g ↦ Id (D .hom (F .obj a) (F .obj c)) (F .mor a c (C .comp a b c g f))
           (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f)))
         (functor_compose C D D (functor_identity D) F .map_comp a b c) (F .map_comp a b c)
         (f g ↦ concat_p1 (D .hom (F .obj a) (F .obj c)) (F .mor a c (C .comp a b c g f))
           (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f)) (F .map_comp a b c f g))))

{` ρ : F ∘ id_C = F. `}
def functor_right_unit (C D : WildPrecat) (F : WildFunctor C D)
  : Id (WildFunctor C D) (functor_compose C C D F (functor_identity C)) F
  ≔ (obj ≔ refl (F .obj),
     mor ≔ refl (F .mor),
     map_id ≔ funext (C .ob) (a ↦ Id (D .hom (F .obj a) (F .obj a)) (F .mor a a (C .idn a)) (D .idn (F .obj a)))
       (functor_compose C C D F (functor_identity C) .map_id) (F .map_id)
       (a ↦ concat_1p (D .hom (F .obj a) (F .obj a)) (F .mor a a (C .idn a)) (D .idn (F .obj a)) (F .map_id a)),
     map_comp ≔ funext3 (C .ob) (_ ↦ C .ob) (_ _ ↦ C .ob)
       (a b c ↦ (f : C .hom a b) (g : C .hom b c)
         → Id (D .hom (F .obj a) (F .obj c)) (F .mor a c (C .comp a b c g f))
             (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f)))
       (functor_compose C C D F (functor_identity C) .map_comp) (F .map_comp)
       (a b c ↦ funext2 (C .hom a b) (_ ↦ C .hom b c)
         (f g ↦ Id (D .hom (F .obj a) (F .obj c)) (F .mor a c (C .comp a b c g f))
           (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f)))
         (functor_compose C C D F (functor_identity C) .map_comp a b c) (F .map_comp a b c)
         (f g ↦ concat_1p (D .hom (F .obj a) (F .obj c)) (F .mor a c (C .comp a b c g f))
           (D .comp (F .obj a) (F .obj b) (F .obj c) (F .mor b c g) (F .mor a b f)) (F .map_comp a b c f g))))

{` α : H ∘ (G ∘ F) = (H ∘ G) ∘ F. `}
def functor_assoc (C0 C1 C2 C3 : WildPrecat) (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3)
  : Id (WildFunctor C0 C3) (functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F))
      (functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F)
  ≔ let K ≔ functor_compose C0 C1 C3 (functor_compose C1 C2 C3 H G) F in
    let L ≔ functor_compose C0 C2 C3 H (functor_compose C0 C1 C2 G F) in
    let o ≔ (x ↦ H .obj (G .obj (F .obj x))) : C0 .ob → C3 .ob in
    (obj ≔ refl (K .obj),
     mor ≔ refl (K .mor),
     map_id ≔ funext (C0 .ob) (a ↦ Id (C3 .hom (o a) (o a)) (K .mor a a (C0 .idn a)) (C3 .idn (o a)))
       (L .map_id) (K .map_id)
       (a ↦ ch6c_ap_concat_assoc (C2 .hom (G .obj (F .obj a)) (G .obj (F .obj a)))
         (C3 .hom (o a) (o a)) (H .mor (G .obj (F .obj a)) (G .obj (F .obj a)))
         (G .mor (F .obj a) (F .obj a) (F .mor a a (C0 .idn a)))
         (G .mor (F .obj a) (F .obj a) (C1 .idn (F .obj a)))
         (C2 .idn (G .obj (F .obj a))) (C3 .idn (o a))
         (refl (G .mor (F .obj a) (F .obj a)) (F .map_id a)) (G .map_id (F .obj a)) (H .map_id (G .obj (F .obj a)))),
     map_comp ≔ funext3 (C0 .ob) (_ ↦ C0 .ob) (_ _ ↦ C0 .ob)
       (a b c ↦ (f : C0 .hom a b) (g : C0 .hom b c)
         → Id (C3 .hom (o a) (o c)) (K .mor a c (C0 .comp a b c g f))
             (C3 .comp (o a) (o b) (o c) (K .mor b c g) (K .mor a b f)))
       (L .map_comp) (K .map_comp)
       (a b c ↦ funext2 (C0 .hom a b) (_ ↦ C0 .hom b c)
         (f g ↦ Id (C3 .hom (o a) (o c)) (K .mor a c (C0 .comp a b c g f))
           (C3 .comp (o a) (o b) (o c) (K .mor b c g) (K .mor a b f)))
         (L .map_comp a b c) (K .map_comp a b c)
         (f g ↦
           let Fa ≔ F .obj a in let Fb ≔ F .obj b in let Fc ≔ F .obj c in
           let GFa ≔ G .obj Fa in let GFb ≔ G .obj Fb in let GFc ≔ G .obj Fc in
           ch6c_ap_concat_assoc (C2 .hom GFa GFc) (C3 .hom (o a) (o c)) (H .mor GFa GFc)
             (G .mor Fa Fc (F .mor a c (C0 .comp a b c g f)))
             (G .mor Fa Fc (C1 .comp Fa Fb Fc (F .mor b c g) (F .mor a b f)))
             (C2 .comp GFa GFb GFc (G .mor Fb Fc (F .mor b c g)) (G .mor Fa Fb (F .mor a b f)))
             (C3 .comp (o a) (o b) (o c) (K .mor b c g) (K .mor a b f))
             (refl (G .mor Fa Fc) (F .map_comp a b c f g))
             (G .map_comp Fa Fb Fc (F .mor a b f) (F .mor b c g))
             (H .map_comp GFa GFb GFc (G .mor Fa Fb (F .mor a b f)) (G .mor Fb Fc (F .mor b c g))))))

{` xca:wildprecat-of-wildprecats: the wild precategory of (small) wild
   precategories. `}
def WildPrecatWild : WildPrecat
  ≔ (ob ≔ WildPrecat,
     hom ≔ C D ↦ WildFunctor C D,
     idn ≔ C ↦ functor_identity C,
     comp ≔ C D E G F ↦ functor_compose C D E G F,
     lu ≔ C D F ↦ functor_left_unit C D F,
     ru ≔ C D F ↦ functor_right_unit C D F,
     assoc ≔ C0 C1 C2 C3 F G H ↦ functor_assoc C0 C1 C2 C3 F G H)

{` If C_4 has hom-sets, the pentagon in the wild precategory of wild
   precategories holds: functors into C_4 are determined by their actions
   on objects and arrows (functor_path_equiv), and all five
   identifications are reflexivities there. `}
def functor_data_path_refl_concat (C D : WildPrecat) (X : FunctorData C D) (p q : Id (FunctorData C D) X X)
  (hp : Id (Id (FunctorData C D) X X) p (refl X)) (hq : Id (Id (FunctorData C D) X X) q (refl X))
  : Id (Id (FunctorData C D) X X) (concat (FunctorData C D) X X X p q) (refl X)
  ≔ concat (Id (FunctorData C D) X X) (concat (FunctorData C D) X X X p q)
      (concat (FunctorData C D) X X X (refl X) q) (refl X)
      (refl ((s ↦ concat (FunctorData C D) X X X s q) : Id (FunctorData C D) X X → Id (FunctorData C D) X X) hp)
      (concat (Id (FunctorData C D) X X) (concat (FunctorData C D) X X X (refl X) q) q (refl X)
        (concat_1p (FunctorData C D) X X q) hq)

def wild_precat_pentagon_precategory (C0 C1 C2 C3 C4 : WildPrecat) (hs : HasHomSets C4)
  (F : WildFunctor C0 C1) (G : WildFunctor C1 C2) (H : WildFunctor C2 C3) (K : WildFunctor C3 C4)
  : WildPentagonFiller WildPrecatWild C0 C1 C2 C3 C4 F G H K
  ≔ let W ≔ WildPrecatWild in
    let FD ≔ FunctorData C0 C4 in
    let fd ≔ functor_data C0 C4 in
    let hg ≔ W .comp C1 C2 C3 H G in
    let gf ≔ W .comp C0 C1 C2 G F in
    let kh ≔ W .comp C2 C3 C4 K H in
    let P0 ≔ W .comp C0 C3 C4 K (W .comp C0 C2 C3 H gf) in
    let P1 ≔ W .comp C0 C3 C4 K (W .comp C0 C1 C3 hg F) in
    let P2 ≔ W .comp C0 C1 C4 (W .comp C1 C3 C4 K hg) F in
    let P3 ≔ W .comp C0 C1 C4 (W .comp C1 C2 C4 kh G) F in
    let P4 ≔ W .comp C0 C2 C4 kh gf in
    let a1 ≔ cat_whisker_left W C0 C3 C4 K (W .comp C0 C2 C3 H gf) (W .comp C0 C1 C3 hg F) (W .assoc C0 C1 C2 C3 F G H) in
    let a2 ≔ W .assoc C0 C1 C3 C4 F hg K in
    let a3 ≔ cat_whisker_right W C0 C1 C4 (W .comp C1 C3 C4 K hg) (W .comp C1 C2 C4 kh G) F (W .assoc C1 C2 C3 C4 G H K) in
    let a4 ≔ W .assoc C0 C2 C3 C4 gf H K in
    let a5 ≔ W .assoc C0 C1 C2 C4 F G kh in
    let X ≔ fd P0 in
    let e ≔ functor_path_equiv C0 C4 hs P0 P3 in
    let lhs ≔ concat (WildFunctor C0 C4) P0 P1 P3 a1 (concat (WildFunctor C0 C4) P1 P2 P3 a2 a3) in
    let rhs ≔ concat (WildFunctor C0 C4) P0 P4 P3 a4 a5 in
    equivalence_injective (Id (WildFunctor C0 C4) P0 P3) (Id FD X X) e lhs rhs
      (concat (Id FD X X) (e .map lhs) (refl X) (e .map rhs)
        (concat (Id FD X X) (e .map lhs)
          (concat FD X X X (refl fd a1) (concat FD X X X (refl fd a2) (refl fd a3))) (refl X)
          (concat (Id FD X X) (e .map lhs)
            (concat FD X X X (refl fd a1) (refl fd (concat (WildFunctor C0 C4) P1 P2 P3 a2 a3)))
            (concat FD X X X (refl fd a1) (concat FD X X X (refl fd a2) (refl fd a3)))
            (map_path_concat (WildFunctor C0 C4) FD fd P0 P1 P3 a1 (concat (WildFunctor C0 C4) P1 P2 P3 a2 a3))
            (refl ((s ↦ concat FD X X X (refl fd a1) s) : Id FD X X → Id FD X X)
              (map_path_concat (WildFunctor C0 C4) FD fd P1 P2 P3 a2 a3)))
          (functor_data_path_refl_concat C0 C4 X (refl fd a1) (concat FD X X X (refl fd a2) (refl fd a3))
            (refl (refl X))
            (functor_data_path_refl_concat C0 C4 X (refl fd a2) (refl fd a3) (refl (refl X)) (refl (refl X)))))
        (inverse (Id FD X X) (e .map rhs) (refl X)
          (concat (Id FD X X) (e .map rhs) (concat FD X X X (refl fd a4) (refl fd a5)) (refl X)
            (map_path_concat (WildFunctor C0 C4) FD fd P0 P4 P3 a4 a5)
            (functor_data_path_refl_concat C0 C4 X (refl fd a4) (refl fd a5) (refl (refl X)) (refl (refl X))))))

{` Litmus: in the wild precategory of wild precategories, composing the
   identity functor of the wild category of types with itself acts on
   objects as the identity. `}
def wild_precat_wild_identity_composite (A : Type)
  : Id Type (WildPrecatWild .comp TypeWild TypeWild TypeWild (functor_identity TypeWild) (functor_identity TypeWild) .obj A) A
  ≔ refl A
