export "bridge-04-phi-functors"
export "05-homs"
export "../../../src/744-concr-equivalence-of-categories"
export "../../../src/641-ff-split-eso-equivalences"

{` Bridges for absgroup.tex, sec "Homomorphisms, from abstract to
   concrete and back" (blind file 05-homs), except xca:SG2=SG2-contractible
   (bridge-05b-sg2).

   The blind concr on morphisms is, for any choice d of the data of
   xca:phi_!-OK and xca:Bconcr-OK (1), the map bridge_gen_hom (restriction
   of a map of groupoids F to components, pointed by a path k : F a = b) for
   F = blind φ_!, a, b = the blind principal torsors and k = the path of the
   data. Ours (concr_hom) is bridge_gen_hom for F = agset_induce, our
   principal torsors and induce_principal_path. Three generic facts relate
   them: changing F along a homotopy (bridge_gen_hom_vary), moving the points
   along paths (bridge_gen_adj, with the functor laws and the equivalence on
   arrows preserved by path induction), and the identification of the two
   pointing paths of P_H, which is checked on classes [t, s] (paths of
   G-sets are determined by their transport). `}

{` lem:homomabstrconcr. `}
def bridge_lem_homomabstrconcr : blind_lem_homomabstrconcr ≔ G H ↦ abstr_hom_is_equiv G H

{` The blind wild category of abstract groups has our hom-sets,
   identities and composition. `}
def bridge_def_abs_group_wild_hom (G H : BlindAbsGroup)
  : Id Type (BlindAbsGroupWild .hom G H) (AbstractGroupWild .hom (bridge_ag7 G) (bridge_ag7 H))
  ≔ refl (AbstractHom (bridge_ag7 G) (bridge_ag7 H))

def bridge_def_abs_group_wild_comp (G H K : BlindAbsGroup) (g : BlindAbsHom H K) (f : BlindAbsHom G H)
  : Id (AbstractHom (bridge_ag7 G) (bridge_ag7 K)) (BlindAbsGroupWild .comp G H K g f)
      (AbstractGroupWild .comp (bridge_ag7 G) (bridge_ag7 H) (bridge_ag7 K) g f)
  ≔ refl (abstract_hom_compose (bridge_ag7 G) (bridge_ag7 H) (bridge_ag7 K) f g)

{` Generic path lemmas. `}
def bridge_J_to (A : Type) (a : A) (P : (x : A) → Id A x a → Type) (base : P a (refl a)) (x : A) (p : Id A x a)
  : P x p
  ≔ let base' : P a (inverse A a a (refl a))
      ≔ transport (Id A a a) (P a) (refl a) (inverse A a a (refl a))
          (inverse (Id A a a) (inverse A a a (refl a)) (refl a) (inverse_refl A a)) base in
    let r : P x (inverse A a x (inverse A x a p))
      ≔ J A a (y q ↦ P y (inverse A a y q)) base' x (inverse A x a p) in
    transport (Id A x a) (P x) (inverse A a x (inverse A x a p)) p (inverse_inverse A x a p) r

def bridge_transport_inv_cancel (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (b : B x)
  : Id (B x) (transport A B y x (inverse A x y p) (transport A B x y p b)) b
  ≔ J A x (y p ↦ (b : B x) → Id (B x) (transport A B y x (inverse A x y p) (transport A B x y p b)) b)
      (b ↦ concat (B x) (transport A B x x (inverse A x x (refl x)) (transport A B x x (refl x) b))
        (transport A B x x (refl x) (transport A B x x (refl x) b)) b
        (refl ((q ↦ transport A B x x q (transport A B x x (refl x) b)) : Id A x x → B x) (inverse_refl A x))
        (concat (B x) (transport A B x x (refl x) (transport A B x x (refl x) b)) (transport A B x x (refl x) b) b
          (transport_refl A B x (transport A B x x (refl x) b)) (transport_refl A B x b)))
      y p b

{` A transport fixing every point is fixed by the inverse transport. `}
def bridge_transport_inv_fixed (A : Type) (B : A → Type) (x : A) (p : Id A x x)
  (h : (b : B x) → Id (B x) (transport A B x x p b) b) (b : B x)
  : Id (B x) (transport A B x x (inverse A x x p) b) b
  ≔ concat (B x) (transport A B x x (inverse A x x p) b) (transport A B x x (inverse A x x p) (transport A B x x p b)) b
      (refl (transport A B x x (inverse A x x p)) (inverse (B x) (transport A B x x p b) b (h b)))
      (bridge_transport_inv_cancel A B x x p b)

{` Paths of G-sets are determined by their transport. `}
def bridge_agset_path_ext (K : AbstractGroup) (X Y : AbstractGSet K) (p q : Id (AbstractGSet K) X Y)
  (h : (x : agset_carrier K X) → Id (agset_carrier K Y)
     (transport (AbstractGSet K) (agset_carrier K) X Y p x) (transport (AbstractGSet K) (agset_carrier K) X Y q x))
  : Id (Id (AbstractGSet K) X Y) p q
  ≔ equivalence_injective (Id (AbstractGSet K) X Y) (AbstractGSetIso K X Y) (agset_path_iso_equiv K X Y) p q
      (agset_iso_path K X Y (agset_path_to_iso K X Y p) (agset_path_to_iso K X Y q) h)

{` The restriction of F : A → B to components, pointed by k : F a = b. `}
def bridge_gen_torsor (A B : Type) (F : A → B) (a : A) (b : B) (k : Id B (F a) b) (x : NativeComponent A a)
  : NativeComponent B b
  ≔ (F (x .fst),
     mere_rec (Id A a (x .fst)) (Mere (Id B b (F (x .fst)))) (mere_isprop (Id B b (F (x .fst))))
       (p ↦ mere (Id B b (F (x .fst))) (concat B b (F a) (F (x .fst)) (inverse B (F a) b k) (map_path A B F a (x .fst) p)))
       (x .snd))

def bridge_gen_hom (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (F : A → B) (a : A) (b : B) (k : Id B (F a) b)
  : GroupHom (automorphism_group A hA a) (automorphism_group B hB b)
  ≔ mkhom (automorphism_group A hA a) (automorphism_group B hB b)
      (bridge_gen_torsor A B F a b k,
       component_path B b (component_point B b) (bridge_gen_torsor A B F a b k (component_point A a))
         (inverse B (F a) b k))

{` Moving the points: k : F a = b becomes F a' = b' along π : a' = a and
   σ : b' = b. `}
def bridge_gen_adj (A B : Type) (F : A → B) (a a' : A) (b b' : B) (π : Id A a' a) (σ : Id B b' b) (k : Id B (F a) b)
  : Id B (F a') b'
  ≔ concat B (F a') (F a) b' (map_path A B F a' a π) (concat B (F a) b b' k (inverse B b' b σ))

def bridge_gen_adj_refl (A B : Type) (F : A → B) (a : A) (b : B) (k : Id B (F a) b)
  : Id (Id B (F a) b) (bridge_gen_adj A B F a a b b (refl a) (refl b) k) k
  ≔ calc
      bridge_gen_adj A B F a a b b (refl a) (refl b) k = concat B (F a) b b k (inverse B b b (refl b))
        by concat_1p B (F a) b (concat B (F a) b b k (inverse B b b (refl b)))
      = concat B (F a) b b k (refl b) by refl (concat B (F a) b b k) (inverse_refl B b)
      = k by concat_p1 B (F a) b k ∎

{` Functor laws and equivalence on arrows survive moving the points. `}
def bridge_gen_id (A : Type) (hA : isGroupoid A) (F : A → A) (a : A) (k : Id A (F a) a)
  (h0 : Id (GroupHom (automorphism_group A hA a) (automorphism_group A hA a))
    (bridge_gen_hom A A hA hA F a a k) (group_hom_id (automorphism_group A hA a)))
  (a' : A) (π : Id A a' a)
  : Id (GroupHom (automorphism_group A hA a') (automorphism_group A hA a'))
      (bridge_gen_hom A A hA hA F a' a' (bridge_gen_adj A A F a a' a a' π π k)) (group_hom_id (automorphism_group A hA a'))
  ≔ bridge_J_to A a (x p ↦ Id (GroupHom (automorphism_group A hA x) (automorphism_group A hA x))
        (bridge_gen_hom A A hA hA F x x (bridge_gen_adj A A F a x a x p p k)) (group_hom_id (automorphism_group A hA x)))
      (concat (GroupHom (automorphism_group A hA a) (automorphism_group A hA a))
        (bridge_gen_hom A A hA hA F a a (bridge_gen_adj A A F a a a a (refl a) (refl a) k))
        (bridge_gen_hom A A hA hA F a a k) (group_hom_id (automorphism_group A hA a))
        (refl (bridge_gen_hom A A hA hA F a a) (bridge_gen_adj_refl A A F a a k)) h0)
      a' π

def bridge_gen_comp (A1 A2 A3 : Type) (h1 : isGroupoid A1) (h2 : isGroupoid A2) (h3 : isGroupoid A3)
  (F1 : A1 → A2) (F2 : A2 → A3) (F3 : A1 → A3) (a1 : A1) (a2 : A2) (a3 : A3)
  (k1 : Id A2 (F1 a1) a2) (k2 : Id A3 (F2 a2) a3) (k3 : Id A3 (F3 a1) a3)
  (h0 : Id (GroupHom (automorphism_group A1 h1 a1) (automorphism_group A3 h3 a3))
    (bridge_gen_hom A1 A3 h1 h3 F3 a1 a3 k3)
    (group_hom_compose (automorphism_group A1 h1 a1) (automorphism_group A2 h2 a2) (automorphism_group A3 h3 a3)
      (bridge_gen_hom A1 A2 h1 h2 F1 a1 a2 k1) (bridge_gen_hom A2 A3 h2 h3 F2 a2 a3 k2)))
  (a1' : A1) (p1 : Id A1 a1' a1) (a2' : A2) (p2 : Id A2 a2' a2) (a3' : A3) (p3 : Id A3 a3' a3)
  : Id (GroupHom (automorphism_group A1 h1 a1') (automorphism_group A3 h3 a3'))
      (bridge_gen_hom A1 A3 h1 h3 F3 a1' a3' (bridge_gen_adj A1 A3 F3 a1 a1' a3 a3' p1 p3 k3))
      (group_hom_compose (automorphism_group A1 h1 a1') (automorphism_group A2 h2 a2') (automorphism_group A3 h3 a3')
        (bridge_gen_hom A1 A2 h1 h2 F1 a1' a2' (bridge_gen_adj A1 A2 F1 a1 a1' a2 a2' p1 p2 k1))
        (bridge_gen_hom A2 A3 h2 h3 F2 a2' a3' (bridge_gen_adj A2 A3 F2 a2 a2' a3 a3' p2 p3 k2)))
  ≔ let S : (x1 : A1) → Id A1 x1 a1 → (x2 : A2) → Id A2 x2 a2 → (x3 : A3) → Id A3 x3 a3 → Type
      ≔ x1 q1 x2 q2 x3 q3 ↦
        Id (GroupHom (automorphism_group A1 h1 x1) (automorphism_group A3 h3 x3))
          (bridge_gen_hom A1 A3 h1 h3 F3 x1 x3 (bridge_gen_adj A1 A3 F3 a1 x1 a3 x3 q1 q3 k3))
          (group_hom_compose (automorphism_group A1 h1 x1) (automorphism_group A2 h2 x2) (automorphism_group A3 h3 x3)
            (bridge_gen_hom A1 A2 h1 h2 F1 x1 x2 (bridge_gen_adj A1 A2 F1 a1 x1 a2 x2 q1 q2 k1))
            (bridge_gen_hom A2 A3 h2 h3 F2 x2 x3 (bridge_gen_adj A2 A3 F2 a2 x2 a3 x3 q2 q3 k2))) in
    let G1 ≔ automorphism_group A1 h1 a1 in let G2 ≔ automorphism_group A2 h2 a2 in let G3 ≔ automorphism_group A3 h3 a3 in
    let base : S a1 (refl a1) a2 (refl a2) a3 (refl a3)
      ≔ concat (GroupHom G1 G3)
          (bridge_gen_hom A1 A3 h1 h3 F3 a1 a3 (bridge_gen_adj A1 A3 F3 a1 a1 a3 a3 (refl a1) (refl a3) k3))
          (bridge_gen_hom A1 A3 h1 h3 F3 a1 a3 k3)
          (group_hom_compose G1 G2 G3
            (bridge_gen_hom A1 A2 h1 h2 F1 a1 a2 (bridge_gen_adj A1 A2 F1 a1 a1 a2 a2 (refl a1) (refl a2) k1))
            (bridge_gen_hom A2 A3 h2 h3 F2 a2 a3 (bridge_gen_adj A2 A3 F2 a2 a2 a3 a3 (refl a2) (refl a3) k2)))
          (refl (bridge_gen_hom A1 A3 h1 h3 F3 a1 a3) (bridge_gen_adj_refl A1 A3 F3 a1 a3 k3))
          (concat (GroupHom G1 G3) (bridge_gen_hom A1 A3 h1 h3 F3 a1 a3 k3)
            (group_hom_compose G1 G2 G3 (bridge_gen_hom A1 A2 h1 h2 F1 a1 a2 k1) (bridge_gen_hom A2 A3 h2 h3 F2 a2 a3 k2))
            (group_hom_compose G1 G2 G3
              (bridge_gen_hom A1 A2 h1 h2 F1 a1 a2 (bridge_gen_adj A1 A2 F1 a1 a1 a2 a2 (refl a1) (refl a2) k1))
              (bridge_gen_hom A2 A3 h2 h3 F2 a2 a3 (bridge_gen_adj A2 A3 F2 a2 a2 a3 a3 (refl a2) (refl a3) k2)))
            h0
            (refl ((u v ↦ group_hom_compose G1 G2 G3 (bridge_gen_hom A1 A2 h1 h2 F1 a1 a2 u) (bridge_gen_hom A2 A3 h2 h3 F2 a2 a3 v))
                    : Id A2 (F1 a1) a2 → Id A3 (F2 a2) a3 → GroupHom G1 G3)
              (inverse (Id A2 (F1 a1) a2) (bridge_gen_adj A1 A2 F1 a1 a1 a2 a2 (refl a1) (refl a2) k1) k1
                (bridge_gen_adj_refl A1 A2 F1 a1 a2 k1))
              (inverse (Id A3 (F2 a2) a3) (bridge_gen_adj A2 A3 F2 a2 a2 a3 a3 (refl a2) (refl a3) k2) k2
                (bridge_gen_adj_refl A2 A3 F2 a2 a3 k2)))) in
    bridge_J_to A1 a1 (x1 q1 ↦ (x2 : A2) (q2 : Id A2 x2 a2) (x3 : A3) (q3 : Id A3 x3 a3) → S x1 q1 x2 q2 x3 q3)
      (x2 q2 ↦ bridge_J_to A2 a2 (x2 q2 ↦ (x3 : A3) (q3 : Id A3 x3 a3) → S a1 (refl a1) x2 q2 x3 q3)
        (x3 q3 ↦ bridge_J_to A3 a3 (x3 q3 ↦ S a1 (refl a1) a2 (refl a2) x3 q3) base x3 q3) x2 q2)
      a1' p1 a2' p2 a3' p3

def bridge_gen_equiv (M A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (F : M → A → B) (a : A) (b : B)
  (k : (m : M) → Id B (F m a) b)
  (h0 : BookIsEquiv M (GroupHom (automorphism_group A hA a) (automorphism_group B hB b))
    (m ↦ bridge_gen_hom A B hA hB (F m) a b (k m)))
  (a' : A) (π : Id A a' a) (b' : B) (σ : Id B b' b)
  : BookIsEquiv M (GroupHom (automorphism_group A hA a') (automorphism_group B hB b'))
      (m ↦ bridge_gen_hom A B hA hB (F m) a' b' (bridge_gen_adj A B (F m) a a' b b' π σ (k m)))
  ≔ let S : (x : A) → Id A x a → (y : B) → Id B y b → Type
      ≔ x p y q ↦ BookIsEquiv M (GroupHom (automorphism_group A hA x) (automorphism_group B hB y))
          (m ↦ bridge_gen_hom A B hA hB (F m) x y (bridge_gen_adj A B (F m) a x b y p q (k m))) in
    let base : S a (refl a) b (refl b)
      ≔ bridge_book_equiv_homotopic M (GroupHom (automorphism_group A hA a) (automorphism_group B hB b))
          (m ↦ bridge_gen_hom A B hA hB (F m) a b (k m), h0)
          (m ↦ bridge_gen_hom A B hA hB (F m) a b (bridge_gen_adj A B (F m) a a b b (refl a) (refl b) (k m)))
          (m ↦ refl (bridge_gen_hom A B hA hB (F m) a b)
            (inverse (Id B (F m a) b) (bridge_gen_adj A B (F m) a a b b (refl a) (refl b) (k m)) (k m)
              (bridge_gen_adj_refl A B (F m) a b (k m)))) in
    bridge_J_to A a (x p ↦ (y : B) (q : Id B y b) → S x p y q)
      (y q ↦ bridge_J_to B b (y q ↦ S a (refl a) y q) base y q) a' π b' σ

{` Changing F along a homotopy h (with k adjusted). `}
def bridge_concat_inv_refl (B : Type) (x y : B) (k : Id B x y)
  : Id (Id B x y) (concat B x x y (inverse B x x (refl x)) k) k
  ≔ concat (Id B x y) (concat B x x y (inverse B x x (refl x)) k) (concat B x x y (refl x) k) k
      (refl ((q ↦ concat B x x y q k) : Id B x x → Id B x y) (inverse_refl B x)) (concat_1p B x y k)

def bridge_gen_vary (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (F F' : A → B) (h : (x : A) → Id B (F x) (F' x))
  (a : A) (b : B) (k : Id B (F a) b) (k' : Id B (F' a) b)
  (e : Id (Id B (F' a) b) (concat B (F' a) (F a) b (inverse B (F a) (F' a) (h a)) k) k')
  : Id (GroupHom (automorphism_group A hA a) (automorphism_group B hB b))
      (bridge_gen_hom A B hA hB F a b k) (bridge_gen_hom A B hA hB F' a b k')
  ≔ let T : (F'' : A → B) → Id (A → B) F F'' → Type
      ≔ F'' E ↦ (k'' : Id B (F'' a) b)
        → Id (Id B (F'' a) b) (concat B (F'' a) (F a) b (inverse B (F a) (F'' a) (E (refl a))) k) k''
        → Id (GroupHom (automorphism_group A hA a) (automorphism_group B hB b))
            (bridge_gen_hom A B hA hB F a b k) (bridge_gen_hom A B hA hB F'' a b k'') in
    let base : T F (refl F)
      ≔ k'' e'' ↦ refl (bridge_gen_hom A B hA hB F a b)
          (concat (Id B (F a) b) k (concat B (F a) (F a) b (inverse B (F a) (F a) (refl (F a))) k) k''
            (inverse (Id B (F a) b) (concat B (F a) (F a) b (inverse B (F a) (F a) (refl (F a))) k) k
              (bridge_concat_inv_refl B (F a) b k))
            e'') in
    let E ≔ funext A (_ ↦ B) F F' h in
    J (A → B) F T base F' E k'
      (concat (Id B (F' a) b) (concat B (F' a) (F a) b (inverse B (F a) (F' a) (E (refl a))) k)
        (concat B (F' a) (F a) b (inverse B (F a) (F' a) (h a)) k) k'
        (refl ((q ↦ concat B (F' a) (F a) b (inverse B (F a) (F' a) q) k) : Id B (F a) (F' a) → Id B (F' a) b)
          (inverse (Id B (F a) (F' a)) (h a) (E (refl a)) (funext_beta A (_ ↦ B) F F' h a)))
        e)

{` Our concr(G) and the automorphism group of P_G in AbstractGSet G with
   another groupoid witness have the same classifying pointed type, so
   homomorphisms are rewrapped without change (record types are nominal in
   their parameters, so this is an explicit map with refl round trips). `}
def bridge_wrap (G H : AbstractGroup) (hG : isGroupoid (AbstractGSet G)) (hH : isGroupoid (AbstractGSet H))
  (f : GroupHom (concr G) (concr H))
  : GroupHom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group (AbstractGSet H) hH (agset_principal H))
  ≔ mkhom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group (AbstractGSet H) hH (agset_principal H))
      (hom_B (concr G) (concr H) f)

def bridge_unwrap (G H : AbstractGroup) (hG : isGroupoid (AbstractGSet G)) (hH : isGroupoid (AbstractGSet H))
  (f : GroupHom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group (AbstractGSet H) hH (agset_principal H)))
  : GroupHom (concr G) (concr H)
  ≔ mkhom (concr G) (concr H)
      (hom_B (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group (AbstractGSet H) hH (agset_principal H)) f)

def bridge_wrap_equiv (G H : AbstractGroup) (hG : isGroupoid (AbstractGSet G)) (hH : isGroupoid (AbstractGSet H))
  : Equiv (GroupHom (concr G) (concr H))
      (GroupHom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group (AbstractGSet H) hH (agset_principal H)))
  ≔ quasi_inverse_equiv (GroupHom (concr G) (concr H))
      (GroupHom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group (AbstractGSet H) hH (agset_principal H)))
      (bridge_wrap G H hG hH) (bridge_unwrap G H hG hH) (f ↦ refl f) (f ↦ refl f)

{` Our concr_hom (rewrapped) is bridge_gen_hom (the pointing paths have the
   same first component). `}
def bridge_ours_gen (G H : AbstractGroup) (φ : AbstractHom G H) (hG : isGroupoid (AbstractGSet G)) (hH : isGroupoid (AbstractGSet H))
  : Id (GroupHom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group (AbstractGSet H) hH (agset_principal H)))
      (bridge_wrap G H hG hH (concr_hom G H φ))
      (bridge_gen_hom (AbstractGSet G) (AbstractGSet H) hG hH (agset_induce G H φ) (agset_principal G) (agset_principal H)
        (induce_principal_path G H φ))
  ≔ let A ≔ AbstractGSet H in let PH ≔ agset_principal H in
    let f ≔ concr_hom_torsor G H φ in
    let u ≔ component_point A PH in let v ≔ f (abstract_principal_torsor G) in
    let k0 ≔ inverse A (agset_induce G H φ (agset_principal G)) PH (induce_principal_path G H φ) in
    refl ((q ↦ mkhom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group A hH PH) (f, q))
          : Id (NativeComponent A PH) u v
            → GroupHom (automorphism_group (AbstractGSet G) hG (agset_principal G)) (automorphism_group A hH PH))
      (equivalence_injective (Id (NativeComponent A PH) u v) (Id A PH (v .fst)) (component_path_equiv A PH u v)
        (concr_hom_point G H φ) (component_path A PH u v k0)
        (inverse (Id A PH (v .fst)) (component_path_equiv A PH u v .map (component_path A PH u v k0)) k0
          (equiv_counit (Id (NativeComponent A PH) u v) (Id A PH (v .fst)) (component_path_equiv A PH u v) k0)))

{` Transport of classes along ap φ_! (path induction). `}
def bridge_induce_class_transport (G H : AbstractGroup) (φ : AbstractHom G H) (X Y : AbstractGSet G) (p : Id (AbstractGSet G) X Y)
  (t : H .carrier) (x : agset_carrier G X)
  : Id (AgsetInduceCarrier G H φ Y)
      (transport (AbstractGSet G) (Z ↦ AgsetInduceCarrier G H φ Z) X Y p (agset_induce_class G H φ X t x))
      (agset_induce_class G H φ Y t (transport (AbstractGSet G) (agset_carrier G) X Y p x))
  ≔ J (AbstractGSet G) X
      (Y p ↦ Id (AgsetInduceCarrier G H φ Y)
        (transport (AbstractGSet G) (Z ↦ AgsetInduceCarrier G H φ Z) X Y p (agset_induce_class G H φ X t x))
        (agset_induce_class G H φ Y t (transport (AbstractGSet G) (agset_carrier G) X Y p x)))
      (concat (AgsetInduceCarrier G H φ X)
        (transport (AbstractGSet G) (Z ↦ AgsetInduceCarrier G H φ Z) X X (refl X) (agset_induce_class G H φ X t x))
        (agset_induce_class G H φ X t x)
        (agset_induce_class G H φ X t (transport (AbstractGSet G) (agset_carrier G) X X (refl X) x))
        (transport_refl (AbstractGSet G) (Z ↦ AgsetInduceCarrier G H φ Z) X (agset_induce_class G H φ X t x))
        (refl (agset_induce_class G H φ X t)
          (inverse (agset_carrier G X) (transport (AbstractGSet G) (agset_carrier G) X X (refl X) x) x
            (transport_refl (AbstractGSet G) (agset_carrier G) X x))))
      Y p

{` Transport along the path from the blind to our principal torsor is the
   identity on elements (its carrier component is refl). `}
def bridge_principal_carrier (G : BlindAbsGroup) (s : G .carrier)
  : Id (G .carrier)
      (transport (AbstractGSet (bridge_ag7 G)) (agset_carrier (bridge_ag7 G)) (blind_abs_principal G) (agset_principal (bridge_ag7 G))
        (bridge_principal_path G) s) s
  ≔ transport_refl Type (Y ↦ Y) (G .carrier) s

def bridge_principal_carrier_inv (G : BlindAbsGroup) (s : G .carrier)
  : Id (G .carrier)
      (transport (AbstractGSet (bridge_ag7 G)) (agset_carrier (bridge_ag7 G)) (agset_principal (bridge_ag7 G)) (blind_abs_principal G)
        (inverse (AbstractGSet (bridge_ag7 G)) (blind_abs_principal G) (agset_principal (bridge_ag7 G)) (bridge_principal_path G)) s) s
  ≔ let A ≔ AbstractGSet (bridge_ag7 G) in let C ≔ agset_carrier (bridge_ag7 G) in
    let Pb ≔ blind_abs_principal G in let P ≔ agset_principal (bridge_ag7 G) in let π ≔ bridge_principal_path G in
    concat (G .carrier) (transport A C P Pb (inverse A Pb P π) s) (transport A C P Pb (inverse A Pb P π) (transport A C Pb P π s)) s
      (refl (transport A C P Pb (inverse A Pb P π)) (inverse (G .carrier) (transport A C Pb P π s) s (bridge_principal_carrier G s)))
      (bridge_transport_inv_cancel A C Pb P π s)

{` The moved pointing path of ours, F_o(Pb_G) = Pb_H, and its action on
   classes: [t, s] ↦ t φ(s). `}
def bridge_adj_ipp (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  : Id (AbstractGSet (bridge_ag7 H)) (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi (blind_abs_principal G)) (blind_abs_principal H)
  ≔ bridge_gen_adj (AbstractGSet (bridge_ag7 G)) (AbstractGSet (bridge_ag7 H)) (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi)
      (agset_principal (bridge_ag7 G)) (blind_abs_principal G) (agset_principal (bridge_ag7 H)) (blind_abs_principal H)
      (bridge_principal_path G) (bridge_principal_path H) (induce_principal_path (bridge_ag7 G) (bridge_ag7 H) phi)

def bridge_adj_ipp_class (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (t : H .carrier) (s : G .carrier)
  : Id (H .carrier)
      (transport (AbstractGSet (bridge_ag7 H)) (agset_carrier (bridge_ag7 H))
        (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi (blind_abs_principal G)) (blind_abs_principal H)
        (bridge_adj_ipp G H phi) (agset_induce_class (bridge_ag7 G) (bridge_ag7 H) phi (blind_abs_principal G) t s))
      (H .mul t (phi .fst s))
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let AG ≔ AbstractGSet G' in let AH ≔ AbstractGSet H' in let C ≔ agset_carrier H' in
    let F ≔ agset_induce G' H' phi in
    let PbG ≔ blind_abs_principal G in let PG ≔ agset_principal G' in
    let PbH ≔ blind_abs_principal H in let PH ≔ agset_principal H' in
    let πG ≔ bridge_principal_path G in let πH ≔ bridge_principal_path H in
    let ipp ≔ induce_principal_path G' H' phi in
    let c0 ≔ agset_induce_class G' H' phi PbG t s in
    let tr ≔ transport AH C in
    let y1 ≔ tr (F PbG) (F PG) (refl F πG) c0 in
    calc
      tr (F PbG) PbH (bridge_adj_ipp G H phi) c0
      = tr (F PG) PbH (concat AH (F PG) PH PbH ipp (inverse AH PbH PH πH)) y1
        by transport_concat AH C (F PbG) (F PG) PbH (refl F πG) (concat AH (F PG) PH PbH ipp (inverse AH PbH PH πH)) c0
      = tr PH PbH (inverse AH PbH PH πH) (tr (F PG) PH ipp y1)
        by transport_concat AH C (F PG) PH PbH ipp (inverse AH PbH PH πH) y1
      = tr (F PG) PH ipp y1 by bridge_principal_carrier_inv H (tr (F PG) PH ipp y1)
      = tr (F PG) PH ipp (agset_induce_class G' H' phi PG t (transport AG (agset_carrier G') PbG PG πG s))
        by refl (tr (F PG) PH ipp) (bridge_induce_class_transport G' H' phi PbG PG πG t s)
      = tr (F PG) PH ipp (agset_induce_class G' H' phi PG t s)
        by refl ((z ↦ tr (F PG) PH ipp (agset_induce_class G' H' phi PG t z)) : G .carrier → H .carrier)
             (bridge_principal_carrier G s)
      = H .mul t (phi .fst s)
        by induce_principal_transport G' H' phi (agset_induce_class G' H' phi PG t s) ∎

{` xca:Bconcr-OK (1), for every choice of the data of xca:phi_!-OK. `}
def bridge_xca_bconcr_ok1 : blind_xca_bconcr_ok1
  ≔ G H phi okS ↦
    let H' ≔ bridge_ag7 H in let AH ≔ AbstractGSet H' in let C ≔ agset_carrier H' in
    let PbG ≔ blind_abs_principal G in let PbH ≔ blind_abs_principal H in
    let Fb ≔ blind_phi_shriek G H phi okS in let Fo ≔ agset_induce (bridge_ag7 G) H' phi in
    let hp ≔ bridge_phi_shriek_path G H phi okS PbG in
    (concat AH (Fb PbG) (Fo PbG) PbH hp (bridge_adj_ipp G H phi),
     t s ↦ concat (H .carrier)
       (transport AH C (Fb PbG) PbH (concat AH (Fb PbG) (Fo PbG) PbH hp (bridge_adj_ipp G H phi))
         (blind_phi_class G H phi PbG (okS PbG) t s))
       (transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi)
         (transport AH C (Fb PbG) (Fo PbG) hp (blind_phi_class G H phi PbG (okS PbG) t s)))
       (H .mul t (phi .fst s))
       (transport_concat AH C (Fb PbG) (Fo PbG) PbH hp (bridge_adj_ipp G H phi) (blind_phi_class G H phi PbG (okS PbG) t s))
       (concat (H .carrier)
         (transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi)
           (transport AH C (Fb PbG) (Fo PbG) hp (blind_phi_class G H phi PbG (okS PbG) t s)))
         (transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi) (agset_induce_class (bridge_ag7 G) H' phi PbG t s))
         (H .mul t (phi .fst s))
         (refl (transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi)) (bridge_phi_shriek_path_class G H phi okS PbG t s))
         (bridge_adj_ipp_class G H phi t s)))

{` The key comparison: for any data, the blind pointing path, moved to our
   φ_!, is our moved pointing path (checked on classes). `}
def bridge_key_path (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (okS : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X) (ok1 : BlindBconcrOK1 G H phi okS)
  : Id (Id (AbstractGSet (bridge_ag7 H)) (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi (blind_abs_principal G)) (blind_abs_principal H))
      (concat (AbstractGSet (bridge_ag7 H)) (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi (blind_abs_principal G))
        (blind_phi_shriek G H phi okS (blind_abs_principal G)) (blind_abs_principal H)
        (inverse (AbstractGSet (bridge_ag7 H)) (blind_phi_shriek G H phi okS (blind_abs_principal G))
          (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi (blind_abs_principal G))
          (bridge_phi_shriek_path G H phi okS (blind_abs_principal G)))
        (ok1 .fst))
      (bridge_adj_ipp G H phi)
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let AH ≔ AbstractGSet H' in let C ≔ agset_carrier H' in
    let PbG ≔ blind_abs_principal G in let PbH ≔ blind_abs_principal H in
    let Fb ≔ blind_phi_shriek G H phi okS in let Fo ≔ agset_induce G' H' phi in
    let hp ≔ bridge_phi_shriek_path G H phi okS PbG in
    let ihp ≔ inverse AH (Fb PbG) (Fo PbG) hp in
    let lhs ≔ concat AH (Fo PbG) (Fb PbG) PbH ihp (ok1 .fst) in
    let R ≔ agset_induce_relation G' H' phi PbG in
    bridge_agset_path_ext H' (Fo PbG) PbH lhs (bridge_adj_ipp G H phi)
      (quotient_prop_induction (Product (H .carrier) (G .carrier)) R
        (z ↦ Id (H .carrier) (transport AH C (Fo PbG) PbH lhs z) (transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi) z))
        (z ↦ abstract_group_set H' (transport AH C (Fo PbG) PbH lhs z) (transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi) z))
        (u ↦ let c0 ≔ agset_induce_class G' H' phi PbG (u .fst) (u .snd) in
             let cb ≔ blind_phi_class G H phi PbG (okS PbG) (u .fst) (u .snd) in
             calc
               transport AH C (Fo PbG) PbH lhs c0
               = transport AH C (Fb PbG) PbH (ok1 .fst) (transport AH C (Fo PbG) (Fb PbG) ihp c0)
                 by transport_concat AH C (Fo PbG) (Fb PbG) PbH ihp (ok1 .fst) c0
               = transport AH C (Fb PbG) PbH (ok1 .fst) (transport AH C (Fo PbG) (Fb PbG) ihp (transport AH C (Fb PbG) (Fo PbG) hp cb))
                 by refl ((z ↦ transport AH C (Fb PbG) PbH (ok1 .fst) (transport AH C (Fo PbG) (Fb PbG) ihp z))
                            : AgsetInduceCarrier G' H' phi PbG → H .carrier)
                      (inverse (AgsetInduceCarrier G' H' phi PbG) (transport AH C (Fb PbG) (Fo PbG) hp cb) c0
                        (bridge_phi_shriek_path_class G H phi okS PbG (u .fst) (u .snd)))
               = transport AH C (Fb PbG) PbH (ok1 .fst) cb
                 by refl (transport AH C (Fb PbG) PbH (ok1 .fst)) (bridge_transport_inv_cancel AH C (Fb PbG) (Fo PbG) hp cb)
               = H .mul (u .fst) (phi .fst (u .snd)) by ok1 .snd (u .fst) (u .snd)
               = transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi) c0
                 by inverse (H .carrier) (transport AH C (Fo PbG) PbH (bridge_adj_ipp G H phi) c0)
                      (H .mul (u .fst) (phi .fst (u .snd))) (bridge_adj_ipp_class G H phi (u .fst) (u .snd)) ∎))

{` For any data d, the blind concr on φ is our concr_hom with moved points. `}
def bridge_mor_moved (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  : GroupHom (blind_concr G) (blind_concr H)
  ≔ bridge_gen_hom (AbstractGSet (bridge_ag7 G)) (AbstractGSet (bridge_ag7 H)) (blind_abs_gset_groupoid G) (blind_abs_gset_groupoid H)
      (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi) (blind_abs_principal G) (blind_abs_principal H) (bridge_adj_ipp G H phi)

def bridge_concr_mor_cmp (d : BlindConcrData) (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  : Id (GroupHom (blind_concr G) (blind_concr H)) (blind_concr_mor_d d G H phi) (bridge_mor_moved G H phi)
  ≔ let okS ≔ d .fst G H phi in
    bridge_gen_vary (AbstractGSet (bridge_ag7 G)) (AbstractGSet (bridge_ag7 H)) (blind_abs_gset_groupoid G) (blind_abs_gset_groupoid H)
      (blind_phi_shriek G H phi okS) (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi)
      (bridge_phi_shriek_path G H phi okS) (blind_abs_principal G) (blind_abs_principal H)
      (d .snd G H phi .fst) (bridge_adj_ipp G H phi)
      (bridge_key_path G H phi okS (d .snd G H phi))

{` Our functor laws and equivalence on arrows, in bridge_gen_hom form. `}
def bridge_ours_gen_b (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  : Id (GroupHom (automorphism_group (AbstractGSet (bridge_ag7 G)) (blind_abs_gset_groupoid G) (agset_principal (bridge_ag7 G)))
          (automorphism_group (AbstractGSet (bridge_ag7 H)) (blind_abs_gset_groupoid H) (agset_principal (bridge_ag7 H))))
      (bridge_wrap (bridge_ag7 G) (bridge_ag7 H) (blind_abs_gset_groupoid G) (blind_abs_gset_groupoid H)
        (concr_hom (bridge_ag7 G) (bridge_ag7 H) phi))
      (bridge_gen_hom (AbstractGSet (bridge_ag7 G)) (AbstractGSet (bridge_ag7 H)) (blind_abs_gset_groupoid G) (blind_abs_gset_groupoid H)
        (agset_induce (bridge_ag7 G) (bridge_ag7 H) phi) (agset_principal (bridge_ag7 G)) (agset_principal (bridge_ag7 H))
        (induce_principal_path (bridge_ag7 G) (bridge_ag7 H) phi))
  ≔ bridge_ours_gen (bridge_ag7 G) (bridge_ag7 H) phi (blind_abs_gset_groupoid G) (blind_abs_gset_groupoid H)

def bridge_concr_map_id (d : BlindConcrData) : BlindConcrMapId d
  ≔ G ↦ let G' ≔ bridge_ag7 G in let A ≔ AbstractGSet G' in let hb ≔ blind_abs_gset_groupoid G in
    let P ≔ agset_principal G' in
    let F ≔ agset_induce G' G' (abstract_hom_id G') in
    let h0 : Id (GroupHom (automorphism_group A hb P) (automorphism_group A hb P))
               (bridge_gen_hom A A hb hb F P P (induce_principal_path G' G' (abstract_hom_id G')))
               (group_hom_id (automorphism_group A hb P))
      ≔ concat (GroupHom (automorphism_group A hb P) (automorphism_group A hb P))
          (bridge_gen_hom A A hb hb F P P (induce_principal_path G' G' (abstract_hom_id G')))
          (bridge_wrap G' G' hb hb (concr_hom G' G' (abstract_hom_id G'))) (group_hom_id (automorphism_group A hb P))
          (inverse (GroupHom (automorphism_group A hb P) (automorphism_group A hb P))
            (bridge_wrap G' G' hb hb (concr_hom G' G' (abstract_hom_id G')))
            (bridge_gen_hom A A hb hb F P P (induce_principal_path G' G' (abstract_hom_id G')))
            (bridge_ours_gen_b G G (blind_abshom_id G)))
          (refl (bridge_wrap G' G' hb hb) (concr_hom_id G')) in
    concat (GroupHom (blind_concr G) (blind_concr G)) (blind_concr_mor_d d G G (blind_abshom_id G))
      (bridge_mor_moved G G (blind_abshom_id G)) (group_hom_id (blind_concr G))
      (bridge_concr_mor_cmp d G G (blind_abshom_id G))
      (bridge_gen_id A hb F P (induce_principal_path G' G' (abstract_hom_id G')) h0
        (blind_abs_principal G) (bridge_principal_path G))

def bridge_concr_map_comp (d : BlindConcrData) : BlindConcrMapComp d
  ≔ G H K f g ↦
    let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in let K' ≔ bridge_ag7 K in
    let AG ≔ AbstractGSet G' in let AH ≔ AbstractGSet H' in let AK ≔ AbstractGSet K' in
    let hG ≔ blind_abs_gset_groupoid G in let hH ≔ blind_abs_gset_groupoid H in let hK ≔ blind_abs_gset_groupoid K in
    let PG ≔ agset_principal G' in let PH ≔ agset_principal H' in let PK ≔ agset_principal K' in
    let gf ≔ abstract_hom_compose G' H' K' f g in
    let AutG ≔ automorphism_group AG hG PG in let AutH ≔ automorphism_group AH hH PH in let AutK ≔ automorphism_group AK hK PK in
    let gen ≔ bridge_gen_hom in
    let h0 : Id (GroupHom AutG AutK)
               (gen AG AK hG hK (agset_induce G' K' gf) PG PK (induce_principal_path G' K' gf))
               (group_hom_compose AutG AutH AutK
                 (gen AG AH hG hH (agset_induce G' H' f) PG PH (induce_principal_path G' H' f))
                 (gen AH AK hH hK (agset_induce H' K' g) PH PK (induce_principal_path H' K' g)))
      ≔ calc
          gen AG AK hG hK (agset_induce G' K' gf) PG PK (induce_principal_path G' K' gf)
          = bridge_wrap G' K' hG hK (concr_hom G' K' gf)
            by inverse (GroupHom AutG AutK) (bridge_wrap G' K' hG hK (concr_hom G' K' gf))
                 (gen AG AK hG hK (agset_induce G' K' gf) PG PK (induce_principal_path G' K' gf))
                 (bridge_ours_gen_b G K (blind_abshom_compose G H K f g))
          = group_hom_compose AutG AutH AutK (bridge_wrap G' H' hG hH (concr_hom G' H' f)) (bridge_wrap H' K' hH hK (concr_hom H' K' g))
            by refl (bridge_wrap G' K' hG hK) (concr_hom_compose G' H' K' f g)
          = group_hom_compose AutG AutH AutK
              (gen AG AH hG hH (agset_induce G' H' f) PG PH (induce_principal_path G' H' f))
              (gen AH AK hH hK (agset_induce H' K' g) PH PK (induce_principal_path H' K' g))
            by refl ((u v ↦ group_hom_compose AutG AutH AutK u v) : GroupHom AutG AutH → GroupHom AutH AutK → GroupHom AutG AutK)
                 (bridge_ours_gen_b G H f) (bridge_ours_gen_b H K g) ∎ in
    calc
      blind_concr_mor_d d G K (blind_abshom_compose G H K f g)
      = bridge_mor_moved G K (blind_abshom_compose G H K f g) by bridge_concr_mor_cmp d G K (blind_abshom_compose G H K f g)
      = group_hom_compose (blind_concr G) (blind_concr H) (blind_concr K) (bridge_mor_moved G H f) (bridge_mor_moved H K g)
        by bridge_gen_comp AG AH AK hG hH hK (agset_induce G' H' f) (agset_induce H' K' g) (agset_induce G' K' gf) PG PH PK
             (induce_principal_path G' H' f) (induce_principal_path H' K' g) (induce_principal_path G' K' gf) h0
             (blind_abs_principal G) (bridge_principal_path G) (blind_abs_principal H) (bridge_principal_path H)
             (blind_abs_principal K) (bridge_principal_path K)
      = group_hom_compose (blind_concr G) (blind_concr H) (blind_concr K) (blind_concr_mor_d d G H f) (blind_concr_mor_d d H K g)
        by refl ((u v ↦ group_hom_compose (blind_concr G) (blind_concr H) (blind_concr K) u v)
                   : GroupHom (blind_concr G) (blind_concr H) → GroupHom (blind_concr H) (blind_concr K)
                     → GroupHom (blind_concr G) (blind_concr K))
             (inverse (GroupHom (blind_concr G) (blind_concr H)) (blind_concr_mor_d d G H f) (bridge_mor_moved G H f)
               (bridge_concr_mor_cmp d G H f))
             (inverse (GroupHom (blind_concr H) (blind_concr K)) (blind_concr_mor_d d H K g) (bridge_mor_moved H K g)
               (bridge_concr_mor_cmp d H K g)) ∎

{` xca:Bconcr-OK (2), for every choice of the data. `}
def bridge_xca_bconcr_ok2 : blind_xca_bconcr_ok2 ≔ d ↦ (bridge_concr_map_id d, bridge_concr_map_comp d)

{` thm:concr-equiv-cats, for every choice of the data: fully faithful
   (our concr_hom is an equivalence on arrows, moved along the points) and
   split essentially surjective (blind_concr(blind_abstr K) = concr(abstr K) = K),
   hence an equivalence (ff_split_eso_is_cat_equivalence). `}
def bridge_blind_concr_functor (d : BlindConcrData) : WildFunctor BlindAbsGroupWild GroupWild
  ≔ (obj ≔ blind_concr, mor ≔ blind_concr_mor_d d, map_id ≔ bridge_concr_map_id d, map_comp ≔ bridge_concr_map_comp d)

def bridge_concr_mor_equiv (d : BlindConcrData) (G H : BlindAbsGroup)
  : BookIsEquiv (BlindAbsHom G H) (GroupHom (blind_concr G) (blind_concr H)) (blind_concr_mor_d d G H)
  ≔ let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let AG ≔ AbstractGSet G' in let AH ≔ AbstractGSet H' in
    let hG ≔ blind_abs_gset_groupoid G in let hH ≔ blind_abs_gset_groupoid H in
    let PG ≔ agset_principal G' in let PH ≔ agset_principal H' in
    let M ≔ AbstractHom G' H' in
    let Hom0 ≔ GroupHom (automorphism_group AG hG PG) (automorphism_group AH hH PH) in
    let ours : BookEquiv M Hom0
      ≔ book_equivalence M Hom0
          (compose_equiv M (GroupHom (concr G') (concr H')) Hom0
            (concr_hom G' H', cat_equivalence_mor_is_equiv AbstractGroupWild GroupWild concr_functor concr_is_cat_equivalence G' H')
            (bridge_wrap_equiv G' H' hG hH)) in
    let h0 : BookIsEquiv M Hom0 (m ↦ bridge_gen_hom AG AH hG hH (agset_induce G' H' m) PG PH (induce_principal_path G' H' m))
      ≔ bridge_book_equiv_homotopic M Hom0 ours
          (m ↦ bridge_gen_hom AG AH hG hH (agset_induce G' H' m) PG PH (induce_principal_path G' H' m))
          (m ↦ bridge_ours_gen_b G H m) in
    let moved : BookIsEquiv M (GroupHom (blind_concr G) (blind_concr H)) (bridge_mor_moved G H)
      ≔ bridge_gen_equiv M AG AH hG hH (m ↦ agset_induce G' H' m) PG PH (m ↦ induce_principal_path G' H' m) h0
          (blind_abs_principal G) (bridge_principal_path G) (blind_abs_principal H) (bridge_principal_path H) in
    bridge_book_equiv_homotopic M (GroupHom (blind_concr G) (blind_concr H)) (bridge_mor_moved G H, moved)
      (blind_concr_mor_d d G H)
      (m ↦ inverse (GroupHom (blind_concr G) (blind_concr H)) (blind_concr_mor_d d G H m) (bridge_mor_moved G H m)
        (bridge_concr_mor_cmp d G H m))

def bridge_concr_split_eso (d : BlindConcrData) : IsSplitEso BlindAbsGroupWild GroupWild (bridge_blind_concr_functor d)
  ≔ K ↦ (blind_abstr K,
         cat_idtoiso GroupWild (blind_concr (blind_abstr K)) K
           (concat Group (blind_concr (blind_abstr K)) (concr (abstr K)) K
             (bridge_concr_path (blind_abstr K)) (concr_abstr_path K)))

def bridge_thm_concr_equiv_cats : blind_thm_concr_equiv_cats
  ≔ d ↦ (bridge_concr_map_id d, (bridge_concr_map_comp d,
         ff_split_eso_is_cat_equivalence BlindAbsGroupWild GroupWild (bridge_blind_concr_functor d)
           (fully_faithful_from_equivs BlindAbsGroupWild GroupWild (bridge_blind_concr_functor d) (bridge_concr_mor_equiv d))
           (bridge_concr_split_eso d)))

{` Existence of the data (so the "for every choice" statements are not
   vacuous): ours provides xca:phi_!-OK and xca:Bconcr-OK (1). `}
def bridge_concr_data : BlindConcrData
  ≔ (G H phi ↦ bridge_xca_phi_shriek_ok G H phi, G H phi ↦ bridge_xca_bconcr_ok1 G H phi (bridge_xca_phi_shriek_ok G H phi))
