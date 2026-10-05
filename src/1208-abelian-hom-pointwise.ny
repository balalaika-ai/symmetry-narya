export "1207-abelian-hom-group"
export "64-pointed-cycle-maps"
export "701-abstract-homomorphisms"

{` Chapter 12, the lemma at abelian.tex 824: the equivalence
   USym(Hom(G, H)) ≃ absHom(G, H) is a homomorphism from abstr(Hom(G, H)) to
   the pointwise abstract group on absHom(G, H) (H abelian).

   Proof (differs from the book's pasting argument, which is marked TODO in
   the source): for abelian H, Ω of a pointed map into BH does not depend on
   its pointing path, because conjugation in USym H is trivial; this defines
   free_loop_symmetry : FreeLoop(BH) → USym H. The homotopy attached to a
   product p·q is the pointwise concatenation of those of q and p, and ap of a
   pointwise concatenation splits into the two whiskered factors, which are
   identified with the factors of p and q using that Ω(BB H) is connected. `}

{` In an abelian group conjugation is trivial. `}
def abelian_conjugate_trivial (H : Group) (hH : IsAbelian H) (d x : USym H)
  : Id (USym H) (pointed_loop_conjugate (BG H .carrier) (shape H) (shape H) d x) x
  ≔ let A ≔ BG H .carrier in let a ≔ shape H in
    calc
      pointed_loop_conjugate A a a d x = concat A a a a d (concat A a a a x (inverse A a a d)) by refl _
      = concat A a a a d (concat A a a a (inverse A a a d) x)
        by refl (concat A a a a d) (hH (inverse A a a d) x)
      = concat A a a a (concat A a a a d (inverse A a a d)) x
        by inverse (Id A a a) (concat A a a a (concat A a a a d (inverse A a a d)) x)
          (concat A a a a d (concat A a a a (inverse A a a d) x))
          (concat_assoc A a a a a d (inverse A a a d) x)
      = concat A a a a (refl a) x
        by refl ((r ↦ concat A a a a r x) : Id A a a → Id A a a) (concat_inverse_right A a a d)
      = x by concat_1p A a a x ∎

{` For abelian H, conjugating a loop at y back to sh_H does not depend on the
   chosen path sh_H = y. `}
def free_loop_conjugate_constant (H : Group) (hH : IsAbelian H) (y : BG H .carrier) (β : Id (BG H .carrier) y y)
  : WeaklyConstant (Id (BG H .carrier) (shape H) y) (USym H)
      (e ↦ pointed_loop_conjugate (BG H .carrier) (shape H) y e β)
  ≔ e e' ↦
    let A ≔ BG H .carrier in let a ≔ shape H in
    let d ≔ concat A a y a e' (inverse A a y e) in
    let de : Id (Id A a y) (concat A a a y d e) e'
      ≔ calc
          concat A a a y d e = concat A a y y e' (concat A y a y (inverse A a y e) e)
            by concat_assoc A a y a y e' (inverse A a y e) e
          = concat A a y y e' (refl y) by refl (concat A a y y e') (concat_inverse_left A a y e)
          = e' by concat_p1 A a y e' ∎ in
    calc
      pointed_loop_conjugate A a y e β
        = pointed_loop_conjugate A a a d (pointed_loop_conjugate A a y e β)
        by inverse (USym H) (pointed_loop_conjugate A a a d (pointed_loop_conjugate A a y e β))
          (pointed_loop_conjugate A a y e β) (abelian_conjugate_trivial H hH d (pointed_loop_conjugate A a y e β))
      = pointed_loop_conjugate A a y (concat A a a y d e) β
        by inverse (USym H) (pointed_loop_conjugate A a y (concat A a a y d e) β)
          (pointed_loop_conjugate A a a d (pointed_loop_conjugate A a y e β))
          (loop_conjugate_compose A a a y d e β)
      = pointed_loop_conjugate A a y e' β
        by refl ((r ↦ pointed_loop_conjugate A a y r β) : Id A a y → Id A a a) de ∎

def free_loop_symmetry (H : Group) (hH : IsAbelian H) (y : BG H .carrier) (β : Id (BG H .carrier) y y) : USym H
  ≔ weakly_constant_rec (Id (BG H .carrier) (shape H) y) (USym H)
      (e ↦ pointed_loop_conjugate (BG H .carrier) (shape H) y e β) (usym_set H)
      (free_loop_conjugate_constant H hH y β) (bg_connected H .snd (shape H) y)

def free_loop_symmetry_value (H : Group) (hH : IsAbelian H) (y : BG H .carrier) (β : Id (BG H .carrier) y y)
  (e : Id (BG H .carrier) (shape H) y)
  : Id (USym H) (free_loop_symmetry H hH y β) (pointed_loop_conjugate (BG H .carrier) (shape H) y e β)
  ≔ weakly_constant_rec_value (Id (BG H .carrier) (shape H) y) (USym H)
      (e ↦ pointed_loop_conjugate (BG H .carrier) (shape H) y e β) (usym_set H)
      (free_loop_conjugate_constant H hH y β) (bg_connected H .snd (shape H) y) e

{` Ω of a homomorphism into an abelian group only depends on its underlying
   function. `}
def usym_hom_free_loop (G H : Group) (hH : IsAbelian H) (f : GroupHom G H) (g : USym G)
  : Id (USym H) (usym_hom G H f g)
      (free_loop_symmetry H hH (hom_function G H f (shape G)) (refl (hom_function G H f) g))
  ≔ inverse (USym H) (free_loop_symmetry H hH (hom_function G H f (shape G)) (refl (hom_function G H f) g))
      (usym_hom G H f g)
      (free_loop_symmetry_value H hH (hom_function G H f (shape G)) (refl (hom_function G H f) g) (hom_point G H f))

def free_loop_symmetry_function_path (H : Group) (hH : IsAbelian H) (W : Type) (w : W) (α : Id W w w)
  (F F' : W → BG H .carrier) (P : Id (W → BG H .carrier) F F')
  : Id (USym H) (free_loop_symmetry H hH (F w) (refl F α)) (free_loop_symmetry H hH (F' w) (refl F' α))
  ≔ refl ((K ↦ free_loop_symmetry H hH (K w) (refl K α)) : (W → BG H .carrier) → USym H) P

def free_loop_symmetry_concat (H : Group) (hH : IsAbelian H) (y : BG H .carrier) (β β' : Id (BG H .carrier) y y)
  : Id (USym H) (free_loop_symmetry H hH y (concat (BG H .carrier) y y y β β'))
      (concat (BG H .carrier) (shape H) (shape H) (shape H) (free_loop_symmetry H hH y β) (free_loop_symmetry H hH y β'))
  ≔ let A ≔ BG H .carrier in let a ≔ shape H in
    mere_rec (Id A a y)
      (Id (USym H) (free_loop_symmetry H hH y (concat A y y y β β'))
        (concat A a a a (free_loop_symmetry H hH y β) (free_loop_symmetry H hH y β')))
      (usym_set H (free_loop_symmetry H hH y (concat A y y y β β'))
        (concat A a a a (free_loop_symmetry H hH y β) (free_loop_symmetry H hH y β')))
      (e ↦ calc
        free_loop_symmetry H hH y (concat A y y y β β') = pointed_loop_conjugate A a y e (concat A y y y β β')
          by free_loop_symmetry_value H hH y (concat A y y y β β') e
        = concat A a a a (pointed_loop_conjugate A a y e β) (pointed_loop_conjugate A a y e β')
          by loop_conjugate_concat A a y e β β'
        = concat A a a a (free_loop_symmetry H hH y β) (free_loop_symmetry H hH y β')
          by inverse (USym H) (concat A a a a (free_loop_symmetry H hH y β) (free_loop_symmetry H hH y β'))
            (concat A a a a (pointed_loop_conjugate A a y e β) (pointed_loop_conjugate A a y e β'))
            (refl (concat A a a a) (free_loop_symmetry_value H hH y β e) (free_loop_symmetry_value H hH y β' e)) ∎)
      (bg_connected H .snd a y)

{` Whiskering by a loop of BB H does not change the symmetry of BH obtained
   through ev = bb_loops_evaluation (Ω(BB H) is connected; at refl the
   whiskering map is homotopic to the identity). `}
def whisker_right_free_loop (H : AbelianGroup) (l l' : Loop (BB (H .fst))) (α : Id (Loop (BB (H .fst))) l l)
  : Id (USym (H .fst))
      (free_loop_symmetry (H .fst) (H .snd)
        (bb_loops_evaluation (H .fst) (concat (BB (H .fst) .carrier) (bb_point (H .fst)) (bb_point (H .fst)) (bb_point (H .fst)) l l'))
        (refl ((t ↦ bb_loops_evaluation (H .fst)
            (concat (BB (H .fst) .carrier) (bb_point (H .fst)) (bb_point (H .fst)) (bb_point (H .fst)) t l'))
          : Loop (BB (H .fst)) → BG (H .fst) .carrier) α))
      (free_loop_symmetry (H .fst) (H .snd) (bb_loops_evaluation (H .fst) l) (refl (bb_loops_evaluation (H .fst)) α))
  ≔ let B ≔ BB (H .fst) .carrier in let b ≔ bb_point (H .fst) in
    let M ≔ bb_loops_evaluation (H .fst) in
    let P ≔ (m ↦ Id (USym (H .fst))
        (free_loop_symmetry (H .fst) (H .snd) (M (concat B b b b l m))
          (refl ((t ↦ M (concat B b b b t m)) : Loop (BB (H .fst)) → BG (H .fst) .carrier) α))
        (free_loop_symmetry (H .fst) (H .snd) (M l) (refl M α))) : Loop (BB (H .fst)) → Type in
    connected_based_elim native_truncation (Loop (BB (H .fst))) (bb_simply_connected (H .fst) .snd) (refl b) P
      (m ↦ usym_set (H .fst)
        (free_loop_symmetry (H .fst) (H .snd) (M (concat B b b b l m))
          (refl ((t ↦ M (concat B b b b t m)) : Loop (BB (H .fst)) → BG (H .fst) .carrier) α))
        (free_loop_symmetry (H .fst) (H .snd) (M l) (refl M α)))
      (free_loop_symmetry_function_path (H .fst) (H .snd) (Loop (BB (H .fst))) l α
        (t ↦ M (concat B b b b t (refl b))) M
        (funext (Loop (BB (H .fst))) (_ ↦ BG (H .fst) .carrier) (t ↦ M (concat B b b b t (refl b))) M
          (t ↦ refl M (concat_p1 B b b t))))
      l'

def whisker_left_free_loop (H : AbelianGroup) (l l' : Loop (BB (H .fst))) (β : Id (Loop (BB (H .fst))) l' l')
  : Id (USym (H .fst))
      (free_loop_symmetry (H .fst) (H .snd)
        (bb_loops_evaluation (H .fst) (concat (BB (H .fst) .carrier) (bb_point (H .fst)) (bb_point (H .fst)) (bb_point (H .fst)) l l'))
        (refl ((t ↦ bb_loops_evaluation (H .fst)
            (concat (BB (H .fst) .carrier) (bb_point (H .fst)) (bb_point (H .fst)) (bb_point (H .fst)) l t))
          : Loop (BB (H .fst)) → BG (H .fst) .carrier) β))
      (free_loop_symmetry (H .fst) (H .snd) (bb_loops_evaluation (H .fst) l') (refl (bb_loops_evaluation (H .fst)) β))
  ≔ let B ≔ BB (H .fst) .carrier in let b ≔ bb_point (H .fst) in
    let M ≔ bb_loops_evaluation (H .fst) in
    let P ≔ (m ↦ Id (USym (H .fst))
        (free_loop_symmetry (H .fst) (H .snd) (M (concat B b b b m l'))
          (refl ((t ↦ M (concat B b b b m t)) : Loop (BB (H .fst)) → BG (H .fst) .carrier) β))
        (free_loop_symmetry (H .fst) (H .snd) (M l') (refl M β))) : Loop (BB (H .fst)) → Type in
    connected_based_elim native_truncation (Loop (BB (H .fst))) (bb_simply_connected (H .fst) .snd) (refl b) P
      (m ↦ usym_set (H .fst)
        (free_loop_symmetry (H .fst) (H .snd) (M (concat B b b b m l'))
          (refl ((t ↦ M (concat B b b b m t)) : Loop (BB (H .fst)) → BG (H .fst) .carrier) β))
        (free_loop_symmetry (H .fst) (H .snd) (M l') (refl M β)))
      (free_loop_symmetry_function_path (H .fst) (H .snd) (Loop (BB (H .fst))) l' β
        (t ↦ M (concat B b b b (refl b) t)) M
        (funext (Loop (BB (H .fst))) (_ ↦ BG (H .fst) .carrier) (t ↦ M (concat B b b b (refl b) t)) M
          (t ↦ refl M (concat_1p B b b t))))
      l

{` The homotopy ptw(p) attached to p : USym(Hom(G, H)), and its behaviour on
   products: ptw(p·q) = ptw(q)·ptw(p) pointwise (concatenation order). `}
def hom_symmetry_homotopy (G : Group) (H : AbelianGroup) (p : USym (abelian_hom_group G H))
  : BG G .carrier → Loop (BB (H .fst))
  ≔ x ↦ p .fst .fst (refl x)

def hom_symmetry_homotopy_mul (G : Group) (H : AbelianGroup) (p q : USym (abelian_hom_group G H))
  : Id (BG G .carrier → Loop (BB (H .fst)))
      (hom_symmetry_homotopy G H (usym_mul (abelian_hom_group G H) p q))
      (x ↦ concat (BB (H .fst) .carrier) (bb_point (H .fst)) (bb_point (H .fst)) (bb_point (H .fst))
        (hom_symmetry_homotopy G H q x) (hom_symmetry_homotopy G H p x))
  ≔ let Hom ≔ abelian_hom_group G H in
    let P ≔ BookPointedMap (BG G) (BB (H .fst)) in
    let c ≔ book_pointed_constant (BG G) (BB (H .fst)) in
    let F ≔ BG G .carrier → BB (H .fst) .carrier in
    let cf ≔ c .fst in
    let C ≔ BG Hom .carrier in
    let s ≔ shape Hom in
    let e1 : Id (Id P c c) (usym_mul Hom p q .fst) (concat P c c c (q .fst) (p .fst))
      ≔ map_path_concat C P (u ↦ u .fst) s s s q p in
    let e2 : Id (Id F cf cf) (concat P c c c (q .fst) (p .fst) .fst) (concat F cf cf cf (q .fst .fst) (p .fst .fst))
      ≔ map_path_concat P F (u ↦ u .fst) c c c (q .fst) (p .fst) in
    funext (BG G .carrier) (_ ↦ Loop (BB (H .fst)))
      (hom_symmetry_homotopy G H (usym_mul Hom p q))
      (x ↦ concat (BB (H .fst) .carrier) (bb_point (H .fst)) (bb_point (H .fst)) (bb_point (H .fst))
        (hom_symmetry_homotopy G H q x) (hom_symmetry_homotopy G H p x))
      (x ↦ calc
        usym_mul Hom p q .fst .fst (refl x) = concat P c c c (q .fst) (p .fst) .fst (refl x)
          by refl ((r ↦ r .fst (refl x)) : Id P c c → Loop (BB (H .fst))) e1
        = concat F cf cf cf (q .fst .fst) (p .fst .fst) (refl x)
          by refl ((r ↦ r (refl x)) : Id F cf cf → Loop (BB (H .fst))) e2
        = concat (BB (H .fst) .carrier) (bb_point (H .fst)) (bb_point (H .fst)) (bb_point (H .fst))
            (q .fst .fst (refl x)) (p .fst .fst (refl x))
          by map_path_concat F (BB (H .fst) .carrier) (k ↦ k x) cf cf cf (q .fst .fst) (p .fst .fst) ∎)

{` The homomorphism attached to p : USym(Hom(G, H)). `}
def hom_of_symmetry (G : Group) (H : AbelianGroup) (p : USym (abelian_hom_group G H)) : GroupHom G (H .fst)
  ≔ abelian_hom_usym_equiv G H .map p

def hom_of_symmetry_usym (G : Group) (H : AbelianGroup) (p : USym (abelian_hom_group G H)) (g : USym G)
  : Id (USym (H .fst)) (usym_hom G (H .fst) (hom_of_symmetry G H p) g)
      (free_loop_symmetry (H .fst) (H .snd) (bb_loops_evaluation (H .fst) (hom_symmetry_homotopy G H p (shape G)))
        (refl (bb_loops_evaluation (H .fst)) (refl (hom_symmetry_homotopy G H p) g)))
  ≔ usym_hom_free_loop G (H .fst) (H .snd) (hom_of_symmetry G H p) g

{` The lemma at abelian.tex 824, pointwise form: the image of p·q acts on g
   as the product of the images of p and q. `}
def abelian_hom_usym_mul (G : Group) (H : AbelianGroup) (p q : USym (abelian_hom_group G H)) (g : USym G)
  : Id (USym (H .fst)) (usym_hom G (H .fst) (hom_of_symmetry G H (usym_mul (abelian_hom_group G H) p q)) g)
      (usym_mul (H .fst) (usym_hom G (H .fst) (hom_of_symmetry G H p) g) (usym_hom G (H .fst) (hom_of_symmetry G H q) g))
  ≔ let K ≔ H .fst in let hK ≔ H .snd in
    let B ≔ BB K .carrier in let b ≔ bb_point K in
    let M ≔ bb_loops_evaluation K in
    let hq ≔ hom_symmetry_homotopy G H q in let hp ≔ hom_symmetry_homotopy G H p in
    let w ≔ (x ↦ concat B b b b (hq x) (hp x)) : BG G .carrier → Loop (BB K) in
    let l ≔ hq (shape G) in let l' ≔ hp (shape G) in
    let X ≔ refl ((t ↦ concat B b b b t l') : Loop (BB K) → Loop (BB K)) (refl hq g) in
    let Y ≔ refl (concat B b b b l) (refl hp g) in
    let m ≔ concat B b b b l l' in
    calc
      usym_hom G K (hom_of_symmetry G H (usym_mul (abelian_hom_group G H) p q)) g
        = free_loop_symmetry K hK (M (hom_symmetry_homotopy G H (usym_mul (abelian_hom_group G H) p q) (shape G)))
            (refl ((x ↦ M (hom_symmetry_homotopy G H (usym_mul (abelian_hom_group G H) p q) x)) : BG G .carrier → BG K .carrier) g)
        by hom_of_symmetry_usym G H (usym_mul (abelian_hom_group G H) p q) g
      = free_loop_symmetry K hK (M (w (shape G))) (refl ((x ↦ M (w x)) : BG G .carrier → BG K .carrier) g)
        by free_loop_symmetry_function_path K hK (BG G .carrier) (shape G) g
          (x ↦ M (hom_symmetry_homotopy G H (usym_mul (abelian_hom_group G H) p q) x)) (x ↦ M (w x))
          (refl ((h ↦ (x ↦ M (h x))) : (BG G .carrier → Loop (BB K)) → BG G .carrier → BG K .carrier)
            (hom_symmetry_homotopy_mul G H p q))
      = free_loop_symmetry K hK (M m) (refl M (concat (Loop (BB K)) m (concat B b b b (hq (shape G)) l') m X Y))
        by refl ((r ↦ free_loop_symmetry K hK (M m) (refl M r)) : Id (Loop (BB K)) m m → USym K)
          (map_path_pointwise_concat (BG G .carrier) B b b b hq hp (shape G) (shape G) g)
      = free_loop_symmetry K hK (M m) (concat (BG K .carrier) (M m) (M (concat B b b b l l')) (M m) (refl M X) (refl M Y))
        by refl ((r ↦ free_loop_symmetry K hK (M m) r) : Id (BG K .carrier) (M m) (M m) → USym K)
          (map_path_concat (Loop (BB K)) (BG K .carrier) M m m m X Y)
      = concat (BG K .carrier) (shape K) (shape K) (shape K)
          (free_loop_symmetry K hK (M m) (refl M X)) (free_loop_symmetry K hK (M m) (refl M Y))
        by free_loop_symmetry_concat K hK (M m) (refl M X) (refl M Y)
      = concat (BG K .carrier) (shape K) (shape K) (shape K)
          (free_loop_symmetry K hK (M l) (refl M (refl hq g))) (free_loop_symmetry K hK (M l') (refl M (refl hp g)))
        by refl (concat (BG K .carrier) (shape K) (shape K) (shape K))
          (whisker_right_free_loop H l l' (refl hq g)) (whisker_left_free_loop H l l' (refl hp g))
      = concat (BG K .carrier) (shape K) (shape K) (shape K)
          (usym_hom G K (hom_of_symmetry G H q) g) (usym_hom G K (hom_of_symmetry G H p) g)
        by inverse (USym K)
          (concat (BG K .carrier) (shape K) (shape K) (shape K)
            (usym_hom G K (hom_of_symmetry G H q) g) (usym_hom G K (hom_of_symmetry G H p) g))
          (concat (BG K .carrier) (shape K) (shape K) (shape K)
            (free_loop_symmetry K hK (M l) (refl M (refl hq g))) (free_loop_symmetry K hK (M l') (refl M (refl hp g))))
          (refl (concat (BG K .carrier) (shape K) (shape K) (shape K))
            (hom_of_symmetry_usym G H q g) (hom_of_symmetry_usym G H p g))
      = usym_mul K (usym_hom G K (hom_of_symmetry G H p) g) (usym_hom G K (hom_of_symmetry G H q) g)
        by refl (usym_mul K (usym_hom G K (hom_of_symmetry G H p) g) (usym_hom G K (hom_of_symmetry G H q) g)) ∎

{` (ab)(cd) = (ac)(bd) in an abelian group. `}
def abelian_interchange (K : Group) (hK : IsAbelian K) (x y z w : USym K)
  : Id (USym K) (usym_mul K (usym_mul K x y) (usym_mul K z w)) (usym_mul K (usym_mul K x z) (usym_mul K y w))
  ≔ let L ≔ usym_abstract_laws K in let m ≔ usym_mul K in
    calc
      m (m x y) (m z w) = m x (m y (m z w)) by inverse (USym K) (m x (m y (m z w))) (m (m x y) (m z w)) (L .assoc x y (m z w))
      = m x (m (m y z) w) by refl (m x) (L .assoc y z w)
      = m x (m (m z y) w) by refl (m x) (refl ((u ↦ m u w) : USym K → USym K) (hK y z))
      = m x (m z (m y w)) by refl (m x) (inverse (USym K) (m z (m y w)) (m (m z y) w) (L .assoc z y w))
      = m (m x z) (m y w) by L .assoc x z (m y w) ∎

{` The pointwise abstract group absHom_ptw(abstr G, abstr H) for abelian H
   (xca:abs-homgroup, "if" direction, needed here). `}
def pointwise_hom_mul (G : Group) (H : AbelianGroup)
  (φ ψ : AbstractHom (abstr G) (abstr (H .fst))) : AbstractHom (abstr G) (abstr (H .fst))
  ≔ let K ≔ H .fst in let A ≔ BG K .carrier in let a ≔ shape K in
    ((g ↦ usym_mul K (φ .fst g) (ψ .fst g)),
     s s' ↦ calc
       usym_mul K (φ .fst (usym_mul G s s')) (ψ .fst (usym_mul G s s'))
         = usym_mul K (usym_mul K (φ .fst s) (φ .fst s')) (usym_mul K (ψ .fst s) (ψ .fst s'))
         by refl (usym_mul K) (φ .snd s s') (ψ .snd s s')
       = usym_mul K (usym_mul K (φ .fst s) (ψ .fst s)) (usym_mul K (φ .fst s') (ψ .fst s'))
         by abelian_interchange K (H .snd) (φ .fst s) (φ .fst s') (ψ .fst s) (ψ .fst s') ∎)

{` Alias of abstract_hom_ext (module 701). `}
def abstract_hom_path (G H : AbstractGroup) (φ ψ : AbstractHom G H)
  (h : (g : G .carrier) → Id (H .carrier) (φ .fst g) (ψ .fst g)) : Id (AbstractHom G H) φ ψ
  ≔ abstract_hom_ext G H φ ψ h

{` The lemma at abelian.tex 824: abstr ∘ (USym(Hom(G, H)) ≃ Hom(G, H)) sends
   products to pointwise products. `}
def abelian_hom_abstract_mul (G : Group) (H : AbelianGroup) (p q : USym (abelian_hom_group G H))
  : Id (AbstractHom (abstr G) (abstr (H .fst)))
      (abelian_hom_abstract_map G H (usym_mul (abelian_hom_group G H) p q))
      (pointwise_hom_mul G H (abelian_hom_abstract_map G H p) (abelian_hom_abstract_map G H q))
  ≔ abstract_hom_path (abstr G) (abstr (H .fst))
      (abelian_hom_abstract_map G H (usym_mul (abelian_hom_group G H) p q))
      (pointwise_hom_mul G H (abelian_hom_abstract_map G H p) (abelian_hom_abstract_map G H q))
      (abelian_hom_usym_mul G H p q)

{` Path algebra: if p l p⁻¹ = q m q⁻¹ then p · l · (p⁻¹ · q) = q · m
   (concatenation order). `}
def conjugate_agreement_shift (A : Type) (a y z : A) (p : Id A a y) (l : Id A y y) (q : Id A a z) (m : Id A z z)
  (e : Id (Id A a a) (pointed_loop_conjugate A a y p l) (pointed_loop_conjugate A a z q m))
  : Id (Id A a z) (concat A a y z p (concat A y y z l (concat A y a z (inverse A a y p) q))) (concat A a z z q m)
  ≔ J A a (y p ↦ (l : Id A y y) → Id (Id A a a) (pointed_loop_conjugate A a y p l) (pointed_loop_conjugate A a z q m)
        → Id (Id A a z) (concat A a y z p (concat A y y z l (concat A y a z (inverse A a y p) q))) (concat A a z z q m))
      (J A a (z q ↦ (m : Id A z z) → (l : Id A a a)
            → Id (Id A a a) (pointed_loop_conjugate A a a (refl a) l) (pointed_loop_conjugate A a z q m)
            → Id (Id A a z) (concat A a a z (refl a) (concat A a a z l (concat A a a z (inverse A a a (refl a)) q)))
                (concat A a z z q m))
        (m l e ↦
          let lm : Id (Id A a a) l m
            ≔ calc
                l = pointed_loop_conjugate A a a (refl a) l
                  by inverse (Id A a a) (pointed_loop_conjugate A a a (refl a) l) l (loop_conjugate_at_refl A a l)
                = pointed_loop_conjugate A a a (refl a) m by e
                = m by loop_conjugate_at_refl A a m ∎ in
          calc
            concat A a a a (refl a) (concat A a a a l (concat A a a a (inverse A a a (refl a)) (refl a)))
              = concat A a a a l (concat A a a a (inverse A a a (refl a)) (refl a))
              by concat_1p A a a (concat A a a a l (concat A a a a (inverse A a a (refl a)) (refl a)))
            = concat A a a a l (inverse A a a (refl a))
              by refl (concat A a a a l) (concat_p1 A a a (inverse A a a (refl a)))
            = concat A a a a l (refl a) by refl (concat A a a a l) (inverse_refl A a)
            = l by concat_p1 A a a l
            = m by lm
            = concat A a a a (refl a) m
              by inverse (Id A a a) (concat A a a a (refl a) m) m (concat_1p A a a m) ∎)
        z q m)
      y p l e

{` abstr is injective on homomorphisms (the injectivity half of
   lem:homomabstrconcr, absgroup.tex 934): if Ω f = Ω f' pointwise then
   f = f'. For x : BG the type of identifications k : f(x) = f'(x)
   compatible with every α : sh_G = x is a proposition, inhabited at sh_G. `}
def AbstrAgreementFamily (G H : Group) (f f' : GroupHom G H) (x : BG G .carrier) : Type
  ≔ let B ≔ BG H .carrier in let F ≔ hom_function G H f in let F' ≔ hom_function G H f' in
    Σ (Id B (F x) (F' x))
      (k ↦ (α : Id (BG G .carrier) (shape G) x) → Id (Id B (shape H) (F' x))
        (concat B (shape H) (F (shape G)) (F' x) (hom_point G H f)
          (concat B (F (shape G)) (F x) (F' x) (refl F α) k))
        (concat B (shape H) (F' (shape G)) (F' x) (hom_point G H f') (refl F' α)))

def abstr_agreement_prop (G H : Group) (f f' : GroupHom G H) (x : BG G .carrier)
  : isProp (AbstrAgreementFamily G H f f' x)
  ≔ let B ≔ BG H .carrier in let F ≔ hom_function G H f in let F' ≔ hom_function G H f' in
    let C ≔ (k ↦ (α : Id (BG G .carrier) (shape G) x) → Id (Id B (shape H) (F' x))
        (concat B (shape H) (F (shape G)) (F' x) (hom_point G H f)
          (concat B (F (shape G)) (F x) (F' x) (refl F α) k))
        (concat B (shape H) (F' (shape G)) (F' x) (hom_point G H f') (refl F' α))) : Id B (F x) (F' x) → Type in
    let hC : (k : Id B (F x) (F' x)) → isProp (C k) ≔ (k ↦ pi_prop (Id (BG G .carrier) (shape G) x)
        (α ↦ Id (Id B (shape H) (F' x))
          (concat B (shape H) (F (shape G)) (F' x) (hom_point G H f)
            (concat B (F (shape G)) (F x) (F' x) (refl F α) k))
          (concat B (shape H) (F' (shape G)) (F' x) (hom_point G H f') (refl F' α)))
        (α ↦ bg_groupoid H (shape H) (F' x)
          (concat B (shape H) (F (shape G)) (F' x) (hom_point G H f)
            (concat B (F (shape G)) (F x) (F' x) (refl F α) k))
          (concat B (shape H) (F' (shape G)) (F' x) (hom_point G H f') (refl F' α)))) in
    u v ↦ subtype_equal (Id B (F x) (F' x)) C hC u v
      (mere_rec (Id (BG G .carrier) (shape G) x) (Id (Id B (F x) (F' x)) (u .fst) (v .fst))
        (bg_groupoid H (F x) (F' x) (u .fst) (v .fst))
        (α ↦ concat_cancel_left B (F (shape G)) (F x) (F' x) (refl F α) (u .fst) (v .fst)
          (concat_cancel_left B (shape H) (F (shape G)) (F' x) (hom_point G H f)
            (concat B (F (shape G)) (F x) (F' x) (refl F α) (u .fst))
            (concat B (F (shape G)) (F x) (F' x) (refl F α) (v .fst))
            (concat (Id B (shape H) (F' x))
              (concat B (shape H) (F (shape G)) (F' x) (hom_point G H f)
                (concat B (F (shape G)) (F x) (F' x) (refl F α) (u .fst)))
              (concat B (shape H) (F' (shape G)) (F' x) (hom_point G H f') (refl F' α))
              (concat B (shape H) (F (shape G)) (F' x) (hom_point G H f)
                (concat B (F (shape G)) (F x) (F' x) (refl F α) (v .fst)))
              (u .snd α)
              (inverse (Id B (shape H) (F' x))
                (concat B (shape H) (F (shape G)) (F' x) (hom_point G H f)
                  (concat B (F (shape G)) (F x) (F' x) (refl F α) (v .fst)))
                (concat B (shape H) (F' (shape G)) (F' x) (hom_point G H f') (refl F' α))
                (v .snd α)))))
        (bg_connected G .snd (shape G) x))

def abstr_hom_injective (G H : Group) (f f' : GroupHom G H)
  (e : (g : USym G) → Id (USym H) (usym_hom G H f g) (usym_hom G H f' g))
  : Id (GroupHom G H) f f'
  ≔ let B ≔ BG H .carrier in let F ≔ hom_function G H f in let F' ≔ hom_function G H f' in
    let sG ≔ shape G in let sH ≔ shape H in
    let fpt ≔ hom_point G H f in let fpt' ≔ hom_point G H f' in
    let k0 ≔ concat B (F sG) sH (F' sG) (inverse B sH (F sG) fpt) fpt' in
    let base : AbstrAgreementFamily G H f f' sG
      ≔ (k0, α ↦ conjugate_agreement_shift B sH (F sG) (F' sG) fpt (refl F α) fpt' (refl F' α) (e α)) in
    let D ≔ connected_based_elim native_truncation (BG G .carrier) (bg_connected G) sG
      (AbstrAgreementFamily G H f f') (abstr_agreement_prop G H f f') base in
    let coh : Id (Id B sH (F' sG)) (concat B sH (F sG) (F' sG) fpt (D sG .fst)) fpt'
      ≔ calc
          concat B sH (F sG) (F' sG) fpt (D sG .fst)
            = concat B sH (F sG) (F' sG) fpt (concat B (F sG) (F sG) (F' sG) (refl (F sG)) (D sG .fst))
            by refl (concat B sH (F sG) (F' sG) fpt)
              (inverse (Id B (F sG) (F' sG)) (concat B (F sG) (F sG) (F' sG) (refl (F sG)) (D sG .fst)) (D sG .fst)
                (concat_1p B (F sG) (F' sG) (D sG .fst)))
          = concat B sH (F' sG) (F' sG) fpt' (refl (F' sG)) by D sG .snd (refl sG)
          = fpt' by concat_p1 B sH (F' sG) fpt' ∎ in
    equiv_inverse_map (Id (GroupHom G H) f f') (PointedHomotopy (BG G) (BG H) (hom_B G H f) (hom_B G H f'))
      (group_hom_path_equiv G H f f') ((x ↦ D x .fst), coh)

{` Consequence of the lemma at abelian.tex 824 (stated in fields.tex before
   lem:grpHomOK): Hom(G, H) is an abelian group. `}
def abelian_hom_group_abelian (G : Group) (H : AbelianGroup) : IsAbelian (abelian_hom_group G H)
  ≔ p q ↦ equivalence_injective (USym (abelian_hom_group G H)) (GroupHom G (H .fst)) (abelian_hom_usym_equiv G H)
      (usym_mul (abelian_hom_group G H) p q) (usym_mul (abelian_hom_group G H) q p)
      (abstr_hom_injective G (H .fst) (hom_of_symmetry G H (usym_mul (abelian_hom_group G H) p q))
        (hom_of_symmetry G H (usym_mul (abelian_hom_group G H) q p))
        (g ↦ calc
          usym_hom G (H .fst) (hom_of_symmetry G H (usym_mul (abelian_hom_group G H) p q)) g
            = usym_mul (H .fst) (usym_hom G (H .fst) (hom_of_symmetry G H p) g) (usym_hom G (H .fst) (hom_of_symmetry G H q) g)
            by abelian_hom_usym_mul G H p q g
          = usym_mul (H .fst) (usym_hom G (H .fst) (hom_of_symmetry G H q) g) (usym_hom G (H .fst) (hom_of_symmetry G H p) g)
            by H .snd (usym_hom G (H .fst) (hom_of_symmetry G H p) g) (usym_hom G (H .fst) (hom_of_symmetry G H q) g)
          = usym_hom G (H .fst) (hom_of_symmetry G H (usym_mul (abelian_hom_group G H) q p)) g
            by inverse (USym (H .fst))
              (usym_hom G (H .fst) (hom_of_symmetry G H (usym_mul (abelian_hom_group G H) q p)) g)
              (usym_mul (H .fst) (usym_hom G (H .fst) (hom_of_symmetry G H q) g) (usym_hom G (H .fst) (hom_of_symmetry G H p) g))
              (abelian_hom_usym_mul G H q p g) ∎))

def abelian_hom_abelian_group (G : Group) (H : AbelianGroup) : AbelianGroup
  ≔ (abelian_hom_group G H, abelian_hom_group_abelian G H)
