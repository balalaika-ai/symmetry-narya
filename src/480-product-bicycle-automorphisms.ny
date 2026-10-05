export "479-commuting-bicycle-classification"

{` Automorphism groups of product bicycles, and the footnote to the exercise
   at group.tex 2146: the Klein four-group is the automorphism group of the
   pictured 4-element commuting bicycle. General tools: an equivalence of
   groupoids, a subtype by propositions, and a binary product transport
   automorphism groups (Aut_A(a) for def:automorphism-group). `}

def bicycle_automorphism_group_equiv_path (A A' : Type) (e : Equiv A A') (hA : isGroupoid A) (hA' : isGroupoid A') (a : A)
  : Id Group (automorphism_group A hA a) (automorphism_group A' hA' (e .map a))
  ≔ equivalence_induction A
      (A' e ↦ (hA' : isGroupoid A') (a : A) → Id Group (automorphism_group A hA a) (automorphism_group A' hA' (e .map a)))
      (hA' a ↦ refl ((h ↦ automorphism_group A h a) : isGroupoid A → Group) (isgroupoid_isprop A hA hA'))
      A' e hA' a

{` Aut_{Σ A P}((a, p)) = Aut_A(a) for a family of propositions P. `}
def bicycle_subtype_component_map (A : Type) (P : A → Type) (a : A) (p : P a)
  (u : NativeComponent (Σ A P) (a, p)) : NativeComponent A a
  ≔ (u .fst .fst, mere_rec (Id (Σ A P) (a, p) (u .fst)) (Mere (Id A a (u .fst .fst))) (mere_isprop (Id A a (u .fst .fst)))
      (q ↦ mere (Id A a (u .fst .fst)) (q .fst)) (u .snd))

def bicycle_subtype_component_inverse (A : Type) (P : A → Type) (hP : (x : A) → isProp (P x)) (a : A) (p : P a)
  (v : NativeComponent A a) : NativeComponent (Σ A P) (a, p)
  ≔ let px : P (v .fst) ≔ mere_rec (Id A a (v .fst)) (P (v .fst)) (hP (v .fst)) (q ↦ transport A P a (v .fst) q p) (v .snd) in
    ((v .fst, px),
     mere_rec (Id A a (v .fst)) (Mere (Id (Σ A P) (a, p) (v .fst, px))) (mere_isprop (Id (Σ A P) (a, p) (v .fst, px)))
       (q ↦ mere (Id (Σ A P) (a, p) (v .fst, px)) (subtype_equal A P hP (a, p) (v .fst, px) q)) (v .snd))

def bicycle_subtype_component_equiv (A : Type) (P : A → Type) (hP : (x : A) → isProp (P x)) (a : A) (p : P a)
  : Equiv (NativeComponent (Σ A P) (a, p)) (NativeComponent A a)
  ≔ quasi_inverse_equiv (NativeComponent (Σ A P) (a, p)) (NativeComponent A a)
      (bicycle_subtype_component_map A P a p) (bicycle_subtype_component_inverse A P hP a p)
      (u ↦ component_path (Σ A P) (a, p)
        (bicycle_subtype_component_inverse A P hP a p (bicycle_subtype_component_map A P a p u)) u
        (subtype_equal A P hP
          (bicycle_subtype_component_inverse A P hP a p (bicycle_subtype_component_map A P a p u) .fst) (u .fst)
          (refl (u .fst .fst))))
      (v ↦ component_path A a (bicycle_subtype_component_map A P a p (bicycle_subtype_component_inverse A P hP a p v)) v
        (refl (v .fst)))

def bicycle_automorphism_group_subtype_path (A : Type) (P : A → Type) (hP : (x : A) → isProp (P x))
  (hA : isGroupoid A) (hS : isGroupoid (Σ A P)) (a : A) (p : P a)
  : Id Group (automorphism_group (Σ A P) hS (a, p)) (automorphism_group A hA a)
  ≔ group_path_from_pointed_equiv (automorphism_group (Σ A P) hS (a, p)) (automorphism_group A hA a)
      ((bicycle_subtype_component_map A P a p,
        component_path A a (component_point A a) (bicycle_subtype_component_map A P a p (component_point (Σ A P) (a, p)))
          (refl a)),
       book_equivalence (NativeComponent (Σ A P) (a, p)) (NativeComponent A a)
         (bicycle_subtype_component_equiv A P hP a p) .equiv)

{` Aut_{A×B}((a, b)) = Aut_A(a) × Aut_B(b). `}
def bicycle_product_component_map (A B : Type) (a : A) (b : B) (u : NativeComponent (Product A B) (a, b))
  : Product (NativeComponent A a) (NativeComponent B b)
  ≔ ((u .fst .fst, mere_rec (Id (Product A B) (a, b) (u .fst)) (Mere (Id A a (u .fst .fst))) (mere_isprop (Id A a (u .fst .fst)))
        (q ↦ mere (Id A a (u .fst .fst)) (q .fst)) (u .snd)),
     (u .fst .snd, mere_rec (Id (Product A B) (a, b) (u .fst)) (Mere (Id B b (u .fst .snd))) (mere_isprop (Id B b (u .fst .snd)))
        (q ↦ mere (Id B b (u .fst .snd)) (q .snd)) (u .snd)))

def bicycle_product_component_inverse (A B : Type) (a : A) (b : B) (v : Product (NativeComponent A a) (NativeComponent B b))
  : NativeComponent (Product A B) (a, b)
  ≔ ((v .fst .fst, v .snd .fst),
     mere_rec (Id A a (v .fst .fst)) (Mere (Id (Product A B) (a, b) (v .fst .fst, v .snd .fst)))
       (mere_isprop (Id (Product A B) (a, b) (v .fst .fst, v .snd .fst)))
       (q1 ↦ mere_rec (Id B b (v .snd .fst)) (Mere (Id (Product A B) (a, b) (v .fst .fst, v .snd .fst)))
         (mere_isprop (Id (Product A B) (a, b) (v .fst .fst, v .snd .fst)))
         (q2 ↦ mere (Id (Product A B) (a, b) (v .fst .fst, v .snd .fst)) (q1, q2)) (v .snd .snd))
       (v .fst .snd))

def bicycle_product_component_equiv (A B : Type) (a : A) (b : B)
  : Equiv (NativeComponent (Product A B) (a, b)) (Product (NativeComponent A a) (NativeComponent B b))
  ≔ quasi_inverse_equiv (NativeComponent (Product A B) (a, b)) (Product (NativeComponent A a) (NativeComponent B b))
      (bicycle_product_component_map A B a b) (bicycle_product_component_inverse A B a b)
      (u ↦ component_path (Product A B) (a, b)
        (bicycle_product_component_inverse A B a b (bicycle_product_component_map A B a b u)) u (refl (u .fst)))
      (v ↦ (component_path A a (bicycle_product_component_map A B a b (bicycle_product_component_inverse A B a b v) .fst)
              (v .fst) (refl (v .fst .fst)),
            component_path B b (bicycle_product_component_map A B a b (bicycle_product_component_inverse A B a b v) .snd)
              (v .snd) (refl (v .snd .fst))))

def bicycle_automorphism_group_product_path (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (a : A) (b : B)
  : Id Group (automorphism_group (Product A B) (groupoid_product A B hA hB) (a, b))
      (product_group (automorphism_group A hA a) (automorphism_group B hB b))
  ≔ group_path_from_pointed_equiv (automorphism_group (Product A B) (groupoid_product A B hA hB) (a, b))
      (product_group (automorphism_group A hA a) (automorphism_group B hB b))
      ((bicycle_product_component_map A B a b,
        (component_path A a (component_point A a) (bicycle_product_component_map A B a b (component_point (Product A B) (a, b)) .fst)
           (refl a),
         component_path B b (component_point B b) (bicycle_product_component_map A B a b (component_point (Product A B) (a, b)) .snd)
           (refl b))),
       book_equivalence (NativeComponent (Product A B) (a, b)) (Product (NativeComponent A a) (NativeComponent B b))
         (bicycle_product_component_equiv A B a b) .equiv)

{` The automorphism group of the product bicycle of two cycles is the
   product of their automorphism groups (via the equivalence of module 479). `}
def split_commuting_bicycles_groupoid : isGroupoid SplitCommutingBicycles
  ≔ hlevel_to_groupoid SplitCommutingBicycles
      (subtype_hlevel (suc. (suc. zero.)) Bicycles (B ↦ Product (IsCommutingBicycle B) (IsSplitBicycle B))
        (groupoid_to_hlevel Bicycles bicycles_groupoid) split_commuting_prop)

def cycle_pairs_groupoid : isGroupoid (Product Cycles Cycles)
  ≔ groupoid_product Cycles Cycles cycles_groupoid cycles_groupoid

def cycle_product_bicycle_automorphism_path (c d : Cycles)
  : Id Group (bicycle_automorphism_group (cycle_product_bicycle c d))
      (product_group (automorphism_group Cycles cycles_groupoid c) (automorphism_group Cycles cycles_groupoid d))
  ≔ let G1 ≔ bicycle_automorphism_group (cycle_product_bicycle c d) in
    let G2 ≔ automorphism_group SplitCommutingBicycles split_commuting_bicycles_groupoid (cycles_to_split_bicycles (c, d)) in
    let G3 ≔ automorphism_group (Product Cycles Cycles) cycle_pairs_groupoid (c, d) in
    let G4 ≔ product_group (automorphism_group Cycles cycles_groupoid c) (automorphism_group Cycles cycles_groupoid d) in
    concat Group G1 G2 G4
      (inverse Group G2 G1
        (bicycle_automorphism_group_subtype_path Bicycles (B ↦ Product (IsCommutingBicycle B) (IsSplitBicycle B))
          split_commuting_prop bicycles_groupoid split_commuting_bicycles_groupoid
          (cycle_product_bicycle c d) (cycles_to_split_bicycles (c, d) .snd)))
      (concat Group G2 G3 G4
        (inverse Group G3 G2
          (bicycle_automorphism_group_equiv_path (Product Cycles Cycles) SplitCommutingBicycles cycle_pairs_split_bicycles_equiv
            cycle_pairs_groupoid split_commuting_bicycles_groupoid (c, d)))
        (bicycle_automorphism_group_product_path Cycles Cycles cycles_groupoid cycles_groupoid c d))
