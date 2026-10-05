export "404-group-examples"

{` xca:BGtotype (group.tex 1329). For a group G and a groupoid A:
     (1) BG÷ → A
     (2) Σ(a : A) Σ(f : BG÷ → A) (a = f(sh_G))
     (3) Σ(a : A) (BG →* (A, a))
     (4) Σ(a : A) Hom(G, Aut_A(a)).
   (2) and (3) agree judgmentally (BookPointedMap is that Σ-type);
   (3) ≃ (1) is xca:freemaps (pointed_map_chosen_target_equiv, module 122);
   (3) ≃ (4) needs that pointed maps from a connected type into (A, a) are
   pointed maps into the component A_(a) (xca:ptd-conn-to-comp of
   actions.tex, proved here as pointed_maps_into_component). `}

def BGToTypeOne (G : Group) (A : Type) : Type ≔ BG G .carrier → A

def BGToTypeTwo (G : Group) (A : Type) : Type
  ≔ Σ A (a ↦ Σ (BG G .carrier → A) (f ↦ Id A a (f (shape G))))

def BGToTypeThree (G : Group) (A : Type) : Type ≔ Σ A (a ↦ BookPointedMap (BG G) (A, a))

def BGToTypeFour (G : Group) (A : Type) (hA : isGroupoid A) : Type
  ≔ Σ A (a ↦ GroupHom G (automorphism_group A hA a))

def bg_to_type_two_three (G : Group) (A : Type) : Id Type (BGToTypeTwo G A) (BGToTypeThree G A)
  ≔ refl (BGToTypeTwo G A)

def bg_to_type_three_one (G : Group) (A : Type) : Equiv (BGToTypeThree G A) (BGToTypeOne G A)
  ≔ pointed_map_chosen_target_equiv (BG G) A

def bg_to_type_two_one (G : Group) (A : Type) : Equiv (BGToTypeTwo G A) (BGToTypeOne G A)
  ≔ pointed_map_chosen_target_equiv (BG G) A

{` xca:ptd-conn-to-comp: for a connected pointed type X,
   (X →* (A, a)) ≃ (X →* (A_(a), (a, !))). The truncation component of
   the lifted map at x is obtained from a mere path x0 = x; the pointing
   path of the lift is the component path with first component f_pt. The
   inverse composes with the first projection; the round trip on
   (X →* (A, a)) is refl. `}
def component_lift_map (X : Pointed) (hX : Connected (X .carrier)) (A : Type) (a : A)
  (f : BookPointedMap X (A, a)) (x : X .carrier) : NativeComponent A a
  ≔ (f .fst x, mere_rec (Id (X .carrier) (X .point) x) (Mere (Id A a (f .fst x))) (mere_isprop (Id A a (f .fst x)))
      (r ↦ mere (Id A a (f .fst x)) (concat A a (f .fst (X .point)) (f .fst x) (f .snd) (refl (f .fst) r)))
      (hX .snd (X .point) x))

def component_lift (X : Pointed) (hX : Connected (X .carrier)) (A : Type) (a : A)
  (f : BookPointedMap X (A, a)) : BookPointedMap X (NativeComponent A a, component_point A a)
  ≔ (component_lift_map X hX A a f,
     component_path A a (component_point A a) (component_lift_map X hX A a f (X .point)) (f .snd))

def component_project (X : Pointed) (A : Type) (a : A)
  (g : BookPointedMap X (NativeComponent A a, component_point A a)) : BookPointedMap X (A, a)
  ≔ (x ↦ g .fst x .fst, g .snd .fst)

def component_project_lift (X : Pointed) (hX : Connected (X .carrier)) (A : Type) (a : A)
  (f : BookPointedMap X (A, a))
  : Id (BookPointedMap X (A, a)) (component_project X A a (component_lift X hX A a f)) f
  ≔ refl f

def component_lift_project (X : Pointed) (hX : Connected (X .carrier)) (A : Type) (a : A)
  (g : BookPointedMap X (NativeComponent A a, component_point A a))
  : Id (BookPointedMap X (NativeComponent A a, component_point A a)) (component_lift X hX A a (component_project X A a g)) g
  ≔ let Y : Pointed ≔ (NativeComponent A a, component_point A a) in
    let P ≔ NativeComponent A a in
    let x0 ≔ X .point in
    let g' ≔ component_lift X hX A a (component_project X A a g) in
    let h : (x : X .carrier) → Id P (g' .fst x) (g .fst x)
      ≔ x ↦ component_path A a (g' .fst x) (g .fst x) (refl (g .fst x .fst)) in
    let lhs ≔ concat P (component_point A a) (g' .fst x0) (g .fst x0) (g' .snd) (h x0) in
    equiv_inverse_map (Id (BookPointedMap X Y) g' g) (PointedHomotopy X Y g' g) (pointed_map_path_equiv X Y g' g)
      (h, equivalence_injective (Id P (component_point A a) (g .fst x0)) (Id A a (g .fst x0 .fst))
            (component_path_equiv A a (component_point A a) (g .fst x0)) lhs (g .snd)
            (concat (Id A a (g .fst x0 .fst)) (lhs .fst)
              (concat A a (g .fst x0 .fst) (g .fst x0 .fst) (g .snd .fst) (refl (g .fst x0 .fst)))
              (g .snd .fst)
              (map_path_concat P A (u ↦ u .fst) (component_point A a) (g' .fst x0) (g .fst x0) (g' .snd) (h x0))
              (concat_p1 A a (g .fst x0 .fst) (g .snd .fst))))

def pointed_maps_into_component (X : Pointed) (hX : Connected (X .carrier)) (A : Type) (a : A)
  : Equiv (BookPointedMap X (A, a)) (BookPointedMap X (NativeComponent A a, component_point A a))
  ≔ quasi_inverse_equiv (BookPointedMap X (A, a)) (BookPointedMap X (NativeComponent A a, component_point A a))
      (component_lift X hX A a) (component_project X A a)
      (component_project_lift X hX A a) (component_lift_project X hX A a)

{` (3) ≃ (4), fiberwise over a : A, and the composite (1) ≃ (4). `}
def bg_to_type_three_four (G : Group) (A : Type) (hA : isGroupoid A)
  : Equiv (BGToTypeThree G A) (BGToTypeFour G A hA)
  ≔ family_equiv A (a ↦ BookPointedMap (BG G) (A, a)) (a ↦ GroupHom G (automorphism_group A hA a))
      (a ↦ compose_equiv (BookPointedMap (BG G) (A, a))
        (BookPointedMap (BG G) (NativeComponent A a, component_point A a))
        (GroupHom G (automorphism_group A hA a))
        (pointed_maps_into_component (BG G) (bg_connected G) A a)
        (canonical_inverse_equiv (GroupHom G (automorphism_group A hA a))
          (BookPointedMap (BG G) (NativeComponent A a, component_point A a))
          (group_hom_classifying_equiv G (automorphism_group A hA a))))

def bg_to_type_one_four (G : Group) (A : Type) (hA : isGroupoid A)
  : Equiv (BGToTypeOne G A) (BGToTypeFour G A hA)
  ≔ compose_equiv (BGToTypeOne G A) (BGToTypeThree G A) (BGToTypeFour G A hA)
      (canonical_inverse_equiv (BGToTypeThree G A) (BGToTypeOne G A) (bg_to_type_three_one G A))
      (bg_to_type_three_four G A hA)

{` Litmus: a map f : BG÷ → A goes to (f(sh_G), the homomorphism
   G → Aut_A(f(sh_G)) classified by f on components, pointed by refl in
   the first component). `}
def bg_to_type_one_four_point (G : Group) (A : Type) (hA : isGroupoid A) (f : BG G .carrier → A)
  : Id A (bg_to_type_one_four G A hA .map f .fst) (f (shape G))
  ≔ refl (f (shape G))

def bg_to_type_one_four_function (G : Group) (A : Type) (hA : isGroupoid A) (f : BG G .carrier → A) (x : BG G .carrier)
  : Id A (hom_function G (automorphism_group A hA (f (shape G))) (bg_to_type_one_four G A hA .map f .snd) x .fst) (f x)
  ≔ refl (f x)
