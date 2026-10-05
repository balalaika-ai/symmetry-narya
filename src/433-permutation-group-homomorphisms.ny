export "431-homomorphism-remarks"

{` ex:groups-morphisms, item 1 (group.tex 1141): homomorphisms of
   permutation groups Σ_S → Σ_{S⊔T}, Σ_S → Σ_{S×T}, Σ_m → Σ_{m+n} and
   Σ_m → Σ_{mn}. BΣ_S is the component Set_(S) pointed at S (module 404). `}

def set_sum_right (T X : SetTypes) : SetTypes
  ≔ (Sum (X .fst) (T .fst), sum_set (X .fst) (T .fst) (X .snd) (T .snd))

def set_product_right (T X : SetTypes) : SetTypes
  ≔ (Product (X .fst) (T .fst), product_set (X .fst) (T .fst) (X .snd) (T .snd))

{` The map _⊔T : Set_(S) → Set_(S⊔T), pointed by refl (judgmentally), as a
   homomorphism Σ_S → Σ_{S⊔T}; likewise _×T. These are instances of
   automorphism_group_map_hom (module 431). `}
def permutation_sum_hom (S T : SetTypes) : GroupHom (permutation_group S) (permutation_group (set_sum_right T S))
  ≔ automorphism_group_map_hom SetTypes SetTypes sets_groupoid sets_groupoid (set_sum_right T) S

def permutation_product_hom (S T : SetTypes)
  : GroupHom (permutation_group S) (permutation_group (set_product_right T S))
  ≔ automorphism_group_map_hom SetTypes SetTypes sets_groupoid sets_groupoid (set_product_right T) S

{` Litmus: the classifying map sends X to X ⊔ T, and it is pointed by refl. `}
def permutation_sum_hom_carrier (S T : SetTypes) (u : BG (permutation_group S) .carrier)
  : Id Type (hom_function (permutation_group S) (permutation_group (set_sum_right T S)) (permutation_sum_hom S T) u .fst .fst)
      (Sum (u .fst .fst) (T .fst))
  ≔ refl (Sum (u .fst .fst) (T .fst))

def permutation_sum_hom_point (S T : SetTypes)
  : Id (Id (BG (permutation_group (set_sum_right T S)) .carrier) (shape (permutation_group (set_sum_right T S)))
         (hom_function (permutation_group S) (permutation_group (set_sum_right T S)) (permutation_sum_hom S T)
           (shape (permutation_group S))))
      (hom_point (permutation_group S) (permutation_group (set_sum_right T S)) (permutation_sum_hom S T))
      (refl (shape (permutation_group (set_sum_right T S))))
  ≔ refl (refl (shape (permutation_group (set_sum_right T S))))

{` Transport along ap_{_⊔T}(p) and ap_{_×T}(p) does nothing to T. `}
def transport_sum_right_inl (T A A' : Type) (p : Id Type A A') (a : A)
  : Id (Sum A' T) (transport Type (Y ↦ Y) (Sum A T) (Sum A' T) (refl ((Y ↦ Sum Y T) : Type → Type) p) (inl. a))
      (inl. (transport Type (Y ↦ Y) A A' p a))
  ≔ J Type A
      (A' p ↦ Id (Sum A' T) (transport Type (Y ↦ Y) (Sum A T) (Sum A' T) (refl ((Y ↦ Sum Y T) : Type → Type) p) (inl. a))
        (inl. (transport Type (Y ↦ Y) A A' p a)))
      (concat (Sum A T) (transport Type (Y ↦ Y) (Sum A T) (Sum A T) (refl (Sum A T)) (inl. a)) (inl. a)
        (inl. (transport Type (Y ↦ Y) A A (refl A) a))
        (transport_refl Type (Y ↦ Y) (Sum A T) (inl. a))
        (inverse (Sum A T) (inl. (transport Type (Y ↦ Y) A A (refl A) a)) (inl. a)
          (refl ((z ↦ inl. z) : A → Sum A T) (transport_refl Type (Y ↦ Y) A a))))
      A' p

def transport_sum_right_inr (T A A' : Type) (p : Id Type A A') (t : T)
  : Id (Sum A' T) (transport Type (Y ↦ Y) (Sum A T) (Sum A' T) (refl ((Y ↦ Sum Y T) : Type → Type) p) (inr. t)) (inr. t)
  ≔ J Type A
      (A' p ↦ Id (Sum A' T) (transport Type (Y ↦ Y) (Sum A T) (Sum A' T) (refl ((Y ↦ Sum Y T) : Type → Type) p) (inr. t))
        (inr. t))
      (transport_refl Type (Y ↦ Y) (Sum A T) (inr. t))
      A' p

def transport_product_right (T A A' : Type) (p : Id Type A A') (a : A) (t : T)
  : Id (Product A' T)
      (transport Type (Y ↦ Y) (Product A T) (Product A' T) (refl ((Y ↦ Product Y T) : Type → Type) p) (a, t))
      (transport Type (Y ↦ Y) A A' p a, t)
  ≔ J Type A
      (A' p ↦ Id (Product A' T)
        (transport Type (Y ↦ Y) (Product A T) (Product A' T) (refl ((Y ↦ Product Y T) : Type → Type) p) (a, t))
        (transport Type (Y ↦ Y) A A' p a, t))
      (concat (Product A T) (transport Type (Y ↦ Y) (Product A T) (Product A T) (refl (Product A T)) (a, t)) (a, t)
        (transport Type (Y ↦ Y) A A (refl A) a, t)
        (transport_refl Type (Y ↦ Y) (Product A T) (a, t))
        (inverse (Product A T) (transport Type (Y ↦ Y) A A (refl A) a, t) (a, t)
          (transport_refl Type (Y ↦ Y) A a, refl t)))
      A' p

{` "If you have a symmetry of S, then we get a symmetry of S ⊔ T (which
   doesn't do anything to T)": the action of the image of g on S ⊔ T is g on
   S and the identity on T. Similarly on S × T, g acts on the first
   component only. `}
def permutation_sum_hom_action_inl (S T : SetTypes) (g : USym (permutation_group S)) (s : S .fst)
  : Id (Sum (S .fst) (T .fst))
      (permutation_action (set_sum_right T S)
        (usym_hom (permutation_group S) (permutation_group (set_sum_right T S)) (permutation_sum_hom S T) g) (inl. s))
      (inl. (permutation_action S g s))
  ≔ let F ≔ set_sum_right T S in
    let E ≔ Sum (S .fst) (T .fst) in
    concat E
      (permutation_action F (usym_hom (permutation_group S) (permutation_group F) (permutation_sum_hom S T) g) (inl. s))
      (transport Type (Y ↦ Y) E E (refl ((Y ↦ Sum Y (T .fst)) : Type → Type) (g .fst .fst)) (inl. s))
      (inl. (permutation_action S g s))
      (refl ((q ↦ transport Type (Y ↦ Y) E E q (inl. s)) : Id Type E E → E)
        (loops_map_refl_family (NativeComponent SetTypes S) (NativeComponent SetTypes F)
          (native_component_map SetTypes SetTypes (set_sum_right T) S) (component_point SetTypes S)
          (u ↦ u .fst .fst) g))
      (transport_sum_right_inl (T .fst) (S .fst) (S .fst) (g .fst .fst) s)

def permutation_sum_hom_action_inr (S T : SetTypes) (g : USym (permutation_group S)) (t : T .fst)
  : Id (Sum (S .fst) (T .fst))
      (permutation_action (set_sum_right T S)
        (usym_hom (permutation_group S) (permutation_group (set_sum_right T S)) (permutation_sum_hom S T) g) (inr. t))
      (inr. t)
  ≔ let F ≔ set_sum_right T S in
    let E ≔ Sum (S .fst) (T .fst) in
    concat E
      (permutation_action F (usym_hom (permutation_group S) (permutation_group F) (permutation_sum_hom S T) g) (inr. t))
      (transport Type (Y ↦ Y) E E (refl ((Y ↦ Sum Y (T .fst)) : Type → Type) (g .fst .fst)) (inr. t))
      (inr. t)
      (refl ((q ↦ transport Type (Y ↦ Y) E E q (inr. t)) : Id Type E E → E)
        (loops_map_refl_family (NativeComponent SetTypes S) (NativeComponent SetTypes F)
          (native_component_map SetTypes SetTypes (set_sum_right T) S) (component_point SetTypes S)
          (u ↦ u .fst .fst) g))
      (transport_sum_right_inr (T .fst) (S .fst) (S .fst) (g .fst .fst) t)

def permutation_product_hom_action (S T : SetTypes) (g : USym (permutation_group S)) (s : S .fst) (t : T .fst)
  : Id (Product (S .fst) (T .fst))
      (permutation_action (set_product_right T S)
        (usym_hom (permutation_group S) (permutation_group (set_product_right T S)) (permutation_product_hom S T) g) (s, t))
      (permutation_action S g s, t)
  ≔ let F ≔ set_product_right T S in
    let E ≔ Product (S .fst) (T .fst) in
    concat E
      (permutation_action F (usym_hom (permutation_group S) (permutation_group F) (permutation_product_hom S T) g) (s, t))
      (transport Type (Y ↦ Y) E E (refl ((Y ↦ Product Y (T .fst)) : Type → Type) (g .fst .fst)) (s, t))
      (permutation_action S g s, t)
      (refl ((q ↦ transport Type (Y ↦ Y) E E q (s, t)) : Id Type E E → E)
        (loops_map_refl_family (NativeComponent SetTypes S) (NativeComponent SetTypes F)
          (native_component_map SetTypes SetTypes (set_product_right T) S) (component_point SetTypes S)
          (u ↦ u .fst .fst) g))
      (transport_product_right (T .fst) (S .fst) (S .fst) (g .fst .fst) s t)

{` The isomorphism Σ_S ≅ Σ_{S'} induced by an identification S' = S of sets
   (given as an equivalence d : S' ≃ S, i.e. the set path ua(d)): the
   classifying map is X ↦ X on underlying sets, pointed by ua(d). Its action
   is conjugation, g ↦ d⁻¹ ∘ g ∘ d. `}
def permutation_relabel_map (S S' : SetTypes) (d : Equiv (S' .fst) (S .fst)) (u : NativeComponent SetTypes S)
  : NativeComponent SetTypes S'
  ≔ (u .fst, mere_rec (Id SetTypes S (u .fst)) (Mere (Id SetTypes S' (u .fst))) (mere_isprop (Id SetTypes S' (u .fst)))
      (p ↦ mere (Id SetTypes S' (u .fst)) (concat SetTypes S' S (u .fst) (set_types_path S' S d) p)) (u .snd))

def permutation_relabel_point (S S' : SetTypes) (d : Equiv (S' .fst) (S .fst))
  : Id (NativeComponent SetTypes S') (component_point SetTypes S')
      (permutation_relabel_map S S' d (component_point SetTypes S))
  ≔ component_path SetTypes S' (component_point SetTypes S') (permutation_relabel_map S S' d (component_point SetTypes S))
      (set_types_path S' S d)

def permutation_relabel_hom (S S' : SetTypes) (d : Equiv (S' .fst) (S .fst))
  : GroupHom (permutation_group S) (permutation_group S')
  ≔ mkhom (permutation_group S) (permutation_group S') (permutation_relabel_map S S' d, permutation_relabel_point S S' d)

def permutation_relabel_is_iso (S S' : SetTypes) (d : Equiv (S' .fst) (S .fst))
  : IsGroupIso (permutation_group S) (permutation_group S') (permutation_relabel_hom S S' d)
  ≔ let d' ≔ canonical_inverse_equiv (S' .fst) (S .fst) d in
    book_equivalence (NativeComponent SetTypes S) (NativeComponent SetTypes S')
      (quasi_inverse_equiv (NativeComponent SetTypes S) (NativeComponent SetTypes S')
        (permutation_relabel_map S S' d) (permutation_relabel_map S' S d')
        (u ↦ component_path SetTypes S (permutation_relabel_map S' S d' (permutation_relabel_map S S' d u)) u
          (refl (u .fst)))
        (v ↦ component_path SetTypes S' (permutation_relabel_map S S' d (permutation_relabel_map S' S d' v)) v
          (refl (v .fst))))
      .equiv

def permutation_relabel_iso (S S' : SetTypes) (d : Equiv (S' .fst) (S .fst))
  : GroupIso (permutation_group S) (permutation_group S')
  ≔ (permutation_relabel_hom S S' d, permutation_relabel_is_iso S S' d)

{` Transport along p⁻¹ undoes transport along p, applied at d(d⁻¹ z). `}
def permutation_relabel_back (S S' : SetTypes) (d : Equiv (S' .fst) (S .fst)) (z : S .fst)
  : Id (S' .fst)
      (transport (NativeComponent SetTypes S') (u ↦ u .fst .fst)
        (permutation_relabel_map S S' d (component_point SetTypes S)) (component_point SetTypes S')
        (inverse (NativeComponent SetTypes S') (component_point SetTypes S')
          (permutation_relabel_map S S' d (component_point SetTypes S)) (permutation_relabel_point S S' d)) z)
      (equiv_inverse_map (S' .fst) (S .fst) d z)
  ≔ let P ≔ NativeComponent SetTypes S' in let pt ≔ component_point SetTypes S' in
    let kpt ≔ permutation_relabel_map S S' d (component_point SetTypes S) in
    let kp ≔ permutation_relabel_point S S' d in
    let back : S .fst → S' .fst ≔ w ↦ transport P (u ↦ u .fst .fst) kpt pt (inverse P pt kpt kp) w in
    let w ≔ equiv_inverse_map (S' .fst) (S .fst) d z in
    concat (S' .fst) (back z) (back (d .map w)) w
      (refl back (inverse (S .fst) (d .map w) z (equiv_counit (S' .fst) (S .fst) d z)))
      (transport_inverse_roundtrip P (u ↦ u .fst .fst) pt kpt kp w)

def permutation_relabel_action (S S' : SetTypes) (d : Equiv (S' .fst) (S .fst)) (g : USym (permutation_group S))
  (y : S' .fst)
  : Id (S' .fst)
      (permutation_action S' (usym_hom (permutation_group S) (permutation_group S') (permutation_relabel_hom S S' d) g) y)
      (equiv_inverse_map (S' .fst) (S .fst) d (permutation_action S g (d .map y)))
  ≔ let P ≔ NativeComponent SetTypes S' in let pt ≔ component_point SetTypes S' in
    let kpt ≔ permutation_relabel_map S S' d (component_point SetTypes S) in
    let kp ≔ permutation_relabel_point S S' d in
    let pi : P → Type ≔ u ↦ u .fst .fst in
    let a ≔ refl (permutation_relabel_map S S' d) g in
    calc
      permutation_action S' (usym_hom (permutation_group S) (permutation_group S') (permutation_relabel_hom S S' d) g) y
      = transport P pi kpt pt (concat P kpt kpt pt a (inverse P pt kpt kp)) (transport P pi pt kpt kp y)
        by transport_concat P pi pt kpt pt kp (concat P kpt kpt pt a (inverse P pt kpt kp)) y
      = transport P pi kpt pt (inverse P pt kpt kp) (transport P pi kpt kpt a (d .map y))
        by transport_concat P pi kpt kpt pt a (inverse P pt kpt kp) (d .map y)
      = equiv_inverse_map (S' .fst) (S .fst) d (permutation_action S g (d .map y))
        by permutation_relabel_back S S' d (permutation_action S g (d .map y)) ∎

{` Σ_m → Σ_{m+n} and Σ_m → Σ_{mn}: compose _⊔Fin(n) (resp. _×Fin(n)) with
   the isomorphism induced by the identification Fin(m+n) = Fin(m) ⊔ Fin(n)
   (resp. Fin(mn) = Fin(m) × Fin(n)) of module 35. The product
   identification enumerates (a, b) as a + m·b (litmus below), i.e. pairs
   in lexicographic order with the second component as leading key; the
   book leaves this choice open ("somewhat arbitrary"). `}
def fin_sum_identification (m n : Nat) : Equiv (Fin (add m n)) (Sum (Fin m) (Fin n))
  ≔ canonical_inverse_equiv (Sum (Fin m) (Fin n)) (Fin (add m n)) (fin_sum_equiv m n)

def fin_product_identification (m n : Nat) : Equiv (Fin (mul m n)) (Product (Fin m) (Fin n))
  ≔ canonical_inverse_equiv (Product (Fin m) (Fin n)) (Fin (mul m n)) (fin_product_equiv m n)

def symmetric_sum_hom (m n : Nat) : GroupHom (symmetric_group m) (symmetric_group (add m n))
  ≔ group_hom_compose (symmetric_group m) (permutation_group (set_sum_right (standard_set n) (standard_set m)))
      (symmetric_group (add m n))
      (permutation_sum_hom (standard_set m) (standard_set n))
      (permutation_relabel_hom (set_sum_right (standard_set n) (standard_set m)) (standard_set (add m n))
        (fin_sum_identification m n))

def symmetric_product_hom (m n : Nat) : GroupHom (symmetric_group m) (symmetric_group (mul m n))
  ≔ group_hom_compose (symmetric_group m) (permutation_group (set_product_right (standard_set n) (standard_set m)))
      (symmetric_group (mul m n))
      (permutation_product_hom (standard_set m) (standard_set n))
      (permutation_relabel_hom (set_product_right (standard_set n) (standard_set m)) (standard_set (mul m n))
        (fin_product_identification m n))

{` The induced actions on Fin(m+n): the image of g acts on the copy of
   Fin m by g and fixes the copy of Fin n. `}
def symmetric_sum_hom_action (m n : Nat) (g : USym (symmetric_group m)) (y : Fin (add m n))
  : Id (Fin (add m n))
      (permutation_action (standard_set (add m n)) (usym_hom (symmetric_group m) (symmetric_group (add m n)) (symmetric_sum_hom m n) g) y)
      (fin_sum_equiv m n .map
        (permutation_action (set_sum_right (standard_set n) (standard_set m))
          (usym_hom (symmetric_group m) (permutation_group (set_sum_right (standard_set n) (standard_set m)))
            (permutation_sum_hom (standard_set m) (standard_set n)) g)
          (fin_sum_identification m n .map y)))
  ≔ let S ≔ set_sum_right (standard_set n) (standard_set m) in
    let K ≔ symmetric_group (add m n) in
    let f ≔ permutation_sum_hom (standard_set m) (standard_set n) in
    let r ≔ permutation_relabel_hom S (standard_set (add m n)) (fin_sum_identification m n) in
    concat (Fin (add m n))
      (permutation_action (standard_set (add m n)) (usym_hom (symmetric_group m) K (symmetric_sum_hom m n) g) y)
      (permutation_action (standard_set (add m n)) (usym_hom (permutation_group S) K r (usym_hom (symmetric_group m) (permutation_group S) f g)) y)
      (fin_sum_equiv m n .map (permutation_action S (usym_hom (symmetric_group m) (permutation_group S) f g)
        (fin_sum_identification m n .map y)))
      (refl ((q ↦ permutation_action (standard_set (add m n)) q y) : USym K → Fin (add m n))
        (loops_map_compose_pointwise (BG (symmetric_group m)) (BG (permutation_group S)) (BG K)
          (hom_B (symmetric_group m) (permutation_group S) f) (hom_B (permutation_group S) K r) g))
      (permutation_relabel_action S (standard_set (add m n)) (fin_sum_identification m n)
        (usym_hom (symmetric_group m) (permutation_group S) f g) y)

def symmetric_sum_hom_fixes (m n : Nat) (g : USym (symmetric_group m)) (t : Fin n)
  : Id (Fin (add m n))
      (permutation_action (standard_set (add m n)) (usym_hom (symmetric_group m) (symmetric_group (add m n)) (symmetric_sum_hom m n) g)
        (fin_sum_equiv m n .map (inr. t)))
      (fin_sum_equiv m n .map (inr. t))
  ≔ let S ≔ set_sum_right (standard_set n) (standard_set m) in
    let f ≔ permutation_sum_hom (standard_set m) (standard_set n) in
    let e ≔ fin_sum_equiv m n in
    let act : Sum (Fin m) (Fin n) → Sum (Fin m) (Fin n)
      ≔ permutation_action S (usym_hom (symmetric_group m) (permutation_group S) f g) in
    calc
      permutation_action (standard_set (add m n)) (usym_hom (symmetric_group m) (symmetric_group (add m n)) (symmetric_sum_hom m n) g)
        (e .map (inr. t))
      = e .map (act (fin_sum_identification m n .map (e .map (inr. t))))
        by symmetric_sum_hom_action m n g (e .map (inr. t))
      = e .map (act (inr. t))
        by refl ((z ↦ e .map (act z)) : Sum (Fin m) (Fin n) → Fin (add m n))
          (equiv_retraction (Sum (Fin m) (Fin n)) (Fin (add m n)) e (inr. t))
      = e .map (inr. t)
        by refl (e .map) (permutation_sum_hom_action_inr (standard_set m) (standard_set n) g t) ∎

def symmetric_sum_hom_acts (m n : Nat) (g : USym (symmetric_group m)) (a : Fin m)
  : Id (Fin (add m n))
      (permutation_action (standard_set (add m n)) (usym_hom (symmetric_group m) (symmetric_group (add m n)) (symmetric_sum_hom m n) g)
        (fin_sum_equiv m n .map (inl. a)))
      (fin_sum_equiv m n .map (inl. (permutation_action (standard_set m) g a)))
  ≔ let S ≔ set_sum_right (standard_set n) (standard_set m) in
    let f ≔ permutation_sum_hom (standard_set m) (standard_set n) in
    let e ≔ fin_sum_equiv m n in
    let act : Sum (Fin m) (Fin n) → Sum (Fin m) (Fin n)
      ≔ permutation_action S (usym_hom (symmetric_group m) (permutation_group S) f g) in
    calc
      permutation_action (standard_set (add m n)) (usym_hom (symmetric_group m) (symmetric_group (add m n)) (symmetric_sum_hom m n) g)
        (e .map (inl. a))
      = e .map (act (fin_sum_identification m n .map (e .map (inl. a))))
        by symmetric_sum_hom_action m n g (e .map (inl. a))
      = e .map (act (inl. a))
        by refl ((z ↦ e .map (act z)) : Sum (Fin m) (Fin n) → Fin (add m n))
          (equiv_retraction (Sum (Fin m) (Fin n)) (Fin (add m n)) e (inl. a))
      = e .map (inl. (permutation_action (standard_set m) g a))
        by refl (e .map) (permutation_sum_hom_action_inl (standard_set m) (standard_set n) g a) ∎

{` The induced action on Fin(mn): the image of g acts on the first
   component of pairs only. `}
def symmetric_product_hom_action (m n : Nat) (g : USym (symmetric_group m)) (y : Fin (mul m n))
  : Id (Fin (mul m n))
      (permutation_action (standard_set (mul m n)) (usym_hom (symmetric_group m) (symmetric_group (mul m n)) (symmetric_product_hom m n) g) y)
      (fin_product_equiv m n .map
        (permutation_action (set_product_right (standard_set n) (standard_set m))
          (usym_hom (symmetric_group m) (permutation_group (set_product_right (standard_set n) (standard_set m)))
            (permutation_product_hom (standard_set m) (standard_set n)) g)
          (fin_product_identification m n .map y)))
  ≔ let S ≔ set_product_right (standard_set n) (standard_set m) in
    let K ≔ symmetric_group (mul m n) in
    let f ≔ permutation_product_hom (standard_set m) (standard_set n) in
    let r ≔ permutation_relabel_hom S (standard_set (mul m n)) (fin_product_identification m n) in
    concat (Fin (mul m n))
      (permutation_action (standard_set (mul m n)) (usym_hom (symmetric_group m) K (symmetric_product_hom m n) g) y)
      (permutation_action (standard_set (mul m n)) (usym_hom (permutation_group S) K r (usym_hom (symmetric_group m) (permutation_group S) f g)) y)
      (fin_product_equiv m n .map (permutation_action S (usym_hom (symmetric_group m) (permutation_group S) f g)
        (fin_product_identification m n .map y)))
      (refl ((q ↦ permutation_action (standard_set (mul m n)) q y) : USym K → Fin (mul m n))
        (loops_map_compose_pointwise (BG (symmetric_group m)) (BG (permutation_group S)) (BG K)
          (hom_B (symmetric_group m) (permutation_group S) f) (hom_B (permutation_group S) K r) g))
      (permutation_relabel_action S (standard_set (mul m n)) (fin_product_identification m n)
        (usym_hom (symmetric_group m) (permutation_group S) f g) y)

def symmetric_product_hom_acts (m n : Nat) (g : USym (symmetric_group m)) (a : Fin m) (b : Fin n)
  : Id (Fin (mul m n))
      (permutation_action (standard_set (mul m n)) (usym_hom (symmetric_group m) (symmetric_group (mul m n)) (symmetric_product_hom m n) g)
        (fin_product_equiv m n .map (a, b)))
      (fin_product_equiv m n .map (permutation_action (standard_set m) g a, b))
  ≔ let S ≔ set_product_right (standard_set n) (standard_set m) in
    let f ≔ permutation_product_hom (standard_set m) (standard_set n) in
    let e ≔ fin_product_equiv m n in
    let act : Product (Fin m) (Fin n) → Product (Fin m) (Fin n)
      ≔ permutation_action S (usym_hom (symmetric_group m) (permutation_group S) f g) in
    calc
      permutation_action (standard_set (mul m n)) (usym_hom (symmetric_group m) (symmetric_group (mul m n)) (symmetric_product_hom m n) g)
        (e .map (a, b))
      = e .map (act (fin_product_identification m n .map (e .map (a, b))))
        by symmetric_product_hom_action m n g (e .map (a, b))
      = e .map (act (a, b))
        by refl ((z ↦ e .map (act z)) : Product (Fin m) (Fin n) → Fin (mul m n))
          (equiv_retraction (Product (Fin m) (Fin n)) (Fin (mul m n)) e (a, b))
      = e .map (permutation_action (standard_set m) g a, b)
        by refl (e .map) (permutation_product_hom_action (standard_set m) (standard_set n) g a b) ∎
