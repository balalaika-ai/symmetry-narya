export "176-transposition-generation"

{` Maps with contractible fibers are decidable coverings. `}
def equivalence_is_covering (A B : Type) (e : BookEquiv A B) : IsCovering A B (e .map)
  ≔ b ↦ prop_is_set (BookFiber A B (e .map) b)
      (contractible_prop (BookFiber A B (e .map) b) (native_contraction (BookFiber A B (e .map) b) (e .equiv b)))

def equivalence_covering_decidable (A B : Type) (e : BookEquiv A B)
  : (b : B) → DecidableEquality (BookFiber A B (e .map) b)
  ≔ b x y ↦ inl. (contractible_prop (BookFiber A B (e .map) b)
      (native_contraction (BookFiber A B (e .map) b) (e .equiv b)) x y)

def equivalence_connected_decidable_cover (A B : Type) (e : BookEquiv A B) (h : Connected A)
  : ConnectedDecidableCoverings B
  ≔ (((A, (e .map, equivalence_is_covering A B e)), h), equivalence_covering_decidable A B e)

def identity_book_equiv (A : Type) : BookEquiv A A ≔ book_equivalence A A (identity_equiv A)

{` Paths of connected decidable coverings are paths of the underlying maps. `}
def connected_decidable_cover_path (B : Type) (u v : ConnectedDecidableCoverings B)
  (p : Id (MapsInto B) (u .fst .fst .fst, u .fst .fst .snd .fst) (v .fst .fst .fst, v .fst .fst .snd .fst))
  : Id (ConnectedDecidableCoverings B) u v
  ≔ subtype_equal (ConnectedCoverings B) (c ↦ CoveringDecidable B (c .fst))
      (c ↦ covering_decidable_prop B (c .fst)) u v
      (subtype_equal (Coverings B) (c ↦ Connected (c .fst)) (c ↦ connected_isprop (c .fst)) (u .fst) (v .fst)
        (refl ((c ↦ (c .fst .fst, (c .fst .snd, c .snd))) : BundledCovering B → Coverings B)
          (subtype_equal (MapsInto B) (CoveringProperty B) (covering_property_prop B)
            ((u .fst .fst .fst, u .fst .fst .snd .fst), u .fst .fst .snd .snd)
            ((v .fst .fst .fst, v .fst .fst .snd .fst), v .fst .fst .snd .snd) p)))

{` rem:flipthecircle: as connected decidable coverings (S¹, r) = (S¹, id),
   since the reflection r is an equivalence. `}
def circle_flip_cover (C : CircleSignature) : ConnectedDecidableCoverings (C .carrier)
  ≔ equivalence_connected_decidable_cover (C .carrier) (C .carrier) (circle_reflection_equiv C) (native_circle_connected C)

def circle_identity_cover (C : CircleSignature) : ConnectedDecidableCoverings (C .carrier)
  ≔ equivalence_connected_decidable_cover (C .carrier) (C .carrier) (identity_book_equiv (C .carrier)) (native_circle_connected C)

def circle_flip_cover_map (C : CircleSignature)
  : Id (C .carrier → C .carrier) (circle_flip_cover C .fst .fst .snd .fst) (circle_reflection C)
  ≔ refl (circle_reflection C)

def circle_flip_identity_cover (C : CircleSignature)
  : Id (ConnectedDecidableCoverings (C .carrier)) (circle_flip_cover C) (circle_identity_cover C)
  ≔ connected_decidable_cover_path (C .carrier) (circle_flip_cover C) (circle_identity_cover C)
      (precompose_equivalence_path (C .carrier) (C .carrier) (C .carrier)
        (native_equivalence (C .carrier) (C .carrier) (circle_reflection_equiv C)) (identity (C .carrier)))

{` Degree of maps of the circle is multiplicative under composition. `}
def circle_map_general_winding (C : CircleSignature) (g : C .carrier → C .carrier) (x : C .carrier)
  (p : Id (C .carrier) x x)
  : Id Int (circle_general_winding C (g x) (refl g p)) (int_mul (circle_map_degree C g) (circle_general_winding C x p))
  ≔ circle_ind_prop C
      (x ↦ (p : Id (C .carrier) x x) →
        Id Int (circle_general_winding C (g x) (refl g p)) (int_mul (circle_map_degree C g) (circle_general_winding C x p)))
      (x ↦ pi_prop (Id (C .carrier) x x)
        (p ↦ Id Int (circle_general_winding C (g x) (refl g p)) (int_mul (circle_map_degree C g) (circle_general_winding C x p)))
        (p ↦ int_set (circle_general_winding C (g x) (refl g p)) (int_mul (circle_map_degree C g) (circle_general_winding C x p))))
      (p ↦ calc
        circle_general_winding C (g (C .base)) (refl g p)
        = circle_general_winding C (g (C .base)) (refl g (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p)))
          by refl ((q ↦ circle_general_winding C (g (C .base)) (refl g q)) : Id (C .carrier) (C .base) (C .base) → Int)
            (inverse (Id (C .carrier) (C .base) (C .base))
              (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p)) p (circle_power_winding C p))
        = int_mul (circle_map_degree C g) (circle_winding C p) by circle_map_winding_power C g (circle_winding C p)
        = int_mul (circle_map_degree C g) (circle_general_winding C (C .base) p)
          by refl (int_mul (circle_map_degree C g))
            (inverse Int (circle_general_winding C (C .base) p) (circle_winding C p) (circle_general_winding_base_value C p)) ∎)
      x p

def circle_map_degree_compose (C : CircleSignature) (g f : C .carrier → C .carrier)
  : Id Int (circle_map_degree C (compose (C .carrier) (C .carrier) (C .carrier) g f))
      (int_mul (circle_map_degree C g) (circle_map_degree C f))
  ≔ circle_map_general_winding C g (f (C .base)) (refl f (C .loop))

def circle_degree_map_degree (C : CircleSignature) (m : Nat)
  : Id Int (circle_map_degree C (circle_degree_map C m)) (pos. m)
  ≔ calc
      circle_map_degree C (circle_degree_map C m)
      = circle_general_winding C (C .base) (loop_power_nat (C .carrier) (C .base) (C .loop) m)
        by circle_degree_rec C (C .base) (loop_power_nat (C .carrier) (C .base) (C .loop) m)
      = circle_winding C (loop_power_nat (C .carrier) (C .base) (C .loop) m)
        by circle_general_winding_base_value C (loop_power_nat (C .carrier) (C .base) (C .loop) m)
      = (pos. m : Int) by circle_winding_power C (pos. m) ∎

{` rem:flipthecircle, last sentence, for positive m = suc n: dg_m r and dg_m
   give the same connected covering, while as maps they differ (degrees
   -m and m). `}
def degree_flip_cover (C : CircleSignature) (n : Nat) : Coverings (C .carrier)
  ≔ (C .carrier, (compose (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (circle_reflection C),
      precompose_equivalence_covering (C .carrier) (C .carrier) (C .carrier)
        (native_equivalence (C .carrier) (C .carrier) (circle_reflection_equiv C)) (circle_degree_map C (suc. n))
        (circle_degree_is_covering C (suc. n) (lt_to_book zero. (suc. n) star.))))

def degree_flip_cover_path (C : CircleSignature) (n : Nat)
  : Id (Coverings (C .carrier)) (degree_flip_cover C n)
      (circle_degree_cover C (suc. n) (lt_to_book zero. (suc. n) star.))
  ≔ precompose_equivalence_covering_path (C .carrier) (C .carrier) (C .carrier)
      (native_equivalence (C .carrier) (C .carrier) (circle_reflection_equiv C)) (circle_degree_map C (suc. n))
      (circle_degree_is_covering C (suc. n) (lt_to_book zero. (suc. n) star.))

def degree_flip_degree (C : CircleSignature) (n : Nat)
  : Id Int (circle_map_degree C (compose (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (circle_reflection C)))
      (neg. n)
  ≔ calc
      circle_map_degree C (compose (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (circle_reflection C))
      = int_mul (circle_map_degree C (circle_degree_map C (suc. n))) (circle_map_degree C (circle_reflection C))
        by circle_map_degree_compose C (circle_degree_map C (suc. n)) (circle_reflection C)
      = int_mul (pos. (suc. n)) (circle_map_degree C (circle_reflection C))
        by refl ((k ↦ int_mul k (circle_map_degree C (circle_reflection C))) : Int → Int) (circle_degree_map_degree C (suc. n))
      = int_mul (pos. (suc. n)) (neg. zero.) by refl (int_mul (pos. (suc. n))) (circle_degree_reflection C)
      = (neg. n : Int) by refl (neg. n : Int) ∎

def degree_flip_maps_differ (C : CircleSignature) (n : Nat)
  (p : Id (C .carrier → C .carrier)
    (compose (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (circle_reflection C))
    (circle_degree_map C (suc. n))) : Empty
  ≔ int_encode (neg. n) (pos. (suc. n)) (calc
      (neg. n : Int)
      = circle_map_degree C (compose (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (circle_reflection C))
        by inverse Int (circle_map_degree C (compose (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C (suc. n)) (circle_reflection C)))
          (neg. n) (degree_flip_degree C n)
      = circle_map_degree C (circle_degree_map C (suc. n)) by refl (circle_map_degree C) p
      = (pos. (suc. n) : Int) by circle_degree_map_degree C (suc. n) ∎)

{` rem:bang: the commutation type of a power with the permutation is a
   proposition for a set, so its witness need not be named. `}
def power_commutation_prop (A : Type) (hA : isSet A) (e : Equiv A A) (z : Int)
  : isProp (Id (A → A) (compose A A A (permutation_power A e z) (e .map)) (compose A A A (e .map) (permutation_power A e z)))
  ≔ pi_set A (_ ↦ A) (_ ↦ hA) (compose A A A (permutation_power A e z) (e .map)) (compose A A A (e .map) (permutation_power A e z))
