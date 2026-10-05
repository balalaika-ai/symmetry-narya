export "986-integer-vector-homomorphisms"
export "18-families-and-fibers"
export "34-finite-logic"
export "38-finite-components"
export "145-order-quotient-images"

{` Chapter 9 (subgroups.tex 1186), general n × n integer matrices: fibers
   and cokernels of the homomorphisms int_vec_hom F (module 986) for F a
   composite of factors (module 980: unimodular maps and diagonal maps with
   nonzero entries). Every fiber of B(int_vec_hom F) has merely
   card(F) = Π |diagonal entries| elements: fibers of a composite are sums of
   fibers (so cardinalities multiply), a unimodular factor gives an
   isomorphism (contractible fibers), a diagonal factor is the diag_hom of
   module 966 (identified via winding vectors), whose fiber over the shape
   is known, and all fibers of a classifying map are merely equivalent to
   the one over the shape (BZ^n is connected). Since such F are injective,
   int_vec_hom F is a monomorphism and its cokernel at the shape has
   card(F) elements. `}

{` Factors are additive and injective. `}
def ivh_respect (n : Nat) (F : (Fin n → Int) → Fin n → Int) (x y : Fin n → Int)
  (h : (i : Fin n) → Id Int (x i) (y i)) (i : Fin n) : Id Int (F x i) (F y i)
  ≔ refl ((z ↦ F z i) : (Fin n → Int) → Int) (ivh_vec_path n x y h)

def ivh_factor_additive (n : Nat) (f : IntMatFactor n) : IntVecAdditive n (int_mat_factor_map n f)
  ≔ match f [
  | inl. u ↦ u .snd .snd .fst
  | inr. d ↦ x y i ↦ int_mul_rdistr (x i) (y i) (d .fst i) ]

def int_mat_factors_additive (n : Nat) (l : List (IntMatFactor n)) : IntVecAdditive n (int_mat_factors_eval n l)
  ≔ match l [
  | nil. ↦ x y i ↦ refl (int_add (x i) (y i))
  | cons. f l ↦ x y i ↦
      concat Int (int_mat_factor_map n f (int_mat_factors_eval n l (int_vec_add n x y)) i)
        (int_mat_factor_map n f (int_vec_add n (int_mat_factors_eval n l x) (int_mat_factors_eval n l y)) i)
        (int_add (int_mat_factor_map n f (int_mat_factors_eval n l x) i) (int_mat_factor_map n f (int_mat_factors_eval n l y) i))
        (ivh_respect n (int_mat_factor_map n f) (int_mat_factors_eval n l (int_vec_add n x y))
          (int_vec_add n (int_mat_factors_eval n l x) (int_mat_factors_eval n l y)) (int_mat_factors_additive n l x y) i)
        (ivh_factor_additive n f (int_mat_factors_eval n l x) (int_mat_factors_eval n l y) i) ]

def ivh_int_mul_cancel (d : Int) (nz : IntNonzero d) (a b : Int) (e : Id Int (int_mul a d) (int_mul b d)) : Id Int a b
  ≔ match d [
  | pos. k ↦ match k [
    | zero. ↦ match nz (refl (pos. zero. : Int)) []
    | suc. k ↦ int_mul_cancel_pos k a b e ]
  | neg. k ↦
    calc
      a = int_neg (int_neg a) by inverse Int (int_neg (int_neg a)) a (int_neg_neg a)
      = int_neg (int_neg b) by refl int_neg (int_mul_cancel_pos k (int_neg a) (int_neg b) e)
      = b by int_neg_neg b ∎ ]

def ivh_factor_injective (n : Nat) (f : IntMatFactor n) (x y : Fin n → Int)
  (h : (i : Fin n) → Id Int (int_mat_factor_map n f x i) (int_mat_factor_map n f y i)) (i : Fin n) : Id Int (x i) (y i)
  ≔ match f [
  | inl. u ↦
    let F ≔ u .fst in let G ≔ u .snd .fst in let retr ≔ u .snd .snd .snd .snd in
    calc
      x i = G (F x) i by inverse Int (G (F x) i) (x i) (retr x i)
      = G (F y) i by ivh_respect n G (F x) (F y) h i
      = y i by retr y i ∎
  | inr. d ↦ ivh_int_mul_cancel (d .fst i) (d .snd i) (x i) (y i) (h i) ]

def int_mat_factors_injective (n : Nat) (l : List (IntMatFactor n)) (x y : Fin n → Int)
  (h : (i : Fin n) → Id Int (int_mat_factors_eval n l x i) (int_mat_factors_eval n l y i)) (i : Fin n) : Id Int (x i) (y i)
  ≔ match l [
  | nil. ↦ h i
  | cons. f l ↦ int_mat_factors_injective n l x y
      (ivh_factor_injective n f (int_mat_factors_eval n l x) (int_mat_factors_eval n l y) h) i ]

{` Fibers of a composite: Σ_{u : f⁻¹(z)} g⁻¹(u₁) ≃ (f ∘ g)⁻¹(z). `}
def ivh_path_inverse_equiv (X : Type) (x y : X) : Equiv (Id X x y) (Id X y x)
  ≔ quasi_inverse_equiv (Id X x y) (Id X y x) (inverse X x y) (inverse X y x)
      (r ↦ inverse_inverse X x y r) (r ↦ inverse_inverse X y x r)

def ivh_comp_fiber_equiv (X0 X1 X2 : Type) (g : X0 → X1) (f : X1 → X2) (z : X2)
  : Equiv (Σ (BookFiber X1 X2 f z) (u ↦ BookFiber X0 X1 g (u .fst))) (BookFiber X0 X2 (x ↦ f (g x)) z)
  ≔ let S1 ≔ Σ (BookFiber X1 X2 f z) (u ↦ BookFiber X0 X1 g (u .fst)) in
    let S2 ≔ Σ X0 (x ↦ Σ X1 (y ↦ Product (Id X1 y (g x)) (Id X2 z (f y)))) in
    let S3 ≔ Σ X0 (x ↦ Σ X1 (y ↦ Product (Id X1 (g x) y) (Id X2 z (f y)))) in
    compose_equiv S1 S2 (BookFiber X0 X2 (x ↦ f (g x)) z)
      (quasi_inverse_equiv S1 S2
        (t ↦ (t .snd .fst, (t .fst .fst, (t .snd .snd, t .fst .snd))))
        (s ↦ ((s .snd .fst, s .snd .snd .snd), (s .fst, s .snd .snd .fst)))
        (t ↦ refl t) (s ↦ refl s))
      (compose_equiv S2 S3 (BookFiber X0 X2 (x ↦ f (g x)) z)
        (family_equiv X0 (x ↦ Σ X1 (y ↦ Product (Id X1 y (g x)) (Id X2 z (f y))))
          (x ↦ Σ X1 (y ↦ Product (Id X1 (g x) y) (Id X2 z (f y))))
          (x ↦ family_equiv X1 (y ↦ Product (Id X1 y (g x)) (Id X2 z (f y))) (y ↦ Product (Id X1 (g x) y) (Id X2 z (f y)))
            (y ↦ ch9w2_product_equiv_left (Id X1 y (g x)) (Id X1 (g x) y) (Id X2 z (f y)) (ivh_path_inverse_equiv X1 y (g x)))))
        (family_equiv X0 (x ↦ Σ X1 (y ↦ Product (Id X1 (g x) y) (Id X2 z (f y)))) (x ↦ Id X2 z (f (g x)))
          (x ↦ contract_away_simple X1 (g x) (y ↦ Id X2 z (f y)))))

{` A sum over a set with a elements of sets with b elements has a·b elements. `}
def ivh_sigma_card (A : Type) (P : A → Type) (a b : Nat) (hA : Mere (Equiv A (Fin a)))
  (hP : (u : A) → Mere (Equiv (P u) (Fin b)))
  : Mere (Equiv (Σ A P) (Fin (mul a b)))
  ≔ let T ≔ Equiv (Σ A P) (Fin (mul a b)) in
    let fin : IsFinite A
      ≔ mere_rec (Equiv A (Fin a)) (IsFinite A) (mere_isprop (Σ Nat (k ↦ Id Type A (Fin k))))
          (e ↦ mere (Σ Nat (k ↦ Id Type A (Fin k))) (a, ua A (Fin a) e)) hA in
    mere_rec (Equiv A (Fin a)) (Mere T) (mere_isprop T)
      (e ↦ mere_rec ((u : A) → Equiv (P u) (Fin b)) (Mere T) (mere_isprop T)
        (d ↦ mere T (compose_equiv (Σ A P) (Product (Fin a) (Fin b)) (Fin (mul a b))
               (sigma_equivalences A (Fin a) P (_ ↦ Fin b) e d) (fin_product_equiv a b)))
        (finite_choice A fin (u ↦ Equiv (P u) (Fin b)) hP))
      hA

{` Cardinalities of fibers multiply along composites (g first). `}
def ivh_compose_fiber_card (G H K : Group) (g : GroupHom G H) (f : GroupHom H K) (a b : Nat)
  (hf : (w : BG K .carrier) → Mere (Equiv (HomFiber H K f w) (Fin a)))
  (hg : (y : BG H .carrier) → Mere (Equiv (HomFiber G H g y) (Fin b)))
  (w : BG K .carrier)
  : Mere (Equiv (HomFiber G K (group_hom_compose G H K g f) w) (Fin (mul a b)))
  ≔ let S ≔ Σ (HomFiber H K f w) (u ↦ HomFiber G H g (u .fst)) in
    let T ≔ HomFiber G K (group_hom_compose G H K g f) w in
    let E : Equiv S T ≔ ivh_comp_fiber_equiv (BG G .carrier) (BG H .carrier) (BG K .carrier)
      (hom_function G H g) (hom_function H K f) w in
    mere_rec (Equiv S (Fin (mul a b))) (Mere (Equiv T (Fin (mul a b)))) (mere_isprop (Equiv T (Fin (mul a b))))
      (e ↦ mere (Equiv T (Fin (mul a b))) (compose_equiv T S (Fin (mul a b)) (canonical_inverse_equiv S T E) e))
      (ivh_sigma_card (HomFiber H K f w) (u ↦ HomFiber G H g (u .fst)) a b (hf w) (u ↦ hg (u .fst)))

{` All fibers of a classifying map from the one over the shape. `}
def ivh_fibers_from_shape (G H : Group) (f : GroupHom G H) (c : Nat)
  (h0 : Mere (Equiv (HomFiber G H f (shape H)) (Fin c))) (w : BG H .carrier)
  : Mere (Equiv (HomFiber G H f w) (Fin c))
  ≔ connected_based_elim native_truncation (BG H .carrier) (bg_connected H) (shape H)
      (v ↦ Mere (Equiv (HomFiber G H f v) (Fin c))) (v ↦ mere_isprop (Equiv (HomFiber G H f v) (Fin c))) h0 w

def ivh_shape_fiber_of_cokernel (G H : Group) (f : GroupHom G H) (m : IsGroupMono G H f) (c : Nat)
  (e : Equiv (gset_underlying H (cokernel G H f)) (Fin c))
  : Equiv (HomFiber G H f (shape H)) (Fin c)
  ≔ let F ≔ HomFiber G H f (shape H) in
    compose_equiv F (SetTrunc F) (Fin c)
      (canonical_inverse_equiv (SetTrunc F) F (set_trunc_of_set_equiv F (group_mono_covering G H f m (shape H)))) e

{` Unimodular factors: int_vec_hom F is an isomorphism, its fibers are contractible. `}
def ivh_compose_additive (n : Nat) (F G : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F) (hG : IntVecAdditive n G)
  : IntVecAdditive n (x ↦ F (G x))
  ≔ x y i ↦ concat Int (F (G (int_vec_add n x y)) i) (F (int_vec_add n (G x) (G y)) i) (int_add (F (G x) i) (F (G y) i))
      (ivh_respect n F (G (int_vec_add n x y)) (int_vec_add n (G x) (G y)) (hG x y) i) (hF (G x) (G y) i)

def ivh_identity_additive (n : Nat) : IntVecAdditive n (x ↦ x) ≔ x y i ↦ refl (int_add (x i) (y i))

def ivh_inverse_additive (n : Nat) (F G : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  (sec : (x : Fin n → Int) (i : Fin n) → Id Int (F (G x) i) (x i))
  (retr : (x : Fin n → Int) (i : Fin n) → Id Int (G (F x) i) (x i))
  : IntVecAdditive n G
  ≔ x y i ↦ calc
      G (int_vec_add n x y) i = G (F (int_vec_add n (G x) (G y))) i
        by ivh_respect n G (int_vec_add n x y) (F (int_vec_add n (G x) (G y)))
             (j ↦ calc
               int_add (x j) (y j) = int_add (F (G x) j) (F (G y) j)
                 by refl int_add (inverse Int (F (G x) j) (x j) (sec x j)) (inverse Int (F (G y) j) (y j) (sec y j))
               = F (int_vec_add n (G x) (G y)) j
                 by inverse Int (F (int_vec_add n (G x) (G y)) j) (int_add (F (G x) j) (F (G y) j)) (hF (G x) (G y) j) ∎) i
      = int_add (G x i) (G y i) by retr (int_vec_add n (G x) (G y)) i ∎

def ivh_inverse_hom_path (C : CircleSignature) (n : Nat) (F G : (Fin n → Int) → Fin n → Int)
  (hF : IntVecAdditive n F) (hG : IntVecAdditive n G)
  (sec : (x : Fin n → Int) (i : Fin n) → Id Int (F (G x) i) (x i))
  : Id (BG (int_power_group C n) .carrier → BG (int_power_group C n) .carrier)
      (x ↦ hom_function (int_power_group C n) (int_power_group C n) (int_vec_hom C n F hF)
        (hom_function (int_power_group C n) (int_power_group C n) (int_vec_hom C n G hG) x))
      (x ↦ x)
  ≔ let Zn ≔ int_power_group C n in
    group_hom_function_path Zn Zn (group_hom_compose Zn Zn Zn (int_vec_hom C n G hG) (int_vec_hom C n F hF)) (group_hom_id Zn)
      (calc
        group_hom_compose Zn Zn Zn (int_vec_hom C n G hG) (int_vec_hom C n F hF)
        = int_vec_hom C n (x ↦ F (G x)) (ivh_compose_additive n F G hF hG)
          by inverse (GroupHom Zn Zn) (int_vec_hom C n (x ↦ F (G x)) (ivh_compose_additive n F G hF hG))
               (group_hom_compose Zn Zn Zn (int_vec_hom C n G hG) (int_vec_hom C n F hF))
               (int_vec_hom_compose C n F G hF hG (ivh_compose_additive n F G hF hG))
        = int_vec_hom C n (x ↦ x) (ivh_identity_additive n)
          by int_vec_hom_ext C n (x ↦ F (G x)) (x ↦ x) (ivh_compose_additive n F G hF hG) (ivh_identity_additive n) sec
        = group_hom_id Zn by int_vec_hom_identity C n (ivh_identity_additive n) ∎)

def ivh_unimodular_fibers (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  (u : IntVecUnimodular n F) (w : BG (int_power_group C n) .carrier)
  : Mere (Equiv (HomFiber (int_power_group C n) (int_power_group C n) (int_vec_hom C n F hF) w) (Fin (suc. zero.)))
  ≔ let Zn ≔ int_power_group C n in let B ≔ BG Zn .carrier in
    let G ≔ u .fst in let sec ≔ u .snd .snd .fst in let retr ≔ u .snd .snd .snd in
    let hG ≔ ivh_inverse_additive n F G hF sec retr in
    let f ≔ hom_function Zn Zn (int_vec_hom C n F hF) in
    let g ≔ hom_function Zn Zn (int_vec_hom C n G hG) in
    let eps ≔ happly B (_ ↦ B) (x ↦ f (g x)) (x ↦ x) (ivh_inverse_hom_path C n F G hF hG sec) in
    let eta ≔ happly B (_ ↦ B) (x ↦ g (f x)) (x ↦ x) (ivh_inverse_hom_path C n G F hG hF retr) in
    let Fw ≔ HomFiber Zn Zn (int_vec_hom C n F hF) w in
    let c : BookIsContr Fw ≔ book_quasi_inverse_equiv B B f g eta eps .equiv w in
    mere (Equiv Fw (Fin (suc. zero.)))
      (compose_equiv Fw Unit (Fin (suc. zero.)) (contractible_unit_equiv Fw (native_contraction Fw c))
        (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv))

{` Diagonal factors: int_vec_hom (diag d) is diag_hom d of module 966. `}
def ivh_happly_inverse (I X : Type) (f g : I → X) (p : Id (I → X) f g) (i : I)
  : Id (Id X (g i) (f i)) (happly I (_ ↦ X) g f (inverse (I → X) f g p) i) (inverse X (f i) (g i) (happly I (_ ↦ X) f g p i))
  ≔ J (I → X) f
      (g p ↦ Id (Id X (g i) (f i)) (happly I (_ ↦ X) g f (inverse (I → X) f g p) i) (inverse X (f i) (g i) (happly I (_ ↦ X) f g p i)))
      (concat (Id X (f i) (f i)) (happly I (_ ↦ X) f f (inverse (I → X) f f (refl f)) i) (refl (f i)) (inverse X (f i) (f i) (refl (f i)))
        (refl ((r ↦ happly I (_ ↦ X) f f r i) : Id (I → X) f f → Id X (f i) (f i)) (inverse_refl (I → X) f))
        (inverse (Id X (f i) (f i)) (inverse X (f i) (f i) (refl (f i))) (refl (f i)) (inverse_refl X (f i))))
      g p

def ivh_happly_ap (I X : Type) (φ : I → X → X) (x y : I → X) (p : Id (I → X) x y) (i : I)
  : Id (Id X (φ i (x i)) (φ i (y i)))
      (happly I (_ ↦ X) (j ↦ φ j (x j)) (j ↦ φ j (y j)) (refl ((z ↦ j ↦ φ j (z j)) : (I → X) → I → X) p) i)
      (refl (φ i) (happly I (_ ↦ X) x y p i))
  ≔ J (I → X) x
      (y p ↦ Id (Id X (φ i (x i)) (φ i (y i)))
          (happly I (_ ↦ X) (j ↦ φ j (x j)) (j ↦ φ j (y j)) (refl ((z ↦ j ↦ φ j (z j)) : (I → X) → I → X) p) i)
          (refl (φ i) (happly I (_ ↦ X) x y p i)))
      (refl (refl (φ i (x i)))) y p

def ivh_diag_usym_component (C : CircleSignature) (n : Nat) (d : Fin n → Int) (p : USym (int_power_group C n)) (i : Fin n)
  : Id (USym (circle_group C))
      (happly (Fin n) (_ ↦ C .carrier) (_ ↦ C .base) (_ ↦ C .base)
        (usym_hom (int_power_group C n) (int_power_group C n) (diag_hom C n d) p) i)
      (usym_hom (circle_group C) (circle_group C) (circle_multiplication_hom C (d i))
        (happly (Fin n) (_ ↦ C .carrier) (_ ↦ C .base) (_ ↦ C .base) p i))
  ≔ let X ≔ C .carrier in let b ≔ C .base in let Z ≔ circle_group C in
    let o : Fin n → X ≔ _ ↦ b in
    let m : Fin n → X → X ≔ j ↦ hom_function Z Z (circle_multiplication_hom C (d j)) in
    let Do : Fin n → X ≔ j ↦ m j b in
    let hp : (j : Fin n) → Id X b (m j b) ≔ j ↦ hom_point Z Z (circle_multiplication_hom C (d j)) in
    let P : Id (Fin n → X) o Do ≔ funext (Fin n) (_ ↦ X) o Do hp in
    let A : Id (Fin n → X) Do Do ≔ refl ((z ↦ j ↦ m j (z j)) : (Fin n → X) → Fin n → X) p in
    let IP : Id (Fin n → X) Do o ≔ inverse (Fin n → X) o Do P in
    let pi ≔ happly (Fin n) (_ ↦ X) o o p i in
    let Pi ≔ happly (Fin n) (_ ↦ X) o Do P i in
    calc
      happly (Fin n) (_ ↦ X) o o (concat (Fin n → X) o Do o P (concat (Fin n → X) Do Do o A IP)) i
      = concat X b (m i b) b Pi (happly (Fin n) (_ ↦ X) Do o (concat (Fin n → X) Do Do o A IP) i)
        by ivh_happly_concat (Fin n) X o Do o P (concat (Fin n → X) Do Do o A IP) i
      = concat X b (m i b) b Pi (concat X (m i b) (m i b) b (refl (m i) pi) (inverse X b (m i b) Pi))
        by refl (concat X b (m i b) b Pi)
             (calc
               happly (Fin n) (_ ↦ X) Do o (concat (Fin n → X) Do Do o A IP) i
               = concat X (m i b) (m i b) b (happly (Fin n) (_ ↦ X) Do Do A i) (happly (Fin n) (_ ↦ X) Do o IP i)
                 by ivh_happly_concat (Fin n) X Do Do o A IP i
               = concat X (m i b) (m i b) b (refl (m i) pi) (inverse X b (m i b) Pi)
                 by refl ((u v ↦ concat X (m i b) (m i b) b u v) : Id X (m i b) (m i b) → Id X (m i b) b → Id X (m i b) b)
                      (ivh_happly_ap (Fin n) X m o o p i) (ivh_happly_inverse (Fin n) X o Do P i) ∎)
      = concat X b (m i b) b (hp i) (concat X (m i b) (m i b) b (refl (m i) pi) (inverse X b (m i b) (hp i)))
        by refl ((u ↦ concat X b (m i b) b u (concat X (m i b) (m i b) b (refl (m i) pi) (inverse X b (m i b) u)))
                   : Id X b (m i b) → Id X b b)
             (inverse (Id X b (m i b)) (hp i) Pi (funext_beta (Fin n) (_ ↦ X) o Do hp i)) ∎

def ivh_diag_windings (C : CircleSignature) (n : Nat) (d : Fin n → Int) (p : USym (int_power_group C n)) (i : Fin n)
  : Id Int (int_power_winding C n (usym_hom (int_power_group C n) (int_power_group C n) (diag_hom C n d) p) i)
      (int_diag_map n d (int_power_winding C n p) i)
  ≔ let pi ≔ happly (Fin n) (_ ↦ C .carrier) (_ ↦ C .base) (_ ↦ C .base) p i in
    concat Int (int_power_winding C n (usym_hom (int_power_group C n) (int_power_group C n) (diag_hom C n d) p) i)
      (circle_winding C (usym_hom (circle_group C) (circle_group C) (circle_multiplication_hom C (d i)) pi))
      (int_diag_map n d (int_power_winding C n p) i)
      (refl (circle_winding C) (ivh_diag_usym_component C n d p i))
      (circle_multiplication_winding C (d i) pi)

def ivh_diag_path (C : CircleSignature) (n : Nat) (d : Fin n → Int) (hd : IntVecAdditive n (int_diag_map n d))
  : Id (GroupHom (int_power_group C n) (int_power_group C n)) (int_vec_hom C n (int_diag_map n d) hd) (diag_hom C n d)
  ≔ let Zn ≔ int_power_group C n in let w ≔ int_power_winding C n in
    ivh_hom_ext_windings C n (int_vec_hom C n (int_diag_map n d) hd) (diag_hom C n d)
      (p i ↦ concat Int (w (usym_hom Zn Zn (int_vec_hom C n (int_diag_map n d) hd) p) i) (int_diag_map n d (w p) i)
        (w (usym_hom Zn Zn (diag_hom C n d) p) i)
        (int_vec_hom_windings C n (int_diag_map n d) hd p i)
        (inverse Int (w (usym_hom Zn Zn (diag_hom C n d) p) i) (int_diag_map n d (w p) i) (ivh_diag_windings C n d p i)))

def ivh_diag_fibers (C : CircleSignature) (n : Nat) (d : Fin n → Int) (nz : (i : Fin n) → IntNonzero (d i))
  (hd : IntVecAdditive n (int_diag_map n d)) (w : BG (int_power_group C n) .carrier)
  : Mere (Equiv (HomFiber (int_power_group C n) (int_power_group C n) (int_vec_hom C n (int_diag_map n d) hd) w)
      (Fin (fin_nat_prod n (i ↦ int_abs_nat (d i)))))
  ≔ let Zn ≔ int_power_group C n in let c ≔ fin_nat_prod n (i ↦ int_abs_nat (d i)) in
    transport (GroupHom Zn Zn) (h ↦ (v : BG Zn .carrier) → Mere (Equiv (HomFiber Zn Zn h v) (Fin c)))
      (diag_hom C n d) (int_vec_hom C n (int_diag_map n d) hd)
      (inverse (GroupHom Zn Zn) (int_vec_hom C n (int_diag_map n d) hd) (diag_hom C n d) (ivh_diag_path C n d hd))
      (ivh_fibers_from_shape Zn Zn (diag_hom C n d) c
        (mere (Equiv (HomFiber Zn Zn (diag_hom C n d) (shape Zn)) (Fin c))
          (ivh_shape_fiber_of_cokernel Zn Zn (diag_hom C n d) (diag_mono C n d nz) c (diag_cokernel_card C n d nz))))
      w

{` Every fiber of a factor, then of a list of factors. `}
def ivh_factor_fibers (C : CircleSignature) (n : Nat) (f : IntMatFactor n) (w : BG (int_power_group C n) .carrier)
  : Mere (Equiv (HomFiber (int_power_group C n) (int_power_group C n)
        (int_vec_hom C n (int_mat_factor_map n f) (ivh_factor_additive n f)) w) (Fin (int_mat_factor_card n f)))
  ≔ match f [
  | inl. u ↦ ivh_unimodular_fibers C n (u .fst) (u .snd .snd .fst) (u .snd) w
  | inr. d ↦ ivh_diag_fibers C n (d .fst) (d .snd) (ivh_factor_additive n (inr. d)) w ]

def int_vec_factors_fiber_card (C : CircleSignature) (n : Nat) (l : List (IntMatFactor n)) (w : BG (int_power_group C n) .carrier)
  : Mere (Equiv (HomFiber (int_power_group C n) (int_power_group C n)
        (int_vec_hom C n (int_mat_factors_eval n l) (int_mat_factors_additive n l)) w) (Fin (int_mat_factors_card n l)))
  ≔ let Zn ≔ int_power_group C n in
    match l [
    | nil. ↦ ivh_unimodular_fibers C n (x ↦ x) (int_mat_factors_additive n nil.)
        (x ↦ x, (int_mat_factors_additive n nil., ((x i ↦ refl (x i)), (x i ↦ refl (x i))))) w
    | cons. f l ↦
      let hl ≔ int_vec_hom C n (int_mat_factors_eval n l) (int_mat_factors_additive n l) in
      let hf ≔ int_vec_hom C n (int_mat_factor_map n f) (ivh_factor_additive n f) in
      let c ≔ mul (int_mat_factor_card n f) (int_mat_factors_card n l) in
      transport (GroupHom Zn Zn) (h ↦ Mere (Equiv (HomFiber Zn Zn h w) (Fin c)))
        (group_hom_compose Zn Zn Zn hl hf)
        (int_vec_hom C n (int_mat_factors_eval n (cons. f l)) (int_mat_factors_additive n (cons. f l)))
        (inverse (GroupHom Zn Zn) (int_vec_hom C n (int_mat_factors_eval n (cons. f l)) (int_mat_factors_additive n (cons. f l)))
          (group_hom_compose Zn Zn Zn hl hf)
          (int_vec_hom_compose C n (int_mat_factor_map n f) (int_mat_factors_eval n l) (ivh_factor_additive n f)
            (int_mat_factors_additive n l) (int_mat_factors_additive n (cons. f l))))
        (ivh_compose_fiber_card Zn Zn Zn hl hf (int_mat_factor_card n f) (int_mat_factors_card n l)
          (ivh_factor_fibers C n f) (int_vec_factors_fiber_card C n l) w) ]

{` Monomorphism, and the cokernel at the shape has card elements. `}
def int_vec_factors_hom_good (C : CircleSignature) (n : Nat) (l : List (IntMatFactor n))
  : Product (IsGroupMono (int_power_group C n) (int_power_group C n)
        (int_vec_hom C n (int_mat_factors_eval n l) (int_mat_factors_additive n l)))
      (Mere (Equiv (gset_underlying (int_power_group C n)
          (cokernel (int_power_group C n) (int_power_group C n) (int_vec_hom C n (int_mat_factors_eval n l) (int_mat_factors_additive n l))))
        (Fin (int_mat_factors_card n l))))
  ≔ let Zn ≔ int_power_group C n in
    let h ≔ int_vec_hom C n (int_mat_factors_eval n l) (int_mat_factors_additive n l) in
    let c ≔ int_mat_factors_card n l in
    let m : IsGroupMono Zn Zn h
      ≔ int_vec_hom_mono C n (int_mat_factors_eval n l) (int_mat_factors_additive n l) (int_mat_factors_injective n l) in
    let F ≔ HomFiber Zn Zn h (shape Zn) in
    (m,
     mere_rec (Equiv F (Fin c)) (Mere (Equiv (SetTrunc F) (Fin c))) (mere_isprop (Equiv (SetTrunc F) (Fin c)))
       (e ↦ mere (Equiv (SetTrunc F) (Fin c))
         (compose_equiv (SetTrunc F) F (Fin c) (set_trunc_of_set_equiv F (group_mono_covering Zn Zn h m (shape Zn))) e))
       (int_vec_factors_fiber_card C n l (shape Zn)))
