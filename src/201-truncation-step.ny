export "200-truncation-structures"

{` def:join-construction-of-truncation, inductive step.  Given all
   (k-1)-truncations R, the k-truncation of A is the image of
   I : A → (A → NTypes k), x ↦ (y ↦ ‖x = y‖). `}
def trunc_path_family (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x : A) : A → NTypes k
  ≔ y ↦ (R (Id A x y) .carrier, R (Id A x y) .level)

def TruncStep (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) : Type
  ≔ Image A (A → NTypes k) (trunc_path_family k R A)

def trunc_step_unit (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) : A → TruncStep k R A
  ≔ image_factor A (A → NTypes k) (trunc_path_family k R A)

def trunc_step_level (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type)
  : HLevel (suc. (suc. k)) (TruncStep k R A)
  ≔ hlevel_sigma (suc. (suc. k)) (A → NTypes k) (P ↦ Mere (BookFiber A (A → NTypes k) (trunc_path_family k R A) P))
      (hlevel_function (suc. (suc. k)) A (NTypes k) (ntypes_level k))
      (P ↦ prop_hlevel (suc. k) (Mere (BookFiber A (A → NTypes k) (trunc_path_family k R A) P))
        (mere_isprop (BookFiber A (A → NTypes k) (trunc_path_family k R A) P)))

def trunc_step_code (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (z : A) (w : TruncStep k R A) : Type
  ≔ w .fst z .fst

{` The canonical map (x = y) → (|x| = |y|), defined by path induction as
   transport of refl.  (The ap-based form raised bug[E0500] in Narya efafad2
   when written with the J base case inline; the trigger is an inline base case
   containing inverse_refl, see tests/narya/e0500-truncation-step.ny.
   This transport form avoids it.) `}
def trunc_step_path_gen (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x y : A) (r : Id A x y)
  : Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y)
  ≔ transport A (z ↦ Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A z)) x y r
      (refl (trunc_step_unit k R A x))

{` The map of eq:trunc-path-eq, induced by the universal property. `}
def trunc_step_path_map (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x y : A)
  : R (Id A x y) .carrier → Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y)
  ≔ trunc_extend k (Id A x y) (R (Id A x y)) (Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y))
      (trunc_step_level k R A (trunc_step_unit k R A x) (trunc_step_unit k R A y))
      (trunc_step_path_gen k R A x y)

def trunc_step_decode (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x y : A)
  (p : Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y)) : R (Id A x y) .carrier
  ≔ transport (TruncStep k R A) (trunc_step_code k R A y) (trunc_step_unit k R A y) (trunc_step_unit k R A x)
      (inverse (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y) p) (R (Id A y y) .unit_map (refl y))

def trunc_step_decode_base (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x : A)
  : Id (R (Id A x x) .carrier) (trunc_step_decode k R A x x (trunc_step_path_gen k R A x x (refl x))) (R (Id A x x) .unit_map (refl x))
  ≔ let C ≔ TruncStep k R A in let u ≔ trunc_step_unit k R A in
    calc
        trunc_step_decode k R A x x (trunc_step_path_gen k R A x x (refl x))
        = trunc_step_decode k R A x x (refl (u x))
          by refl (trunc_step_decode k R A x x) (transport_refl A (z ↦ Id C (u x) (u z)) x (refl (u x)))
        = transport C (trunc_step_code k R A x) (u x) (u x) (refl (u x)) (R (Id A x x) .unit_map (refl x))
          by refl ((q ↦ transport C (trunc_step_code k R A x) (u x) (u x) q (R (Id A x x) .unit_map (refl x)))
              : Id C (u x) (u x) → R (Id A x x) .carrier)
            (inverse_refl C (u x))
        = R (Id A x x) .unit_map (refl x)
          by transport_refl C (trunc_step_code k R A x) (u x) (R (Id A x x) .unit_map (refl x)) ∎

{` Written to avoid bug[E0500] in Narya efafad2, whose trigger is an inline J
   base case containing inverse_refl (tests/narya/e0500-truncation-step.ny;
   a separate definition for the base case also works). `}
def trunc_step_decode_ap (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x y : A) (r : Id A x y)
  : Id (R (Id A x y) .carrier) (trunc_step_decode k R A x y (trunc_step_path_gen k R A x y r)) (R (Id A x y) .unit_map r)
  ≔ J A x (y r ↦ Id (R (Id A x y) .carrier) (trunc_step_decode k R A x y (trunc_step_path_gen k R A x y r)) (R (Id A x y) .unit_map r))
      (trunc_step_decode_base k R A x) y r

def trunc_step_section (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x y : A) (v : R (Id A x y) .carrier)
  : Id (R (Id A x y) .carrier) (trunc_step_decode k R A x y (trunc_step_path_map k R A x y v)) v
  ≔ let X ≔ R (Id A x y) .carrier in
    let C ≔ TruncStep k R A in let u ≔ trunc_step_unit k R A in
    let G ≔ trunc_step_path_map k R A x y in
    let F ≔ trunc_step_decode k R A x y in
    trunc_induction k (Id A x y) (R (Id A x y)) (w ↦ Id X (F (G w)) w)
      (w ↦ hlevel_raise k (Id X (F (G w)) w) (R (Id A x y) .level (F (G w)) w))
      (r ↦ concat X (F (G (R (Id A x y) .unit_map r))) (F (trunc_step_path_gen k R A x y r)) (R (Id A x y) .unit_map r)
        (refl F (inverse (Id C (u x) (u y)) (trunc_step_path_gen k R A x y r) (G (R (Id A x y) .unit_map r))
          (trunc_extend_beta k (Id A x y) (R (Id A x y)) (Id C (u x) (u y)) (trunc_step_level k R A (u x) (u y))
            (trunc_step_path_gen k R A x y) r)))
        (trunc_step_decode_ap k R A x y r))
      v

{` Identifications in the image are determined by the induced
   identifications of the code types (subtype, funext, NTypes subtype). `}
def trunc_step_code_paths_injective (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type)
  (w1 w2 : TruncStep k R A)
  : PathReflecting (Id (TruncStep k R A) w1 w2)
      ((z : A) → Id Type (trunc_step_code k R A z w1) (trunc_step_code k R A z w2))
      (q z ↦ refl (trunc_step_code k R A z) q)
  ≔ let C ≔ TruncStep k R A in let T ≔ NTypes k in
    let I ≔ trunc_path_family k R A in
    let M : (A → T) → Type ≔ P ↦ Mere (BookFiber A (A → T) I P) in
    p q h ↦
      equivalence_injective (Id C w1 w2) (Id (A → T) (w1 .fst) (w2 .fst))
        (subtype_path_equiv (A → T) M (P ↦ mere_isprop (BookFiber A (A → T) I P)) w1 w2) p q
        (equivalence_injective (Id (A → T) (w1 .fst) (w2 .fst)) (Homotopy A (_ ↦ T) (w1 .fst) (w2 .fst))
          (function_extensionality A (_ ↦ T) (w1 .fst) (w2 .fst)) (p .fst) (q .fst)
          (funext A (z ↦ Id T (w1 .fst z) (w2 .fst z)) (happly A (_ ↦ T) (w1 .fst) (w2 .fst) (p .fst))
            (happly A (_ ↦ T) (w1 .fst) (w2 .fst) (q .fst))
            (z ↦ equivalence_injective (Id T (w1 .fst z) (w2 .fst z)) (Id Type (w1 .fst z .fst) (w2 .fst z .fst))
              (subtype_path_equiv Type (HLevel (suc. k)) (Z ↦ hlevel_isprop (suc. k) Z) (w1 .fst z) (w2 .fst z))
              (p .fst (refl z)) (q .fst (refl z)) (h (refl z)))))

def trunc_step_decode_injective (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x y : A)
  : PathReflecting (Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y)) (R (Id A x y) .carrier)
      (trunc_step_decode k R A x y)
  ≔ let C ≔ TruncStep k R A in let u ≔ trunc_step_unit k R A in
    let Rx : A → Type ≔ z ↦ R (Id A x z) .carrier in
    let Ry : A → Type ≔ z ↦ R (Id A y z) .carrier in
    let K : Id C (u x) (u y) → (z : A) → Ry z → Rx z
      ≔ p z ↦ transport C (trunc_step_code k R A z) (u y) (u x) (inverse C (u x) (u y) p) in
    p q h ↦
      let hY ≔ equivalence_injective (YonedaSections A Rx y) (Rx y) (yoneda_evaluation_equiv A Rx y)
        (z r ↦ K p z (R (Id A y z) .unit_map r)) (z r ↦ K q z (R (Id A y z) .unit_map r)) h in
      let hK ≔ pi_injective A (z ↦ Ry z → Rx z) (z ↦ Id A y z → Rx z)
        (z m ↦ compose (Id A y z) (Ry z) (Rx z) m (R (Id A y z) .unit_map))
        (z ↦ equivalence_injective (Ry z → Rx z) (Id A y z → Rx z)
          (trunc_precompose_equiv k (Id A y z) (R (Id A y z)) (Rx z) (R (Id A x z) .level)))
        (K p) (K q) hY in
      let hT ≔ pi_injective A (z ↦ Id Type (Ry z) (Rx z)) (z ↦ Ry z → Rx z)
        (z Q ↦ transport Type (Z ↦ Z) (Ry z) (Rx z) Q)
        (z ↦ type_path_transport_injective (Ry z) (Rx z))
        (z ↦ refl (trunc_step_code k R A z) (inverse C (u x) (u y) p))
        (z ↦ refl (trunc_step_code k R A z) (inverse C (u x) (u y) q)) hK in
      inverse_injective C (u x) (u y) p q
        (trunc_step_code_paths_injective k R A (u y) (u x) (inverse C (u x) (u y) p) (inverse C (u x) (u y) q) hT)

{` eq:trunc-path-eq: the induced map ‖x = y‖ → (|x| = |y|) is an equivalence. `}
def trunc_step_path_equiv (k : Nat) (R : (X : Type) → TruncStructure k X) (A : Type) (x y : A)
  : Equiv (R (Id A x y) .carrier) (Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y))
  ≔ quasi_inverse_equiv (R (Id A x y) .carrier) (Id (TruncStep k R A) (trunc_step_unit k R A x) (trunc_step_unit k R A y))
      (trunc_step_path_map k R A x y) (trunc_step_decode k R A x y) (trunc_step_section k R A x y)
      (p ↦ trunc_step_decode_injective k R A x y (trunc_step_path_map k R A x y (trunc_step_decode k R A x y p)) p
        (trunc_step_section k R A x y (trunc_step_decode k R A x y p)))
