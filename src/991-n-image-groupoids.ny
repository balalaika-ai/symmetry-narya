export "230-higher-images"
export "25-coverings"

{` Chapter 9 (subgroups.tex), rem:n-im-ptd-map: "if X and Z are
   connected groupoids, then so is Σ_{z:Z} ‖f⁻¹(z)‖_n" for every n ≥ -1 (module 939 has n = 0). Needs that the
   truncation of a groupoid is a groupoid (for n ≥ 1 the truncation does nothing). `}

{` For an n-type A (HLevel (k+1)) the unit A → ‖A‖_k is an equivalence. `}
def trunc_level_unit_equiv (k : Nat) (A : Type) (hA : HLevel (suc. k) A) : Equiv A (Trunc k A)
  ≔ let R ≔ truncation k A in
    let u ≔ trunc_unit k A in
    let r ≔ trunc_extend k A R A hA (identity A) in
    let beta : (a : A) → Id A (r (u a)) a ≔ a ↦ inverse A a (r (u a)) (trunc_extend_beta k A R A hA (identity A) a) in
    quasi_inverse_equiv A (Trunc k A) u r beta
      (x ↦ refl ((φ ↦ φ x) : (Trunc k A → Trunc k A) → Trunc k A)
        (trunc_maps_equal k A R (Trunc k A) (trunc_level k A) (y ↦ u (r y)) (identity (Trunc k A))
          (a ↦ refl u (beta a))))

def hlevel_raise_from_three (n : Nat) (A : Type) (h : HLevel (suc. (suc. (suc. zero.))) A) : HLevel (suc. (suc. (suc. n))) A
  ≔ match n [
  | zero. ↦ h
  | suc. m ↦ hlevel_raise (suc. (suc. (suc. m))) A (hlevel_raise_from_three m A h) ]

def trunc_groupoid_of_groupoid (k : Nat) (A : Type) (h : HLevel (suc. (suc. (suc. zero.))) A)
  : HLevel (suc. (suc. (suc. zero.))) (Trunc k A)
  ≔ match k [
  | zero. ↦ hlevel_raise (suc. (suc. zero.)) (Trunc zero. A) (hlevel_raise (suc. zero.) (Trunc zero. A) (trunc_level zero. A))
  | suc. k1 ↦ match k1 [
    | zero. ↦ hlevel_raise (suc. (suc. zero.)) (Trunc (suc. zero.) A) (trunc_level (suc. zero.) A)
    | suc. k2 ↦ match k2 [
      | zero. ↦ trunc_level (suc. (suc. zero.)) A
      | suc. k3 ↦ hlevel_equiv (suc. (suc. (suc. zero.))) A (Trunc (suc. (suc. (suc. k3))) A)
          (trunc_level_unit_equiv (suc. (suc. (suc. k3))) A (hlevel_raise_from_three (suc. k3) A h)) h ] ] ]

{` rem:n-im-ptd-map: the n-image (n = k - 1) of a map between connected groupoids is a connected groupoid. `}
def n_image_connected_groupoid (k : Nat) (X Z : Type) (f : X → Z)
  (hX : Connected X) (gX : isGroupoid X) (gZ : isGroupoid Z)
  : Product (Connected (NImage k X Z f)) (isGroupoid (NImage k X Z f))
  ≔ let three : Nat ≔ suc. (suc. (suc. zero.)) in
    let fib_level : (b : Z) → HLevel three (BookFiber X Z f b)
      ≔ b ↦ hlevel_sigma three X (x ↦ Id Z b (f x)) (groupoid_to_hlevel X gX)
          (x ↦ hlevel_raise (suc. (suc. zero.)) (Id Z b (f x)) (set_to_hlevel_two (Id Z b (f x)) (gZ b (f x)))) in
    (n_image_connected k X Z f hX,
     hlevel_to_groupoid (NImage k X Z f)
       (hlevel_sigma three Z (b ↦ Trunc k (BookFiber X Z f b)) (groupoid_to_hlevel Z gZ)
         (b ↦ trunc_groupoid_of_groupoid k (BookFiber X Z f b) (fib_level b))))
