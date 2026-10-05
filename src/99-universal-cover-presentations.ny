export "98-pointed-universal-coverings"

def path_cover_pointed (B : Pointed) : Pointed
  ≔ (Σ (B .carrier) (b ↦ Id (B .carrier) (B .point) b), (B .point, refl (B .point)))

def book_pointed_path_projection (B : Pointed) : BookPointedMap (path_cover_pointed B) B
  ≔ (t ↦ t .fst, refl (B .point))

def pointed_path_cover (B : Pointed) (groupoid : isGroupoid (B .carrier)) : BookPointedCoverings B
  ≔ (path_cover_pointed B, (book_pointed_path_projection B, path_cover (B .carrier) groupoid (B .point) .snd .snd))

def pointed_path_cover_universal (B : Pointed) (groupoid : isGroupoid (B .carrier))
  : IsUniversalPointedCover (path_cover_pointed B) B (book_pointed_path_projection B)
  ≔ contractible_cover_universal (path_cover_pointed B) B (book_pointed_path_projection B)
      (book_pathspace_contractible (B .carrier) (B .point))

def unit_path_cover_equiv (B : Pointed) : Equiv Unit (path_cover_pointed B .carrier)
  ≔ quasi_inverse_equiv Unit (path_cover_pointed B .carrier)
      (constant Unit (path_cover_pointed B .carrier) (path_cover_pointed B .point))
      (constant (path_cover_pointed B .carrier) Unit star.)
      (u ↦ unit_prop star. u) (book_pathspace_contractible (B .carrier) (B .point) .contract)

def unit_path_cover_pointed_map (B : Pointed) : BookPointedMap pointed_unit (path_cover_pointed B)
  ≔ (unit_path_cover_equiv B .map, refl (path_cover_pointed B .point))

def unit_path_cover_pointed_triangle (B : Pointed)
  : Id (BookPointedMap pointed_unit B)
      (book_pointed_compose pointed_unit (path_cover_pointed B) B (unit_path_cover_pointed_map B) (book_pointed_path_projection B))
      (book_pointed_constant pointed_unit B)
  ≔ (refl (constant Unit (B .carrier) (B .point)), concat_1p (B .carrier) (B .point) (B .point) (refl (B .point)))

def finite_one_pointed : Pointed ≔ (Fin (suc. zero.), inr. star.)
def finite_one_contractible : BookIsContr (finite_one_pointed .carrier)
  ≔ book_contraction (Fin (suc. zero.))
      (contractible_domain_of_equiv (Fin (suc. zero.)) Unit fin_one_equiv unit_contractible)

def finite_one_path_cover_equiv (B : Pointed) : Equiv (finite_one_pointed .carrier) (path_cover_pointed B .carrier)
  ≔ compose_equiv (Fin (suc. zero.)) Unit (path_cover_pointed B .carrier) fin_one_equiv (unit_path_cover_equiv B)

def finite_one_path_cover_pointed_map (B : Pointed) : BookPointedMap finite_one_pointed (path_cover_pointed B)
  ≔ (finite_one_path_cover_equiv B .map, refl (path_cover_pointed B .point))

def finite_one_path_cover_pointed_triangle (B : Pointed)
  : Id (BookPointedMap finite_one_pointed B)
      (book_pointed_compose finite_one_pointed (path_cover_pointed B) B
        (finite_one_path_cover_pointed_map B) (book_pointed_path_projection B))
      (book_pointed_constant finite_one_pointed B)
  ≔ (refl (constant (Fin (suc. zero.)) (B .carrier) (B .point)),
      concat_1p (B .carrier) (B .point) (B .point) (refl (B .point)))

def constant_finite_one_cover (B : Pointed) (groupoid : isGroupoid (B .carrier)) : BookPointedCoverings B
  ≔ (finite_one_pointed, (book_pointed_constant finite_one_pointed B,
      b ↦ sigma_set (Fin (suc. zero.)) (_ ↦ Id (B .carrier) b (B .point))
        (fin_set (suc. zero.)) (_ ↦ groupoid b (B .point))))

{` def:universalcover, the book's constant Fin 1 map. With the path projection
   (above) and the constant Unit map (constant_unit_cover_universal, module 285)
   all three pointed presentations are universal. `}
def constant_finite_one_cover_universal (B : Pointed) (groupoid : isGroupoid (B .carrier))
  : IsUniversalPointedCover finite_one_pointed B (book_pointed_constant finite_one_pointed B)
  ≔ contractible_cover_universal finite_one_pointed B (book_pointed_constant finite_one_pointed B) finite_one_contractible

def book_circle_exponential_map (C : CircleSignature)
  : BookPointedMap (circle_integer_total_pointed C) (circle_pointed C)
  ≔ (t ↦ t .fst, refl (C .base))

def circle_exponential_pointing_comparison (C : CircleSignature)
  : Id (BookPointedMap (circle_integer_total_pointed C) (circle_pointed C))
      (native_pointed_to_book (circle_integer_total_pointed C) (circle_pointed C) (circle_exponential_map C))
      (book_circle_exponential_map C)
  ≔ (refl ((t ↦ t .fst) : circle_integer_total_pointed C .carrier → C .carrier), inverse_refl (C .carrier) (C .base))

def circle_integer_book_pointed_cover (C : CircleSignature) : BookPointedCoverings (circle_pointed C)
  ≔ (circle_integer_total_pointed C,
      (book_circle_exponential_map C, circle_integer_cover C .snd .snd))

{` cor:univ-covers-S1, both actual pointed coverings. `}
def circle_path_cover_universal (C : CircleSignature)
  : IsUniversalPointedCover (path_cover_pointed (circle_pointed C)) (circle_pointed C)
      (book_pointed_path_projection (circle_pointed C))
  ≔ pointed_path_cover_universal (circle_pointed C) (circle_groupoid C)

def circle_integer_cover_universal (C : CircleSignature)
  : IsUniversalPointedCover (circle_integer_total_pointed C) (circle_pointed C)
      (book_circle_exponential_map C)
  ≔ contractible_cover_universal (circle_integer_total_pointed C) (circle_pointed C)
      (book_circle_exponential_map C) (circle_integer_total_contractible C)
