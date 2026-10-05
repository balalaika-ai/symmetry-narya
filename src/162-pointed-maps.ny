export "161-subtypes-and-hedberg"

{` Pointed maps use the book orientation pt_Y = f(pt_X) of
   BookPointedMap from 98. The book composite h(pt_X)·f_pt first follows
   f_pt and then h(pt_X). `}
def PointedHomotopy (X Y : Pointed) (f g : BookPointedMap X Y) : Type
  ≔ Σ (Homotopy (X .carrier) (_ ↦ Y .carrier) (f .fst) (g .fst))
      (h ↦ Id (Id (Y .carrier) (Y .point) (g .fst (X .point)))
        (concat (Y .carrier) (Y .point) (f .fst (X .point)) (g .fst (X .point)) (f .snd) (h (X .point)))
        (g .snd))

{` con:identity-ptd-maps, by the displayed chain: pairs of paths,
   transport in T(k) = (pt_Y = k(pt_X)), and function extensionality. `}
def pointed_map_path_equiv (X Y : Pointed) (f g : BookPointedMap X Y)
  : Equiv (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g)
  ≔ let A ≔ X .carrier in
    let B ≔ Y .carrier in
    let T : (A → B) → Type ≔ k ↦ Id B (Y .point) (k (X .point)) in
    let E ≔ Id (A → B) (f .fst) (g .fst) in
    let H ≔ Homotopy A (_ ↦ B) (f .fst) (g .fst) in
    let P : H → Type ≔ h ↦ Id (Id B (Y .point) (g .fst (X .point)))
      (concat B (Y .point) (f .fst (X .point)) (g .fst (X .point)) (f .snd) (h (X .point))) (g .snd) in
    compose_equiv (Id (BookPointedMap X Y) f g) (SigmaPath (A → B) T f g) (PointedHomotopy X Y f g)
      (canonical_inverse_equiv (SigmaPath (A → B) T f g) (Id (BookPointedMap X Y) f g)
        (sigma_path_equiv (A → B) T f g))
      (compose_equiv (SigmaPath (A → B) T f g) (Σ E (e ↦ P (happly A (_ ↦ B) (f .fst) (g .fst) e)))
        (PointedHomotopy X Y f g)
        (family_equiv E (e ↦ Id T e (f .snd) (g .snd)) (e ↦ P (happly A (_ ↦ B) (f .fst) (g .fst) e))
          (e ↦ pathover_transport_equiv (A → B) T (f .fst) (g .fst) e (f .snd) (g .snd)))
        (sigma_pullback_equiv E H (function_extensionality A (_ ↦ B) (f .fst) (g .fst)) P))

{` xca:identity-ptd-maps: the same kind of map, defined by induction on
   the path; it is an equivalence because both total spaces over g are
   contractible. `}
def pointed_map_path_homotopy (X Y : Pointed) (f g : BookPointedMap X Y)
  (p : Id (BookPointedMap X Y) f g) : PointedHomotopy X Y f g
  ≔ J (BookPointedMap X Y) f (g _ ↦ PointedHomotopy X Y f g)
      (x ↦ refl (f .fst x), concat_p1 (Y .carrier) (Y .point) (f .fst (X .point)) (f .snd)) g p

def pointed_homotopy_total_contractible (X Y : Pointed) (f : BookPointedMap X Y)
  : BookIsContr (Σ (BookPointedMap X Y) (g ↦ PointedHomotopy X Y f g))
  ≔ book_contractibility_equiv (Σ (BookPointedMap X Y) (g ↦ Id (BookPointedMap X Y) f g))
      (Σ (BookPointedMap X Y) (g ↦ PointedHomotopy X Y f g))
      (family_equiv (BookPointedMap X Y) (g ↦ Id (BookPointedMap X Y) f g)
        (g ↦ PointedHomotopy X Y f g) (g ↦ pointed_map_path_equiv X Y f g))
      .map (book_contraction (Σ (BookPointedMap X Y) (g ↦ Id (BookPointedMap X Y) f g))
        (iscontr_idfrom (BookPointedMap X Y) f))

def contractible_map_equiv (A B : Type) (f : A → B) (hA : BookIsContr A) (hB : BookIsContr B)
  : isEquiv A B f
  ≔ native_equivalence A B (f, b ↦ contractible_map_book_fiber A B f hA hB b) .equiv

def pointed_map_path_homotopy_equiv (X Y : Pointed) (f g : BookPointedMap X Y)
  : isEquiv (Id (BookPointedMap X Y) f g) (PointedHomotopy X Y f g) (pointed_map_path_homotopy X Y f g)
  ≔ let M ≔ BookPointedMap X Y in
    fiberwise_from_total M (g ↦ Id M f g) (g ↦ PointedHomotopy X Y f g)
      (g ↦ pointed_map_path_homotopy X Y f g)
      (contractible_map_equiv (Σ M (g ↦ Id M f g)) (Σ M (g ↦ PointedHomotopy X Y f g))
        (totalize M (g ↦ Id M f g) (g ↦ PointedHomotopy X Y f g) (g ↦ pointed_map_path_homotopy X Y f g))
        (book_contraction (Σ M (g ↦ Id M f g)) (iscontr_idfrom M f))
        (pointed_homotopy_total_contractible X Y f)) g

{` def:pointedtypes, A_+ = (A ⊔ True, inr triv), and xca:plusforgetadjoint. `}
def plus_pointed (A : Type) : Pointed ≔ (Sum A Unit, inr. star.)

def plus_extend (A : Type) (B : Pointed) (f : A → B .carrier) : BookPointedMap (plus_pointed A) B
  ≔ ([ inl. a ↦ f a | inr. _ ↦ B .point ], refl (B .point))

def plus_restrict (A : Type) (B : Pointed) (g : BookPointedMap (plus_pointed A) B) : A → B .carrier
  ≔ a ↦ g .fst (inl. a)

def plus_extend_restrict (A : Type) (B : Pointed) (g : BookPointedMap (plus_pointed A) B)
  : Id (BookPointedMap (plus_pointed A) B) (plus_extend A B (plus_restrict A B g)) g
  ≔ equiv_inverse_map (Id (BookPointedMap (plus_pointed A) B) (plus_extend A B (plus_restrict A B g)) g)
      (PointedHomotopy (plus_pointed A) B (plus_extend A B (plus_restrict A B g)) g)
      (pointed_map_path_equiv (plus_pointed A) B (plus_extend A B (plus_restrict A B g)) g)
      ([ inl. a ↦ refl (g .fst (inl. a)) | inr. u ↦ match u [ star. ↦ g .snd ] ],
       concat_1p (B .carrier) (B .point) (g .fst (inr. star.)) (g .snd))

def plus_forget_adjunction (A : Type) (B : Pointed)
  : Equiv (A → B .carrier) (BookPointedMap (plus_pointed A) B)
  ≔ quasi_inverse_equiv (A → B .carrier) (BookPointedMap (plus_pointed A) B)
      (plus_extend A B) (plus_restrict A B) (f ↦ refl f) (plus_extend_restrict A B)

{` def:pointedequiv, with the book notion of equivalence. `}
def BookPointedEquiv (X Y : Pointed) : Type
  ≔ Σ (BookPointedMap X Y) (f ↦ BookIsEquiv (X .carrier) (Y .carrier) (f .fst))

{` xca:pointedequiv. A path r of pointed types has a path of carriers
   r .carrier and a path over it between the points; the latter gives
   q : pt_Y = r .carrier .trr (pt_X). `}
def pointed_path_point (X Y : Pointed) (r : Id Pointed X Y)
  : Id (Y .carrier) (Y .point) (r .carrier .trr (X .point))
  ≔ inverse (Y .carrier) (r .carrier .trr (X .point)) (Y .point)
      (pathover_transport_equiv Type (T ↦ T) (X .carrier) (Y .carrier) (r .carrier)
        (X .point) (Y .point) .map (r .point))

def pointed_path_to_equiv (X Y : Pointed) (r : Id Pointed X Y) : BookPointedEquiv X Y
  ≔ ((r .carrier .trr, pointed_path_point X Y r),
     book_equivalence (X .carrier) (Y .carrier) (transport_equiv (X .carrier) (Y .carrier) (r .carrier)) .equiv)

def pointed_equivalences_regroup (X : Pointed)
  : Equiv (Σ Pointed (Y ↦ BookPointedEquiv X Y))
      (Σ Type (B ↦ Σ (BookEquiv (X .carrier) B) (e ↦ Σ B (y ↦ Id B y (e .map (X .point))))))
  ≔ quasi_inverse_equiv (Σ Pointed (Y ↦ BookPointedEquiv X Y))
      (Σ Type (B ↦ Σ (BookEquiv (X .carrier) B) (e ↦ Σ B (y ↦ Id B y (e .map (X .point))))))
      (u ↦ (u .fst .carrier, ((u .snd .fst .fst, u .snd .snd), (u .fst .point, u .snd .fst .snd))))
      (w ↦ ((w .fst, w .snd .snd .fst), ((w .snd .fst .map, w .snd .snd .snd), w .snd .fst .equiv)))
      (u ↦ refl u) (w ↦ refl w)

def pointed_equivalences_total_contractible (X : Pointed)
  : BookIsContr (Σ Pointed (Y ↦ BookPointedEquiv X Y))
  ≔ let A ≔ X .carrier in
    let S ≔ Σ Type (B ↦ Σ (BookEquiv A B) (e ↦ Σ B (y ↦ Id B y (e .map (X .point))))) in
    let U ≔ Σ Type (B ↦ BookEquiv A B) in
    let V ≔ Σ Type (B ↦ Id Type A B) in
    let e1 ≔ family_equiv Type (B ↦ Σ (BookEquiv A B) (e ↦ Σ B (y ↦ Id B y (e .map (X .point)))))
      (B ↦ BookEquiv A B)
      (B ↦ contractible_fiber_projection (BookEquiv A B) (e ↦ Σ B (y ↦ Id B y (e .map (X .point))))
        (e ↦ path_to_contractible B (e .map (X .point)))) in
    let e2 ≔ family_equiv Type (B ↦ BookEquiv A B) (B ↦ Id Type A B)
      (B ↦ canonical_inverse_equiv (Id Type A B) (BookEquiv A B)
        (native_equivalence (Id Type A B) (BookEquiv A B) (book_univalence A B))) in
    book_contractibility_equiv V (Σ Pointed (Y ↦ BookPointedEquiv X Y))
      (canonical_inverse_equiv (Σ Pointed (Y ↦ BookPointedEquiv X Y)) V
        (compose_equiv (Σ Pointed (Y ↦ BookPointedEquiv X Y)) S V (pointed_equivalences_regroup X)
          (compose_equiv S U V e1 e2)))
      .map (book_contraction V (iscontr_idfrom Type A))

def pointed_path_equiv (X Y : Pointed) : Equiv (Id Pointed X Y) (BookPointedEquiv X Y)
  ≔ (pointed_path_to_equiv X Y,
      fiberwise_from_total Pointed (Y ↦ Id Pointed X Y) (Y ↦ BookPointedEquiv X Y)
        (Y ↦ pointed_path_to_equiv X Y)
        (contractible_map_equiv (Σ Pointed (Y ↦ Id Pointed X Y)) (Σ Pointed (Y ↦ BookPointedEquiv X Y))
          (totalize Pointed (Y ↦ Id Pointed X Y) (Y ↦ BookPointedEquiv X Y) (Y ↦ pointed_path_to_equiv X Y))
          (book_contraction (Σ Pointed (Y ↦ Id Pointed X Y)) (iscontr_idfrom Pointed X))
          (pointed_equivalences_total_contractible X)) Y)
