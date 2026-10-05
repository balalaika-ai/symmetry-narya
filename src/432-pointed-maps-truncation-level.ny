export "285-chapter-three-completions"
export "401-group-homomorphisms"

{` Footnote ft:ptd-decr-h-lev (group.tex 1135): X →* Y is an n-type
   whenever X is (k−1)-connected and Y is (n+k)-truncated, for all k ≥ 0
   and n ≥ −1.

   Indices: NConnectedType k A (module 230) is the book's "(k−1)-connected";
   HLevel j is the book's (j−2)-truncated. With m ≔ n + 2 the claim reads:
   NConnectedType k X÷ and HLevel (k + m) Y÷ imply HLevel m (X →* Y). We prove
   it for all m ≥ 0 (also n = −2) and more generally for pointed sections of
   a family of types, by induction on m: identifications of pointed
   sections are pointed sections of the family of identity types (con:fib-
   vs-path for the evaluation map), and for m = 0 sections over a
   (k−1)-connected type into (k−2)-types are determined by their value at
   the point (HoTT book Lemma 7.5.7, n_connected_sections_equiv, applied to
   the (k−2)-connected point inclusion 1 → X). `}

{` Pointed sections Σ(s : Π_x P x) (p0 = s(x0)); for a constant family these
   are the book's pointed maps (judgmentally). `}
def PointedSections (X : Pointed) (P : X .carrier → Type) (p0 : P (X .point)) : Type
  ≔ Σ ((x : X .carrier) → P x) (s ↦ Id (P (X .point)) p0 (s (X .point)))

def pointed_sections_constant (X Y : Pointed)
  : Id Type (PointedSections X (_ ↦ Y .carrier) (Y .point)) (BookPointedMap X Y)
  ≔ refl (BookPointedMap X Y)

def pointed_sections_eval (X : Pointed) (P : X .carrier → Type) (s : (x : X .carrier) → P x) : P (X .point)
  ≔ s (X .point)

{` Identifications of pointed sections are pointed sections of the
   identity-type family, pointed at u_pt⁻¹ · v_pt (concatenation order). `}
def pointed_sections_path_equiv (X : Pointed) (P : X .carrier → Type) (p0 : P (X .point))
  (u v : PointedSections X P p0)
  : Equiv (Id (PointedSections X P p0) u v)
      (PointedSections X (x ↦ Id (P x) (u .fst x) (v .fst x))
        (concat (P (X .point)) (u .fst (X .point)) p0 (v .fst (X .point))
          (inverse (P (X .point)) p0 (u .fst (X .point)) (u .snd)) (v .snd)))
  ≔ let A ≔ X .carrier in let x0 ≔ X .point in
    let S ≔ (x : A) → P x in
    let q0 ≔ concat (P x0) (u .fst x0) p0 (v .fst x0) (inverse (P x0) p0 (u .fst x0) (u .snd)) (v .snd) in
    compose_equiv (Id (PointedSections X P p0) u v)
      (BookFiber (Id S (u .fst) (v .fst)) (Id (P x0) (u .fst x0) (v .fst x0))
        (map_path S (P x0) (pointed_sections_eval X P) (u .fst) (v .fst)) q0)
      (PointedSections X (x ↦ Id (P x) (u .fst x) (v .fst x)) q0)
      (fiber_path_equiv S (P x0) (pointed_sections_eval X P) p0 u v)
      (sigma_pullback_equiv (Id S (u .fst) (v .fst)) (Homotopy A P (u .fst) (v .fst))
        (function_extensionality A P (u .fst) (v .fst))
        (h ↦ Id (Id (P x0) (u .fst x0) (v .fst x0)) q0 (h x0)))

{` The point inclusion 1 → X of a k-connected-index type (book: (j)-connected
   for k = j+1) is (j−1)-connected (index j): its fibers are the identity
   types x = x0, whose j-truncations are identity types of the contractible
   ‖X‖_{j}. `}
def unit_sigma_equiv (T : Type) : Equiv T (Σ Unit (_ ↦ T))
  ≔ quasi_inverse_equiv T (Σ Unit (_ ↦ T)) (t ↦ (star., t)) (w ↦ w .snd) (t ↦ refl t)
      (w ↦ (unit_prop star. (w .fst), refl (w .snd)))

def point_inclusion_n_connected (j : Nat) (X : Pointed) (hX : NConnectedType (suc. j) (X .carrier))
  : NConnectedMap j Unit (X .carrier) (_ ↦ X .point)
  ≔ b ↦
    let A ≔ X .carrier in let x0 ≔ X .point in
    let T ≔ Trunc (suc. j) A in
    let tb ≔ trunc_unit (suc. j) A b in let t0 ≔ trunc_unit (suc. j) A x0 in
    let hpath : NConnectedType j (Id A b x0)
      ≔ book_contractibility_equiv (Id T tb t0) (Trunc j (Id A b x0))
          (canonical_inverse_equiv (Trunc j (Id A b x0)) (Id T tb t0) (trunc_path_equiv j A b x0))
          .map (book_contraction (Id T tb t0)
            (prop_paths_contractible T (contractible_prop T (native_contraction T hX)) tb t0)) in
    n_connected_type_equiv j (Id A b x0) (Σ Unit (_ ↦ Id A b x0)) (unit_sigma_equiv (Id A b x0)) hpath

{` m = 0: pointed sections into (k−2)-types over a (k−1)-connected type
   are contractible. `}
def pointed_sections_contractible (X : Pointed) (k : Nat)
  : NConnectedType k (X .carrier) → (P : X .carrier → Type) → ((x : X .carrier) → HLevel k (P x))
    → (p0 : P (X .point)) → HLevel zero. (PointedSections X P p0)
  ≔ match k [
  | zero. ↦ _ P hP p0 ↦
      sigma_contractible ((x : X .carrier) → P x) (s ↦ Id (P (X .point)) p0 (s (X .point)))
        (pi_contractible (X .carrier) P hP)
        (s ↦ prop_paths_contractible (P (X .point)) (contractible_prop (P (X .point)) (hP (X .point)))
          p0 (s (X .point)))
  | suc. j ↦ hX P hP p0 ↦
      let A ≔ X .carrier in let x0 ≔ X .point in
      let e1 ≔ n_connected_sections_equiv j Unit A (_ ↦ x0) (point_inclusion_n_connected j X hX) P hP in
      let e2 ≔ contractible_domain_evaluation (Unit, star.) (P x0) (book_contraction Unit unit_contractible) in
      let e ≔ compose_equiv ((x : A) → P x) (Unit → P x0) (P x0) e1 e2 in
      hlevel_equiv zero. (Σ (P x0) (q ↦ Id (P x0) p0 q)) (PointedSections X P p0)
        (canonical_inverse_equiv (PointedSections X P p0) (Σ (P x0) (q ↦ Id (P x0) p0 q))
          (sigma_pullback_equiv ((x : A) → P x) (P x0) e (q ↦ Id (P x0) p0 q)))
        (iscontr_idfrom (P x0) p0) ]

{` The general statement for pointed sections, by induction on m. `}
def pointed_sections_hlevel (k : Nat) (X : Pointed) (hX : NConnectedType k (X .carrier)) (m : Nat)
  : (P : X .carrier → Type) → ((x : X .carrier) → HLevel (add k m) (P x))
    → (p0 : P (X .point)) → HLevel m (PointedSections X P p0)
  ≔ match m [
  | zero. ↦ P hP p0 ↦ pointed_sections_contractible X k hX P hP p0
  | suc. n ↦ P hP p0 ↦ u v ↦
      let x0 ≔ X .point in
      let P' : X .carrier → Type ≔ x ↦ Id (P x) (u .fst x) (v .fst x) in
      let q0 ≔ concat (P x0) (u .fst x0) p0 (v .fst x0) (inverse (P x0) p0 (u .fst x0) (u .snd)) (v .snd) in
      hlevel_equiv n (PointedSections X P' q0) (Id (PointedSections X P p0) u v)
        (canonical_inverse_equiv (Id (PointedSections X P p0) u v) (PointedSections X P' q0)
          (pointed_sections_path_equiv X P p0 u v))
        (pointed_sections_hlevel k X hX n P' (x ↦ hP x (u .fst x) (v .fst x)) q0) ]

{` ft:ptd-decr-h-lev, general form: if X is (k−1)-connected and Y is
   (n+k)-truncated then X →* Y is an n-type, written with m = n + 2 ≥ 0
   (the book's n ≥ −1 is m ≥ 1; m = 0 is the extra case n = −2). `}
def pointed_maps_truncation_level (k m : Nat) (X Y : Pointed) (hX : NConnectedType k (X .carrier))
  (hY : HLevel (add k m) (Y .carrier)) : HLevel m (BookPointedMap X Y)
  ≔ pointed_sections_hlevel k X hX m (_ ↦ Y .carrier) (_ ↦ hY) (Y .point)

{` The printed indices: k ≥ 0 and n ≥ −1 written as n = n' − 1 with n' : Nat;
   "(n+k)-truncated" is HLevel (k + n' + 1) and "n-type" is HLevel (n' + 1). `}
def pointed_maps_truncation_level_book (k n' : Nat) (X Y : Pointed) (hX : NConnectedType k (X .carrier))
  (hY : HLevel (add k (suc. n')) (Y .carrier)) : HLevel (suc. n') (BookPointedMap X Y)
  ≔ pointed_maps_truncation_level k (suc. n') X Y hX hY

{` The special case of the footnote's first sentence (k = 1, n = 0):
   X connected and Y a groupoid give a set; this re-derives the core's
   pointed_maps_set through the general statement. `}
def pointed_maps_set_from_general (X Y : Pointed) (hX : Connected (X .carrier)) (hY : isGroupoid (Y .carrier))
  : isSet (BookPointedMap X Y)
  ≔ hlevel_two_to_set (BookPointedMap X Y)
      (pointed_maps_truncation_level (suc. zero.) (suc. (suc. zero.)) X Y
        (equiv_inverse_map (NConnectedType (suc. zero.) (X .carrier)) (Connected (X .carrier))
          (zero_connected_connected (X .carrier)) hX)
        (groupoid_to_hlevel (Y .carrier) hY))

{` Litmus (k = 0, m = 0): pointed maps from any type into a contractible
   type form a contractible type. `}
def pointed_maps_into_contractible (X Y : Pointed) (m : Mere (X .carrier)) (hY : isContr (Y .carrier))
  : isContr (BookPointedMap X Y)
  ≔ pointed_maps_truncation_level zero. zero. X Y
      (equiv_inverse_map (NConnectedType zero. (X .carrier)) (Mere (X .carrier))
        (minus_one_connected_nonempty (X .carrier)) m)
      hY
