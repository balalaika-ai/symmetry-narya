export "11-concrete-rings"
export "../../../src/1352-book-integer-multiplication"
export "../../../src/127-symmetries-of-circle"

{` Bridges for the footnote of the example at fields.tex 1177 (the twist s, the rotations e_z and their
   two claims). The blind s(z) (circle induction with s(base) = loop) agrees pointwise with our
   book_integer_twist (both are loops in a set, equal at base), so the blind e_z is our circle_translation C z. The
   claim e_loop = s (after e_base = id) is proved pointwise: evaluated at x, the conjugated loop is a loop in the
   set x = x, so it suffices to check x = base, where it is loop because loops of S¹ commute. `}

{` happly preserves concatenation and inversion (as ivh_happly_concat/_inverse of chapter 9). `}
def b11c_happly_concat (I X : Type) (f g h : I → X) (p : Id (I → X) f g) (q : Id (I → X) g h) (i : I)
  : Id (Id X (f i) (h i)) (happly I (_ ↦ X) f h (concat (I → X) f g h p q) i)
      (concat X (f i) (g i) (h i) (happly I (_ ↦ X) f g p i) (happly I (_ ↦ X) g h q i))
  ≔ J (I → X) g
      (h q ↦ Id (Id X (f i) (h i)) (happly I (_ ↦ X) f h (concat (I → X) f g h p q) i)
          (concat X (f i) (g i) (h i) (happly I (_ ↦ X) f g p i) (happly I (_ ↦ X) g h q i)))
      (concat (Id X (f i) (g i)) (happly I (_ ↦ X) f g (concat (I → X) f g g p (refl g)) i) (happly I (_ ↦ X) f g p i)
        (concat X (f i) (g i) (g i) (happly I (_ ↦ X) f g p i) (refl (g i)))
        (refl ((r ↦ happly I (_ ↦ X) f g r i) : Id (I → X) f g → Id X (f i) (g i)) (concat_p1 (I → X) f g p))
        (inverse (Id X (f i) (g i)) (concat X (f i) (g i) (g i) (happly I (_ ↦ X) f g p i) (refl (g i)))
          (happly I (_ ↦ X) f g p i) (concat_p1 X (f i) (g i) (happly I (_ ↦ X) f g p i))))
      h q

def b11c_happly_inverse (I X : Type) (f g : I → X) (p : Id (I → X) f g) (i : I)
  : Id (Id X (g i) (f i)) (happly I (_ ↦ X) g f (inverse (I → X) f g p) i) (inverse X (f i) (g i) (happly I (_ ↦ X) f g p i))
  ≔ J (I → X) f
      (g p ↦ Id (Id X (g i) (f i)) (happly I (_ ↦ X) g f (inverse (I → X) f g p) i) (inverse X (f i) (g i) (happly I (_ ↦ X) f g p i)))
      (concat (Id X (f i) (f i)) (happly I (_ ↦ X) f f (inverse (I → X) f f (refl f)) i) (refl (f i)) (inverse X (f i) (f i) (refl (f i)))
        (refl ((r ↦ happly I (_ ↦ X) f f r i) : Id (I → X) f f → Id X (f i) (f i)) (inverse_refl (I → X) f))
        (inverse (Id X (f i) (f i)) (inverse X (f i) (f i) (refl (f i))) (refl (f i)) (inverse_refl X (f i))))
      g p

{` s(base) = loop for the blind s (its base computation rule). `}
def b11c_s_base (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base)) (blind_Zring_s_fun C (C .base)) (C .loop)
  ≔ C .induction (x ↦ Id (C .carrier) x x)
      (C .loop, pathover_of_eq (C .carrier) (x ↦ Id (C .carrier) x x) (C .base) (C .base) (C .loop)
        (C .loop) (C .loop) (blind_Zring_loop_case C)) .snd .fst

def bridge_def_Zring_s_fun (C : CircleSignature) (z : C .carrier)
  : Id (Id (C .carrier) z z) (blind_Zring_s_fun C z) (book_integer_twist C z)
  ≔ let S ≔ C .carrier in
    circle_ind_prop C (x ↦ Id (Id S x x) (blind_Zring_s_fun C x) (book_integer_twist C x))
      (x ↦ circle_groupoid C x x (blind_Zring_s_fun C x) (book_integer_twist C x))
      (concat (Id S (C .base) (C .base)) (blind_Zring_s_fun C (C .base)) (C .loop) (book_integer_twist C (C .base))
        (b11c_s_base C)
        (inverse (Id S (C .base) (C .base)) (book_integer_twist C (C .base)) (C .loop) (book_integer_twist_base C)))
      z

def bridge_def_Zring_s (C : CircleSignature)
  : Id (Id (C .carrier → C .carrier) (identity (C .carrier)) (identity (C .carrier)))
      (blind_Zring_s C) (funext (C .carrier) (_ ↦ C .carrier) (identity (C .carrier)) (identity (C .carrier)) (book_integer_twist C))
  ≔ let S ≔ C .carrier in
    refl (funext S (_ ↦ S) (identity S) (identity S))
      (funext S (x ↦ Id S x x) (blind_Zring_s_fun C) (book_integer_twist C) (bridge_def_Zring_s_fun C))

def bridge_def_Zring_e (C : CircleSignature) (z : C .carrier)
  : Id (C .carrier → C .carrier) (blind_Zring_e C z) (circle_translation C z .map)
  ≔ refl ((l ↦ circle_rec C (C .carrier) (z, l)) : Id (C .carrier) z z → C .carrier → C .carrier) (bridge_def_Zring_s_fun C z)

{` Footnote claim e_p(base) = p (up to the base computation paths), by path induction. `}
def bridge_exa_Zring_e_point : blind_exa_Zring_e_point
  ≔ C z p ↦
    let S ≔ C .carrier in let b ≔ C .base in
    J S b (z p ↦ Id (Id S b z)
        (concat S b (blind_Zring_e C b b) z
          (inverse S (blind_Zring_e C b b) b (blind_Zring_e_beta C b))
          (concat S (blind_Zring_e C b b) (blind_Zring_e C z b) z
            (refl ((w : S) ↦ blind_Zring_e C w b) p) (blind_Zring_e_beta C z)))
        p)
      (concat (Id S b b)
        (concat S b (blind_Zring_e C b b) b (inverse S (blind_Zring_e C b b) b (blind_Zring_e_beta C b))
          (concat S (blind_Zring_e C b b) (blind_Zring_e C b b) b (refl (blind_Zring_e C b b)) (blind_Zring_e_beta C b)))
        (concat S b (blind_Zring_e C b b) b (inverse S (blind_Zring_e C b b) b (blind_Zring_e_beta C b)) (blind_Zring_e_beta C b))
        (refl b)
        (refl (concat S b (blind_Zring_e C b b) b (inverse S (blind_Zring_e C b b) b (blind_Zring_e_beta C b)))
          (concat_1p S (blind_Zring_e C b b) b (blind_Zring_e_beta C b)))
        (concat_inverse_left S (blind_Zring_e C b b) b (blind_Zring_e_beta C b)))
      z p

{` Conjugation by a loop is trivial when loops commute; conjugation along any path then only depends on the
   endpoints. `}
def b11c_conj_loop_trivial (A : Type) (b : A)
  (comm : (u v : Id A b b) → Id (Id A b b) (concat A b b b u v) (concat A b b b v u))
  (q l : Id A b b) : Id (Id A b b) (pointed_loop_conjugate A b b q l) l
  ≔ calc
      pointed_loop_conjugate A b b q l = concat A b b b q (concat A b b b (inverse A b b q) l)
        by refl (concat A b b b q) (comm l (inverse A b b q))
      = concat A b b b (concat A b b b q (inverse A b b q)) l
        by inverse (Id A b b) (concat A b b b (concat A b b b q (inverse A b b q)) l)
          (concat A b b b q (concat A b b b (inverse A b b q) l)) (concat_assoc A b b b b q (inverse A b b q) l)
      = concat A b b b (refl b) l
        by refl ((r ↦ concat A b b b r l) : Id A b b → Id A b b) (concat_inverse_right A b b q)
      = l by concat_1p A b b l ∎

def b11c_conj_any (A : Type) (b : A)
  (comm : (u v : Id A b b) → Id (Id A b b) (concat A b b b u v) (concat A b b b v u))
  (y : A) (r : Id A b y) : (q : Id A b y) (m : Id A y y) (l : Id A b b)
    → Id (Id A b b) (pointed_loop_conjugate A b y r m) l → Id (Id A b b) (pointed_loop_conjugate A b y q m) l
  ≔ J A b (y r ↦ (q : Id A b y) (m : Id A y y) (l : Id A b b)
        → Id (Id A b b) (pointed_loop_conjugate A b y r m) l → Id (Id A b b) (pointed_loop_conjugate A b y q m) l)
      (q m l e ↦
        concat (Id A b b) (pointed_loop_conjugate A b b q m) (pointed_loop_conjugate A b b q l) l
          (refl (pointed_loop_conjugate A b b q)
            (concat (Id A b b) m (pointed_loop_conjugate A b b (refl b) m) l
              (inverse (Id A b b) (pointed_loop_conjugate A b b (refl b) m) m (loop_conjugate_at_refl A b m)) e))
          (b11c_conj_loop_trivial A b comm q l))
      y r

{` Footnote claim e_base = id and e_loop = s. `}
def b11c_iota (C : CircleSignature)
  : Id (C .carrier → C .carrier) (blind_Zring_e C (C .base)) (identity (C .carrier))
  ≔ let S ≔ C .carrier in
    concat (S → S) (blind_Zring_e C (C .base)) (circle_rec C S (C .base, C .loop)) (identity S)
      (refl ((l ↦ circle_rec C S (C .base, l)) : Id S (C .base) (C .base) → S → S) (b11c_s_base C))
      (circle_rec_eta C S (identity S))

def b11c_pointwise (C : CircleSignature) (x : C .carrier) : Id (C .carrier) x x
  ≔ let S ≔ C .carrier in let h ≔ happly S (_ ↦ S) (blind_Zring_e C (C .base)) (identity S) (b11c_iota C) in
    concat S x (blind_Zring_e C (C .base) x) x (inverse S (blind_Zring_e C (C .base) x) x (h x))
      (concat S (blind_Zring_e C (C .base) x) (blind_Zring_e C (C .base) x) x
        (refl ((z ↦ blind_Zring_e C z x) : S → S) (C .loop)) (h x))

def b11c_pointwise_base (C : CircleSignature)
  : Id (Id (C .carrier) (C .base) (C .base)) (b11c_pointwise C (C .base)) (C .loop)
  ≔ let S ≔ C .carrier in let b ≔ C .base in
    let f ≔ (z ↦ blind_Zring_e C z b) : S → S in
    let hb ≔ happly S (_ ↦ S) (blind_Zring_e C b) (identity S) (b11c_iota C) b in
    let ι ≔ (z ↦ inverse S (f z) z (blind_Zring_e_beta C z)) : (z : S) → Id S z (f z) in
    let m ≔ refl f (C .loop) in
    concat (Id S b b) (b11c_pointwise C b) (pointed_loop_conjugate S b (f b) (inverse S (f b) b hb) m) (C .loop)
      (refl (concat S b (f b) b (inverse S (f b) b hb))
        (refl (concat S (f b) (f b) b m) (inverse (Id S (f b) b) (inverse S b (f b) (inverse S (f b) b hb)) hb
          (inverse_inverse S (f b) b hb))))
      (b11c_conj_any S b (circle_loops_commute C) (f b) (ι b) (inverse S (f b) b hb) m (C .loop)
        (loops_map_homotopic_identity S f ι b (C .loop)))

def b11c_pointwise_s (C : CircleSignature) (x : C .carrier)
  : Id (Id (C .carrier) x x) (b11c_pointwise C x) (blind_Zring_s_fun C x)
  ≔ let S ≔ C .carrier in
    circle_ind_prop C (y ↦ Id (Id S y y) (b11c_pointwise C y) (blind_Zring_s_fun C y))
      (y ↦ circle_groupoid C y y (b11c_pointwise C y) (blind_Zring_s_fun C y))
      (concat (Id S (C .base) (C .base)) (b11c_pointwise C (C .base)) (C .loop) (blind_Zring_s_fun C (C .base))
        (b11c_pointwise_base C)
        (inverse (Id S (C .base) (C .base)) (blind_Zring_s_fun C (C .base)) (C .loop) (b11c_s_base C)))
      x

def b11c_conjugated (C : CircleSignature) : Id (C .carrier → C .carrier) (identity (C .carrier)) (identity (C .carrier))
  ≔ let S ≔ C .carrier in let e0 ≔ blind_Zring_e C (C .base) in
    concat (S → S) (identity S) e0 (identity S)
      (inverse (S → S) e0 (identity S) (b11c_iota C))
      (concat (S → S) e0 e0 (identity S) (refl (blind_Zring_e C) (C .loop)) (b11c_iota C))

def b11c_conjugated_happly (C : CircleSignature) (x : C .carrier)
  : Id (Id (C .carrier) x x) (happly (C .carrier) (_ ↦ C .carrier) (identity (C .carrier)) (identity (C .carrier)) (b11c_conjugated C) x)
      (b11c_pointwise C x)
  ≔ let S ≔ C .carrier in let e0 ≔ blind_Zring_e C (C .base) in let I ≔ identity S in
    let hp ≔ (f g : S → S) (p : Id (S → S) f g) ↦ happly S (_ ↦ S) f g p x in
    calc
      hp I I (b11c_conjugated C)
      = concat S x (e0 x) x (hp I e0 (inverse (S → S) e0 I (b11c_iota C)))
          (hp e0 I (concat (S → S) e0 e0 I (refl (blind_Zring_e C) (C .loop)) (b11c_iota C)))
        by b11c_happly_concat S S I e0 I (inverse (S → S) e0 I (b11c_iota C))
          (concat (S → S) e0 e0 I (refl (blind_Zring_e C) (C .loop)) (b11c_iota C)) x
      = concat S x (e0 x) x (inverse S (e0 x) x (hp e0 I (b11c_iota C)))
          (concat S (e0 x) (e0 x) x (hp e0 e0 (refl (blind_Zring_e C) (C .loop))) (hp e0 I (b11c_iota C)))
        by refl (concat S x (e0 x) x)
          (b11c_happly_inverse S S e0 I (b11c_iota C) x)
          (b11c_happly_concat S S e0 e0 I (refl (blind_Zring_e C) (C .loop)) (b11c_iota C) x)
      = b11c_pointwise C x by refl (b11c_pointwise C x) ∎

def bridge_exa_Zring_e_base_loop : blind_exa_Zring_e_base_loop
  ≔ C ↦
    let S ≔ C .carrier in let I ≔ identity S in
    (b11c_iota C,
     calc
       b11c_conjugated C = funext S (_ ↦ S) I I (happly S (_ ↦ S) I I (b11c_conjugated C))
         by inverse (Id (S → S) I I) (funext S (_ ↦ S) I I (happly S (_ ↦ S) I I (b11c_conjugated C))) (b11c_conjugated C)
           (funext_eta S (_ ↦ S) I I (b11c_conjugated C))
       = funext S (_ ↦ S) I I (blind_Zring_s_fun C)
         by refl (funext S (_ ↦ S) I I)
           (funext S (x ↦ Id S x x) (happly S (_ ↦ S) I I (b11c_conjugated C)) (blind_Zring_s_fun C)
             (x ↦ concat (Id S x x) (happly S (_ ↦ S) I I (b11c_conjugated C) x) (b11c_pointwise C x) (blind_Zring_s_fun C x)
               (b11c_conjugated_happly C x) (b11c_pointwise_s C x)))
       = blind_Zring_s C by refl (blind_Zring_s C) ∎)
