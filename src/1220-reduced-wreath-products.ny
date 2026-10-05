export "1211-wreath-lamplighter"
export "709-groups-are-abstract-groups"

{` Chapter 12, sec:direct-sums (abelian.tex 938-952): reduced (restricted)
   wreath products and the Lamplighter group C₂ ≀ Z. The book's \wip asks
   how to form infinite direct sums; for the restricted wreath product it is
   enough to take, for each z : BG, the abstract group ⊕_{X(z)} H of finitely
   supported functions X(z) → USym H with the pointwise product, and its
   concrete group concr(-) (chapter 7, def:concr). Finite support is
   Kuratowski-style, "every x is listed in some list l or f(x) = e", so no
   decidable equality is needed and the construction is uniform in z (the
   G-action on X transports it). Then H ≀_X G ≔ G ⋉ (z ↦ concr(⊕_{X(z)} H)). `}

{` x occurs in the list l (up to identification). `}
def fs_listed (S : Type) (l : List S) (x : S) : Type
  ≔ match l [ nil. ↦ Empty | cons. y rest ↦ Sum (Id S y x) (fs_listed S rest x) ]

def fs_listed_append_left (S : Type) (l l' : List S) (x : S) (h : fs_listed S l x)
  : fs_listed S (append S l l') x
  ≔ match l [
    | nil. ↦ match h [ ]
    | cons. y rest ↦ match h [
      | inl. e ↦ inl. e
      | inr. h' ↦ inr. (fs_listed_append_left S rest l' x h') ] ]

def fs_listed_append_right (S : Type) (l l' : List S) (x : S) (h : fs_listed S l' x)
  : fs_listed S (append S l l') x
  ≔ match l [
    | nil. ↦ h
    | cons. y rest ↦ inr. (fs_listed_append_right S rest l' x h) ]

{` f : S → USym H vanishes outside l. `}
def FsCovered (S : Type) (H : Group) (f : S → USym H) (l : List S) : Type
  ≔ (x : S) → Sum (fs_listed S l x) (Id (USym H) (f x) (usym_unit H))

def FinSupported (S : Type) (H : Group) (f : S → USym H) : Type ≔ Mere (Σ (List S) (FsCovered S H f))

def fin_supported_prop (S : Type) (H : Group) (f : S → USym H) : isProp (FinSupported S H f)
  ≔ mere_isprop (Σ (List S) (FsCovered S H f))

{` The carrier of ⊕_S H. `}
def FinSupp (S : SetTypes) (H : Group) : Type ≔ Σ (S .fst → USym H) (FinSupported (S .fst) H)

def fs_unit (S : SetTypes) (H : Group) : FinSupp S H
  ≔ (_ ↦ usym_unit H,
     mere (Σ (List (S .fst)) (FsCovered (S .fst) H (_ ↦ usym_unit H)))
       (nil., _ ↦ inr. (refl (usym_unit H))))

def fs_mul_function (S : SetTypes) (H : Group) (a b : FinSupp S H) : S .fst → USym H
  ≔ x ↦ usym_mul H (a .fst x) (b .fst x)

def fs_mul_covered (S : SetTypes) (H : Group) (a b : FinSupp S H) (l l' : List (S .fst))
  (c : FsCovered (S .fst) H (a .fst) l) (c' : FsCovered (S .fst) H (b .fst) l')
  : FsCovered (S .fst) H (fs_mul_function S H a b) (append (S .fst) l l')
  ≔ x ↦ match c x [
    | inl. h ↦ inl. (fs_listed_append_left (S .fst) l l' x h)
    | inr. p ↦ match c' x [
      | inl. h' ↦ inl. (fs_listed_append_right (S .fst) l l' x h')
      | inr. p' ↦ inr. (concat (USym H) (usym_mul H (a .fst x) (b .fst x))
          (usym_mul H (usym_unit H) (usym_unit H)) (usym_unit H)
          (refl (usym_mul H) p p') (usym_abstract_laws H .unit_right (usym_unit H))) ] ]

def fs_mul (S : SetTypes) (H : Group) (a b : FinSupp S H) : FinSupp S H
  ≔ let T ≔ Σ (List (S .fst)) (FsCovered (S .fst) H (fs_mul_function S H a b)) in
    (fs_mul_function S H a b,
     mere_rec (Σ (List (S .fst)) (FsCovered (S .fst) H (a .fst))) (Mere T) (mere_isprop T)
       (u ↦ mere_rec (Σ (List (S .fst)) (FsCovered (S .fst) H (b .fst))) (Mere T) (mere_isprop T)
         (v ↦ mere T (append (S .fst) (u .fst) (v .fst), fs_mul_covered S H a b (u .fst) (v .fst) (u .snd) (v .snd)))
         (b .snd))
       (a .snd))

def usym_inv_unit (H : Group) : Id (USym H) (usym_inv H (usym_unit H)) (usym_unit H)
  ≔ concat (USym H) (usym_inv H (usym_unit H)) (usym_mul H (usym_unit H) (usym_inv H (usym_unit H))) (usym_unit H)
      (inverse (USym H) (usym_mul H (usym_unit H) (usym_inv H (usym_unit H))) (usym_inv H (usym_unit H))
        (usym_abstract_laws H .unit_left (usym_inv H (usym_unit H))))
      (usym_abstract_laws H .inv_right (usym_unit H))

def fs_inv (S : SetTypes) (H : Group) (a : FinSupp S H) : FinSupp S H
  ≔ let f ≔ (x ↦ usym_inv H (a .fst x)) : S .fst → USym H in
    let T ≔ Σ (List (S .fst)) (FsCovered (S .fst) H f) in
    (f,
     mere_rec (Σ (List (S .fst)) (FsCovered (S .fst) H (a .fst))) (Mere T) (mere_isprop T)
       (u ↦ mere T (u .fst, x ↦ match u .snd x [
         | inl. h ↦ inl. h
         | inr. p ↦ inr. (concat (USym H) (usym_inv H (a .fst x)) (usym_inv H (usym_unit H)) (usym_unit H)
             (refl (usym_inv H) p) (usym_inv_unit H)) ]))
       (a .snd))

def fs_path (S : SetTypes) (H : Group) (a b : FinSupp S H) (h : (x : S .fst) → Id (USym H) (a .fst x) (b .fst x))
  : Id (FinSupp S H) a b
  ≔ subtype_equal (S .fst → USym H) (FinSupported (S .fst) H) (fin_supported_prop (S .fst) H) a b
      (funext (S .fst) (_ ↦ USym H) (a .fst) (b .fst) h)

def fs_set (S : SetTypes) (H : Group) : isSet (FinSupp S H)
  ≔ sigma_set (S .fst → USym H) (FinSupported (S .fst) H) (pi_set (S .fst) (_ ↦ USym H) (_ ↦ usym_set H))
      (f ↦ prop_is_set (FinSupported (S .fst) H f) (fin_supported_prop (S .fst) H f))

{` ⊕_S H, the abstract group of finitely supported functions S → USym H
   under the pointwise product. `}
def finsupp_abstract_group (S : SetTypes) (H : Group) : AbstractGroup
  ≔ let L ≔ usym_abstract_laws H in
    (FinSupp S H, fs_unit S H, fs_mul S H, fs_inv S H,
     (carrier_set ≔ fs_set S H,
      unit_right ≔ a ↦ fs_path S H (fs_mul S H a (fs_unit S H)) a (x ↦ L .unit_right (a .fst x)),
      unit_left ≔ a ↦ fs_path S H (fs_mul S H (fs_unit S H) a) a (x ↦ L .unit_left (a .fst x)),
      assoc ≔ a b c ↦ fs_path S H (fs_mul S H a (fs_mul S H b c)) (fs_mul S H (fs_mul S H a b) c)
        (x ↦ L .assoc (a .fst x) (b .fst x) (c .fst x)),
      inv_right ≔ a ↦ fs_path S H (fs_mul S H a (fs_inv S H a)) (fs_unit S H) (x ↦ L .inv_right (a .fst x))))

{` Reduced wreath product: H ≀_X G ≔ G ⋉ (z ↦ concr(⊕_{X(z)} H)). `}
def reduced_power_group (H G : Group) (X : GSet G) (z : BG G .carrier) : Group
  ≔ concr (finsupp_abstract_group (X z) H)

def reduced_wreath_product (H G : Group) (X : GSet G) : Group
  ≔ semidirect_product G (reduced_power_group H G X)

{` USym(H ≀_X G) ≃ USym G × ⊕_{X(sh_G)} H. `}
def reduced_wreath_usym_equiv (H G : Group) (X : GSet G)
  : Equiv (USym (reduced_wreath_product H G X)) (Product (USym G) (FinSupp (X (shape G)) H))
  ≔ let A ≔ finsupp_abstract_group (X (shape G)) H in
    compose_equiv (USym (reduced_wreath_product H G X)) (Product (USym G) (USym (concr A)))
      (Product (USym G) (FinSupp (X (shape G)) H))
      (semidirect_usym_equiv G (reduced_power_group H G X))
      (product_equiv (USym G) (USym (concr A)) (USym G) (FinSupp (X (shape G)) H)
        (identity_equiv (USym G))
        (canonical_inverse_equiv (FinSupp (X (shape G)) H) (USym (concr A)) (concr_abstr_carrier_equiv A)))

{` example (Lamplighter group): C₂ ≀ Z, the reduced wreath product of
   C₂ = cyclic_group_fin 1 by Z = circle_group C acting on its principal
   Z-set. Its symmetries are pairs of an element of Z and a finitely
   supported function Z → C₂ (lamplighter_usym_equiv). `}
def lamplighter_group (C : CircleSignature) : Group
  ≔ reduced_wreath_product (cyclic_group_fin (suc. zero.)) (circle_group C) (principal_gset (circle_group C))

def lamplighter_usym_equiv (C : CircleSignature)
  : Equiv (USym (lamplighter_group C))
      (Product (USym (circle_group C)) (FinSupp (principal_gset (circle_group C) (shape (circle_group C)))
        (cyclic_group_fin (suc. zero.))))
  ≔ reduced_wreath_usym_equiv (cyclic_group_fin (suc. zero.)) (circle_group C) (principal_gset (circle_group C))

{` Litmus: the finitely supported functions on USym Z = (sh = sh) include
   the unit (all lamps off), which is supported on the empty list. `}
def lamplighter_lamps_off (C : CircleSignature)
  : FinSupp (principal_gset (circle_group C) (shape (circle_group C))) (cyclic_group_fin (suc. zero.))
  ≔ fs_unit (principal_gset (circle_group C) (shape (circle_group C))) (cyclic_group_fin (suc. zero.))
