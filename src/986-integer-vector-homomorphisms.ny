export "980-integer-vectors-factors"
export "710-hom-delooping"
export "413-group-motivation"

{` Chapter 9 (subgroups.tex 1186), general n × n integer matrices: additive
   self-maps F of Int^n as homomorphisms Z^n → Z^n (Z^n = int_power_group C n,
   BZ^n = Fin n → C). The winding vector w(p)_i = winding of the i-th
   component of a symmetry p identifies USym(Z^n) with Int^n as groups
   (w(p · q) = w(p) + w(q)); int_vec_hom F is the delooping (module 710) of
   the abstract homomorphism p ↦ w⁻¹(F(w(p))), so USym of it acts on winding
   vectors as F (int_vec_hom_windings). Homomorphisms Z^n → Z^n are
   determined by their action on winding vectors; this gives extensionality,
   composition (int_vec_hom (F ∘ G) = int_vec_hom F ∘ int_vec_hom G), the
   identity, and: int_vec_hom F is a monomorphism if F is injective, and not
   a monomorphism if F kills a nonzero vector. `}

{` happly turns concatenation in a function type into pointwise concatenation. `}
def ivh_happly_concat (I X : Type) (f g h : I → X) (p : Id (I → X) f g) (q : Id (I → X) g h) (i : I)
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

{` The winding vector of a symmetry of Z^n and its inverse. `}
def int_power_winding (C : CircleSignature) (n : Nat) (p : USym (int_power_group C n)) : Fin n → Int
  ≔ i ↦ circle_winding C (happly (Fin n) (_ ↦ C .carrier) (_ ↦ C .base) (_ ↦ C .base) p i)

def ivh_unwind (C : CircleSignature) (n : Nat) (v : Fin n → Int) : USym (int_power_group C n)
  ≔ funext (Fin n) (_ ↦ C .carrier) (_ ↦ C .base) (_ ↦ C .base) (i ↦ circle_power C (v i))

def ivh_vec_path (n : Nat) (x y : Fin n → Int) (h : (i : Fin n) → Id Int (x i) (y i)) : Id (Fin n → Int) x y
  ≔ funext (Fin n) (_ ↦ Int) x y h

def ivh_wind_unwind (C : CircleSignature) (n : Nat) (v : Fin n → Int) (i : Fin n)
  : Id Int (int_power_winding C n (ivh_unwind C n v) i) (v i)
  ≔ let X ≔ C .carrier in let b ≔ C .base in
    let h : (i : Fin n) → Id X b b ≔ i ↦ circle_power C (v i) in
    concat Int (int_power_winding C n (ivh_unwind C n v) i) (circle_winding C (h i)) (v i)
      (refl (circle_winding C)
        (inverse (Id X b b) (h i) (happly (Fin n) (_ ↦ X) (_ ↦ b) (_ ↦ b) (funext (Fin n) (_ ↦ X) (_ ↦ b) (_ ↦ b) h) i)
          (funext_beta (Fin n) (_ ↦ X) (_ ↦ b) (_ ↦ b) h i)))
      (circle_winding_power C (v i))

def ivh_unwind_wind (C : CircleSignature) (n : Nat) (p : USym (int_power_group C n))
  : Id (USym (int_power_group C n)) (ivh_unwind C n (int_power_winding C n p)) p
  ≔ let X ≔ C .carrier in let b ≔ C .base in
    let hp : (i : Fin n) → Id X b b ≔ happly (Fin n) (_ ↦ X) (_ ↦ b) (_ ↦ b) p in
    concat (Id (Fin n → X) (_ ↦ b) (_ ↦ b)) (ivh_unwind C n (int_power_winding C n p))
      (funext (Fin n) (_ ↦ X) (_ ↦ b) (_ ↦ b) hp) p
      (refl ((h ↦ funext (Fin n) (_ ↦ X) (_ ↦ b) (_ ↦ b) h) : ((i : Fin n) → Id X b b) → Id (Fin n → X) (_ ↦ b) (_ ↦ b))
        (funext (Fin n) (_ ↦ Id X b b) (i ↦ circle_power C (circle_winding C (hp i))) hp
          (i ↦ circle_power_winding C (hp i))))
      (funext_eta (Fin n) (_ ↦ X) (_ ↦ b) (_ ↦ b) p)

def ivh_winding_injective (C : CircleSignature) (n : Nat) (p q : USym (int_power_group C n))
  (h : (i : Fin n) → Id Int (int_power_winding C n p i) (int_power_winding C n q i))
  : Id (USym (int_power_group C n)) p q
  ≔ let Zn ≔ int_power_group C n in
    calc
      p = ivh_unwind C n (int_power_winding C n p)
        by inverse (USym Zn) (ivh_unwind C n (int_power_winding C n p)) p (ivh_unwind_wind C n p)
      = ivh_unwind C n (int_power_winding C n q)
        by refl (ivh_unwind C n) (ivh_vec_path n (int_power_winding C n p) (int_power_winding C n q) h)
      = q by ivh_unwind_wind C n q ∎

{` w(p · q) = w(p) + w(q). `}
def ivh_winding_mul (C : CircleSignature) (n : Nat) (p q : USym (int_power_group C n)) (i : Fin n)
  : Id Int (int_power_winding C n (usym_mul (int_power_group C n) p q) i)
      (int_add (int_power_winding C n p i) (int_power_winding C n q i))
  ≔ let X ≔ C .carrier in let b ≔ C .base in
    let o : Fin n → X ≔ _ ↦ b in
    concat Int (int_power_winding C n (usym_mul (int_power_group C n) p q) i)
      (circle_winding C (usym_mul (circle_group C) (happly (Fin n) (_ ↦ X) o o p i) (happly (Fin n) (_ ↦ X) o o q i)))
      (int_add (int_power_winding C n p i) (int_power_winding C n q i))
      (refl (circle_winding C) (ivh_happly_concat (Fin n) X o o o q p i))
      (circle_winding_mul C (happly (Fin n) (_ ↦ X) o o p i) (happly (Fin n) (_ ↦ X) o o q i))

def ivh_winding_unit (C : CircleSignature) (n : Nat) (i : Fin n)
  : Id Int (int_power_winding C n (usym_unit (int_power_group C n)) i) int_zero
  ≔ circle_winding_power C int_zero

{` The abstract homomorphism p ↦ w⁻¹(F(w(p))). `}
def ivh_abstract_map (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (p : USym (int_power_group C n))
  : USym (int_power_group C n)
  ≔ ivh_unwind C n (F (int_power_winding C n p))

def ivh_abstract_law (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  : IsAbstractHom (abstr (int_power_group C n)) (abstr (int_power_group C n)) (ivh_abstract_map C n F)
  ≔ let Zn ≔ int_power_group C n in
    let w ≔ int_power_winding C n in
    let f ≔ ivh_abstract_map C n F in
    s s' ↦ ivh_winding_injective C n (f (usym_mul Zn s s')) (usym_mul Zn (f s) (f s'))
      (i ↦ calc
        w (f (usym_mul Zn s s')) i = F (w (usym_mul Zn s s')) i by ivh_wind_unwind C n (F (w (usym_mul Zn s s'))) i
        = F (int_vec_add n (w s) (w s')) i
          by refl ((x ↦ F x i) : (Fin n → Int) → Int)
               (ivh_vec_path n (w (usym_mul Zn s s')) (int_vec_add n (w s) (w s')) (j ↦ ivh_winding_mul C n s s' j))
        = int_add (F (w s) i) (F (w s') i) by hF (w s) (w s') i
        = int_add (w (f s) i) (w (f s') i)
          by refl int_add (inverse Int (w (f s) i) (F (w s) i) (ivh_wind_unwind C n (F (w s)) i))
               (inverse Int (w (f s') i) (F (w s') i) (ivh_wind_unwind C n (F (w s')) i))
        = w (usym_mul Zn (f s) (f s')) i
          by inverse Int (w (usym_mul Zn (f s) (f s')) i) (int_add (w (f s) i) (w (f s') i)) (ivh_winding_mul C n (f s) (f s') i) ∎)

def ivh_abstract (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  : AbstractHom (abstr (int_power_group C n)) (abstr (int_power_group C n))
  ≔ (ivh_abstract_map C n F, ivh_abstract_law C n F hF)

{` The homomorphism Z^n → Z^n of an additive map F of Int^n. `}
def int_vec_hom (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  : GroupHom (int_power_group C n) (int_power_group C n)
  ≔ deloop_hom (int_power_group C n) (int_power_group C n) (ivh_abstract C n F hF)

def ivh_usym (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  (p : USym (int_power_group C n))
  : Id (USym (int_power_group C n)) (usym_hom (int_power_group C n) (int_power_group C n) (int_vec_hom C n F hF) p)
      (ivh_abstract_map C n F p)
  ≔ let Zn ≔ int_power_group C n in
    refl ((φ ↦ φ .fst p) : AbstractHom (abstr Zn) (abstr Zn) → USym Zn)
      (deloop_hom_section Zn Zn (ivh_abstract C n F hF))

def int_vec_hom_windings (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  (p : USym (int_power_group C n)) (i : Fin n)
  : Id Int (int_power_winding C n (usym_hom (int_power_group C n) (int_power_group C n) (int_vec_hom C n F hF) p) i)
      (F (int_power_winding C n p) i)
  ≔ concat Int (int_power_winding C n (usym_hom (int_power_group C n) (int_power_group C n) (int_vec_hom C n F hF) p) i)
      (int_power_winding C n (ivh_abstract_map C n F p) i) (F (int_power_winding C n p) i)
      (refl ((u ↦ int_power_winding C n u i) : USym (int_power_group C n) → Int) (ivh_usym C n F hF p))
      (ivh_wind_unwind C n (F (int_power_winding C n p)) i)

{` Homomorphisms Z^n → Z^n with the same action on winding vectors are equal. `}
def ivh_hom_ext_windings (C : CircleSignature) (n : Nat) (h h' : GroupHom (int_power_group C n) (int_power_group C n))
  (e : (p : USym (int_power_group C n)) (i : Fin n)
       → Id Int (int_power_winding C n (usym_hom (int_power_group C n) (int_power_group C n) h p) i)
           (int_power_winding C n (usym_hom (int_power_group C n) (int_power_group C n) h' p) i))
  : Id (GroupHom (int_power_group C n) (int_power_group C n)) h h'
  ≔ let Zn ≔ int_power_group C n in
    equivalence_injective (GroupHom Zn Zn) (AbstractHom (abstr Zn) (abstr Zn)) (abstr_hom_equiv Zn Zn) h h'
      (abstract_hom_ext (abstr Zn) (abstr Zn) (abstr_hom Zn Zn h) (abstr_hom Zn Zn h')
        (p ↦ ivh_winding_injective C n (usym_hom Zn Zn h p) (usym_hom Zn Zn h' p) (e p)))

def int_vec_hom_ext (C : CircleSignature) (n : Nat) (F G : (Fin n → Int) → Fin n → Int)
  (hF : IntVecAdditive n F) (hG : IntVecAdditive n G)
  (h : (x : Fin n → Int) (i : Fin n) → Id Int (F x i) (G x i))
  : Id (GroupHom (int_power_group C n) (int_power_group C n)) (int_vec_hom C n F hF) (int_vec_hom C n G hG)
  ≔ let Zn ≔ int_power_group C n in let w ≔ int_power_winding C n in
    ivh_hom_ext_windings C n (int_vec_hom C n F hF) (int_vec_hom C n G hG)
      (p i ↦ calc
        w (usym_hom Zn Zn (int_vec_hom C n F hF) p) i = F (w p) i by int_vec_hom_windings C n F hF p i
        = G (w p) i by h (w p) i
        = w (usym_hom Zn Zn (int_vec_hom C n G hG) p) i
          by inverse Int (w (usym_hom Zn Zn (int_vec_hom C n G hG) p) i) (G (w p) i) (int_vec_hom_windings C n G hG p i) ∎)

{` int_vec_hom (F ∘ G) = int_vec_hom F ∘ int_vec_hom G (G first). `}
def int_vec_hom_compose (C : CircleSignature) (n : Nat) (F G : (Fin n → Int) → Fin n → Int)
  (hF : IntVecAdditive n F) (hG : IntVecAdditive n G) (hFG : IntVecAdditive n (x ↦ F (G x)))
  : Id (GroupHom (int_power_group C n) (int_power_group C n)) (int_vec_hom C n (x ↦ F (G x)) hFG)
      (group_hom_compose (int_power_group C n) (int_power_group C n) (int_power_group C n) (int_vec_hom C n G hG) (int_vec_hom C n F hF))
  ≔ let Zn ≔ int_power_group C n in let w ≔ int_power_winding C n in
    let hf ≔ int_vec_hom C n F hF in let hg ≔ int_vec_hom C n G hG in
    ivh_hom_ext_windings C n (int_vec_hom C n (x ↦ F (G x)) hFG) (group_hom_compose Zn Zn Zn hg hf)
      (p i ↦ calc
        w (usym_hom Zn Zn (int_vec_hom C n (x ↦ F (G x)) hFG) p) i = F (G (w p)) i
          by int_vec_hom_windings C n (x ↦ F (G x)) hFG p i
        = F (w (usym_hom Zn Zn hg p)) i
          by refl ((x ↦ F x i) : (Fin n → Int) → Int)
               (ivh_vec_path n (G (w p)) (w (usym_hom Zn Zn hg p))
                 (j ↦ inverse Int (w (usym_hom Zn Zn hg p) j) (G (w p) j) (int_vec_hom_windings C n G hG p j)))
        = w (usym_hom Zn Zn hf (usym_hom Zn Zn hg p)) i
          by inverse Int (w (usym_hom Zn Zn hf (usym_hom Zn Zn hg p)) i) (F (w (usym_hom Zn Zn hg p)) i)
               (int_vec_hom_windings C n F hF (usym_hom Zn Zn hg p) i)
        = w (usym_hom Zn Zn (group_hom_compose Zn Zn Zn hg hf) p) i
          by refl ((u ↦ w u i) : USym Zn → Int)
               (inverse (USym Zn) (usym_hom Zn Zn (group_hom_compose Zn Zn Zn hg hf) p) (usym_hom Zn Zn hf (usym_hom Zn Zn hg p))
                 (happly (USym Zn) (_ ↦ USym Zn) (usym_hom Zn Zn (group_hom_compose Zn Zn Zn hg hf))
                   (x ↦ usym_hom Zn Zn hf (usym_hom Zn Zn hg x)) (usym_hom_compose Zn Zn Zn hg hf) p)) ∎)

def int_vec_hom_identity (C : CircleSignature) (n : Nat) (hI : IntVecAdditive n (x ↦ x))
  : Id (GroupHom (int_power_group C n) (int_power_group C n)) (int_vec_hom C n (x ↦ x) hI) (group_hom_id (int_power_group C n))
  ≔ let Zn ≔ int_power_group C n in let w ≔ int_power_winding C n in
    ivh_hom_ext_windings C n (int_vec_hom C n (x ↦ x) hI) (group_hom_id Zn)
      (p i ↦ concat Int (w (usym_hom Zn Zn (int_vec_hom C n (x ↦ x) hI) p) i) (w p i) (w (usym_hom Zn Zn (group_hom_id Zn) p) i)
        (int_vec_hom_windings C n (x ↦ x) hI p i)
        (refl ((u ↦ w u i) : USym Zn → Int)
          (inverse (USym Zn) (usym_hom Zn Zn (group_hom_id Zn) p) p (usym_hom_id Zn p))))

{` Injective F gives a monomorphism. `}
def int_vec_hom_mono (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  (inj : (x y : Fin n → Int) → ((i : Fin n) → Id Int (F x i) (F y i)) → (i : Fin n) → Id Int (x i) (y i))
  : IsGroupMono (int_power_group C n) (int_power_group C n) (int_vec_hom C n F hF)
  ≔ let Zn ≔ int_power_group C n in let w ≔ int_power_winding C n in
    let h ≔ int_vec_hom C n F hF in
    path_reflecting_set_embedding (USym Zn) (USym Zn) (usym_set Zn) (usym_hom Zn Zn h)
      (p q e ↦ ivh_winding_injective C n p q
        (inj (w p) (w q) (i ↦ calc
          F (w p) i = w (usym_hom Zn Zn h p) i
            by inverse Int (w (usym_hom Zn Zn h p) i) (F (w p) i) (int_vec_hom_windings C n F hF p i)
          = w (usym_hom Zn Zn h q) i by refl ((u ↦ w u i) : USym Zn → Int) e
          = F (w q) i by int_vec_hom_windings C n F hF q i ∎)))

{` F killing a nonzero vector gives a non-monomorphism. `}
def int_vec_hom_not_mono (C : CircleSignature) (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F)
  (x : Fin n → Int) (hx : Not ((i : Fin n) → Id Int (x i) int_zero))
  (hk : (i : Fin n) → Id Int (F x i) int_zero)
  : Not (IsGroupMono (int_power_group C n) (int_power_group C n) (int_vec_hom C n F hF))
  ≔ m ↦
    let Zn ≔ int_power_group C n in let w ≔ int_power_winding C n in
    let h ≔ int_vec_hom C n F hF in
    let p ≔ ivh_unwind C n x in
    let u ≔ usym_unit Zn in
    let e : Id (USym Zn) (usym_hom Zn Zn h p) (usym_hom Zn Zn h u)
      ≔ ivh_winding_injective C n (usym_hom Zn Zn h p) (usym_hom Zn Zn h u)
          (i ↦ calc
            w (usym_hom Zn Zn h p) i = F (w p) i by int_vec_hom_windings C n F hF p i
            = F x i by refl ((y ↦ F y i) : (Fin n → Int) → Int) (ivh_vec_path n (w p) x (ivh_wind_unwind C n x))
            = int_zero by hk i
            = w u i by inverse Int (w u i) int_zero (ivh_winding_unit C n i)
            = w (usym_hom Zn Zn h u) i
              by refl ((v ↦ w v i) : USym Zn → Int) (inverse (USym Zn) (usym_hom Zn Zn h u) u (usym_hom_unit Zn Zn h)) ∎) in
    let r : Id (USym Zn) p u ≔ embedding_reflects_paths (USym Zn) (USym Zn) (usym_hom Zn Zn h) m p u e in
    hx (i ↦ calc
      x i = w p i by inverse Int (w p i) (x i) (ivh_wind_unwind C n x i)
      = w u i by refl ((v ↦ w v i) : USym Zn → Int) r
      = int_zero by ivh_winding_unit C n i ∎)
