export "530-burnside-lemma"
export "531-fermat-arithmetic"

{` Chapter 5, proof of Fermat's Little Theorem: the C_p-set
   X(S, t) ≔ (S → Fin n) on p-cycles (S, t), here for p = m+1 and the
   book's literal C_p = Aut_Cyc(Fin p, s) (cyclic_group_fin m, module 404).
   A shape z : BC_p is a cycle in the component of (Fin p, s); its carrier
   is z.1.1.1.1. The action of g : USym C_p on f : Fin p → Fin n is
   transport in the function-type family (lem:trp-in-function-type):
   (g · f)(g_*(i)) = f(i), where g_* : Fin p → Fin p is transport of the
   carrier along g (cycle_path_evaluate), and g ↦ g_*(0) is the
   equivalence USym C_p ≃ Fin p of cor:id-m-cycle. `}

def fermat_group (m : Nat) : Group ≔ cyclic_group_fin m

def fermat_gset (m n : Nat) : GSet (fermat_group m)
  ≔ z ↦ (z .fst .fst .fst .fst → Fin n,
         pi_set (z .fst .fst .fst .fst) (_ ↦ Fin n) (_ ↦ fin_set n))

{` "The underlying set is the type of functions Fin p → Fin n" (by definition). `}
def fermat_gset_underlying (m n : Nat)
  : Id Type (gset_underlying (fermat_group m) (fermat_gset m n)) (Fin (suc. m) → Fin n)
  ≔ refl (Fin (suc. m) → Fin n)

def fermat_gset_finite (m n : Nat) : IsFiniteGSet (fermat_group m) (fermat_gset m n)
  ≔ fin_function_finite (suc. m) n

{` "... which is finite of cardinality n^p". `}
def fermat_gset_card (m n : Nat)
  : Id Nat (gset_card (fermat_group m) (fermat_gset m n) (fermat_gset_finite m n)) (nat_power n (suc. m))
  ≔ fin_function_cardinality (suc. m) n (fermat_gset_finite m n)

def fermat_group_finite (m : Nat) : IsFiniteGroup (fermat_group m) ≔ cyclic_group_fin_finite m

def fermat_group_card (m : Nat) : Id Nat (group_card (fermat_group m) (fermat_group_finite m)) (suc. m)
  ≔ cyclic_group_fin_card m

{` g_* : Fin p → Fin p, transport of the carrier along g. `}
def fermat_rotation (m : Nat) (g : USym (fermat_group m)) (i : Fin (suc. m)) : Fin (suc. m)
  ≔ cycle_path_evaluate (finite_fin_cycle m) (finite_fin_cycle m) (g .fst) i

{` cor:id-m-cycle: the equivalence USym C_p ≃ Fin p is g ↦ g_*(0). `}
def fermat_rotation_evaluation (m : Nat) (g : USym (fermat_group m))
  : Id (Fin (suc. m)) (cyclic_group_fin_usym_equiv m .map g) (fermat_rotation m g (inr. star.))
  ≔ refl (fermat_rotation m g (inr. star.))

def fermat_transport_function_apply_base (A : Type) (Y : A → Type) (F : Type) (x : A) (f : Y x → F) (y : Y x)
  : Id F (transport A (z ↦ Y z → F) x x (refl x) f (transport A Y x x (refl x) y)) (f y)
  ≔ concat F (transport A (z ↦ Y z → F) x x (refl x) f (transport A Y x x (refl x) y))
      (f (transport A Y x x (refl x) y)) (f y)
      (refl ((φ ↦ φ (transport A Y x x (refl x) y)) : (Y x → F) → F) (transport_refl A (z ↦ Y z → F) x f))
      (refl f (transport_refl A Y x y))

{` Transport of a function along e, evaluated at the transported argument:
   (e_* f)(e_* y) = f(y) (lem:trp-in-function-type for a constant codomain). `}
def fermat_transport_function_apply (A : Type) (Y : A → Type) (F : Type) (x x' : A) (e : Id A x x')
  (f : Y x → F) (y : Y x)
  : Id F (transport A (z ↦ Y z → F) x x' e f (transport A Y x x' e y)) (f y)
  ≔ J A x (x' e ↦ (y : Y x) → Id F (transport A (z ↦ Y z → F) x x' e f (transport A Y x x' e y)) (f y))
      (y ↦ fermat_transport_function_apply_base A Y F x f y) x' e y

{` Transport of a constant function is that constant function. `}
def fermat_transport_constant_function (A : Type) (Y : A → Type) (F : Type) (x x' : A) (e : Id A x x') (c : F)
  : Id (Y x' → F) (transport A (z ↦ Y z → F) x x' e (_ ↦ c)) (_ ↦ c)
  ≔ J A x (x' e ↦ Id (Y x' → F) (transport A (z ↦ Y z → F) x x' e (_ ↦ c)) (_ ↦ c))
      (transport_refl A (z ↦ Y z → F) x (_ ↦ c)) x' e

{` (g · f)(g_*(i)) = f(i): g rotates the sequence f. `}
def fermat_action_rotation (m n : Nat) (g : USym (fermat_group m)) (f : Fin (suc. m) → Fin n) (i : Fin (suc. m))
  : Id (Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g f (fermat_rotation m g i)) (f i)
  ≔ fermat_transport_function_apply (BG (fermat_group m) .carrier) (z ↦ z .fst .fst .fst .fst) (Fin n)
      (shape (fermat_group m)) (shape (fermat_group m)) g f i

{` Constant functions are fixed by every symmetry. `}
def fermat_constant_fixed (m n : Nat) (g : USym (fermat_group m)) (c : Fin n)
  : Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g (_ ↦ c)) (_ ↦ c)
  ≔ fermat_transport_constant_function (BG (fermat_group m) .carrier) (z ↦ z .fst .fst .fst .fst) (Fin n)
      (shape (fermat_group m)) (shape (fermat_group m)) g c

{` f is constant: f(k) = f(0) for all k (the book's "f is one of the n
   constant functions"). `}
def FermatConstant (m n : Nat) (f : Fin (suc. m) → Fin n) : Type
  ≔ (k : Fin (suc. m)) → Id (Fin n) (f k) (f (inr. star.))

def fermat_constant_prop (m n : Nat) (f : Fin (suc. m) → Fin n) : isProp (FermatConstant m n f)
  ≔ pi_prop (Fin (suc. m)) (k ↦ Id (Fin n) (f k) (f (inr. star.))) (k ↦ fin_set n (f k) (f (inr. star.)))

def fermat_constant_path (m n : Nat) (f : Fin (suc. m) → Fin n) (h : FermatConstant m n f)
  : Id (Fin (suc. m) → Fin n) (_ ↦ f (inr. star.)) f
  ≔ funext (Fin (suc. m)) (_ ↦ Fin n) (_ ↦ f (inr. star.)) f
      (k ↦ inverse (Fin n) (f k) (f (inr. star.)) (h k))

def fermat_constant_fixed_by (m n : Nat) (f : Fin (suc. m) → Fin n) (h : FermatConstant m n f)
  (g : USym (fermat_group m))
  : Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g f) f
  ≔ transport (Fin (suc. m) → Fin n)
      (φ ↦ Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g φ) φ)
      (_ ↦ f (inr. star.)) f (fermat_constant_path m n f h) (fermat_constant_fixed m n g (f (inr. star.)))

{` If every symmetry fixes f, then f is constant: for k take the symmetry
   g with g_*(0) = k (cor:id-m-cycle); then f(k) = (g · f)(g_*(0)) = f(0). `}
def fermat_fixed_by_all_constant (m n : Nat) (f : Fin (suc. m) → Fin n)
  (h : (g : USym (fermat_group m)) → Id (Fin (suc. m) → Fin n) (gset_usym_act (fermat_group m) (fermat_gset m n) g f) f)
  : FermatConstant m n f
  ≔ k ↦
    let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let E ≔ cyclic_group_fin_usym_equiv m in
    let g ≔ equiv_inverse_map (USym G) (Fin (suc. m)) E k in
    let r : Id (Fin (suc. m)) (fermat_rotation m g (inr. star.)) k ≔ equiv_counit (USym G) (Fin (suc. m)) E k in
    calc
      f k
      = f (fermat_rotation m g (inr. star.)) by refl f (inverse (Fin (suc. m)) (fermat_rotation m g (inr. star.)) k r)
      = gset_usym_act G X g f (fermat_rotation m g (inr. star.))
        by refl ((φ ↦ φ (fermat_rotation m g (inr. star.))) : (Fin (suc. m) → Fin n) → Fin n)
          (inverse (Fin (suc. m) → Fin n) (gset_usym_act G X g f) f (h g))
      = f (inr. star.) by fermat_action_rotation m n g f (inr. star.) ∎

{` The constant functions form a copy of Fin n: f ↦ f(0). `}
def fermat_constants_equiv (m n : Nat)
  : Equiv (Σ (Fin (suc. m) → Fin n) (f ↦ FermatConstant m n f)) (Fin n)
  ≔ quasi_inverse_equiv (Σ (Fin (suc. m) → Fin n) (f ↦ FermatConstant m n f)) (Fin n)
      (u ↦ u .fst (inr. star.)) (c ↦ (_ ↦ c, _ ↦ refl c))
      (u ↦ subtype_equal (Fin (suc. m) → Fin n) (f ↦ FermatConstant m n f) (fermat_constant_prop m n)
        (_ ↦ u .fst (inr. star.), _ ↦ refl (u .fst (inr. star.))) u (fermat_constant_path m n (u .fst) (u .snd)))
      (c ↦ refl c)
