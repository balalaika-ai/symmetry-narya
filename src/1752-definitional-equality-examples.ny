export "1751-injections-into-contractible"

{` Running text of appendix B, section "Equality by definition"
   (metamath.tex). The examples of judgmental equalities are checked by
   refl, which Narya accepts only if both sides are definitionally equal.
   The rules themselves (congruence closure, reduction, Church–Rosser,
   termination) are metatheory and are not formalized. Addition is module 1's
   add, defined by recursion on the second argument exactly as in the book. `}

def metamath_one : Nat ≔ suc. zero.

def defeq_explicit_definition : Id Nat metamath_one (suc. zero.) ≔ refl (suc. zero.)

def defeq_add_zero (n : Nat) : Id Nat (add n zero.) n ≔ refl n

def defeq_add_succ (n m : Nat) : Id Nat (add n (suc. m)) (suc. (add n m)) ≔ refl (suc. (add n m))

def defeq_beta (a : Nat) : Id Nat ((x ↦ add x x) a) (add a a) ≔ refl (add a a)

def defeq_eta (A B : Type) (f : A → B) : Id (A → B) (x ↦ f x) f ≔ refl f

def defeq_one_plus_zero : Id Nat (add metamath_one zero.) metamath_one ≔ refl metamath_one

def defeq_add_two_steps (n m : Nat) : Id Nat (add n (suc. (suc. m))) (suc. (add n (suc. m)))
  ≔ refl (suc. (add n (suc. m)))

def defeq_succ_congruence (n m : Nat) : Id Nat (suc. (add n (suc. m))) (suc. (suc. (add n m)))
  ≔ refl (suc. (suc. (add n m)))

def defeq_add_two_steps_closed (n m : Nat) : Id Nat (add n (suc. (suc. m))) (suc. (suc. (add n m)))
  ≔ refl (suc. (suc. (add n m)))

{` "Let's elaborate id ∘ f ≡ f": composition and identity of module 0. `}
def defeq_identity_compose (A B : Type) (f : A → B) : Id (A → B) (compose A B B (identity B) f) f ≔ refl f

{` Typing up to definitional equality: with B ≔ A, a family on A is a
   family on B and the Π-types agree. `}
def metamath_alias (A : Type) : Type ≔ A

def defeq_family_retyped (A : Type) (P : A → Type) : metamath_alias A → Type ≔ P

def defeq_pi_types (A : Type) (P : A → Type)
  : Id Type ((x : metamath_alias A) → P x) ((x : A) → P x) ≔ refl ((x : A) → P x)

{` Internal, propositional shadows of the canonicity examples: every natural
   number is zero or a successor, every element of L ⊔ R is inl or inr. The
   canonicity statements themselves concern closed terms and judgmental
   equality and are metatheoretic. `}
def nat_zero_or_successor (n : Nat) : Sum (Id Nat n zero.) (Σ Nat (m ↦ Id Nat n (suc. m)))
  ≔ match n [ zero. ↦ inl. (refl (zero. : Nat)) | suc. m ↦ inr. (m, refl (suc. m : Nat)) ]

def coproduct_constructor_form (L R : Type) (x : Sum L R)
  : Sum (Σ L (l ↦ Id (Sum L R) x (inl. l))) (Σ R (r ↦ Id (Sum L R) x (inr. r)))
  ≔ match x [ inl. l ↦ inl. (l, refl (inl. l : Sum L R)) | inr. r ↦ inr. (r, refl (inr. r : Sum L R)) ]
