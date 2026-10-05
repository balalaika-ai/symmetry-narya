export "1752-definitional-equality-examples"

{` metamath.tex:162–163 says that the symmetric closure of →* (the reflexive
   transitive closure of one-step reduction) coincides with equality by
   definition, the congruence closure of the basic forms. For an abstract
   rewriting relation this is false: the symmetric closure of →* need not be
   transitive. Here closures are given by explicit chains of length k (no
   inductive families): Steps R x y k is a forward chain, Zigzag R x y k a
   chain of forward or backward steps (the equivalence closure). With the
   relation a → b, a → c on three elements, b and c are related by the
   equivalence closure (b ← a → c) but neither b →* c nor c →* b. The
   correct statement is that ≡ is the equivalence closure of →, which by
   Church–Rosser coincides with joinability (∃c, e →* c and e' →* c). `}

def Steps (A : Type) (R : A → A → Type) (x y : A) (k : Nat) : Type
  ≔ match k [ zero. ↦ Id A x y | suc. k ↦ Σ A (z ↦ Product (R x z) (Steps A R z y k)) ]

def ReflexiveTransitiveClosure (A : Type) (R : A → A → Type) (x y : A) : Type ≔ Σ Nat (Steps A R x y)

def SymmetricClosure (A : Type) (S : A → A → Type) (x y : A) : Type ≔ Sum (S x y) (S y x)

def Zigzag (A : Type) (R : A → A → Type) (x y : A) (k : Nat) : Type
  ≔ match k [ zero. ↦ Id A x y | suc. k ↦ Σ A (z ↦ Product (Sum (R x z) (R z x)) (Zigzag A R z y k)) ]

def EquivalenceClosure (A : Type) (R : A → A → Type) (x y : A) : Type ≔ Σ Nat (Zigzag A R x y)

{` The three-element example: Fin 3 with 0 → 1 and 0 → 2. `}
def rw_three : Nat ≔ suc. two
def rw_a : Fin rw_three ≔ inr. star.
def rw_b : Fin rw_three ≔ inl. (inr. star.)
def rw_c : Fin rw_three ≔ inl. (inl. (inr. star.))

def fork_step (x y : Fin rw_three) : Type
  ≔ match x [
  | inr. _ ↦ match y [ inr. _ ↦ Empty | inl. _ ↦ Unit ]
  | inl. _ ↦ Empty ]

def fork_b_c_equivalent : EquivalenceClosure (Fin rw_three) fork_step rw_b rw_c
  ≔ (suc. (suc. zero.), (rw_a, (inr. star., (rw_c, (inl. star., refl rw_c)))))

def rw_b_ne_c (p : Id (Fin rw_three) rw_b rw_c) : Empty
  ≔ sum_encode (Fin (suc. zero.)) Unit (inr. star.) (inl. (inr. star.))
      (sum_encode (Fin two) Unit rw_b rw_c p)

def rw_c_ne_b (p : Id (Fin rw_three) rw_c rw_b) : Empty
  ≔ rw_b_ne_c (inverse (Fin rw_three) rw_c rw_b p)

{` From b or c (no outgoing steps) every chain is trivial. `}
def fork_b_steps (y : Fin rw_three) (k : Nat) (s : Steps (Fin rw_three) fork_step rw_b y k) : Id (Fin rw_three) rw_b y
  ≔ match k [ zero. ↦ s | suc. k ↦ match s .snd .fst [] ]

def fork_c_steps (y : Fin rw_three) (k : Nat) (s : Steps (Fin rw_three) fork_step rw_c y k) : Id (Fin rw_three) rw_c y
  ≔ match k [ zero. ↦ s | suc. k ↦ match s .snd .fst [] ]

def fork_not_symmetric_closure
  (h : SymmetricClosure (Fin rw_three) (ReflexiveTransitiveClosure (Fin rw_three) fork_step) rw_b rw_c) : Empty
  ≔ match h [
  | inl. s ↦ rw_b_ne_c (fork_b_steps rw_c (s .fst) (s .snd))
  | inr. s ↦ rw_c_ne_b (fork_c_steps rw_b (s .fst) (s .snd)) ]

{` The printed coincidence fails: not every pair related by the equivalence
   closure of → is related by the symmetric closure of →*. `}
def symmetric_closure_not_equivalence_closure
  (h : (A : Type) (R : A → A → Type) (x y : A) → EquivalenceClosure A R x y
       → SymmetricClosure A (ReflexiveTransitiveClosure A R) x y) : Empty
  ≔ fork_not_symmetric_closure (h (Fin rw_three) fork_step rw_b rw_c fork_b_c_equivalent)

{` metamath.tex:181–184: a normal form only reduces to itself, so two normal
   forms with a common reduct are equal. `}
def NormalForm (A : Type) (R : A → A → Type) (x : A) : Type ≔ (y : A) → Not (R x y)

def normal_form_steps (A : Type) (R : A → A → Type) (x y : A) (nx : NormalForm A R x) (k : Nat)
  (s : Steps A R x y k) : Id A x y
  ≔ match k [ zero. ↦ s | suc. k ↦ absurd (Id A x y) (nx (s .fst) (s .snd .fst)) ]

def normal_forms_joinable_equal (A : Type) (R : A → A → Type) (n n' : A)
  (hn : NormalForm A R n) (hn' : NormalForm A R n')
  (j : Σ A (c ↦ Product (ReflexiveTransitiveClosure A R n c) (ReflexiveTransitiveClosure A R n' c)))
  : Id A n n'
  ≔ concat A n (j .fst) n' (normal_form_steps A R n (j .fst) hn (j .snd .fst .fst) (j .snd .fst .snd))
      (inverse A n' (j .fst) (normal_form_steps A R n' (j .fst) hn' (j .snd .snd .fst) (j .snd .snd .snd)))
