export "04-path-algebra"

{` The opposite orientation of lem:thepathspaceiscontractible. `}
def path_to_contractible (A : Type) (a : A) : isContr (Σ A (x ↦ Id A x a))
  ≔ ((a, refl a), u ↦ (u .snd, conn A (u .fst) a (u .snd)))

def identity_equiv (A : Type) : Equiv A A
  ≔ (identity A, a ↦ path_to_contractible A a)

def id_to_equiv (A B : Type) (p : Id Type A B) : Equiv A B
  ≔ J Type A (B _ ↦ Equiv A B) (identity_equiv A) B p

{` This constructs an inverse equivalence; its map is not claimed to reduce
   to equiv_inverse_map. The comparison remains a separate theorem. `}
def inverse_equiv (A B : Type) (e : Equiv A B) : Equiv B A
  ≔ transport Type (X ↦ Equiv X A) A B (ua A B e) (identity_equiv A)

def contractible_retract (A B : Type) (hA : isContr A) (f : A → B) (g : B → A)
  (s : (b : B) → Id B (f (g b)) b) : isContr B
  ≔ (f (hA .center), b ↦ concat B b (f (g b)) (f (hA .center))
      (inverse B (f (g b)) b (s b)) (refl f (hA .contract (g b))))

def contractible_prop (A : Type) (h : isContr A) : isProp A
  ≔ x y ↦ concat A x (h .center) y (h .contract x)
      (inverse A y (h .center) (h .contract y))

{` lem:isEq-pair=, native heterogeneous version of paths over paths. `}
def SigmaPath (A : Type) (B : A → Type) (u v : Σ A B) : Type
  ≔ Σ (Id A (u .fst) (v .fst)) (p ↦ Id B p (u .snd) (v .snd))

def sigma_path_pair (A : Type) (B : A → Type) (u v : Σ A B)
  (pq : SigmaPath A B u v) : Id (Σ A B) u v ≔ (pq .fst, pq .snd)

def sigma_path_split (A : Type) (B : A → Type) (u v : Σ A B)
  (r : Id (Σ A B) u v) : SigmaPath A B u v ≔ (r .fst, r .snd)

def sigma_path_equiv (A : Type) (B : A → Type) (u v : Σ A B)
  : Equiv (SigmaPath A B u v) (Id (Σ A B) u v)
  ≔ (sigma_path_pair A B u v, r ↦
    ((sigma_path_split A B u v r, refl r), t ↦
      (refl (sigma_path_split A B u v) (t .snd),
       conn (Id (Σ A B) u v) (sigma_path_pair A B u v (t .fst)) r (t .snd))))

{` xca:binary-prod-comm `}
def product_swap (A B : Type) (p : Product A B) : Product B A ≔ (p .snd, p .fst)

def product_swap_equiv (A B : Type) : Equiv (Product A B) (Product B A)
  ≔ (product_swap A B, p ↦
    ((product_swap B A p, refl p), t ↦
      (refl (product_swap B A) (t .snd),
       conn (Product B A) (product_swap A B (t .fst)) p (t .snd))))

{` xca:Sigma-curry, with a fully dependent codomain. `}
def curry (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (f : (p : Σ A B) → C (p .fst) (p .snd)) : (a : A) (b : B a) → C a b
  ≔ a b ↦ f (a, b)

def uncurry (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (f : (a : A) (b : B a) → C a b) : (p : Σ A B) → C (p .fst) (p .snd)
  ≔ p ↦ f (p .fst) (p .snd)

def curry_equiv (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  : Equiv ((p : Σ A B) → C (p .fst) (p .snd)) ((a : A) (b : B a) → C a b)
  ≔ (curry A B C, f ↦
    ((uncurry A B C f, refl f), t ↦
      (refl (uncurry A B C) (t .snd),
       conn ((a : A) (b : B a) → C a b) (curry A B C (t .fst)) f (t .snd))))

{` xca:AC-in-TT: dependent choice with witnesses, without truncation. `}
def choice_forward (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (f : (a : A) → Σ (B a) (C a))
  : Σ ((a : A) → B a) (g ↦ (a : A) → C a (g a))
  ≔ (a ↦ f a .fst, a ↦ f a .snd)

def choice_backward (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (p : Σ ((a : A) → B a) (g ↦ (a : A) → C a (g a)))
  : (a : A) → Σ (B a) (C a) ≔ a ↦ (p .fst a, p .snd a)

def choice_equiv (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  : Equiv ((a : A) → Σ (B a) (C a))
      (Σ ((a : A) → B a) (g ↦ (a : A) → C a (g a)))
  ≔ (choice_forward A B C, p ↦
    ((choice_backward A B C p, refl p), t ↦
      (refl (choice_backward A B C) (t .snd),
       conn (Σ ((a : A) → B a) (g ↦ (a : A) → C a (g a)))
         (choice_forward A B C (t .fst)) p (t .snd))))
