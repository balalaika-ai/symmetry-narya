export "210-truncation-smallness"
export "186-chapter-two-remarks"

{` Maps out of (Z, succ): for every type Y (no sethood) and every equivalence
   F : Y ≃ Y, the type of maps (Int, succ) → (Y, F) of types with automorphism
   is equivalent to Y (int_maps_equiv, by contractibility; its map is not
   definitionally evaluation at 0).  Z is the free type with an automorphism
   with evaluation at 0 as the equivalence in int_maps_evaluation_equiv
   (module 284).  Used for the circle. `}

def nat_cons (Y : Type) (y : Y) (g : Nat → Y) (n : Nat) : Y ≔ match n [ zero. ↦ y | suc. m ↦ g m ]

def nat_fun_split (Y : Type) : Equiv (Product Y (Nat → Y)) (Nat → Y)
  ≔ quasi_inverse_equiv (Product Y (Nat → Y)) (Nat → Y) (u ↦ nat_cons Y (u .fst) (u .snd))
      (h ↦ (h zero., n ↦ h (suc. n))) (u ↦ refl u)
      (h ↦ funext Nat (_ ↦ Y) (nat_cons Y (h zero.) (n ↦ h (suc. n))) h
        (n ↦ match n [ zero. ↦ refl (h zero.) | suc. m ↦ refl (h (suc. m)) ]))

def nat_pi_cons (Q : Nat → Type) (q0 : Q zero.) (qs : (n : Nat) → Q (suc. n)) (n : Nat) : Q n
  ≔ match n [ zero. ↦ q0 | suc. m ↦ qs m ]

def nat_pi_split (Q : Nat → Type) : Equiv (Product (Q zero.) ((n : Nat) → Q (suc. n))) ((n : Nat) → Q n)
  ≔ quasi_inverse_equiv (Product (Q zero.) ((n : Nat) → Q (suc. n))) ((n : Nat) → Q n)
      (u ↦ nat_pi_cons Q (u .fst) (u .snd)) (h ↦ (h zero., n ↦ h (suc. n))) (u ↦ refl u)
      (h ↦ funext Nat Q (nat_pi_cons Q (h zero.) (n ↦ h (suc. n))) h
        (n ↦ match n [ zero. ↦ refl (h zero.) | suc. m ↦ refl (h (suc. m)) ]))

def int_cons (Y : Type) (p q : Nat → Y) (k : Int) : Y ≔ match k [ pos. n ↦ p n | neg. n ↦ q n ]

def int_fun_split (Y : Type) : Equiv (Product (Nat → Y) (Nat → Y)) (Int → Y)
  ≔ quasi_inverse_equiv (Product (Nat → Y) (Nat → Y)) (Int → Y) (u ↦ int_cons Y (u .fst) (u .snd))
      (h ↦ (n ↦ h (pos. n), n ↦ h (neg. n))) (u ↦ refl u)
      (h ↦ funext Int (_ ↦ Y) (int_cons Y (n ↦ h (pos. n)) (n ↦ h (neg. n))) h
        (k ↦ match k [ pos. n ↦ refl (h (pos. n)) | neg. n ↦ refl (h (neg. n)) ]))

def int_pi_cons (Q : Int → Type) (p : (n : Nat) → Q (pos. n)) (q : (n : Nat) → Q (neg. n)) (k : Int) : Q k
  ≔ match k [ pos. n ↦ p n | neg. n ↦ q n ]

def int_pi_split (Q : Int → Type)
  : Equiv (Product ((n : Nat) → Q (pos. n)) ((n : Nat) → Q (neg. n))) ((k : Int) → Q k)
  ≔ quasi_inverse_equiv (Product ((n : Nat) → Q (pos. n)) ((n : Nat) → Q (neg. n))) ((k : Int) → Q k)
      (u ↦ int_pi_cons Q (u .fst) (u .snd)) (h ↦ (n ↦ h (pos. n), n ↦ h (neg. n))) (u ↦ refl u)
      (h ↦ funext Int Q (int_pi_cons Q (n ↦ h (pos. n)) (n ↦ h (neg. n))) h
        (k ↦ match k [ pos. n ↦ refl (h (pos. n)) | neg. n ↦ refl (h (neg. n)) ]))

{` Reindexing a sum along an equivalence of bases. `}
def sigma_base_change (A B : Type) (e : Equiv A B) (C : B → Type)
  : Equiv (Σ A (a ↦ C (e .map a))) (Σ B C)
  ≔ equivalence_induction A (B e ↦ (C : B → Type) → Equiv (Σ A (a ↦ C (e .map a))) (Σ B C))
      (C ↦ identity_equiv (Σ A C)) B e C

def concat_cancel_inverse_right (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z)
  : Id (Id A x y) (concat A x z y (concat A x y z p q) (inverse A y z q)) p
  ≔ calc
      concat A x z y (concat A x y z p q) (inverse A y z q)
      = concat A x y y p (concat A y z y q (inverse A y z q)) by concat_assoc A x y z y p q (inverse A y z q)
      = concat A x y y p (refl y) by refl (concat A x y y p) (concat_inverse_right A y z q)
      = p by concat_p1 A x y p ∎

def concat_inverse_cancel_right (A : Type) (x y z : A) (p : Id A x y) (q : Id A z y)
  : Id (Id A x y) (concat A x z y (concat A x y z p (inverse A z y q)) q) p
  ≔ calc
      concat A x z y (concat A x y z p (inverse A z y q)) q
      = concat A x y y p (concat A y z y (inverse A z y q) q) by concat_assoc A x y z y p (inverse A z y q) q
      = concat A x y y p (refl y) by refl (concat A x y y p) (concat_inverse_left A z y q)
      = p by concat_p1 A x y p ∎

{` Sequences g with g 0 = F y and g (n+1) = F (g n) form a contractible type,
   for any function F on any type. `}
def ForwardSteps (Y : Type) (F : Y → Y) (y : Y) (g : Nat → Y) : Type
  ≔ Product (Id Y (g zero.) (F y)) ((n : Nat) → Id Y (g (suc. n)) (F (g n)))

def ForwardSequences (Y : Type) (F : Y → Y) (y : Y) : Type ≔ Σ (Nat → Y) (ForwardSteps Y F y)

def ForwardOrbitPaths (Y : Type) (F : Y → Y) (y : Y) (g : Nat → Y) : Type
  ≔ (n : Nat) → Id Y (g n) (iterate Y F (suc. n) y)

def forward_orbit_paths (Y : Type) (F : Y → Y) (y : Y) (g : Nat → Y) (u : ForwardSteps Y F y g) (n : Nat)
  : Id Y (g n) (iterate Y F (suc. n) y)
  ≔ match n [
  | zero. ↦ u .fst
  | suc. m ↦ concat Y (g (suc. m)) (F (g m)) (F (iterate Y F (suc. m) y)) (u .snd m)
      (refl F (forward_orbit_paths Y F y g u m)) ]

def forward_orbit_steps (Y : Type) (F : Y → Y) (y : Y) (g : Nat → Y) (H : ForwardOrbitPaths Y F y g)
  : ForwardSteps Y F y g
  ≔ (H zero., n ↦ concat Y (g (suc. n)) (F (iterate Y F (suc. n) y)) (F (g n)) (H (suc. n))
      (inverse Y (F (g n)) (F (iterate Y F (suc. n) y)) (refl F (H n))))

def forward_orbit_roundtrip (Y : Type) (F : Y → Y) (y : Y) (g : Nat → Y) (H : ForwardOrbitPaths Y F y g) (n : Nat)
  : Id (Id Y (g n) (iterate Y F (suc. n) y)) (forward_orbit_paths Y F y g (forward_orbit_steps Y F y g H) n) (H n)
  ≔ match n [
  | zero. ↦ refl (H zero.)
  | suc. m ↦ calc
      concat Y (g (suc. m)) (F (g m)) (F (iterate Y F (suc. m) y))
        (concat Y (g (suc. m)) (F (iterate Y F (suc. m) y)) (F (g m)) (H (suc. m))
          (inverse Y (F (g m)) (F (iterate Y F (suc. m) y)) (refl F (H m))))
        (refl F (forward_orbit_paths Y F y g (forward_orbit_steps Y F y g H) m))
      = concat Y (g (suc. m)) (F (g m)) (F (iterate Y F (suc. m) y))
          (concat Y (g (suc. m)) (F (iterate Y F (suc. m) y)) (F (g m)) (H (suc. m))
            (inverse Y (F (g m)) (F (iterate Y F (suc. m) y)) (refl F (H m))))
          (refl F (H m))
        by refl ((v ↦ concat Y (g (suc. m)) (F (g m)) (F (iterate Y F (suc. m) y))
            (concat Y (g (suc. m)) (F (iterate Y F (suc. m) y)) (F (g m)) (H (suc. m))
              (inverse Y (F (g m)) (F (iterate Y F (suc. m) y)) (refl F (H m)))) (refl F v))
          : Id Y (g m) (iterate Y F (suc. m) y) → Id Y (g (suc. m)) (F (iterate Y F (suc. m) y)))
          (forward_orbit_roundtrip Y F y g H m)
      = H (suc. m)
        by concat_inverse_cancel_right Y (g (suc. m)) (F (iterate Y F (suc. m) y)) (F (g m)) (H (suc. m)) (refl F (H m)) ∎ ]

def forward_steps_equiv (Y : Type) (F : Y → Y) (y : Y) (g : Nat → Y)
  : Equiv (ForwardSteps Y F y g) (ForwardOrbitPaths Y F y g)
  ≔ quasi_inverse_equiv (ForwardSteps Y F y g) (ForwardOrbitPaths Y F y g)
      (forward_orbit_paths Y F y g) (forward_orbit_steps Y F y g)
      (u ↦ (refl (u .fst), funext Nat (n ↦ Id Y (g (suc. n)) (F (g n)))
        (forward_orbit_steps Y F y g (forward_orbit_paths Y F y g u) .snd) (u .snd)
        (n ↦ concat_cancel_inverse_right Y (g (suc. n)) (F (g n)) (F (iterate Y F (suc. n) y)) (u .snd n)
          (refl F (forward_orbit_paths Y F y g u n)))))
      (H ↦ funext Nat (n ↦ Id Y (g n) (iterate Y F (suc. n) y))
        (forward_orbit_paths Y F y g (forward_orbit_steps Y F y g H)) H (forward_orbit_roundtrip Y F y g H))

def forward_sequences_contractible (Y : Type) (F : Y → Y) (y : Y) : isContr (ForwardSequences Y F y)
  ≔ let orbit ≔ ((n v ↦ Id Y v (iterate Y F (suc. n) y)) : Nat → Y → Type) in
    hlevel_equiv zero. ((n : Nat) → Σ Y (orbit n)) (ForwardSequences Y F y)
      (compose_equiv ((n : Nat) → Σ Y (orbit n)) (Σ (Nat → Y) (ForwardOrbitPaths Y F y)) (ForwardSequences Y F y)
        (choice_equiv Nat (_ ↦ Y) orbit)
        (canonical_inverse_equiv (ForwardSequences Y F y) (Σ (Nat → Y) (ForwardOrbitPaths Y F y))
          (family_equiv (Nat → Y) (ForwardSteps Y F y) (ForwardOrbitPaths Y F y) (forward_steps_equiv Y F y))))
      (pi_contractible Nat (n ↦ Σ Y (orbit n)) (n ↦ path_to_contractible Y (iterate Y F (suc. n) y)))

{` Sequences with y = F (g 0) and g n = F (g (n+1)): each step lies in a
   contractible fiber of the equivalence F. `}
def BackwardSequences (Y : Type) (F : Equiv Y Y) (y : Y) : Type
  ≔ Σ (Nat → Y) (g ↦ Product (Id Y y (F .map (g zero.))) ((n : Nat) → Id Y (g n) (F .map (g (suc. n)))))

def preimage_path_equiv (Y : Type) (F : Equiv Y Y) (u v : Y)
  : Equiv (Id Y u (F .map v)) (Id Y v (equiv_inverse_map Y Y F u))
  ≔ let G ≔ equiv_inverse_map Y Y F in
    compose_equiv (Id Y u (F .map v)) (Id Y (F .map v) (F .map (G u))) (Id Y v (G u))
      (compose_equiv (Id Y u (F .map v)) (Id Y (F .map v) u) (Id Y (F .map v) (F .map (G u)))
        (inverse_path_equiv Y u (F .map v))
        (id_to_equiv (Id Y (F .map v) u) (Id Y (F .map v) (F .map (G u)))
          (refl ((w ↦ Id Y (F .map v) w) : Y → Type) (inverse Y (F .map (G u)) u (equiv_counit Y Y F u)))))
      (canonical_inverse_equiv (Id Y v (G u)) (Id Y (F .map v) (F .map (G u))) (equivalence_on_paths Y Y F v (G u)))

def backward_forward_equiv (Y : Type) (F : Equiv Y Y) (y : Y)
  : Equiv (BackwardSequences Y F y) (ForwardSequences Y (equiv_inverse_map Y Y F) y)
  ≔ let G ≔ equiv_inverse_map Y Y F in
    family_equiv (Nat → Y)
      (g ↦ Product (Id Y y (F .map (g zero.))) ((n : Nat) → Id Y (g n) (F .map (g (suc. n)))))
      (ForwardSteps Y G y)
      (g ↦ product_equiv (Id Y y (F .map (g zero.))) ((n : Nat) → Id Y (g n) (F .map (g (suc. n))))
        (Id Y (g zero.) (G y)) ((n : Nat) → Id Y (g (suc. n)) (G (g n)))
        (preimage_path_equiv Y F y (g zero.))
        (pi_family_equiv Nat (n ↦ Id Y (g n) (F .map (g (suc. n)))) (n ↦ Id Y (g (suc. n)) (G (g n)))
          (n ↦ preimage_path_equiv Y F (g n) (g (suc. n)))))

def backward_sequences_contractible (Y : Type) (F : Equiv Y Y) (y : Y) : isContr (BackwardSequences Y F y)
  ≔ hlevel_equiv zero. (ForwardSequences Y (equiv_inverse_map Y Y F) y) (BackwardSequences Y F y)
      (canonical_inverse_equiv (BackwardSequences Y F y) (ForwardSequences Y (equiv_inverse_map Y Y F) y)
        (backward_forward_equiv Y F y))
      (forward_sequences_contractible Y (equiv_inverse_map Y Y F) y)

{` Maps of types with automorphism (Int, succ) → (Y, F). `}
def IntMaps (Y : Type) (F : Equiv Y Y) : Type ≔ PermutationMap Int Y int_succ_equiv F

def IntSplitSteps (Y : Type) (F : Equiv Y Y) (p q : Nat → Y) : Type
  ≔ Product ((n : Nat) → Id Y (p (suc. n)) (F .map (p n)))
      (Product (Id Y (p zero.) (F .map (q zero.))) ((n : Nat) → Id Y (q n) (F .map (q (suc. n)))))

def commutes_split_equiv (Y : Type) (F : Equiv Y Y) (p q : Nat → Y)
  : Equiv (IntSplitSteps Y F p q) (Commutes Int Y int_succ_equiv F (int_cons Y p q))
  ≔ let Q ≔ ((k ↦ Id Y (int_cons Y p q (int_succ k)) (F .map (int_cons Y p q k))) : Int → Type) in
    compose_equiv (IntSplitSteps Y F p q) (Product ((n : Nat) → Q (pos. n)) ((n : Nat) → Q (neg. n))) ((k : Int) → Q k)
      (product_equiv ((n : Nat) → Q (pos. n)) (Product (Q (neg. zero.)) ((n : Nat) → Q (neg. (suc. n))))
        ((n : Nat) → Q (pos. n)) ((n : Nat) → Q (neg. n))
        (identity_equiv ((n : Nat) → Q (pos. n))) (nat_pi_split (n ↦ Q (neg. n))))
      (int_pi_split Q)

def IntSplit (Y : Type) (F : Equiv Y Y) : Type
  ≔ Σ (Product (Nat → Y) (Nat → Y)) (pq ↦ IntSplitSteps Y F (pq .fst) (pq .snd))

def int_maps_split_equiv (Y : Type) (F : Equiv Y Y) : Equiv (IntSplit Y F) (IntMaps Y F)
  ≔ compose_equiv (IntSplit Y F)
      (Σ (Product (Nat → Y) (Nat → Y)) (pq ↦ Commutes Int Y int_succ_equiv F (int_cons Y (pq .fst) (pq .snd))))
      (IntMaps Y F)
      (family_equiv (Product (Nat → Y) (Nat → Y)) (pq ↦ IntSplitSteps Y F (pq .fst) (pq .snd))
        (pq ↦ Commutes Int Y int_succ_equiv F (int_cons Y (pq .fst) (pq .snd)))
        (pq ↦ commutes_split_equiv Y F (pq .fst) (pq .snd)))
      (sigma_base_change (Product (Nat → Y) (Nat → Y)) (Int → Y) (int_fun_split Y) (Commutes Int Y int_succ_equiv F))

def IntSplitCurried (Y : Type) (F : Equiv Y Y) : Type
  ≔ Σ (Nat → Y) (p ↦ Σ (Nat → Y) (q ↦ IntSplitSteps Y F p q))

def int_split_curry_equiv (Y : Type) (F : Equiv Y Y) : Equiv (IntSplit Y F) (IntSplitCurried Y F)
  ≔ quasi_inverse_equiv (IntSplit Y F) (IntSplitCurried Y F)
      (u ↦ (u .fst .fst, (u .fst .snd, u .snd))) (v ↦ ((v .fst, v .snd .fst), v .snd .snd))
      (u ↦ refl u) (v ↦ refl v)

def IntSplitHead (Y : Type) (F : Equiv Y Y) : Type
  ≔ Σ (Product Y (Nat → Y)) (yg ↦ Σ (Nat → Y) (q ↦ IntSplitSteps Y F (nat_cons Y (yg .fst) (yg .snd)) q))

def IntSplitSeparated (Y : Type) (F : Equiv Y Y) : Type
  ≔ Σ (Product Y (Nat → Y)) (yg ↦ Σ (Nat → Y) (q ↦
      Product (ForwardSteps Y (F .map) (yg .fst) (yg .snd))
        (Product (Id Y (yg .fst) (F .map (q zero.))) ((n : Nat) → Id Y (q n) (F .map (q (suc. n)))))))

def int_split_separate_equiv (Y : Type) (F : Equiv Y Y) : Equiv (IntSplitSeparated Y F) (IntSplitHead Y F)
  ≔ family_equiv (Product Y (Nat → Y))
      (yg ↦ Σ (Nat → Y) (q ↦ Product (ForwardSteps Y (F .map) (yg .fst) (yg .snd))
        (Product (Id Y (yg .fst) (F .map (q zero.))) ((n : Nat) → Id Y (q n) (F .map (q (suc. n)))))))
      (yg ↦ Σ (Nat → Y) (q ↦ IntSplitSteps Y F (nat_cons Y (yg .fst) (yg .snd)) q))
      (yg ↦ family_equiv (Nat → Y)
        (q ↦ Product (ForwardSteps Y (F .map) (yg .fst) (yg .snd))
          (Product (Id Y (yg .fst) (F .map (q zero.))) ((n : Nat) → Id Y (q n) (F .map (q (suc. n))))))
        (q ↦ IntSplitSteps Y F (nat_cons Y (yg .fst) (yg .snd)) q)
        (q ↦ product_equiv (ForwardSteps Y (F .map) (yg .fst) (yg .snd))
          (Product (Id Y (yg .fst) (F .map (q zero.))) ((n : Nat) → Id Y (q n) (F .map (q (suc. n)))))
          ((n : Nat) → Id Y (nat_cons Y (yg .fst) (yg .snd) (suc. n)) (F .map (nat_cons Y (yg .fst) (yg .snd) n)))
          (Product (Id Y (yg .fst) (F .map (q zero.))) ((n : Nat) → Id Y (q n) (F .map (q (suc. n)))))
          (nat_pi_split (n ↦ Id Y (nat_cons Y (yg .fst) (yg .snd) (suc. n)) (F .map (nat_cons Y (yg .fst) (yg .snd) n))))
          (identity_equiv (Product (Id Y (yg .fst) (F .map (q zero.))) ((n : Nat) → Id Y (q n) (F .map (q (suc. n))))))))

def IntSplitFibers (Y : Type) (F : Equiv Y Y) : Type
  ≔ Σ Y (y ↦ Product (ForwardSequences Y (F .map) y) (BackwardSequences Y F y))

def int_split_fibers_equiv (Y : Type) (F : Equiv Y Y) : Equiv (IntSplitSeparated Y F) (IntSplitFibers Y F)
  ≔ quasi_inverse_equiv (IntSplitSeparated Y F) (IntSplitFibers Y F)
      (u ↦ (u .fst .fst, ((u .fst .snd, u .snd .snd .fst), (u .snd .fst, u .snd .snd .snd))))
      (v ↦ ((v .fst, v .snd .fst .fst), (v .snd .snd .fst, (v .snd .fst .snd, v .snd .snd .snd))))
      (u ↦ refl u) (v ↦ refl v)

def int_split_fibers_contract (Y : Type) (F : Equiv Y Y) : Equiv (IntSplitFibers Y F) Y
  ≔ contractible_fiber_projection Y (y ↦ Product (ForwardSequences Y (F .map) y) (BackwardSequences Y F y))
      (y ↦ sigma_contractible (ForwardSequences Y (F .map) y) (_ ↦ BackwardSequences Y F y)
        (forward_sequences_contractible Y (F .map) y) (_ ↦ backward_sequences_contractible Y F y))

{` The free-action equivalence (Int, succ) → (Y, F) ≃ Y, for every type Y. `}
def int_maps_equiv (Y : Type) (F : Equiv Y Y) : Equiv (IntMaps Y F) Y
  ≔ let A0 ≔ IntMaps Y F in let A1 ≔ IntSplit Y F in let A2 ≔ IntSplitCurried Y F in
    let A3 ≔ IntSplitHead Y F in let A4 ≔ IntSplitSeparated Y F in let A5 ≔ IntSplitFibers Y F in
    let e01 ≔ canonical_inverse_equiv A1 A0 (int_maps_split_equiv Y F) in
    let e12 ≔ int_split_curry_equiv Y F in
    let e23 ≔ canonical_inverse_equiv A3 A2
      (sigma_base_change (Product Y (Nat → Y)) (Nat → Y) (nat_fun_split Y) (p ↦ Σ (Nat → Y) (q ↦ IntSplitSteps Y F p q))) in
    let e34 ≔ canonical_inverse_equiv A4 A3 (int_split_separate_equiv Y F) in
    let e45 ≔ int_split_fibers_equiv Y F in
    compose_equiv A0 A5 Y
      (compose_equiv A0 A4 A5 (compose_equiv A0 A3 A4 (compose_equiv A0 A2 A3 (compose_equiv A0 A1 A2 e01 e12) e23) e34) e45)
      (int_split_fibers_contract Y F)
