export "48-euclidean-division"

def Collision (A B : Type) (f : A → B) : Type ≔ sig (
  left : A,
  right : A,
  distinct : Id A left right → Empty,
  same : Id B (f left) (f right))

{` The finite pigeonhole algorithm searches for a collision with the last
   input. If none exists, it removes that input and its image, reducing n. `}
def fin_pigeonhole (n : Nat) (f : Fin (suc. n) → Fin n) : Collision (Fin (suc. n)) (Fin n) f
  ≔ match n [
  | zero. ↦ match f (inr. star.) []
  | suc. n ↦ match fin_sigma_decidable (suc. n)
      (i ↦ Id (Fin (suc. n)) (f (inl. i)) (f (inr. star.)))
      (i ↦ fin_decidable_equality (suc. n) (f (inl. i)) (f (inr. star.))) [
    | inl. found ↦ (inl. (found .fst), inr. star.,
        (p ↦ sum_encode (Fin (suc. n)) Unit (inl. (found .fst)) (inr. star.) p), found .snd)
    | inr. no ↦ let b ≔ f (inr. star.) in
        let g : Fin (suc. n) → Without (Fin (suc. n)) b
          ≔ (i ↦ (f (inl. i), p ↦ no (i, p))) in
        let e ≔ without_fin_equiv n b in
        let c ≔ fin_pigeonhole n (i ↦ e .map (g i)) in
        (inl. (c .left), inl. (c .right),
          (p ↦ c .distinct (sum_encode (Fin (suc. n)) Unit (inl. (c .left)) (inl. (c .right)) p)),
          equivalence_injective (Without (Fin (suc. n)) b) (Fin n) e (g (c .left)) (g (c .right)) (c .same) .fst) ] ]

def fin_index (n : Nat) (i : Fin n) : Nat ≔ fin_below_equiv n .map i .fst
def fin_index_bound (n : Nat) (i : Fin n) : Lt (fin_index n i) n ≔ fin_below_equiv n .map i .snd

def fin_index_injective (n : Nat) (i j : Fin n) (p : Id Nat (fin_index n i) (fin_index n j)) : Id (Fin n) i j
  ≔ equivalence_injective (Fin n) (Below n) (fin_below_equiv n) i j
      (subtype_equal Nat (k ↦ Lt k n) (k ↦ le_prop (suc. k) n)
        (fin_below_equiv n .map i) (fin_below_equiv n .map j) p)

def fin_index_from_bound (n k : Nat) (h : Lt k n)
  : Id Nat (fin_index n (equiv_inverse_map (Fin n) (Below n) (fin_below_equiv n) (k, h))) k
  ≔ map_path (Below n) Nat (p ↦ p .fst)
      (fin_below_equiv n .map (equiv_inverse_map (Fin n) (Below n) (fin_below_equiv n) (k, h))) (k, h)
      (equiv_counit (Fin n) (Below n) (fin_below_equiv n) (k, h))

def BoundedNatMap (N : Nat) (f : Nat → Nat) : Type
  ≔ (n : Nat) → BookLt n (suc. N) → BookLt (f n) N

def bounded_nat_map_fin (N : Nat) (f : Nat → Nat) (h : BoundedNatMap N f) (i : Fin (suc. N)) : Fin N
  ≔ equiv_inverse_map (Fin N) (Below N) (fin_below_equiv N)
      (f (fin_index (suc. N) i), lt_from_book (f (fin_index (suc. N) i)) N
        (h (fin_index (suc. N) i) (lt_to_book (fin_index (suc. N) i) (suc. N) (fin_index_bound (suc. N) i))))

def bounded_nat_map_value (N : Nat) (f : Nat → Nat) (h : BoundedNatMap N f) (i : Fin (suc. N))
  : Id Nat (fin_index N (bounded_nat_map_fin N f h i)) (f (fin_index (suc. N) i))
  ≔ fin_index_from_bound N (f (fin_index (suc. N) i))
      (lt_from_book (f (fin_index (suc. N) i)) N
        (h (fin_index (suc. N) i) (lt_to_book (fin_index (suc. N) i) (suc. N) (fin_index_bound (suc. N) i))))

def BoundedCollision (N : Nat) (f : Nat → Nat) : Type
  ≔ Σ Nat (m ↦ Σ Nat (n ↦ Product (BookLt m n) (Product (BookLt n (suc. N)) (Id Nat (f n) (f m)))))

def order_bounded_collision (N : Nat) (f : Nat → Nat) (x y : Nat)
  (hx : Lt x (suc. N)) (hy : Lt y (suc. N)) (neq : Id Nat x y → Empty) (eqn : Id Nat (f x) (f y))
  : BoundedCollision N f
  ≔ match le_total x y [
  | inl. h ↦ (x, (y, (lt_to_book x y (le_not_equal_lt x y h neq),
      (lt_to_book y (suc. N) hy, inverse Nat (f x) (f y) eqn))))
  | inr. h ↦ (y, (x, (lt_to_book y x (le_not_equal_lt y x h (p ↦ neq (inverse Nat y x p))),
      (lt_to_book x (suc. N) hx, eqn)))) ]

{` lem:PHP. The actual witnesses satisfy m < n < N+1 in the book relation. `}
def pigeonhole (N : Nat) (f : Nat → Nat) (h : BoundedNatMap N f) : BoundedCollision N f
  ≔ let c ≔ fin_pigeonhole N (bounded_nat_map_fin N f h) in
    order_bounded_collision N f (fin_index (suc. N) (c .left)) (fin_index (suc. N) (c .right))
      (fin_index_bound (suc. N) (c .left)) (fin_index_bound (suc. N) (c .right))
      (p ↦ c .distinct (fin_index_injective (suc. N) (c .left) (c .right) p))
      (calc
        f (fin_index (suc. N) (c .left)) = fin_index N (bounded_nat_map_fin N f h (c .left))
          by bounded_nat_map_value N f h (c .left)
        = fin_index N (bounded_nat_map_fin N f h (c .right)) by refl (fin_index N) (c .same)
        = f (fin_index (suc. N) (c .right)) by bounded_nat_map_value N f h (c .right) ∎)

{` cor:Fin-n-injective, for the book's bounded-natural-number presentations. `}
def bounded_finite_types_distinct (m n : Nat) (h : BookLt m n)
  (p : Id Type (Σ Nat (k ↦ BookLt k m)) (Σ Nat (k ↦ BookLt k n))) : Empty
  ≔ lt_not_equal m n (lt_from_book m n h)
      (fin_equiv_cardinality m n
        (compose_equiv (Fin m) (Σ Nat (k ↦ BookLt k m)) (Fin n) (fin_book_below_equiv m)
          (compose_equiv (Σ Nat (k ↦ BookLt k m)) (Σ Nat (k ↦ BookLt k n)) (Fin n)
            (id_to_equiv (Σ Nat (k ↦ BookLt k m)) (Σ Nat (k ↦ BookLt k n)) p)
            (canonical_inverse_equiv (Fin n) (Σ Nat (k ↦ BookLt k n)) (fin_book_below_equiv n)))))
