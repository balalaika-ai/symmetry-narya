export "148-order-gcd-lcm"
export "184-cyc-n-connected-coverings"
export "179-cycles-in-cycle-notation"

{` Chapter 2 results stated for an arbitrary TruncationSignature, instantiated
   at the constructed propositional truncation native_truncation (Mere). `}

def native_same_component_properties (A : Type) (P : A → PropTypes) (x y : A) (p : Mere (Id A x y))
  : Id PropTypes (P x) (P y)
  ≔ same_component_properties native_truncation A P x y p

def native_connected_loops_prop_contractible (A : Type) (hA : Connected A) (h : (a : A) → isProp (Id A a a))
  : BookIsContr A
  ≔ connected_loops_prop_contractible native_truncation A hA h

def native_connected_sigma (A : Type) (B : A → Type) (hA : Connected A) (hB : (a : A) → Connected (B a))
  : Connected (Σ A B)
  ≔ connected_sigma native_truncation A B hA hB

def native_nonempty_to_connected_surjective (A B : Type) (f : A → B) (hA : Mere A) (hB : Connected B)
  : Surjective A B f
  ≔ nonempty_to_connected_surjective native_truncation A B f hA hB

def native_nonempty_connected_embedding_equiv (A B : Type) (f : A → B) (hA : Mere A) (hB : Connected B)
  (h : IsEmbedding A B f) : BookEquiv A B
  ≔ nonempty_connected_embedding_equiv native_truncation A B f hA hB h

def native_surjection_preserves_connected (A B : Type) (f : A → B) (hA : Connected A) (s : Surjective A B f)
  : Connected B
  ≔ surjection_preserves_connected native_truncation A B f hA s

def native_loop_fibers_to_all_ap (n : Nat) (A B : Type) (f : A → B) (hA : Connected A) (a : A)
  (h : ApFibersLevel n A B f a a) : (x y : A) → ApFibersLevel n A B f x y
  ≔ loop_fibers_to_all_ap native_truncation n A B f hA a h

def native_loop_fibers_to_fibers (n : Nat) (A B : Type) (f : A → B) (hA : Connected A) (a : A)
  (h : ApFibersLevel n A B f a a) : (b : B) → HLevel (suc. n) (BookFiber A B f b)
  ≔ loop_fibers_to_fibers native_truncation n A B f hA a h

def native_connected_map_equiv_from_paths (A B : Type) (f : A → B) (hA : Connected A) (hB : Connected B)
  (h : (x y : A) → BookIsEquiv (Id A x y) (Id B (f x) (f y)) (map_path A B f x y)) : BookEquiv A B
  ≔ connected_map_equiv_from_paths native_truncation A B f hA hB h

def native_connected_map_equiv_from_loops (A B : Type) (f : A → B) (hA : Connected A) (hB : Connected B) (a : A)
  (h : BookIsEquiv (Id A a a) (Id B (f a) (f a)) (map_path A B f a a)) : BookEquiv A B
  ≔ connected_map_equiv_from_loops native_truncation A B f hA hB a h

{` def:prop-trunc, the induction principle into families of propositions,
   packaged for the constructed truncation. `}
def native_truncation_induction (A : Type) (P : Mere A → Type) (h : (t : Mere A) → isProp (P t))
  (g : (a : A) → P (mere A a)) (t : Mere A) : P t
  ≔ mere_eliminate A P h g t
