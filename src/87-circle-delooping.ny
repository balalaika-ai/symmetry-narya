export "86-general-covering-loop-images"

def loop_inverse_unique (A : Type) (a : A) (p q : Id A a a)
  (h : Id (Id A a a) (concat A a a a p q) (refl a)) : Id (Id A a a) q (inverse A a a p)
  ≔ calc
      q = concat A a a a (inverse A a a p) (concat A a a a p q) by concat_left_inverse A a a a p q
      = concat A a a a (inverse A a a p) (refl a) by refl (concat A a a a (inverse A a a p)) h
      = inverse A a a p by concat_p1 A a a (inverse A a a p) ∎

def LoopMapUnit (A B : Type) (a : A) (b : B) (f : Id A a a → Id B b b) : Type
  ≔ Id (Id B b b) (f (refl a)) (refl b)
def LoopMapComposition (A B : Type) (a : A) (b : B) (f : Id A a a → Id B b b) : Type
  ≔ (p q : Id A a a) → Id (Id B b b) (f (concat A a a a p q)) (concat B b b b (f p) (f q))

def loop_map_inverse (A B : Type) (a : A) (b : B) (f : Id A a a → Id B b b)
  (unit : LoopMapUnit A B a b f) (composition : LoopMapComposition A B a b f) (p : Id A a a)
  : Id (Id B b b) (f (inverse A a a p)) (inverse B b b (f p))
  ≔ loop_inverse_unique B b (f p) (f (inverse A a a p)) (calc
      concat B b b b (f p) (f (inverse A a a p)) = f (concat A a a a p (inverse A a a p))
        by composition p (inverse A a a p)
      = f (refl a) by refl f (concat_inverse_right A a a p)
      = refl b by unit ∎)

def loop_map_power_nat (A B : Type) (a : A) (b : B) (f : Id A a a → Id B b b)
  (unit : LoopMapUnit A B a b f) (composition : LoopMapComposition A B a b f) (p : Id A a a) (n : Nat)
  : Id (Id B b b) (f (loop_power_nat A a p n)) (loop_power_nat B b (f p) n)
  ≔ match n [
  | zero. ↦ unit
  | suc. n ↦ concat (Id B b b) (f (loop_power_nat A a p (suc. n)))
      (concat B b b b (f (loop_power_nat A a p n)) (f p)) (loop_power_nat B b (f p) (suc. n))
      (composition (loop_power_nat A a p n) p)
      (refl ((q ↦ concat B b b b q (f p)) : Id B b b → Id B b b) (loop_map_power_nat A B a b f unit composition p n)) ]

def loop_map_power (A B : Type) (a : A) (b : B) (f : Id A a a → Id B b b)
  (unit : LoopMapUnit A B a b f) (composition : LoopMapComposition A B a b f) (p : Id A a a) (z : Int)
  : Id (Id B b b) (f (loop_power A a p z)) (loop_power B b (f p) z)
  ≔ match z [
  | pos. n ↦ loop_map_power_nat A B a b f unit composition p n
  | neg. n ↦ concat (Id B b b) (f (loop_power_nat A a (inverse A a a p) (suc. n)))
      (loop_power_nat B b (f (inverse A a a p)) (suc. n)) (loop_power B b (f p) (neg. n))
      (loop_map_power_nat A B a b f unit composition (inverse A a a p) (suc. n))
      (refl ((q ↦ loop_power_nat B b q (suc. n)) : Id B b b → Id B b b) (loop_map_inverse A B a b f unit composition p)) ]

def circle_rec_based_action (C : CircleSignature) (A : Type) (a : A) (l : Id A a a)
  (p : Id (C .carrier) (C .base) (C .base)) : Id A a a
  ≔ let f ≔ circle_rec C A (a, l) in
    transport A (x ↦ Id A x x) (f (C .base)) a (circle_rec_beta C A (a, l) .fst) (refl f p)

def circle_rec_based_power (C : CircleSignature) (A : Type) (a : A) (l : Id A a a) (z : Int)
  : Id (Id A a a) (circle_rec_based_action C A a l (loop_power (C .carrier) (C .base) (C .loop) z)) (loop_power A a l z)
  ≔ let f ≔ circle_rec C A (a, l) in let q ≔ circle_rec_beta C A (a, l) in
    let tr ≔ transport A (x ↦ Id A x x) (f (C .base)) a (q .fst) in
    concat (Id A a a) (circle_rec_based_action C A a l (loop_power (C .carrier) (C .base) (C .loop) z))
      (tr (loop_power A (f (C .base)) (refl f (C .loop)) z)) (loop_power A a l z)
      (refl tr (map_loop_power (C .carrier) A f (C .base) (C .loop) z))
      (pathover_transport_equiv A (x ↦ Id A x x) (f (C .base)) a (q .fst)
        (loop_power A (f (C .base)) (refl f (C .loop)) z) (loop_power A a l z)
        .map (refl (free_loop_power A z) q .snd))

def circle_delooping_action (C : CircleSignature) (A : Type) (a : A)
  (e : Equiv (Id (C .carrier) (C .base) (C .base)) (Id A a a))
  (unit : LoopMapUnit (C .carrier) A (C .base) a (e .map))
  (composition : LoopMapComposition (C .carrier) A (C .base) a (e .map))
  (p : Id (C .carrier) (C .base) (C .base))
  : Id (Id A a a) (circle_rec_based_action C A a (e .map (C .loop)) p) (e .map p)
  ≔ calc
      circle_rec_based_action C A a (e .map (C .loop)) p
      = circle_rec_based_action C A a (e .map (C .loop)) (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p))
        by refl (circle_rec_based_action C A a (e .map (C .loop))) (circle_power_winding C p)
      = loop_power A a (e .map (C .loop)) (circle_winding C p)
        by circle_rec_based_power C A a (e .map (C .loop)) (circle_winding C p)
      = e .map (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p))
        by loop_map_power (C .carrier) A (C .base) a (e .map) unit composition (C .loop) (circle_winding C p)
      = e .map p by refl (e .map) (circle_power_winding C p) ∎

def circle_delooping_loops (C : CircleSignature) (A : Type) (a : A)
  (e : Equiv (Id (C .carrier) (C .base) (C .base)) (Id A a a))
  (unit : LoopMapUnit (C .carrier) A (C .base) a (e .map))
  (composition : LoopMapComposition (C .carrier) A (C .base) a (e .map))
  : Equiv (Id (C .carrier) (C .base) (C .base))
      (Id A (circle_rec C A (a, e .map (C .loop)) (C .base)) (circle_rec C A (a, e .map (C .loop)) (C .base)))
  ≔ let f ≔ circle_rec C A (a, e .map (C .loop)) in
    let q ≔ circle_rec_beta C A (a, e .map (C .loop)) .fst in
    let T ≔ Id A (f (C .base)) (f (C .base)) in
    let tr ≔ transport_equiv T (Id A a a) (refl ((x ↦ Id A x x) : A → Type) q) in
    let normalized ≔ equiv_change_map (Id (C .carrier) (C .base) (C .base)) (Id A a a) e
      (circle_rec_based_action C A a (e .map (C .loop)))
      (p ↦ inverse (Id A a a) (circle_rec_based_action C A a (e .map (C .loop)) p) (e .map p)
        (circle_delooping_action C A a e unit composition p)) in
    equiv_change_map (Id (C .carrier) (C .base) (C .base)) T
      (compose_equiv (Id (C .carrier) (C .base) (C .base)) (Id A a a) T normalized (canonical_inverse_equiv T (Id A a a) tr))
      (map_path (C .carrier) A f (C .base) (C .base))
      (p ↦ equiv_retraction T (Id A a a) tr (refl f p))

{` lem:S1-delooping: the map is the specified circle recursor.  The coherent
   base computation is propositional under the supplied CircleSignature. `}
def circle_delooping_equiv (C : CircleSignature) (A : Type) (connected : Connected A) (a : A)
  (e : Equiv (Id (C .carrier) (C .base) (C .base)) (Id A a a))
  (unit : LoopMapUnit (C .carrier) A (C .base) a (e .map))
  (composition : LoopMapComposition (C .carrier) A (C .base) a (e .map)) : BookEquiv (C .carrier) A
  ≔ connected_map_equiv_from_loops native_truncation (C .carrier) A (circle_rec C A (a, e .map (C .loop)))
      (native_circle_connected C) connected (C .base)
      (book_equivalence (Id (C .carrier) (C .base) (C .base))
        (Id A (circle_rec C A (a, e .map (C .loop)) (C .base)) (circle_rec C A (a, e .map (C .loop)) (C .base)))
        (circle_delooping_loops C A a e unit composition) .equiv)
