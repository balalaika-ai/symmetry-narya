export "108-minus-two-images"

def connected_set_map_constant (A S : Type) (h : Connected A) (hs : isSet S) (f : A → S)
  : WeaklyConstant A S f
  ≔ x y ↦ mere_rec (Id A x y) (Id S (f x) (f y)) (hs (f x) (f y))
      (map_path A S f x y) (h .snd x y)

def connected_set_map_value (A S : Type) (h : Connected A) (hs : isSet S) (f : A → S) : S
  ≔ weakly_constant_rec A S f hs (connected_set_map_constant A S h hs f) (h .fst)

def connected_set_map_value_beta (A S : Type) (h : Connected A) (hs : isSet S) (f : A → S) (a : A)
  : Id S (connected_set_map_value A S h hs f) (f a)
  ≔ concat S (connected_set_map_value A S h hs f)
      (weakly_constant_rec A S f hs (connected_set_map_constant A S h hs f) (mere A a)) (f a)
      (refl (weakly_constant_rec A S f hs (connected_set_map_constant A S h hs f))
        (mere_isprop A (h .fst) (mere A a)))
      (weakly_constant_rec_beta A S f hs (connected_set_map_constant A S h hs f) a)

def restrict_sections (A B : Type) (p : A → B) (P : B → Type)
  : ((b : B) → P b) → (a : A) → P (p a) ≔ s a ↦ s (p a)

def section_on_fiber (A B : Type) (p : A → B) (P : B → Type) (s : (a : A) → P (p a)) (b : B)
  : BookFiber A B p b → P b
  ≔ w ↦ transport B P (p (w .fst)) b (inverse B b (p (w .fst)) (w .snd)) (s (w .fst))

def extend_connected_sections (A B : Type) (p : A → B) (hp : ConnectedFibers A B p)
  (P : B → Type) (hs : (b : B) → isSet (P b)) (s : (a : A) → P (p a)) (b : B) : P b
  ≔ connected_set_map_value (BookFiber A B p b) (P b) (hp b) (hs b) (section_on_fiber A B p P s b)

def extend_connected_sections_beta (A B : Type) (p : A → B) (hp : ConnectedFibers A B p)
  (P : B → Type) (hs : (b : B) → isSet (P b)) (s : (a : A) → P (p a)) (a : A)
  : Id (P (p a)) (extend_connected_sections A B p hp P hs s (p a)) (s a)
  ≔ concat (P (p a)) (extend_connected_sections A B p hp P hs s (p a))
      (section_on_fiber A B p P s (p a) (a, refl (p a))) (s a)
      (connected_set_map_value_beta (BookFiber A B p (p a)) (P (p a)) (hp (p a)) (hs (p a))
        (section_on_fiber A B p P s (p a)) (a, refl (p a)))
      (concat (P (p a)) (section_on_fiber A B p P s (p a) (a, refl (p a)))
        (transport B P (p a) (p a) (refl (p a)) (s a)) (s a)
        (refl ((q ↦ transport B P (p a) (p a) q (s a)) : Id B (p a) (p a) → P (p a))
          (inverse_refl B (p a))) (transport_refl B P (p a) (s a)))

def extend_connected_sections_eta_point (A B : Type) (p : A → B) (hp : ConnectedFibers A B p)
  (P : B → Type) (hs : (b : B) → isSet (P b)) (s : (b : B) → P b) (b : B)
  : Id (P b) (extend_connected_sections A B p hp P hs (restrict_sections A B p P s) b) (s b)
  ≔ mere_rec (BookFiber A B p b)
      (Id (P b) (extend_connected_sections A B p hp P hs (restrict_sections A B p P s) b) (s b))
      (hs b (extend_connected_sections A B p hp P hs (restrict_sections A B p P s) b) (s b))
      (w ↦ concat (P b) (extend_connected_sections A B p hp P hs (restrict_sections A B p P s) b)
        (section_on_fiber A B p P (restrict_sections A B p P s) b w) (s b)
        (connected_set_map_value_beta (BookFiber A B p b) (P b) (hp b) (hs b)
          (section_on_fiber A B p P (restrict_sections A B p P s) b) w)
        (pathover_transport_equiv B P (p (w .fst)) b (inverse B b (p (w .fst)) (w .snd))
          (s (p (w .fst))) (s b) .map (refl s (inverse B b (p (w .fst)) (w .snd))))) (hp b .fst)

{` The actual restriction map is an equivalence for every family of sets.
   Both inverse laws retain dependent section types and transport. `}
def connected_map_sections_equiv (A B : Type) (p : A → B) (hp : ConnectedFibers A B p)
  (P : B → Type) (hs : (b : B) → isSet (P b))
  : Equiv ((b : B) → P b) ((a : A) → P (p a))
  ≔ quasi_inverse_equiv ((b : B) → P b) ((a : A) → P (p a)) (restrict_sections A B p P)
      (extend_connected_sections A B p hp P hs)
      (s ↦ funext B P (extend_connected_sections A B p hp P hs (restrict_sections A B p P s)) s
        (extend_connected_sections_eta_point A B p hp P hs s))
      (s ↦ funext A (a ↦ P (p a))
        (restrict_sections A B p P (extend_connected_sections A B p hp P hs s)) s
        (extend_connected_sections_beta A B p hp P hs s))

def ConnectedSectionExtensions (A B : Type) (p : A → B) (P : B → Type) (s : (a : A) → P (p a)) : Type
  ≔ BookFiber ((b : B) → P b) ((a : A) → P (p a)) (restrict_sections A B p P) s

def connected_section_extensions_contractible (A B : Type) (p : A → B) (hp : ConnectedFibers A B p)
  (P : B → Type) (hs : (b : B) → isSet (P b)) (s : (a : A) → P (p a))
  : BookIsContr (ConnectedSectionExtensions A B p P s)
  ≔ book_equivalence ((b : B) → P b) ((a : A) → P (p a))
      (connected_map_sections_equiv A B p hp P hs) .equiv s
