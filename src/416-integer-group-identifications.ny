export "413-group-motivation"
export "405-integer-group"

{` Chapter 4, ex:circlegroup and xca:groups (group.tex 389-418). `}

{` ex:circlegroup, for every circle C: Z ≔ mkgroup(S¹, base) is circle_group C
   (BZ ≡ (S¹, base), circle_group_classifying); S¹ is a connected groupoid
   (native_circle_connected, circle_groupoid); base = base ≃ ℤ with composition
   corresponding to addition (circle_power_mul, circle_winding_mul, module 413);
   and the canonical identification Z = Aut_S¹(base) of
   rem:symmetriesofnonconnectedgroupoids. `}
def circle_group_automorphism_path (C : CircleSignature)
  : Id Group (circle_group C) (automorphism_group (C .carrier) (circle_groupoid C) (C .base))
  ≔ pcg_automorphism_path (circle_pcg C)

{` The type of infinite cycles of def:S1toC, InfCyc = Σ(X : U) Σ(t : X → X) ‖(ℤ, s) = (X, t)‖,
   is InfiniteCycles (the component of (ℤ, s) in Σ(X : U)(X → X)) up to
   reassociation of Σ; thm:S1bysymmetries is circle_infinite_cycles_equiv. `}
def InfiniteCyclesBookForm : Type
  ≔ Σ Type (X ↦ Σ (X → X) (t ↦ Mere (Id Endomorphisms integer_endomorphism (X, t))))

def infinite_cycles_book_form_equiv : Equiv InfiniteCycles InfiniteCyclesBookForm
  ≔ quasi_inverse_equiv InfiniteCycles InfiniteCyclesBookForm
      (u ↦ (u .fst .fst, (u .fst .snd, u .snd))) (w ↦ ((w .fst, w .snd .fst), w .snd .snd))
      (u ↦ refl u) (w ↦ refl w)

def circle_infinite_cycles_book_form (C : CircleSignature) : BookEquiv (C .carrier) InfiniteCyclesBookForm
  ≔ book_equivalence (C .carrier) InfiniteCyclesBookForm
      (compose_equiv (C .carrier) InfiniteCycles InfiniteCyclesBookForm
        (native_equivalence (C .carrier) InfiniteCycles (circle_infinite_cycles_equiv C))
        infinite_cycles_book_form_equiv)

{` The book's Z at the constructed circle: Z = Aut_S¹(base). `}
def integer_group_automorphism_path
  : Id Group integer_group (automorphism_group (CycleComponent zero.) (circle_groupoid constructed_circle)
      (principal_component_point zero.))
  ≔ circle_group_automorphism_path constructed_circle

{` xca:groups. Aut_Cyc(ℤ, s) is cyclic_group 0, whose classifying type is
   (Cyc_0, (ℤ, s)). The constructed circle of chapter 3 is this pointed type
   (S¹ ≔ Cyc_0, modules 220-223, following thm:S1bysymmetries), so
   cyclic_group 0 is circle_group_with constructed_circle c g for its own
   witnesses c, g (by definition). The two identifications are the identity
   and the flip of the circle (module 413); they differ. `}
def integer_cyclic_path : Id Group integer_group (cyclic_group zero.)
  ≔ circle_group_identity_path constructed_circle (native_component_connected Cycles (principal_cycle zero.))
      (component_groupoid Cycles cycles_groupoid (principal_cycle zero.))

def integer_cyclic_flip_path : Id Group integer_group (cyclic_group zero.)
  ≔ circle_group_flip_path constructed_circle (native_component_connected Cycles (principal_cycle zero.))
      (component_groupoid Cycles cycles_groupoid (principal_cycle zero.))

def integer_cyclic_paths_differ
  (h : Id (Id Group integer_group (cyclic_group zero.)) integer_cyclic_path integer_cyclic_flip_path) : Empty
  ≔ circle_group_paths_differ constructed_circle (native_component_connected Cycles (principal_cycle zero.))
      (component_groupoid Cycles cycles_groupoid (principal_cycle zero.)) h
