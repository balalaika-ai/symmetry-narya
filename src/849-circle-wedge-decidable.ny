export "848-decidable-sums-of-groups"
export "879-free-sum-wedges"

{` Litmus for lem:wedgeofgpoidisgpoid (congp.tex:627) at an actual wedge of
   two circles: constructed_circle_wedge (module 879, built without HITs from
   the constructed free group on Bool).  Z ∨ Z obtained by
   decidable_sum_of_groups from this wedge is a decidable group, it is not
   abelian, and β evaluates on a short word to the expected product. `}

def constructed_circle_sum_group : Group
  ≔ circle_decidable_sum_group constructed_circle constructed_circle_wedge

def constructed_circle_sum_group_decidable : IsDecidableGroup constructed_circle_sum_group
  ≔ circle_decidable_sum_group_decidable constructed_circle constructed_circle_wedge

def constructed_circle_sum_not_abelian (h : IsAbelian constructed_circle_sum_group) : Empty
  ≔ circle_decidable_sum_not_abelian constructed_circle constructed_circle_wedge h

def constructed_circle_sum_word_example
  : Id (USym constructed_circle_sum_group)
      (wedge_words_compose (circle_pointed constructed_circle) (circle_pointed constructed_circle)
        constructed_circle_wedge (circle_sum_word_example constructed_circle))
      (usym_mul constructed_circle_sum_group
        (wedge_loop1 (circle_pointed constructed_circle) (circle_pointed constructed_circle) constructed_circle_wedge
          (constructed_circle .loop))
        (usym_mul constructed_circle_sum_group
          (wedge_loop2 (circle_pointed constructed_circle) (circle_pointed constructed_circle) constructed_circle_wedge
            (constructed_circle .loop))
          (wedge_loop1 (circle_pointed constructed_circle) (circle_pointed constructed_circle) constructed_circle_wedge
            (constructed_circle .loop))))
  ≔ circle_sum_word_example_compose constructed_circle constructed_circle_wedge

{` The symmetries of Z ∨ Z are the words: β is an equivalence. `}
def constructed_circle_sum_words_equiv
  : Equiv (WedgeWords (circle_pointed constructed_circle) (circle_pointed constructed_circle))
      (USym constructed_circle_sum_group)
  ≔ decidable_sum_words_equiv (circle_group constructed_circle) (circle_group constructed_circle)
      constructed_circle_wedge (circle_group_decidable constructed_circle) (circle_group_decidable constructed_circle)
