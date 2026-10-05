export "68-subgroup-cycles"

def cycle_subgroup_laws (c : Cycles) : IntegerSubgroupLaws (CyclePeriods c)
  ≔ (power_period_zero (c .fst .fst .fst) (c .fst .snd),
      (power_period_add (c .fst .fst .fst) (c .fst .snd), power_period_neg (c .fst .fst .fst) (c .fst .snd)))

def period_image_subgroup (H : Subtypes Int)
  : Mere (BookFiber Cycles (Subtypes Int) CyclePeriods H) → IntegerSubgroupLaws H
  ≔ mere_rec (BookFiber Cycles (Subtypes Int) CyclePeriods H) (IntegerSubgroupLaws H) (integer_subgroup_laws_prop H)
      (w ↦ transport (Subtypes Int) IntegerSubgroupLaws (CyclePeriods (w .fst)) H
        (inverse (Subtypes Int) H (CyclePeriods (w .fst)) (w .snd)) (cycle_subgroup_laws (w .fst)))

def subgroup_period_image (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Mere (BookFiber Cycles (Subtypes Int) CyclePeriods H)
  ≔ mere (BookFiber Cycles (Subtypes Int) CyclePeriods H)
      (subgroup_cycle H h, inverse (Subtypes Int) (CyclePeriods (subgroup_cycle H h)) H (subgroup_cycle_periods H h))

{` cor:set-trunc-cyc, pointwise equality of the displayed image predicate
   and the subgroup predicate. `}
def period_image_characterization (H : Subtypes Int)
  : Equiv (Mere (BookFiber Cycles (Subtypes Int) CyclePeriods H)) (IntegerSubgroupLaws H)
  ≔ iff_equiv (Mere (BookFiber Cycles (Subtypes Int) CyclePeriods H)) (IntegerSubgroupLaws H)
      (mere_isprop (BookFiber Cycles (Subtypes Int) CyclePeriods H)) (integer_subgroup_laws_prop H)
      (period_image_subgroup H) (subgroup_period_image H)

def period_image_predicate : Subtypes (Subtypes Int)
  ≔ H ↦ (Mere (BookFiber Cycles (Subtypes Int) CyclePeriods H), mere_isprop (BookFiber Cycles (Subtypes Int) CyclePeriods H))
def subgroup_predicate : Subtypes (Subtypes Int) ≔ H ↦ (IntegerSubgroupLaws H, integer_subgroup_laws_prop H)

def period_image_is_subgroups : Id (Subtypes (Subtypes Int)) period_image_predicate subgroup_predicate
  ≔ funext (Subtypes Int) (_ ↦ PropTypes) period_image_predicate subgroup_predicate
      (H ↦ proposition_extensionality (period_image_predicate H) (subgroup_predicate H)
        (period_image_subgroup H) (subgroup_period_image H))

def cycle_period_image_equiv : Equiv (Image Cycles (Subtypes Int) CyclePeriods) IntegerSubgroups
  ≔ family_equiv (Subtypes Int) (H ↦ Mere (BookFiber Cycles (Subtypes Int) CyclePeriods H))
      IntegerSubgroupLaws period_image_characterization

def Order : Type ≔ SetTrunc Cycles
def cycle_order : Cycles → Order ≔ set_trunc Cycles
def order_set : isSet Order ≔ set_trunc_set Cycles
def infinite_order : Order ≔ cycle_order infinite_cycle

def order_periods : Order → Subtypes Int
  ≔ set_trunc_rec Cycles (Subtypes Int) (subtypes_set Int) CyclePeriods

def order_periods_injective : PathReflecting Order (Subtypes Int) order_periods
  ≔ quotient_rec_injective Cycles (Subtypes Int) (mere_path_relation Cycles) (subtypes_set Int) CyclePeriods
      (set_trunc_respects Cycles (Subtypes Int) (subtypes_set Int) CyclePeriods) cycle_periods_imply_paths

def order_subgroup_laws (d : Order) : IntegerSubgroupLaws (order_periods d)
  ≔ set_trunc_induction Cycles (d ↦ IntegerSubgroupLaws (order_periods d))
      (d ↦ prop_is_set (IntegerSubgroupLaws (order_periods d)) (integer_subgroup_laws_prop (order_periods d)))
      cycle_subgroup_laws d

def order_to_subgroup (d : Order) : IntegerSubgroups ≔ (order_periods d, order_subgroup_laws d)
def subgroup_to_order (H : IntegerSubgroups) : Order ≔ cycle_order (subgroup_cycle (H .fst) (H .snd))

def order_subgroup_roundtrip (d : Order) : Id Order (subgroup_to_order (order_to_subgroup d)) d
  ≔ order_periods_injective (subgroup_to_order (order_to_subgroup d)) d
      (subgroup_cycle_periods (order_periods d) (order_subgroup_laws d))

def subgroup_order_roundtrip (H : IntegerSubgroups) : Id IntegerSubgroups (order_to_subgroup (subgroup_to_order H)) H
  ≔ subtype_equal (Subtypes Int) IntegerSubgroupLaws integer_subgroup_laws_prop
      (order_to_subgroup (subgroup_to_order H)) H (subgroup_cycle_periods (H .fst) (H .snd))

def orders_subgroups_equiv : Equiv Order IntegerSubgroups
  ≔ quasi_inverse_equiv Order IntegerSubgroups order_to_subgroup subgroup_to_order
      order_subgroup_roundtrip subgroup_order_roundtrip

{` def:standard-cycle: no representative of an order is selected. `}
def standard_cycle (d : Order) : Cycles ≔ subgroup_cycle (order_periods d) (order_subgroup_laws d)
def standard_cycle_order (d : Order) : Id Order (cycle_order (standard_cycle d)) d ≔ order_subgroup_roundtrip d

def OrderDivides (d k : Order) : Type ≔ Inclusion Int (order_periods k) (order_periods d)
def order_divides_prop (d k : Order) : isProp (OrderDivides d k)
  ≔ inclusion_prop Int (order_periods k) (order_periods d)
def order_divides_refl (d : Order) : OrderDivides d d ≔ inclusion_refl Int (order_periods d)
def order_divides_trans (d k l : Order) (h : OrderDivides d k) (g : OrderDivides k l) : OrderDivides d l
  ≔ inclusion_trans Int (order_periods l) (order_periods k) (order_periods d) g h
def order_divides_antisym (d k : Order) (h : OrderDivides d k) (g : OrderDivides k d) : Id Order d k
  ≔ order_periods_injective d k (inclusion_antisym Int (order_periods d) (order_periods k) g h)
