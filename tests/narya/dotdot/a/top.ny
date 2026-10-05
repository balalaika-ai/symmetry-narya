import "base"
import "../b/mid"

{` mid.ny imports ../a/base.ny. Narya loads it a second time as a/../b/../a/base.ny, so the E of h is a
   different constant from the E of base.ny. `}
def f (x : E) : E ≔ h x
