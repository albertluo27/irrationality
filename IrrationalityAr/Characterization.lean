import IrrationalityAr.RationalCase
import IrrationalityAr.IrrationalCase

namespace IrrationalityAr

/-- Main characterization theorem. This belongs in a separate module so the
rational and irrational directions remain independent and the import graph has
no cycle. -/
theorem rational_iff_eventuallyAP (r : ℝ) :
    IsRational r ↔ IsEventuallyAP (A r) := by
  constructor
  · exact rational_eventuallyAP
  · intro hAP
    by_contra hirr
    exact irrational_no_infiniteAP hirr (eventuallyAP_containsInfiniteAP hAP)

end IrrationalityAr
