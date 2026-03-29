import TraceTheory.Language
import TraceTheory.MyhillNerode

namespace TraceTheory

theorem recognizable_image_of_regular_finite_rank {X : Language α}
    (hX_reg : X.IsRegular)
    (hX_rank : HasFiniteRank I X) :
    IsRecognizable (Trace.mk' I '' X) := by
  sorry

end TraceTheory
