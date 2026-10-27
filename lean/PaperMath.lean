-- Root module of the `PaperMath` library: everything that `lake build` checks.
-- `Common/`: lemmas reusable across articles. `Papers/<Name>/`: one directory per article.

-- Common
import PaperMath.Common.ZetaSeries
import PaperMath.Common.LogBounds
import PaperMath.Common.ZetaTail
import PaperMath.Common.TrigBounds
import PaperMath.Common.HingeIntegral
import PaperMath.Common.Zeta23Port.MV.Final

-- Papers/RvmClock — "The Riemann–von Mangoldt clock"
import PaperMath.Papers.RvmClock.Maximal
import PaperMath.Papers.RvmClock.Bathtub
import PaperMath.Papers.RvmClock.Transfer
import PaperMath.Papers.RvmClock.Construction
import PaperMath.Papers.RvmClock.MeanValue
import PaperMath.Papers.RvmClock.Mertens
import PaperMath.Papers.RvmClock.Gaps
import PaperMath.Papers.RvmClock.Inputs
import PaperMath.Papers.RvmClock.PrimeFourth
import PaperMath.Papers.RvmClock.Phase
import PaperMath.Papers.RvmClock.Fourth
import PaperMath.Papers.RvmClock.Sublevel
import PaperMath.Papers.RvmClock.Profile
import PaperMath.Papers.RvmClock.ZetaLines
import PaperMath.Papers.RvmClock.ZetaNodes
import PaperMath.Papers.RvmClock.ZetaBound
import PaperMath.Papers.RvmClock.Backlund
import PaperMath.Papers.RvmClock.Explicit
import PaperMath.Papers.RvmClock.Thm13
import PaperMath.Papers.RvmClock.ZetaConst
import PaperMath.Papers.RvmClock.ZetaSigS
import PaperMath.Papers.RvmClock.Thm13Zeta
import PaperMath.Papers.RvmClock.C1
import PaperMath.Papers.RvmClock.ZetaFacts
import PaperMath.Papers.RvmClock.LambdaB
