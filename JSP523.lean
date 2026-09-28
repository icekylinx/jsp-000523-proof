import JSP523.Coarse.AllRank
import JSP523.Rank3.PartIIAsymptotic
import JSP523.Rank4.LocalC8Actual
import JSP523.Rank4.GraphMarkedCapacity
import JSP523.Rank4.ColoredSlotPayment
import JSP523.Counting.IntersectingCovers
import JSP523.Counting.CommonCells
import JSP523.Counting.DistancePacking
import JSP523.Rank5.LocalExactTheorem
import JSP523.Rank5.LocalEqualityExact
import JSP523.Rank5.LocalEqualityConstruction

/-!
# JSP-000523: selected Lean formalization

This is a partial formalization of `paper/proof.pdf`, maintained by Yilin Liu.
The imports cover Theorem I.1; Theorem II.1 and Corollary II.2; the
local rank-four Theorem III.2 and related finite lemmas; the common-cell
assertion (IV.1.1), Lemmas IV.1.1–IV.1.2, and their finite codegree
bounds; and the local rank-at-least-five Theorem IV.2.1 and its equality cases.

The manuscript's Theorem 1 is not yet assembled in Lean. The global
rank-four argument of Theorem III.1 and the global rank-at-least-five
argument of Part IV are in progress.
-/
