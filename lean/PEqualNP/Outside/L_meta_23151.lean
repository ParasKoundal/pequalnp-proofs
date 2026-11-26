import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23151
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.and, [10, 14]⟩, ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.or, [15, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (30445 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23151

theorem PEqualNP.Outside.L_meta_23151 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30445 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23151.circ, PEqualNP.Outside.L_meta_23151.mono, by decide, PEqualNP.Outside.L_meta_23151.rep⟩
