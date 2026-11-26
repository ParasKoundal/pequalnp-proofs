import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23150
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.and, [10, 15]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [13, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (30314 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23150

theorem PEqualNP.Outside.L_meta_23150 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30314 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23150.circ, PEqualNP.Outside.L_meta_23150.mono, by decide, PEqualNP.Outside.L_meta_23150.rep⟩
