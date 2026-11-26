import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23156
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [3, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (62969 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23156

theorem PEqualNP.Outside.L_meta_23156 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (62969 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23156.circ, PEqualNP.Outside.L_meta_23156.mono, by decide, PEqualNP.Outside.L_meta_23156.rep⟩
