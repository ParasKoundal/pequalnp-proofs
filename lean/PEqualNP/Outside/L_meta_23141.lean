import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23141
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [14, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (13180 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23141

theorem PEqualNP.Outside.L_meta_23141 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (13180 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23141.circ, PEqualNP.Outside.L_meta_23141.mono, by decide, PEqualNP.Outside.L_meta_23141.rep⟩
