import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23158
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (64764 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23158

theorem PEqualNP.Outside.L_meta_23158 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (64764 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23158.circ, PEqualNP.Outside.L_meta_23158.mono, by decide, PEqualNP.Outside.L_meta_23158.rep⟩
