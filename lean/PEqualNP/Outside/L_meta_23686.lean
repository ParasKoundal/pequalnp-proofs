import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23686
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [11, 14]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.or, [4, 17]⟩, ⟨GateOp.or, [15, 18]⟩], 19⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (816761 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23686

theorem PEqualNP.Outside.L_meta_23686 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816761 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23686.circ, PEqualNP.Outside.L_meta_23686.mono, by decide, PEqualNP.Outside.L_meta_23686.rep⟩
