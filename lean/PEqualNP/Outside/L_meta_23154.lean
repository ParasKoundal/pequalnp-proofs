import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23154
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [10, 15]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [16, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (32382 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23154

theorem PEqualNP.Outside.L_meta_23154 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (32382 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23154.circ, PEqualNP.Outside.L_meta_23154.mono, by decide, PEqualNP.Outside.L_meta_23154.rep⟩
