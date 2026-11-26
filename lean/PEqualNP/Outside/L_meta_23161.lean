import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23161
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (130039 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23161

theorem PEqualNP.Outside.L_meta_23161 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (130039 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23161.circ, PEqualNP.Outside.L_meta_23161.mono, by decide, PEqualNP.Outside.L_meta_23161.rep⟩
