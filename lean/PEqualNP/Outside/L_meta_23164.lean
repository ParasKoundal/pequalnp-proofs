import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23164
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [13, 10]⟩, ⟨GateOp.and, [0, 14]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [15, 18]⟩], 19⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (14206 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23164

theorem PEqualNP.Outside.L_meta_23164 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14206 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23164.circ, PEqualNP.Outside.L_meta_23164.mono, by decide, PEqualNP.Outside.L_meta_23164.rep⟩
