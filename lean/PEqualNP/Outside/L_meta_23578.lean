import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23578
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [12, 14]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [1, 18]⟩, ⟨GateOp.and, [17, 19]⟩], 20⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (270841 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23578

theorem PEqualNP.Outside.L_meta_23578 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (270841 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23578.circ, PEqualNP.Outside.L_meta_23578.mono, by decide, PEqualNP.Outside.L_meta_23578.rep⟩
