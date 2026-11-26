import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23574
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [12, 11]⟩, ⟨GateOp.or, [11, 9]⟩, ⟨GateOp.or, [14, 8]⟩, ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [16, 19]⟩], 20⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (267254 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23574

theorem PEqualNP.Outside.L_meta_23574 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (267254 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23574.circ, PEqualNP.Outside.L_meta_23574.mono, by decide, PEqualNP.Outside.L_meta_23574.rep⟩
