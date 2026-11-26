import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23148
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.and, [9, 14]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (29436 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23148

theorem PEqualNP.Outside.L_meta_23148 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (29436 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23148.circ, PEqualNP.Outside.L_meta_23148.mono, by decide, PEqualNP.Outside.L_meta_23148.rep⟩
