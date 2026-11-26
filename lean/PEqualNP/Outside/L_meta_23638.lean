import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23638
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [11, 15]⟩, ⟨GateOp.or, [6, 16]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.and, [14, 19]⟩], 20⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (275261 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23638

theorem PEqualNP.Outside.L_meta_23638 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275261 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23638.circ, PEqualNP.Outside.L_meta_23638.mono, by decide, PEqualNP.Outside.L_meta_23638.rep⟩
