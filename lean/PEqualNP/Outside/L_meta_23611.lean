import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23611
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [17, 15]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [18, 19]⟩], 20⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (272173 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23611

theorem PEqualNP.Outside.L_meta_23611 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (272173 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23611.circ, PEqualNP.Outside.L_meta_23611.mono, by decide, PEqualNP.Outside.L_meta_23611.rep⟩
