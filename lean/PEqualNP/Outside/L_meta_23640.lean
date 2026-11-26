import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23640
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.and, [10, 16]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [18, 19]⟩], 20⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (275314 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23640

theorem PEqualNP.Outside.L_meta_23640 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275314 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23640.circ, PEqualNP.Outside.L_meta_23640.mono, by decide, PEqualNP.Outside.L_meta_23640.rep⟩
