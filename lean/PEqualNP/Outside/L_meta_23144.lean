import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23144
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [14, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (14141 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23144

theorem PEqualNP.Outside.L_meta_23144 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14141 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23144.circ, PEqualNP.Outside.L_meta_23144.mono, by decide, PEqualNP.Outside.L_meta_23144.rep⟩
