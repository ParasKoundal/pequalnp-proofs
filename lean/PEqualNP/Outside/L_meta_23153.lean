import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23153
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [1, 15]⟩, ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.or, [14, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (30457 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23153

theorem PEqualNP.Outside.L_meta_23153 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30457 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23153.circ, PEqualNP.Outside.L_meta_23153.mono, by decide, PEqualNP.Outside.L_meta_23153.rep⟩
