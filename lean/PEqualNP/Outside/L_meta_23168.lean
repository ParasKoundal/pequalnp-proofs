import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23168
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.and, [9, 14]⟩, ⟨GateOp.or, [4, 13]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [16, 18]⟩], 19⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23168

theorem PEqualNP.Outside.L_meta_23168 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_23168.circ, PEqualNP.Outside.L_meta_23168.mono, by decide, PEqualNP.Outside.L_meta_23168.rep⟩
