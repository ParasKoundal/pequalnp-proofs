import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23157
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [11, 16]⟩, ⟨GateOp.or, [12, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (62971 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23157

theorem PEqualNP.Outside.L_meta_23157 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (62971 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23157.circ, PEqualNP.Outside.L_meta_23157.mono, by decide, PEqualNP.Outside.L_meta_23157.rep⟩
