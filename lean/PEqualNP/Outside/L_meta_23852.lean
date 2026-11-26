import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23852
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [10, 14]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.or, [15, 18]⟩], 19⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1881579 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23852

theorem PEqualNP.Outside.L_meta_23852 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881579 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23852.circ, PEqualNP.Outside.L_meta_23852.mono, by decide, PEqualNP.Outside.L_meta_23852.rep⟩
