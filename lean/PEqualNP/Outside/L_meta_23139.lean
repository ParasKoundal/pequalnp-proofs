import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23139
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.or, [3, 15]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [16, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (12670 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23139

theorem PEqualNP.Outside.L_meta_23139 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (12670 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23139.circ, PEqualNP.Outside.L_meta_23139.mono, by decide, PEqualNP.Outside.L_meta_23139.rep⟩
