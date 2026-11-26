import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23147
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [13, 17]⟩], 18⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (16254 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23147

theorem PEqualNP.Outside.L_meta_23147 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (16254 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_23147.circ, PEqualNP.Outside.L_meta_23147.mono, by decide, PEqualNP.Outside.L_meta_23147.rep⟩
