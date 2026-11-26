import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23104
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [13, 15]⟩], 16⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (6127 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_23104

theorem PEqualNP.Outside.L_meta_23104 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (6127 : ℕ).testBit (6 * u.val + v.val)) 8) := by
  exact ⟨PEqualNP.Outside.L_meta_23104.circ, PEqualNP.Outside.L_meta_23104.mono, by decide, PEqualNP.Outside.L_meta_23104.rep⟩
