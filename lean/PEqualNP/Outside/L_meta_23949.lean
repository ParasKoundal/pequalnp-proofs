import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23949 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4894 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.CircuitLowerBounds.Circuit.mk [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [3, 4], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [1, 5], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [0, 6], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [1, 5], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [7, 8], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [8], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [2, 10], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [9, 11]] 12, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
