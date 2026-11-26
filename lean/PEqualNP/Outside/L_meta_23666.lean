import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23666 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36029 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.CircuitLowerBounds.Circuit.mk [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [2, 3], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [0, 6], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [1, 7], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [0, 1], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [8], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [9, 10], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [2, 3], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [11, 12]] 13, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
