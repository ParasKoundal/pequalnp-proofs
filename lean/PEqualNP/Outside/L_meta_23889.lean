import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23889 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13084 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.CircuitLowerBounds.Circuit.mk [PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [1, 4], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [3, 4], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.not [5], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [2, 7], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [0, 1], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [6, 9], PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.or [8, 10]] 11, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
