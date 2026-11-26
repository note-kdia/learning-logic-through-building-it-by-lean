import Ronri.Logic.Semantics

namespace Ronri.PL

/-- 練習問題9 (1) (a) -/
theorem ex9_1a (A B : Formula α) : Tautology (.imp A B) → Tautology A → Tautology B := by
  intro hAB hA v
  specialize hAB v
  specialize hA v
  unfold eval at hAB
  rw [hA] at hAB
  cases hB : eval v B with
  | false =>
    rw [hB] at hAB
    exact hAB
  | true => rfl

/--
練習問題9 (1) (b)
成立しないため、A = P, B = P ∧ ¬ P のときに矛盾することを示す
-/
theorem ex9_1b : ¬ (∀ A B : Formula String, Satisfiable (.imp A B) → Satisfiable A → Satisfiable B) := by
  intro h
  have hAB : Satisfiable (.imp (.var "p") (.and (.var "p") (.not (.var "p")))) :=
    ⟨fun _ => false, rfl⟩
  have hA : Satisfiable (.var "p") :=
    ⟨fun _ => true, rfl⟩
  obtain ⟨v, hv⟩ := h _ _ hAB hA
  simp only [eval] at hv
  cases hp : v "p" with
  | false =>
    rw [hp] at hv
    dsimp only at hv
    contradiction
  | true =>
    rw [hp] at hv
    dsimp only at hv
    contradiction

end Ronri.PL
