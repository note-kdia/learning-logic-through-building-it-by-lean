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

/--
練習問題9 (1) (c)
命題: A->BがトートロジーでAが充足可能ならばBも充足可能である。
-/
theorem ex9_1c (A B : Formula α) : Tautology (.imp A B) → Satisfiable A → Satisfiable B := by
  intro hAB hA
  obtain ⟨v, hAv⟩ := hA
  specialize hAB v
  unfold eval at hAB
  rw [hAv] at hAB
  exists v
  cases hB : eval v B with
  | false =>
    rw [hB] at hAB
    exact hAB
  | true => rfl


/--
練習問題9 (2) のための定義
定義: 結合子として→と∧のみを含むような論理式
-/
def OnlyImpAnd {α : Type} : Formula α → Prop
  | .var _ => True
  | .not _ => False
  | .or _ _ => False
  | .and A B => OnlyImpAnd A ∧ OnlyImpAnd B
  | .imp A B => OnlyImpAnd A ∧ OnlyImpAnd B

/--
練習問題9 (2) のための補題
命題: 結合子として→と∧のみを含むような論理式は、各原子式がtrueのとき必ず真になる
-/
lemma onlyImpAnd_eval_true (A : Formula α) : OnlyImpAnd A -> eval (fun _ => true) A = true := by
  induction A with 
  | var p =>
    intro h
    rfl
  | not A ih =>
    intro h
    unfold OnlyImpAnd at h
    exact False.elim h
  | or A B ihA ihB =>
    intro h
    unfold OnlyImpAnd at h
    exact False.elim h
  | and A B ihA ihB =>
    intro h
    obtain ⟨hA, hB⟩ := h
    specialize ihA hA
    specialize ihB hB
    simp only [eval]
    rw [ihA, ihB]
  | imp A B ihA ihB =>
    intro h
    obtain ⟨hA, hB⟩ := h
    specialize ihA hA
    specialize ihB hB
    simp only [eval]
    rw [ihA, ihB]

/--
練習問題9 (2)
命題: 結合子として→と∧のみを含むような論理式はすべて充足可能である
-/
theorem ex9_2 (A : Formula α) : OnlyImpAnd A → Satisfiable A := by
  intro h
  exists (fun _ => true)
  exact onlyImpAnd_eval_true A h

end Ronri.PL
