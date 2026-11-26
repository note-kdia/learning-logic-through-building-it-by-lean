import Mathlib.Data.Set.Basic
import Ronri.Logic.Syntax

namespace Ronri.PL

/-- 付値：各原子式に真理値を割り当てる -/
def Valuation (α : Type) := α → Bool

/-- 真理表 (3.1) -/
def eval {α : Type} (v : Valuation α) : Formula α → Bool
  | .var p => v p -- 原子式の場合
  | .not A =>     -- 否定の場合
    match eval v A with
    | true => false
    | false => true
  | .and A B =>   -- 連言の場合
    match eval v A, eval v B with
    | true,  true  => true
    | true,  false => false
    | false, true  => false
    | false, false => false
  | .or A B =>   -- 選言の場合
    match eval v A, eval v B with
    | true,  true  => true
    | true,  false => true
    | false, true  => true
    | false, false => false
  | .imp A B =>   -- 条件法の場合
    match eval v A, eval v B with
    | true,  true  => true
    | true,  false => false
    | false, true  => true
    | false, false => true

/-- トートロジー (3.3) -/
def Tautology {α : Type} (A : Formula α) : Prop :=
  ∀ v, eval v A = true

/-- 矛盾式 (3.3) -/
def Contradiction {α : Type} (A : Formula α) : Prop :=
  ∀ v, eval v A = false

/-- 充足可能式(3.1) -/
def Satisfiable {α : Type} (A : Formula α) : Prop :=
  ∃ v, eval v A = true

end Ronri.PL
