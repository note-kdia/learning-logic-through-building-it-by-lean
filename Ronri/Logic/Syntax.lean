namespace Ronri.PL

/-- 人工言語Lの論理式 (2.2) -/
inductive Formula (α : Type) where
  | var : α → Formula α
  | not : Formula α → Formula α
  | and : Formula α → Formula α → Formula α
  | or  : Formula α → Formula α → Formula α
  | imp : Formula α → Formula α → Formula α

/-- iff (↔) -/
abbrev Formula.iff {α : Type} (A B : Formula α) : Formula α :=
  .and (.imp A B) (.imp B A)

/-- xor (⊻) -/
abbrev Formula.xor {α : Type} (A B : Formula α) : Formula α :=
  .not (.iff A B)

end Ronri.PL
