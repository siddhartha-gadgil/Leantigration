import Mathlib

variable {α : Type}[LinearOrder α]

def belowPivot (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x ≤  pivot)

def abovePivot (pivot : α) (l : List α) : List α :=
  l.filter (fun x => x > pivot)

def quickSort : List α → List α
  | [] => []
  | pivot :: l =>
    have : (belowPivot pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    have : (abovePivot pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    (quickSort (belowPivot pivot l)) ++ pivot :: (quickSort (abovePivot pivot l))
termination_by l => l.length

theorem quickSort_nil : quickSort ([] : List α) = [] := by
  rfl

theorem quickSort_cons (pivot : α) (l : List α) :
  quickSort (pivot :: l) = (quickSort (belowPivot pivot l)) ++ pivot :: (quickSort (abovePivot pivot l)) := by
  rfl

theorem mem_iff_below_or_above_pivot (pivot : α) (l : List α)(x : α) :
  x ∈ l ↔ x ∈ belowPivot pivot l ∨ x ∈ abovePivot pivot l := by
    apply Iff.intro
    · intro h
      by_cases h' : x ≤ pivot
      · apply Or.inl
        apply List.mem_filter_of_mem h
        simp
        assumption
      · apply Or.inr
        apply List.mem_filter_of_mem h
        simp
        apply lt_of_not_ge
        assumption
    · intro h
      cases h
      case mpr.inl h' =>
        exact List.mem_of_mem_filter h'
      case mpr.inr h' =>
        exact List.mem_of_mem_filter h'

theorem mem_iff_mem_quickSort (l: List α)(x : α) :
  x ∈ l ↔ x ∈ quickSort l := by
    match l with
    | [] =>
      simp [quickSort_nil]
    | pivot :: l =>
      rw [quickSort_cons]
      simp
      rw [mem_iff_below_or_above_pivot pivot ]
      have : (belowPivot pivot l).length < (pivot :: l).length := by
        simp [List.length_cons]
        apply Nat.succ_le_succ
        apply List.length_filter_le
      have : (abovePivot pivot l).length < (pivot :: l).length := by
        simp [List.length_cons]
        apply Nat.succ_le_succ
        apply List.length_filter_le
      let ihb := mem_iff_mem_quickSort (belowPivot pivot l)
      let iha := mem_iff_mem_quickSort (abovePivot pivot l)
      rw [← ihb, ← iha]
      aesop
termination_by l.length

inductive Sorted : List α → Prop
  | nil : Sorted []
  | singleton (x : α) : Sorted [x]
  | step (x y : α) (l : List α) :
    x ≤ y → Sorted (y :: l) → Sorted (x :: y :: l)

theorem append_sorted (bound: α)(l₁ l₂ : List α) :
  (∀ x ∈ l₁, x ≤ bound) → (∀ x ∈ l₂, bound ≤  x) → Sorted l₁ → Sorted l₂ → Sorted (l₁ ++ l₂) := by
  intro h₁ h₂ s₁
  induction s₁
  case nil =>
    intro s₂
    exact s₂
  case singleton x =>
    simp at h₁
    intro s₂
    induction s₂
    case nil =>
      apply Sorted.singleton
    case singleton y =>
      apply Sorted.step x y
      · simp at h₂
        trans bound
        · assumption
        · assumption
      · apply Sorted.singleton
    case step y z l hxy s _ =>
      simp
      apply Sorted.step x y
      · trans bound
        · assumption
        · simp [List.mem_cons] at h₂
          exact h₂.left
      · exact Sorted.step y z l hxy s
  case step x y l hxy _ ih =>
    intro s₂
    apply Sorted.step x y (l ++ l₂) hxy
    rw [← List.cons_append]
    have : (y :: l).length + l₂.length < (x :: y :: l).length + l₂.length := by
      simp
    apply ih
    · simp [List.mem_cons]
      simp [List.mem_cons] at h₁
      apply And.intro
      · apply h₁.right.left
      · apply h₁.right.right
    · exact s₂

theorem quickSort_sorted (l : List α) : Sorted (quickSort l) := by
  match l with
    | [] =>
      simp [quickSort_nil]
      apply Sorted.nil
    | pivot :: l =>
      rw [quickSort_cons]
      have : (belowPivot pivot l).length < (pivot :: l).length := by
        simp [List.length_cons]
        apply Nat.succ_le_succ
        apply List.length_filter_le
      have : (abovePivot pivot l).length < (pivot :: l).length := by
        simp [List.length_cons]
        apply Nat.succ_le_succ
        apply List.length_filter_le
      let ihb := quickSort_sorted (belowPivot pivot l)
      let iha := mem_iff_mem_quickSort (abovePivot pivot l)
      apply append_sorted pivot
      · sorry
      · simp
        sorry
      · assumption
      · sorry
termination_by l.length
