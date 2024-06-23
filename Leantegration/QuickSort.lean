import Mathlib.Data.List.Basic
import Mathlib.Tactic

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
      · left
        apply List.mem_filter_of_mem h
        simp
        assumption
      · right
        apply List.mem_filter_of_mem h
        simp
        apply lt_of_not_ge
        assumption
    · intro h
      cases h
      case mpr.inl h' =>
        apply List.mem_of_mem_filter
        assumption
      case mpr.inr h' =>
        exact List.mem_of_mem_filter h'

theorem mem_iff_mem_quickSort (l: List α)(x : α) :
  x ∈ l ↔ x ∈ quickSort l := by
    match l with
    | [] =>
      simp [quickSort_nil]
    | pivot :: l =>
      simp [quickSort_cons]
      rw [mem_iff_below_or_above_pivot pivot]
      have : (belowPivot pivot l).length < l.length + 1 := by
        apply Nat.succ_le_succ
        apply List.length_filter_le
      let ihb := mem_iff_mem_quickSort (belowPivot pivot l)
      have : (abovePivot pivot l).length < l.length + 1 := by
        apply Nat.succ_le_succ
        apply List.length_filter_le
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
    simp
  case singleton x =>
    simp at h₁
    intro s₂
    cases s₂
    case nil =>
      apply Sorted.singleton
    case singleton y =>
      apply Sorted.step x y
      · simp at h₂
        trans bound <;> assumption
      · apply Sorted.singleton
    case step y z l hyz s =>
      simp
      apply Sorted.step x y
      · trans bound
        · assumption
        · simp [List.mem_cons] at h₂
          exact h₂.left
      · exact Sorted.step y z l hyz s
  case step x y l hxy _ ih =>
    intro s₂
    apply Sorted.step x y (l ++ l₂) hxy
    rw [← List.cons_append]
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
      let iha := quickSort_sorted (abovePivot pivot l)
      apply append_sorted pivot
      · intro x
        rw [← mem_iff_mem_quickSort]
        intro h
        let lem := List.of_mem_filter h
        simp at lem
        assumption
      · simp
        intro x
        rw [← mem_iff_mem_quickSort]
        intro h
        let lem := List.of_mem_filter h
        simp at lem
        apply le_of_lt
        assumption
      · assumption
      · apply append_sorted pivot [pivot] (quickSort (abovePivot pivot l))
        · simp
        · intro x h
          rw [← mem_iff_mem_quickSort] at h
          let lem := List.of_mem_filter h
          simp at lem
          apply le_of_lt
          assumption
        · apply Sorted.singleton
        · assumption
termination_by l.length

def quickSortTask (depth: Nat) : List α → Task (List α)
  | [] => Task.pure []
  | pivot :: l =>
    have : (belowPivot pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    have : (abovePivot pivot l).length < (pivot :: l).length := by
      simp [List.length_cons]
      apply Nat.succ_le_succ
      apply List.length_filter_le
    match depth with
    | 0 =>
      Task.spawn fun _ => (quickSort (belowPivot pivot l)) ++ pivot :: (quickSort (abovePivot pivot l))
    | d + 1 =>
    let t₁ :=
      quickSortTask d (belowPivot pivot l)
    let t₂ := quickSortTask d (abovePivot pivot l)
    t₁.bind fun l₁ =>
      t₂.map fun l₂ =>
        l₁ ++ pivot :: l₂
termination_by l => l.length

def quickSortPar (depth: Nat) (l : List α) : List α :=
  (quickSortTask depth l).get

example (n: Nat): (n + 1)/2 < n + 1 := by
  exact Nat.div_lt_self' n 0

#check Array.eraseIdx
#check Array.size_filter_le


variable [Inhabited α]
partial def quickSortArr (arr : Array α) : Array α :=
  if arr.size ≤ 1 then arr else
  let pivot := arr.get! 0
  let arr := arr.eraseIdx 0
  let (l, r) := arr.partition (fun x => x ≤ pivot)
  let l := quickSortArr l
  let r := quickSortArr r
  l.push pivot ++ r

partial def quickSortArrTask (depth: Nat) (arr : Array α) : Task (Array α) :=
  if arr.size ≤ 1 then Task.pure arr else
  match depth with
  | 0 =>
    Task.spawn fun _ =>
      quickSortArr arr
  | d + 1 =>
  let pivot := arr.get! 0
  let arr := arr.eraseIdx 0
  let (l, r) := arr.partition (fun x => x ≤ pivot)
  let l := quickSortArrTask d l
  let r := quickSortArrTask d r
  l.bind fun l =>
    r.map fun r =>
      l.push pivot ++ r

def quickSortArrPar (depth: Nat) (arr : Array α) : Array α :=
  (quickSortArrTask depth arr).get
