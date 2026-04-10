-- Binary Search on sorted lists with correctness proofs
-- Lean 4.29.0

/-!
## Sorted predicate
-/

/-- A list is sorted in non-decreasing order. -/
inductive Sorted : List Nat → Prop where
  | nil  : Sorted []
  | single : ∀ x, Sorted [x]
  | cons : ∀ x y t, x ≤ y → Sorted (y :: t) → Sorted (x :: y :: t)

/-!
## Algorithm
-/

/-- Core loop: search `a` for `target` in the inclusive range `[lo, hi]`. -/
def bsearchAux (a : Array Nat) (target : Nat) (lo hi : Nat) : Option Nat :=
  if lo ≤ hi then
    let mid := lo + (hi - lo) / 2
    if a[mid]! = target then
      some mid
    else if a[mid]! < target then
      if mid + 1 > hi then none
      else bsearchAux a target (mid + 1) hi
    else
      if mid = 0 then none
      else bsearchAux a target lo (mid - 1)
  else
    none
termination_by hi + 1 - lo

/-- Unfolding when `lo > hi`. -/
theorem bsearchAux_of_gt (a : Array Nat) (target lo hi : Nat) (h : ¬lo ≤ hi) :
    bsearchAux a target lo hi = none := by
  have := @bsearchAux.eq_1 a target lo hi
  simp only [if_neg h] at this
  exact this

/-- Unfolding when `lo ≤ hi`. -/
theorem bsearchAux_of_le (a : Array Nat) (target lo hi : Nat) (h : lo ≤ hi) :
    bsearchAux a target lo hi =
      if a[lo + (hi - lo) / 2]! = target then some (lo + (hi - lo) / 2)
      else if a[lo + (hi - lo) / 2]! < target then
        if lo + (hi - lo) / 2 + 1 > hi then none
        else bsearchAux a target (lo + (hi - lo) / 2 + 1) hi
      else
        if lo + (hi - lo) / 2 = 0 then none
        else bsearchAux a target lo (lo + (hi - lo) / 2 - 1) := by
  have := @bsearchAux.eq_1 a target lo hi
  simp only [if_pos h] at this
  exact this

/-- Binary search over a `List Nat`. Returns the index when found. -/
def bsearch (l : List Nat) (target : Nat) : Option Nat :=
  let a := l.toArray
  if a.isEmpty then none
  else bsearchAux a target 0 (a.size - 1)

/-!
## Correctness
-/

private theorem mid_lt_size {a : Array Nat} {lo hi : Nat}
    (hle : lo ≤ hi) (hbound : hi < a.size) :
    lo + (hi - lo) / 2 < a.size := by omega

/-- **Soundness** for `bsearchAux`: If `hi < a.size` and the search returns
      `some i`, then `i < a.size` and `a[i]! = target`. -/
theorem bsearchAux_sound (a : Array Nat) (target : Nat) :
    ∀ lo hi : Nat, hi < a.size →
    ∀ i, bsearchAux a target lo hi = some i → i < a.size ∧ a[i]! = target := by
  intro lo hi hbound
  induction fuel : hi + 1 - lo using Nat.strongRecOn generalizing lo hi with
  | ind fuel ih =>
  intro i hres
  by_cases hle : lo ≤ hi
  · rw [bsearchAux_of_le _ _ _ _ hle] at hres
    have hmid_lt : lo + (hi - lo) / 2 < a.size := mid_lt_size hle hbound
    by_cases heq : a[lo + (hi - lo) / 2]! = target
    · -- found: hres : some (lo + (hi-lo)/2) = some i
      simp only [heq, ite_true] at hres
      have hi_eq : i = lo + (hi - lo) / 2 := by injection hres; omega
      exact ⟨hi_eq ▸ hmid_lt, hi_eq ▸ heq⟩
    · simp only [heq, ite_false] at hres
      by_cases hlt : a[lo + (hi - lo) / 2]! < target
      · -- recurse right
        rw [if_pos hlt] at hres
        by_cases hstop : lo + (hi - lo) / 2 + 1 > hi
        · rw [if_pos hstop] at hres; exact absurd hres (by simp)
        · rw [if_neg (by omega)] at hres
          exact ih (hi + 1 - (lo + (hi - lo) / 2 + 1)) (by omega)
            (lo + (hi - lo) / 2 + 1) hi (by omega) (by omega) i hres
      · -- recurse left
        rw [if_neg hlt] at hres
        by_cases hzero : lo + (hi - lo) / 2 = 0
        · rw [if_pos hzero] at hres; exact absurd hres (by simp)
        · rw [if_neg hzero] at hres
          exact ih (lo + (hi - lo) / 2 - 1 + 1 - lo) (by omega)
            lo (lo + (hi - lo) / 2 - 1) (by omega) (by omega) i hres
  · rw [bsearchAux_of_gt _ _ _ _ hle] at hres
    exact absurd hres (by simp)


/-! ### Soundness (list interface) -/

/-- **Soundness**: `bsearch l target = some i` implies `l[i]? = some target`. -/
theorem bsearch_sound (l : List Nat) (target : Nat) (i : Nat) :
    bsearch l target = some i → l[i]? = some target := by
  intro h
  unfold bsearch at h
  by_cases hemp : l.toArray.isEmpty
  · simp [hemp] at h
  · simp only [hemp] at h
    rw [Array.isEmpty_iff] at hemp
    have hsize : 0 < l.toArray.size := by
      cases hq : l.toArray.size with
      | zero => exact absurd (Array.size_eq_zero_iff.mp hq) hemp
      | succ n => omega
    have hbound : l.toArray.size - 1 < l.toArray.size := Nat.sub_lt hsize (by omega)
    obtain ⟨hi_lt, heq⟩ :=
      bsearchAux_sound l.toArray target 0 (l.toArray.size - 1) hbound i h
    simp only [List.size_toArray] at hi_lt
    rw [List.getElem?_eq_some_iff]
    refine ⟨hi_lt, ?_⟩
    have hlt' : i < l.toArray.size := by simp [List.size_toArray, hi_lt]
    rw [getElem!_pos l.toArray i hlt'] at heq
    simpa [List.getElem_toArray] using heq


/-! ### Completeness -/

/-- The array `a` is non-decreasing on the index range `[lo, hi]`. -/
def ArraySorted (a : Array Nat) (lo hi : Nat) : Prop :=
  ∀ i j, lo ≤ i → i < j → j ≤ hi → j < a.size → a[i]! ≤ a[j]!

/-- Monotone on a sub-range implies monotone on any sub-range. -/
private theorem ArraySorted.mono {a : Array Nat} {lo hi lo' hi' : Nat}
    (h : ArraySorted a lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    ArraySorted a lo' hi' :=
  fun i j hi' hij hj' hj'' => h i j (Nat.le_trans hlo hi') hij (Nat.le_trans hj' hhi) hj''

/-- A `Sorted` list gives an `ArraySorted` array (globally). -/
theorem sorted_toArray (l : List Nat) (hs : Sorted l) :
    ArraySorted l.toArray 0 (l.toArray.size - 1) := by
  -- work entirely in terms of List.getElem! via the @[simp] lemma
  -- List.getElem!_toArray : xs.toArray[i]! = xs[i]!
  simp only [List.size_toArray, ArraySorted]
  induction hs with
  | nil =>
    -- empty array: j < 0 is impossible
    intro i j _ _ _ hj; simp at hj
  | single x =>
    -- array of size 1: j ≤ 0 and i < j → i < 0, impossible
    intro i j _ hij hj hjs
    simp only [List.length_singleton] at hjs
    omega
  | cons x y t hxy _ ih =>
    intro i j _ hij hjhi hjsize
    simp only [List.length_cons] at hjhi hjsize
    simp only [List.getElem!_toArray]
    rcases i with _ | i
    · -- i = 0: (x :: y :: t)[0]! = x; need x ≤ (x :: y :: t)[j]!
      simp only [List.getElem!_cons_zero]
      rcases j with _ | j
      · omega
      · simp only [List.getElem!_cons_succ]
        rcases j with _ | j
        · -- j = 0 in tail: (y :: t)[0]! = y ≥ x
          simp [hxy]
        · -- j ≥ 1 in tail: x ≤ y ≤ (y::t)[j+1]! by ih
          have hyle : y ≤ (y :: t)[j + 1]! := by
            simp only [List.getElem!_toArray] at ih
            exact ih 0 (j + 1) (by omega) (by omega)
              (by simp [List.length_cons]; omega)
              (by simp [List.length_cons]; omega)
          omega
    · -- i ≥ 1: shift both into (y :: t)
      rcases j with _ | j
      · omega
      · simp only [List.getElem!_cons_succ]
        simp only [List.getElem!_toArray] at ih
        exact ih i j (by omega) (by omega)
          (by simp [List.length_cons]; omega)
          (by simp [List.length_cons]; omega)

/-- **Key auxiliary**: if `target` is in `a[lo..hi]` and `a` is sorted there,
    then `bsearchAux a target lo hi` returns `some`. -/
theorem bsearchAux_complete (a : Array Nat) (target : Nat) :
    ∀ lo hi : Nat, hi < a.size →
    ArraySorted a lo hi →
    (∃ k, lo ≤ k ∧ k ≤ hi ∧ a[k]! = target) →
    ∃ i, bsearchAux a target lo hi = some i := by
  intro lo hi
  induction fuel : hi + 1 - lo using Nat.strongRecOn generalizing lo hi with
  | ind fuel ih =>
  intro hbound hsorted ⟨k, hklo, hkhi, hkeq⟩
  by_cases hle : lo ≤ hi
  · rw [bsearchAux_of_le _ _ _ _ hle]
    -- work with mid inline to avoid `set` substitution issues
    have hmid_lo : lo ≤ lo + (hi - lo) / 2 := Nat.le_add_right lo _
    have hmid_hi : lo + (hi - lo) / 2 ≤ hi := by omega
    have hmid_lt : lo + (hi - lo) / 2 < a.size := mid_lt_size hle hbound
    by_cases heq : a[lo + (hi - lo) / 2]! = target
    · exact ⟨lo + (hi - lo) / 2, by rw [if_pos heq]⟩
    · rw [if_neg heq]
      by_cases hlt : a[lo + (hi - lo) / 2]! < target
      · -- target is strictly to the right of mid
        rw [if_pos hlt]
        have hk_right : lo + (hi - lo) / 2 + 1 ≤ k := by
          rcases Nat.lt_or_ge k (lo + (hi - lo) / 2) with hlt' | hge
          · -- k < mid ⟹ a[k]! ≤ a[mid]! < target, contradicts a[k]! = target
            have := hsorted k (lo + (hi - lo) / 2) (by omega) hlt' hmid_hi hmid_lt
            omega
          · -- k ≥ mid; if k = mid then a[k]! = a[mid]! ≠ target, contradiction
            rcases Nat.lt_or_eq_of_le hge with hgt | rfl
            · exact hgt
            · exact absurd hkeq (by omega)
        rw [if_neg (by omega)]
        exact ih (hi + 1 - (lo + (hi - lo) / 2 + 1)) (by omega)
          (lo + (hi - lo) / 2 + 1) hi (by omega) (by omega)
          (hsorted.mono (by omega) (by omega))
          ⟨k, hk_right, hkhi, hkeq⟩
      · -- target is strictly to the left of mid (a[mid]! > target)
        rw [if_neg hlt]
        have hgt : target < a[lo + (hi - lo) / 2]! :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_lt hlt) (Ne.symm heq)
        have hk_left : k ≤ lo + (hi - lo) / 2 - 1 := by
          rcases Nat.lt_or_ge k (lo + (hi - lo) / 2) with hlt' | hge
          · omega
          · rcases Nat.lt_or_eq_of_le hge with hgt | rfl
            · -- k > mid ⟹ a[mid]! ≤ a[k]!, contradicts target < a[mid]!
              have := hsorted (lo + (hi - lo) / 2) k hmid_lo hgt (by omega) (by omega)
              omega
            · exact absurd hkeq (by omega)
        -- mid ≠ 0: k ≤ mid - 1 and lo ≤ k, so if mid = 0 then k ≤ 0 and lo ≤ k,
        -- meaning lo = 0, k = 0, mid = 0; but hgt says target < a[mid]! = a[k]! = target.
        have hzero : lo + (hi - lo) / 2 ≠ 0 := by
          intro hmid0
          have hk0 : k = 0 := Nat.le_zero.mp (Nat.le_trans hk_left (hmid0 ▸ Nat.pred_le _))
          have hlo0 : lo = 0 := Nat.le_zero.mp (hk0 ▸ hklo)
          subst hk0 hlo0
          simp at hmid0
          -- goal: target < a[0 + (hi - 0) / 2]! and a[0]! = target
          -- hi < 2 so (hi - 0) / 2 = 0, hence a[0 + 0]! = a[0]! = target, contradiction
          simp only [Nat.sub_zero] at hgt
          have : hi / 2 = 0 := by omega
          rw [this] at hgt
          simp at hgt
          omega
        rw [if_neg hzero]
        exact ih (lo + (hi - lo) / 2 - 1 + 1 - lo) (by omega)
          lo (lo + (hi - lo) / 2 - 1) (by omega) (by omega)
          (hsorted.mono (by omega) (by omega))
          ⟨k, hklo, hk_left, hkeq⟩
  · omega

/-- **Completeness**: sorted list, `target ∈ l` → `bsearch` finds it. -/
theorem bsearch_complete (l : List Nat) (target : Nat)
    (hs : Sorted l) (hm : target ∈ l) :
    ∃ i, bsearch l target = some i := by
  unfold bsearch
  rw [List.mem_iff_getElem] at hm
  obtain ⟨k, hk, hkeq⟩ := hm
  -- l is non-empty because k < l.length
  have hne : l.toArray ≠ #[] := by
    intro heq
    have hlen : l.length = 0 := by
      have h := heq ▸ (List.size_toArray (α := Nat) ▸ rfl : l.toArray.size = l.length)
      simp at h
      exact h.symm
    omega
  simp only [Array.isEmpty_iff, hne, ite_false]
  have hsize : 0 < l.toArray.size := by simp [List.size_toArray]; omega
  apply bsearchAux_complete
  · exact Nat.sub_lt hsize (by omega)
  · exact sorted_toArray l hs
  · refine ⟨k, Nat.zero_le _, ?_, ?_⟩
    · simp [List.size_toArray]; omega
    · rw [List.getElem!_toArray]
      rw [getElem!_pos l k hk]
      exact hkeq
