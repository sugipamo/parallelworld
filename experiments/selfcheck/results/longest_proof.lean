import Gamma

namespace PWStmt
def S0 : (Prop) := ((((Spec.NestedCopulaBounds) : (List ℚ → ℚ × ℚ × ℚ) → Prop) ((fun p : List ℚ => match p with | [] => ((0 : ℚ), (1 : ℚ), (0 : ℚ)) | a :: t => (max 0 ((a :: t).sum - (((a :: t).length : ℚ) - 1)), (a :: t).prod, t.foldr min a)) : (List ℚ → ℚ × ℚ × ℚ))))
end PWStmt

theorem pw_goal : PWStmt.S0 := by
  unfold PWStmt.S0
  try dsimp only
  unfold Spec.NestedCopulaBounds
  intro p hne hp
  have hprod : ∀ L : List ℚ, (∀ x ∈ L, 0 ≤ x ∧ x ≤ 1) → 0 ≤ L.prod ∧ L.prod ≤ 1 := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons b L ih =>
      intro h
      have hb := h b (List.mem_cons_self b L)
      have hL := ih (fun x hx => h x (List.mem_cons_of_mem b hx))
      rw [List.prod_cons]
      constructor
      · exact mul_nonneg hb.1 hL.1
      · nlinarith [hb.1, hb.2, hL.1, hL.2]
  have hW : ∀ L : List ℚ, (∀ x ∈ L, 0 ≤ x ∧ x ≤ 1) → L.sum - ((L.length : ℚ) - 1) ≤ L.prod := by
    intro L
    induction L with
    | nil => intro _; simp
    | cons b L ih =>
      intro h
      have hb := h b (List.mem_cons_self b L)
      have h' : ∀ x ∈ L, 0 ≤ x ∧ x ≤ 1 := fun x hx => h x (List.mem_cons_of_mem b hx)
      have hL := ih h'
      have hP := hprod L h'
      rw [List.prod_cons, List.sum_cons, List.length_cons]
      push_cast
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (sub_nonneg.mpr hP.2)]
  have hfold : ∀ (t : List ℚ) (a : ℚ), t.foldr min a ≤ a := by
    intro t a
    induction t with
    | nil => simp
    | cons b t ih => simp only [List.foldr_cons]; exact le_trans (min_le_right _ _) ih
  have hpm : ∀ (t : List ℚ) (a : ℚ), (∀ x ∈ a :: t, 0 ≤ x ∧ x ≤ 1) → (a :: t).prod ≤ t.foldr min a := by
    intro t
    induction t with
    | nil => intro a _; simp
    | cons b t ih =>
      intro a h
      have ha := h a (List.mem_cons_self a _)
      have hb := h b (List.mem_cons_of_mem a (List.mem_cons_self b t))
      have ht : ∀ x ∈ t, 0 ≤ x ∧ x ≤ 1 := fun x hx => h x (List.mem_cons_of_mem a (List.mem_cons_of_mem b hx))
      have hat : ∀ x ∈ a :: t, 0 ≤ x ∧ x ≤ 1 := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact ht x hx
      have ih' := ih a hat
      have hP := hprod t ht
      rw [List.prod_cons] at ih'
      simp only [List.prod_cons, List.foldr_cons]
      apply le_min
      · have haP : a * t.prod ≤ 1 := by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hP.2)]
        nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr haP)]
      · nlinarith [mul_nonneg (mul_nonneg ha.1 hP.1) (sub_nonneg.mpr hb.2), ih']
  cases p with
  | nil => exact absurd rfl hne
  | cons a t =>
    have hp' : ∀ x ∈ a :: t, 0 ≤ x ∧ x ≤ 1 := hp
    exact ⟨le_max_left _ _, max_le (hprod _ hp').1 (hW _ hp'), hpm t a hp', le_trans (hfold t a) (hp' a (List.mem_cons_self a t)).2⟩
