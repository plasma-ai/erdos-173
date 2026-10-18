module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Families in general position

A family `s : Fin n → V` in a finite-dimensional vector space is in general position
when each of its subfamilies with at most `finrank K V` members is linearly
independent. If a set `A` meets the complement of every finite union of proper
subspaces, it contains families in general position of every length: choose each
new member outside the spans of all small subfamilies of the previous ones.
-/

@[expose] public section

noncomputable section

namespace Erdos173.Template

open Module

variable (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Every subfamily with at most `finrank K V` members is linearly independent. -/
def GeneralFamily {n : ℕ} (s : Fin n → V) : Prop :=
  ∀ t : Finset (Fin n), t.card ≤ finrank K V → LinearIndepOn K s (t : Set (Fin n))

variable {K}

/-- Families in general position from avoidance of finitely many proper subspaces. -/
lemma exists_generalFamily [FiniteDimensional K V] (A : Set V)
    (ha : ∀ P : Finset (Submodule K V), (∀ p ∈ P, p < ⊤) → ∃ x ∈ A, ∀ p ∈ P, x ∉ p) (n : ℕ) :
    ∃ s : Fin n → V, (∀ i, s i ∈ A) ∧ GeneralFamily K s := by
  classical
  induction n with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, fun t _ => ?_⟩
    have : t = ∅ := Finset.eq_empty_of_forall_notMem fun i => i.elim0
    simp [this, linearIndepOn_empty]
  | succ n ih =>
    obtain ⟨s, hA, hg⟩ := ih
    let B := (Finset.univ : Finset (Finset (Fin n))).filter (fun t => t.card < finrank K V)
    let P := B.image (fun t : Finset (Fin n) => Submodule.span K (s '' (t : Set (Fin n))))
    have hP : ∀ p ∈ P, p < ⊤ := by
      intro p hp
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
      have hc : t.card < finrank K V := (Finset.mem_filter.mp ht).2
      apply Submodule.lt_top_of_finrank_lt_finrank
      have h1 := finrank_span_finset_le_card (R := K) (t.image s)
      have h2 : (t.image s).card ≤ t.card := Finset.card_image_le
      rw [Finset.coe_image] at h1
      exact (h1.trans h2).trans_lt hc
    obtain ⟨x, hx, havoid⟩ := ha P hP
    have havo (t : Finset (Fin n)) (hc : t.card < finrank K V) :
        x ∉ Submodule.span K (s '' (t : Set (Fin n))) :=
      havoid _ (Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩, rfl⟩)
    refine ⟨Fin.snoc s x, fun i => ?_, fun t ht => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa using hx
      | cast i => simpa using hA i
    let t' := (Finset.univ : Finset (Fin n)).filter (fun i => Fin.castSucc i ∈ t)
    have hcomp : (Fin.snoc s x : Fin (n + 1) → V) ∘ Fin.castSucc = s := by
      funext i
      simp
    have himage : Fin.castSucc '' (t' : Set (Fin n)) = (t : Set (Fin (n + 1))) \ {Fin.last n} := by
      ext i
      induction i using Fin.lastCases with
      | last => simp [t', Fin.castSucc_ne_last]
      | cast i => simp [t', Fin.castSucc_ne_last]
    have hcard : t'.card + (if Fin.last n ∈ t then 1 else 0) ≤ t.card := by
      have hsub : t'.map Fin.castSuccEmb ⊆ t.erase (Fin.last n) := by
        intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
        exact Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last j, (Finset.mem_filter.mp hj).2⟩
      have h := Finset.card_le_card hsub
      rw [Finset.card_map] at h
      split_ifs with hl
      · rw [Finset.card_erase_of_mem hl] at h
        have := Finset.card_pos.mpr ⟨_, hl⟩
        omega
      · exact h.trans (Finset.card_erase_le)
    have hold : LinearIndepOn K (Fin.snoc s x : Fin (n + 1) → V)
        (Fin.castSucc '' (t' : Set (Fin n))) :=
      LinearIndepOn.image_of_comp _ _ (by rw [hcomp]; exact hg t' (by split_ifs at hcard <;> omega))
    by_cases hl : Fin.last n ∈ t
    · have he : (t : Set (Fin (n + 1))) =
          insert (Fin.last n) (Fin.castSucc '' (t' : Set (Fin n))) := by
        rw [himage]
        ext i
        by_cases hi : i = Fin.last n
        · subst hi
          simpa using hl
        · simp [hi]
      rw [he, linearIndepOn_insert (by rw [himage]; simp)]
      refine ⟨hold, ?_⟩
      rw [Fin.snoc_last, ← Set.image_comp, hcomp]
      exact havo t' (by rw [ite_eq_left hl] at hcard; omega)
    · have he : (t : Set (Fin (n + 1))) = Fin.castSucc '' (t' : Set (Fin n)) := by
        rw [himage]
        ext i
        by_cases hi : i = Fin.last n
        · subst hi
          simpa using hl
        · simp [hi]
      rw [he]
      exact hold

/-- In a family in general position, any `finrank K V` members form a basis. -/
lemma GeneralFamily.linearIndependent {n : ℕ} {s : Fin n → V} (hs : GeneralFamily K s)
    (e : Fin (finrank K V) ↪ Fin n) : LinearIndependent K (s ∘ e) := by
  classical
  have h := hs (Finset.univ.map e) (by simp)
  have hc : LinearIndependent K (fun i : ((Finset.univ.map e : Finset (Fin n)) : Set (Fin n)) =>
      s i) := h
  exact hc.comp (fun i => ⟨e i, by simp⟩) (fun i j hij => e.injective (congrArg Subtype.val hij))

end Erdos173.Template

end
