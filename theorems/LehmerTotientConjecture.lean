-- ============================================================================
-- CONJECTURE #2 : LEHMER'S TOTIENT PROBLEM (φ(n) | n - 1) — PURE LEAN 4
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

theorem not_dvd_both_n_and_pred (n d : Nat) (hd : 2 ≤ d)
    (h_dvd_n : d ∣ n) (h_dvd_pred : d ∣ n - 1) : False := by
  rcases h_dvd_n with ⟨a, ha⟩
  rcases h_dvd_pred with ⟨b, hb⟩
  have h_lt : d * b < d * a := by omega
  have hb_lt_a : b < a := Nat.lt_of_mul_lt_mul_left h_lt
  have h_le : d * (b + 1) ≤ d * a := Nat.mul_le_mul_left d hb_lt_a
  rw [Nat.mul_add, Nat.mul_one] at h_le
  omega

def IsLehmerNumber (phi : Nat → Nat) (n : Nat) : Prop :=
  2 ≤ n ∧ phi n ∣ n - 1

theorem lehmerSquarefreeObstruction
    (phi : Nat → Nat)
    (h_phi_sq : ∀ p n : Nat, 2 ≤ p → p * p ∣ n → p ∣ phi n)
    (n p : Nat) (hp : 2 ≤ p) (h_sq : p * p ∣ n) :
    ¬ IsLehmerNumber phi n := by
  rintro ⟨_, h_lehmer⟩
  have h_p_phi : p ∣ phi n := h_phi_sq p n hp h_sq
  have h_p_pred : p ∣ n - 1 := Nat.dvd_trans h_p_phi h_lehmer
  have h_p_n : p ∣ n := Nat.dvd_trans ⟨p, rfl⟩ h_sq
  exact not_dvd_both_n_and_pred n p hp h_p_n h_p_pred

theorem lehmerMustBeOdd
    (phi : Nat → Nat)
    (h_phi_even : ∀ n : Nat, 3 ≤ n → 2 ∣ phi n)
    (n : Nat) (hn : 3 ≤ n) (h_lehmer : IsLehmerNumber phi n) :
    n % 2 = 1 := by
  have h_2_phi : 2 ∣ phi n := h_phi_even n hn
  have h_2_pred : 2 ∣ n - 1 := Nat.dvd_trans h_2_phi h_lehmer.2
  rcases h_2_pred with ⟨k, hk⟩
  omega

def IsLehmerCandidateObstruction (n : Nat) : Prop :=
  n % 2 = 1 ∧ ∀ p : Nat, 2 ≤ p → ¬ (p * p ∣ n)

theorem lehmerUniversalMasterTheorem
    (phi : Nat → Nat)
    (h_phi_sq : ∀ p n : Nat, 2 ≤ p → p * p ∣ n → p ∣ phi n)
    (h_phi_even : ∀ n : Nat, 3 ≤ n → 2 ∣ phi n) :
    ∀ n : Nat, 3 ≤ n →
      ¬ IsLehmerNumber phi n ∨ IsLehmerCandidateObstruction n := by
  intro n hn
  by_cases h_lehmer : IsLehmerNumber phi n
  · right
    refine ⟨lehmerMustBeOdd phi h_phi_even n hn h_lehmer, ?_⟩
    intro p hp h_sq
    exact lehmerSquarefreeObstruction phi h_phi_sq n p hp h_sq h_lehmer
  · left
    exact h_lehmer

#print axioms not_dvd_both_n_and_pred
#print axioms lehmerSquarefreeObstruction
#print axioms lehmerMustBeOdd
#print axioms lehmerUniversalMasterTheorem
