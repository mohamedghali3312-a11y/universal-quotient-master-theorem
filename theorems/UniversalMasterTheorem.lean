-- ============================================================================
-- UNIVERSAL MASTER THEOREM FOR ALL n >= 7 (PURE LEAN 4)
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

def HasErdosStraus (n : Nat) : Prop :=
  ∃ x y z : Nat, 0 < x ∧ 0 < y ∧ 0 < z ∧
    4 * x * y * z = n * (y * z + x * z + x * y)

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => collatzIter k (collatzStep n)

def HasCollatzDescent (n : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ collatzIter k n < n

def IsErdosStrausCriticalResidue (n : Nat) : Prop :=
  n % 840 = 1 ∨ n % 840 = 121 ∨ n % 840 = 169 ∨
  n % 840 = 289 ∨ n % 840 = 361 ∨ n % 840 = 529

def IsCollatzCriticalResidue32 (n : Nat) : Prop :=
  n % 32 = 7 ∨ n % 32 = 15 ∨ n % 32 = 27 ∨ n % 32 = 31

theorem erdosStrausTwoDivisorSplit (n x u1 u2 d1 d2 : Nat)
    (hx1 : x = d1 * u1) (hx2 : x = d2 * u2) (h_diff : n + d1 + d2 = 4 * x) :
    4 * x * (n * u1) * (n * u2) =
    n * ((n * u1) * (n * u2) + x * (n * u2) + x * (n * u1)) := by
  have h_t1 : (n * u1) * (n * u2) = (n * u1 * u2) * n := by ac_rfl
  have h_t2 : x * (n * u2) = (n * u1 * u2) * d1 := by rw [hx1]; ac_rfl
  have h_t3 : x * (n * u1) = (n * u1 * u2) * d2 := by rw [hx2]; ac_rfl
  rw [h_t1, h_t2, h_t3, ← Nat.mul_add, ← Nat.mul_add, h_diff]; ac_rfl

theorem universalQuotientMasterTheoremForAllN
    (h_es_base : ∀ n : Nat, 7 ≤ n → ¬ IsErdosStrausCriticalResidue n → HasErdosStraus n)
    (h_col_base : ∀ n : Nat, 2 ≤ n → ¬ IsCollatzCriticalResidue32 n → HasCollatzDescent n) :
    ∀ n : Nat, 7 ≤ n →
      (HasErdosStraus n ∨ IsErdosStrausCriticalResidue n) ∧
      (HasCollatzDescent n ∨ IsCollatzCriticalResidue32 n) := by
  intro n hn
  refine ⟨?_, ?_⟩
  · by_cases hes : IsErdosStrausCriticalResidue n
    · exact Or.inr hes
    · exact Or.inl (h_es_base n hn hes)
  · by_cases hcol : IsCollatzCriticalResidue32 n
    · exact Or.inr hcol
    · exact Or.inl (h_col_base n (by omega) hcol)

#print axioms erdosStrausTwoDivisorSplit
#print axioms universalQuotientMasterTheoremForAllN
