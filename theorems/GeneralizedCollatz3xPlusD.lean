-- ============================================================================
-- CONJECTURE #4 : GENERALIZED COLLATZ DYNAMICS (3x + d & 5x + 1) — PURE LEAN 4
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

def step3xPlusD (d n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + d

def iter3xPlusD (d : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter3xPlusD d k (step3xPlusD d n)

def Has3xPlusDDescent (d n : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ iter3xPlusD d k n < n

-- 1. Universal Even Descent (50% of all integers for ANY d)
theorem collatz3xPlusDEvenDescent (d m : Nat) (hm : 1 ≤ m) :
    iter3xPlusD d 1 (2 * m) < 2 * m := by
  simp only [iter3xPlusD, step3xPlusD]
  omega

-- 2. Universal Mod 4 Descent for d ≡ 1 (mod 8)
theorem collatz3xPlusDMod4Eq1Descent (j m : Nat) (hm : 2 * j + 1 ≤ m) :
    iter3xPlusD (8 * j + 1) 3 (4 * m + 1) < 4 * m + 1 := by
  simp only [iter3xPlusD, step3xPlusD]
  omega

-- 3. Universal Mod 4 Descent for d ≡ 3 (mod 4)
theorem collatz3xPlusDMod4Eq3Descent (j m : Nat) (hm : j + 1 ≤ m) :
    iter3xPlusD (4 * j + 3) 3 (4 * m + 3) < 4 * m + 3 := by
  simp only [iter3xPlusD, step3xPlusD]
  omega

-- 4. Crandall 5x + 1 Operator and Exact Non-Trivial 10-Step Cycle at n = 13
def step5xPlus1 (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 5 * n + 1

def iter5xPlus1 : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter5xPlus1 k (step5xPlus1 n)

theorem crandall5xPlus1Cycle13 : iter5xPlus1 10 13 = 13 := by
  decide

-- 5. Universal 3x + d Master Dichotomy
theorem generalizedCollatzMasterTheorem (d : Nat) (hd : d % 2 = 1) :
    ∀ n : Nat, 2 * d + 2 ≤ n →
      Has3xPlusDDescent d n ∨ (n % 4 = 1 ∨ n % 4 = 3) := by
  intro n hn
  by_cases h0 : n % 2 = 0
  · left
    refine ⟨1, by omega, ?_⟩
    have hn_eq : n = 2 * (n / 2) := by omega
    rw [hn_eq]
    exact collatz3xPlusDEvenDescent d (n / 2) (by omega)
  · right
    omega

#print axioms collatz3xPlusDEvenDescent
#print axioms collatz3xPlusDMod4Eq1Descent
#print axioms collatz3xPlusDMod4Eq3Descent
#print axioms crandall5xPlus1Cycle13
#print axioms generalizedCollatzMasterTheorem
