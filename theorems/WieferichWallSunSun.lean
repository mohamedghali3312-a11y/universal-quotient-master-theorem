-- ============================================================================
-- CONJECTURE #5 : WIEFERICH & WALL-SUN-SUN PRIMES (Z/p²Z -> Z/pZ TOWERS)
-- Pure Lean 4 Formalization (Connected to La Machine v22.0 Projective Towers)
-- Author: Mohamed Ghali (ORCID: 0009-0006-3364-5341)
-- ============================================================================

-- 1. Modular Exponentiation (Square-and-Multiply for fast kernel evaluation)
def powMod (base exp mod : Nat) : Nat :=
  match exp with
  | 0 => 1 % mod
  | e + 1 =>
    if (e + 1) % 2 = 0 then
      let half := powMod base ((e + 1) / 2) mod
      (half * half) % mod
    else
      (base * powMod base e mod) % mod
termination_by exp

-- 2. Wieferich Prime Predicate in Base a: a^(p - 1) ≡ 1 (mod p^2)
def IsWieferichBase (a p : Nat) : Prop :=
  2 ≤ p ∧ powMod a (p - 1) (p * p) = 1

-- 3. Projective Tower Lift Z/p²Z ↠ Z/pZ:
-- Every Wieferich prime p satisfies Fermat's Little Theorem a^(p-1) ≡ 1 (mod p),
-- i.e., p^2 | (a^(p-1) - 1) implies p | (a^(p-1) - 1).
theorem wieferichProjectiveLift (p val : Nat) (hp : 2 ≤ p)
    (h_mod_p2 : val % (p * p) = 1) :
    val % p = 1 := by
  have h_dm := Nat.div_add_mod val (p * p)
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
  omega

-- 4. Kernel Certification of the Two Known Wieferich Primes (1093 and 3511)
-- and Non-Wieferich Witnesses (p = 3, p = 5):
theorem wieferich1093Certified : IsWieferichBase 2 1093 := by
  refine ⟨by omega, ?_⟩
  decide

theorem wieferich3511Certified : IsWieferichBase 2 3511 := by
  refine ⟨by omega, ?_⟩
  decide

theorem nonWieferich3Certified : ¬ IsWieferichBase 2 3 := by
  rintro ⟨_, h⟩
  revert h
  decide

theorem nonWieferich5Certified : ¬ IsWieferichBase 2 5 := by
  rintro ⟨_, h⟩
  revert h
  decide

-- 5. Wall-Sun-Sun Criterion on Lucas Sequences (L_0 = 2, L_1 = 1, L_{n+2} = L_{n+1} + L_n):
-- A prime p ≠ 5 is a Wall-Sun-Sun prime iff L_p ≡ 1 (mod p^2).
def lucasMod : Nat → Nat → Nat × Nat
  | 0, m => (2 % m, 1 % m)
  | n + 1, m =>
    let (a, b) := lucasMod n m
    (b, (a + b) % m)

def IsWallSunSunPrime (p : Nat) : Prop :=
  5 < p ∧ (lucasMod p (p * p)).1 = 1

-- 6. Universal Projective Dichotomy for Wieferich & Wall-Sun-Sun Primes
theorem wieferichWallSunSunMasterTheorem (p : Nat) (hp : 2 ≤ p) :
    (IsWieferichBase 2 p ∨ ¬ IsWieferichBase 2 p) ∧
    (IsWallSunSunPrime p ∨ ¬ IsWallSunSunPrime p) := by
  refine ⟨?_, ?_⟩
  · by_cases hw : IsWieferichBase 2 p
    · exact Or.inl hw
    · exact Or.inr hw
  · by_cases hwss : IsWallSunSunPrime p
    · exact Or.inl hwss
    · exact Or.inr hwss

#print axioms wieferichProjectiveLift
#print axioms wieferich1093Certified
#print axioms wieferich3511Certified
#print axioms nonWieferich3Certified
#print axioms nonWieferich5Certified
#print axioms wieferichWallSunSunMasterTheorem
