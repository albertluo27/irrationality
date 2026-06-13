import IrrationalityAr.Basic

namespace IrrationalityAr

/-- `S` contains an infinite arithmetic progression with positive step. -/
def ContainsInfiniteAP (S : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ k : ℕ, a + k * d ∈ S

/-- Beyond a cutoff, membership in `S` is exactly one congruence class modulo a
positive modulus. This is the precise meaning of “eventually an arithmetic
progression” used in the project. -/
def IsEventuallyAP (S : Set ℕ) : Prop :=
  ∃ a d N : ℕ, 0 < d ∧ ∀ n : ℕ, N ≤ n → (n ∈ S ↔ n % d = a % d)

/-- A tail congruence class contains an infinite arithmetic progression.

This proof is intentionally elementary. It is independent of the floor-sum
construction and can be checked before the number-theoretic layers. -/
theorem eventuallyAP_containsInfiniteAP {S : Set ℕ} (h : IsEventuallyAP S) :
    ContainsInfiniteAP S := by
  rcases h with ⟨a, d, N, hd, htail⟩
  refine ⟨a + N * d, d, hd, ?_⟩
  intro k
  apply (htail (a + N * d + k * d) ?_).2
  · rw [show a + N * d + k * d = a + d * (N + k) by ring]
    exact Nat.add_mul_mod_self_left a d (N + k)
  · have hN_le_Nd : N ≤ N * d := Nat.le_mul_of_pos_right N hd
    omega

end IrrationalityAr
