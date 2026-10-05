import VerifiedGarbage.Spec.Ecdsa.Rfc6979

/-!
# Deterministic ECDSA: the search for a candidate, step by step

For a curve and hash function whose candidates are each one `V`
(`blocks = 1`), `K` and `V` before candidate `i` (`kvAt`), and the search
from there: a suitable candidate ends it (`search_ok`), an unsuitable one
moves to the next (`search_fail`), so after `i` unsuitable candidates the
search is the one from candidate `i`, `i` candidates later (`search_shift`).
The same for candidates of `b` `V`s each, `b = blocks` (`kvAtB`, `candAtB`,
`searchB_ok`, `searchB_fail`, `searchB_shift`).
-/

namespace VG.Proof.Ecdsa.Rfc6979

open VG.Spec.Ecdsa.Rfc6979 VG.Spec.Weierstrass

variable (C : Curve) (H : Spec.Hmac.HashFunction) (hlen : Nat)

/-- `K` and `V` after an unsuitable candidate `HMAC_K(V)`. -/
def step (K V : List Byte) : List Byte × List Byte := next H K (Spec.Hmac.hmac H K V)

/-- `K` and `V` before candidate `i`. -/
def kvAt (K V : List Byte) : Nat → List Byte × List Byte
  | 0 => (K, V)
  | i + 1 => step H (kvAt K V i).1 (kvAt K V i).2

/-- Candidate `i`'s `V`. -/
def candAt (K V : List Byte) (i : Nat) : List Byte := Spec.Hmac.hmac H (kvAt H K V i).1 (kvAt H K V i).2

variable {C H hlen}

theorem genT_one (K V : List Byte) : genT H K 1 V = (Spec.Hmac.hmac H K V ++ [], Spec.Hmac.hmac H K V) := rfl

theorem search_ok (hb : blocks C hlen = 1) {d e : Nat} {K V : List Byte} {n : Nat} {rs : Nat × Nat}
    (h : Spec.Ecdsa.signWith C d e (bits2int C (Spec.Hmac.hmac H K V ++ [])) = some rs) :
    search C H hlen d e K V (n + 1) = (some rs, 1) := by
  simp only [search, hb, genT_one, h]

theorem search_fail (hb : blocks C hlen = 1) {d e : Nat} {K V : List Byte} {n : Nat}
    (h : Spec.Ecdsa.signWith C d e (bits2int C (Spec.Hmac.hmac H K V ++ [])) = none) :
    search C H hlen d e K V (n + 1) =
      ((search C H hlen d e (step H K V).1 (step H K V).2 n).1,
        (search C H hlen d e (step H K V).1 (step H K V).2 n).2 + 1) := by
  simp only [search, hb, genT_one, h, step]

/-- A search with candidates left tries at least one. -/
theorem search_pos (hb : blocks C hlen = 1) {d e : Nat} {K V : List Byte} {n : Nat} :
    1 ≤ (search C H hlen d e K V (n + 1)).2 := by
  cases h : Spec.Ecdsa.signWith C d e (bits2int C (Spec.Hmac.hmac H K V ++ [])) with
  | some rs => rw [search_ok hb h]; exact Nat.le_refl 1
  | none => rw [search_fail hb h]; omega

theorem search_shift (hb : blocks C hlen = 1) {d e : Nat} {K V : List Byte} :
    ∀ i n, i ≤ n → (∀ j < i, Spec.Ecdsa.signWith C d e (bits2int C (candAt H K V j ++ [])) = none) →
      search C H hlen d e K V n =
        ((search C H hlen d e (kvAt H K V i).1 (kvAt H K V i).2 (n - i)).1,
          (search C H hlen d e (kvAt H K V i).1 (kvAt H K V i).2 (n - i)).2 + i)
  | 0, n, _, _ => by simp [kvAt]
  | i + 1, n, hi, hf => by
    rw [search_shift hb i n (by omega) fun j hj => hf j (by omega),
      show n - i = (n - (i + 1)) + 1 by omega, search_fail hb (hf i (by omega))]
    simp only [kvAt, Prod.mk.injEq, true_and]
    omega

end VG.Proof.Ecdsa.Rfc6979

/-! ## Candidates of `b` `V`s -/

namespace VG.Proof.Ecdsa.Rfc6979

open VG.Spec.Ecdsa.Rfc6979 VG.Spec.Weierstrass

variable {C : Curve} {H : Spec.Hmac.HashFunction} {hlen : Nat}

variable (H) in
/-- `K` and `V` after an unsuitable candidate of `b` `V`s. -/
def stepB (b : Nat) (K V : List Byte) : List Byte × List Byte := next H K (genT H K b V).2

variable (H) in
/-- `K` and `V` before candidate `i`, of `b` `V`s each. -/
def kvAtB (b : Nat) (K V : List Byte) : Nat → List Byte × List Byte
  | 0 => (K, V)
  | i + 1 => stepB H b (kvAtB b K V i).1 (kvAtB b K V i).2

variable (H) in
/-- Candidate `i`'s `T`, of `b` `V`s. -/
def candAtB (b : Nat) (K V : List Byte) (i : Nat) : List Byte :=
  (genT H (kvAtB H b K V i).1 b (kvAtB H b K V i).2).1

theorem searchB_ok {b : Nat} (hb : blocks C hlen = b) {d e : Nat} {K V : List Byte} {n : Nat} {rs : Nat × Nat}
    (h : Spec.Ecdsa.signWith C d e (bits2int C (genT H K b V).1) = some rs) :
    search C H hlen d e K V (n + 1) = (some rs, 1) := by
  subst hb
  rcases hg : genT H K (blocks C hlen) V with ⟨T, V'⟩
  rw [hg] at h
  simp only [search, hg, h]

theorem searchB_fail {b : Nat} (hb : blocks C hlen = b) {d e : Nat} {K V : List Byte} {n : Nat}
    (h : Spec.Ecdsa.signWith C d e (bits2int C (genT H K b V).1) = none) :
    search C H hlen d e K V (n + 1) =
      ((search C H hlen d e (stepB H b K V).1 (stepB H b K V).2 n).1,
        (search C H hlen d e (stepB H b K V).1 (stepB H b K V).2 n).2 + 1) := by
  subst hb
  rcases hg : genT H K (blocks C hlen) V with ⟨T, V'⟩
  rw [hg] at h
  simp only [search, hg, h, stepB]

/-- A search with candidates left tries at least one. -/
theorem searchB_pos {b : Nat} (hb : blocks C hlen = b) {d e : Nat} {K V : List Byte} {n : Nat} :
    1 ≤ (search C H hlen d e K V (n + 1)).2 := by
  cases h : Spec.Ecdsa.signWith C d e (bits2int C (genT H K b V).1) with
  | some rs => rw [searchB_ok hb h]; exact Nat.le_refl 1
  | none => rw [searchB_fail hb h]; omega

theorem searchB_shift {b : Nat} (hb : blocks C hlen = b) {d e : Nat} {K V : List Byte} :
    ∀ i n, i ≤ n → (∀ j < i, Spec.Ecdsa.signWith C d e (bits2int C (candAtB H b K V j)) = none) →
      search C H hlen d e K V n =
        ((search C H hlen d e (kvAtB H b K V i).1 (kvAtB H b K V i).2 (n - i)).1,
          (search C H hlen d e (kvAtB H b K V i).1 (kvAtB H b K V i).2 (n - i)).2 + i)
  | 0, n, _, _ => by simp [kvAtB]
  | i + 1, n, hi, hf => by
    rw [searchB_shift hb i n (by omega) fun j hj => hf j (by omega),
      show n - i = (n - (i + 1)) + 1 by omega, searchB_fail hb (hf i (by omega))]
    simp only [kvAtB, Prod.mk.injEq, true_and]
    omega

end VG.Proof.Ecdsa.Rfc6979
