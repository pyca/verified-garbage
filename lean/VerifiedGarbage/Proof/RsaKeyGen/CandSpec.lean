import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.RsaKeyGen.MillerRabin

/-!
# A candidate, as the implementations compute it

`candidateStep` for a prime of `L = 8 w` octets, restated with the octets of
the randomness at offsets (`seg r a n`, the `n` octets from `a`):
`candidateStep_eq`. Its Miller–Rabin loop, one witness at a time from an
offset (`mrLoop_step`, `mrLoop_done`), each witness's test by the flag of
`MillerRabin.lean` (`mrIteration_cand`).
-/

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Spec.Rsa

theorem ite_t {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) : (if p then a else b) = a := by
  simp [h]

theorem ite_f {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) : (if p then a else b) = b := by
  simp [h]

/-- The `n` octets of `r` from `a`. -/
def seg (r : Rand) (a n : Nat) : List Byte := (r.drop a).take n

theorem draw_drop (r : Rand) (a n : Nat) (hn : 0 < n) :
    draw n (r.drop a) = if a + n ≤ r.length then some (os2ip (seg r a n), r.drop (a + n)) else none := by
  unfold draw seg
  simp only [List.length_take, List.length_drop, List.drop_drop]
  by_cases h : a + n ≤ r.length
  · rw [ite_t (by omega), ite_t h, Nat.add_comm]
  · rw [ite_f (by omega), ite_f h]

/-- What `candidateStep` makes of a candidate `c` once drawn, for the
randomness `r'` after it. -/
def afterDraw (bits e : Nat) (p : Option Nat) (c : Nat) (r' : Rand) : Option (Candidate × Rand) :=
  if tooClose bits p c then some (.close, r')
  else if !obviouslyComposite bits c && Nat.gcd (c - 1) e == 1 then
    (primalityTest c r').map fun pr => (if pr.1 then .prime c else .rejected, pr.2)
  else some (.rejected, r')

/-- `candidateStep`: the candidate from the first `L` octets, then
`afterDraw`. -/
theorem candidateStep_eq (L e : Nat) (p : Option Nat) (r : Rand) (hL : 0 < L) :
    candidateStep (8 * L) e p r =
      if L ≤ r.length then afterDraw (8 * L) e p (candidate (8 * L) (os2ip (seg r 0 L))) (r.drop L)
      else none := by
  have hd := draw_drop r 0 L hL
  simp only [List.drop_zero, Nat.zero_add] at hd
  unfold candidateStep afterDraw
  rw [show 8 * L / 8 = L by omega, hd]
  by_cases h : L ≤ r.length
  · simp only [h, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]
    split
    · rfl
    · split
      · cases primalityTest (candidate (8 * L) (os2ip (seg r 0 L))) (r.drop L) with
        | none => rfl
        | some pr =>
          obtain ⟨b, r''⟩ := pr
          cases b <;> rfl
      · rfl
  · simp [h]

/-! ## Miller–Rabin, one witness at a time -/

/-- The witnesses' loop, at the offset `used` of `r`, with the state
`(i, uniform)` that draws: the next `L` octets give a witness; it proves `c`
composite, or the loop goes on from the state it counts. -/
theorem mrLoop_step (c checks a m L : Nat) (r : Rand) (i uni used : Nat) (hgo : i ≤ blindedChecks ∨ uni < checks)
    (hwb : witnessBytes c = L) (hL : 0 < L) :
    loop (mrStep c checks a m) (i, uni) (r.drop used) =
      if used + L ≤ r.length then
        if mrIteration c a m (witness (c - 1) (os2ip (seg r used L))).1 then
          loop (mrStep c checks a m)
            (i + 1, uni + if (witness (c - 1) (os2ip (seg r used L))).2 then 1 else 0) (r.drop (used + L))
        else some (false, r.drop (used + L))
      else none := by
  rw [loop]
  unfold mrStep
  by_cases h : used + L ≤ r.length
  · by_cases hm : mrIteration c a m (witness (c - 1) (os2ip (seg r used L))).1 = true
    · simp only [hgo, ↓reduceIte, hwb, draw_drop r used L hL, h, hm, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, List.length_drop]
      exact ite_t (by omega) _ _
    · simp only [hgo, ↓reduceIte, hwb, draw_drop r used L hL, h, hm, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Bool.false_eq_true]
  · simp only [hgo, ↓reduceIte, hwb, draw_drop r used L hL, h, Option.bind_eq_bind, Option.bind_none]

/-- The witnesses' loop, once enough have passed: `c` is probably prime. -/
theorem mrLoop_done (c checks a m : Nat) (r : Rand) (i uni : Nat) (hgo : ¬(i ≤ blindedChecks ∨ uni < checks)) :
    loop (mrStep c checks a m) (i, uni) r = some (true, r) := by
  rw [loop]
  unfold mrStep
  simp only [hgo, ↓reduceIte]

/-! ## The candidate's shape -/

theorem bitLength_eq {n b : Nat} (h1 : 2 ^ b ≤ n) (h2 : n < 2 ^ (b + 1)) : bitLength n = b + 1 := by
  unfold bitLength
  rw [ite_f (by have := Nat.two_pow_pos b; omega), (Nat.log2_eq_iff (by have := Nat.two_pow_pos b; omega)).mpr ⟨h1, h2⟩]

/-- A candidate of `64 w` bits: the bits of it and of it minus one, and the
octets of a witness. -/
theorem cand_bits {w c : Nat} (hw : 1 ≤ w) (hc : PrimeShape (64 * w) c) :
    bitLength c = 64 * w ∧ bitLength (c - 1) = 64 * w ∧ witnessBytes c = 8 * w := by
  obtain ⟨hodd, hlo, hhi⟩ := hc
  have h2 : 2 ^ (64 * w) = 2 ^ (64 * w - 2) * 4 := by
    rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]; congr 1; omega
  have h1 : 2 ^ (64 * w - 1) = 2 ^ (64 * w - 2) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have hb1 := bitLength_eq (n := c) (b := 64 * w - 1) (by omega) (by rw [show 64 * w - 1 + 1 = 64 * w by omega]; omega)
  have hb2 := bitLength_eq (n := c - 1) (b := 64 * w - 1) (by omega)
    (by rw [show 64 * w - 1 + 1 = 64 * w by omega]; omega)
  refine ⟨by rw [hb1]; omega, by rw [hb2]; omega, ?_⟩
  unfold witnessBytes
  rw [hb2, show 64 * w - 1 + 1 = 64 * w by omega]
  omega

/-- A witness's test, by the flag over the bits of `c − 1` from the top
(`T = 64 w`). -/
theorem mrIteration_cand {w c b : Nat} (hw : 1 ≤ w) (hc : PrimeShape (64 * w) c) (P : Bool) :
    mrIteration c (splitTwos (c - 1)).1 (splitTwos (c - 1)).2 b = mrRun c b (64 * w - 1) P := by
  obtain ⟨hb, hb1, _⟩ := cand_bits hw hc
  obtain ⟨hodd, hlo, hhi⟩ := hc
  have : 4 ≤ 2 ^ (64 * w - 2) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  exact (mrRun_eq (T := 64 * w) (by omega) hodd (by omega) (by rw [hb]; exact Nat.le_refl _) P).symm

/-- `primalityTest` of a candidate: the witnesses' loop from `(1, 0)`. -/
theorem primalityTest_cand {w c : Nat} (hw : 1 ≤ w) (hc : PrimeShape (64 * w) c) (r : Rand) :
    primalityTest c r = loop (mrStep c (checksForSize (64 * w)) (splitTwos (c - 1)).1 (splitTwos (c - 1)).2)
      (1, 0) r := by
  obtain ⟨hb, _, _⟩ := cand_bits hw hc
  obtain ⟨hodd, hlo, hhi⟩ := hc
  have : 4 ≤ 2 ^ (64 * w - 2) := by
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ (64 * w - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold primalityTest
  rw [ite_f (by omega), ite_f (by omega), ite_f (by omega), hb]

/-- `BN_prime_checks_for_size` for the sizes of the candidates, as the
implementations choose it from `w`. -/
def checksW (w : Nat) : Nat :=
  if w < 5 then 27 else if w < 6 then 8 else if w < 7 then 7 else if w < 8 then 6 else
  if w < 22 then 5 else if w < 59 then 4 else 3

theorem checksW_eq : ∀ w < 65, 4 ≤ w → checksForSize (64 * w) = checksW w := by decide

end VG.Proof.RsaKeyGen
