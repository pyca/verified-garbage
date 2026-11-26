module

import VerifiedGarbage.Proof.RsaKeyGen.Primes
public import VerifiedGarbage.Impl.RsaKeyGen.Primes
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.RsaKeyGen.Primes
meta import VerifiedGarbage.Impl.RsaKeyGen.Primes
meta import VerifiedGarbage.Spec.RsaKeyGen
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The table of small primes

`Impl.RsaKeyGen.slots` is the candidates' table, on every target: the primes
3 to 3671, 3, then the primes 3673 to 8161. Its entries are odd, from 3 to
8161 (`tabEntry_facts`), and trial division by its first 512 (or all 1024)
entries is `obviouslyComposite` for primes of up to 1024 (or more) bits
(`trialAny_eq`). The primes are evaluated once, as a literal
(`primes.lit_eq`), from the literal of the sieve (`compMask.lit_eq`): its
33,000 steps `m ||| 2 ^ (d * k)` are, for each `d`, a geometric sum
(`multMask_eq`), which the kernel computes by one division.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen

/-- `Σ_{k < n} 2^(d k)`. -/
def powSum (d : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 1 + 2 ^ d * powSum d n

theorem powSum_eq {d : Nat} (hd : 0 < d) (n : Nat) : powSum d n = (2 ^ (d * n) - 1) / (2 ^ d - 1) := by
  have h2 : 1 < 2 ^ d := Nat.one_lt_two_pow (Nat.ne_of_gt hd)
  have e : (2 ^ d - 1) * powSum d n + 1 = 2 ^ (d * n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, Nat.pow_add, ← ih, powSum]
      generalize powSum d n = p
      obtain ⟨a, ha⟩ : ∃ a, 2 ^ d = a + 1 := ⟨2 ^ d - 1, (Nat.sub_add_cancel (Nat.le_of_lt h2)).symm⟩
      rw [ha, Nat.add_sub_cancel]
      simp only [Nat.mul_add, Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm]
      omega_using []
  rw [← e, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (Nat.sub_pos_of_lt h2)]

/-- `multMask`'s fold over the `n` numbers from `k ≥ 2`, from a mask of lower bits. -/
theorem foldl_range'_eq {d : Nat} (hd : 0 < d) : ∀ n k m, 2 ≤ k → m < 2 ^ (d * k) →
    (List.range' k n).foldl (fun m k => if 2 ≤ k then m ||| 2 ^ (d * k) else m) m = m + 2 ^ (d * k) * powSum d n
  | 0, _, _, _, _ => rfl
  | n + 1, k, m, hk, hm => by
    have h1 : m ||| 2 ^ (d * k) = m + 2 ^ (d * k) := by
      have := Nat.two_pow_add_eq_or_of_lt hm 1
      rw [Nat.mul_one] at this
      rw [Nat.or_comm, ← this, Nat.add_comm]
    have h2 : m + 2 ^ (d * k) < 2 ^ (d * (k + 1)) := by
      refine Nat.lt_of_lt_of_le (Nat.add_lt_add_right hm _) ?_
      rw [← Nat.two_mul, ← Nat.pow_succ']
      exact Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_succ]; omega_using [hd])
    rw [List.range'_succ, List.foldl_cons, ite_eq_left hk, h1, foldl_range'_eq hd n (k + 1) _ (Nat.le_succ_of_le hk) h2,
      powSum]
    simp only [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_assoc, Nat.add_assoc]

/-- `multMask`, a geometric sum: the multiples from the second on. -/
def multMaskF (d : Nat) : Nat :=
  Nat.mul (Nat.pow 2 (Nat.mul d 2))
    (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul d (Nat.sub (Nat.div 8162 d) 1))) 1) (Nat.sub (Nat.pow 2 d) 1))

theorem multMask_eq {d : Nat} (hd : 0 < d) : multMask d = multMaskF d := by
  rw [multMask, List.range_eq_range']
  show _ = 2 ^ (d * 2) * ((2 ^ (d * (8162 / d - 1)) - 1) / (2 ^ d - 1))
  rw [← powSum_eq hd]
  rcases Nat.eq_zero_or_pos (8162 / d) with h | h
  · rw [h]
    rfl
  · obtain ⟨K, hK⟩ : ∃ K, 8162 / d = K + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    rw [hK, List.range'_succ, List.range'_succ, List.foldl_cons, List.foldl_cons]
    show (List.range' 2 K).foldl _ 0 = _
    rw [foldl_range'_eq hd K 2 0 (Nat.le_refl 2) (Nat.two_pow_pos _), Nat.zero_add, Nat.add_sub_cancel]

/-- `compMask`, its masks by `multMaskF`. -/
def compMaskF : Nat := (List.range 91).foldl (fun m d => if 2 ≤ d then m ||| multMaskF d else m) 0

theorem compMask_eq : compMask = compMaskF := by
  refine congrArg (fun f => (List.range 91).foldl f 0) (funext fun m => funext fun d => ?_)
  by_cases h : 2 ≤ d
  · rw [ite_eq_left h, ite_eq_left h, multMask_eq (Nat.lt_of_lt_of_le (by decide) h)]
  · rw [ite_eq_right h, ite_eq_right h]

materialize_value compMaskF

noncomputable abbrev compMask.lit : Nat := compMaskF.lit

theorem compMask.lit_eq : compMask = compMask.lit := compMask_eq.trans compMaskF.lit_eq

materialize_value primes

end VG.Impl.RsaKeyGen

namespace VG.Proof.RsaKeyGen

open VG.Spec.RsaKeyGen VG.Impl.RsaKeyGen

theorem primes_length : primes.length = 1024 := by rw [primes.lit_eq]; decide +kernel

theorem three_mem : 3 ∈ (primes.take 512).drop 1 := by rw [primes.lit_eq]; decide +kernel

/-! The facts about the table's layout are proven for any list of 1024
entries: about `primes` itself, the kernel would evaluate it (and the sieve)
to check the rewrites. -/

theorem slots_length_of {P : List Nat} (hlen : P.length = 1024) :
    ((P.take 512).drop 1 ++ [3] ++ P.drop 512).length = 1024 := by
  simp only [List.length_append, List.length_drop, List.length_take, hlen, List.length_singleton]
  omega_using []

theorem slots_length : slots.length = 1024 := slots_length_of primes_length

theorem mem_slots_of {P : List Nat} (hlen : P.length = 1024) (h3 : 3 ∈ (P.take 512).drop 1) (x : Nat) :
    x ∈ (P.take 512).drop 1 ++ [3] ++ P.drop 512 ↔ x ∈ (P.take 1024).drop 1 := by
  have hsplit : (P.take 1024).drop 1 = (P.take 512).drop 1 ++ P.drop 512 := by
    rw [List.take_of_length_le (Nat.le_of_eq hlen), ← List.drop_append_of_le_length (by
      simp [hlen]), List.take_append_drop]
  rw [hsplit]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ((h | rfl) | h)
    · exact .inl h
    · exact .inl h3
    · exact .inr h
  · rintro (h | h)
    · exact .inl (.inl h)
    · exact .inr h

theorem mem_slots_take_of {P : List Nat} (hlen : P.length = 1024) (h3 : 3 ∈ (P.take 512).drop 1)
    (x : Nat) : x ∈ ((P.take 512).drop 1 ++ [3] ++ P.drop 512).take 512 ↔ x ∈ (P.take 512).drop 1 := by
  have hl : ((P.take 512).drop 1 ++ [3]).length = 512 := by
    simp only [List.length_append, List.length_drop, List.length_take, hlen, List.length_singleton]
    omega_using []
  simp only [List.take_append_of_le_length (Nat.le_of_eq hl.symm), List.take_of_length_le (Nat.le_of_eq hl),
    List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | rfl)
    · exact h
    · exact h3
  · exact .inl

theorem getD_of_lt {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem slots_all : slots.all (fun s => s % 2 == 1 && decide (3 ≤ s) && decide (s < 8162)) = true := by
  unfold slots; rw [primes.lit_eq]; decide +kernel

/-- The table's entries are odd, from 3 to 8161. -/
theorem tabEntry_facts {i : Nat} (hi : i < 1024) : tabEntry i % 2 = 1 ∧ 3 ≤ tabEntry i ∧ tabEntry i < 8162 := by
  have h := List.all_eq_true.mp slots_all (slots[i]'(by rw [slots_length]; exact hi)) (List.getElem_mem _)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have : tabEntry i = slots[i]'(by rw [slots_length]; exact hi) := by
    unfold tabEntry; exact getD_of_lt _
  rw [this]; exact ⟨h.1.1, h.1.2, h.2⟩

/-- Trial division by the first `4 n` entries of the table. -/
def trialAny (n c : Nat) : Bool := (List.range (4 * n)).any fun i => c % tabEntry i == 0

theorem range_map_tabEntry (n : Nat) (hn : n ≤ 1024) : (List.range n).map tabEntry = slots.take n := by
  apply List.ext_getElem (by simp [slots_length]; omega_using [hn])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take, tabEntry]
  exact getD_of_lt _

theorem any_mem_congr {l₁ l₂ : List Nat} (p : Nat → Bool) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.any p = l₂.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨x, hx, hp⟩ => ⟨x, (h x).mp hx, hp⟩, fun ⟨x, hx, hp⟩ => ⟨x, (h x).mpr hx, hp⟩⟩

theorem smallPrimes_lt {s : Nat} (h : s ∈ smallPrimes) : s < 8162 := by
  unfold smallPrimes at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

/-- The table's trial division is `obviouslyComposite`, for a prime of
`64 w` bits. -/
theorem trialAny_eq {w c : Nat} (hc : 8161 < c) :
    trialAny (if 17 ≤ w then 256 else 128) c = obviouslyComposite (64 * w) c := by
  unfold trialAny obviouslyComposite
  have hne : ∀ l : List Nat, (∀ s ∈ l, s ∈ smallPrimes) →
      l.any (fun s => c % s == 0 && c != s) = l.any (fun s => c % s == 0) := by
    intro l hl
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨fun ⟨x, hx, h1, _⟩ => ⟨x, hx, h1⟩, fun ⟨x, hx, h1⟩ => ⟨x, hx, h1, by
      have := smallPrimes_lt (hl x hx); omega_using [hc, this]⟩⟩
  rw [hne _ fun s hs => List.mem_of_mem_take (List.mem_of_mem_drop hs), ← primes_eq]
  rw [show (fun i => c % tabEntry i == 0) = (fun s => c % s == 0) ∘ tabEntry from rfl, ← List.any_map]
  unfold trialPrimes
  by_cases hw : 17 ≤ w
  · simp only [hw, ↓reduceIte, show 1024 < 64 * w by omega_using [hw]]
    rw [range_map_tabEntry _ (by decide), show 4 * 256 = 1024 from rfl,
      List.take_of_length_le (Nat.le_of_eq slots_length)]
    exact any_mem_congr _ (mem_slots_of primes_length three_mem)
  · simp only [hw, ↓reduceIte, show ¬ 1024 < 64 * w by omega_using [hw]]
    rw [range_map_tabEntry _ (by decide), show 4 * 128 = 512 from rfl]
    exact any_mem_congr _ (mem_slots_take_of primes_length three_mem)

end VG.Proof.RsaKeyGen
