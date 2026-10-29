module

import VerifiedGarbage.Proof.Aes.Blocks
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# GCM: what one pass over a buffer of eight blocks needs

Untrusted: everything here is checked by Lean. Facts the paths for short
records use, which hash a few blocks after zero ones and count from below the
first counter block:

* `ghashFrom_zeros`: blocks of zeros before the others leave GHASH from zero
  as it is, since `0 • H = 0` (`mul_zero_left`);
* `repeat_inc32_add`, `repeat_inc32_pred`: `inc₃₂` repeats every `2³²`
  steps, so `2³² − 1` steps after `inc₃₂(J₀)` give `J₀` back: the keystream
  from byte `16 · 2³²` on is the keystream (`ksByte_wrap`), and its block
  `2³² − 1` from `inc₃₂(J₀)` is `CIPH_K(J₀)` (`ksByte_pred`);
* `ghash_lead`: GHASH over zero blocks, the additional data (at most a block)
  and the text each padded, and the lengths block is the tag's.
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.Spec.Gcm (Block mul ghashFrom ghash inc32 toBytes ofBytes blocks zeros padLen)

/-- `0 • y = 0`. -/
theorem mul_zero_left (y : Block) : mul 0 y = 0 := by
  have inv : ∀ (l : List Nat) (zv : Block × Block), zv.1 = 0 →
      (l.foldl (fun (zv : Block × Block) i =>
        let (z, v) := zv
        let z := if (0 : Block).getMsbD i then z ^^^ v else z
        let v := if v.getLsbD 0 then (v >>> 1) ^^^ Spec.Gcm.R else v >>> 1
        (z, v)) zv).1 = 0 := by
    intro l
    induction l with
    | nil => intro zv h; exact h
    | cons i l ih =>
      intro zv h
      rw [List.foldl_cons]
      exact ih _ (by simp [BitVec.getMsbD_zero, h])
  exact inv _ _ rfl

/-- Blocks of zeros, then `xs`, hashed from zero: `xs` hashed from zero. -/
theorem ghashFrom_zeros (h : Block) (k : Nat) (xs : List Block) :
    ghashFrom h 0 (List.replicate k 0 ++ xs) = ghashFrom h 0 xs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, ghashFrom, List.foldl_cons, BitVec.xor_self,
      show (0#128 : Block) = 0 from rfl, mul_zero_left]
    exact ih

/-- Two blocks with the same high 96 and low 32 bits are equal. -/
theorem block_ext {x y : Block} (h₁ : x.extractLsb' 32 96 = y.extractLsb' 32 96)
    (h₂ : x.extractLsb' 0 32 = y.extractLsb' 0 32) : x = y := by
  ext i hi
  by_cases hl : i < 32
  · have := congrArg (·.getLsbD i) h₂
    simpa [BitVec.getLsbD_extractLsb', hl, ← BitVec.getLsbD_eq_getElem] using this
  · have := congrArg (·.getLsbD (i - 32)) h₁
    simp only [BitVec.getLsbD_extractLsb', show i - 32 < 96 by omega, decide_true, Bool.true_and,
      show 32 + (i - 32) = i by omega] at this
    simpa [← BitVec.getLsbD_eq_getElem] using this

/-- `inc₃₂` repeated `2³² + i` times is `inc₃₂` repeated `i` times. -/
theorem repeat_inc32_add (x : Block) (i : Nat) : Nat.repeat inc32 (2 ^ 32 + i) x = Nat.repeat inc32 i x := by
  refine block_ext (by rw [Proof.Aes.repeat_inc32_hi, Proof.Aes.repeat_inc32_hi]) ?_
  rw [Proof.Aes.repeat_inc32_lo, Proof.Aes.repeat_inc32_lo]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp

/-- `2³² − 1` steps of `inc₃₂` after `inc₃₂(J)` give `J`. -/
theorem repeat_inc32_pred (J : Block) : Nat.repeat inc32 (2 ^ 32 - 1) (inc32 J) = J := by
  refine block_ext (by rw [Proof.Aes.repeat_inc32_hi, Proof.Aes.inc32_hi]) ?_
  rw [Proof.Aes.repeat_inc32_lo, Proof.Aes.inc32_lo, BitVec.add_assoc,
    show (1 : BitVec 32) + BitVec.ofNat 32 (2 ^ 32 - 1) = 0 from rfl]
  exact BitVec.add_zero _

/-- The keystream from byte `16 · 2³²` on is the keystream. -/
theorem ksByte_wrap (ciph : Block → Block) (icb : Block) (i : Nat) :
    ksByte ciph icb (16 * 2 ^ 32 + i) = ksByte ciph icb i := by
  unfold ksByte
  rw [show (16 * 2 ^ 32 + i) / 16 = 2 ^ 32 + i / 16 by omega, show (16 * 2 ^ 32 + i) % 16 = i % 16 by omega,
    repeat_inc32_add]

/-- Block `2³² − 1` of the keystream from `inc₃₂(J)` is `CIPH(J)`. -/
theorem ksByte_pred (ciph : Block → Block) (J : Block) {t : Nat} (ht : t < 16) :
    ksByte ciph (inc32 J) (16 * (2 ^ 32 - 1) + t) = (toBytes (ciph J)).getD t 0 := by
  unfold ksByte
  rw [show (16 * (2 ^ 32 - 1) + t) / 16 = 2 ^ 32 - 1 by omega, show (16 * (2 ^ 32 - 1) + t) % 16 = t by omega,
    repeat_inc32_pred]

theorem ofBytes_zeros16 : ofBytes (zeros 16) = 0 := by decide

theorem blocks_zeros (k : Nat) : blocks (zeros (16 * k)) = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show zeros (16 * (k + 1)) = zeros (16 * k) ++ zeros 16 by
        rw [zeros, zeros, zeros, List.replicate_append_replicate, Nat.mul_succ],
      blocks_append (by simp [length_zeros]), ih, blocks_single (length_zeros 16), ofBytes_zeros16,
      List.replicate_succ']

set_option linter.unusedSimpArgs false in
/-- GHASH from zero over `lead` zero blocks, the additional data `a` (at most
a block) and the text `c` each padded to whole blocks, and the lengths block:
the tag's GHASH (`fullTag_eq`). -/
theorem ghash_lead (h : Block) (lead : Nat) {a c : List Byte} (ha : a.length ≤ 16) :
    ghashFrom h 0 (blocks (zeros (16 * lead) ++ a ++ zeros (16 - a.length) ++ c ++ zeros (padLen c.length) ++
      lensBlock a.length c.length)) =
      ghashFrom h (ghash h (blocks (padded a c))) [ofBytes (lensBlock a.length c.length)] := by
  have zz : zeros (16 * (lead + 1)) = zeros (16 * lead) ++ zeros 16 := by
    rw [zeros, zeros, zeros, List.replicate_append_replicate, Nat.mul_succ]
  have e : ∃ k, zeros (16 * lead) ++ a ++ zeros (16 - a.length) ++ c ++ zeros (padLen c.length) =
      zeros (16 * k) ++ padded a c := by
    by_cases ha0 : a = []
    · subst ha0
      refine ⟨lead + 1, ?_⟩
      by_cases hc : c = []
      · subst hc
        rw [zz]
        simp [padded, Spec.Gcm.ghashInput, padLen, zeros]
      · rw [padded, ghashInput_of_ne hc]
        simp only [List.append_nil, List.length_nil, Nat.sub_zero, List.nil_append, List.length_append,
          length_zeros, show padLen 0 = 0 from rfl, Nat.zero_add, zz, show zeros 0 = [] from rfl, List.append_assoc]
    · have hl : 0 < a.length := List.length_pos_iff.mpr ha0
      refine ⟨lead, ?_⟩
      have p₁ : padLen a.length = 16 - a.length := by simp only [padLen]; omega
      by_cases hc : c = []
      · subst hc
        simp only [padded, Spec.Gcm.ghashInput, ↓reduceIte, List.length_nil, List.append_nil, p₁,
          List.append_assoc, show padLen 0 = 0 from rfl, show zeros 0 = [] from rfl, List.length_append,
          length_zeros, show a.length + (16 - a.length) = 16 by omega, show padLen 16 = 0 from rfl]
      · rw [padded, ghashInput_of_ne hc]
        have p₂ : padLen (a.length + (16 - a.length + c.length)) = padLen c.length := by
          simp only [padLen]; omega
        simp only [List.length_append, length_zeros, p₁, List.append_assoc, p₂]
  obtain ⟨k, hk⟩ := e
  rw [hk, List.append_assoc, blocks_append (by simp [length_zeros]), blocks_zeros,
    blocks_append (length_padded a c), blocks_single (length_lensBlock _ _), ghashFrom_zeros, ghashFrom_append]
  rfl

end VG.Proof.Gcm
