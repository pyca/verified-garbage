module

import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.WordStep
meta import VerifiedGarbage.Proof.Bignum.WordStep
public import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.R2wFast
public import VerifiedGarbage.Proof.Bignum.X86_64.R2
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wFast
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2
meta import VerifiedGarbage.Impl.Bignum.X86_64.R2Adx
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Rsa.Ranges
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `Bignum.X86_64.R2aCT`, which only this module used -/

section

/-! ### `Bignum.X86_64.R2aFast`, which only this module used -/

section

/-! ### `Bignum.X86_64.R2aRecip`, which this module and modules that import it used -/

section

/-! ### `Bignum.Recip`, which this module and modules that import it used -/

section

/-!
# The reciprocal of a word, from where it stops

For a word `d ≥ 2^63`, `v = ⌊(2^128 - 1) / d⌋ - 2^64` is the largest `v`
with `(2^64 + v) d < 2^128`. Code that corrects some guess of `v` one at a
time, down while `over v d` (`(2^64 + v) d ≥ 2^128`, from the carry of
`d + ⌊v d / 2^64⌋`) and then up while `up v d`, stops at that `v`
(`recip_exact`): its correctness needs no bound on the guess.
-/

@[expose] public section

namespace VG.Proof.Bignum.Recip

/-- Whether `(2^64 + v) d ≥ 2^128`, as code can test it: the carry of
`d + ⌊v d / 2^64⌋`. -/
def over (v D : Nat) : Bool := decide (2 ^ 64 ≤ v * D / 2 ^ 64 + D)

/-- Whether to raise `v`: `v + 1` is a word and `(2^64 + v + 1) d < 2^128`. -/
def up (v D : Nat) : Bool := !decide (v + 1 = 2 ^ 64) && !over (v + 1) D

theorem over_pos {v D : Nat} (hD : D < 2 ^ 64) (h : over v D = true) : 1 ≤ v := by
  refine Nat.pos_of_ne_zero fun h0 => ?_
  unfold over at h
  rw [h0, Nat.zero_mul, Nat.zero_div, Nat.zero_add, decide_eq_true_eq] at h
  omega_using [h, hD]

/-- `over v d` is false iff `(2^64 + v) d < 2^128`. -/
theorem over_false {v D : Nat} (hD : D < 2 ^ 64) (h : over v D = false) : 2 ^ 64 * D + v * D < 2 ^ 128 := by
  unfold over at h
  rw [decide_eq_false_iff_not, Nat.not_le, ← Nat.lt_sub_iff_add_lt, Nat.div_lt_iff_lt_mul (by decide)] at h
  have : (2 ^ 64 - D) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D := by
    rw [Nat.sub_mul, Nat.mul_comm D]
  omega_using [h, this, hD]

theorem over_true {v D : Nat} (hD : D < 2 ^ 64) (h : over v D = true) : 2 ^ 128 ≤ 2 ^ 64 * D + v * D := by
  unfold over at h
  rw [decide_eq_true_eq, ← Nat.sub_le_iff_le_add, Nat.le_div_iff_mul_le (by decide)] at h
  have : (2 ^ 64 - D) * 2 ^ 64 = 2 ^ 128 - 2 ^ 64 * D := by
    rw [Nat.sub_mul, Nat.mul_comm D]
  omega_using [h, this, hD]

/-- The largest `v` with `(2^64 + v) d < 2^128` is `v = ⌊(2^128 - 1) / d⌋ - 2^64`. -/
theorem recip_exact {v D : Nat} (hd : 2 ^ 63 ≤ D) (hD : D < 2 ^ 64) (ho : over v D = false) (hu : up v D = false) : v = (2 ^ 128 - 1) / D - 2 ^ 64 := by
  have h1 := over_false hD ho
  have h2 : 2 ^ 128 ≤ 2 ^ 64 * D + (v + 1) * D := by
    unfold up at hu
    rw [Bool.and_eq_false_iff, Bool.not_eq_false', Bool.not_eq_false', decide_eq_true_eq] at hu
    rcases hu with h | h
    · rw [h]; omega_using [hd]
    · exact over_true hD h
  rw [Nat.add_mul, Nat.one_mul] at h2
  have e : (2 ^ 128 - 1) / D = 2 ^ 64 + v := by
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.add_mul]; omega_using [h1]
    · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega_using [h2]
  omega_using [e]

end VG.Proof.Bignum.Recip

end

end

/-!
# `R² mod m` by word steps with ADX: the reciprocal

`R2Adx.recipN` (`Impl/Bignum/X86_64/R2Adx.lean`): `recipGuess` leaves some
guess of `v = ⌊(2^128 - 1) / d⌋ - 2^64` in `rcx`, of which nothing is
proven but that it is a word (`recipGuess_ok`); `recipDown` then lowers it while
`(2^64 + v) d ≥ 2^128` (`down_ok`, `downLoop_ok`), and `recipUp` raises it
while `(2^64 + v + 1) d < 2^128` (`up_ok`, `upLoop_ok`), which leaves the
largest `v` with `(2^64 + v) d < 2^128`: `v` itself (`recipN_ok`, with
`R2Words.recip`'s statement, `R2w.recip_ok`), by `Recip.recip_exact`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.Recip

/-! ## The guess -/

/-- What a Newton step leaves in `rcx`, from `v` in `rcx` and `d` in `rsi`. -/
def stepV (v d : BitVec 64) : BitVec 64 :=
  let e := (BitVec.ofNat 64 (v.toNat * d.toNat / 2 ^ 64) + d) ^^^ BitVec.allOnes 64
  v + (e + BitVec.ofNat 64 (e.toNat * v.toNat / 2 ^ 64))

/-- `n` Newton steps from `v`. -/
def stepsV (d : BitVec 64) : Nat → BitVec 64 → BitVec 64
  | 0, v => v
  | n + 1, v => stepsV d n (stepV v d)

/-- What `recipGuess` leaves in `rcx`, for `d = m[w - 1]`. -/
def guessV (d : BitVec 64) : BitVec 64 := stepsV d 6 (d ^^^ BitVec.allOnes 64)

/-- A Newton step writes only `rdx`, `r14`, `rax`, `r11` and `rcx`. -/
theorem recipStep_ok (s : State) :
    WP isa (.block recipStep) s fun t => t.gpr .rcx = stepV (s.gpr .rcx) (s.gpr .rsi) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi ∧ Keep [.rdx, .r14, .rax, .r11, .rcx] s t := by
  exact WP.mono (WP.keep [.rdx, .r14, .rax, .r11, .rcx] (c := .block recipStep)
    (Q := fun t => t.gpr .rcx = stepV (s.gpr .rcx) (s.gpr .rsi) ∧ t.mem = s.mem ∧ t.gpr .rsi = s.gpr .rsi)
    (by unfold recipStep; xrun [execMulx, R2w.sxm1]; rfl) rfl)
    fun t ⟨⟨hcx, hm, hsi⟩, k⟩ => ⟨hcx, hm, hsi, k⟩

/-- `n` Newton steps. -/
theorem recipSteps_ok (n : Nat) (s : State) :
    WP isa (.block (List.replicate n recipStep).flatten) s fun t =>
      t.gpr .rcx = stepsV (s.gpr .rsi) n (s.gpr .rcx) ∧ t.mem = s.mem ∧
      t.gpr .rsi = s.gpr .rsi ∧ Keep [.rdx, .r14, .rax, .r11, .rcx] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, Keep.refl _ _⟩
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, WP.block_append_iff]
    exact WP.mono (recipStep_ok s) fun t ⟨hcx, hm, hsi, k⟩ => WP.mono (ih t) fun t' ⟨hcx', hm', hsi', k'⟩ =>
      ⟨by rw [hcx', hsi, hcx]; rfl, hm'.trans hm, hsi'.trans hsi,
        (k.trans k').mono (by decide)⟩

/-- `recipGuess`: `d = m[w - 1]` into `rsi`, for `m` at `r10` of `w` words, and
`guessV d` into `rcx`. -/
theorem recipGuess_ok {t : State} {B : Addr} {Z w em : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hM : em + 8 * w ≤ Z) :
    WP isa (.block recipGuess) t fun t' => t'.gpr .rsi = word t.mem B (em + 8 * (w - 1)) ∧
      t'.gpr .rcx = guessV (word t.mem B (em + 8 * (w - 1))) ∧ t'.mem = t.mem ∧
      Keep [.rsi, .rcx, .rdx, .r14, .rax, .r11] t t' := by
  rw [show recipGuess = ([.mov .rsi (.mem (ix .r10 .r12 (-8))), .mov .rcx (.reg .rsi), .alu .xor .rcx (.imm (-1))] :
      List Instr) ++ (List.replicate 6 recipStep).flatten from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' => t'.gpr .rsi = word t.mem B (em + 8 * (w - 1)) ∧
      t'.gpr .rcx = word t.mem B (em + 8 * (w - 1)) ^^^ BitVec.allOnes 64 ∧ t'.mem = t.mem) (by
    xrun [State.ea, ix, addrm8 h10 h12 hw, hs.ld (show em + 8 * (w - 1) + 8 ≤ Z by omega_using [hw, hM]),
      R2w.sxm1]) rfl) fun t₁ ⟨⟨hsi₁, hcx₁, hm₁⟩, k₁⟩ => ?_
  exact WP.mono (recipSteps_ok 6 t₁) fun t' ⟨hcx', hm', hsi', k'⟩ =>
    ⟨hsi'.trans hsi₁, by rw [hcx', hsi₁, hcx₁]; rfl, hm'.trans hm₁, (k₁.trans k').mono (by decide)⟩

/-! ## The corrections -/

theorem toNat_ofNat64 {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem hi_lt {v D : Nat} (hv : v < 2 ^ 64) (hD : D < 2 ^ 64) : v * D / 2 ^ 64 < 2 ^ 64 := by
  rw [Nat.div_lt_iff_lt_mul (by decide)]
  exact Nat.mul_lt_mul'' hv hD

theorem down_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.block recipDown) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v - (over v D).toNat) ∧
      t'.zf = some (!over v D) ∧ t'.mem = t.mem ∧ Keep [.rdx, .r14, .rax, .rcx] t t' := by
  refine WP.mono (WP.keep [.rdx, .r14, .rax, .rcx] (c := .block recipDown) (Q := fun t' =>
    t'.gpr .rcx = BitVec.ofNat 64 (v - (over v D).toNat) ∧ t'.zf = some (!over v D) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨h1, h2, h3⟩, k⟩ => ⟨h1, h2, h3, k⟩
  unfold recipDown
  xrun [execMulx, hcx, hsi]
  rw [toNat_ofNat64 hv, toNat_ofNat64 hD, toNat_ofNat64 (hi_lt hv hD)]
  unfold over
  by_cases hc : 2 ^ 64 ≤ v * D / 2 ^ 64 + D
  · have hv1 : 1 ≤ v := by
      refine Nat.pos_of_ne_zero fun h0 => ?_
      rw [h0, Nat.zero_mul, Nat.zero_div] at hc
      omega_using [hc, hD]
    simp only [decide_eq_true hc, Bool.toNat_true, Bool.not_true]
    rw [BitVec.and_self, show BitVec.setWidth 64 (BitVec.ofBool true) = BitVec.ofNat 64 1 from rfl,
      BitVec.zero_sub, ← BitVec.sub_eq_add_neg, R2w.ofNat_sub_ofNat64 hv1]
    exact ⟨rfl, beq_eq_false_iff_ne.mpr fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_neg, BitVec.toNat_ofNat, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega_using [this]⟩
  · simp only [decide_eq_false hc, Bool.toNat_false, Bool.not_false, Nat.sub_zero]
    rw [show BitVec.setWidth 64 (BitVec.ofBool false) = 0#64 from rfl, BitVec.sub_zero, BitVec.add_zero,
      BitVec.and_self]
    exact ⟨rfl, rfl⟩

theorem upA_ok {t : State} {v : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64) :
    WP isa (.block [.mov .rdx (.reg .rcx), .alu .add .rdx (.imm 1), .alu .sbb .r11 (.reg .r11)]) t fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (v + 1) ∧ t'.gpr .r11 = mask (decide (v + 1 = 2 ^ 64)) ∧
      t'.mem = t.mem ∧ Keep [.rdx, .r11] t t' := by
  refine WP.mono (WP.keep [.rdx, .r11] (Q := fun t' => t'.gpr .rdx = BitVec.ofNat 64 (v + 1) ∧
    t'.gpr .r11 = mask (decide (v + 1 = 2 ^ 64)) ∧ t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h1, h2, h3⟩, k⟩ => ⟨h1, h2, h3, k⟩
  xrun [hcx]
  refine ⟨by rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat], ?_⟩
  rw [toNat_ofNat64 hv, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
    decide_eq_decide.mpr (show 2 ^ 64 ≤ v + 1 ↔ v + 1 = 2 ^ 64 by omega_using [hv])]
  rfl

theorem upB_ok {t : State} {x D : Nat} (hdx : t.gpr .rdx = BitVec.ofNat 64 x)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.block [.mulx .r14 .rax (.reg .rsi), .alu .add .r14 (.reg .rsi), .alu .sbb .rax (.reg .rax)]) t
      fun t' => t'.gpr .rax = mask (over (x % 2 ^ 64) D) ∧ t'.mem = t.mem ∧ Keep [.r14, .rax] t t' := by
  refine WP.mono (WP.keep [.r14, .rax] (Q := fun t' => t'.gpr .rax = mask (over (x % 2 ^ 64) D) ∧
    t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  xrun [execMulx, hdx, hsi]
  rw [BitVec.toNat_ofNat x, toNat_ofNat64 hD, toNat_ofNat64 (hi_lt (Nat.mod_lt x (by decide)) hD)]
  rfl

theorem mask_or (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;>
    simp only [mask_true, mask_false, Bool.or_true, Bool.or_false, BitVec.allOnes_or, BitVec.or_allOnes,
      BitVec.or_self]

theorem mask_xor (c : Bool) : mask c ^^^ BitVec.allOnes 64 = mask (!c) := by
  cases c
  · rw [BitVec.xor_allOnes, mask_false, Bool.not_false, mask_true, show (0 : BitVec 64) = 0#64 from rfl,
      BitVec.not_zero]
  · rw [BitVec.xor_allOnes, mask_true, Bool.not_true, mask_false, BitVec.not_allOnes]; rfl

theorem upC_ok {t : State} {v : Nat} {a b : Bool} (hax : t.gpr .rax = mask a) (h11 : t.gpr .r11 = mask b)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 v) :
    WP isa (.block [.alu .or .rax (.reg .r11), .alu .xor .rax (.imm (-1)), .alu .sub .rcx (.reg .rax),
      .alu .test .rax (.reg .rax)]) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v + (!a && !b).toNat) ∧
      t'.zf = some (a || b) ∧ t'.mem = t.mem ∧ Keep [.rax, .rcx] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v + (!a && !b).toNat) ∧
    t'.zf = some (a || b) ∧ t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h1, h2, h3⟩, k⟩ => ⟨h1, h2, h3, k⟩
  xrun [hax, h11, hcx, R2w.sxm1]
  rw [mask_or, mask_xor, BitVec.and_self]
  cases a <;> cases b
  · rw [show (!(false || false)) = true from rfl, mask_true]
    refine ⟨BitVec.eq_of_toNat_eq ?_, beq_eq_false_iff_ne.mpr fun h => ?_⟩
    · rw [BitVec.toNat_sub, BitVec.toNat_allOnes, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        show (!false && !false).toNat = 1 from rfl]
      omega_using []
    · have := congrArg BitVec.toNat h
      rw [BitVec.toNat_allOnes, show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at this
      omega_using [this]
  all_goals
    rw [show ∀ x y : Bool, (!(x || y)) = false → mask (!(x || y)) = 0#64 from fun x y h => by rw [h]; rfl]
    · exact ⟨by rw [BitVec.sub_zero]; rfl, rfl⟩
    · rfl

theorem up_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.block recipUp) t fun t' => t'.gpr .rcx = BitVec.ofNat 64 (v + (up v D).toNat) ∧
      t'.zf = some (!up v D) ∧ t'.mem = t.mem ∧ Keep [.rdx, .r11, .r14, .rax, .rcx] t t' := by
  rw [show recipUp = ([.mov .rdx (.reg .rcx), .alu .add .rdx (.imm 1), .alu .sbb .r11 (.reg .r11)] : List Instr) ++
      (([.mulx .r14 .rax (.reg .rsi), .alu .add .r14 (.reg .rsi), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      ([.alu .or .rax (.reg .r11), .alu .xor .rax (.imm (-1)), .alu .sub .rcx (.reg .rax),
        .alu .test .rax (.reg .rax)] : List Instr)) from rfl, WP.block_append_iff]
  refine WP.mono (upA_ok hcx hv) fun t₁ ⟨h1dx, h111, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (upB_ok h1dx ((k₁.gpr (by decide)).trans hsi) hD) fun t₂ ⟨h2ax, hm₂, k₂⟩ => ?_
  refine WP.mono (upC_ok h2ax ((k₂.gpr (by decide)).trans h111)
    ((k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hcx))) fun t' ⟨h3cx, h3z, hm₃, k₃⟩ => ?_
  have hu : (!over ((v + 1) % 2 ^ 64) D && !decide (v + 1 = 2 ^ 64)) = up v D := by
    unfold up
    by_cases h : v + 1 = 2 ^ 64
    · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and]
    · rw [Nat.mod_eq_of_lt (by omega_using [hv, h]), Bool.and_comm]
  refine ⟨by rw [h3cx, hu], by rw [h3z, ← hu, Bool.not_and, Bool.not_not, Bool.not_not], by rw [hm₃, hm₂, hm₁],
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-! ## The loops -/

/-- `recipDown` while it lowers `v`: then `(2^64 + v) d < 2^128`. -/
theorem downLoop_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.loop (.block recipDown) .ne) t fun t' => ∃ v', t'.gpr .rcx = BitVec.ofNat 64 v' ∧ v' < 2 ^ 64 ∧
      over v' D = false ∧ t'.mem = t.mem ∧ Keep [.rdx, .r14, .rax, .rcx] t t' := by
  refine WP.loop (M := isa) (fun n (s : State) => s.gpr .rcx = BitVec.ofNat 64 n ∧ n < 2 ^ 64 ∧ s.mem = t.mem ∧
    Keep [.rdx, .r14, .rax, .rcx] t s) (fun n s ⟨h1, h2, h3, k⟩ => ?_) v t ⟨hcx, hv, rfl, Keep.refl _ _⟩
  refine WP.mono (down_ok h1 h2 ((k.gpr (by decide)).trans hsi) hD) fun s' ⟨h1', hz, hm', k'⟩ => ?_
  cases ho : over n D
  · rw [ho, Bool.toNat_false, Nat.sub_zero] at h1'
    exact .inl ⟨by simp only [eval, hz, ho, Option.map_some, Bool.not_false, Bool.not_true],
      n, h1', h2, ho, hm'.trans h3, (k.trans k').mono (by decide)⟩
  · have hn := over_pos hD ho
    rw [ho, Bool.toNat_true] at h1'
    exact .inr ⟨by simp only [eval, hz, ho, Option.map_some, Bool.not_true, Bool.not_false],
      n - 1, by omega_using [hn], h1', by omega_using [h2], hm'.trans h3, (k.trans k').mono (by decide)⟩

/-- `recipUp` while it raises `v`, from `v` with `(2^64 + v) d < 2^128`: then
also `up v d` is false. -/
theorem upLoop_ok {t : State} {v D : Nat} (hcx : t.gpr .rcx = BitVec.ofNat 64 v) (hv : v < 2 ^ 64)
    (ho : over v D = false) (hsi : t.gpr .rsi = BitVec.ofNat 64 D) (hD : D < 2 ^ 64) :
    WP isa (.loop (.block recipUp) .ne) t fun t' => ∃ v', t'.gpr .rcx = BitVec.ofNat 64 v' ∧ v' < 2 ^ 64 ∧
      over v' D = false ∧ up v' D = false ∧ t'.mem = t.mem ∧ Keep [.rdx, .r11, .r14, .rax, .rcx] t t' := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ u, n = 2 ^ 64 - u ∧ s.gpr .rcx = BitVec.ofNat 64 u ∧ u < 2 ^ 64 ∧
    over u D = false ∧ s.mem = t.mem ∧ Keep [.rdx, .r11, .r14, .rax, .rcx] t s)
    (fun n s ⟨u, hn, h1, h2, ho', h3, k⟩ => ?_) (2 ^ 64 - v) t ⟨v, rfl, hcx, hv, ho, rfl, Keep.refl _ _⟩
  refine WP.mono (up_ok h1 h2 ((k.gpr (by decide)).trans hsi) hD) fun s' ⟨h1', hz, hm', k'⟩ => ?_
  cases hu : up u D
  · rw [hu, Bool.toNat_false, Nat.add_zero] at h1'
    exact .inl ⟨by simp only [eval, hz, hu, Option.map_some, Bool.not_false, Bool.not_true],
      u, h1', h2, ho', hu, hm'.trans h3, (k.trans k').mono (by decide)⟩
  · rw [hu, Bool.toNat_true] at h1'
    unfold up at hu
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not] at hu
    exact .inr ⟨by simp only [eval, hz, up, hu, Option.map_some, decide_false, Bool.not_false, Bool.and_self,
        Bool.not_not],
      2 ^ 64 - (u + 1), by omega_using [hn, h2, hu.1], u + 1, rfl, h1', by omega_using [h2, hu.1], hu.2,
      hm'.trans h3, (k.trans k').mono (by decide)⟩

/-! ## The reciprocal -/

/-- `recipN`: `v` for `d = m[w - 1] ≥ 2^63` into the word at `r8`, for `m` at
`r10` of `w` words, as `R2Words.recip` (`R2w.recip_ok`). -/
theorem recipN_ok {t : State} {B : Addr} {Z w em ev : Nat} (hs : Scr t B Z)
    (h10 : t.gpr .r10 = off B em) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (h8 : t.gpr .r8 = off B ev)
    (hw : 1 ≤ w) (hM : em + 8 * w ≤ Z) (hE : ev + 8 ≤ Z)
    (hd : 2 ^ 63 ≤ (word t.mem B (em + 8 * (w - 1))).toNat) :
    WP isa recipN t fun t' => t'.mem = t.mem.writeW (off B ev)
        (BitVec.ofNat 64 ((2 ^ 128 - 1) / (word t.mem B (em + 8 * (w - 1))).toNat - 2 ^ 64)) ∧
      Keep [.rsi, .rdx, .rax, .rcx, .r13, .r11, .r14, .r15] t t' := by
  generalize hD : word t.mem B (em + 8 * (w - 1)) = Dw at hd
  have hD' := Dw.isLt
  have eD : Dw = BitVec.ofNat 64 Dw.toNat := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold recipN
  refine WP.seq (WP.mono (recipGuess_ok hs h10 h12 hw hM) fun t₁ ⟨h1si, _, hm₁, k₁⟩ => ?_)
  rw [hD, eD] at h1si
  have hv₁ := (t₁.gpr .rcx).isLt
  refine WP.seq (WP.mono (downLoop_ok (v := (t₁.gpr .rcx).toNat) (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    hv₁ h1si hD') fun t₂ ⟨v₂, h2cx, hv₂, ho₂, hm₂, k₂⟩ => ?_)
  have h2si : t₂.gpr .rsi = BitVec.ofNat 64 Dw.toNat := (k₂.gpr (by decide)).trans h1si
  refine WP.seq (WP.mono (upLoop_ok h2cx hv₂ ho₂ h2si hD') fun t₃ ⟨v₃, h3cx, hv₃, ho₃, hu₃, hm₃, k₃⟩ => ?_)
  have hs₃ := ((hs.congr k₁.2.2).congr k₂.2.2).congr k₃.2.2
  have h38 : t₃.gpr .r8 = off B ev := by
    rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), h8]
  refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t₃.mem.writeW (off B ev) (t₃.gpr .rcx)) (by
    xrun [State.ea, at0, h38, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs₃.st hE]) rfl)
    fun t' ⟨hm', k'⟩ => ⟨?_, ((k₁.trans k₂).trans (k₃.trans k')).mono (by decide)⟩
  rw [hm', hm₃, hm₂, hm₁, h3cx, recip_exact hd hD' ho₃ hu₃]

end VG.Proof.Bignum.X86_64.R2ax

end

end

/-!
# `R² mod m` by word steps with ADX on x86-64

`R2Adx.steps`: `c` word steps, `x := x 2^(64 c) mod m` (`steps_ok`), with
`R - m` kept in the accumulator; `R2Adx.fast`: `R - m` into `x` and the
accumulator, the reciprocal `v` of `m`'s top word and `w` steps, `R² mod m`
(`fast_ok`); and `R2Adx.choice`, which takes `fast` for `m`'s top bit set and
`w` a multiple of 4, `vg_rsa_public`'s computation otherwise (`choice_ok`,
`R2w.choice_ok`'s statement).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep
open VG.Proof.Bignum.X86_64.R2w (sub_mul_mod neg_ok fastFlag old_eq)

/-! ## The steps -/

/-- After `j` of `c` steps from `s`, from `x = X`, modulo `m = M` whose top
word is `T`, with `v = ⌊(2^128 - 1) / T⌋ - 2^64` the temporary's first word. -/
structure StepsInv (s : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (c X M T j : Nat) (t : State) :
    Prop where
  scr : Scr t B Z
  rdi : t.gpr .rdi = B
  hdr : Hdr t.mem B w minv
  cnt : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j)
  xv : wv t.mem B (slot w aR2) w = X * 2 ^ (64 * j) % M
  nv : wv t.mem B (slot w aN) w = M
  top : (word t.mem B (slot w aN + 8 * (w - 1))).toNat = T
  rcp : (word t.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / T - 2 ^ 64
  acc : wv t.mem B (slot w aAcc) w + M = 2 ^ (64 * w)
  frm : Frm B (r2Ranges w) s.mem t.mem
  keep : Keep mmRegs s t

theorem stepIter_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {c X M T j : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 4 ≤ w) (hw4 : w % 4 = 0) (hw' : w < 2 ^ 30) (hc : c < 2 ^ 31) (hM : 0 < M)
    (hT : 2 ^ 63 ≤ T) (hj : j < c) {t : State} (hI : StepsInv s B Z w minv c X M T j t) :
    WP isa (.seq step (.block (dblCount sCnt))) t fun t' =>
      t'.zf = some (decide (j + 1 = c)) ∧ StepsInv s B Z w minv c X M T (j + 1) t' := by
  have hn := hI.scr.nowrap
  obtain hsl8 := slot_le (w := w) (show aN < 8 by decide)
  obtain hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (show sCnt < 32 by decide)
  obtain hZ0 := slot_le (w := w) (show 0 < 8 by decide)
  obtain hc0 : 8 * sCnt + 8 ≤ Z := by have := hhs 0; omega_using [hZ, hZ0, this]
  obtain hlt : wv t.mem B (slot w aR2) w < wv t.mem B (slot w aN) w := by rw [hI.xv, hI.nv]; exact Nat.mod_lt _ hM
  obtain hst := step_ok (L := ⟨B, Z, w, minv⟩) ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩ hw hw4 hw' (by rw [hI.top]; exact hT)
    (by rw [hI.rcp, hI.top]) hlt (by rw [hI.nv]; exact hI.acc)
  refine WP.seq (WP.mono hst fun t₁ ⟨hg₁, hv₁, ha₁, k₁⟩ => ?_)
  dsimp only at hg₁ hv₁ ha₁
  have hst₁ : Scr t₁ B Z := hg₁.1.scr
  have hdi₁ : t₁.gpr .rdi = B := hg₁.1.rdi
  have hH₁ : Hdr t₁.mem B w minv := hg₁.1.hdr
  obtain hcnt₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (c - j) := by
    rw [ha₁.word_eq (fun j' hj' => Or.inl (by simp at hj'; rcases hj' with rfl; exact hhs _))
      (by omega_using [hn, hc0]), hI.cnt]
  obtain hld : InRegions (t₁.rd ++ t₁.wr) (off B (8 * sCnt)) 8 := hst₁.ld hc0
  obtain hsto : InRegions t₁.wr (off B (8 * sCnt)) 8 := hst₁.st hc0
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.mem = t₁.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (c - (j + 1))) ∧ t'.zf = some (decide (c - (j + 1) = 0))) (by
    xrun [State.ea, hdr, hdi₁, hdrOff, hld, hsto, hcnt₁,
      ofNat64_pred (show 1 ≤ c - j by omega_using [hj]) (by omega_using [hc]), ofNat64_beq_zero (show c - j - 1 < 2 ^ 64 by omega_using [hc])]
    exact ⟨by congr 2, by congr 1⟩) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨?_, ?_⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega_using [hj])
  obtain o' : Outside B (8 * sCnt) 8 t₁.mem t'.mem := by rw [hm']; exact writeW_outside _ _ _ (by omega_using [hn, hc0])
  obtain hN₁ : wv t₁.mem B (slot w aN) w = M := by
    rw [ha₁.wv_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aN < aR2 by decide); omega_using [this]) (by omega_using [hZ, hn, hsl8]), hI.nv]
  obtain hT₁ : (word t₁.mem B (slot w aN + 8 * (w - 1))).toNat = T := by
    rw [ha₁.word_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aN < aR2 by decide); omega_using [this]) (by omega_using [hZ, hn, hsl8]), hI.top]
  obtain hsv := slot_le (w := w) (show aTmp < 8 by decide)
  obtain hV₁ : (word t₁.mem B (slot w aTmp)).toNat = (2 ^ 128 - 1) / T - 2 ^ 64 := by
    rw [ha₁.word_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aTmp < aR2 by decide); omega_using [this]) (by omega_using [hZ, hn, hsv]), hI.rcp]
  obtain hst8 := slot_le (w := w) (show aAcc < 8 by decide)
  obtain hC₁ : wv t₁.mem B (slot w aAcc) w = wv t.mem B (slot w aAcc) w := by
    rw [ha₁.wv_eq (fun j' hj' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl
      have := Rsa.slot_lt (w := w) (show aAcc < aR2 by decide); omega_using [this]) (by omega_using [hZ, hn, hst8])]
  obtain hH' : Hdr t'.mem B w minv := by rw [hm']; exact Hdr.store hH₁ (by decide) (by decide) _
  refine ⟨hst₁.congr k'.2.2, (k'.gpr (by decide)).trans hdi₁, hH', by rw [hm', word_writeW_self], ?_, ?_, ?_, ?_,
    ?_, ?_, ((hI.keep.trans k₁).trans k').mono (by decide)⟩
  · rw [o'.wv (by have := hhs aR2; omega_using [this]) (by have := slot_le (w := w) (show aR2 < 8 by decide); omega_using [hZ, hn, this]), hv₁,
      hI.xv, hI.nv, Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, show 64 * j + 64 = 64 * (j + 1) by omega_using []]
  · rw [o'.wv (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8]), hN₁]
  · rw [o'.word (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8]), hT₁]
  · rw [o'.word (by have := hhs aTmp; omega_using [this]) (by omega_using [hZ, hn, hsv]), hV₁]
  · rw [o'.wv (by have := hhs aAcc; omega_using [this]) (by omega_using [hZ, hn, hst8]), hC₁]; exact hI.acc
  · exact (hI.frm.trans (Frm.of_arrays ha₁ (by simp [r2Ranges]))).trans (Frm.of_outside o' (by simp [r2Ranges]))

theorem steps_eq : steps =
    .seq (.block [.store (hdr sCnt) .rcx]) (.loop (.seq step (.block (dblCount sCnt))) .ne) := rfl

/-- `steps`' start: the count `c` into `sCnt`. -/
theorem stepsStart_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {c : Nat}
    (hcx : s.gpr .rcx = BitVec.ofNat 64 c) (hO : wv s.mem B (slot w aR2) w < wv s.mem B (slot w aN) w)
    (hv : (word s.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64)
    (hc : wv s.mem B (slot w aAcc) w + wv s.mem B (slot w aN) w = 2 ^ (64 * w)) :
    WP isa (.block [.store (hdr sCnt) .rcx]) s (StepsInv s B Z w minv c (wv s.mem B (slot w aR2) w)
      (wv s.mem B (slot w aN) w) (word s.mem B (slot w aN + 8 * (w - 1))).toNat 0) := by
  have hn := hs.nowrap
  obtain hsl8 := slot_le (w := w) (show aN < 8 by decide)
  obtain hsr8 := slot_le (w := w) (show aR2 < 8 by decide)
  obtain hsv := slot_le (w := w) (show aTmp < 8 by decide)
  obtain hhs : ∀ j, 8 * sCnt + 8 ≤ slot w j := fun j => hdr_lt_slot w j (show sCnt < 32 by decide)
  obtain hZ0 := slot_le (w := w) (show 0 < 8 by decide)
  obtain hc0 : 8 * sCnt + 8 ≤ Z := by have := hhs 0; omega_using [hZ, hZ0, this]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off B (8 * sCnt)) (s.gpr .rcx))
    (by xrun [State.ea, hdr, hdi, hdrOff, hs.st hc0]) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_
  obtain o₁ : Outside B (8 * sCnt) 8 s.mem s₁.mem := by rw [hm₁]; exact writeW_outside _ _ _ (by omega_using [hn, hc0])
  exact ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hdi, by rw [hm₁]; exact Hdr.store hH (by decide) (by decide) _,
      by rw [hm₁, word_writeW_self, hcx, Nat.sub_zero],
      by rw [o₁.wv (by have := hhs aR2; omega_using [this]) (by omega_using [hZ, hn, hsr8]), Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
        Nat.mod_eq_of_lt hO],
      o₁.wv (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8]),
      by rw [o₁.word (by have := hhs aN; omega_using [this]) (by omega_using [hZ, hn, hsl8])],
      by rw [o₁.word (by have := hhs aTmp; omega_using [this]) (by omega_using [hZ, hn, hsv])]; exact hv,
      by rw [o₁.wv (d := slot w aAcc) (k := w) (by have := hhs aAcc; omega_using [this])
          (by have := slot_le (w := w) (show aAcc < 8 by decide); omega_using [hZ, hn, this])]; exact hc,
      Frm.of_outside o₁ (by simp [r2Ranges]), k₁.mono (by decide)⟩

/-- What `steps` leaves, from `StepsInv`. -/
theorem StepsInv.post {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {c X M T : Nat} {t : State}
    (hZ : slot w 8 ≤ Z) (hI : StepsInv s B Z w minv c X M T c t) :
    wv t.mem B (slot w aR2) w = X * 2 ^ (64 * c) % M ∧ wv t.mem B (slot w aN) w = M ∧
      (word t.mem B (slot w aN) = word s.mem B (slot w aN)) ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Good t B Z w minv ∧ Keep mmRegs s t := by
  have hn := hI.scr.nowrap
  obtain hsl8 := slot_le (w := w) (show aN < 8 by decide)
  exact ⟨hI.xv, hI.nv, by
      rw [hI.frm.word_eq (fun r hr => by
        have := r2Ranges_arr w (j := aN) (by decide) (by decide) (by decide) r hr; omega_using [this]) (by omega_using [hZ, hn, hsl8])],
    hI.frm, ⟨hI.scr, hI.rdi, hI.hdr⟩, hI.keep⟩

/-- `steps`: `c ≥ 1` word steps (the count in `rcx`), `x := x 2^(64 c) mod m`. -/
theorem steps_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 4 ≤ w) (hw4 : w % 4 = 0)
    (hw' : w < 2 ^ 30) {c : Nat} (hc : 1 ≤ c) (hc' : c < 2 ^ 31) (hcx : s.gpr .rcx = BitVec.ofNat 64 c)
    (hT : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat)
    (hv : (word s.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64)
    (hO : wv s.mem B (slot w aR2) w < wv s.mem B (slot w aN) w)
    (hcc : wv s.mem B (slot w aAcc) w + wv s.mem B (slot w aN) w = 2 ^ (64 * w)) :
    WP isa steps s fun t =>
      wv t.mem B (slot w aR2) w = wv s.mem B (slot w aR2) w * 2 ^ (64 * c) % wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w aN) w = wv s.mem B (slot w aN) w ∧
      (word t.mem B (slot w aN) = word s.mem B (slot w aN)) ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Good t B Z w minv ∧ Keep mmRegs s t := by
  obtain hM : 0 < wv s.mem B (slot w aN) w := Nat.lt_of_le_of_lt (Nat.zero_le _) hO
  rw [steps_eq]
  refine WP.seq (WP.mono (stepsStart_ok hs hdi hH hZ hcx hO hv hcc) fun s₁ h0 => ?_)
  exact wp_upto (a := 0) (N := c) (by omega_using [hc]) _ (fun j _ hj t hI => stepIter_ok hZ hw hw4 hw' hc' hM hT hj hI)
    (fun t hI => hI.post hZ) h0

/-! ## `R² mod m` by word steps -/

theorem fast_eq : fast = .seq (.block [.mov .rbx (.mem (hdr (sArr aR2))),
      .mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aTmp))),
      .mov32 .rbp (.imm 0)])
    (.seq (wordLoop 0 R2Words.negBody) (.seq (.block [.mov .r8 (.reg .rbx), .mov .rbx (.mem (hdr (sArr aAcc)))])
      (.seq R2Words.copyBack
        (.seq (.block [.mov .rbx (.mem (hdr (sArr aR2))), .mov .r8 (.mem (hdr (sArr aTmp)))])
          (.seq recipN (.seq (.block [.mov .rcx (.mem (hdr sW))]) steps)))))) := rfl

/-- `fast`: `R² mod m`, for the odd `m` of `w` words (a multiple of 4), its
top word at least `2^63`. -/
theorem fast_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 4 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1)
    (hT : 2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat) (h4 : w % 4 = 0) :
    WP isa fast s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  obtain hw' : w < 2 ^ 31 := by omega_using [hw30]
  have hs := hg.scr
  have hnw := hs.nowrap
  obtain hN0 : 0 < N := by omega_using [hodd]
  obtain hNR : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  -- `m > R / 2`: its top bit is set, and it is odd.
  obtain hhalf : 2 ^ (64 * w) < 2 * N := by
    obtain e : N = wv s.mem B (slot w aN) (w - 1) +
        2 ^ (64 * (w - 1)) * (word s.mem B (slot w aN + 8 * (w - 1))).toNat := by
      rw [← hn, show w = (w - 1) + 1 by omega_using [hw], wv_succ, show w - 1 + 1 - 1 = w - 1 by omega_using []]
    obtain hp : 2 ^ (64 * w) = 2 * (2 ^ (64 * (w - 1)) * 2 ^ 63) := by
      rw [← Nat.pow_add, show 64 * w = 1 + (64 * (w - 1) + 63) by omega_using [hw], Nat.pow_add, Nat.pow_one]
    obtain hle := Nat.mul_le_mul_left (2 ^ (64 * (w - 1))) hT
    obtain hev : 2 ^ (64 * (w - 1)) * 2 ^ 63 % 2 = 0 := by
      rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
    omega_using [hodd, e, hp, hle]
  obtain hsx := slot_le (w := w) (show aR2 < 8 by decide)
  obtain hsm := slot_le (w := w) (show aN < 8 by decide)
  obtain hsv := slot_le (w := w) (show aTmp < 8 by decide)
  obtain hsa := slot_le (w := w) (show aAcc < 8 by decide)
  obtain sXM := Rsa.slot_lt (w := w) (show aN < aR2 by decide)
  obtain sXV := Rsa.slot_lt (w := w) (show aTmp < aR2 by decide)
  obtain sMV := Rsa.slot_lt (w := w) (show aN < aTmp by decide)
  obtain sXA := Rsa.slot_lt (w := w) (show aAcc < aR2 by decide)
  obtain sMA := Rsa.slot_lt (w := w) (show aN < aAcc by decide)
  obtain sAV := Rsa.slot_lt (w := w) (show aAcc < aTmp by decide)
  obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  rw [fast_eq]
  refine WP.seq (WP.mono (WP.keep [.rbx, .r10, .r12, .r8, .rbp] (Q := fun t =>
      t.gpr .rbx = off B (slot w aR2) ∧ t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
      hl (sArr aTmp) (by decide), hg.hdr.harr aR2 (by decide), hg.hdr.harr aN (by decide), hg.hdr.hw,
      hg.hdr.harr aTmp (by decide)]) rfl)
    fun t₁ ⟨⟨h1bx, h110, h112, _, h1bp, hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.2.2
  obtain hM0 : 0 < wv t₁.mem B (slot w aN) w := by rw [hm₁, hn]; exact hN0
  obtain e1 : slot w aR2 + 8 * w ≤ Z := by omega_using [hZ, hsx]
  obtain e2 : slot w aN + 8 * w ≤ Z := by omega_using [sXA, sMA, e1]
  obtain sM : slot w aR2 + 8 * w ≤ slot w aN ∨ slot w aN + 8 * w ≤ slot w aR2 := by omega_using [sXA, sMA]
  refine WP.seq (WP.mono (neg_ok hs₁ h1bx h110 h112 h1bp (by omega_using [hw]) hw' e1 e2 sM hM0)
    fun t₂ ⟨hx₂, ho₂, k₂⟩ => ?_)
  rw [hm₁, hn] at hx₂
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain k₁₂ := k₁.trans k₂
  -- `mc := x`.
  obtain hdi₂ : t₂.gpr .rdi = B := (k₁₂.gpr (by decide)).trans hg.rdi
  obtain hH₂ : Hdr t₂.mem B w minv :=
    (Arrays.of_outside (j := aR2) (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (by omega_using [])).hdr
      (hm₁ ▸ hg.hdr)
  obtain hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₂.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off B (slot w aR2) ∧
      t.gpr .rbx = off B (slot w aAcc) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ (sArr aAcc) (by decide), hH₂.harr aAcc (by decide),
      (k₂.gpr (by decide)).trans h1bx]) rfl) fun t₃ ⟨⟨h38, h3bx, hm₃⟩, k₃⟩ => ?_)
  refine WP.seq ?_
  unfold R2Words.copyBack
  refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off B (slot w aR2) ∧ t.mem = t₃.mem)
    (by xrun [h38]) rfl) fun t₄ ⟨⟨h4si, hm₄⟩, k₄⟩ => ?_)
  obtain hs₄ := hs₂.congr (k₄.2.2.trans k₃.2.2)
  obtain k₃₄ := k₃.trans k₄
  obtain h412 : t₄.gpr .r12 = BitVec.ofNat 64 w := (k₃₄.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h112)
  obtain hsepw : ∀ j < w, ∀ b < 8, ofs B (off B (slot w aR2 + 8 * j) + BitVec.ofNat 64 b) < slot w aAcc ∨
      slot w aAcc + 8 * w ≤ ofs B (off B (slot w aR2 + 8 * j) + BitVec.ofNat 64 b) := fun j hj b hb => by
    rw [ofs_off B (by omega_using [hnw, e1, hj, hb])]; omega_using [sXA]
  refine WP.mono (copyWords_ok (S := B) (D := B) h4si ((k₄.gpr (by decide)).trans h3bx) h412
    (by omega_using [hw]) hw' (by omega_using [hnw, sXA, e1]) (fun j hj => hs₄.ld (by omega_using [e1, hj])) (fun j hj => hs₄.st (by omega_using [sXA, e1, hj]))
    hsepw) fun t₅ ⟨hc₅, _, ho₅, k₅⟩ => ?_
  rw [hm₄, hm₃, hx₂] at hc₅
  obtain hs₅ := hs₄.congr k₅.2.2
  obtain hm₂₄ : t₄.mem = t₂.mem := hm₄.trans hm₃
  rw [hm₂₄] at ho₅
  -- `v`.
  obtain hH₅ : Hdr t₅.mem B w minv :=
    (Arrays.of_outside (j := aAcc) (List.mem_singleton_self _) ho₅ (Nat.le_refl _) (by omega_using [])).hdr hH₂
  obtain hdi₅ : t₅.gpr .rdi = B := (k₅.gpr (by decide)).trans ((k₃₄.gpr (by decide)).trans hdi₂)
  obtain hl₅ : ∀ i < 32, InRegions (t₅.rd ++ t₅.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₅.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.rbx, .r8] (Q := fun t => t.gpr .rbx = off B (slot w aR2) ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.mem = t₅.mem) (by
    xrun [State.ea, hdr, hdi₅, hdrOff, hl₅ (sArr aR2) (by decide), hl₅ (sArr aTmp) (by decide),
      hH₅.harr aR2 (by decide), hH₅.harr aTmp (by decide)]) rfl) fun t₆ ⟨⟨_, h68, hm₆⟩, k₆⟩ => ?_)
  obtain hs₆ := hs₅.congr k₆.2.2
  obtain k₄₆ := k₅.trans k₆
  obtain h610 : t₆.gpr .r10 = off B (slot w aN) :=
    (k₄₆.gpr (by decide)).trans ((k₃₄.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h110))
  obtain h612 : t₆.gpr .r12 = BitVec.ofNat 64 w := (k₄₆.gpr (by decide)).trans h412
  obtain eV : slot w aTmp + 8 ≤ Z := by omega_using [sXV, e1]
  obtain hN₆ : wv t₆.mem B (slot w aN) w = N := by
    rw [hm₆, ho₅.wv (by omega_using [sMA]) (by omega_using [hnw, e2]), ho₂.wv (by omega_using [sM]) (by omega_using [hnw, e2]), hm₁, hn]
  obtain hT₆ : 2 ^ 63 ≤ (word t₆.mem B (slot w aN + 8 * (w - 1))).toNat := by
    rw [hm₆, ho₅.word (by omega_using [sMA]) (by omega_using [hnw, sMA, sAV, eV]), ho₂.word (by omega_using [sXA, sMA]) (by omega_using [hnw, sMA, sAV, eV]), hm₁]; exact hT
  refine WP.seq (WP.mono (recipN_ok hs₆ h610 h612 h68 (by omega_using [hw]) e2 eV hT₆) fun t₇ ⟨hm₇, k₇⟩ => ?_)
  obtain hvlt : (2 ^ 128 - 1) / (word t₆.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 128 - 1) / (word t₆.mem B (slot w aN + 8 * (w - 1))).toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega_using [hT₆])]; omega_using [hT₆]
    omega_using [this]
  obtain o₇ : Outside B (slot w aTmp) 8 t₆.mem t₇.mem := by rw [hm₇]; exact writeW_outside _ _ _ (by omega_using [hnw, eV])
  obtain hs₇ := hs₆.congr k₇.2.2
  obtain hdi₇ : t₇.gpr .rdi = B := (k₇.gpr (by decide)).trans ((k₆.gpr (by decide)).trans hdi₅)
  obtain hH₇ : Hdr t₇.mem B w minv :=
    (Arrays.of_outside (j := aTmp) (List.mem_singleton_self _) o₇ (Nat.le_refl _) (by omega_using [])).hdr
      (hm₆ ▸ hH₅)
  obtain hl₇ : ∀ i < 32, InRegions (t₇.rd ++ t₇.wr) (off B (8 * i)) 8 := fun i hi =>
    hs₇.ld (by have := hdr_lt_slot w 8 hi; omega_using [hZ, this])
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 w ∧ t.mem = t₇.mem)
    (by xrun [State.ea, hdr, hdi₇, hdrOff, hl₇ sW (by decide), hH₇.hw]) rfl) fun t₈ ⟨⟨h8cx, hm₈⟩, k₈⟩ => ?_)
  -- The values before the steps.
  obtain hN₈ : wv t₈.mem B (slot w aN) w = N := by rw [hm₈, o₇.wv (by omega_using [sMA, sAV]) (by omega_using [hnw, e2]), hN₆]
  obtain hT₈ : 2 ^ 63 ≤ (word t₈.mem B (slot w aN + 8 * (w - 1))).toNat := by
    rw [hm₈, o₇.word (by omega_using [sMA, sAV]) (by omega_using [hnw, sMA, sAV, eV])]; exact hT₆
  obtain hV₈ : (word t₈.mem B (slot w aTmp)).toNat =
      (2 ^ 128 - 1) / (word t₈.mem B (slot w aN + 8 * (w - 1))).toNat - 2 ^ 64 := by
    rw [hm₈, o₇.word (d := slot w aN + 8 * (w - 1)) (by omega_using [sMA, sAV]) (by omega_using [hnw, sMA, sAV, eV]), hm₇, word_writeW_self,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]
  obtain hX₈ : wv t₈.mem B (slot w aR2) w = 2 ^ (64 * w) - N := by
    rw [hm₈, o₇.wv (by omega_using [sXV]) (by omega_using [hnw, e1]), hm₆, ho₅.wv (by omega_using [sXA]) (by omega_using [hnw, e1]), hx₂]
  obtain hC₈ : wv t₈.mem B (slot w aAcc) w = 2 ^ (64 * w) - N := by
    rw [hm₈, o₇.wv (by omega_using [sAV]) (by omega_using [hnw, sAV, eV]), hm₆, hc₅]
  obtain hO₈ : wv t₈.mem B (slot w aR2) w < wv t₈.mem B (slot w aN) w := by rw [hX₈, hN₈]; omega_arith
  obtain hsp := steps_ok (hs₇.congr k₈.2.2) ((k₈.gpr (by decide)).trans hdi₇) (hm₈ ▸ hH₇) hZ hw h4 hw30
    (c := w) (by omega_using [hw]) (by omega_using [hw']) h8cx hT₈ hV₈ hO₈ (by rw [hC₈, hN₈]; omega_using [hNR])
  refine WP.mono hsp fun t ⟨hx, _, _, hf, hgt, kt⟩ => ⟨hgt, ?_, ?_, ?_, ?_⟩
  · rw [hx, hN₈]; exact Nat.mod_lt _ hN0
  · rw [hx, hX₈, hN₈, sub_mul_mod (Nat.le_of_lt hNR), Nat.mod_mod]
  · have f₂ : Frm B (r2Ranges w) s.mem t₂.mem := by
      rw [← hm₁]; exact Frm.of_arrays (Arrays.of_outside (j := aR2) (List.mem_singleton_self _) ho₂
        (Nat.le_refl _) (by omega_using [])) (by simp [r2Ranges])
    obtain f₅ : Frm B (r2Ranges w) t₂.mem t₅.mem :=
      Frm.of_arrays1 (Arrays.of_outside (j := aAcc) (List.mem_singleton_self _) ho₅ (Nat.le_refl _) (by omega_using []))
        (by simp [r2Ranges])
    obtain f₇ : Frm B (r2Ranges w) t₆.mem t₇.mem :=
      Frm.of_arrays1 (Arrays.of_outside (j := aTmp) (List.mem_singleton_self _) o₇ (Nat.le_refl _) (by omega_using []))
        (by simp [r2Ranges])
    exact ((((f₂.trans f₅).trans (by rw [hm₆]; exact Frm.refl _ _ _)).trans f₇).trans
      (by rw [hm₈]; exact Frm.refl _ _ _)).trans hf
  · exact ((((((k₁₂.trans k₃₄).trans k₅).trans k₆).trans k₇).trans k₈).trans kt).mono (by decide)

/-- `choice`: `R² mod m` for the odd `m` of `w ≥ 2` words, its top word not
zero, by word steps when `m`'s top bit is set and `w` is a multiple of 4 and
by `vg_rsa_public`'s computation otherwise: `r2_ok`'s result. -/
theorem choice_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N) (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h10 : s.gpr .r10 = off B (slot w aN)) (hodd : N % 2 = 1)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (R2Adx.choice M.mm) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hnw := hs.nowrap
  obtain hsm := slot_le (w := w) (show aN < 8 by decide)
  obtain hd8 : slot w aN + 8 * (w - 1) + 8 ≤ Z := by omega_using [hZ, hsm]
  obtain hld : InRegions (s.rd ++ s.wr) (off B (slot w aN + 8 * (w - 1))) 8 := hs.ld hd8
  unfold R2Adx.choice
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (2 ^ 63 ≤
      (word s.mem B (slot w aN + 8 * (w - 1))).toNat ∧ w % 4 = 0)) ∧ t.mem = s.mem) (by
    unfold R2Words.fastTest
    xrun [State.ea, ix, addrm8 h10 h12 (by omega_using [hw]), hld]
    rw [h12]
    exact fastFlag _ (by omega_using [hnw, hd8])) rfl) fun t₁ ⟨⟨hz₁, hm₁⟩, k₁⟩ => ?_)
  obtain hg₁ : Good t₁ B Z w minv := ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, hm₁ ▸ hg.hdr⟩
  obtain hn₁ : wv t₁.mem B (slot w aN) w = N := by rw [hm₁, hn]
  obtain hinv₁ : ((word t₁.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by rw [hm₁]; exact hinv
  generalize hP : decide (2 ^ 63 ≤ (word s.mem B (slot w aN + 8 * (w - 1))).toNat ∧ w % 4 = 0) = P at hz₁
  refine WP.ite P (by simp only [eval, hz₁]) (fun hc => ?_) (fun hc => ?_)
  · obtain ⟨hT, h4⟩ := of_decide_eq_true (hP.trans hc)
    refine WP.mono (fast_ok hg₁ hZ (by omega_using [hw, h4]) hw30 hn₁ hodd (by rw [hm₁]; exact hT) h4)
      fun t ⟨h1, h2, h3, h4', h5⟩ => ⟨h1, h2, h3, by rw [← hm₁]; exact h4', (k₁.trans h5).mono (by decide)⟩
  · rw [old_eq]
    refine WP.mono (r2_ok_with _ (rolled_sqs_spec M 5 (by decide)) hg₁ hZ hw hw30 hn₁ hinv₁ ((k₁.gpr (by decide)).trans h12)
      ((k₁.gpr (by decide)).trans h10) hodd hlo)
      fun t ⟨h1, h2, h3, h4', h5⟩ => ⟨h1, h2, h3, by rw [← hm₁]; exact h4', (k₁.trans h5).mono (by decide)⟩

end VG.Proof.Bignum.X86_64.R2ax

end

end

/-!
# `R² mod m` by word steps with ADX: constant time but for `m`

A step's addresses depend only on the working space and `w`, and its
branches, `fix3`'s and `fix`'s, on the signs of `t` over three words and
over all, functions of `x` and `m` (as `q̂` is, refined by `fix3`:
`SPub.qr`): in the
steps, `x` is `(R - m) 2^(64 j) mod m` after `j` of them, a function of `m`,
which is public (`SPub`, `step_ct`). The steps' count is `w` (`steps_ct`),
and `choice` branches on the top bit of `m` and on `w` (`choice_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep VG.Proof.Bignum.Recip

/-! ## A step -/

/-- The public data of a step: the working space, `x` and `m`. -/
structure SPub where
  L : Lay
  X : Nat
  M : Nat

/-- `R` and `2^64 R`. -/
abbrev SPub.R (p : SPub) : Nat := 2 ^ (64 * p.L.w)
abbrev SPub.W (p : SPub) : Nat := 2 ^ (64 * (p.L.w + 1))

/-- `q̂`, from the top words of `x` and `m`. -/
def SPub.q (p : SPub) : Nat :=
  min ((p.X / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64 * 2 ^ 64 + p.X / 2 ^ (64 * (p.L.w - 2)) % 2 ^ 64) /
    (p.M / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64)) (2 ^ 64 - 1)

/-- The word `w - i` of `x`, and of `m`. -/
def SPub.u (p : SPub) (i : Nat) : Nat := p.X / 2 ^ (64 * (p.L.w - i)) % 2 ^ 64
def SPub.d (p : SPub) (i : Nat) : Nat := p.M / 2 ^ (64 * (p.L.w - i)) % 2 ^ 64

/-- The top three words of `x`, and the top two of `m`. -/
def SPub.U (p : SPub) : Nat := p.u 1 * 2 ^ 128 + p.u 2 * 2 ^ 64 + p.u 3
def SPub.D (p : SPub) : Nat := p.d 1 * 2 ^ 64 + p.d 2

/-- `fix3` on `q̂` and `t` (over three words). -/
def fixQ (T q : Nat) : Nat := if 2 ^ 192 / 2 ≤ T then (q + (2 ^ 64 - 1)) % 2 ^ 64 else q
def fixT (D T : Nat) : Nat := if 2 ^ 192 / 2 ≤ T then (T + D) % 2 ^ 192 else T

/-- `t = U - q̂ D` (`R2Words.quot3`); `q̂` and `t` after one `fix3`; `q̂` after
two (`refine3`). -/
def SPub.T1 (p : SPub) : Nat := (p.U + (2 ^ 192 - p.q * p.D)) % 2 ^ 192
def SPub.q1 (p : SPub) : Nat := fixQ p.T1 p.q
def SPub.T2 (p : SPub) : Nat := fixT p.D p.T1
def SPub.qr (p : SPub) : Nat := fixQ p.T2 p.q1

theorem SPub.q_lt (p : SPub) : p.q < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
theorem fixQ_lt {T q : Nat} (h : q < 2 ^ 64) : fixQ T q < 2 ^ 64 := by
  unfold fixQ; split
  · exact Nat.mod_lt _ (by decide)
  · exact h
theorem SPub.qr_lt (p : SPub) : p.qr < 2 ^ 64 := fixQ_lt (fixQ_lt p.q_lt)

/-- `t = x 2^64 - q̂ m` modulo `2^64 R`. -/
def SPub.t1 (p : SPub) : Nat := (p.X * 2 ^ 64 + p.qr * (p.R - p.M) + p.qr * (p.W - p.R)) % p.W

/-- `t + m` if `t` is negative. -/
def fixV (W M T : Nat) : Nat := if W / 2 ≤ T then (T + M) % W else T

/-- `step_ok`'s hypotheses, with the values public. -/
def SPre (p : SPub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧ p.X < p.M ∧
    wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.M = p.R

theorem GoodL.congr {L : Lay} {s t : State} (h : GoodL L s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : GoodL L t :=
  ⟨⟨h.1.scr.congr hw, hdi.trans h.1.rdi, hm ▸ h.1.hdr⟩, h.2⟩

theorem SPre.congr {p : SPub} {s t : State} (h : SPre p s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : SPre p t := by
  obtain ⟨hg, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨GoodL.congr hg hm hw hdi, h1, h2, h3, hm ▸ h4, hm ▸ h5, hm ▸ h6, hm ▸ h7, h8, hm ▸ h9⟩

/-- After a step's loads. -/
def SB (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r8 = off p.L.B (slot p.L.w aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
    t.gpr .rbp = off p.L.B (slot p.L.w aTmp)

theorem pins_SB : Pins SB [.rbx, .r10, .r8, .r12, .rbp, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

theorem sb_ok {p : SPub} {s : State} (h : SPre p s) : WP isa (.block R2Words.bases) s (SB p) :=
  WP.mono (R2w.stepBases_ok h.1) fun t ⟨h1, h2, h3, h4, h5, hm, k⟩ =>
    ⟨SPre.congr h hm k.2.2 (k.gpr (by decide)), h1, h2, h3, h4, h5⟩

/-- With the estimate `V` in `rcx`. -/
def SQ (V : Nat) (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rcx = BitVec.ofNat 64 V

theorem pins_SQ (V : SPub → Nat) : Pins (fun p => SQ (V p) p) [.rbx, .r10, .r12] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]

theorem sq_ok {p : SPub} {s : State} (h : SB p s) : WP isa (.block R2Words.quot) s (SQ p.q p) := by
  obtain ⟨hp, hbx, h10, _, h12, hbp⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, _, hw', hd, hv, hX, hM, hXM, _⟩ := hp'
  have hs := hg.1.scr
  have hZ := hg.2
  have hn := hs.nowrap
  obtain hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  obtain hsv := slot_le (w := p.L.w) (show aTmp < 8 by decide)
  obtain hu := R2w.top_le (by omega_using [hw]) (hX ▸ hM ▸ hXM)
  refine WP.mono (R2w.quot_ok hs hbx h10 h12 hbp (by omega_using [hw]) (by omega_using [hZ, hsx]) (by omega_using [hZ, hsm]) (by omega_using [hZ, hsv]) hu hd hv)
    fun t ⟨hcx, hm, k⟩ => ⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
      (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, ?_⟩
  rw [hcx, word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - 1 < p.L.w by omega_using [hw]),
    word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - 2 < p.L.w by omega_using [hw]),
    word_of_wv s.mem p.L.B (slot p.L.w aN) p.L.w (show p.L.w - 1 < p.L.w by omega_using [hw]), hX, hM]
  rfl

/-- At the start of the pass. -/
def SH (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rsi = off p.L.B (slot p.L.w aAcc) ∧
    t.gpr .rdx = BitVec.ofNat 64 p.qr ∧ t.gpr .r8 = 0 ∧ t.gpr .r9 = 0 ∧ t.gpr .r14 = 0 ∧ t.gpr .r15 = 0

/-- A sum's low part from its carry. -/
theorem mod_of_carry {R A W c : Nat} (hR : R < W) (hc : c < 2) (h : R + W * c = A) : R = A % W := by
  rcases (show c = 0 ∨ c = 1 by omega_using [hc]) with rfl | rfl
  · rw [Nat.mul_zero, Nat.add_zero] at h; rw [← h, Nat.mod_eq_of_lt hR]
  · rw [Nat.mul_one] at h; rw [← h, Nat.add_mod_right, Nat.mod_eq_of_lt hR]

/-- A difference's low part from its borrow. -/
theorem mod_of_borrow {T P U W b : Nat} (hT : T < W) (hP : P ≤ W) (hb : b < 2) (h : T + P = U + W * b) :
    T = (U + (W - P)) % W := by
  rcases (show b = 0 ∨ b = 1 by omega_using [hb]) with rfl | rfl
  · rw [Nat.mul_zero, Nat.add_zero] at h
    rw [show U + (W - P) = T + W by omega_using [h, hP], Nat.add_mod_right, Nat.mod_eq_of_lt hT]
  · rw [Nat.mul_one] at h
    rw [show U + (W - P) = T by omega_using [h, hP], Nat.mod_eq_of_lt hT]

/-- The words `w - i` of `x` and `m`. -/
theorem SPre.words {p : SPub} {s : State} (h : SPre p s) :
    (∀ i, 1 ≤ i → i ≤ 3 → (word s.mem p.L.B (slot p.L.w aR2 + 8 * (p.L.w - i))).toNat = p.u i) ∧
    (∀ i, 1 ≤ i → i ≤ 2 → (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - i))).toNat = p.d i) := by
  obtain ⟨_, hw, _, _, _, _, hX, hM, _, _⟩ := h
  exact ⟨fun i h1 _ => by rw [word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - i < p.L.w by omega_using [hw, h1]), hX]; rfl,
    fun i h1 _ => by rw [word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - i < p.L.w by omega_using [hw, h1]), hM]; rfl⟩

/-- With `t = T` in `r15`, `r14`, `r13`. -/
def S3 (T V : Nat) (p : SPub) (t : State) : Prop :=
  SQ V p t ∧ (t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat = T

theorem pins_S3 (T V : SPub → Nat) : Pins (fun p => S3 (T p) (V p) p) [.rbx, .r10, .r12] :=
  fun p s₁ s₂ h₁ h₂ => pins_SQ V p s₁ s₂ h₁.1 h₂.1

theorem s3_ok {p : SPub} {s : State} (h : SQ p.q p s) : WP isa (.block R2Words.quot3) s (S3 p.T1 p.q p) := by
  obtain ⟨hp, hbx, h10, h12, hcx⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, _, _, _, _, _, _, _, _⟩ := hp'
  obtain ⟨hu, hd⟩ := hp.words
  have hs := hg.1.scr
  have hZ := hg.2
  obtain hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  refine WP.mono (R2w.quot3_ok hs hbx h10 h12 (by omega_using [hw]) (by omega_using [hZ, hsx]) (by omega_using [hZ, hsm]))
    fun t ⟨⟨b, hb, hv⟩, hm, k⟩ => ⟨⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
      (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩, ?_⟩
  rw [hu 1 (by omega_using []) (by omega_using []), hu 2 (by omega_using []) (by omega_using []),
    hu 3 (by omega_using []) (by omega_using []), hd 1 (by omega_using []) (by omega_using []),
    hd 2 (by omega_using []) (by omega_using []), hcx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.q_lt] at hv
  have hq := p.q_lt
  obtain hD : p.D < 2 ^ 128 := by
    have := Nat.mod_lt (p.M / 2 ^ (64 * (p.L.w - 1))) (show 0 < 2 ^ 64 by decide)
    have := Nat.mod_lt (p.M / 2 ^ (64 * (p.L.w - 2))) (show 0 < 2 ^ 64 by decide)
    unfold SPub.D SPub.d; omega_using []
  obtain hqD : p.q * p.D ≤ 2 ^ 192 := Nat.le_trans (Nat.mul_le_mul (Nat.le_of_lt hq) (Nat.le_of_lt hD)) (by decide)
  obtain hT : (t.gpr .r15).toNat * 2 ^ 128 + (t.gpr .r14).toNat * 2 ^ 64 + (t.gpr .r13).toNat < 2 ^ 192 := by
    have := (t.gpr .r15).isLt; have := (t.gpr .r14).isLt; have := (t.gpr .r13).isLt; omega_using []
  exact mod_of_borrow hT hqD hb hv

/-- `rcx - 1` as `fixQ` gives it. -/
theorem ofNat_sub_one (V : Nat) : BitVec.ofNat 64 V - 1 = BitVec.ofNat 64 ((V + (2 ^ 64 - 1)) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega_using []

/-- With the sign of `t` in `CF`. -/
def S3c (T V : SPub → Nat) (p : SPub) (t : State) : Prop :=
  S3 (T p) (V p) p t ∧ t.cf = some (decide (2 ^ 192 / 2 ≤ T p))

/-- `fix3` leaks the same in runs with the same `t`. -/
theorem fix3_ct (T V : SPub → Nat) :
    RelCT isa (Two fun p => S3 (T p) (V p) p) fix3 (Two fun p => S3 (fixT p.D (T p)) (fixQ (T p) (V p)) p) := by
  unfold fix3
  refine RelCT.seq (two_piece (Ψ := S3c T V) _ (pins_S3 T V) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨⟨hp, hbx, h10, h12, hcx⟩, hT⟩ := h
    refine WP.mono (WP.keep [.r11] (Q := fun t => t.cf = some (decide (2 ^ 63 ≤ (s.gpr .r15).toNat)) ∧
        t.mem = s.mem) (by xrun [top_cf]) rfl) fun t ⟨⟨hc, hm⟩, k⟩ =>
      ⟨⟨⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10,
        (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩, ?_⟩, ?_⟩
    · rw [k.gpr (by decide), k.gpr (by decide), k.gpr (by decide)]; exact hT
    · rw [hc, ← hT]
      have := (s.gpr .r15).isLt; have := (s.gpr .r14).isLt; have := (s.gpr .r13).isLt
      exact congrArg some (decide_eq_decide.mpr (by omega_using []))
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · refine (two_piece (Ψ := fun p => S3 (fixT p.D (T p)) (fixQ (T p) (V p)) p) _
      (fun p s₁ s₂ h₁ h₂ => pins_S3 T V p s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => ?_).mono
      (fun _ _ h => h) fun _ _ h => h
    simp only [eval, hc, Option.some.injEq, decide_eq_true_eq] at hb
    obtain ⟨⟨hp, hbx, h10, h12, hcx⟩, hT⟩ := h
    have hp' := hp
    obtain ⟨hg, hw, _, _, _, _, _, _, _, _⟩ := hp'
    obtain ⟨_, hd⟩ := hp.words
    have hZ := hg.2
    obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (fix3Body_ok hg.1.scr h10 h12 (by omega_using [hw]) (by omega_using [hZ, hsm]))
      fun t ⟨hcx', ⟨c, hc', hv⟩, hm, k⟩ => ⟨⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
        (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, ?_⟩, ?_⟩
    · rw [hcx', hcx, ofNat_sub_one]; unfold fixQ; simp only [hb, ↓reduceIte]
    · rw [hT, hd 1 (by omega_using []) (by omega_using []), hd 2 (by omega_using []) (by omega_using [])] at hv
      unfold fixT; simp only [hb, ↓reduceIte]
      have := (t.gpr .r15).isLt; have := (t.gpr .r14).isLt; have := (t.gpr .r13).isLt
      exact mod_of_carry (by omega_using []) hc' hv
  · refine (two_piece (Ψ := fun p => S3 (fixT p.D (T p)) (fixQ (T p) (V p)) p) [] (fun _ _ _ _ _ _ h => nomatch h)
      (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => WP.block_nil ?_).mono (fun _ _ h => h) fun _ _ h => h
    simp only [eval, hc, Option.some.injEq, decide_eq_false_iff_not] at hb
    unfold fixT fixQ
    simp only [hb, ↓reduceIte]
    exact h

theorem sh_ok {p : SPub} {s : State} (h : SQ p.qr p s) : WP isa (.block mulHead) s (SH p) := by
  obtain ⟨hp, hbx, h10, h12, hcx⟩ := h
  have hg := hp.1
  obtain hhd := hdr_lt_slot p.L.w 0 (show sArr aAcc < 32 by decide)
  obtain hs0 := slot_le (w := p.L.w) (show 0 < 8 by decide)
  have hZ := hg.2
  refine WP.mono (mulHead_ok hg.1.scr hg.1.rdi (hg.1.hdr.harr aAcc (by decide)) (by omega_using [hhd, hs0, hZ]))
    fun t ⟨hdx, hsi, h8, h9, h14, h15, hm, k⟩ => ⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)),
      (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hsi,
      hdx.trans hcx, h8, h9, h14, h15⟩

theorem pins_SH : Pins SH [.rbx, .rsi, .r12, .r15, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.2.2.2.2.2, h₂.2.2.2.2.2.2.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

/-- Before a `fix`, with `t = V`. -/
def SF (V : Nat) (p : SPub) (t : State) : Prop :=
  GoodL p.L t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧
    wv t.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) = V ∧ wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M

/-- `T` from `T + q R ≡ V`. -/
theorem t_eq {T q R W V : Nat} (hT : T < W) (hR : R ≤ W) (h : (T + q * R) % W = V % W) :
    T = (V + q * (W - R)) % W := by
  obtain e : (T + q * R + q * (W - R)) % W = (V + q * (W - R)) % W := by
    rw [Nat.add_mod (T + q * R), h, ← Nat.add_mod]
  rw [Nat.add_assoc, ← Nat.mul_add, show R + (W - R) = W by omega_using [hR], Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hT] at e
  exact e

theorem sf_ok {p : SPub} {s : State} (h : SH p s) :
    WP isa (.seq tiles (.block mulTop)) s (SF p.t1 p) := by
  obtain ⟨hp, hbx, h10, h12, hsi, hdx, h8, h9, h14, h15⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, hw4, hw', _, _, hX, hM, hXM, hC⟩ := hp'
  have hs := hg.1.scr
  have hZ := hg.2
  have hn := hs.nowrap
  obtain hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  obtain hsa := slot_le (w := p.L.w) (show aAcc < 8 by decide)
  obtain sXA := slot_sep (w := p.L.w) (show aR2 ≠ aAcc by decide)
  obtain sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
  have hq := p.qr_lt
  refine WP.mono (mulBody_ok (N := p.L.w / 4) hs hbx hsi h12 h8 h9 h14 h15 (by omega_using [hw4]) (by omega_using [hw]) (by omega_using [hZ, hn, hsa])
    (by omega_using [hZ, hsx]) (by omega_using [hZ, hsa]) (by omega_using [sXA])) fun t ⟨hv, ho, k⟩ => ?_
  obtain hM' : wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M := by rw [ho.wv (by omega_using [sXM]) (by omega_using [hZ, hn, hsm]), hM]
  obtain ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
  refine ⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩,
    (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hw, hw', ?_, hM'⟩
  rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, hX, show wv s.mem p.L.B (slot p.L.w aAcc) p.L.w = p.R - p.M by
    omega_using [hC]] at hv
  unfold SPub.t1
  exact t_eq (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_using [])) hv

theorem pins_SF (V : SPub → Nat) : Pins (fun p => SF (V p) p) [.rbx, .r10, .r12, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.1.1.rdi, h₂.1.1.rdi]

/-- With the sign of `t` in `CF`. -/
def SFc (V : SPub → Nat) (p : SPub) (t : State) : Prop :=
  SF (V p) p t ∧ t.cf = some (decide (p.W / 2 ≤ V p))

/-- `fix` leaks the same in runs with the same `t`, which it makes `fixV`. -/
theorem fix_ct (V : SPub → Nat) :
    RelCT isa (Two fun p => SF (V p) p) fix (Two fun p => SF (fixV p.W p.M (V p)) p) := by
  unfold fix
  refine RelCT.seq (two_piece (Ψ := SFc V) _ (pins_SF V) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    have hs := hg.1.scr
    have hn := hs.nowrap
    have hZ := hg.2
    obtain hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    obtain hea : s.ea (ix .rbx .r12) = off p.L.B (slot p.L.w aR2 + 8 * p.L.w) := ea_ix0 s hbx h12
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (2 ^ 63 ≤
        (word s.mem p.L.B (slot p.L.w aR2 + 8 * p.L.w)).toNat)) ∧ t.mem = s.mem) (by
      xrun [hea, hs.ld (show slot p.L.w aR2 + 8 * p.L.w + 8 ≤ p.L.Z by omega_using [hZ, hsx]), top_cf]) rfl)
      fun t ⟨⟨hc, hm⟩, k⟩ => ⟨⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
        (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hw, hw', hm ▸ hT, hm ▸ hM⟩, ?_⟩
    rw [hc, ← hT]
    congr 1
    exact decide_eq_decide.mpr (R2w.top_half _ _ _ _).symm
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · refine (two_piece (Ψ := fun p => SF (fixV p.W p.M (V p)) p) _ (fun p s₁ s₂ h₁ h₂ => pins_SF V p s₁ s₂ h₁.1.1 h₂.1.1)
      (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
    obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    simp only [eval, hc, Option.some.injEq, decide_eq_true_eq] at hb
    have hs := hg.1.scr
    have hn := hs.nowrap
    have hZ := hg.2
    obtain hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    obtain sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧ t.mem = s.mem)
      (by xrun [hbx]) rfl) fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_)
    refine WP.mono (R2w.addBack_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h10) h8
      ((k₁.gpr (by decide)).trans h12) (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hZ, hsm]) (by omega_using [hZ, hsx]) (by omega_using [sXM]))
      fun t ⟨c, hv, ho, k⟩ => ?_
    simp only [hm₁, ← R2w.top_half, hT, hM] at hv
    simp only [hb, ↓reduceIte] at hv
    obtain ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem := by
      rw [← hm₁]; exact Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
    obtain kk := k₁.trans k
    refine ⟨⟨⟨hs.congr (k.2.2.trans k₁.2.2), (kk.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩,
      (kk.gpr (by decide)).trans hbx, (kk.gpr (by decide)).trans h10, (kk.gpr (by decide)).trans h12, hw, hw', ?_,
      by rw [ha.wv_of_not_mem (by decide) (by decide) (by omega_using [hn, hZ])]; exact hM⟩
    obtain hlt := wv_lt t.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
    unfold fixV
    simp only [hb, ↓reduceIte]
    cases c
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
      rw [← hv, Nat.mod_eq_of_lt hlt]
    · simp only [Bool.toNat_true, Nat.mul_one] at hv
      rw [← hv, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · refine (two_piece (Ψ := fun p => SF (fixV p.W p.M (V p)) p) [] (fun _ _ _ _ _ _ h => nomatch h)
      (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => WP.block_nil ?_).mono (fun _ _ h => h) fun _ _ h => h
    simp only [eval, hc, Option.some.injEq, decide_eq_false_iff_not] at hb
    obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    exact ⟨hg, hbx, h10, h12, hw, hw', by unfold fixV; simp only [hb, ↓reduceIte]; exact hT, hM⟩

/-- The pass: `t` leaks nothing but its addresses. -/
theorem mulSub_ct : RelCT isa (Two fun p => SQ p.qr p) mulSub (Two (fun p => SF p.t1 p)) := by
  unfold mulSub
  refine RelCT.seq (two_piece (Ψ := SH) [.rdi] (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide)
    fun _ _ h => sh_ok h) ?_
  exact two_post (two_taint _ pins_SH (by taint_decide)) fun _ _ h => sf_ok h

/-- A step leaks the same in runs with the same working space, `x` and `m`. -/
theorem step_ct : RelCT isa (Two SPre) step fun _ _ => True := by
  rw [show step = .seq (.block R2Words.bases) (.seq (.block R2Words.quot) (.seq refine3 (.seq mulSub fix))) from rfl]
  refine RelCT.seq (two_piece (Ψ := SB) [.rdi] (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide)
    fun _ _ h => sb_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := fun p => SQ p.q p) _ pins_SB (by taint_decide) fun _ _ h => sq_ok h) ?_
  obtain hr : RelCT isa (Two fun p => SQ p.q p) refine3 (Two fun p => SQ p.qr p) := by
    unfold refine3
    refine RelCT.seq (two_piece (Ψ := fun p => S3 p.T1 p.q p) _ (pins_SQ SPub.q) (by taint_decide)
      fun _ _ h => s3_ok h) (RelCT.seq (fix3_ct SPub.T1 SPub.q) ((fix3_ct SPub.T2 SPub.q1).mono (fun _ _ h => h)
        fun _ _ h => ?_))
    obtain ⟨p, h₁, h₂⟩ := h
    exact ⟨p, h₁.1, h₂.1⟩
  exact RelCT.seq hr (RelCT.seq mulSub_ct ((fix_ct (fun p => p.t1)).mono (fun _ _ h => h) fun _ _ _ => trivial))

/-! ## The steps -/

/-- The public data of `steps`: the working space, the count and `m`. -/
structure StPub where
  L : Lay
  c : Nat
  M : Nat

/-- `x` after `j` steps from `R - m`. -/
def StPub.X (p : StPub) (j : Nat) : Nat := (2 ^ (64 * p.L.w) - p.M) * 2 ^ (64 * j) % p.M

/-- What `steps` keeps, after `j` steps. -/
def StepsAt (p : StPub) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (T : Nat), StepsInv σ p.L.B p.L.Z p.L.w p.L.minv p.c (2 ^ (64 * p.L.w) - p.M) p.M T j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧ p.c < 2 ^ 31 ∧ 0 < p.M ∧ 2 ^ 63 ≤ T

theorem stepsAt_pre {p : StPub} {j : Nat} {t : State} (h : StepsAt p j t) :
    SPre ⟨p.L, p.X j, p.M⟩ t := by
  obtain ⟨_, T, hI, hZ, hw, hw4, hw', _, hM, hT⟩ := h
  exact ⟨⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩, hw, hw4, hw', by rw [hI.top]; exact hT, by rw [hI.rcp, hI.top], hI.xv,
    hI.nv, Nat.mod_lt _ hM, hI.acc⟩

/-- `steps`' hypotheses. -/
def StepsPre (p : StPub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧ 1 ≤ p.c ∧ p.c < 2 ^ 31 ∧
    s.gpr .rcx = BitVec.ofNat 64 p.c ∧ 2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.M ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    2 ^ (64 * p.L.w) - p.M < p.M ∧ wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.M = 2 ^ (64 * p.L.w)

/-- `steps` leaks the same in runs with the same working space, count and `m`. -/
theorem steps_ct : RelCT isa (Two StepsPre) steps (Two fun p s => StepsAt p p.c s) := by
  rw [steps_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ StepsAt p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨hg, hw, hw4, hw', hc1, hc', hcx, hT, hv, hX, hN, hO, hC⟩
    obtain hM : 0 < p.M := by omega_using [hO]
    obtain hO' : wv s.mem p.L.B (slot p.L.w aR2) p.L.w < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by
      rw [hX, hN]; exact hO
    refine WP.mono (stepsStart_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hcx hO' hv (by rw [hN]; exact hC))
      fun t hI => ⟨by omega_using [hc1], s, _, ?_, hg.2, hw, hw4, hw', hc', hM, hT⟩
    rw [hX, hN] at hI; exact hI
  refine two_loop (Φ := StepsAt) (fun p => p.c) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun (q : StPub × Nat) s => GoodL q.1.L s)
      ((two_map (fun q : StPub × Nat => (⟨q.1.L, q.1.X q.2, q.1.M⟩ : SPub)) (fun _ _ h => stepsAt_pre h.2)
        step_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_good q.1.L s₁ s₂ h₁ h₂) (by taint_decide))
    rintro ⟨p, j⟩ s ⟨hj, h⟩
    obtain hp := stepsAt_pre h
    obtain ⟨hg, hw, hw4, hw', hd, hv, hX, hN, hXM, hC⟩ := hp
    exact WP.mono (step_ok hg hw hw4 hw' hd hv (by rw [hX, hN]; exact hXM) (by rw [hN]; exact hC))
      fun t ⟨hg', _⟩ => hg'
  · rintro p j s hj ⟨σ, T, hI, hZ, hw, hw4, hw', hc', hM, hT⟩
    exact WP.mono (stepIter_ok hZ hw hw4 hw' hc' hM hT hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, T, hI', hZ, hw, hw4, hw', hc', hM, hT⟩,
        fun e => e ▸ ⟨σ, T, hI', hZ, hw, hw4, hw', hc', hM, hT⟩⟩

/-! ## The reciprocal's corrections

`recipN`'s loops branch on `v` and `d`, which agree in both runs: `d` is
`m`'s top word, and `v` starts as `guessV d`. -/

section Recip
variable {α : Type} (Φ : α → State → Prop) (D : α → Nat)

/-- `Φ`, `d = D a` in `rsi` and the word `v` in `rcx`. -/
def RD (q : α × Nat) (s : State) : Prop :=
  Φ q.1 s ∧ s.gpr .rsi = BitVec.ofNat 64 (D q.1) ∧ s.gpr .rcx = BitVec.ofNat 64 q.2 ∧ q.2 < 2 ^ 64

theorem pins_RD (n : Nat) : Pins (fun a s => RD Φ D (a, n) s) [.rcx, .rsi] := by
  intro a s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.1, h₂.2.1]

/-- With `(2^64 + v) d < 2^128`. -/
def RU (q : α × Nat) (s : State) : Prop := RD Φ D q s ∧ over q.2 (D q.1) = false

theorem pins_RU (n : Nat) : Pins (fun a s => RU Φ D (a, n) s) [.rcx, .rsi] :=
  fun a s₁ s₂ h₁ h₂ => pins_RD Φ D n a s₁ s₂ h₁.1 h₂.1

theorem downLoop_ct (hΦ : ∀ a s t, Φ a s → t.mem = s.mem → Keep [.rdx, .r14, .rax, .rcx] s t → Φ a t)
    (hD : ∀ a, D a < 2 ^ 64) :
    RelCT isa (Two (RD Φ D)) (.loop (.block recipDown) .ne) (Two (RU Φ D)) := by
  obtain key : ∀ n, RelCT isa (fun s₁ s₂ => ∃ a, RD Φ D (a, n) s₁ ∧ RD Φ D (a, n) s₂)
      (.loop (.block recipDown) .ne) (Two (RU Φ D)) := by
    refine RelCT.loop (M := isa) (fun n s₁ s₂ => ∃ a, RD Φ D (a, n) s₁ ∧ RD Φ D (a, n) s₂) fun n => ?_
    refine (two_post (Φ := fun a s => RD Φ D (a, n) s)
      (Ψ := fun a s => RD Φ D (a, n - (over n (D a)).toNat) s ∧ s.zf = some (!over n (D a)))
      (two_taint [.rcx, .rsi] (pins_RD Φ D n) (by taint_decide)) fun a s h => ?_).mono (fun _ _ h => h) ?_
    · exact WP.mono (down_ok h.2.2.1 h.2.2.2 h.2.1 (hD a)) fun t ⟨hcx, hz, hm, k⟩ =>
        ⟨⟨hΦ _ _ _ h.1 hm k, (k.gpr (by decide)).trans h.2.1, hcx, by omega_using [h.2.2.2]⟩, hz⟩
    · rintro s₁ s₂ ⟨a, ⟨h₁, z₁⟩, h₂, z₂⟩
      refine ⟨by simp only [eval, z₁, z₂], fun hf => ?_, fun ht => ?_⟩
      · have ho : over n (D a) = false := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using hf
        rw [ho, Bool.toNat_false, Nat.sub_zero] at h₁ h₂
        exact ⟨(a, n), ⟨h₁, ho⟩, h₂, ho⟩
      · have ho : over n (D a) = true := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using ht
        rw [ho, Bool.toNat_true] at h₁ h₂
        exact ⟨n - 1, by have := over_pos (hD a) ho; omega_using [this], a, h₁, h₂⟩
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂ => key q.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨q.1, h₁, h₂⟩ e₁ e₂

theorem upLoop_ct (hΦ : ∀ a s t, Φ a s → t.mem = s.mem → Keep [.rdx, .r11, .r14, .rax, .rcx] s t → Φ a t)
    (hD : ∀ a, D a < 2 ^ 64) :
    RelCT isa (Two (RU Φ D)) (.loop (.block recipUp) .ne)
      (Two fun q s => RU Φ D q s ∧ up q.2 (D q.1) = false) := by
  obtain key : ∀ n, RelCT isa (fun s₁ s₂ => ∃ a v, n = 2 ^ 64 - v ∧ RU Φ D (a, v) s₁ ∧ RU Φ D (a, v) s₂)
      (.loop (.block recipUp) .ne) (Two fun q s => RU Φ D q s ∧ up q.2 (D q.1) = false) := by
    refine RelCT.loop (M := isa) (fun n s₁ s₂ => ∃ a v, n = 2 ^ 64 - v ∧ RU Φ D (a, v) s₁ ∧ RU Φ D (a, v) s₂)
      fun n => ?_
    refine RelCT.mono (P := Two fun (q : α × Nat) s => n = 2 ^ 64 - q.2 ∧ RU Φ D q s) ?_
      (fun s₁ s₂ ⟨a, v, hn, h₁, h₂⟩ => ⟨(a, v), ⟨hn, h₁⟩, hn, h₂⟩) (fun _ _ h => h)
    refine (two_post (Φ := fun (q : α × Nat) s => n = 2 ^ 64 - q.2 ∧ RU Φ D q s)
      (Ψ := fun q s => n = 2 ^ 64 - q.2 ∧ RD Φ D (q.1, q.2 + (up q.2 (D q.1)).toNat) s ∧
        over q.2 (D q.1) = false ∧ s.zf = some (!up q.2 (D q.1)))
      (two_taint [.rcx, .rsi] (fun q s₁ s₂ h₁ h₂ => pins_RU Φ D q.2 q.1 s₁ s₂ h₁.2 h₂.2) (by taint_decide))
      fun q s h => ?_).mono (fun _ _ h => h) ?_
    · obtain ⟨hn, ⟨hΦ', hsi, hcx, hv⟩, ho⟩ := h
      obtain hb : q.2 + (up q.2 (D q.1)).toNat < 2 ^ 64 := by
        cases hu : up q.2 (D q.1)
        · rw [Bool.toNat_false, Nat.add_zero]; exact hv
        · unfold up at hu
          rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hu
          rw [Bool.toNat_true]; omega_using [hv, hu.1]
      exact WP.mono (up_ok hcx hv hsi (hD q.1)) fun t ⟨hcx', hz, hm, k⟩ =>
        ⟨hn, ⟨hΦ _ _ _ hΦ' hm k, (k.gpr (by decide)).trans hsi, hcx', hb⟩, ho, hz⟩
    · rintro s₁ s₂ ⟨⟨a, v⟩, ⟨hn, h₁, ho, z₁⟩, -, h₂, -, z₂⟩
      refine ⟨by simp only [eval, z₁, z₂], fun hf => ?_, fun ht => ?_⟩
      · have hu : up v (D a) = false := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using hf
        rw [hu, Bool.toNat_false, Nat.add_zero] at h₁ h₂
        exact ⟨(a, v), ⟨⟨h₁, ho⟩, hu⟩, ⟨h₂, ho⟩, hu⟩
      · have hu : up v (D a) = true := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using ht
        rw [hu, Bool.toNat_true] at h₁ h₂
        unfold up at hu
        rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not] at hu
        exact ⟨2 ^ 64 - (v + 1), by omega_using [hn, h₁.2.2.2, hu.1], a, v + 1, rfl, ⟨h₁, hu.2⟩, h₂, hu.2⟩
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂ =>
    key (2 ^ 64 - q.2) s₁ s₂ t₁ t₂ s₁' s₂' ⟨q.1, q.2, rfl, h₁, h₂⟩ e₁ e₂

end Recip

/-! ## `fast` -/

/-- What `fast` keeps from `R - m` on, `x = R - m`. -/
def FX (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.L.w % 4 = 0 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.N ∧ 2 ^ (64 * p.L.w) - p.N < p.N

/-- After `R - m`. -/
def FX2 (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ s.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- Before the copy into the accumulator. -/
def FX3 (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ s.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧ s.gpr .rbx = off p.L.B (slot p.L.w aAcc) ∧
    s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- With `mc = R - m` in the accumulator. -/
def FXA (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.N = 2 ^ (64 * p.L.w) ∧
    s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- Before `v`. -/
def FX5 (p : R2Pub) (s : State) : Prop := FXA p s ∧ s.gpr .r8 = off p.L.B (slot p.L.w aTmp)

/-- After `v`. -/
def FX6 (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.L.w % 4 = 0 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.N ∧ 2 ^ (64 * p.L.w) - p.N < p.N ∧
    wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.N = 2 ^ (64 * p.L.w) ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64

theorem pins_FX2 : Pins FX2 [.rbx, .r10, .r12, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

theorem pins_FX3 : Pins FX3 [.r8, .rbx, .r12] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.2, h₂.2.2.2.2]

theorem pins_FX5 : Pins FX5 [.r10, .r12, .r8] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.1.2.2.1, h₂.1.2.2.1]
  · rw [h₁.1.2.2.2, h₂.1.2.2.2]
  · rw [h₁.2, h₂.2]

theorem FX.congr {p : R2Pub} {s t : State} (h : FX p s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : FX p t := by
  obtain ⟨hg, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨GoodL.congr hg hm hw hdi, h1, h2, h3, hm ▸ h4, hm ▸ h5, hm ▸ h6, h7⟩

/-- `m`'s top word, a word under `FX`. -/
def topW (p : R2Pub) : Nat := p.top % 2 ^ 64

theorem FX.top {p : R2Pub} {s : State} (h : FX p s) :
    word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1)) = BitVec.ofNat 64 (topW p) := by
  obtain ⟨-, hw, -, -, hn, -⟩ := h
  obtain hsplit : p.N = p.N % 2 ^ (64 * (p.L.w - 1)) +
      2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
    obtain e : wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1 + 1) = p.N := by
      rw [Nat.sub_add_cancel (by omega_using [hw])]; exact hn
    rw [wv] at e
    obtain hlt := wv_lt s.mem p.L.B (slot p.L.w aN) (p.L.w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  obtain hT : (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top := by
    unfold R2Pub.top
    obtain hP := Nat.two_pow_pos (64 * (p.L.w - 1))
    have := Nat.mod_lt p.N hP
    rw [Nat.div_eq_of_lt_le (k := (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat) ?_ ?_]
    · rw [Nat.mul_comm]; omega_using [hsplit]
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega_using [hsplit]
  apply BitVec.eq_of_toNat_eq
  rw [hT, BitVec.toNat_ofNat, topW, Nat.mod_mod]
  exact (Nat.mod_eq_of_lt (hT ▸ BitVec.isLt _)).symm

theorem FX5.keep {p : R2Pub} {s t : State} {rs : List Reg} (h : FX5 p s) (hm : t.mem = s.mem) (k : Keep rs s t)
    (h10 : .r10 ∉ rs) (h12 : .r12 ∉ rs) (h8 : .r8 ∉ rs) (hdi : .rdi ∉ rs) : FX5 p t :=
  ⟨⟨FX.congr h.1.1 hm k.2.2 (k.gpr hdi), hm ▸ h.1.2.1, (k.gpr h10).trans h.1.2.2.1, (k.gpr h12).trans h.1.2.2.2⟩,
    (k.gpr h8).trans h.2⟩

/-- `recipN` leaks the same in runs that agree on `m`: its loops branch on
`m`'s top word and on `v`, which starts as `guessV` of it. -/
theorem recipN_ct : RelCT isa (Two FX5) recipN (Two FX6) := by
  obtain hD : ∀ p, topW p < 2 ^ 64 := fun p => Nat.mod_lt _ (by decide)
  unfold recipN
  simp only [seqs]
  -- The guess.
  obtain hguess : RelCT isa (Two FX5) (.block recipGuess) (Two (RD FX5 topW)) := by
    refine (two_piece (Ψ := fun p s => RD FX5 topW (p, (guessV (BitVec.ofNat 64 (topW p))).toNat) s)
      _ pins_FX5 (by taint_decide) fun p s h => ?_).mono (fun _ _ h => h)
        fun s₁ s₂ ⟨p, h₁, h₂⟩ => ⟨(p, (guessV (BitVec.ofNat 64 (topW p))).toNat), h₁, h₂⟩
    have hg := h.1.1.1
    have hs := hg.1.scr
    have hZ := hg.2
    obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (recipGuess_ok hs h.1.2.2.1 h.1.2.2.2 (by have := h.1.1.2.1; omega_using [this])
      (by omega_using [hZ, hsm])) fun t ⟨hsi, hcx, hm, k⟩ => ?_
    rw [FX.top h.1.1] at hsi hcx
    exact ⟨FX5.keep h hm k (by decide) (by decide) (by decide) (by decide), hsi,
      by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq], BitVec.isLt _⟩
  refine RelCT.seq hguess ?_
  -- The corrections.
  refine RelCT.seq (downLoop_ct FX5 topW (fun p s t h hm k => FX5.keep h hm k (by decide) (by decide)
    (by decide) (by decide)) hD) ?_
  refine RelCT.seq (upLoop_ct FX5 topW (fun p s t h hm k => FX5.keep h hm k (by decide) (by decide)
    (by decide) (by decide)) hD) ?_
  -- `v` to the temporary.
  refine (two_piece (Ψ := fun q s => FX6 q.1 s) [.r8] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁.1.1.1.2, h₂.1.1.1.2])
    (by taint_decide) fun q s h => ?_).mono (fun _ _ h => h) fun s₁ s₂ ⟨q, h₁, h₂⟩ => ⟨q.1, h₁, h₂⟩
  obtain ⟨⟨⟨hfx, hsi, hcx, hv⟩, ho⟩, hu⟩ := h
  obtain ⟨⟨⟨hg, hw, hw', h4, hN, hT, hX, hO⟩, hc, h10, h12⟩, h8⟩ := hfx
  have hs := hg.1.scr
  have hnw := hs.nowrap
  have hZ := hg.2
  obtain hsx := slot_le (w := q.1.L.w) (show aR2 < 8 by decide)
  obtain hsm := slot_le (w := q.1.L.w) (show aN < 8 by decide)
  obtain hsv := slot_le (w := q.1.L.w) (show aTmp < 8 by decide)
  obtain hsa := slot_le (w := q.1.L.w) (show aAcc < 8 by decide)
  obtain sXV := slot_sep (w := q.1.L.w) (show aR2 ≠ aTmp by decide)
  obtain sMV := slot_sep (w := q.1.L.w) (show aN ≠ aTmp by decide)
  obtain sAV := slot_sep (w := q.1.L.w) (show aAcc ≠ aTmp by decide)
  obtain eT : (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat = topW q.1 := by
    rw [FX.top ⟨hg, hw, hw', h4, hN, hT, hX, hO⟩, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hD _)]
  obtain hvx := recip_exact (by rw [← eT]; exact hT) (hD q.1) ho hu
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off q.1.L.B (slot q.1.L.w aTmp))
      (BitVec.ofNat 64 ((2 ^ 128 - 1) / (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat - 2 ^ 64)))
    (by
      xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs.st (show slot q.1.L.w aTmp + 8 ≤ q.1.L.Z by omega_using [hZ, hsv])]
      rw [hcx, hvx, eT]) rfl) fun t ⟨hm, k⟩ => ?_
  obtain o : Outside q.1.L.B (slot q.1.L.w aTmp) 8 s.mem t.mem := by rw [hm]; exact writeW_outside _ _ _ (by omega_using [hnw, hZ, hsv])
  obtain ha : Arrays q.1.L.B q.1.L.w [aTmp] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega_using [])
  obtain hvlt : (2 ^ 128 - 1) / (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat - 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 128 - 1) / (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega_using [hT])]; omega_using [hT]
    omega_using [this]
  obtain hT₁ : word t.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1)) =
      word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1)) := o.word (by omega_using [sMV]) (by omega_using [hnw, hZ, hsm])
  refine ⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
    by rw [o.wv (by omega_using [sMV]) (by omega_using [hnw, hZ, hsm])]; exact hN, by rw [hT₁]; exact hT,
    by rw [o.wv (by omega_using [sXV]) (by omega_using [hnw, hZ, hsx])]; exact hX, hO, by rw [o.wv (by omega_using [sAV]) (by omega_using [hnw, hZ, hsa])]; exact hc, ?_⟩
  rw [hT₁, hm, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]

/-- `fast` leaks the same in runs that agree on `m`. -/
theorem fast_ct : RelCT isa (Two R2w.FPre) fast fun _ _ => True := by
  rw [fast_eq]
  -- The loads.
  refine RelCT.seq (two_piece (Ψ := R2w.F1) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1.1
    obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.rbx, .r10, .r12, .r8, .rbp] (Q := fun t =>
        t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .r8 = off p.L.B (slot p.L.w aTmp) ∧ t.gpr .rbp = mask false ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
        hl (sArr aTmp) (by decide), hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aN (by decide), hg.1.hdr.hw,
        hg.1.hdr.harr aTmp (by decide)]) rfl)
      fun t ⟨⟨hbx, h10, h12, h8, hbp, hm⟩, k⟩ => ⟨⟨?_, h.2⟩, hbx, hbp, h8⟩
    obtain ⟨⟨hg, hw, hw', hN, hinv, -, -, hodd, hlo⟩, -⟩ := h
    exact ⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), hw, hw', hm ▸ hN, hm ▸ hinv, h12, h10, hodd, hlo⟩
  -- `R - m`.
  refine RelCT.seq (two_piece (Ψ := FX2) _ R2w.pins_F1 (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩, hT, h4⟩, hbx, hbp, h8⟩
    obtain ⟨hT', -⟩ := R2Pre.top ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    obtain hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    obtain sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    obtain hN0 : 0 < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by rw [hN]; omega_using [hodd]
    obtain hng := R2w.neg_ok hs hbx h10 h12 hbp (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hZ, hsx]) (by omega_using [hZ, hsm]) (by omega_using [sXM]) hN0
    refine WP.mono hng fun t ⟨hx, ho, k⟩ => ?_
    obtain ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
    obtain hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by omega_using [hnw, hZ]
    obtain hhalf : 2 ^ (64 * p.L.w) < 2 * p.N := by
      obtain e : p.N = wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1) +
          2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
        rw [← hN, show p.L.w = (p.L.w - 1) + 1 by omega_using [hw], wv_succ, show p.L.w - 1 + 1 - 1 = p.L.w - 1 by omega_using []]
      obtain hp : 2 ^ (64 * p.L.w) = 2 * (2 ^ (64 * (p.L.w - 1)) * 2 ^ 63) := by
        rw [← Nat.pow_add, show 64 * p.L.w = 1 + (64 * (p.L.w - 1) + 63) by omega_using [hw], Nat.pow_add, Nat.pow_one]
      rw [hT'] at e
      obtain hle := Nat.mul_le_mul_left (2 ^ (64 * (p.L.w - 1))) hT
      obtain hev : 2 ^ (64 * (p.L.w - 1)) * 2 ^ 63 % 2 = 0 := by
        rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
      omega_using [hodd, e, hp, hle]
    obtain hNR : p.N < 2 ^ (64 * p.L.w) := hN ▸ wv_lt _ _ _ _
    refine ⟨⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, by omega_using [hw, h4], hw', h4,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ho.word (by omega_using [sXM]) (by omega_using [hsm, hn']), hT']; exact hT, by rw [hx, hN], by omega_using [hhalf, hNR]⟩,
      (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `mc`'s bases.
  refine RelCT.seq (two_piece (Ψ := FX3) _ pins_FX2 (by taint_decide) ?_) ?_
  · rintro p s ⟨hx, hbx, h10, h12⟩
    have hg := hx.1
    obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧
        t.gpr .rbx = off p.L.B (slot p.L.w aAcc) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aAcc) (by decide), hg.1.hdr.harr aAcc (by decide), hbx]) rfl)
      fun t ⟨⟨h8, hb, hm⟩, k⟩ => ⟨FX.congr hx hm k.2.2 (k.gpr (by decide)), h8, hb,
        (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `mc := x`.
  refine RelCT.seq (two_post (Ψ := FXA) (two_taint _ pins_FX3 (by taint_decide)) ?_) ?_
  · rintro p s ⟨hx, h8, hbx, h10, h12⟩
    have hx' := hx
    obtain ⟨hg, hw, hw', h4, hN, hT, hX, hO⟩ := hx'
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    obtain hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    obtain hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    obtain hsa := slot_le (w := p.L.w) (show aAcc < 8 by decide)
    obtain sXA := slot_sep (w := p.L.w) (show aR2 ≠ aAcc by decide)
    obtain sMA := slot_sep (w := p.L.w) (show aN ≠ aAcc by decide)
    unfold R2Words.copyBack
    refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off p.L.B (slot p.L.w aR2) ∧ t.mem = s.mem)
      (by xrun [h8]) rfl) fun t₁ ⟨⟨hsi, hm₁⟩, k₁⟩ => ?_)
    obtain hs₁ := hs.congr k₁.2.2
    obtain hsepw : ∀ j < p.L.w, ∀ b < 8, ofs p.L.B (off p.L.B (slot p.L.w aR2 + 8 * j) + BitVec.ofNat 64 b) <
        slot p.L.w aAcc ∨ slot p.L.w aAcc + 8 * p.L.w ≤ ofs p.L.B (off p.L.B (slot p.L.w aR2 + 8 * j) +
          BitVec.ofNat 64 b) := fun j hj b hb => by
      rw [ofs_off p.L.B (by omega_using [hnw, hZ, hsx, hj, hb])]; omega_using [sXA, hj, hb]
    refine WP.mono (copyWords_ok (S := p.L.B) (D := p.L.B) hsi ((k₁.gpr (by decide)).trans hbx)
      ((k₁.gpr (by decide)).trans h12) (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hnw, hZ, hsa]) (fun j hj => hs₁.ld (by omega_using [hZ, hsx, hj]))
      (fun j hj => hs₁.st (by omega_using [hZ, hsa, hj])) hsepw) fun t ⟨hc, _, ho, k⟩ => ?_
    rw [hm₁] at hc ho
    obtain ha : Arrays p.L.B p.L.w [aAcc] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
    obtain kk := k₁.trans k
    obtain hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by omega_using [hnw, hZ]
    obtain hNR : p.N < 2 ^ (64 * p.L.w) := hN ▸ wv_lt _ _ _ _
    refine ⟨⟨⟨⟨hs.congr (k.2.2.trans k₁.2.2), (kk.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ho.word (by omega_using [sMA]) (by omega_using [hsm, hn'])]; exact hT,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hX, hO⟩,
      by rw [hc, hX]; omega_using [hNR], (kk.gpr (by decide)).trans h10, (kk.gpr (by decide)).trans h12⟩
  -- `v`'s bases.
  refine RelCT.seq (two_piece (Ψ := FX5) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨hx, hc, h10, h12⟩
    have hg := hx.1
    obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.rbx, .r8] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aTmp) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide),
        hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aTmp (by decide)]) rfl)
      fun t ⟨⟨h8, hm⟩, k⟩ => ⟨⟨FX.congr hx hm k.2.2 (k.gpr (by decide)), hm ▸ hc, (k.gpr (by decide)).trans h10,
        (k.gpr (by decide)).trans h12⟩, h8⟩
  -- `v`.
  refine RelCT.seq recipN_ct ?_
  -- The count.
  refine RelCT.seq (two_piece (Ψ := fun p s => FX6 p s ∧ s.gpr .rcx = BitVec.ofNat 64 p.L.w) _
    (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1
    obtain hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 p.L.w ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl sW (by decide), hg.1.hdr.hw]) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨?_, hcx⟩
    obtain ⟨hg, hw, hw', h4, hN, hT, hX, hO, hc, hv⟩ := h
    exact ⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), hw, hw', h4, hm ▸ hN, hm ▸ hT, hm ▸ hX, hO, hm ▸ hc, hm ▸ hv⟩
  -- The steps.
  refine (two_map (fun p : R2Pub => (⟨p.L, p.L.w, p.N⟩ : StPub)) (fun p s h => ?_) steps_ct).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨⟨hg, hw, hw', h4, hN, hT, hX, hO, hc, hv⟩, hcx⟩ := h
  exact ⟨hg, hw, h4, hw', show 1 ≤ p.L.w by omega_using [hw], show p.L.w < 2 ^ 31 by omega_using [hw'], hcx, hT, hv, hX, hN, hO, hc⟩

/-! ## The choice -/

/-- `choice` leaks the same in runs that agree on `m`. -/
theorem choice_ct (M : Mont) : RelCT isa (Two R2Pre) (R2Adx.choice M.mm) fun _ _ => True := by
  unfold R2Adx.choice
  refine RelCT.seq (two_piece (Ψ := R2w.R2t) _ pins_r2Pre (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hT, -⟩ := h.top
    have hn := h.1.1.scr.nowrap
    have := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (2 ^ 63 ≤ p.top ∧ p.L.w % 4 = 0)) ∧
        t.mem = s.mem) (by
      unfold R2Words.fastTest
      xrun [State.ea, ix, addrm8 h.2.2.2.2.2.2.1 h.2.2.2.2.2.1 (by have := h.2.1; omega_arith),
        h.1.1.scr.ld (show slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega_arith)]
      rw [h.2.2.2.2.2.1]
      refine (R2w.fastFlag _ (by have := h.2.2.1; omega_arith)).trans ?_
      rw [← hT]) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨?_, hz⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map id (fun p s ⟨⟨h, hz⟩, hc⟩ => by
      simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at hc
      exact ⟨h, hc.1, hc.2⟩) fast_ct
  · rw [R2w.old_eq]
    exact two_map id (fun p s h => h.1.1) (r2_ct_with _ (rolled_sqs_ct M 5 (Or.inr rfl)))

end VG.Proof.Bignum.X86_64.R2ax

end

end

/-!
# Computations of `R² mod m` on x86-64

What the functions that compute `R² mod m` use of the code that does
(`R2Impl`): its result (`r2_ok`'s, as `R2w.choice_ok` states it) and that it
leaks only `m` (`R2w.choice_ct`). `R2Words.choice` (`R2Impl.words`) and, with
ADX, `R2Adx.choice` (`R2Impl.adx`) do.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- Code computing `R² mod m` into `aR2`, with Montgomery multiplication `M`. -/
structure R2Impl (M : Mont) where
  code : Prog isa
  ok : ∀ {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat},
    Good s B Z w minv → slot w 8 ≤ Z → 2 ≤ w → w < 2 ^ 30 → wv s.mem B (slot w aN) w = N →
    ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 →
    s.gpr .r12 = BitVec.ofNat 64 w → s.gpr .r10 = off B (slot w aN) → N % 2 = 1 → 2 ^ (64 * (w - 1)) ≤ N →
    WP isa code s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t
  ct : RelCT isa (Two R2Pre) code fun _ _ => True

/-- By word steps and two squarings, or doublings and squarings. -/
def R2Impl.words (M : Mont) : R2Impl M :=
  ⟨R2Words.choice M.mm, R2w.choice_ok M, R2w.choice_ct M⟩

/-- By `w` word steps with ADX, or doublings and squarings. -/
def R2Impl.adx (M : Mont) : R2Impl M :=
  ⟨R2Adx.choice M.mm, R2ax.choice_ok M, R2ax.choice_ct M⟩

end VG.Proof.Bignum.X86_64
