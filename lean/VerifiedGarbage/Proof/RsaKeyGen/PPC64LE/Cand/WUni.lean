module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Witness
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Bits
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Copy
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Close
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: whether a draw is at least 2

`atLeast2_ok`: `r21 := 1` if the draw `x` in array 4 is at least 2, else 0,
from `x₀ >> 1` or'ed with its other words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (atLeast2 toThree uniform)
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)
open VG.Proof.MillerRabin.PPC64LE (Env)

/-- Whether a word is zero, as a flag: `((a & 1) | (a >> 1)) − 1`'s top bit,
inverted. -/
theorem flag_ne0 (a : BitVec 64) :
    (((a &&& BitVec.ofNat 64 1) ||| a >>> 1) - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (if a = 0 then 0 else 1) := by
  have ha := a.isLt
  have e1 : (a &&& BitVec.ofNat 64 1).toNat = a.toNat % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_comm, Nat.one_and_eq_mod_two]
  have e2 : (a >>> 1).toNat = a.toNat / 2 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb : ((a &&& BitVec.ofNat 64 1) ||| a >>> 1).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_or, e1, e2]; exact Nat.or_lt_two_pow (by omega) (by omega)
  have hz : ((a &&& BitVec.ofNat 64 1) ||| a >>> 1) = 0 ↔ a = 0 := by
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_or, e1, e2, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at h'
      exact BitVec.eq_of_toNat_eq (by simp; omega)
    · intro h; subst h; decide
  generalize ((a &&& BitVec.ofNat 64 1) ||| a >>> 1) = b at hb hz
  have hb' : b = BitVec.ofNat 64 b.toNat := by simp
  rw [hb', borrow63_val hb (show 1 < 2 ^ 63 by decide)]
  by_cases h : a = 0
  · have : b.toNat = 0 := by rw [hz.mpr h]; rfl
    rw [ite_eq_left (by omega), ite_eq_left h]; decide
  · have : b.toNat ≠ 0 := fun e => h (hz.mp (BitVec.eq_of_toNat_eq (by rw [e]; rfl)))
    rw [ite_eq_right (by omega), ite_eq_right h]; decide

theorem or_eq_zero (a b : BitVec 64) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_or, show (0 : BitVec 64).toNat = 0 from rfl, Nat.or_eq_zero_iff] at h'
    exact ⟨BitVec.eq_of_toNat_eq h'.1, BitVec.eq_of_toNat_eq h'.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem shr1_eq_zero (a : BitVec 64) : a >>> 1 = 0 ↔ a &&& (BitVec.allOnes 64 - 1) = 0 := by
  rw [VG.Proof.RsaKeyGen.and_m2_eq_zero]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h'
    simp at h'; omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp; omega

/-- `atLeast2`: `r21 := 1` if array 4 holds at least 2, else 0. -/
theorem atLeast2_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa atLeast2 s fun t =>
      (t.gpr .r21 = BitVec.ofNat 64 (if 2 ≤ wv s.mem B (slot w 4) w then 1 else 0) ∧ t.mem = s.mem ∧
        Env t B Z w) ∧ Keep [.r0, .r3, .r5, .r6, .r21] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  have s4 : slot w 4 + 8 * w ≤ Z := by rw [slot_lin]; omega
  unfold atLeast2
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r5) (by decide) (by decide) 4) fun t₁ ⟨⟨a5, m₁⟩, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  refine WP.mono (WP.keep [.r5, .r6, .r21] (Q := fun t => t.gpr .r21 = word s.mem B (slot w 4) >>> 1 ∧
      t.gpr .r5 = off B (slot w 4 + 8 * 1) ∧ t.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ?_ (by decide))
    fun t₂ ⟨⟨b21, b5, b6, m₂⟩, k₂⟩ => ?_
  · have h11 : t₁.gpr .r11 = BitVec.ofNat 64 (2 * w) := (k₁.gpr _ (by decide)).trans h.h11
    have e6 : BitVec.ofNat 64 (2 * w) >>> 1 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (w - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      omega
    prun [a5, h11, e6, hs₁.ld (d := slot w 4) (n := 8) (by omega), m₁]
  have k12 := k₁.trans k₂
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r21 = 0 ↔ (word s.mem B (slot w 4) >>> 1 = 0 ∧
        ∀ j, 1 ≤ j → j ≤ i → word s.mem B (slot w 4 + 8 * j) = 0)) ∧
      t.gpr .r5 = off B (slot w 4 + 8 * (i + 1)) ∧ t.mem = s.mem ∧ Keep [.r0, .r3, .r5, .r6, .r21] s t
  refine WP.seq (WP.mono (wp_countdown (body := .block ([.load .d .r3 .r5 0, .logic .or .r21 .r21 .r3,
      .addi .r5 .r5 8] ++ ([.subi .r6 .r6 1] : List Instr))) (cnt := .r6) (N := w - 1) (by omega) (by omega) Inv
    (fun i hi t ⟨tz, t5, tm, tk⟩ _ => ?_)
    ⟨by rw [b21]; exact ⟨fun e => ⟨e, fun j h1 h2 => absurd h2 (by omega)⟩, fun e => e.1⟩, b5, m₂, k12.mono⟩ b6)
    fun t ⟨tz, _, tm, tk⟩ => ?_)
  · have hst : WP isa (.block [.load .d .r3 .r5 0, .logic .or .r21 .r21 .r3, .addi .r5 .r5 8, .subi .r6 .r6 1]) t
        fun t' => (t'.gpr .r21 = t.gpr .r21 ||| word s.mem B (slot w 4 + 8 * (i + 1)) ∧
          t'.gpr .r5 = off B (slot w 4 + 8 * (i + 1 + 1)) ∧ t'.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1 ∧
          t'.mem = t.mem) ∧ Keep [.r3, .r5, .r6, .r21] t t' := by
      refine WP.keep _ ?_ (by decide)
      prun [t5, (hs.congr tk.wr).ld (d := slot w 4 + 8 * (i + 1)) (n := 8) (by omega), tm]
      rw [show slot w 4 + 8 * (i + 1) + 8 = slot w 4 + 8 * (i + 1 + 1) by omega]
    refine WP.mono hst fun t' ⟨⟨u21, u5, u6, um⟩, uk⟩ => ⟨⟨?_, u5, um.trans tm, tk.trans' uk.mono⟩, u6⟩
    rw [u21, or_eq_zero, tz]
    constructor
    · rintro ⟨⟨e0, ej⟩, ei⟩
      refine ⟨e0, fun j h1 h2 => ?_⟩
      rcases Nat.lt_or_ge j (i + 1) with hj | hj
      · exact ej j h1 (by omega)
      · rw [show j = i + 1 by omega]; exact ei
    · rintro ⟨e0, ej⟩
      exact ⟨⟨e0, fun j h1 h2 => ej j h1 (by omega)⟩, ej (i + 1) (by omega) (Nat.le_refl _)⟩
  · refine WP.mono (WP.keep [.r0, .r3, .r21] (Q := fun u => u.gpr .r21 =
        (((t.gpr .r21 &&& BitVec.ofNat 64 1) ||| t.gpr .r21 >>> 1) - BitVec.ofNat 64 1) >>> 63 ^^^ BitVec.ofNat 64 1 ∧
        u.mem = t.mem) (by prun []) (by decide)) fun u ⟨⟨u21, um⟩, ku⟩ => ?_
    have K := tk.trans ku
    refine ⟨⟨?_, um.trans tm, h.keep K (by decide)⟩, K.mono (by simp)⟩
    rw [u21, flag_ne0]
    have hle := VG.Proof.RsaKeyGen.wv_le_one (m := s.mem) (p := B) (d := slot w 4) (w := w) (by omega)
    rw [← shr1_eq_zero] at hle
    have e : (t.gpr .r21 = 0) ↔ wv s.mem B (slot w 4) w ≤ 1 := by
      rw [tz, hle]
      exact ⟨fun ⟨a, b⟩ => ⟨a, fun i h1 h2 => b i h1 (by omega)⟩, fun ⟨a, b⟩ => ⟨a, fun j h1 h2 => b j h1 (by omega)⟩⟩
    by_cases hz : t.gpr .r21 = 0
    · rw [ite_eq_left hz, ite_eq_right (by have := e.mp hz; omega)]
    · rw [ite_eq_right hz, ite_eq_left (by have := mt e.mpr hz; omega)]

/-- `toThree`: array 4's `w` words into array 3, and its word `w` := 0. -/
theorem toThree_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) :
    WP isa toThree s fun t =>
      ((∀ i < w, word t.mem B (slot w 3 + 8 * i) = word s.mem B (slot w 4 + 8 * i)) ∧
        word t.mem B (slot w 3 + 8 * w) = 0 ∧ Outside B (slot w 3) (8 * w + 8) s.mem t.mem ∧ Env t B Z w) ∧
        Keep [.r0, .r5, .r6, .r14, .r15, .r17] s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h.hZ
  rw [slot_lin] at hZ
  unfold toThree
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (h.base (rd := .r14) (by decide) (by decide) 3) fun t₁ ⟨⟨a14, m₁⟩, k₁⟩ => ?_
  have e₁ := h.keep k₁ (by decide)
  refine WP.mono (e₁.base (rd := .r15) (by decide) (by decide) 4) fun t₂ ⟨⟨a15, m₂⟩, k₂⟩ => ?_
  have e₂ := e₁.keep k₂ (by decide)
  refine WP.seq (WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.copyWithin_ok e₂.hs (dS := slot w 4) (dD := slot w 3)
    a15 (by rw [k₂.gpr _ (by decide), a14]) e₂.h11 (by omega) (by omega) (by rw [slot_lin]; omega)
    (by rw [slot_lin]; omega) (by rw [slot_lin, slot_lin]; omega)) fun t₃ ⟨⟨_, hc, o₃⟩, k₃⟩ => ?_)
  have e₃ := e₂.keep k₃ (by decide)
  have hm2 : t₂.mem = s.mem := by rw [m₂, m₁]
  rw [WP.block_append_iff]
  refine WP.mono (e₃.base (rd := .r5) (by decide) (by decide) 3) fun t₄ ⟨⟨a5, m₄⟩, k₄⟩ => ?_
  have e₄ := e₃.keep k₄ (by decide)
  have e8 : off B (slot w 3) + BitVec.ofNat 64 (2 * w) <<< 2 = off B (slot w 3 + 8 * w) := by
    rw [show BitVec.ofNat 64 (2 * w) <<< 2 = BitVec.ofNat 64 (8 * w) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      omega, off_add]
  refine WP.mono (WP.keep [.r0, .r5, .r6] (Q := fun t => t.mem = t₄.mem.writeW (off B (slot w 3 + 8 * w)) (0 : BitVec 64))
    (by prun [a5, e₄.h11, e8, e₄.hs.st (d := slot w 3 + 8 * w) (n := 8) (by rw [slot_lin]; omega)]; rfl)
    (by decide)) fun t ⟨tm, kt⟩ => ?_
  have K := (((k₁.trans k₂).trans k₃).trans k₄).trans kt
  have wo := writeW_outside t₄.mem B (d := slot w 3 + 8 * w) (0 : BitVec 64) (by rw [slot_lin]; omega)
  refine ⟨⟨fun i hi => ?_, ?_, ?_, e₄.keep kt (by decide)⟩, K.mono (by simp)⟩
  · rw [tm, wo.word (by omega) (by rw [slot_lin]; omega), m₄, hc i hi, hm2]
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm, ← hm2, m₄]
    rw [m₄] at wo
    exact (o₃.mono (o' := slot w 3) (n' := 8 * w + 8) (Nat.le_refl _) (by omega)).trans
      (wo.mono (o' := slot w 3) (n' := 8 * w + 8) (by omega) (by omega))

theorem or1_nat (a : Nat) : a ||| 1 = a + (1 - a % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  rcases i with _ | i
  · simp [Nat.testBit_zero]; omega
  · rw [Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    simp
    congr 1; omega

theorem mask_and1 (b : Nat) (hb : b ≤ 1) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 b) &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 b := by
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

/-- The registers `uniform` writes. -/
def uniRegs : List Reg := [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r21]

/-- `uniform`: `r21 := 1` if the draw `x` in array 4 is a uniform witness for
`c` in array 0 (`2 ≤ x < c − 1`, as `x + (1 − x mod 2) < c`), else 0. -/
theorem uniform_ok {s : State} {B : Addr} {Z w c : Nat} (h : Env s B Z w) (h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ Z)
    (hc : wv s.mem B (slot w 0) w = c) (hcR : c < 2 ^ (64 * w)) :
    WP isa uniform s fun t =>
      (t.gpr .r21 = BitVec.ofNat 64 (if 2 ≤ wv s.mem B (slot w 4) w ∧
          wv s.mem B (slot w 4) w + (1 - wv s.mem B (slot w 4) w % 2) < c then 1 else 0) ∧
        Env t B Z w ∧ VG.Proof.Mont.Outs B [(slot w 3, 8 * w + 8), (slot w 6, 8 * w)] s.mem t.mem) ∧ Keep uniRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hw4 := h.hw
  have hw128 := h.hw'
  have hZ := h35
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr] at hZ
  rw [slot_lin] at hZ
  generalize hx : wv s.mem B (slot w 4) w = x
  unfold uniform
  refine WP.seq (WP.mono (atLeast2_ok h) fun t₁ ⟨⟨a21, m₁, e₁⟩, k₁⟩ => ?_)
  rw [hx] at a21
  refine WP.seq (WP.mono (toThree_ok e₁) fun t₂ ⟨⟨c3, z3, o₂, e₂⟩, k₂⟩ => ?_)
  rw [m₁] at c3 o₂
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (e₂.base (rd := .r5) (by decide) (by decide) 3) fun t₃ ⟨⟨a5, m₃⟩, k₃⟩ => ?_
  have e₃ := e₂.keep k₃ (by decide)
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.mem = t₃.mem.writeW (off B (slot w 3))
      (word t₃.mem B (slot w 3) ||| BitVec.ofNat 64 1) ∧ t.gpr .r5 = t₃.gpr .r5) (by
    prun [a5, e₃.hs.ld (d := slot w 3) (n := 8) (by rw [slot_lin]; omega),
      e₃.hs.st (d := slot w 3) (n := 8) (by rw [slot_lin]; omega)]) (by decide)) fun t₄ ⟨⟨m₄, _⟩, k₄⟩ => ?_
  have e₄ := e₃.keep k₄ (by decide)
  refine WP.mono (e₄.base (rd := .r8) (by decide) (by decide) 3) fun t₅ ⟨⟨a8, m₅⟩, k₅⟩ => ?_
  have e₅ := e₄.keep k₅ (by decide)
  refine WP.mono (e₅.base (rd := .r9) (by decide) (by decide) 6) fun t₆ ⟨⟨a9, m₆⟩, k₆⟩ => ?_
  have e₆ := e₅.keep k₆ (by decide)
  have hm6 : t₆.mem = t₄.mem := by rw [m₆, m₅]
  have k16 := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆)
  -- The numbers subtracted.
  have w0 : word t₃.mem B (slot w 3) = word s.mem B (slot w 4) := by
    rw [m₃]; have := c3 0 (by omega); simpa using this
  have hA : wv t₆.mem B (slot w 3) w = x + (1 - x % 2) := by
    rw [hm6, m₄, wv_low _ _ _ _ (by omega), word_writeW_self, w0]
    have hrest : wv (t₃.mem.writeW (off B (slot w 3)) (word s.mem B (slot w 4) ||| BitVec.ofNat 64 1)) B
        (slot w 3 + 8) (w - 1) = wv s.mem B (slot w 4 + 8) (w - 1) := by
      apply wv_shift'; intro i hi
      rw [(writeW_outside t₃.mem B (d := slot w 3) _ (by rw [slot_lin]; omega)).word (by omega)
        (by rw [slot_lin]; omega), m₃,
        show slot w 3 + 8 + 8 * i = slot w 3 + 8 * (i + 1) by omega,
        show slot w 4 + 8 + 8 * i = slot w 4 + 8 * (i + 1) by omega]
      exact c3 (i + 1) (by omega)
    rw [hrest]
    have hx' := wv_low s.mem B (slot w 4) w (by omega)
    rw [hx] at hx'
    rw [BitVec.toNat_or, show (BitVec.ofNat 64 1).toNat = 1 from rfl, or1_nat]
    have : (word s.mem B (slot w 4)).toNat % 2 = x % 2 := by omega
    omega
  have zA : VG.Proof.Mont.w32 t₆.mem B (slot w 3 + 4 * (2 * w)) = 0 := by
    have e := VG.Proof.Mont.word_eq_w32 t₆.mem B (slot w 3 + 8 * w)
    have z : VG.Proof.Mont.word t₆.mem B (slot w 3 + 8 * w) = 0 := by
      show t₆.mem.readW _ 64 = 0
      rw [hm6, m₄, Mem.readW_writeW_sep (Offset.sep B (by omega) (by rw [slot_lin]; omega)
        (by rw [slot_lin]; omega)) (by decide), m₃]
      exact z3
    have z' : (VG.Proof.Mont.word t₆.mem B (slot w 3 + 8 * w)).toNat = 0 := by rw [z]; rfl
    rw [show slot w 3 + 4 * (2 * w) = slot w 3 + 8 * w by omega]
    omega
  have hM : wv t₆.mem B (slot w 0) w = c := by
    rw [← hc, hm6, m₄, ← Pre.val32_eq_wv, ← Pre.val32_eq_wv]
    rw [(VG.Proof.Mont.writeW_outside t₃.mem B (d := slot w 3) _ (by rw [slot_lin]; omega)).val32 (by rw [slot_lin, slot_lin]; omega)
      (by rw [slot_lin]; omega), m₃, VG.Proof.Mont.Outside.val32 o₂ (by rw [slot_lin, slot_lin]; omega)
      (by rw [slot_lin]; omega)]
  refine WP.seq (WP.mono (subMod_ok e₆.hs (dA := slot w 3) (dT := slot w 6) (dM := slot w 0) (n := 2 * w)
    (by rw [k₆.gpr _ (by decide), a8]) a9 e₆.h10 e₆.h11 (by omega) (by omega) (by rw [slot_lin]; omega)
    (by rw [slot_lin]; omega) (by rw [slot_lin]; omega) (by rw [slot_lin, slot_lin]; omega)
    (by rw [slot_lin, slot_lin]; omega)) fun t₇ ⟨⟨b, hb, v₇, r₇⟩, o₇, k₇⟩ => ?_)
  rw [zA] at r₇
  simp only [Pre.val32_eq_wv] at v₇
  rw [hA, hM, show 32 * (2 * w) = 64 * w by omega] at v₇
  refine WP.mono (WP.keep [.r0, .r3, .r21] (Q := fun t => t.gpr .r21 = t₇.gpr .r21 &&& (t₇.gpr .r20 &&&
      BitVec.ofNat 64 1) ∧ t.mem = t₇.mem) (by prun []) (by decide)) fun t ⟨⟨t21, tm⟩, kt⟩ => ?_
  have K := (k16.trans k₇).trans kt
  have hD := VG.Proof.Mont.val32_lt t₇.mem B (slot w 6) (2 * w)
  rw [Pre.val32_eq_wv, show 32 * (2 * w) = 64 * w by omega] at hD
  have bi := (borrow_iff hb v₇ hD hcR).1
  refine ⟨⟨?_, ⟨hs.congr K.wr, ?_, ?_, ?_, ?_, hw4, hw128, h.hZ⟩, ?_⟩, K.mono (by simp [uniRegs])⟩
  · have r21₇ : t₇.gpr .r21 = t₁.gpr .r21 :=
      ((((((k₂.trans k₃).trans k₄).trans k₅).trans k₆).trans k₇).gpr .r21 (by decide))
    rw [t21, r₇, show (if 0 < b then 1 else 0) = b by rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl,
      mask_and1 b hb, r21₇, a21]
    by_cases h2 : 2 ≤ x
    · rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · rw [ite_eq_left h2, ite_eq_right (fun hh => absurd (bi.mpr hh.2) (by decide))]; decide
      · rw [ite_eq_left h2, ite_eq_left ⟨h2, bi.mp rfl⟩]; decide
    · rw [ite_eq_right h2, ite_eq_right (fun hh => h2 hh.1)]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide
  · rw [K.gpr _ (by decide)]; exact h.h10
  · rw [K.gpr _ (by decide)]; exact h.h29
  · rw [K.gpr _ (by decide)]; exact h.h11
  · rw [K.gpr _ (by decide)]; exact h.h31
  · intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hy
    rw [tm, o₇ y (by omega), hm6, m₄, VG.Proof.Mont.writeW_outside t₃.mem B (d := slot w 3) _
      (by rw [slot_lin]; omega) y (by omega), m₃, o₂ y hy.1]

end VG.Proof.RsaKeyGen.PPC64LE.Cand
