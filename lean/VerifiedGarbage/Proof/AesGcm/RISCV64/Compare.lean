module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesGcm.RISCV64.Absorb
import VerifiedGarbage.Proof.AesGcm.RISCV64.Flush
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-GCM on RISCV64: checking a received tag (`tagLenOk`, `recv`, `cmp`)

Untrusted: everything here is checked by Lean. As on ARMv7
(`Proof/AesGcm/Arm/Compare.lean`): `tagLenOk` leaves 1 in `r25` iff
`tagLenOk` allows a tag of `r19` bytes, and 0 if not, branching on that
public length (`tagLenOk_ok`); `recv` and `cmp o` copy the received tag (at
`r20`) and the computed one (at `W + o`), `r19` bytes of each, padded with
zeros, to `W + rO` and `W + vO` (`recv_ok`, `cmp_ok`), and `cmpTail` sets
`r3` to 1 if they are equal and 0 if not, without a branch (`cmpTail_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le8)

/-! ## Arithmetic -/

theorem shr63' (y : BitVec 64) : (y >>> 63).toNat = if y.msb then 1 else 0 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.msb_eq_decide]
  have := y.isLt
  by_cases h : 2 ^ (64 - 1) ≤ y.toNat
  · rw [decide_eq_true h]; simp only [ite_true]; simp only [Nat.reduceSub] at h; omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]; simp only [Nat.reduceSub] at h; omega

theorem msb_or_neg64 (x : BitVec 64) : (x ||| (0 - x)) >>> 63 = if x = 0 then 0 else 1 := by
  apply BitVec.eq_of_toNat_eq
  have z0 : (0 : BitVec 64).toNat = 0 := rfl
  rw [shr63', BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide (x := 0 - x), BitVec.toNat_sub, z0,
    Nat.add_zero]
  have := x.isLt
  by_cases h : x = 0
  · subst h; decide
  · have hx : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    have : 2 ^ (64 - 1) ≤ x.toNat ∨ 2 ^ (64 - 1) ≤ (2 ^ 64 - x.toNat) % 2 ^ 64 := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp only [h, ite_false, Bool.or_eq_true, decide_eq_true_eq]
    simp only [this, ite_true]; rfl

/-- `1 - ((x | -x) >> 63)`: 1 iff `x` is 0. -/
theorem cmp_value (x : BitVec 64) :
    BitVec.ofNat 64 1 - ((x ||| (BitVec.ofNat 64 0 - x)) >>> 63) = if x = 0 then 1 else 0 := by
  rw [show BitVec.ofNat 64 0 = 0 from rfl, msb_or_neg64]
  by_cases h : x = 0
  · simp [h]
  · simp only [h, ite_false]; rfl

theorem shrK {n : Nat} (hn : n < 2 ^ 64) (k : Nat) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by have := Nat.div_le_self n (2 ^ k); omega)]

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e := congrArg (fun l => (l.getD (i / 8) 0).getLsbD (i % 8)) h
  simp only [Proof.Cmac.getD_le8 _ (show i / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, show 8 * (i / 8) + i % 8 = i by omega] at e
  exact e

/-- Two blocks are equal iff the OR of the XORs of their words is 0. -/
theorem words_eq (m : Mem) (p q : Addr) :
    ((m.readW p 64 ^^^ m.readW q 64) ||| (m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64)
      = 0) ↔ bytesAt m p 16 = bytesAt m q 16 := by
  rw [Proof.Cmac.bytesAt_split m p, Proof.Cmac.bytesAt_split m q, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW]
  constructor
  · intro h
    have h₁ : m.readW p 64 ^^^ m.readW q 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or] at this ⊢
      simp_all
    have h₂ : m.readW (p + BitVec.ofNat 64 8) 64 ^^^ m.readW (q + BitVec.ofNat 64 8) 64 = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := congrArg (·.getLsbD i) h; simp only [BitVec.getLsbD_or] at this ⊢
      simp_all
    rw [BitVec.xor_eq_zero_iff.mp h₁, BitVec.xor_eq_zero_iff.mp h₂]
  · intro h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [Proof.Cmac.length_le8, Proof.Cmac.length_le8])
    rw [le8_inj h₁, le8_inj h₂, BitVec.xor_self, BitVec.xor_self]; rfl

/-- `xs` written over 16 zero bytes at `P`. -/
theorem pad_bytes {m : Mem} {P : Addr} (hz : bytesAt m P 16 = zeros 16) (xs : List Byte) (hx : xs.length ≤ 16) :
    bytesAt (writeBytes m P xs) P 16 = xs ++ zeros (16 - xs.length) := by
  rw [bytesAt_writeBytes_prefix _ _ _ hx (by decide)]
  congr 1
  rw [show (16 : Nat) = xs.length + (16 - xs.length) by omega, bytesAt_add] at hz
  have e := congrArg (List.drop xs.length) hz
  rw [List.drop_left' (length_bytesAt _ _ _)] at e
  rw [e, show xs.length + (16 - xs.length) = 16 by omega, zeros, List.drop_replicate]
  rfl

/-! ## The length -/

/-- `tagLenOk`: `r25` is 1 iff the tag length is allowed. -/
theorem tagLenOk_ok {s : State} {t : Nat} (h19 : s.gpr .s8 = BitVec.ofNat 64 t) (ht : t < 2 ^ 64) :
    WP isa tagLenOk s fun s' => s'.gpr .s5 = BitVec.ofNat 64 (if Spec.Gcm.tagLenOk t then 1 else 0) ∧
      (∀ r, r ≠ .t0 → r ≠ .s5 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have s2 := shrK ht 2
  have s4 := shrK ht 4
  have d4 : t / 2 ^ 2 < 2 ^ 64 := by omega
  have d16 : t / 2 ^ 4 < 2 ^ 64 := by omega
  have h₁ : WP isa (.block [.li .s5 0, .lsr .d .t0 .s8 2]) s fun s₁ =>
      s₁.gpr .s5 = BitVec.ofNat 64 0 ∧ s₁.gpr .t0 = BitVec.ofNat 64 (t / 2 ^ 2) ∧
        (∀ r, r ≠ .t0 → r ≠ .s5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    crun [Int.reduceNatCast', h19, s2]
    exact ⟨fun r a b => by simp [a, b], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨a25, a0, g₁, k₁⟩ => ?_)
  refine WP.ite (decide (t / 2 ^ 2 = 0)) (eval_zero a0 d4) (fun e => ?_) (fun e => ?_)
  · have : Spec.Gcm.tagLenOk t = false := by simp [Spec.Gcm.tagLenOk]; simp at e; omega
    exact WP.block_nil ⟨by rw [a25, this]; rfl, g₁, k₁⟩
  have e19 : s₁.gpr .s8 = BitVec.ofNat 64 t := by rw [g₁ _ (by decide) (by decide), h19]
  have h₂ : WP isa (.block [.lsr .d .t0 .s8 4]) s₁ fun s₂ =>
      s₂.gpr .t0 = BitVec.ofNat 64 (t / 2 ^ 4) ∧ (∀ r, r ≠ .t0 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    crun [Int.reduceNatCast', e19, s4]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₂ fun s₂ ⟨b0, g₂, k₂⟩ => ?_)
  have k₁₂ := k₁.trans k₂
  have g₁₂ : ∀ r, r ≠ .t0 → r ≠ .s5 → s₂.gpr r = s.gpr r := fun r a b => by rw [g₂ r a, g₁ r a b]
  refine WP.ite (decide (t / 2 ^ 4 = 0)) (eval_zero b0 d16) (fun e' => ?_) (fun e' => ?_)
  · have : Spec.Gcm.tagLenOk t = true := by simp [Spec.Gcm.tagLenOk]; simp at e e'; omega
    rw [this]
    crun [Int.reduceNatCast', ]
    exact ⟨fun r a b => by simp [b, g₁₂ r a b], k₁₂.trans ⟨rfl, rfl, rfl, rfl⟩⟩
  have e19' : s₂.gpr .s8 = BitVec.ofNat 64 t := by rw [g₂ _ (by decide), e19]
  have h16 : 16 ≤ t := by simp at e'; omega
  have hsub : BitVec.ofNat 64 t - BitVec.ofNat 64 16 = BitVec.ofNat 64 (t - 16) := ofNat_sub64 h16 ht
  have h₃ : WP isa (.block [.subi .t0 .s8 16]) s₂ fun s₃ =>
      s₃.gpr .t0 = BitVec.ofNat 64 (t - 16) ∧ (∀ r, r ≠ .t0 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    crun [Int.reduceNatCast', e19', hsub]
    exact ⟨fun r a => by simp [a], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₃ fun s₃ ⟨c0, g₃, k₃⟩ => ?_)
  have k₁₃ := k₁₂.trans k₃
  have g₁₃ : ∀ r, r ≠ .t0 → r ≠ .s5 → s₃.gpr r = s.gpr r := fun r a b => by rw [g₃ r a, g₁₂ r a b]
  refine WP.ite (decide (t - 16 = 0)) (eval_zero c0 (by omega)) (fun e'' => ?_) (fun e'' => ?_)
  · have : Spec.Gcm.tagLenOk t = true := by simp [Spec.Gcm.tagLenOk]; simp at e''; omega
    rw [this]
    crun [Int.reduceNatCast', ]
    exact ⟨fun r a b => by simp [b, g₁₃ r a b], k₁₃.trans ⟨rfl, rfl, rfl, rfl⟩⟩
  · have : Spec.Gcm.tagLenOk t = false := by simp [Spec.Gcm.tagLenOk]; simp at e''; omega
    refine WP.block_nil ⟨?_, g₁₃, k₁₃⟩
    rw [g₃ _ (by decide), g₂ _ (by decide), a25, this]; rfl

/-! ## Padded tags -/

section
variable {V : Reg → BitVec 64} {sp : Addr}

/-- A copy of `tl` bytes from `S` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {s : State} (he : Env V sp s) {S : Addr} {d tl : Nat} (hd : d + 16 ≤ 2560) (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (hSr : Covers [⟨S, tl⟩] (s.rd ++ s.wr))
    (hSd : (⟨S, tl⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 d, 16⟩)
    (hz : bytesAt s.mem (V .s0 + BitVec.ofNat 64 d) 16 = zeros 16) (hr3 : s.gpr .a0 = S)
    (hr4 : s.gpr .a1 = V .s0 + BitVec.ofNat 64 d) (hr5 : s.gpr .a2 = BitVec.ofNat 64 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (V .s0 + BitVec.ofNat 64 d) 16 =
        bytesAt s.mem S tl ++ zeros (16 - tl) ∧
      Frame [⟨V .s0 + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem ∧ LoopOut s S (V .s0 + BitVec.ofNat 64 d) tl s' := by
  have lp : LoopPre s S (V .s0 + BitVec.ofNat 64 d) tl :=
    ⟨hr3, hr4, hr5, h1, by omega, hSr, covers_prefix (he.perm.wC hd) h16, hSd.sub_right (Region.sub_prefix h16)⟩
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm, lo⟩ => ⟨?_, ?_, lo⟩
  · rw [hm, pad_bytes hz _ (by rw [length_bytesAt]; exact h16), length_bytesAt]
  · rw [hm]
    exact (writeBytes_frame' _ (length_bytesAt _ _ _)).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix h16⟩

/-- `recv`: the received tag (`tl` bytes at `r20`), padded with zeros at `W + rO`. -/
theorem recv_ok {s : State} (he : Env V sp s) {tl : Nat} (h19 : V .s8 = BitVec.ofNat 64 tl) (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (hTr : Covers [⟨V .s9, tl⟩] (s.rd ++ s.wr))
    (hTd : (⟨V .s9, tl⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 256, 16⟩) :
    WP isa recv s fun s' => bytesAt s'.mem (V .s0 + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (V .s9) tl ++ zeros (16 - tl) ∧
      Frame [⟨V .s0 + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
  have h20 := he.fr .s9 (by decide); have h19' := he.fr .s8 (by decide); have h31 := he.s0
  have w₀ := he.perm.wW (show 256 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 264 + 8 ≤ 2560 by decide)
  have h₁ : WP isa (.block [.li .t0 0, .store .d .t0 .s0 rO, .store .d .t0 .s0 (rO + 8), mov .a0 .s9,
      .addi .a1 .s0 rO, mov .a2 .s8]) s fun s₁ =>
      s₁.mem = (s.mem.writeW (V .s0 + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (V .s0 + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .a0 = V .s9 ∧ s₁.gpr .a1 = V .s0 + BitVec.ofNat 64 256 ∧ s₁.gpr .a2 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₁.gpr r = s.gpr r) ∧ Keeps' s s₁ := by
    crun [Int.reduceNatCast', rO, h31, h20, h19', h19, w₀, w₁, write_8, mov]
    exact ⟨by rw [add_ofNat_assoc], fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨hm₁, a3, a4, a5, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) k₁.sp k₁.rd k₁.wr
  have fz : Frame [⟨V .s0 + BitVec.ofNat 64 256, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hz : bytesAt s₁.mem (V .s0 + BitVec.ofNat 64 256) 16 = zeros 16 := by rw [hm₁]; exact zeroT_bytes _ _
  have hT₁ : bytesAt s₁.mem (V .s9) tl = bytesAt s.mem (V .s9) tl :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd) (by omega)
  refine WP.mono (padCopy_ok he₁ (d := 256) (by decide) h1 h16 (by rw [k₁.rd, k₁.wr]; exact hTr) hTd hz a3 a4 a5)
    fun s' ⟨hb, hf, lo⟩ => ⟨by rw [hb, hT₁], fz.trans hf, fun r a b c d e => by rw [lo.other r a b c d e,
      g₁ r a b c d], ⟨lo.keeps.1.trans k₁.rd, lo.keeps.2.1.trans k₁.wr, lo.keeps.2.2.1.trans k₁.sp,
      lo.keeps.2.2.2.trans k₁.lr⟩⟩

/-- `cmpTail`: `r3` is 1 iff the 16 bytes at `W + vO` and `W + rO` (272 and 256) are equal. -/
theorem cmpTail_ok {s : State} (he : Env V sp s) :
    WP isa (.block cmpTail) s fun s' =>
      s'.gpr .a0 = (if bytesAt s.mem (V .s0 + BitVec.ofNat 64 272) 16 =
        bytesAt s.mem (V .s0 + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h31 := he.s0
  have r₀ := he.perm.wR (show 272 + 8 ≤ 2560 by decide)
  have r₁ := he.perm.wR (show 256 + 8 ≤ 2560 by decide)
  have r₂ := he.perm.wR (show 280 + 8 ≤ 2560 by decide)
  have r₃ := he.perm.wR (show 264 + 8 ≤ 2560 by decide)
  have hrun : WP isa (.block cmpTail) s fun s' =>
      s'.gpr .a0 = BitVec.ofNat 64 1 - (((s.mem.readW (V .s0 + BitVec.ofNat 64 272) 64 ^^^
          s.mem.readW (V .s0 + BitVec.ofNat 64 256) 64) |||
        (s.mem.readW (V .s0 + BitVec.ofNat 64 280) 64 ^^^ s.mem.readW (V .s0 + BitVec.ofNat 64 264) 64)) |||
        (BitVec.ofNat 64 0 - ((s.mem.readW (V .s0 + BitVec.ofNat 64 272) 64 ^^^
          s.mem.readW (V .s0 + BitVec.ofNat 64 256) 64) |||
        (s.mem.readW (V .s0 + BitVec.ofNat 64 280) 64 ^^^ s.mem.readW (V .s0 + BitVec.ofNat 64 264) 64)))) >>> 63 ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
    apply WP.of_runBlock
    simp only [cmpTail, vO, rO, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load,
      State.write, Size.bytes, Size.bits, h31, r₀, r₁, r₂, r₃, Proof.Gcm.RISCV64.read_8, Option.bind_some,
      Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ne_eq, not_false_eq_true,
      Nat.reduceLT, Nat.reducePow, Nat.reduceMul, Nat.reduceMod, Nat.reduceAdd, ↓reduceIte, and_self,
      implies_true, BitVec.setWidth_eq]
    exact ⟨rfl, fun r a b c => by simp [a, b, c], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.mono hrun fun s' ⟨h3, hg, hk⟩ => ⟨?_, hg, hk⟩
  rw [h3, cmp_value]
  have e := words_eq s.mem (V .s0 + BitVec.ofNat 64 272) (V .s0 + BitVec.ofNat 64 256)
  simp only [add_ofNat_assoc, Nat.reduceAdd] at e
  by_cases hq : bytesAt s.mem (V .s0 + BitVec.ofNat 64 272) 16 = bytesAt s.mem (V .s0 + BitVec.ofNat 64 256) 16
  · simp only [e.mpr hq, hq, ite_true]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hq (e.mp h)), ite_eq_right_of_eq_false _ _ (eq_false hq)]

/-- `cmp o`: the first `tl` bytes of the tag at `W + o`, padded with zeros
at `W + vO`, compared with the received tag at `W + rO`. -/
theorem cmp_ok {s : State} (he : Env V sp s) {o : Nat} (ho : o = 0 ∨ o = 112) {tl : Nat}
    (h19 : V .s8 = BitVec.ofNat 64 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa (cmp o) s fun s' => s'.gpr .a0 = (if bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) =
        bytesAt s.mem (V .s0 + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      Frame [⟨V .s0 + BitVec.ofNat 64 272, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → s'.gpr r = s.gpr r) ∧ Keeps' s s' := by
  have h19' := he.fr .s8 (by decide); have h31 := he.s0
  have w₀ := he.perm.wW (show 272 + 8 ≤ 2560 by decide)
  have w₁ := he.perm.wW (show 280 + 8 ≤ 2560 by decide)
  have o₀ : o < 2 ^ 15 := by omega
  have h₁ : WP isa (.block [.li .t0 0, .store .d .t0 .s0 vO, .store .d .t0 .s0 (vO + 8), .addi .a0 .s0 o,
      .addi .a1 .s0 vO, mov .a2 .s8]) s fun s₁ =>
      s₁.mem = (s.mem.writeW (V .s0 + BitVec.ofNat 64 272) (0 : BitVec 64)).writeW
        (V .s0 + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
      s₁.gpr .a0 = V .s0 + BitVec.ofNat 64 o ∧ s₁.gpr .a1 = V .s0 + BitVec.ofNat 64 272 ∧
      s₁.gpr .a2 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₁.gpr r = s.gpr r) ∧ Keeps' s s₁ := by
    crun [Int.reduceNatCast', vO, h31, h19', h19, w₀, w₁, o₀, write_8, mov]
    exact ⟨by rw [add_ofNat_assoc], fun r a b c d => by simp [a, b, c, d], ⟨rfl, rfl, rfl, rfl⟩⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨hm₁, a3, a4, a5, g₁, k₁⟩ => ?_)
  have he₁ := he.keep (fun r hr => g₁ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide)) k₁.sp k₁.rd k₁.wr
  have fz : Frame [⟨V .s0 + BitVec.ofNat 64 272, 16⟩] s.mem s₁.mem := by
    rw [hm₁]; exact Proof.Cmac.frame_store2 _ _ _
  have hz : bytesAt s₁.mem (V .s0 + BitVec.ofNat 64 272) 16 = zeros 16 := by rw [hm₁]; exact zeroT_bytes _ _
  have hSd : (⟨V .s0 + BitVec.ofNat 64 o, tl⟩ : Region).Disjoint ⟨V .s0 + BitVec.ofNat 64 272, 16⟩ :=
    Lay.w_w (by omega) (by omega) (by decide)
  have hS₁ : bytesAt s₁.mem (V .s0 + BitVec.ofNat 64 o) tl = bytesAt s.mem (V .s0 + BitVec.ofNat 64 o) tl :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega)
  have hR₁ : bytesAt s₁.mem (V .s0 + BitVec.ofNat 64 256) 16 = bytesAt s.mem (V .s0 + BitVec.ofNat 64 256) 16 :=
    bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)
  refine WP.seq (WP.mono (padCopy_ok he₁ (d := 272) (by decide) h1 h16
    (by rw [k₁.rd, k₁.wr]; exact covers_left (he.perm.wC (by omega))) hSd hz a3 a4 a5) fun s₂ ⟨hb, hf, lo⟩ => ?_)
  have he₂ := he₁.keep (fun r hr => lo.other r (by revert r; decide) (by revert r; decide) (by revert r; decide)
    (by revert r; decide) (by revert r; decide)) lo.keeps.2.2.1 lo.keeps.1 lo.keeps.2.1
  have hR₂ : bytesAt s₂.mem (V .s0 + BitVec.ofNat 64 256) 16 = bytesAt s.mem (V .s0 + BitVec.ofNat 64 256) 16 := by
    rw [← hR₁]
    exact bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)
  refine WP.mono (cmpTail_ok he₂) fun s' ⟨h3, g₃, k₃⟩ => ⟨?_, ?_, ?_, ?_⟩
  · rw [h3, hb, hR₂, hS₁]
  · rw [k₃.mem]; exact fz.trans hf
  · intro r a b c d e
    rw [g₃ r b c d, lo.other r a b c d e, g₁ r a b c d]
  · exact ⟨k₃.rd.trans (lo.keeps.1.trans k₁.rd), k₃.wr.trans (lo.keeps.2.1.trans k₁.wr),
      k₃.sp.trans (lo.keeps.2.2.1.trans k₁.sp), k₃.lr.trans (lo.keeps.2.2.2.trans k₁.lr)⟩

end

end VG.Proof.AesGcm.RISCV64
