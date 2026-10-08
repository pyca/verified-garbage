import VerifiedGarbage.Proof.AesCtr.Inc
import VerifiedGarbage.Proof.AesCtr.Spec
import VerifiedGarbage.Proof.AesCbc.X86.Body
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Impl.AesCtr.X86

/-!
# AES-CTR on x86: the increment

`incr` run once, with its memory as explicit writes (`incMem`): four
words, loaded and byte-reversed, the last plus 1 and each other plus the
carry out of the one after it, reversed again and stored. `incMem_bytes`:
the block it writes is `Spec.Ctr.inc` of the one it read.
-/

namespace VG.Proof.AesCtr.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCtr.X86
open VG.Impl.CmacAes.X86 (at_)
open VG.Proof.CmacAes.X86 (ea_at')
open VG.Spec.Aes (bytesAt)

/-- A word plus a carry, as `adc` with 0 computes it. -/
abbrev adc0 (a : BitVec 32) (c : Bool) : BitVec 32 := a + 0 + (BitVec.ofBool c).setWidth 32

/-- The carry out of `adc0`. -/
abbrev cout (a : BitVec 32) (c : Bool) : Bool := decide (2 ^ 32 ≤ a.toNat + (0 : BitVec 32).toNat + c.toNat)

/-- The memory after `incr` on the block at `Q`. -/
def incMem (m : Mem) (Q : Addr) : Mem :=
  let a3 := bswap (m.readW (Q + BitVec.ofNat 64 12) 32)
  let a2 := bswap (m.readW (Q + BitVec.ofNat 64 8) 32)
  let a1 := bswap (m.readW (Q + BitVec.ofNat 64 4) 32)
  let a0 := bswap (m.readW Q 32)
  let c3 := decide (2 ^ 32 ≤ a3.toNat + (1 : BitVec 32).toNat)
  let c2 := cout a2 c3
  let c1 := cout a1 c2
  (((m.writeW (Q + BitVec.ofNat 64 12) (bswap (a3 + 1))).writeW (Q + BitVec.ofNat 64 8) (bswap (adc0 a2 c3))).writeW
    (Q + BitVec.ofNat 64 4) (bswap (adc0 a1 c2))).writeW Q (bswap (adc0 a0 c1))

theorem incr_ok (s : State) {Q : Addr} (hq : (s.gpr .ebx).setWidth 64 = Q) (hfit : (s.gpr .ebx).toNat + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Q + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa incr s = some s' ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.mem = incMem s.mem Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a (d : Nat) (hd : d < 16) : addr (s.gpr .ebx) d = Q + BitVec.ofNat 64 d := by
    rw [addr_eq (by omega), hq]
  have a0 : addr (s.gpr .ebx) 0 = Q := by rw [a 0 (by decide)]; simp
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr Q 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, incr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load32, State.store32, ea_at', execAlu, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg,
      wr_arithFlags, cf_setReg, cf_arithFlags, a0, a 4 (by decide), a 8 (by decide), a 12 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide),
      hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ h₄ => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, h₁, h₂, h₃, h₄]

theorem adc0_toNat (a : BitVec 32) (c : Bool) : (adc0 a c).toNat = (a.toNat + c.toNat) % 2 ^ 32 := by
  have e₀ : (0 : BitVec 32).toNat = 0 := rfl
  cases c
  · have e : (BitVec.setWidth 32 (BitVec.ofBool false)).toNat = 0 := rfl
    rw [adc0, BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_false]; omega
  · have e : (BitVec.setWidth 32 (BitVec.ofBool true)).toNat = 1 := rfl
    rw [adc0, BitVec.toNat_add, BitVec.toNat_add, e₀, e]; simp only [Bool.toNat_true]; omega

theorem cout_toNat (a : BitVec 32) (c : Bool) : (cout a c).toNat = (a.toNat + c.toNat) / 2 ^ 32 := by
  have e₀ : (0 : BitVec 32).toNat = 0 := rfl
  have := a.isLt
  have := c.toNat_le
  rw [cout, e₀]
  by_cases h : 2 ^ 32 ≤ a.toNat + 0 + c.toNat
  · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega
  · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega

theorem incMem_bytes (m : Mem) (Q : Addr) : bytesAt (incMem m Q) Q 16 = Spec.Ctr.inc (bytesAt m Q 16) := by
  have c3 : (decide (2 ^ 32 ≤ (bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat + (1 : BitVec 32).toNat)).toNat =
      ((bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat + 1) / 2 ^ 32 := by
    have := (bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).isLt
    have e₁ : (1 : BitVec 32).toNat = 1 := rfl
    rw [e₁]
    by_cases h : 2 ^ 32 ≤ (bswap (m.readW (Q + BitVec.ofNat 64 12) 32)).toNat + 1
    · rw [decide_eq_true h]; simp only [Bool.toNat_true]; omega
    · rw [decide_eq_false h]; simp only [Bool.toNat_false]; omega
  apply AesCtr.inc_words32
  · show (bswap _ + 1).toNat = ((bswap _).toNat + 1) % 2 ^ 32
    rw [BitVec.toNat_add]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, c3]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, cout_toNat, c3]; rfl
  · show (adc0 _ _).toNat = _
    rw [adc0_toNat, cout_toNat, cout_toNat, c3]; rfl

theorem incMem_frame (m : Mem) (Q : Addr) : Frame [⟨Q, 16⟩] m (incMem m Q) :=
  ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base Q (d := 12) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 8) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base Q (d := 4) (n := 4) (k := 16) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (by simpa using Offset.contains_base Q (d := 0) (n := 4) (k := 16) (by decide) (by decide))

end VG.Proof.AesCtr.X86
