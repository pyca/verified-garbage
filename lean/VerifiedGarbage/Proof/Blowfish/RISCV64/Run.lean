module

import VerifiedGarbage.Impl.Blowfish.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Blowfish
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.TCB.Code

/-!
# Blowfish on RISC-V: running blocks

`brun [facts]` runs a block of the Blowfish code symbolically (`mrun`). The
code's 32-bit values live in the low words of registers: `lo` is that word,
and the `lo_*` lemmas take it through the operations the code uses. The
masks are made by arithmetic shifts (`sra_mask`, `bit_mask`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64

/-- Steps a block of the Blowfish code. -/
syntax "brun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brun) => `(tactic| brun [])
  | `(tactic| brun [$ls,*]) => `(tactic|
      mrun [sch, xL, xR, fReg, pPtr, qReg, acc, mReg, tmp, tmp2, lane, rowPtr, ptr, cnt, $ls,*])

theorem WP.reassoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-! ## Low words -/

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem lo_and (x y : BitVec 64) : lo (x &&& y) = lo x &&& lo y := lo32_and x y
theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := lo32_or x y
theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := lo32_xor x y
theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := lo32_add x y
theorem lo_ext (x : BitVec 32) : lo (x.setWidth 64) = x := lo32_ext x
theorem lo_sext (x : BitVec 32) : lo (sext32 x) = x := lo32_sext x

theorem lo_ofNat (n : Nat) : lo (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide)]

theorem lo_ite (c : Prop) [Decidable c] (x y : BitVec 64) :
    lo (if c then x else y) = if c then lo x else lo y := by
  by_cases h : c <;> simp [h]

/-- A word rotated right by `r < 32`, from the two word shifts. -/
theorem lo_rotr (x : BitVec 64) {r : Nat} (h : r < 32) :
    lo (sext32 (lo x >>> r) ^^^ sext32 (lo x <<< (32 - r))) = (lo x).rotateRight r := by
  rw [lo_xor, lo_sext, lo_sext, RISCV64.ByteLoad.rotr_shifts _ h]

/-! ## Masks -/

/-- `v >> 63`, arithmetically, after `v - 1`: all ones exactly when
`v < 2 ^ 63` is zero. -/
theorem sra_mask (v : BitVec 64) (h : v.toNat < 2 ^ 63) :
    (v - 1#64).sshiftRight 63 = if v.toNat = 0 then BitVec.allOnes 64 else 0 := by
  by_cases e : v.toNat = 0
  · have : v = 0#64 := BitVec.eq_of_toNat_eq (by simp [e])
    subst this; decide
  · rw [ite_eq_right e, BitVec.sshiftRight_eq_of_msb_false]
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
        show BitVec.toNat (0 : BitVec 64) = 0 from rfl]
      simp only [BitVec.toNat_ofNat]
      omega
    · rw [BitVec.msb_eq_decide]
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_false_iff_not]
      omega

/-- Bit `c` of `q` shifted to the top and arithmetically back: all ones if
it is set. -/
theorem bit_mask (q : BitVec 64) {c : Nat} (hc : c < 64) :
    (q <<< (63 - c)).sshiftRight 63 = if q.getLsbD c then BitVec.allOnes 64 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
  have key : (q <<< (63 - c)).getLsbD 63 = q.getLsbD c := by
    rw [BitVec.getLsbD_shiftLeft]
    simp only [show (63 : Nat) < 64 by decide, decide_true, Bool.true_and,
      show ¬ (63 < 63 - c) by omega, decide_false, Bool.not_false, show 63 - (63 - c) = c by omega]
  rw [show (if 63 + i < 64 then (q <<< (63 - c)).getLsbD (63 + i) else (q <<< (63 - c)).getLsbD (64 - 1)) =
    (q <<< (63 - c)).getLsbD 63 by split; (congr 1; omega); rfl, key]
  cases q.getLsbD c
  · simp
  · simp only [ite_true, BitVec.getLsbD_allOnes, hi, decide_true, show ¬ 64 ≤ i by omega, decide_false,
      Bool.not_false, Bool.and_true]

/-- `x XOR ((r XOR x) AND m)` for an all-ones-or-zero mask. -/
theorem select_eq (x r : BitVec 64) (b : Bool) :
    x ^^^ ((r ^^^ x) &&& (if b then BitVec.allOnes 64 else 0)) = if b then r else x := by
  cases b
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm r x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Blowfish.RISCV64
