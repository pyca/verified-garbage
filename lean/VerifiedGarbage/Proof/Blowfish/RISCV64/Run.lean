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
masks are made by arithmetic shifts (`bit_mask`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.RISCV64

open VG VG.RISCV64 VG.Impl.Blowfish.RISCV64

/-- Steps a block of the Blowfish code. -/
syntax "brun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brun) => `(tactic| brun [])
  | `(tactic| brun [$ls,*]) => `(tactic|
      mrun [sch, xL, xR, fReg, pPtr, qReg, acc, mReg, tmp, rowPtr, ptr, cnt, $ls,*])

theorem WP.reassoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-! ## Low words -/

/-- The low word of a register. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32

theorem lo_or (x y : BitVec 64) : lo (x ||| y) = lo x ||| lo y := lo32_or x y
theorem lo_xor (x y : BitVec 64) : lo (x ^^^ y) = lo x ^^^ lo y := lo32_xor x y
theorem lo_add (x y : BitVec 64) : lo (x + y) = lo x + lo y := lo32_add x y
theorem lo_ext (x : BitVec 32) : lo (x.setWidth 64) = x := lo32_ext x
theorem lo_sext (x : BitVec 32) : lo (sext32 x) = x := lo32_sext x

/-! ## Masks -/

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

end VG.Proof.Blowfish.RISCV64
