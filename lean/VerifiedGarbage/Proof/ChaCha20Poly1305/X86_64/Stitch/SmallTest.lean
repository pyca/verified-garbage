module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20-Poly1305 with the AVX2 code for short data (x86-64): the length test

`Stitch.smallTest lim` sets `CF` if `len` (`r9`) is below `lim` or from
`winLo` to `winHi - 1`, writing only `rax`, `r10` and the flags
(`smallTest_ok`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.ChaCha20Poly1305.X86_64.Stitch

/-- `len - winLo` is below `winHi - winLo`, unsigned, in the window alone. -/
theorem win_iff (x : BitVec 64) :
    (x - BitVec.ofNat 64 961).toNat < 64 ↔ 961 ≤ x.toNat ∧ x.toNat < 1025 := by
  bv_omega

theorem readSrc_imm (t : State) {n : Nat}
    (h : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n) :
    readSrc t (.imm (BitVec.ofNat 32 n)) = some (BitVec.ofNat 64 n) :=
  congrArg some h

/-- The length test, from `s`: `CF` set if `len` is below `lim` or in the
window, and only `rax`, `r10` and the flags written. -/
theorem smallTest_ok {lim : Nat} (hl : BitVec.signExtend 64 (BitVec.ofNat 32 lim) = BitVec.ofNat 64 lim)
    (hl0 : 0 < lim) (hl1 : lim < 2 ^ 64) (s : State) :
    WP isa (.block (smallTest lim)) s fun t =>
      isa.eval .b t = some (decide ((s.gpr .r9).toNat < lim ∨
        (winLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < winHi))) ∧
      (∀ r, r ≠ .rax → r ≠ .r10 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x961 : BitVec.signExtend 64 (961#32) = 961#64 := by decide
  have x64 : BitVec.signExtend 64 (64#32) = 64#64 := by decide
  have x0 : BitVec.signExtend 64 (0#32) = 0#64 := by decide
  have hw := win_iff (s.gpr .r9)
  have el : (BitVec.ofNat 64 lim).toNat = lim := by rw [BitVec.toNat_ofNat]; omega
  have e64 : (64#64).toNat = 64 := rfl
  have e0 : (0#64).toNat = 0 := rfl
  rw [show smallTest lim = [.mov32 .rax (.imm 0), .mov .rax (.reg .r9), .mov .r10 (.reg .r9),
    .alu .sub .r10 (.imm (BitVec.ofNat 32 961)), .alu .cmp .r10 (.imm (BitVec.ofNat 32 64)),
    .mov .r10 (.imm (BitVec.ofNat 32 0)), .cmov .b .rax (.reg .r10), .alu .cmp .rax (.imm (BitVec.ofNat 32 lim))]
    from rfl]
  have hr9 := (s.gpr .r9).isLt
  by_cases h : (s.gpr .r9 - 961#64).toNat < 64
  · have hc : ((s.gpr .r9).toNat < lim ∨ winLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < winHi) := by
      simp only [winLo, winHi]; omega
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, readSrc, x961, x64, x0, hl,
      Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, cf_setReg, gpr_setReg, eval, h, hc,
      readSrc32, State.setReg32,
      decide_true, Option.some.injEq, exists_eq_left', ↓reduceIte, reduceCtorEq, e64, el, e0, hl0]
    exact ⟨trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], rfl, rfl, rfl, rfl⟩
  · have hc : ((s.gpr .r9).toNat < lim ∨ winLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < winHi) ↔
        (s.gpr .r9).toNat < lim := by
      simp only [winLo, winHi]; omega
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execCmov, readSrc, x961, x64, x0, hl,
      Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, cf_setReg, gpr_setReg, eval, h, hc,
      readSrc32, State.setReg32,
      decide_false, Bool.false_eq_true, Option.some.injEq, exists_eq_left', ↓reduceIte, reduceCtorEq, e64, el]
    exact ⟨trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], rfl, rfl, rfl, rfl⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
