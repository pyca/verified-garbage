module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.Stitch
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# ChaCha20-Poly1305 with the AVX2 code for short data (x86-64): the length test

`Stitch.smallTest lim` sets `CF` if `len` (`r9`) is below `lim` or from
`winLo` to `winHi - 1`, writing only `rax`, `r10` and the flags
(`smallTest_ok`); `Stitch.ifmaTest` sets it if `len` is from `ifmaLo` to
`ifmaHi - 1`, writing only `rax` and the flags (`ifmaTest_ok`).
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

/-- `len - ifmaLo` is below `ifmaHi - ifmaLo`, unsigned, in the window alone. -/
theorem ifma_iff (x : BitVec 64) :
    (x - BitVec.ofNat 64 449).toNat < 191 ↔ 449 ≤ x.toNat ∧ x.toNat < 640 := by
  bv_omega

/-- The IFMA instance's length test, from `s`: `CF` set if `len` is from
`ifmaLo` to `ifmaHi - 1`, and only `rax` and the flags written. -/
theorem ifmaTest_ok (s : State) :
    WP isa (.block ifmaTest) s fun t =>
      isa.eval .b t = some (decide (ifmaLo ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat < ifmaHi)) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x449 : BitVec.signExtend 64 (BitVec.ofNat 32 449) = BitVec.ofNat 64 449 := by decide
  have x191 : BitVec.signExtend 64 (BitVec.ofNat 32 191) = BitVec.ofNat 64 191 := by decide
  have e191 : (BitVec.ofNat 64 191).toNat = 191 := rfl
  have hw := ifma_iff (s.gpr .r9)
  simp only [ifmaTest, ifmaLo, ifmaHi, Nat.reduceSub, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, x449, x191, Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval,
    e191, Option.some.injEq, exists_eq_left', ↓reduceIte]
  exact ⟨decide_eq_decide.mpr hw, fun r h1 => by simp only [h1, ite_false], rfl, rfl, rfl, rfl⟩

/-- `len mod 512` is from `lo` to `lo + n - 1` if `(len & 511) - lo` is below
`n`. -/
theorem rest_iff (x : BitVec 64) {lo n : Nat} (hlo : lo < 512) (hn : n ≤ 512) :
    ((x &&& BitVec.ofNat 64 511) - BitVec.ofNat 64 lo).toNat < n ↔
      lo ≤ x.toNat % 512 ∧ x.toNat % 512 < lo + n := by
  have ha : (x &&& BitVec.ofNat 64 511).toNat = x.toNat % 512 := by
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 511).toNat = 2 ^ 9 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_sub, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show lo < 2 ^ 64 by omega)]
  have := Nat.mod_lt x.toNat (show 0 < 512 by decide)
  by_cases hl : lo ≤ x.toNat % 512
  · rw [show 2 ^ 64 - lo + x.toNat % 512 = (x.toNat % 512 - lo) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- `decRest`'s tests of the rest (`restTest`): `CF` set if `len mod 512`
(`r13`) is from `lo` to `lo + n - 1`, writing only `rax` and the flags. -/
theorem restTest_ok {lo n : Nat} (hlo : lo < 512) (hn : n ≤ 512)
    (xl : BitVec.signExtend 64 (BitVec.ofNat 32 lo) = BitVec.ofNat 64 lo)
    (xn : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n) (s : State) :
    WP isa (.block (restTest lo n)) s fun t =>
      isa.eval .b t = some (decide (lo ≤ (s.gpr .r13).toNat % 512 ∧ (s.gpr .r13).toNat % 512 < lo + n)) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x511 : BitVec.signExtend 64 (511 : BitVec 32) = BitVec.ofNat 64 511 := by decide
  have en : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  have hw := rest_iff (s.gpr .r13) hlo hn
  simp only [restTest, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, x511, xl, xn,
    Option.bind_some, Option.map_some, gpr_arithFlags, cf_arithFlags, gpr_setReg, eval, en,
    Option.some.injEq, exists_eq_left', ↓reduceIte]
  exact ⟨by rw [decide_eq_decide]; exact hw, fun r h1 => by simp only [h1, ite_false], rfl, rfl, rfl, rfl⟩

/-- `cmp r13, 512`: `CF` set below 512 bytes. -/
theorem cmp13_ok (s : State) :
    WP isa (.block [.alu .cmp .r13 (.imm 512)]) s fun t =>
      isa.eval .b t = some (decide ((s.gpr .r13).toNat < 512)) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  have x512 : BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 := by decide
  have e512 : (BitVec.ofNat 64 512).toNat = 512 := rfl
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, x512,
    Option.bind_some, cf_arithFlags, eval, e512, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, rfl⟩

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
