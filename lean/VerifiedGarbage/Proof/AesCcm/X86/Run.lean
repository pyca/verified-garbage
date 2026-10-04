import VerifiedGarbage.Proof.AesCcm.X86.Env
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-CCM on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-CCM code.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp tglO rO vO tpO dO nO bO)
open VG.Proof.AesGcm.X86 (store32_eq store8_eq gpr_setMem mem_setMem rd_setMem wr_setMem cf_setMem zf_setMem
  readW_writeW_off)

/-- A word at `p + a`, after a byte written at `p + b` elsewhere. -/
theorem readW_writeB_off (m : Mem) (p : Addr) (v : BitVec 8) {a b : Nat} (h : a + 4 ≤ b ∨ b + 1 ≤ a)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 b) v).readW (p + BitVec.ofNat 64 a) 32 = m.readW (p + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Runs a block of the instructions the AES-CCM code uses. The facts given
rewrite the addresses and discharge the permissions. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, blkO, c0O, c1O, ksO, uO, ctxO, roundsO, nonceO, nlenO, aadO, alenO, dataO,
    lenO, okO, scrO, tglO, rO, vO, tpO, dO, nO, bO, List.cons_append, List.nil_append, List.append_assoc,
    Option.bind_some, Option.map_some, readW_writeW_off, readW_writeB_off, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem, mem_setMem, rd_setMem,
    wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self, and_true, true_and,
    eq_self_iff_true, Reg8.reg, $ts,*]) <;>
  try rfl)

/-- Reads registers through the writes of a block. -/
macro "cregs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | with_reducible assumption) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
    $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
macro "cmems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
    rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
    zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
    gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, readW_writeB_off, blkO, c0O, c1O,
    ksO, uO, ctxO, roundsO, nonceO, nlenO, aadO, alenO, dataO, lenO, okO, scrO, tglO, rO, vO, tpO, dO, nO, bO,
    Nat.reduceAdd, Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

end VG.Proof.AesCcm.X86
