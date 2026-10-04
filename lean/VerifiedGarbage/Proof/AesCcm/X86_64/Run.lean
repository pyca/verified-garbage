import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes

/-!
# AES-CCM on x86-64: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`).
-/

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)

theorem setWidth_imm {n : Nat} : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 (n % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Runs a block of the instructions the AES-CCM code uses. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    readSrc32, execAlu, execAlu32, execShift, State.load64, State.store64, State.load32, State.store32,
    State.load8, State.store8, State.ea, State.setReg32, offset_nat, at_, imm, ptr, bO, c0O, c1O, ksO, uO,
    nonceO, nlenO, aadO, alenO, dataO, lenO, tlO, kO, okO, roundsO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, setWidth_imm, and_self, and_true, true_and, $ts,*]) <;> try rfl)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ofNat_add_ofNat]

end VG.Proof.AesCcm.X86_64
