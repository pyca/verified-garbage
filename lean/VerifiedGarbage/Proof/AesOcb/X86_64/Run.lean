import VerifiedGarbage.Proof.AesOcb.X86_64.Env
import VerifiedGarbage.Proof.AesCcm.X86_64.Run

/-!
# AES-OCB on x86-64: running straight-line blocks

Untrusted: everything here is checked by Lean. `orun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Proof.AesCcm.X86_64 (imm_eq offset_nat setWidth_imm)

/-- Runs a block of the instructions the AES-OCB code uses. -/
macro "orun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [imm_eq, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, execShift, State.load64, State.store64, State.load8, State.store8, State.ea,
    offset_nat, at_, ld, st, mvr, addi, tagO, ofsO, ckO, sumO, ldO, l0O, lO, tmpO, t2O, ohO, savO,
    dataO, lenO, tlO, tgO, rndO, aadO, alenO, botO, o0O, nO, nlO, bufO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, Option.bind_some, Option.map_some, gpr_setReg, gpr_arithFlags,
    gpr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags,
    wr_setReg, wr_arithFlags, wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags,
    ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMod, Nat.reducePow, setWidth_imm, and_self, and_true, true_and, $ts,*]) <;> try rfl)

end VG.Proof.AesOcb.X86_64
