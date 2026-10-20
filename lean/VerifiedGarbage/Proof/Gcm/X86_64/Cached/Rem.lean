module
public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
import VerifiedGarbage.Impl.Gcm.X86_64.Stitch
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import VerifiedGarbage.Proof.Gcm.X86_64.Rev
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes
import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base

/-!
# The blocks after the last group

`cmp r10, n` (`cmp10_ok`), which chooses how many registers the blocks
after the last group take (`RemG.lean`, `RemGD.lean`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph sch hk y₀
  addr_eq in_sub in_sub_int in_rdwr blocks_ctr32 blockAt_writeW_sep' ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod prod reduceB)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (gq lastG)
open VG.Impl.Gcm.X86_64.StitchZH (remSetup)
open VG.Proof.Gcm.X86_64.StitchZ (EInv AInv GEnv QG gq_ok gRegs gRegs_ok FinOk)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-- `cmp r10, n`. -/
theorem cmp10_ok (s : State) (i : BitVec 32) (n : Nat) (hi : BitVec.signExtend 64 i = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .cmp .r10 (.imm i)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .r10).toNat < (BitVec.ofNat 64 n).toNat)) ∧ s'.gpr = s.gpr ∧
        (∀ r l, s'.zlane r l = s.zlane r l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

end VG.Proof.Gcm.X86_64.StitchZH
