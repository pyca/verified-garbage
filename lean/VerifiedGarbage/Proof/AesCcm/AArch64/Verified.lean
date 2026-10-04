import VerifiedGarbage.Proof.AesCcm.AArch64.OpenCT
import VerifiedGarbage.Proof.AesCcm.AArch64.SealCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ccm.Contract

/-!
# AES-CCM on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time
(for any implementation `v` of `vg_cmac_aes_update`, with the `vg_aes_ctr32`
that goes with it), a state satisfying the precondition, and the shared
contracts of `Spec/Ccm/Contract.lean`, with no stack: the calls keep the
return address in `x30`, which each function saves in the working space.
-/

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.Impl.AesCcm.AArch64

/-! ## v8–v15 -/

theorem seal_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («seal» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«seal», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

theorem open_keepsV (v : Proof.CmacAes.AArch64.UpdateImpl) :
    («open» v.callee v.ctr.callee).allInstrs keepsV = true := by
  simp only [«open», mac, b0, flagsSeg, aadHead, header, absorbPad, absTail, updBlock, tag, ctr, ctrChunk,
    ctrTail, ctrs, cmp, mask, callUpdate, callCtr, Code.allInstrs, v.keepsV, v.ctr.keepsV]
  decide +kernel

/-! ## Correctness and constant time -/

theorem seal_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : sealAArch64.pre s) :
    ∃ t s', Exec isa («seal» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ sealAArch64.post s s' :=
  WP.withPreservedV (seal_wp v hs) (seal_keepsV v)

theorem open_correct (v : Proof.CmacAes.AArch64.UpdateImpl) (s : State) (hs : openAArch64.pre s) :
    ∃ t s', Exec isa («open» v.callee v.ctr.callee) s t s' ∧ abiPreserved s s' ∧ openAArch64.post s s' :=
  WP.withPreservedV (open_wp v hs) (open_keepsV v)

/-- A state satisfying the precondition of `vg_aes_ccm_seal` and
`vg_aes_ccm_open`: a 7-byte nonce, no associated data, no data, `work` at 0
and a 4-byte tag. -/
def sealSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 7 | .x4 => 0x3000 | .x6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := if a = 0x8008 then 4 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩]
  wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩]

/-! ## The shared contracts -/

theorem seal_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («seal» v.callee v.ctr.callee) (Spec.Ccm.sealContract AArch64.abi) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    sig_implies [Spec.Ccm.sealContract, Spec.Ccm.sealSig, sealAArch64, onePre, onePub, args, rounds,
      AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD, List.range,
      List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

theorem open_verified (v : Proof.CmacAes.AArch64.UpdateImpl) :
    Verified AArch64.target («open» v.callee v.ctr.callee) (Spec.Ccm.openContract AArch64.abi) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    sig_implies [Spec.Ccm.openContract, Spec.Ccm.openSig, Spec.Ccm.sealSig, openAArch64, onePre, onePub,
      openRes, args, rounds, AArch64.abi, AArch64.argRegs, AArch64.stackArg, AArch64.stackArgAddr, List.getD,
      List.range, List.range.loop]
      [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat)

end VG.Proof.AesCcm.AArch64
