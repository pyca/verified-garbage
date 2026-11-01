module

import VerifiedGarbage.Proof.Poly1305.RISCV64.Init
import VerifiedGarbage.Proof.Poly1305.RISCV64.Blocks
import VerifiedGarbage.Proof.Poly1305.RISCV64.Update
import VerifiedGarbage.Proof.Poly1305.RISCV64.Finalize
import VerifiedGarbage.Proof.Poly1305.RISCV64.Buffer
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Impl.Poly1305.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# Poly1305 on RISC-V: the shared contracts

The proofs are written against per-target contracts
(`Proof/Poly1305/RISCV64/Contract.lean`); these theorems move them to the
shared contracts, which the artifacts are emitted with. No function uses
the stack.
-/

@[expose] public section

namespace VG.Proof.Poly1305.RISCV64.Shared

theorem init :
    Verified RISCV64.target Impl.Poly1305.RISCV64.init (Spec.Poly1305.initContract RISCV64.abi) :=
  init_verified.of_implies (by
    contract_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initRISCV64,
      RISCV64.abi, RISCV64.argRegs] [initSat] using initSat)

theorem blocks :
    Verified RISCV64.target Impl.Poly1305.RISCV64.blocks (Proof.Poly1305.blocksContract RISCV64.abi) :=
  blocks_verified.of_implies (by
    contract_implies [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig,
      Proof.Poly1305.blocksRISCV64, RISCV64.abi, RISCV64.argRegs] [blocksSat] using blocksSat)

theorem update :
    Verified RISCV64.target Impl.Poly1305.RISCV64.update (Spec.Poly1305.updateContract RISCV64.abi) :=
  update_verified.of_implies
    { pre := by
        sig_implies_pre [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, Proof.Poly1305.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, RISCV64.abi, RISCV64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, Proof.Poly1305.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Spec.Poly1305.updatePost, RISCV64.abi, RISCV64.argRegs, updateSat] [updateSat]
          using updateSat }

theorem finalize :
    Verified RISCV64.target Impl.Poly1305.RISCV64.finalize (Spec.Poly1305.finalizeContract RISCV64.abi) :=
  finalize_verified.of_implies
    { pre := by
        sig_implies_pre [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, RISCV64.abi, RISCV64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
          Spec.Poly1305.finalizePost, RISCV64.abi, RISCV64.argRegs, finalizeSat] [finalizeSat]
          using finalizeSat }

theorem finalizeScratch : Verified RISCV64.target Impl.Poly1305.RISCV64.finalize
    (Proof.Poly1305.finalizeScratchContract RISCV64.abi) :=
  finalizeScratch_verified.of_implies
    { pre := by
        sig_implies_pre [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizeScratchRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, RISCV64.abi, RISCV64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizeScratchRISCV64, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, RISCV64.abi, RISCV64.argRegs, finalizeScratchSat]
          [finalizeScratchSat] using finalizeScratchSat }

end VG.Proof.Poly1305.RISCV64.Shared
