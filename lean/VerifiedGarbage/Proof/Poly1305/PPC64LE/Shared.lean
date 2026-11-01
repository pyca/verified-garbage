module

import VerifiedGarbage.Proof.Poly1305.PPC64LE.Init
import VerifiedGarbage.Proof.Poly1305.PPC64LE.Blocks
import VerifiedGarbage.Proof.Poly1305.PPC64LE.Update
import VerifiedGarbage.Proof.Poly1305.PPC64LE.Finalize
public import VerifiedGarbage.Proof.Poly1305.BlocksScratch
public import VerifiedGarbage.Proof.Poly1305.Scratch
public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Poly1305.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# Poly1305 on PPC64LE: the shared contracts

The proofs are written against per-target contracts
(`Proof/Poly1305/PPC64LE/Contract.lean`); these theorems move them to the
shared contracts, which the artifacts are emitted with.

`blocks`, `update` and `finalize` keep their working space (128 bytes, where
they save the nonvolatile registers they use) in a frame of their own: they
are the shared contracts with the working space as an argument
(`Proof/Poly1305/BlocksScratch.lean`, `Proof/Poly1305/Scratch.lean` and
`Proof.Poly1305.finalizeScratchContract`) run in a frame that allocates it
(`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.PPC64LE.Shared

open _root_.VG.PPC64LE

theorem init :
    Verified PPC64LE.target Impl.Poly1305.PPC64LE.init (Spec.Poly1305.initContract PPC64LE.abi) :=
  init_verified.of_implies (by
    contract_implies [Spec.Poly1305.initContract, Spec.Poly1305.initSig, Proof.Poly1305.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [initSat] using initSat)

theorem blocksScratch : Verified PPC64LE.target Impl.Poly1305.PPC64LE.blocks
    (Proof.Poly1305.blocksScratchContract PPC64LE.abi) :=
  blocks_verified.of_implies (by
    contract_implies [Proof.Poly1305.blocksScratchContract, Proof.Poly1305.blocksScratchSig,
      Proof.Poly1305.blocksPost, Proof.Poly1305.blocksPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [blocksSat] using blocksSat)

theorem updateScratch : Verified PPC64LE.target Impl.Poly1305.PPC64LE.update
    (Proof.Poly1305.updateScratchContract PPC64LE.abi) :=
  update_verified.of_implies
    { pre := by
        sig_implies_pre [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig,
          Spec.Poly1305.updatePost, Proof.Poly1305.updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig,
          Spec.Poly1305.updatePost, PPC64LE.abi, PPC64LE.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig,
          Spec.Poly1305.updatePost, Proof.Poly1305.updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig,
          Spec.Poly1305.updatePost, PPC64LE.abi, PPC64LE.argRegs, updateSat] [updateSat]
          using updateSat }

theorem finalizeScratch : Verified PPC64LE.target Impl.Poly1305.PPC64LE.finalize
    (Proof.Poly1305.finalizeScratchContract PPC64LE.abi) :=
  finalize_verified.of_implies
    { pre := by
        sig_implies_pre [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, PPC64LE.abi, PPC64LE.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, Proof.Poly1305.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Proof.Poly1305.finalizeScratchContract, Proof.Poly1305.finalizeScratchSig,
          Spec.Poly1305.finalizePost, PPC64LE.abi, PPC64LE.argRegs, finalizeSat] [finalizeSat]
          using finalizeSat }

theorem blocks : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 Impl.Poly1305.PPC64LE.blocks)
    (Proof.Poly1305.blocksContract PPC64LE.abi 160) :=
  PPC64LE.Verified.stackScratch (sig := Proof.Poly1305.blocksSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Proof.Poly1305.blocksPost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 160) blocksScratch (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Poly1305.blocksPost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem update : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r7 Impl.Poly1305.PPC64LE.update)
    (Spec.Poly1305.updateContract PPC64LE.abi 160) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Poly1305.updateSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.updatePost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 160) updateScratch (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Poly1305.updatePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 Impl.Poly1305.PPC64LE.finalize)
    (Spec.Poly1305.finalizeContract PPC64LE.abi 160) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Poly1305.finalizeSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.finalizePost PPC64LE.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 160) finalizeScratch (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Poly1305.finalizePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Poly1305.PPC64LE.Shared
