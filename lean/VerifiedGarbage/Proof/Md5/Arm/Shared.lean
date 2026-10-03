import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Md5.Arm.Compress
import VerifiedGarbage.Proof.Md5.Arm.Stream.Init
import VerifiedGarbage.Proof.Md5.Arm.Stream.Md
import VerifiedGarbage.Spec.Md5.Contract
import VerifiedGarbage.Proof.Md5.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# Md5 on Arm: the shared contracts

The proofs are written against per-target contracts
(`Proof/Md5/Arm/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Md5/Contract.lean`, which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's and PBKDF2's code calls) run
in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Md5.Arm.Shared

theorem compress :
    Verified Arm.target Impl.Md5.Arm.compress (Spec.Md5.compressContract Arm.abi) :=
  Proof.Md5.Arm.compress_verified.of_implies (by
    sig_implies [Spec.Md5.compressContract, Spec.Md5.compressSig,
      Proof.Md5.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.satState)

theorem init : Verified Arm.target Impl.Md5.Arm.Stream.init (Spec.Md5.initContract Arm.abi) :=
  Proof.Md5.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.Stream.initSat)

theorem updateScratch :
    Verified Arm.target Impl.Md5.Arm.Stream.update (Spec.Md5.updateScratchContract Arm.abi) :=
  Proof.Md5.Arm.Stream.Update.update_verified.of_implies (by
    sig_implies [Spec.Md5.updateScratchContract, Spec.Md5.updateScratchSig, Proof.Md5.updateArm,
      Proof.Md5.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.Stream.Update.sat, MdStream.Arm.Update.sat, Impl.Md5.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.Stream.Update.sat)

theorem finalizeScratch :
    Verified Arm.target Impl.Md5.Arm.Stream.finalize (Spec.Md5.finalizeScratchContract Arm.abi) :=
  Proof.Md5.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Md5.finalizeScratchContract, Spec.Md5.finalizeScratchSig,
      Proof.Md5.finalizeArm, Proof.Md5.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Md5.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat, MdStream.Arm.Finalize.satBase,
        Impl.Md5.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Md5.Arm.Stream.Finalize.sat)

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : Arm.State :=
  { MdStream.Arm.Update.sat Impl.Md5.Arm.Stream.params with
    rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 80⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 128 2 Impl.Md5.Arm.Stream.update)
    (Spec.Md5.updateContract Arm.abi 128) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 0) (bytes := 128) (m := 2)
    updateScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Md5.updatePost_local _)
    (by implies_sat [Spec.Md5.updateContract, Spec.Md5.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, MdStream.Arm.Update.sat, Impl.Md5.Arm.Stream.params, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : Arm.State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 80⟩, ⟨0x2000, 16⟩] }

theorem finalize : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 128 1 Impl.Md5.Arm.Stream.finalize)
    (Spec.Md5.finalizeContract Arm.abi 128) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 0) (bytes := 128) (m := 1)
    finalizeScratch (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Md5.finalizePost_local _)
    (by implies_sat [Spec.Md5.finalizeContract, Spec.Md5.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

end VG.Proof.Md5.Arm.Shared
