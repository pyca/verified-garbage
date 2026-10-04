import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Verified
import VerifiedGarbage.Impl.Blake2.Arm.Stream
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# BLAKE2b on ARMv7: the streaming functions

The generic ARMv7 streaming layer (`Proof/Blake2/Arm/Stream/`) instantiated
with BLAKE2b's parameters and its compression function (`compress_verified'`).
-/

namespace VG.Proof.Blake2.ArmB

open VG VG.Arm
open VG.Proof.Blake2.Arm.Stream (CalleeOk okB init_check_b init_verified update_verified
  finalize_verified initB_implies updateB_implies finalizeB_implies)

theorem calleeB : CalleeOk Spec.Blake2.b Impl.Blake2.Arm.B.compress :=
  ⟨compress_verified', by lit_decide⟩

theorem initB_verified :
    Verified Arm.target (Impl.Blake2.Arm.Stream.init Spec.Blake2.b) (Spec.Blake2.initBContract Arm.abi) :=
  init_verified okB init_check_b initB_implies

theorem updateB_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      (Spec.Blake2.updateBScratchContract Arm.abi 16) :=
  update_verified okB calleeB updateB_implies

theorem finalizeB_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress)
      (Spec.Blake2.finalizeBScratchContract Arm.abi 16) :=
  finalize_verified okB calleeB finalizeB_implies

/-! ## `update` and `finalize` with their working space in a frame of their own

The theorems above are of the streaming functions with their working space
as an argument (`update_scratch`, `finalize_scratch`); `update` and
`finalize` run them in a frame that allocates it (`Verified.stackScratch`).
-/

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : Arm.State :=
  { Proof.Blake2.Arm.Stream.updateSat 64 with rd := [⟨0x2000, 0⟩, ⟨0x5000, 8⟩], wr := [⟨0x1000, 192⟩] }

theorem updateB_framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 592 2 (Impl.Blake2.Arm.Stream.update (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress))
    (Spec.Blake2.updateBContract Arm.abi (16 + 592)) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 592) (m := 2)
    updateB_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blake2.updateBPost_local _)
    (by implies_sat [Spec.Blake2.updateBContract, Spec.Blake2.updateBSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, Proof.Blake2.Arm.Stream.updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : Arm.State :=
  { Proof.Blake2.Arm.Stream.finalizeSat 64 with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩] }

theorem finalizeB_framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 592 1 (Impl.Blake2.Arm.Stream.finalize (w := 64) "vg_blake2b_compress" Impl.Blake2.Arm.B.compress))
    (Spec.Blake2.finalizeBContract Arm.abi (16 + 592)) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 592) (m := 1)
    finalizeB_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blake2.finalizeBPost_local _)
    (by implies_sat [Spec.Blake2.finalizeBContract, Spec.Blake2.finalizeBSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, Proof.Blake2.Arm.Stream.finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

end VG.Proof.Blake2.ArmB
