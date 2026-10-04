import VerifiedGarbage.Proof.Blake2.Arm.CompressS.Compress
import VerifiedGarbage.Proof.Blake2.Arm.Stream.Verified
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# BLAKE2s on ARMv7: the streaming functions

The streaming layer (`Proof/Blake2/Arm/Stream/`) instantiated with BLAKE2s and
its compression function (`Proof/Blake2/Arm/CompressS/`), against the shared
contracts of `Spec/Blake2/Contract.lean`.
-/

namespace VG.Proof.Blake2.Arm.Blake2s

open VG VG.Arm
open VG.Proof.Blake2.Arm.Stream

theorem calleeS : CalleeOk Spec.Blake2.s Impl.Blake2.Arm.S.compress :=
  ⟨Proof.Blake2.ArmS.compress_verified', Proof.Blake2.ArmS.compress_noCalls⟩

theorem initS_verified :
    Verified Arm.target (Impl.Blake2.Arm.Stream.init Spec.Blake2.s) (Spec.Blake2.initSContract Arm.abi) :=
  init_verified okS init_check_s initS_implies

theorem updateS_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      (Spec.Blake2.updateSScratchContract Arm.abi 16) :=
  update_verified okS calleeS updateS_implies

theorem finalizeS_verified :
    Verified Arm.target
      (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress)
      (Spec.Blake2.finalizeSScratchContract Arm.abi 16) :=
  finalize_verified okS calleeS finalizeS_implies

/-! ## `update` and `finalize` with their working space in a frame of their own

The theorems above are of the streaming functions with their working space
as an argument (`update_scratch`, `finalize_scratch`); `update` and
`finalize` run them in a frame that allocates it (`Verified.stackScratch`).
-/

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : Arm.State :=
  { Proof.Blake2.Arm.Stream.updateSat 32 with rd := [⟨0x2000, 0⟩, ⟨0x5000, 8⟩], wr := [⟨0x1000, 96⟩] }

theorem updateS_framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 592 2 (Impl.Blake2.Arm.Stream.update (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress))
    (Spec.Blake2.updateSContract Arm.abi (16 + 592)) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 592) (m := 2)
    updateS_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blake2.updateSPost_local _)
    (by implies_sat [Spec.Blake2.updateSContract, Spec.Blake2.updateSSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, Proof.Blake2.Arm.Stream.updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : Arm.State :=
  { Proof.Blake2.Arm.Stream.finalizeSat 32 with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩] }

theorem finalizeS_framed : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 592 1 (Impl.Blake2.Arm.Stream.finalize (w := 32) "vg_blake2s_compress" Impl.Blake2.Arm.S.compress))
    (Spec.Blake2.finalizeSContract Arm.abi (16 + 592)) :=
  Arm.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 72) (stack := 16) (bytes := 592) (m := 1)
    finalizeS_verified (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Blake2.finalizeSPost_local _)
    (by implies_sat [Spec.Blake2.finalizeSContract, Spec.Blake2.finalizeSSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, Proof.Blake2.Arm.Stream.finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

end VG.Proof.Blake2.Arm.Blake2s
