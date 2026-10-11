import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Sm3.Arm.Compress
import VerifiedGarbage.Proof.Sm3.Arm.Stream.Init
import VerifiedGarbage.Proof.Sm3.Arm.Stream.Md
import VerifiedGarbage.Proof.Sm3.Scratch
import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Framework.Arm.StackScratch

/-!
# SM3 on ARMv7: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/Arm/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

The shared contract gives `compress` more scratch (576 bytes) than this one
uses (104): the per-target contract is first widened to that scratch
(`Verified.widen`, the same code running with the same trace and result),
then moved to the shared one.

`update` and `finalize` keep their working space (19 words: the compression
function's 104 bytes, then the registers the streaming code saves) in a frame
of their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sm3.Arm.Shared

open _root_.VG.Arm

/-- `compressArm` with 576 bytes of scratch. -/
def compressWide : Contract Arm.isa :=
  { Proof.Sm3.compressArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 32⟩
      let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
      let scratch : Region := ⟨State.addr (s.gpr .r3), 576⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 576 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub104 (a : Addr) : Region.Sub ⟨a, 104⟩ ⟨a, 576⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sm3.Arm.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 576⟩] }

theorem compressWide_verified : Verified Arm.target Impl.Sm3.Arm.compress compressWide :=
  Verified.widen Proof.Sm3.Arm.compress_verified
    (fun s => [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r3), 104⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub104 _), h₄, h₅.sub_right (sub104 _), h₆, h₇,
        Nat.le_trans (Nat.add_le_add_left (by decide : 104 ≤ 576) _) h₈⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (by
      refine ⟨compressSat, rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
      first
      | exact Offset.disjoint_of_le (by decide) (by decide)
      | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide)))

theorem compress :
    Verified Arm.target Impl.Sm3.Arm.compress (Spec.Sm3.compressContract Arm.abi) :=
  compressWide_verified.of_implies (by
    contract_implies [Spec.Sm3.compressContract, Spec.Sm3.compressSig, compressWide,
      Proof.Sm3.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [compressSat, Proof.Sm3.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using compressSat)

theorem init : Verified Arm.target Impl.Sm3.Arm.Stream.init (Spec.Sm3.initContract Arm.abi) :=
  Proof.Sm3.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sm3.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sm3.Arm.Stream.initSat)

theorem updateScratch :
    Verified Arm.target Impl.Sm3.Arm.Stream.update (Proof.Sm3.updateScratchContract Arm.abi 19) :=
  Proof.Sm3.Arm.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateArm, Proof.Sm3.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
      [Proof.Sm3.Arm.Stream.Update.sat, MdStream.Arm.Update.sat, Impl.Sm3.Arm.Stream.params,
        Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.Sm3.Arm.Stream.Update.sat)

theorem finalizeScratch :
    Verified Arm.target Impl.Sm3.Arm.Stream.finalize (Proof.Sm3.finalizeScratchContract Arm.abi 19) :=
  Proof.Sm3.Arm.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig,
      Spec.Sm3.finalizeSig, Proof.Sm3.finalizeArm, Proof.Sm3.countArm, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sm3.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat, MdStream.Arm.Finalize.satBase,
        Impl.Sm3.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sm3.Arm.Stream.Finalize.sat)

/-- A state satisfying `update`'s precondition. -/
def updateFrameSat : Arm.State :=
  { MdStream.Arm.Update.sat Impl.Sm3.Arm.Stream.params with
    rd := [⟨0, 0⟩, ⟨0x4000, 8⟩], wr := [⟨0x1000, 96⟩] }

theorem update : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 168 2 Impl.Sm3.Arm.Stream.update)
    (Spec.Sm3.updateContract Arm.abi 168) :=
  Arm.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 19)
    (stack := 0) (bytes := 168) (m := 2)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.updatePost_local _)
    (by implies_sat [Spec.Sm3.updateContract, Spec.Sm3.updateSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [updateFrameSat, MdStream.Arm.Update.sat, Impl.Sm3.Arm.Stream.params, Arm.stackArg,
        Arm.stackArgAddr, Mem.readW, Mem.read] using updateFrameSat)

/-- A state satisfying `finalize`'s precondition. -/
def finalizeFrameSat : Arm.State :=
  { MdStream.Arm.Finalize.satBase with rd := [⟨0x5000, 4⟩], wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩] }

theorem finalize : Verified Arm.target
    (Impl.StackScratch.Arm.withStackScratch 168 1 Impl.Sm3.Arm.Stream.finalize)
    (Spec.Sm3.finalizeContract Arm.abi 168) :=
  Arm.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 19)
    (stack := 0) (bytes := 168) (m := 1)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.finalizePost_local _)
    (by implies_sat [Spec.Sm3.finalizeContract, Spec.Sm3.finalizeSig, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [finalizeFrameSat, MdStream.Arm.Finalize.satBase, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
        Mem.read] using finalizeFrameSat)

end VG.Proof.Sm3.Arm.Shared
