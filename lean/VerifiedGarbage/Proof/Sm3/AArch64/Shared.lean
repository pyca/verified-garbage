import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Sm3.AArch64.Compress
import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sm3.AArch64.Stream.Md
import VerifiedGarbage.Proof.Sm3.Scratch
import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch

/-!
# SM3 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/AArch64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

The shared contract gives `compress` more scratch (576 bytes) than this one
uses (64): the per-target contract is first widened to that scratch
(`Verified.widen`, the same code running with the same trace and result),
then moved to the shared one.

`update` and `finalize` keep their working space (14 words: the compression
function's 64 bytes, then the registers the streaming code saves) in a frame
of their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sm3.AArch64.Shared

open _root_.VG.AArch64

/-- `compressAArch64` with 576 bytes of scratch. -/
def compressWide : Contract AArch64.isa :=
  { Proof.Sm3.compressAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 32⟩
      let blocks : Region := ⟨s.gpr .x1, 64 * (s.gpr .x2).toNat⟩
      let scratch : Region := ⟨s.gpr .x3, 576⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub64 (a : Addr) : Region.Sub ⟨a, 64⟩ ⟨a, 576⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sm3.AArch64.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 576⟩] }

theorem compressWide_verified : Verified AArch64.target Impl.Sm3.AArch64.compress compressWide :=
  Verified.widen Proof.Sm3.AArch64.compress_verified
    (fun s => [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x3, 64⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub64 _), h₄, h₅.sub_right (sub64 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (by
      refine ⟨compressSat, rfl, rfl, ?_, ?_, ?_⟩ <;>
      first
      | exact Offset.disjoint_of_le (by decide) (by decide)
      | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide)))

theorem compress :
    Verified AArch64.target Impl.Sm3.AArch64.compress (Spec.Sm3.compressContract AArch64.abi) :=
  compressWide_verified.of_implies (by
    contract_implies [Spec.Sm3.compressContract, Spec.Sm3.compressSig, compressWide,
      Proof.Sm3.compressAArch64, AArch64.abi, AArch64.argRegs]
      [compressSat, Proof.Sm3.AArch64.satState] using compressSat)

theorem init :
    Verified AArch64.target Impl.Sm3.AArch64.Stream.init (Spec.Sm3.initContract AArch64.abi) :=
  Proof.Sm3.AArch64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.initSat] using Proof.Sm3.AArch64.Stream.initSat)

theorem updateScratch :
    Verified AArch64.target Impl.Sm3.AArch64.Stream.update (Proof.Sm3.updateScratchContract AArch64.abi 14 16) :=
  Proof.Sm3.AArch64.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.Update.sat,
        MdStream.AArch64.Update.sat, Impl.Sm3.AArch64.Stream.params] using Proof.Sm3.AArch64.Stream.Update.sat)

theorem finalizeScratch :
    Verified AArch64.target Impl.Sm3.AArch64.Stream.finalize (Proof.Sm3.finalizeScratchContract AArch64.abi 14 16) :=
  Proof.Sm3.AArch64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [Proof.Sm3.AArch64.Stream.Finalize.sat,
        MdStream.AArch64.Finalize.sat, Impl.Sm3.AArch64.Stream.params] using Proof.Sm3.AArch64.Stream.Finalize.sat)

theorem update : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 Impl.Sm3.AArch64.Stream.update)
    (Spec.Sm3.updateContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 14)
    (stack := 16) (bytes := 112)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 Impl.Sm3.AArch64.Stream.finalize)
    (Spec.Sm3.finalizeContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 14)
    (stack := 16) (bytes := 112)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm3.AArch64.Shared
