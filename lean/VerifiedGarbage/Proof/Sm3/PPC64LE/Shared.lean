module

public import VerifiedGarbage.Proof.Sm3.PPC64LE.Compress
import VerifiedGarbage.Proof.Sm3.PPC64LE.Stream.Init
import VerifiedGarbage.Proof.Sm3.PPC64LE.Stream.Md
public import VerifiedGarbage.Proof.Sm3.Scratch
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.Proof.Sm3.Contract
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Sm3.PPC64LE.Stream

/-!
# SM3 on PPC64LE: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/PPC64LE/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

The shared contract gives `compress` more scratch (576 bytes) than this one
uses (112): the per-target contract is first widened to that scratch
(`Verified.widen`, the same code running with the same trace and result),
then moved to the shared one.

`update` and `finalize` keep their working space (20 words: the compression
function's 112 bytes, then the registers the streaming code saves) in a frame
of their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

@[expose] public section

namespace VG.Proof.Sm3.PPC64LE.Shared

open _root_.VG.PPC64LE

/-- `compressPPC64LE` with 576 bytes of scratch. -/
def compressWide : Contract PPC64LE.isa :=
  { Proof.Sm3.compressPPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 32⟩
      let blocks : Region := ⟨s.gpr .r4, 64 * (s.gpr .r5).toNat⟩
      let scratch : Region := ⟨s.gpr .r6, 576⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 576⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sm3.PPC64LE.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 576⟩] }

theorem compressWide_verified : Verified PPC64LE.target Impl.Sm3.PPC64LE.compress compressWide :=
  Verified.widen Proof.Sm3.PPC64LE.compress_verified
    (fun s => [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r6, 112⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (by
      refine ⟨compressSat, rfl, rfl, ?_, ?_, ?_⟩ <;>
      first
      | exact Offset.disjoint_of_le (by decide) (by decide)
      | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide)))

theorem compress :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.compress (Proof.Sm3.compressContract PPC64LE.abi) :=
  compressWide_verified.of_implies (by
    contract_implies [Proof.Sm3.compressContract, Proof.Sm3.compressSig, compressWide,
      Proof.Sm3.compressPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [compressSat, Proof.Sm3.PPC64LE.satState] using compressSat)

theorem init :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.init (Spec.Sm3.initContract PPC64LE.abi) :=
  Proof.Sm3.PPC64LE.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sm3.PPC64LE.Stream.initSat] using Proof.Sm3.PPC64LE.Stream.initSat)

theorem updateScratch :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.update (Proof.Sm3.updateScratchContract PPC64LE.abi 20 48) :=
  Proof.Sm3.PPC64LE.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sm3.PPC64LE.Stream.Update.sat,
        MdStream.PPC64LE.Update.sat, Impl.Sm3.PPC64LE.Stream.params] using Proof.Sm3.PPC64LE.Stream.Update.sat)

theorem finalizeScratch :
    Verified PPC64LE.target Impl.Sm3.PPC64LE.Stream.finalize (Proof.Sm3.finalizeScratchContract PPC64LE.abi 20 48) :=
  Proof.Sm3.PPC64LE.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sm3.PPC64LE.Stream.Finalize.sat,
        MdStream.PPC64LE.Finalize.satD, Impl.Sm3.PPC64LE.Stream.params] using Proof.Sm3.PPC64LE.Stream.Finalize.sat)

theorem update : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r7 Impl.Sm3.PPC64LE.Stream.update)
    (Spec.Sm3.updateContract PPC64LE.abi (48 + 192)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 48) (bytes := 192)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.updatePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified PPC64LE.target
    (Impl.StackScratch.PPC64LE.withStackScratch 192 .r6 Impl.Sm3.PPC64LE.Stream.finalize)
    (Spec.Sm3.finalizeContract PPC64LE.abi (48 + 192)) :=
  PPC64LE.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 48) (bytes := 192)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (fun _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm3.finalizePost_local _)
    (PPC64LE.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm3.PPC64LE.Shared
