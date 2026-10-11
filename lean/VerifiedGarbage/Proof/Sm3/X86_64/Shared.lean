import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sm3.X86_64.Compress
import VerifiedGarbage.Proof.Sm3.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sm3.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sm3.Scratch
import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Sm3.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Inline

/-!
# SM3 on x86-64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sm3/X86_64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sm3/Contract.lean`, which the artifacts are emitted with.

The shared contract gives `compress` more scratch (576 bytes) than this one
uses (112): the per-target contract is first widened to that scratch
(`Verified.widen`, the same code running with the same trace and result),
then moved to the shared one.

`update` and `finalize` keep their working space (20 words: the compression
function's 112 bytes, then our caller's callee-saved registers) in a frame of
their own: they are `updateScratch` and `finalizeScratch` (the shared
contracts with the working space as an argument, `Proof/Sm3/Scratch.lean`)
run in a frame that allocates it (`Verified.stackScratch`).
-/

namespace VG.Proof.Sm3.X86_64.Shared

open _root_.VG.X86_64 in
/-- `compressX86_64` with 576 bytes of scratch. -/
def compressWide : Contract X86_64.isa :=
  { Proof.Sm3.compressX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 32⟩
      let blocks : Region := ⟨s.gpr .rsi, 64 * (s.gpr .rdx).toNat⟩
      let scratch : Region := ⟨s.gpr .rcx, 576⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 576⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWide.pre`. -/
def compressSat : X86_64.State := { Proof.Sm3.X86_64.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 576⟩] }

theorem compressWide_verified : Verified X86_64.target Impl.Sm3.X86_64.compress compressWide :=
  X86_64.Verified.widen Proof.Sm3.X86_64.compress_verified
    (fun s => [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rcx, 112⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _), h₆, h₇.sub_right (sub112 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    (by
      refine ⟨compressSat, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | exact Offset.disjoint_of_le (by decide) (by decide)
      | exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide)))

theorem compress :
    Verified X86_64.target Impl.Sm3.X86_64.compress (Spec.Sm3.compressContract X86_64.abi) :=
  compressWide_verified.of_implies (by
    contract_implies [Spec.Sm3.compressContract, Spec.Sm3.compressSig, compressWide,
      Proof.Sm3.compressX86_64, X86_64.abi, X86_64.argRegs]
      [compressSat, Proof.Sm3.X86_64.satState] using compressSat)

theorem init :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.init (Spec.Sm3.initContract X86_64.abi) :=
  Proof.Sm3.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.initSat] using Proof.Sm3.X86_64.Stream.initSat)

theorem updateScratch :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.update (Proof.Sm3.updateScratchContract X86_64.abi 20 8) :=
  Proof.Sm3.X86_64.Stream.Update.update_verified.of_implies (by
    sig_implies [Proof.Sm3.updateScratchContract, Proof.Sm3.updateScratchSig, Spec.Sm3.updateSig,
      Proof.Sm3.updateX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Sm3.X86_64.Stream.params] using Proof.Sm3.X86_64.Stream.Update.sat)

theorem finalizeScratch :
    Verified X86_64.target Impl.Sm3.X86_64.Stream.finalize (Proof.Sm3.finalizeScratchContract X86_64.abi 20 8) :=
  Proof.Sm3.X86_64.Stream.Finalize.finalize_verified.of_implies (by
    sig_implies [Proof.Sm3.finalizeScratchContract, Proof.Sm3.finalizeScratchSig, Spec.Sm3.finalizeSig,
      Proof.Sm3.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sm3.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Sm3.X86_64.Stream.params] using Proof.Sm3.X86_64.Stream.Finalize.sat)

theorem update : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 168 .r8 Impl.Sm3.X86_64.Stream.update)
    (Spec.Sm3.updateContract X86_64.abi (8 + 168)) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm3.updateSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 8) (bytes := 168)
    (by rw [← Proof.Sm3.updateScratchContract_eq]; exact updateScratch) (by decide) (by decide)
    (by decide) (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalize : Verified X86_64.target
    (Impl.StackScratch.X86_64.withStackScratch 168 .rcx Impl.Sm3.X86_64.Stream.finalize)
    (Spec.Sm3.finalizeContract X86_64.abi (8 + 168)) :=
  X86_64.Verified.stackScratch (sig := Spec.Sm3.finalizeSig) (nm := "scratch") (e := .u64) (n := 20)
    (stack := 8) (bytes := 168)
    (by rw [← Proof.Sm3.finalizeScratchContract_eq]; exact finalizeScratch) (by decide) (by decide)
    (by decide) (Code.all_of_allInstrs (by lit_decide)) (by lit_decide)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Sm3.X86_64.Shared
