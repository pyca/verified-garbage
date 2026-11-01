module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Sm3.RISCV64.Compress
public import VerifiedGarbage.Proof.Sm3.RISCV64.Stream
public import VerifiedGarbage.Spec.Sm3.Contract
public import VerifiedGarbage.Proof.Sm3.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# SM3 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sm3/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sm3/Contract.lean`,
which the artifacts are emitted with. The shared contract gives `compress`
more scratch than this one uses (576 bytes): the per-target contract is
first widened to it (`Verified.widen`). `update` and `finalize` keep their
working space in a frame of their own, of 144 bytes
(`Impl.MdStream.RISCV64.frameBytes`), the `stack` of their contracts.
-/

@[expose] public section

namespace VG.Proof.Sm3.RISCV64.Shared

open _root_.VG.RISCV64

/-- `compressRISCV64` with the shared contract's 576 bytes of scratch. -/
def compressWide : Contract RISCV64.isa :=
  { Proof.Sm3.compressRISCV64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .a0, 32⟩
      let blocks : Region := ⟨s.gpr .a1, 64 * (s.gpr .a2).toNat⟩
      let scratch : Region := ⟨s.gpr .a3, 576⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub80 (a : Addr) : Region.Sub ⟨a, 80⟩ ⟨a, 576⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State :=
  { Proof.Sm3.RISCV64.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 576⟩] }

theorem compressWide_verified :
    Verified RISCV64.target Impl.Sm3.RISCV64.compress compressWide :=
  Verified.widen Proof.Sm3.RISCV64.compress_verified
    (fun s => [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a3, 80⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub80 _), h₄, h₅.sub_right (sub80 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    ⟨compressSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide)⟩

theorem compress :
    Verified RISCV64.target Impl.Sm3.RISCV64.compress (Proof.Sm3.compressContract RISCV64.abi) :=
  compressWide_verified.of_implies (by
    contract_implies [Proof.Sm3.compressContract, Proof.Sm3.compressSig, compressWide,
      Proof.Sm3.compressRISCV64, RISCV64.abi, RISCV64.argRegs]
      [compressSat, Proof.Sm3.RISCV64.satState] using compressSat)

theorem init :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.init (Spec.Sm3.initContract RISCV64.abi) :=
  Proof.Sm3.RISCV64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sm3.initContract, Spec.Sm3.initSig, Proof.Sm3.initRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.initSat] using MdStream.RISCV64.initSat 96)

theorem update :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.update (Spec.Sm3.updateContract RISCV64.abi 144) :=
  Proof.Sm3.RISCV64.Stream.update_verified.of_implies (by
    contract_implies [Spec.Sm3.updateContract, Spec.Sm3.updateSig, Spec.Sm3.updatePost,
      Proof.Sm3.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Update.sat] using MdStream.RISCV64.Update.sat 32)

theorem finalize :
    Verified RISCV64.target Impl.Sm3.RISCV64.Stream.finalize (Spec.Sm3.finalizeContract RISCV64.abi 144) :=
  Proof.Sm3.RISCV64.Stream.finalize_verified.of_implies (by
    contract_implies [Spec.Sm3.finalizeContract, Spec.Sm3.finalizeSig, Spec.Sm3.finalizePost,
      Proof.Sm3.finalizeRISCV64, RISCV64.abi, RISCV64.argRegs]
      [MdStream.RISCV64.Finalize.sat] using MdStream.RISCV64.Finalize.sat 32 32)

end VG.Proof.Sm3.RISCV64.Shared
