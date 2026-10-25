module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# SHA-256 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sha256/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sha256/Contract.lean`,
which the artifacts are emitted with.

The shared contract gives `compress` more scratch than this one uses (560
bytes, sized for x86-64's AVX2 compression function): the per-target
contract is first widened to that scratch (`Verified.widen`, the same code
running with the same trace and result), then moved to the shared one.
-/

@[expose] public section

namespace VG.Proof.Sha256.RISCV64.Shared

open _root_.VG.RISCV64

/-- `compressRISCV64` with 560 bytes of scratch. -/
def compressWide : Contract RISCV64.isa :=
  { Proof.Sha256.compressRISCV64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .a0, 32⟩
      let blocks : Region := ⟨s.gpr .a1, 64 * (s.gpr .a2).toNat⟩
      let scratch : Region := ⟨s.gpr .a3, 560⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub80 (a : Addr) : Region.Sub ⟨a, 80⟩ ⟨a, 560⟩ := Region.sub_prefix (by decide)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified RISCV64.target Impl.Sha256.RISCV64.compress compressWide :=
  Verified.widen Proof.Sha256.RISCV64.compress_verified
    (fun s => [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a3, 80⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub80 _), h₄, h₅.sub_right (sub80 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State :=
  { Proof.Sha256.RISCV64.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩] }

theorem compress :
    Verified RISCV64.target Impl.Sha256.RISCV64.compress (Spec.Sha256.compressContract RISCV64.abi) := by
  have hi : compressWide.Implies (Spec.Sha256.compressContract RISCV64.abi) := by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, compressWide,
      Proof.Sha256.compressRISCV64, RISCV64.abi, RISCV64.argRegs]
      [compressSat, Proof.Sha256.RISCV64.satState] using compressSat
  exact (compressWide_verified hi.sat_left).of_implies hi

end VG.Proof.Sha256.RISCV64.Shared
