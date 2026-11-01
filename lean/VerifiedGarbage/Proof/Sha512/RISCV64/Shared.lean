module

public import VerifiedGarbage.Proof.Sha512.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Sha512.RISCV64.Contract

/-!
# SHA-512 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sha512/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sha512/Contract.lean`,
which the artifacts are emitted with.

The shared contract gives `compress` more scratch than this one uses (1328
bytes, sized for x86-64's AVX2 compression function): the per-target
contract is first widened to that scratch (`Verified.widen`, the same code
running with the same trace and result), then moved to the shared one.
`update` and `finalize` keep their working space in a frame of their own,
of 208 bytes (`Impl.Sha512.RISCV64.Stream.frameBytes`), the `stack` of their
contracts. SHA-384, SHA-512/224 and SHA-512/256 are SHA-512 from other
initial hash values, with their digests the first 48, 28 and 32 bytes of the
final hash value; their `update` is SHA-512's.
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64.Shared

open _root_.VG.RISCV64

/-- `compressRISCV64` with 1328 bytes of scratch. -/
def compressWide : Contract RISCV64.isa :=
  { Proof.Sha512.compressRISCV64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .a0, 64⟩
      let blocks : Region := ⟨s.gpr .a1, 128 * (s.gpr .a2).toNat⟩
      let scratch : Region := ⟨s.gpr .a3, 1328⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub144 (a : Addr) : Region.Sub ⟨a, 144⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified RISCV64.target Impl.Sha512.RISCV64.compress compressWide :=
  Verified.widen Proof.Sha512.RISCV64.compress_verified
    (fun s => [⟨s.gpr .a0, 64⟩, ⟨s.gpr .a3, 144⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub144 _), h₄, h₅.sub_right (sub144 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State :=
  { Proof.Sha512.RISCV64.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

theorem compress :
    Verified RISCV64.target Impl.Sha512.RISCV64.compress (Proof.Sha512.compressContract RISCV64.abi) := by
  have hi : compressWide.Implies (Proof.Sha512.compressContract RISCV64.abi) := by
    contract_implies [Proof.Sha512.compressContract, Proof.Sha512.compressSig, compressWide,
      Proof.Sha512.compressRISCV64, RISCV64.abi, RISCV64.argRegs]
      [compressSat, Proof.Sha512.RISCV64.satState] using compressSat
  exact (compressWide_verified hi.sat_left).of_implies hi

/-- `init` from `iv`, with the shared contract. -/
theorem init_of {iv : Spec.Sha512.HashValue}
    (hv : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Proof.Sha512.initRISCV64 iv)) :
    Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Spec.Sha512.initContract RISCV64.abi iv) :=
  hv.of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.initSat] using Proof.Sha512.RISCV64.Stream.initSat)

theorem init384 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_384)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_384) :=
  init_of Proof.Sha512.RISCV64.Stream.init384_verified

theorem init512 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_512) :=
  init_of Proof.Sha512.RISCV64.Stream.init512_verified

theorem init512_224 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_224)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_512_224) :=
  init_of Proof.Sha512.RISCV64.Stream.init512_224_verified

theorem init512_256 : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith Spec.Sha512.H0_512_256)
    (Spec.Sha512.initContract RISCV64.abi Spec.Sha512.H0_512_256) :=
  init_of Proof.Sha512.RISCV64.Stream.init512_256_verified

theorem update :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.update
      (Spec.Sha512.updateContract RISCV64.abi 208) :=
  Proof.Sha512.RISCV64.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, Spec.Sha512.updatePost,
      Proof.Sha512.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Update.sat] using Proof.Sha512.RISCV64.Stream.Update.sat)

/-- `finalizeDRISCV64 64`, writing all of the final hash value. -/
def finalize64 : Contract RISCV64.isa :=
  { Proof.Sha512.finalizeDRISCV64 64 with
    post := fun s s' => ∀ iv m, Spec.Sha512.Repr iv s.mem (s.gpr .a0) m → m.length < 2 ^ 64 →
      s.gpr .a1 = BitVec.ofNat 64 m.length →
      Spec.Sha512.bytesAt s'.mem (s.gpr .a2) 64 = Spec.Sha512.finalHash iv m }

theorem finalize64_verified :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize finalize64 :=
  Proof.Sha512.RISCV64.Stream.Finalize.finalize64_verified.of_implies
    ⟨fun _ h => h, fun _ _ _ h iv m hr hl hc => by
      rw [h iv m hr hl hc]
      exact List.take_of_length_le (by
        unfold Spec.Sha512.finalHash
        exact Nat.le_of_eq (Proof.Sha512.RISCV64.Stream.Finalize.flat_length_all _)),
      fun _ _ _ _ h => h, Proof.Sha512.RISCV64.Stream.Finalize.finalize64_verified.2.2⟩

theorem finalize :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize
      (Spec.Sha512.finalizeContract RISCV64.abi 208) :=
  finalize64_verified.of_implies (by
    contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, Spec.Sha512.finalizePost,
      finalize64, Proof.Sha512.finalizeDRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 64)

/-! ## The truncated digests

`finalize384`, `finalize512_256` and `finalize512_224` write the first 48,
32 and 28 bytes of the final hash value (`finalizeDRISCV64`); for the
algorithm's initial hash value, that is its digest. -/

/-- `finalizeDRISCV64 D`, for the `D`-byte `digest` of the messages hashed
from `iv`. -/
def finalizeDigestR (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract RISCV64.isa :=
  { Proof.Sha512.finalizeDRISCV64 D with
    post := fun s s' => ∀ m, Spec.Sha512.Repr iv s.mem (s.gpr .a0) m → m.length < 2 ^ 64 →
      s.gpr .a1 = BitVec.ofNat 64 m.length → Spec.Sha512.bytesAt s'.mem (s.gpr .a2) D = digest m }

theorem finalizeDigestR_of {code : Prog isa} {D : Nat} {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte} (hv : Verified RISCV64.target code (Proof.Sha512.finalizeDRISCV64 D))
    (hdg : ∀ m, (Spec.Sha512.finalHash iv m).take D = digest m) :
    Verified RISCV64.target code (finalizeDigestR iv D digest) :=
  hv.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hl hc => (h iv m hr hl hc).trans (hdg m),
    fun _ _ _ _ h => h, hv.2.2⟩

theorem finalize384 :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize384
      (Spec.Sha512.finalizeDigestContract RISCV64.abi Spec.Sha512.H0_384 48 Spec.Sha512.sha384 208) :=
  (finalizeDigestR_of (iv := Spec.Sha512.H0_384) (digest := Spec.Sha512.sha384)
    Proof.Sha512.RISCV64.Stream.Finalize.finalize384_verified fun _ => rfl).of_implies (by
    contract_implies [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig,
      Spec.Sha512.finalizeDigestPost, finalizeDigestR, Proof.Sha512.finalizeDRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 48)

theorem finalize512_256 :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize512_256
      (Spec.Sha512.finalizeDigestContract RISCV64.abi Spec.Sha512.H0_512_256 32 Spec.Sha512.sha512_256
        208) :=
  (finalizeDigestR_of (iv := Spec.Sha512.H0_512_256) (digest := Spec.Sha512.sha512_256)
    Proof.Sha512.RISCV64.Stream.Finalize.finalize512_256_verified fun _ => rfl).of_implies (by
    contract_implies [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig,
      Spec.Sha512.finalizeDigestPost, finalizeDigestR, Proof.Sha512.finalizeDRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 32)

theorem finalize512_224 :
    Verified RISCV64.target Impl.Sha512.RISCV64.Stream.finalize512_224
      (Spec.Sha512.finalizeDigestContract RISCV64.abi Spec.Sha512.H0_512_224 28 Spec.Sha512.sha512_224
        208) :=
  (finalizeDigestR_of (iv := Spec.Sha512.H0_512_224) (digest := Spec.Sha512.sha512_224)
    Proof.Sha512.RISCV64.Stream.Finalize.finalize512_224_verified fun _ => rfl).of_implies (by
    contract_implies [Spec.Sha512.finalizeDigestContract, Spec.Sha512.finalizeDigestSig,
      Spec.Sha512.finalizeDigestPost, finalizeDigestR, Proof.Sha512.finalizeDRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha512.RISCV64.Stream.Finalize.sat] using Proof.Sha512.RISCV64.Stream.Finalize.sat 28)

end VG.Proof.Sha512.RISCV64.Shared
