module

public import VerifiedGarbage.Proof.Sha256.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Sha256.RISCV64.Contract
public import VerifiedGarbage.Proof.Sha256.Stream

/-!
# SHA-256 on RISC-V: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written
against per-target contracts (`Proof/Sha256/RISCV64/Contract.lean`); these
theorems move them to the shared contracts of `Spec/Sha256/Contract.lean`,
which the artifacts are emitted with.

`update` and `finalize` keep their working space in a frame of their own,
of 144 bytes (`Impl.Sha256.RISCV64.Stream.frameBytes`), the `stack` of their
contracts. SHA-224 is SHA-256 from another initial hash value (`init224`),
with its digest the first 7 words of the final hash value (`finalize224`);
its `update` is SHA-256's.
-/

@[expose] public section

namespace VG.Proof.Sha256.RISCV64.Shared

open _root_.VG.RISCV64

theorem init :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.init (Spec.Sha256.initContract RISCV64.abi) :=
  Proof.Sha256.RISCV64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initFromRISCV64,
      Spec.Sha256.Repr, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.initSat] using Proof.Sha256.RISCV64.Stream.initSat)

theorem init224 :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.init224 (Spec.Sha256.init224Contract RISCV64.abi) :=
  Proof.Sha256.RISCV64.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initFromRISCV64,
      RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.initSat] using Proof.Sha256.RISCV64.Stream.initSat)

theorem update :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.update
      (Spec.Sha256.updateContract RISCV64.abi 144) :=
  Proof.Sha256.RISCV64.Stream.Update.update_verified.of_implies (by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Spec.Sha256.updatePost,
      Proof.Sha256.updateRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.Update.sat] using Proof.Sha256.RISCV64.Stream.Update.sat)

/-- `finalizeNRISCV64 8`, writing all of the final hash value. -/
def finalize8 : Contract RISCV64.isa :=
  { Proof.Sha256.finalizeNRISCV64 8 with
    post := fun s s' => ∀ iv m, Spec.Sha256.ReprFrom iv s.mem (s.gpr .a0) m →
      s.gpr .a1 = BitVec.ofNat 64 m.length →
      Spec.Sha256.bytesAt s'.mem (s.gpr .a2) 32 = Spec.Sha256.finalHash iv m }

theorem finalize8_verified :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize finalize8 :=
  Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.of_implies
    ⟨fun _ h => h, fun _ _ _ h iv m hr hc => by
      have := h iv m hr hc
      rwa [List.take_of_length_le (by rw [Proof.Sha256.RISCV64.Stream.Finalize.finalHash_length])]
        at this,
      fun _ _ _ _ h => h, Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.2.2⟩

theorem finalize :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize
      (Spec.Sha256.finalizeContract RISCV64.abi 144) :=
  finalize8_verified.of_implies (by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, Spec.Sha256.finalizePost,
      finalize8, Proof.Sha256.finalizeNRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.Finalize.sat] using Proof.Sha256.RISCV64.Stream.Finalize.sat 8)

/-- `finalizeNRISCV64 7`, for SHA-224's digest of the messages hashed from
its initial hash value. -/
def finalize224R : Contract RISCV64.isa :=
  { Proof.Sha256.finalizeNRISCV64 7 with
    post := fun s s' => ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (s.gpr .a0) m →
      s.gpr .a1 = BitVec.ofNat 64 m.length →
      Spec.Sha256.bytesAt s'.mem (s.gpr .a2) 28 = Spec.Sha256.sha224 m }

theorem finalize224R_verified :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize224 finalize224R :=
  Proof.Sha256.RISCV64.Stream.Finalize.finalize224_verified.of_implies
    ⟨fun _ h => h, fun _ _ _ h m hr hc => h _ m hr hc, fun _ _ _ _ h => h,
      Proof.Sha256.RISCV64.Stream.Finalize.finalize224_verified.2.2⟩

theorem finalize224 :
    Verified RISCV64.target Impl.Sha256.RISCV64.Stream.finalize224
      (Spec.Sha256.finalize224Contract RISCV64.abi 144) :=
  finalize224R_verified.of_implies (by
    contract_implies [Spec.Sha256.finalize224Contract, Spec.Sha256.finalize224Sig,
      Spec.Sha256.finalize224Post, finalize224R, Proof.Sha256.finalizeNRISCV64, RISCV64.abi,
      RISCV64.argRegs]
      [Proof.Sha256.RISCV64.Stream.Finalize.sat] using Proof.Sha256.RISCV64.Stream.Finalize.sat 7)

end VG.Proof.Sha256.RISCV64.Shared
