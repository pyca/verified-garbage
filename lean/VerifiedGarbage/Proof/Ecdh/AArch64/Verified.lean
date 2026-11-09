module

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Ecdh.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
public import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Lit
meta import VerifiedGarbage.Impl.Ecdh.P256.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# ECDH over P-256 on AArch64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P256.law` and `invSound_of_toM`), so `exchange_ok`
gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p256 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p256 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 32 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 32 = List.replicate 32 0
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p256.C (dk p256 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p256.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

end VG.Proof.Ecdh.AArch64
