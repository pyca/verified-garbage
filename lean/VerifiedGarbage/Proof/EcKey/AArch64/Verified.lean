module

public import VerifiedGarbage.Proof.EcKey.AArch64.Main
public import VerifiedGarbage.Proof.EcKey.AArch64.Contract
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
public import VerifiedGarbage.Impl.EcKey.P256.AArch64
meta import VerifiedGarbage.Proof.EcKey.AArch64.Main
meta import VerifiedGarbage.Proof.EcKey.AArch64.Contract
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
meta import VerifiedGarbage.Proof.EcKey.AArch64.Lit
meta import VerifiedGarbage.Impl.EcKey.P256.AArch64

/-!
# P-256 public keys on AArch64: `Verified`

P-256 is a curve the proof supports (`p256_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P256.law` and `invSound_of_toM`), so `publicKey_ok`
gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter.
-/

@[expose] public section

namespace VG.Proof.EcKey.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.EcKey.AArch64
open VG.Proof.Ecdsa.AArch64

theorem pre_of {s : State} (h : pkAArch64.pre s) : PkPre p256 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, held, fit, hdw⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, ⟨by rw [h1]; simp, held, fit, hdw _ (by simp)⟩⟩

theorem post_of {s s' : State} (h : PkPost p256 s s') : pkAArch64.post s s' := by
  unfold PkPost at h
  show match pk s.mem (s.gpr .x1) with
    | some (.affine x y) => (s'.gpr .x0).setWidth 32 = 1 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 65 = Spec.EcKey.encodePoint (.affine x y)
    | _ => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 65 = List.replicate 65 0
  revert h
  generalize hq : pk s.mem (s.gpr .x1) = q
  rw [show Spec.EcKey.publicKey p256.C (dk p256 s) = pk s.mem (s.gpr .x1) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

end VG.Proof.EcKey.AArch64
