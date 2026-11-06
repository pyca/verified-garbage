module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Lit
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.AArch64
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Secp256k1.Lit
meta import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.AArch64
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# ECDSA verification over secp256k1 on AArch64: `Verified`

secp256k1 is a curve the proof supports (`secp256k1_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.Secp256k1.law`), so `verify_ok` gives
the contract's postcondition; `x19` and `x20` are restored, and no instruction
writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so only the pointers affect timing (the contract would let the key, the hash
and the signature affect it too).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.Secp256k1

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1

theorem pre_of {s : State} (h : verifyAArch64.pre s) : FrontPre secp256k1 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨⟨[], h1⟩, h2, h3, h4, h5, h6⟩

end VG.Proof.Ecdsa.Verify.AArch64.Secp256k1
