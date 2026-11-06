module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorePair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetryFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Impl.Rsa.X86.Inverse
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
/-! # Completed numeric key derivation retains the public output environment and a boolean validity mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem core_mask_bit {B : Addr} {n e p q : Nat} {m : Mem} (R : CoreOutcome B n e p q m) :
    slot m B kOk ≤ 1 := by
  unfold CoreOutcome at R
  split at R <;> omega

end VG.Proof.RsaKeyGen.X86.Key
