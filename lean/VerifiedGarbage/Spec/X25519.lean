module

public import VerifiedGarbage.TCB.Mem
public import Wychelean.DH.X25519.Basic

/-! # X25519: byte adapters for Wychelean

**Trusted.** Wychelean specifies scalar multiplication on Curve25519 and its
quadratic twist, including RFC 7748 decoding and encoding. These definitions
only translate between its UInt8 vectors and the machine model's bytes.
-/

@[expose] public section

namespace VG.Spec.X25519

/-- Exactly 32 bytes from memory; clamping and masking belong to Wychelean. -/
def inputAt (m : Mem) (p : Addr) : Vector UInt8 32 :=
  Vector.ofFn fun i => UInt8.ofBitVec (m (p + BitVec.ofNat 64 i.val))

/-- A fixed-length Wychelean output as machine-model bytes. -/
def outputBytes (v : Vector UInt8 32) : List Byte :=
  v.toList.map UInt8.toBitVec

end VG.Spec.X25519
