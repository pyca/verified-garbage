module

import VerifiedGarbage.Impl.MlKem.AArch64.Kem
public import VerifiedGarbage.Impl.MlKem.AArch64.AddSubW
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec12W
public import VerifiedGarbage.Impl.MlKem.AArch64.DotW
public import VerifiedGarbage.Impl.MlKem.AArch64.Widen16
public import VerifiedGarbage.Impl.MlKem.AArch64.Narrow16
public import VerifiedGarbage.Impl.MlKem.AArch64.Top

/-! # AArch64 ML-KEM with 16-bit coefficients: the operations on `scratch`

The sums, conversions, codecs and dot products of polynomials stored with 16 bits in the first
half of each 1024-byte slot of `scratch`, which `Kem16` and the decryption of
`Optimized.decryptM` use. -/

@[expose] public section
namespace VG.Impl.MlKem.AArch64.Kem16
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM

/-- `f ← f + g`, both stored with 16 bits in `scratch`. -/
def addWAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) AddSubW.addW

/-- The polynomial at `f`, stored with 16 bits, at `g` with 32. -/
def widenAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) Widen16.widen

/-- `ByteDecode₁₂` of the 384 bytes at `b + o` into `off`, with 16 bits. -/
def dec12WAt (b : Reg) (o off : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 b o ++ ptrTo .x1 .x28 off)) Codec12W.decW

/-- `ByteEncode₁₂` of the polynomial at `off`, stored with 16 bits, into `b + o`. -/
def enc12WAt (off : Nat) (b : Reg) (o : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 b o)) Codec12W.encW

/-- The polynomial at `f`, stored with 32 bits, at `g` with 16. -/
def narrowAt (f g : Nat) : Prog isa :=
  .seq (.block (ptrTo .x0 .x28 f ++ ptrTo .x1 .x28 g)) Narrow16.narrow

/-- The fused dot product into `out`, of terms in `scratch`. -/
def dotAt (out : Nat) (terms : List (Nat × Nat)) : Prog isa := DotW.dotW .x28 .x28 .x28 out terms

end VG.Impl.MlKem.AArch64.Kem16
