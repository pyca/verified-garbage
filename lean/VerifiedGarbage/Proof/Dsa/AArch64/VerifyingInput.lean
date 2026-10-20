module

public import VerifiedGarbage.Proof.Dsa.AArch64.InitializedFields
public import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSpec
public import VerifiedGarbage.Proof.Dsa.AArch64.CoreVerify

/-! # External input layout for the complete DSA verification program -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure VerifyingInput where
  base : Addr
  digestPointer : Addr
  pLen : Nat
  qLen : Nat
  key : List Byte
  signature : List Byte
  digest : List Byte
  lengths : Spec.Dsa.lengthsValid pLen qLen
  keyLength : key.length = 3 * pLen + qLen
  signatureLength : signature.length = 2 * qLen
  digestBound : digest.length < 2 ^ 64

def VerifyingInput.components (p : VerifyingInput) : PackedComponents p.pLen p.qLen :=
  packedComponents p.pLen p.qLen p.key (Nat.le_of_eq p.keyLength.symm)

abbrev VerifyingInput.prefixLength (p : VerifyingInput) : Nat :=
  min p.digest.length (VG.Proof.Dsa.significant p.components.q).1

abbrev VerifyingInput.accepted (p : VerifyingInput) : Bool :=
  shapeAccepted p.components.p p.components.q
    (by rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega)
    (by rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega)

def VerifyingInput.values (p : VerifyingInput) : VerifyValues :=
  ⟨p.components.g, p.components.y, p.signature.take p.qLen, p.signature.drop p.qLen,
    p.digest.take (VG.Proof.Dsa.significant p.components.q).1⟩

structure VerifyingPre (p : VerifyingInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  pLength : s.gpr .x2 = BitVec.ofNat 64 p.pLen
  stackRead : InRegions (s.rd ++ s.wr) s.sp 8
  qLength : s.gpr .x3 = BitVec.ofNat 64 p.qLen
  digestPointer : s.gpr .x6 = p.digestPointer
  digestLength : s.gpr .x7 = BitVec.ofNat 64 p.digest.length
  base : word s.mem s.sp 0 = p.base
  keySource : Src s p.base usedBytes (s.gpr .x0) p.key
  signatureSource : Src s p.base usedBytes (s.gpr .x4) p.signature
  digestSource : Src s p.base usedBytes p.digestPointer p.digest

def VerifyingInput.layout (p : VerifyingInput) (original : State) (hp : original.gpr .x2 = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .x3 = BitVec.ofNat 64 p.qLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.components.p
  subgroup := Spec.Dsa.decodeBE p.components.q
  pInverse := 0
  qInverse := 0
  fields := verifyFieldValues original p.digestPointer
    (BitVec.ofNat 64 p.digest.length) (BitVec.ofNat 64 p.prefixLength) p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := hq

end VG.Proof.Dsa.AArch64
