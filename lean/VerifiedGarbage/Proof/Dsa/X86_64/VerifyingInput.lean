module

public import VerifiedGarbage.Proof.Dsa.X86_64.InitializedFields
public import VerifiedGarbage.Proof.Dsa.X86_64.SourceSlices
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSpec
public import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerify
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # External input layout for the complete DSA verification program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  pLength : s.gpr .rdx = BitVec.ofNat 64 p.pLen
  stackRead : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * j)) 8
  stackSeparate : ∀ j, 1 ≤ j → j ≤ 3 → ∀ i < 8,
    usedBytes ≤ ofs p.base (off (s.gpr .rsp) (8 * j) + BitVec.ofNat 64 i)
  qLength : s.gpr .rcx = BitVec.ofNat 64 p.qLen
  digestPointer : word s.mem (s.gpr .rsp) 8 = p.digestPointer
  digestLength : word s.mem (s.gpr .rsp) 16 = BitVec.ofNat 64 p.digest.length
  base : word s.mem (s.gpr .rsp) 24 = p.base
  keySource : Src s p.base usedBytes (s.gpr .rdi) p.key
  signatureSource : Src s p.base usedBytes (s.gpr .r8) p.signature
  digestSource : Src s p.base usedBytes p.digestPointer p.digest

def VerifyingInput.layout (p : VerifyingInput) (original : State) (hp : original.gpr .rdx = BitVec.ofNat 64 p.pLen)
    (hq : original.gpr .rcx = BitVec.ofNat 64 p.qLen) : ExecutionLayout where
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

end VG.Proof.Dsa.X86_64
