module

public import VerifiedGarbage.Proof.Dsa.X86_64.InitializedFields
public import VerifiedGarbage.Proof.Dsa.X86_64.SourceSlices
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSpec
public import VerifiedGarbage.Proof.Dsa.X86_64.CoreSign
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import Mathlib.Tactic.Set

/-! # External input layout for the complete DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SigningInput where
  base : Addr
  digestPointer : Addr
  pLen : Nat
  qLen : Nat
  key : List Byte
  nonce : List Byte
  digest : List Byte
  lengths : Spec.Dsa.lengthsValid pLen qLen
  keyLength : key.length = 3 * pLen + 2 * qLen
  nonceLength : nonce.length = qLen
  digestBound : digest.length < 2 ^ 64

def SigningInput.components (p : SigningInput) : PackedComponents p.pLen p.qLen :=
  packedComponents p.pLen p.qLen p.key (by rw [p.keyLength]; omega)

abbrev SigningInput.prefixLength (p : SigningInput) : Nat :=
  min p.digest.length (VG.Proof.Dsa.significant p.components.q).1

abbrev SigningInput.accepted (p : SigningInput) : Bool :=
  shapeAccepted p.components.p p.components.q
    (by rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega)
    (by rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega)

def SigningInput.values (p : SigningInput) : SignValues :=
  ⟨p.components.g, p.nonce, p.components.x, p.digest.take (VG.Proof.Dsa.significant p.components.q).1⟩

structure SigningPre (p : SigningInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  pLength : s.gpr .r8 = BitVec.ofNat 64 p.pLen
  stackRead : ∀ j, 1 ≤ j → j ≤ 4 → InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * j)) 8
  stackSeparate : ∀ j, 1 ≤ j → j ≤ 4 → ∀ i < 8,
    usedBytes ≤ ofs p.base (off (s.gpr .rsp) (8 * j) + BitVec.ofNat 64 i)
  qLength : word s.mem (s.gpr .rsp) 8 = BitVec.ofNat 64 p.qLen
  digestPointer : word s.mem (s.gpr .rsp) 16 = p.digestPointer
  digestLength : word s.mem (s.gpr .rsp) 24 = BitVec.ofNat 64 p.digest.length
  base : word s.mem (s.gpr .rsp) 32 = p.base
  keySource : Src s p.base usedBytes (s.gpr .rdx) p.key
  nonceSource : Src s p.base usedBytes (s.gpr .r9) p.nonce
  digestSource : Src s p.base usedBytes p.digestPointer p.digest
  writable : ∀ i < 2 * p.qLen, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 i) 1
  separate : ∀ i < 2 * p.qLen, usedBytes ≤ ofs p.base (s.gpr .rdi + BitVec.ofNat 64 i)

def SigningInput.layout (p : SigningInput) (original : State) (hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.components.p
  subgroup := Spec.Dsa.decodeBE p.components.q
  pInverse := 0
  qInverse := 0
  fields := signFieldValues original (BitVec.ofNat 64 p.qLen) p.digestPointer
    (BitVec.ofNat 64 p.digest.length) (BitVec.ofNat 64 p.prefixLength) p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := rfl

end VG.Proof.Dsa.X86_64
