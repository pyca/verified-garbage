module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptPrfMemory

/-! # The invariant before each implicit-rejection PRF block -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt
open VG.Proof.RsaPkcs1Enc

structure PrfConfig where
  label : List Nat
  lenCode : List Instr
  length : Nat
  dst : Nat
  blocks : Nat
  extra : Nat
  extraLength : Nat
  blockPositive : 0 < blocks
  blockBound : blocks ≤ 256
  labelBound : label.length + 4 ≤ 16
  dstLow : 272 ≤ dst
  dstHigh : dst + 32 * blocks ≤ sHash
  extraLow : 208 ≤ extra
  extraHigh : extra + extraLength ≤ sHash
  separate : extra + extraLength ≤ dst ∨ dst + 32 * blocks ≤ extra

structure PrfInvariant (g : Geometry) (bs : Fin 9 → List Byte) (s0 : State)
    (R : PrfConfig) (key extra : List Byte) (i : Nat) (s : State) : Prop where
  context : Context g bs s
  frame : Frame (rejectionWrites g) s0.mem s.mem
  keep : Keeps [.eax, .ecx, .edx, .ebx, .edi] s0 s
  counter : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oI) 32 = BitVec.ofNat 32 i
  blocks : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 oNB) 32 = BitVec.ofNat 32 R.blocks
  keyBytes : Spec.Rsa.bytesAt s.mem (g.scratch sKDK 32).base 32 = key
  extraBytes : Spec.Rsa.bytesAt s.mem (g.scratch R.extra R.extraLength).base R.extraLength = extra
  prefixBytes : Spec.Rsa.bytesAt s.mem (g.scratch R.dst (32 * i)).base (32 * i) =
    (List.range i).flatMap (prfBlock key (R.label.map (BitVec.ofNat 8)) R.length)

end VG.Proof.RsaPkcs1Enc.X86.Dec
