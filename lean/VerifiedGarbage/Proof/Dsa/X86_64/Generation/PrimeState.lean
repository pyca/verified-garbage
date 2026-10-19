module
public import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerPre
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

import VerifiedGarbage.Proof.Framework.Omega

/-! # State of DSA's shared Miller–Rabin witness loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64

structure PrimeParams where
  B : Addr
  p : Addr
  rp : Addr
  sp : Addr
  Z : Nat
  w : Nat
  N : Nat
  len : Nat
  drawBytes : Nat
  checks : Nat
  rand : List Byte
  dims : MrDims B Z w
  room : slot w 28 ≤ Z
  len2 : 2 ≤ len
  lenDraw : len ≤ drawBytes
  drawMax : drawBytes ≤ 1024
  drawMin : 8 ≤ drawBytes
  lenWords : (len + 7) / 8 ≤ w
  predBits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * len
  drawWidth : Spec.RsaKeyGen.witnessBytes N = drawBytes
  odd : N % 2 = 1
  n3 : 3 ≤ N
  checksMax : checks < 2 ^ 62
  randMax : rand.length < 2 ^ 64
  stackSize : 128 ≤ sp.toNat
  stackSeparate : Region.Disjoint ⟨B, Z⟩ (below sp 128)
  bufferSeparate : Region.Disjoint ⟨B, Z⟩ ⟨p, len⟩
  bufferOutside : ∀ i < len, Z ≤ ofs B (off p i)
  tapeBuffer : Region.Disjoint ⟨rp, rand.length⟩ ⟨p, len⟩
  tapeStack : Region.Disjoint ⟨rp, rand.length⟩ (below sp 128)

structure PrimeState (P : PrimeParams) (mi : BitVec 64) (used : Nat) (s : State) : Prop where
  ready : ModulusReady s P.B P.Z P.w mi P.N
  ptr : word s.mem P.B (8 * kOut) = P.p
  len : word s.mem P.B (8 * kUsedP) = BitVec.ofNat 64 P.len
  draw : word s.mem P.B (8 * kLen) = BitVec.ofNat 64 P.drawBytes
  rand : word s.mem P.B (8 * kRand) = P.rp
  randLen : word s.mem P.B (8 * kRandLen) = BitVec.ofNat 64 P.rand.length
  used : word s.mem P.B (8 * kUsed) = BitVec.ofNat 64 used
  checks : word s.mem P.B (8 * kChecks) = BitVec.ofNat 64 P.checks
  source : Src s P.B P.Z P.rp P.rand
  writable : ∀ i < P.len, InRegions s.wr (off P.p i) 1
  stack : s.gpr .rsp = P.sp

theorem PrimeState.callRoom {P : PrimeParams} {mi : BitVec 64} {used : Nat} {s : State}
    (h : PrimeState P mi used s) : Caller.Room s P.B P.Z :=
  ⟨by rw [h.stack]; exact P.stackSize, by rw [h.stack]; exact P.stackSeparate⟩

def primeRest (P : PrimeParams) (i uni used : Nat) : Option (Bool × List Byte) :=
  Spec.RsaKeyGen.loop
    (Spec.RsaKeyGen.mrStep P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1 (Spec.Rsa.splitTwos (P.N - 1)).2)
    (i, uni) (P.rand.drop used)

end VG.Proof.Dsa.X86_64.Generation
