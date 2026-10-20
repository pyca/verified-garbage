module
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeSetup

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MillerRabin.AArch64.Contract

/-! # State of DSA's shared Miller–Rabin witness loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64

structure PrimeParams where
  B : Addr
  p : Addr
  rp : Addr
  Z : Nat
  w : Nat
  N : Nat
  len : Nat
  drawBytes : Nat
  checks : Nat
  rand : List Byte
  w4 : 4 ≤ w
  w128 : w ≤ 128
  room : slot w 28 ≤ Z
  len2 : 2 ≤ len
  lenDraw : len ≤ drawBytes
  drawMax : drawBytes ≤ 1024
  drawMin : 8 ≤ drawBytes
  lenWords : len ≤ 8 * w
  predBits : Spec.RsaKeyGen.bitLength (N - 1) = 8 * len
  drawWidth : Spec.RsaKeyGen.witnessBytes N = drawBytes
  odd : N % 2 = 1
  n3 : 3 ≤ N
  checksMax : checks < 2 ^ 62
  randMax : rand.length < 2 ^ 64
  bufferSeparate : Region.Disjoint ⟨B, Z⟩ ⟨p, len⟩
  bufferOutside : ∀ i < len, Z ≤ ofs B (off p i)
  tapeBuffer : Region.Disjoint ⟨rp, rand.length⟩ ⟨p, len⟩

structure PrimeState (P : PrimeParams) (used : Nat) (s : State) : Prop where
  ready : ModulusReady s P.B P.Z P.w P.N
  ptr : word s.mem P.B (8 * kOut) = P.p
  len : word s.mem P.B (8 * kUsedP) = BitVec.ofNat 64 P.len
  draw : word s.mem P.B (8 * kLen) = BitVec.ofNat 64 P.drawBytes
  rand : word s.mem P.B (8 * kRand) = P.rp
  randLen : word s.mem P.B (8 * kRandLen) = BitVec.ofNat 64 P.rand.length
  used : word s.mem P.B (8 * kUsed) = BitVec.ofNat 64 used
  checks : word s.mem P.B (8 * kChecks) = BitVec.ofNat 64 P.checks
  source : Src s P.B P.Z P.rp P.rand
  writable : ∀ i < P.len, InRegions s.wr (off P.p i) 1

def primeRest (P : PrimeParams) (i uni used : Nat) : Option (Bool × List Byte) :=
  Spec.RsaKeyGen.loop
    (Spec.RsaKeyGen.mrStep P.N P.checks (Spec.Rsa.splitTwos (P.N - 1)).1 (Spec.Rsa.splitTwos (P.N - 1)).2)
    (i, uni) (P.rand.drop used)

end VG.Proof.Dsa.AArch64.Generation
