module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PBuild
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ReduceFromFrame
public import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Framework.Omega

/-! # Layout for native p construction and its saved generator exponent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.Generation.Layout

structure PConstructPlan where
  hash : HashPlan
  B : Addr
  Z : Nat
  len : Nat
  qb : List Byte
  width : len = 128 ∨ len = 256 ∨ len = 384
  base : hash.W 5 + BitVec.ofNat 64 arithmetic = B
  workspaceRoom : slot (len / 8) 16 ≤ Z
  qLength : qb.length = hash.len
  qPositive : 0 < Spec.Rsa.os2ip qb
  qFits : 2 * Spec.Rsa.os2ip qb < 2 ^ (64 * (len / 8))
  hashCount : hash.count = (8 * len - 1) / (8 * hash.len)
  hashRoom : len ≤ (hash.count + 1) * hash.len
  shapedSlot : hash.W 0 = off (hash.W 5) shaped
  shapedOutside : ∀ i < len, Z ≤ ofs B (off (off (hash.W 5) shaped) i)
  shapedHash : HashBufferSeparate hash.F hash.S (off (hash.W 5) shaped) len
  shapedInput : ∀ i < len, ∀ j < len,
    off (off hash.output ((hash.count + 1) * hash.len - len)) i ≠ off (off (hash.W 5) shaped) j
  frameHeaders : ∀ k < 37, ∀ j < 32,
    Mem.Sep (off hash.F (8 * k)) 8 (off B (8 * j)) 8
  frameOutside : ∀ k < 37, ∀ i < 8, Z ≤ ofs B (off (off hash.F (8 * k)) i)
  qHash : ∀ r ∈ ⟨off (hash.W 5) shaped, len⟩ :: hash.changed,
    (⟨off (hash.W 5) q, qb.length⟩ : Region).Disjoint r
  pOutside : ∀ i < len, Z ≤ ofs B (off (off (hash.W 5) p) i)
  exponentOutside : ∀ i < len, Z ≤ ofs B (off (off (hash.W 5) exponent) i)
  pExponent : ∀ i < len, ∀ j < len,
    off (off (hash.W 5) p) i ≠ off (off (hash.W 5) exponent) j
  frameArithmetic : ∀ r ∈ [⟨B, Z⟩, ⟨off (hash.W 5) p, len⟩, ⟨off (hash.W 5) exponent, len⟩],
    (⟨hash.F, frameBytes⟩ : Region).Disjoint r
  hashArithmetic : ∀ r ∈ [⟨B, Z⟩, ⟨off (hash.W 5) p, len⟩, ⟨off (hash.W 5) exponent, len⟩],
    (⟨hash.S, oRsa⟩ : Region).Disjoint r

def PConstructPlan.value (p : PConstructPlan) : Nat :=
  Spec.Dsa.pCandidate (8 * p.len) (8 * p.hash.len) (Spec.Rsa.os2ip p.qb) p.hash.seed p.hash.offset

def PConstructPlan.changed (p : PConstructPlan) : List Region :=
  (⟨off (p.hash.W 5) shaped, p.len⟩ :: p.hash.changed) ++
    [⟨p.B, p.Z⟩, ⟨off (p.hash.W 5) VG.Impl.Dsa.Generation.Layout.p, p.len⟩,
      ⟨off (p.hash.W 5) exponent, p.len⟩]

structure PConstructState (p : PConstructPlan) (H : Spec.Mgf1.Hash) (s : State) : Prop where
  hash : HashState p.hash H 0 s
  scratch : Scr s p.B p.Z
  qSource : Src s p.B p.Z (off (p.hash.W 5) q) p.qb
  shapedWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) shaped) i) 1
  pWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) VG.Impl.Dsa.Generation.Layout.p) i) 1
  exponentWrite : ∀ i < p.len, InRegions s.wr (off (off (p.hash.W 5) exponent) i) 1

end VG.Proof.Dsa.X86_64.Generation
