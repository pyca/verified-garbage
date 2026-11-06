module

public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
public import VerifiedGarbage.Proof.MlKem.PolyContract
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
/-! # Paired PRF call, both polynomial outputs and register restoration -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/OutCall.lean`, which only this module imported.

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

def pairWrites (p f g w : Addr) : List Region :=
 [savedR p,pairR p,rateR (p+400),rateR (p+528),X2.callR (p+1536),⟨f,1024⟩,⟨g,1024⟩,⟨w,1024⟩]
def sampled (m : Mem) (a : Addr) (n : Nat) (tr : Bool) : Poly :=
 let f := samplePolyCBD 2 (prf 2 (bytesAt m a 32) (BitVec.ofNat 8 n))
 if tr then ntt f else f

structure TailSetup (s : State) (p f g w : Addr) : Prop where
  pair : ∀i<25, InRegions (s.rd++s.wr) (wordAddr p i) 16
  rateA : ∀i<16, InRegions s.wr (outAddr (p+400) i) 8
  rateB : ∀i<16, InRegions s.wr (outAddr (p+528) i) 8
  call : Covers [pairR p,X2.callR (p+1536)] s.wr
  saved : ∀i<6, InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (1800+8*i)) 8
  cbdA : Covers [⟨p+400,128⟩,⟨f,1024⟩] (s.rd++s.wr)
  cbdB : Covers [⟨p+528,128⟩,⟨g,1024⟩] (s.rd++s.wr)
  nttA : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr
  nttB : Covers [⟨g,1024⟩,⟨w,1024⟩] s.wr
  bufA : (Region.mk (p+400) 128).Disjoint ⟨f,1024⟩
  bufB : (Region.mk (p+528) 128).Disjoint ⟨g,1024⟩
  next : ∀ r ∈ [Region.mk f 1024,⟨w,1024⟩], (Region.mk (p+528) 128).Disjoint r
  fg : (Region.mk f 1024).Disjoint ⟨g,1024⟩
  fw : (Region.mk f 1024).Disjoint ⟨w,1024⟩
  gw : (Region.mk g 1024).Disjoint ⟨w,1024⟩
  savedFar : ∀r∈[Region.mk f 1024,⟨g,1024⟩,⟨w,1024⟩], (savedR p).Disjoint r

end VG.Proof.MlKem.AArch64.Noise
