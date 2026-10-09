import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSqueezeStep

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

structure SqueezeCfg where
 p : Addr
 q : Addr
 a : Addr
 b : Addr
 c : Addr
 d : Addr

def SqueezeCfg.out (c : SqueezeCfg) (i : Nat) : Addr :=
 if i=0 then c.a else if i=1 then c.b else if i=2 then c.c else c.d

def SqueezeCfg.at (c : SqueezeCfg) (i j : Nat) : Addr := c.out i+BitVec.ofNat 64 (136*j)
def SqueezeCfg.writes (c : SqueezeCfg) : List Region :=
 [pairR c.p,pairR c.q,⟨c.a,272⟩,⟨c.b,272⟩,⟨c.c,272⟩,⟨c.d,272⟩]
def SqueezeCfg.stepWrites (c : SqueezeCfg) (j : Nat) : List Region :=
 pairWrites c.p (c.at 0 j) (c.at 1 j)++pairWrites c.q (c.at 2 j) (c.at 3 j)

structure SqueezeLayout (σ : State) (c : SqueezeCfg) : Prop where
 left : ∀j<2,PairLayout σ c.p (c.at 0 j) (c.at 1 j)
 right : ∀j<2,PairLayout σ c.q (c.at 2 j) (c.at 3 j)
 apart : ∀j<2,∀r∈pairWrites c.p (c.at 0 j) (c.at 1 j),
   ∀t∈pairWrites c.q (c.at 2 j) (c.at 3 j),r.Disjoint t
 past : ∀i<4,∀k j,k<j→j<2→∀r∈c.stepWrites j,(rateR (c.at i k)).Disjoint r
 covers : ∀j<2,∀r∈c.stepWrites j,∃t∈c.writes,Region.Sub r t

structure SqueezeInv (σ s : State) (c : SqueezeCfg) (A : Nat→Spec.Sha3.State) (j : Nat) : Prop where
 bound : j≤2
 keep : RegKeep squeezeRegs σ s
 frame : Frame c.writes σ.mem s.mem
 first : PairAt s.mem c.p (Resident.permuted (A 0) j) (Resident.permuted (A 1) j)
 second : PairAt s.mem c.q (Resident.permuted (A 2) j) (Resident.permuted (A 3) j)
 streams : ∀i<4,Stream136 s.mem (c.out i) j (A i)
 r22 : s.gpr .x22=c.p
 r23 : s.gpr .x23=c.q
 r24 : s.gpr .x24=c.at 0 j
 r25 : s.gpr .x25=c.at 1 j
 r26 : s.gpr .x26=c.at 2 j
 r27 : s.gpr .x27=c.at 3 j
 count : s.gpr .x28=BitVec.ofNat 64 (2-j)

theorem SqueezeCfg.next (c : SqueezeCfg) (i j : Nat) : c.at i j+136=c.at i (j+1) := by
  simp only [SqueezeCfg.at,BitVec.add_assoc]
  change c.out i+(BitVec.ofNat 64 (136*j)+BitVec.ofNat 64 136)=_
  rw [←BitVec.ofNat_add,show 136*j+136=136*(j+1) by omega]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
