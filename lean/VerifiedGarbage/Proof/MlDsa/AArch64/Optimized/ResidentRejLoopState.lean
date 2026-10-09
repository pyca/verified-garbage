import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFold
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdvance

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

abbrev parseRegs : List Reg := [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17]

structure StreamLayout (s : State) (b p : Addr) (n : Nat) : Prop where
 bound : n≤336
 read16 : ∀j,3*j+16≤3*n+4 → InRegions (s.rd++s.wr) (b+BitVec.ofNat 64 (3*j)) 16
 read4 : ∀j<n,InRegions (s.rd++s.wr) (b+BitVec.ofNat 64 (3*j)) 4
 write4 : ∀i<256,InRegions s.wr (coeffAddr p i) 4
 write16 : ∀i,i+4≤256 → InRegions s.wr (coeffAddr p i) 16
 disjoint : (⟨b,3*n+4⟩ : Region).Disjoint (polyR p)

def parsed (s : State) (b : Addr) (L : List Zq) (d : Nat) : List Zq :=
 rnFold L (candidateBytes s.mem b d)

structure ParseInv (s₀ : State) (b p : Addr) (n : Nat) (L : List Zq) (d : Nat) (s : State) : Prop where
 keep : Keep parseRegs s₀ s
 frame : Frame [polyR p] s₀.mem s.mem
 constants : Constants s
 bound : d≤n
 x2 : s.gpr .x2=b+BitVec.ofNat 64 (3*d)
 x3 : s.gpr .x3=coeffAddr p (parsed s₀ b L d).length
 x4 : (s.gpr .x4).toNat=256-(parsed s₀ b L d).length
 x5 : (s.gpr .x5).toNat=n-d
 mask : s.gpr .x10=0x7fffff
 zero : s.gpr .x0=0
 stored : Stored s.mem p (parsed s₀ b L d)

theorem ParseInv.byte {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    {i : Nat} (hi : i<3*n+4) : s.mem (b+BitVec.ofNat 64 i)=s₀.mem (b+BitVec.ofNat 64 i) := by
  exact h.frame _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hl.disjoint _ (Offset.contains_base b (by omega) (by have:=hl.bound; omega))

theorem ParseInv.candidate {s₀ s : State} {b p : Addr} {n d : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    {j : Nat} (hj : d+j<n) :
    candidate s.mem (s.gpr .x2+BitVec.ofNat 64 (3*j))=
      candidate s₀.mem (b+BitVec.ofNat 64 (3*(d+j))) := by
  rw [h.x2,Offset.add_add,←Nat.mul_add]
  unfold ResidentRej.candidate
  rw [h.byte hl (by omega)]
  have h1 : b+BitVec.ofNat 64 (3*(d+j))+1=b+BitVec.ofNat 64 (3*(d+j)+1) := by bv_omega
  have h2 : b+BitVec.ofNat 64 (3*(d+j))+2=b+BitVec.ofNat 64 (3*(d+j)+2) := by bv_omega
  rw [h1,h2,h.byte hl (by omega),h.byte hl (by omega)]

theorem ParseInv.batch {s₀ s : State} {b p : Addr} {n d k : Nat} {L : List Zq}
    (hl : StreamLayout s₀ b p n) (h : ParseInv s₀ b p n L d s)
    (hk : d+k≤n) (hout : (parsed s₀ b L d).length+k≤256) :
    candidateFold s.mem (s.gpr .x2) k (parsed s₀ b L d)=parsed s₀ b L (d+k) := by
  have hm : candidateFold s.mem (s.gpr .x2) k (parsed s₀ b L d)=
      candidateFold s₀.mem (b+BitVec.ofNat 64 (3*d)) k (parsed s₀ b L d) := by
    unfold candidateFold
    congr 1
    apply List.map_congr_left
    intro j hj
    rw [h.candidate hl (by have:=List.mem_range.mp hj; omega),Offset.add_add,←Nat.mul_add]
  rw [hm]
  exact candidateFold_continue _ _ _ _ _ hout

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
