import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotState
import VerifiedGarbage.Proof.Framework.CallLay

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Arith

open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlDsa.AArch64.Arith.Neon

/-- Each source polynomial is immutable and disjoint from the output. -/
structure Pre (n : Nat) (s : State) : Prop where
  output : pR (s.gpr .x0)∈s.wr
  input : ∀r∈[Reg.x1,.x2],∀j<n,InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (1024*j)) 1024
  apart : ∀r∈[Reg.x1,.x2],∀j<n,(pR (s.gpr r+BitVec.ofNat 64 (1024*j))).Disjoint (pR (s.gpr .x0))
  bound : ∀r∈[Reg.x1,.x2],∀j<n,∀k<256,
    (coeffAt s.mem (s.gpr r+BitVec.ofNat 64 (1024*j)) k).toNat<3*q

def inputWord (s : State) (r : Reg) (j k : Nat) : BitVec 32 :=
  coeffAt s.mem (s.gpr r+BitVec.ofNat 64 (1024*j)) k

theorem input_current {s₀ s : State} {v : Nat→Nat} {i n : Nat} (hi : i<64)
    (hp : Pre n s₀) (h : Inv s₀ v i s) {r : Reg} (hr : r∈[Reg.x1,.x2]) {j e : Nat}
    (hj : j<n) (he : e<4) : dotInput s r 0 j e=inputWord s₀ r j (4*i+e) := by
  have ha : s.gpr r=coeffAddr (s₀.gpr r) (4*i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.x1
    · exact h.x2
  have addr : s.gpr r+BitVec.ofNat 64 (1024*j+0)=
      coeffAddr (s₀.gpr r+BitVec.ofNat 64 (1024*j)) (4*i) := by
    rw [ha]
    simp only [coeffAddr,Nat.add_zero]
    bv_omega
  unfold dotInput inputWord
  rw [addr,VG.Proof.MlDsa.AArch64.Arith.Neon.vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq]
  exact coeffAt_frame h.frame (by intro r' hr';have hh:=List.mem_singleton.mp hr';subst r';exact hp.apart r hr j hj) (by change 4*i+e<256;omega)

theorem reads {s₀ s : State} {v : Nat→Nat} {i n : Nat} (hi : i<64)
    (hp : Pre n s₀) (h : Inv s₀ v i s) {r : Reg} (hr : r∈[Reg.x1,.x2]) {j : Nat}
    (hj : j<n) : InRegions (s.rd++s.wr) (s.gpr r+BitVec.ofNat 64 (1024*j)) 16 := by
  have ha : s.gpr r=coeffAddr (s₀.gpr r) (4*i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl
    · exact h.x1
    · exact h.x2
  rw [h.keep.rd,h.keep.wr,ha]
  have addr : coeffAddr (s₀.gpr r) (4*i)+BitVec.ofNat 64 (1024*j)=
      coeffAddr (s₀.gpr r+BitVec.ofNat 64 (1024*j)) (4*i) := by
    simp only [coeffAddr];bv_omega
  rw [addr]
  exact VG.CallLay.inRegions_sub (off:=4*(4*i)) (l:=16) (hp.input r hr j hj) (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
