import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackCode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackSpec

namespace VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Round
open VG.Proof.MlDsa.Arith (polyRegion)
open HighPack (packWidth)
open VG.Proof.MlKem.AArch64 (Keep)

structure Pre (g : Nat) (s : State) : Prop where
  gamma : arg32 s .x3=g
  reduced : Reduced s.mem (s.gpr .x2)
  input : InRegions (s.rd++s.wr) (s.gpr .x2) 1024
  hints : InRegions (s.rd++s.wr) (s.gpr .x1) 1024
  output : InRegions s.wr (s.gpr .x0) (32*packWidth g)
  sep : (polyRegion (s.gpr .x2)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩
  hintSep : (polyRegion (s.gpr .x1)).Disjoint ⟨s.gpr .x0,32*packWidth g⟩

structure Post (g : Nat) (s t : State) : Prop where
  frame : Frame [⟨s.gpr .x0,32*packWidth g⟩] s.mem t.mem
  bytes : VG.Spec.Sha3.bytesAt t.mem (s.gpr .x0) (32*packWidth g)=
    packed g s.mem (s.gpr .x1) (s.gpr .x2)

private theorem subregion {rs : List Region} {p : Addr} {len off n : Nat}
    (h : InRegions rs p len) (hb : off+n≤len) (ho : len<2^64) :
    InRegions rs (p+BitVec.ofNat 64 off) n := by
  obtain ⟨r,hr,hp⟩ := h
  exact ⟨r,hr,VG.CallLay.contains_trans hp hb ho⟩

/-- Dispatch accepts the ABI's 32-bit gamma argument; its upper register bits are irrelevant. -/
theorem prog_ok {g : Nat} (hg : IsG g) {s : State} (hp : Pre g s) :
    WP isa Impl.MlDsa.AArch64.Optimized.UseHintPack.prog s (Post g s) := by
  unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
  apply WP.seq
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x4,.x5,.x1]
    (Q:=fun a=>a.gpr .x4=s.gpr .x1 ∧ a.gpr .x5=s.gpr .x2 ∧
      a.gpr .x1=s.gpr .x0 ∧ a.mem=s.mem)
    (by arun) (by decide +kernel) (hv:=rfl)) fun a ha=>?_
  apply zext_ok
  apply onGamma_ok (by decide : Reg.x6≠.x3)
  · rw [zextS_toNat]
    have hh : arg32 a .x3=g := by
      unfold arg32; rw [ha.2.get .x3 (by decide)]; exact hp.gamma
    rw [hh]; exact hg
  · intro g' he b hk hm
    have hsame : g'=g := by
      rw [zextS_toNat] at he
      unfold arg32 at he
      rw [ha.2.get .x3 (by decide)] at he
      exact he.symm.trans hp.gamma
    rw [hsame]
    have bm : b.mem=s.mem := hm.trans ha.1.2.2.2
    have br : b.rd=s.rd := hk.rd.trans ha.2.rd
    have bw : b.wr=s.wr := hk.wr.trans ha.2.wr
    have bh : b.gpr .x4=s.gpr .x1 := by
      rw [hk.get .x4 (by decide),zextS_other _ (by decide)]; exact ha.1.1
    have bi : b.gpr .x5=s.gpr .x2 := by
      rw [hk.get .x5 (by decide),zextS_other _ (by decide)]; exact ha.1.2.1
    have bo : b.gpr .x1=s.gpr .x0 := by
      rw [hk.get .x1 (by decide),zextS_other _ (by decide)]; exact ha.1.2.2.1
    refine WP.mono (code_ok hg b (by rw [bm,bi];exact hp.reduced)
      (by rw [bi,bo];exact hp.sep) (by rw [bh,bo];exact hp.hintSep) ?_ ?_ ?_ ?_) fun t ht=>?_
    · intro j hj k hk
      rw [br,bw,bh,Offset.add_add]
      exact subregion hp.hints (by omega) (by omega)
    · intro j hj k hk
      rw [br,bw,bi,Offset.add_add]
      exact subregion hp.input (by omega) (by omega)
    · intro j hj
      rw [bw,bo]
      apply subregion hp.output
      · rcases hg with rfl|rfl
        · change 8*j+8≤128;omega
        · change 12*j+8≤192;omega
      · rcases hg with rfl|rfl <;> decide
    · intro j hj hw
      rw [bw,bo]
      change InRegions s.wr ((s.gpr .x0+BitVec.ofNat 64 (2*packWidth g*j))+BitVec.ofNat 64 8) 4
      rw [Offset.add_add]
      apply subregion hp.output
      · rw [hw];omega
      · rw [hw];omega
    · exact ⟨by simpa only [bm,bo] using ht.frame,
        by simpa only [bm,bo,bh,bi] using ht.bytes⟩

end VG.Proof.MlDsa.AArch64.Optimized.UseHintPack
