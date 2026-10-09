import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSponge
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSaved
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailHash

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

def frontRegs : List Reg := [.x5,.x6,.x7,.x8,.x10,.x16,.x19,.x20,.x21]

structure FrontPre (wlen : Nat) (s : State) : Prop where
  length : wlen=768 ∨ wlen=1024
  mu : ∀d n,d+n≤64→InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 d) n
  packed : ∀d n,d+n≤wlen→InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 d) n
  seed : ∀d n,d+n≤64→InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 d) n
  work : ∀d n,d+n≤2048→InRegions s.wr (s.gpr .x3+BitVec.ofNat 64 d) n
  muSep : (Region.mk (s.gpr .x0) 64).Disjoint ⟨s.gpr .x3,2048⟩
  packedSep : (Region.mk (s.gpr .x1) wlen).Disjoint ⟨s.gpr .x3,2048⟩
  seedSep : (Region.mk (s.gpr .x4) 64).Disjoint ⟨s.gpr .x3,2048⟩

def FrontPost (wlen : Nat) (σ s : State) : Prop :=
  RegKeep frontRegs σ s ∧ Saved σ s.mem ∧ Frame [⟨σ.gpr .x3,2048⟩] σ.mem s.mem ∧
  s.gpr .x19=σ.gpr .x3 ∧ s.gpr .x20=σ.gpr .x6 ∧ s.gpr .x21=σ.gpr .x2 ∧
  ∃A B,Pairs s A B ∧
    (∀d,d≤136→(Spec.Sha3.toBytes A).take d=Spec.MlDsa.H
      (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) d) ∧
    Spec.Sha3.bytesAt s.mem (bufferBase (σ.gpr .x3)) 640=
      Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640

theorem front_ok {s : State} {wlen : Nat} (hp : FrontPre wlen s) :
    WP isa (.seq (.block (pro++first++upperInit++([.addImm .x .x5 .x1 72] : List Instr)))
      (coreFor wlen)) s (FrontPost wlen s) := by
  rw [WP.seq_iff,List.append_assoc,List.append_assoc,WP.block_append_iff]
  refine WP.mono (pro_ok (fun i hi => hp.work _ _ (by omega))
    (fun i hi => hp.work _ _ (by omega))) fun a ⟨ha,hva,hsa,hfa,h19,h20,h21⟩ => ?_
  have hsub : (Region.mk (s.gpr .x3) 160).Sub ⟨s.gpr .x3,2048⟩ := by
    simpa using Offset.sub_base (s.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)
  have hconfig : CoreConfig a wlen (a.gpr .x1) (a.gpr .x19) := by
    refine ⟨hp.length,rfl,?_,?_,?_⟩
    · intro d n hn; rw [ha.rd,ha.wr,ha.gpr .x1 (by decide)]; exact hp.packed d n hn
    · intro d n hn; rw [ha.wr,h19]; exact hp.work d n hn
    · rw [ha.gpr .x1 (by decide),h19]
      exact hp.packedSep.sub_right (Offset.sub_base _ (d:=256) (n:=680) (k:=2048) (by decide))
  rw [← WP.seq_iff,← List.append_assoc]
  refine WP.mono (sponge_ok hconfig (fun i hi => by
    rw [ha.rd,ha.wr,ha.gpr .x0 (by decide)]; exact hp.mu _ _ (by omega)) (fun i hi => by
    rw [ha.rd,ha.wr,ha.gpr .x4 (by decide)]; exact hp.seed _ _ (by omega)))
    fun t ⟨ht,hft,hpt,hbytes⟩ => ?_
  rw [h19] at hft hbytes
  have hmu : Spec.Sha3.bytesAt a.mem (s.gpr .x0) 64=Spec.Sha3.bytesAt s.mem (s.gpr .x0) 64 := by
    apply Proof.MlKem.bytesAt_frame hfa ?_ (by decide)
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.muSep.sub_right hsub
  have hpw : Spec.Sha3.bytesAt a.mem (s.gpr .x1) wlen=Spec.Sha3.bytesAt s.mem (s.gpr .x1) wlen := by
    apply Proof.MlKem.bytesAt_frame hfa ?_ (by rcases hp.length with rfl|rfl <;> decide)
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.packedSep.sub_right hsub
  have hseed : seedBytes a.mem (s.gpr .x4) (s.gpr .x5)=seedBytes s.mem (s.gpr .x4) (s.gpr .x5) := by
    have hb : Spec.Sha3.bytesAt a.mem (s.gpr .x4) 64=Spec.Sha3.bytesAt s.mem (s.gpr .x4) 64 :=
      Proof.MlKem.bytesAt_frame hfa (by
        intro r hr; rcases List.mem_singleton.mp hr with rfl
        exact hp.seedSep.sub_right hsub) (by decide)
    unfold seedBytes
    rw [hb]
  refine ⟨(ha.trans ht).mono (by simp [frontRegs,spongeRegs]),hsa.keep_core hft,?_,
    (ht.gpr .x19 (by decide)).trans h19,(ht.gpr .x20 (by decide)).trans h20,
    (ht.gpr .x21 (by decide)).trans h21,_,_,hpt,?_,?_⟩
  · apply Frame.trans
    · exact hfa.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨_,by simp,hsub⟩)
    · exact hft.sub (by
        intro r hr
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨_,by simp,Offset.sub_base _ (d:=256) (n:=680) (k:=2048) (by decide)⟩)
  · intro d hd
    rw [lowRun_hash a.mem (a.gpr .x0) (a.gpr .x1) hp.length hd,
      ha.gpr .x0 (by decide),ha.gpr .x1 (by decide),hmu,hpw]
  · rw [ha.gpr .x4 (by decide),ha.gpr .x5 (by decide),hseed] at hbytes
    exact hbytes

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
