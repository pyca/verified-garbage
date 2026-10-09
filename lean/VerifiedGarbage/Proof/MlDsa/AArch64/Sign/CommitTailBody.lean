import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailOutputStage
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailParse

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.Pack (polyRegion)
open VG.Spec.MlDsa

structure Pre (wlen olen : Nat) (s : State) : Prop extends FrontPre wlen s where
  outLength : olen=48 ∨ olen=64
  output : ∀d n,d+n≤olen→InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 d) n
  cache : InRegions s.wr (s.gpr .x6) 1024
  readWork : ∀d n,d+n≤2048→InRegions (s.rd++s.wr) (s.gpr .x3+BitVec.ofNat 64 d) n
  outWork : (Region.mk (s.gpr .x2) olen).Disjoint ⟨s.gpr .x3,2048⟩
  cacheWork : (polyRegion (s.gpr .x6)).Disjoint ⟨s.gpr .x3,2048⟩
  outCache : (Region.mk (s.gpr .x2) olen).Disjoint (polyRegion (s.gpr .x6))

def bodyRegs : List Reg := [.x0,.x1,.x2,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x19,.x20,.x21]
def writes (s : State) (olen : Nat) : List Region :=
  [⟨s.gpr .x3,2048⟩,⟨s.gpr .x2,olen⟩,polyRegion (s.gpr .x6)]

def BodyPost (wlen olen : Nat) (σ s : State) : Prop :=
  RegKeep bodyRegs σ s ∧ Saved σ s.mem ∧ Frame (writes σ olen) σ.mem s.mem ∧ s.gpr .x19=σ.gpr .x3 ∧
  Spec.Sha3.bytesAt s.mem (σ.gpr .x2) olen=H
    (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
  PolyIs s.mem (σ.gpr .x6) (toRq (bitUnpack (H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288))

theorem body_ok {σ s : State} {wlen olen : Nat} (hp : Pre wlen olen σ) (hs : FrontPost wlen σ s) :
    WP isa (.seq (.block (outputStage olen))
      (.seq (.block [.movz .x .x1 640 0]) Impl.MlDsa.AArch64.Pack.bitUnpack)) s (BodyPost wlen olen σ) := by
  obtain ⟨hk,hsv,hf,h19,h20,h21,A,B,hpAB,hhash,hbytes⟩ := hs
  have hmul : 16*(olen/16)=olen := by rcases hp.outLength with rfl|rfl <;> decide
  have hn : olen/16≤12 := by rcases hp.outLength with rfl|rfl <;> decide
  rw [WP.seq_iff,← hmul]
  refine WP.mono (outputStage_ok hn hpAB (fun i hi => by
    rw [hk.wr,h21]; exact hp.output _ _ (by omega))) fun a ⟨ha,hfa,h0,h4,hout⟩ => ?_
  rw [hmul]
  rw [hmul,h21] at hfa hout
  rw [h19] at h0
  rw [h20] at h4
  have hasv : Saved σ a.mem := hsv.keep hfa (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl
    exact hp.outWork.symm.sub_left (by
      simpa using Offset.sub_base (σ.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)))
  have habytes : Spec.Sha3.bytesAt a.mem (bufferBase (σ.gpr .x3)) 640=
      H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640 := by
    rw [Proof.MlKem.bytesAt_frame hfa (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.outWork.symm.sub_left (Offset.sub_base _ (d:=256) (n:=640) (k:=2048) (by decide))) (by decide)]
    exact hbytes
  have hahash := hhash olen (by rcases hp.outLength with rfl|rfl <;> decide)
  rw [hahash] at hout
  refine WP.mono (parse_ok (s:=a) (by
    rw [ha.rd,ha.wr,hk.rd,hk.wr,h0]; exact hp.readWork 256 640 (by decide)) (by
    rw [ha.wr,hk.wr,h4]; exact hp.cache) (by
    rw [h0,h4]
    exact hp.cacheWork.symm.sub_left (Offset.sub_base _ (d:=256) (n:=640) (k:=2048) (by decide))))
    fun t ⟨ht,hft,hpoly⟩ => ?_
  rw [h4] at hft hpoly
  change Spec.Sha3.bytesAt a.mem (σ.gpr .x3+256) 640=_ at habytes
  rw [h0,habytes] at hpoly
  refine ⟨((hk.trans ha).trans ht).mono (by simp [frontRegs,parseRegs,decodeRegs,bodyRegs]),?_,?_,?_,?_,hpoly⟩
  · exact hasv.keep hft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.cacheWork.symm.sub_left (by
        simpa using Offset.sub_base (σ.gpr .x3) (d:=0) (n:=160) (k:=2048) (by decide)))
  · apply Frame.trans (hf.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩))
    apply Frame.trans (hfa.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩))
    exact hft.sub (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact ⟨_,by simp [writes],fun _ hx => hx⟩)
  · exact (ht.gpr .x19 (by decide)).trans ((ha.gpr .x19 (by decide)).trans h19)
  · rw [Proof.MlKem.bytesAt_frame hft (by
      intro r hr; rcases List.mem_singleton.mp hr with rfl
      exact hp.outCache) (by rcases hp.outLength with rfl|rfl <;> decide)]
    exact hout

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
