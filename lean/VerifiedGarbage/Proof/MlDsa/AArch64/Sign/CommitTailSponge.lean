import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailSeed
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailInitial
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskBytes

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail

def spongeRegs : List Reg := [.x5,.x6,.x7,.x8,.x10,.x16]

theorem sponge_ok {s : State} {wlen : Nat} (hc : CoreConfig s wlen (s.gpr .x1) (s.gpr .x19))
    (hmu : ∀j<4,InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (16*j)) 16)
    (hseed : ∀j<8,InRegions (s.rd++s.wr) (s.gpr .x4+BitVec.ofNat 64 (8*j)) 8) :
    WP isa (.seq (.block (first++upperInit++([.addImm .x .x5 .x1 72] : List Instr)))
      (coreFor wlen)) s fun t =>
      RegKeep spongeRegs s t ∧ Frame [bufferRegion (s.gpr .x19)] s.mem t.mem ∧
      Pairs t (lowRun wlen s.mem (s.gpr .x1) (firstState s.mem (s.gpr .x0) (s.gpr .x1))
        ((64+wlen)/136+1))
        (Optimized.Resident.permuted (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) ((64+wlen)/136+1)) ∧
      Spec.Sha3.bytesAt t.mem (bufferBase (s.gpr .x19)) 640 =
        Spec.MlDsa.H (seedBytes s.mem (s.gpr .x4) (s.gpr .x5)) 640 := by
  have hw : 768≤wlen := by rcases hc.length with rfl|rfl <;> decide
  rw [WP.seq_iff]
  refine WP.mono (initial_ok hmu (fun j hj => hc.readable _ _ (by omega))
    (hc.readable 64 8 (by omega)) hseed) ?_
  intro a ⟨ha,hma,h5,hp⟩
  have hca : CoreConfig a wlen (s.gpr .x1) (s.gpr .x19) := by
    refine ⟨hc.length,ha.gpr .x19 (by decide),?_,?_,hc.separate⟩
    · intro d n hn; rw [ha.rd,ha.wr]; exact hc.readable d n hn
    · intro d n hn; rw [ha.wr]; exact hc.writable d n hn
  have hstart : CoreState a wlen (s.gpr .x1) (s.gpr .x19)
      (firstState s.mem (s.gpr .x0) (s.gpr .x1))
      (seedNonceState s.mem (s.gpr .x4) (s.gpr .x5)) 0 a := by
    refine ⟨⟨RegKeep.refl _ _,Frame.refl _ _,?_,fun _ hi => by omega⟩,hp⟩
    simp only [inputPtr,fullCount,Nat.zero_min,Nat.mul_zero,Nat.add_zero]
    exact h5
  refine WP.mono (core_ok hca hstart) fun t ht => ?_
  refine ⟨(ha.trans ht.keep).mono (by simp [coreRegs,spongeRegs]),?_,?_,?_⟩
  · simpa only [hma] using ht.frame
  · simpa only [hma] using ht.pairs
  · have ho := ht.output
    have hn : min ((64+wlen)/136+1) 5=5 := by rcases hc.length with rfl|rfl <;> decide
    rw [hn,seedNonceState_A0] at ho
    exact Optimized.ResidentMask.stream_mask_bytes (d:=20) (Or.inr rfl)
      (seedBytes_length _ _ _) ho

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
