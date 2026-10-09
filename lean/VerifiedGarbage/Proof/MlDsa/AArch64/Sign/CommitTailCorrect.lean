import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailBody
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CommitTailEpi

namespace VG.Proof.MlDsa.AArch64.Sign.CommitTail
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sign.CommitTail
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)

/-- Original ABI state is restored after the shared-lane computation. -/
theorem finish_ok {σ s : State} {wlen olen : Nat} (hp : Pre wlen olen σ)
    (hs : BodyPost wlen olen σ s) :
    WP isa (.block epi) s fun t => abiPreserved σ t ∧ Frame (writes σ olen) σ.mem t.mem ∧
      Spec.Sha3.bytesAt t.mem (σ.gpr .x2) olen=Spec.MlDsa.H
        (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
      Spec.MlDsa.PolyIs t.mem (σ.gpr .x6) (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack
        (Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288)) := by
  obtain ⟨hk,hsv,hf,h19,hh,hm⟩ := hs
  refine WP.mono (epi_ok hsv h19 (fun i hi => by
    rw [hk.rd,hk.wr]; exact hp.readWork _ _ (by omega)) (fun i hi => by
    rw [hk.rd,hk.wr]; exact hp.readWork _ _ (by omega))) fun t ⟨ht,hmt,hv,hg⟩ => ?_
  refine ⟨⟨?_,ht.sp.trans hk.sp,?_⟩,?_,?_,?_⟩
  · intro r hr
    simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact hg 0 (by decide)
      | exact hg 1 (by decide)
      | exact hg 2 (by decide)
      | exact hg 3 (by decide)
      | exact (ht.gpr _ (by decide)).trans (hk.gpr _ (by decide))
  · intro r hr
    simp only [preservedV,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 0 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 1 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 2 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 3 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 4 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 5 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 6 (by decide))
      | exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv 7 (by decide))
  · rw [hmt]; exact hf
  · rw [hmt]; exact hh
  · rw [hmt]; exact hm

/-- Complete measured commitment-plus-mask helper, including save/restore. -/
theorem raw_ok (σ : State) {wlen olen : Nat} (hp : Pre wlen olen σ) :
    WP isa (code wlen olen) σ fun t => abiPreserved σ t ∧ Frame (writes σ olen) σ.mem t.mem ∧
      Spec.Sha3.bytesAt t.mem (σ.gpr .x2) olen=Spec.MlDsa.H
        (Spec.Sha3.bytesAt σ.mem (σ.gpr .x0) 64++Spec.Sha3.bytesAt σ.mem (σ.gpr .x1) wlen) olen ∧
      Spec.MlDsa.PolyIs t.mem (σ.gpr .x6) (Spec.MlDsa.toRq (Spec.MlDsa.bitUnpack
        (Spec.MlDsa.H (seedBytes σ.mem (σ.gpr .x4) (σ.gpr .x5)) 640) 524287 524288)) := by
  obtain ⟨tf,s,hf,hs⟩ := front_ok hp.toFrontPre
  obtain ⟨tb,t,hb,ht⟩ := body_ok hp hs
  obtain ⟨te,u,he,hu⟩ := finish_ok hp ht
  cases hf with
  | seq hf0 hf1 =>
    cases hb with
    | seq hb0 hb1 =>
      exact ⟨_,_,Exec.seq hf0 (Exec.seq hf1 (Exec.seq hb0 (Exec.seq hb1 he))),hu⟩

end VG.Proof.MlDsa.AArch64.Sign.CommitTail
