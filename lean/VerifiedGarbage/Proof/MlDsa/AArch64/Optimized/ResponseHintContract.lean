import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintMachine
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintOnes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintValid
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintField

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Arith (pR)
open VG.Proof.MlKem.AArch64 (Keep)

theorem hintCount_bound (m : Mem) (B : BitVec 32) (p a h : Addr) : hintCount m B p a h 64≤256 := by
  have h0 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=0) (by decide)
  have h1 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=1) (by decide)
  have h2 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=2) (by decide)
  have h3 := hintRun_count_bound m B p a h (j:=64) (by decide) (e:=3) (by decide)
  rw [hintRun_count_value _ _ _ _ _ (by decide) (by decide)] at h0 h1 h2 h3
  unfold hintCount
  omega

/-- Caller-facing exact output: low 32 bits count hints, high 32 bits validate ct0.
Rejected inputs still execute all coefficient writes and preserve the same frame. -/
theorem hintNorm_ok (s : State) (B : Nat) (out : Vector Bool n)
    (hB : 1≤B) (hB' : B≤524288) (hbreg : (s.gpr .x3).setWidth 32=BitVec.ofNat 32 B)
    (ha : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hb : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 off) 16)
    (hh : ∀off,off+16≤1024 → InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 off) 16)
    (hw : ∀off,off+16≤1024 → InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 off) 16)
    (hd : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x1)))
    (he : (pR (s.gpr .x0)).Disjoint (pR (s.gpr .x2)))
    (hr : ∀k<256,-8380417<(coeffAt s.mem (s.gpr .x1) k).toInt ∧
      (coeffAt s.mem (s.gpr .x1) k).toInt<2*8380417)
    (ho : ∀k<256,hintWord (BitVec.ofNat 32 B)
      (reduceWord (coeffAt s.mem (s.gpr .x1) k)+coeffAt s.mem (s.gpr .x0) k)
      (coeffAt s.mem (s.gpr .x2) k)=BitVec.ofNat 32 out[k]!.toNat) :
    WP isa Impl.MlDsa.AArch64.Optimized.Response.hintNorm s fun t =>
      Keep [.x0,.x1,.x2,.x9,.x10] s t ∧ Frame [pR (s.gpr .x0)] s.mem t.mem ∧
      HintIs t.mem (s.gpr .x0) 1 [out] ∧
      (t.gpr .x0).toNat%4294967296=hintOnes [out] ∧
      ((t.gpr .x0).toNat/4294967296=1 ↔
        ∀k<256,normZq (ofInt (coeffAt s.mem (s.gpr .x1) k).toInt)<B) ∧
      (t.gpr .x0).toNat/4294967296≤1 := by
  refine WP.mono (hintNorm_machine s ha hb hh hw) fun t ⟨hk,hm,hv⟩ => ?_
  simp only [hbreg] at hm hv
  have hc := hintCount_bound s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2)
  have hcval := hintCount_ones s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) out hd he
    (by intro k hk; rw [ho k hk,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := out[k]!.toNat_le; omega)])
  have hret := hintRun_packed_value s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) (j:=64) (by decide)
  rw [hcval] at hc hret
  have hvalid := hintFailure_field s.mem B (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) hd hB hB' hr
  refine ⟨hk,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact hintRun_frame _ _ _ _ _ (by decide)
  · apply VG.Proof.MlDsa.Round.hintIs_of_toNat
    intro k hk
    rw [hm,hintRun_coeff _ _ _ _ _ hd he hk,ho k hk]
    rfl
  · rw [hv,hret]; split <;> omega
  · rw [hv,hret]
    cases hf : hintFailure s.mem (BitVec.ofNat 32 B) (s.gpr .x0) (s.gpr .x1) (s.gpr .x2) 64
    · simp only [hf,Bool.false_eq_true,ite_false] at *
      exact iff_of_true (by omega) (hvalid.mp trivial)
    · simp only [hf,ite_true] at *
      exact iff_of_false (by omega) (by intro hn; have := hvalid.mpr hn; contradiction)
  · rw [hv,hret]; split <;> omega

end VG.Proof.MlDsa.AArch64.Optimized.Response
