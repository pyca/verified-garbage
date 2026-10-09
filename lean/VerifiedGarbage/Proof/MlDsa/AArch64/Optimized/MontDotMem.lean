import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Pro

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotBlock
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.MontDot
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_strq wp_nil Keep)
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

theorem body_ok {n : Nat} (hn : 0<n) (hn7 : n≤7) {s : State} (hc : VConsts s)
    (hr : ∀k<n,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (1024*k)) 16 ∧
      InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 (1024*k)) 16)
    (ha : ∀k<n,∀e<4,(dotInput s .x1 0 k e).toNat<3*q)
    (hb : ∀k<n,∀e<4,(dotInput s .x2 0 k e).toNat<3*q)
    (hw : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block (Impl.MlDsa.AArch64.Optimized.MontDot.body n)) s fun t=>
      ∃v,t.mem=s.mem.write (s.gpr .x0) 16 v ∧
      Lanes v (fun e=>mont (dotAccum s 0 n e).toNat%q) ∧ VConsts t ∧
      t.gpr .x0=s.gpr .x0+16 ∧ t.gpr .x1=s.gpr .x1+16 ∧ t.gpr .x2=s.gpr .x2+16 ∧
      t.gpr .x12=s.gpr .x12-1 ∧ Keep [.x0,.x1,.x2,.x12] s t := by
  unfold Impl.MlDsa.AArch64.Optimized.MontDot.body
  refine block_ok hn hn7 hr ha hb hc.q hc.qi fun a hA hv=>?_
  refine wp_strq (by decide) rfl (by simpa only [hA.wr,hA.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw) fun b hB=>?_
  have hk : StepKeep [.v0,.v1,.v2,.v3,.v4] s b :=
    (StepKeep.ofChg hA (by decide)).trans (StepKeep.ofMem hB)
  have hm : b.mem=s.mem.write (s.gpr .x0) 16 (a.v .v0) := by
    simp only [hB.mem,hA.mem,hA.gpr,BitVec.add_zero]
  have cb : VConsts b := ⟨by rw [hk.vec .v16 (by decide)];exact hc.q,
    by rw [hk.vec .v17 (by decide)];exact hc.qi⟩
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
      .addImm .x .x2 .x2 16,.subImm .x .x12 .x12 1]) b fun u=>
      u.mem=b.mem ∧ u.v=b.v ∧ u.gpr .x0=b.gpr .x0+16 ∧ u.gpr .x1=b.gpr .x1+16 ∧
      u.gpr .x2=b.gpr .x2+16 ∧ u.gpr .x12=b.gpr .x12-1 := by
    arun [State.write,BitVec.ofNat_eq_ofNat]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x0,.x1,.x2,.x12] scalar (by decide))
    fun u ⟨⟨hum,huv,h0,h1,h2,h12⟩,ku⟩=>?_
  refine ⟨a.v .v0,hum.trans hm,hv,?_,?_,?_,?_,?_,(hk.keep.trans ku).mono⟩
  · exact ⟨by rw [huv];exact cb.q,by rw [huv];exact cb.qi⟩
  · simpa only [hk.keep.get .x0] using h0
  · simpa only [hk.keep.get .x1] using h1
  · simpa only [hk.keep.get .x2] using h2
  · simpa only [hk.keep.get .x12] using h12

end VG.Proof.MlDsa.AArch64.Optimized.MontDot
