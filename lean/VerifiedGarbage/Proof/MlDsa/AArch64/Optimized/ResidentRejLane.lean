import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAccept
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Impl.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (acc accept_ok)
open VG.Spec.MlDsa (Zq q)

/-- Scalar fallback on one already gathered lane. The selected lane is
zero-extended, and every vector (including unprocessed lanes) is preserved. -/
theorem lane_ok {s : State} {r : VReg} {e : Nat} {p : Addr} {L : List Zq}
    (he : e<4) (hz : (vword (s.v r) e).toNat<2^23)
    (h9 : (s.gpr .x9).toNat=q) (h3 : s.gpr .x3=coeffAddr p L.length)
    (h4 : (s.gpr .x4).toNat=256-L.length) (hL : L.length<256)
    (hst : Stored s.mem p L) (hw : InRegions s.wr (coeffAddr p L.length) 4) :
    WP isa (.block (.umov .w .x11 r e :: rnAccept)) s fun t =>
      Keep [.x11,.x3,.x4,.x13,.x14,.x15] s t ∧ t.v=s.v ∧
      Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (acc L (vword (s.v r) e).toNat).length ∧
      (t.gpr .x4).toNat=256-(acc L (vword (s.v r) e).toNat).length ∧
      Stored t.mem p (acc L (vword (s.v r) e).toNat) := by
  have h : WP isa (.block (.umov .w .x11 r e :: rnAccept)) s fun t =>
      Keep [.x11,.x3,.x4,.x13,.x14,.x15] s t ∧
      Frame [polyR p] s.mem t.mem ∧
      t.gpr .x3=coeffAddr p (acc L (vword (s.v r) e).toNat).length ∧
      (t.gpr .x4).toNat=256-(acc L (vword (s.v r) e).toNat).length ∧
      Stored t.mem p (acc L (vword (s.v r) e).toNat) := by
    refine wp_x (d := .x11) (v := (vword (s.v r) e).setWidth 64)
      (by simp only [exec,Size.bits,show e*32<128 by omega,ite_true]; rfl) fun a ha ea => ?_
    refine WP.mono (accept_ok (aP := p) (L := L) (z := (vword (s.v r) e).toNat)
      (by rw [ea,BitVec.toNat_setWidth_of_le (by decide)]) hz
      (by rw [ha.get .x9]; exact h9) (by rw [ha.get .x3]; exact h3)
      (by rw [ha.get .x4]; exact h4) hL (by rw [ha.mem]; exact hst)
      (by rw [ha.wr]; exact hw)) fun t ⟨hk,hf,hp,hcount,hstored⟩ => ?_
    exact ⟨(ha.keep.trans hk).mono (by decide),by rw [←ha.mem]; exact hf,hp,hcount,hstored⟩
  refine WP.mono (WP.keepV (by rfl) h) ?_
  rintro t ⟨⟨hk,hf,hp,hcount,hstored⟩,hv⟩
  exact ⟨hk,hv,hf,hp,hcount,hstored⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
