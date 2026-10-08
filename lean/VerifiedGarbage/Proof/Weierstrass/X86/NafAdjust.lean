import VerifiedGarbage.Proof.Weierstrass.X86.NafChoose
import VerifiedGarbage.Proof.Weierstrass.X86.NafSubtract

/-! Choose and subtract one signed width-five digit from the public residual. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86
  VG.Proof.Mont.X86 VG.Proof.Mont

theorem nafAdjust_ok {s : State} {base : Addr} {size work k j : Nat}
    (hs : Scr s base size) (ha : work+36≤size)
    (hv : val32 s.mem base work 9=Naf5.residual k j)
    (hb : Naf5.residual k j≤2^256) :
    WP isa (Naf.adjust work) s fun t =>
      t.gpr .ecx=BitVec.ofInt 32 (Naf5.digit k j) ∧
      val32 t.mem base work 9=2*Naf5.residual k (j+1) ∧
      Keeps [.eax,.ecx,.edx] s t ∧ Outside base work 36 s.mem t.mem := by
  rw [Naf.adjust]
  refine WP.seq (wp_movS (readSrc_sc hs (by omega)) fun a ua _ => ?_)
  refine WP.mono (nafParity_ok a) fun b ⟨vb,zb,kb⟩ => ?_
  have sa := hs.of_keeps ua.keeps (by decide)
  have sb := sa.of_keeps kb.keeps (by decide)
  have mb : b.mem=s.mem := kb.2.1.trans ua.mem
  have low : (a.gpr .eax).toNat%32=Naf5.residual k j%32 := by
    rw [ua.gpr]
    have he : val32 s.mem base work 9 =
        w32 s.mem base work+2^32*val32 s.mem base (work+4) 8 := rfl
    change w32 s.mem base work%32=_
    omega
  have hd := nafRaw_eq low
  have K : Keeps [.eax,.ecx,.edx] s b :=
    (ua.keeps.mono (by decide)).trans (kb.keeps.mono (by decide))
  refine WP.ite (decide (a.gpr .eax &&& 1=0)) zb (fun h => ?_) (fun h => ?_)
  · have h0 := of_decide_eq_true h
    have hp := (nafParity _).mp h0
    have he : Naf5.residual k j%2=0 := by omega
    have hn : Naf5.residual k j=2*Naf5.residual k (j+1) := by
      simp only [Naf5.residual_succ,Naf5.next,he,ite_true]
      omega
    apply WP.block_nil
    refine ⟨?_,?_,K,?_⟩
    · rw [vb,h0]
      simpa only [nafRaw,h0,ite_true] using hd
    · rw [mb,hv,hn]
    · rw [mb]; exact Outside.refl _ _ _ _
  · have h0 := of_decide_eq_false h
    refine WP.seq (WP.mono (nafOdd_ok b) fun c ⟨vc,kc⟩ => ?_)
    have hc : c.gpr .ecx=BitVec.ofInt 32 (Naf5.digit k j) := by
      rw [vc,kb.1 .eax (by decide)]
      simpa only [nafRaw,h0,ite_false] using hd
    have mc : c.mem=s.mem := kc.2.1.trans mb
    refine WP.mono (nafSubtract_ok (sb.of_keeps kc.keeps (by decide)) ha hc
      (by rw [mc]; exact hv) hb) fun t ⟨vt,kt,ot⟩ => ⟨?_,vt,?_,?_⟩
    · rw [kt.1 .ecx (by decide),hc]
    · exact (K.trans (kc.keeps.mono (by decide))).trans (kt.mono (by decide))
    · rw [mc] at ot; exact ot

end VG.Proof.Weierstrass.X86
