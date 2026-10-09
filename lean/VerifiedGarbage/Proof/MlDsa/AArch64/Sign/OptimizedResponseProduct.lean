import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedResponse
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def responseProductChk (p : Params) (out secret : Ptr) : Bool :=
  inB (sgB p) out 1024 && inB (sgB p) cP 1024 && inB (sgB p) secret 1024 &&
  inB (sgB p) (sc oPS) 1024 && inB (sgW p) out 1024 && inB (sgW p) (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) out 1024 cP 1024 && sepB (sgR p) (sgW p) out 1024 secret 1024 &&
  sepB (sgR p) (sgW p) out 1024 (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) cP 1024 (sc oPS) 1024 &&
  sepB (sgR p) (sgW p) secret 1024 (sc oPS) 1024

theorem responseProductChk_z {p : Params} (hp : Ok3 p) :
    ∀r<p.ℓ,responseProductChk p t1P (s1P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProductChk_r0 {p : Params} (hp : Ok3 p) :
    ∀r<p.k,responseProductChk p t1P (s2P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProductChk_h {p : Params} (hp : Ok3 p) :
    ∀r<p.k,responseProductChk p t3P (t0P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProductChk_hint {p : Params} (hp : Ok3 p) :
    ∀r<p.k,responseProductChk p t1P (t0P p r)=true := by
  rcases hp with rfl | rfl | rfl <;> decide

theorem responseProduct_ok {p : Params} {S : Nat} {σ s : State} {out secret : Ptr} {f g : Poly}
    (hs : RootedSt p S σ s) (hc : responseProductChk p out secret=true)
    (hf : PosPolyIs s.mem (pa s cP) f) (hg : PosPolyIs s.mem (pa s secret) g) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.responseProduct out secret) s fun t =>
      PPostB S s t [(out,1024),(sc oPS,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT f g)) := by
  simp only [responseProductChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho,ha⟩,hb⟩,hsc⟩,hwo⟩,hws⟩,hoa⟩,hob⟩,hos⟩,has⟩,hbs⟩ := hc
  refine productAt_field_layout hs.1.lay ho ha hb hsc ?_ hf hg
  refine productReady_layout hs.1.lay ho ha hb hsc hwo hws hoa hob hos has hbs
    hs.2.inverse.held hs.2.inverse.fit ?_ hs.2.inverse.readable hf.bound hg.bound
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hwo)
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hws)

end VG.Proof.MlDsa.AArch64.Sign
