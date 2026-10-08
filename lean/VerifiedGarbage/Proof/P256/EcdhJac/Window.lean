import VerifiedGarbage.Proof.P256.EcdhJac.Build
import VerifiedGarbage.Proof.P256.EcdhJac.First
import VerifiedGarbage.Proof.P256.EcdhJac.Step
import VerifiedGarbage.Proof.P256.EcdhJac.Finish

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem window_ok (hC : Law C) (ha : AM3 C) (hO : PrimeOrder C)
    {base : Addr} {P : Point C} {k : Nat} {s : State}
    (hP : onCurve C P=true) (hk : k<2^256) (hf : Fixed base P k s) :
    WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s) := by
  unfold Impl.P256.EcdhJac.window
  refine WP.seq (WP.mono (build_ok hC ha hO hP hf) fun a ⟨fa,hfa,ta⟩=>?_)
  refine WP.seq (WP.mono (first_ok hC hP hk hfa ta) fun b ⟨fb,hb⟩=>?_)
  refine WP.seq (WP.mono (loop_ok hC ha hO hP hb) fun d ⟨fd,hd⟩=>?_)
  refine WP.mono (finish_ok hC hd) fun t ht=>?_
  exact ⟨fa.trans ((frame_build fb).trans ((frame_build fd).trans ht.frame)),ht.field,ht.point⟩

end VG.Proof.P256.EcdhJac
