import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableStep
import VerifiedGarbage.Proof.Framework.RelCTAssoc

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- Build the eight odd multiples and the cached double. -/
theorem arithmeticTable_ok (certs : Forward.Arithmetic.Cases) {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hsize : 8192≤size) (hC : Law C) (ha : AM3 C)
    (ht : K.tbl<4096) (hOne : K.one<C.p) {P : Point C} (hP : onCurve C P=true)
    {s : State} (hI : Inv K.M base size C.p (·∈jacWinSlots K) (winRo K) (tmv C K.M.n base s) s)
    (hJP : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) :
    WP isa (ArithmeticTable.table K) s (fun t => NafTableInv K C base size P s t 8) := by
  unfold ArithmeticTable.table
  apply WP.assoc
  refine WP.seq (WP.mono (nafTable_init_ok hL hJ hAl hm hC ha ht hP hI hJP) fun a ia => ?_)
  apply countLoop_ok (Inv := fun j t => NafTableInv K C base size P s t (8-j))
    (n := 7) (by decide)
  · intro j u hj hj7 hu
    refine WP.mono (arithmeticTable_step_ok certs hL hJ hAl hm hsize hC ha hOne hP (by omega) (by omega) hu)
      fun t it => ?_
    have he : 8-j+1=8-(j-1) := by omega
    refine ⟨he ▸ it,?_⟩
    have hc := it.counter
    have he' : 8-(8-j+1)=j-1 := by omega
    rwa [he'] at hc
  · intro t it; exact it
  · decide
  · exact ia

end VG.Proof.Weierstrass.AArch64
