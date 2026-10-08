import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafCallerInput

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open Spec.Weierstrass

def vNafCode : Prog isa := Cfg.windowMulQ p256Comb
materialize_code vNafCode

theorem vSave_sp : SpOk vSaveCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide),by lit_decide⟩
theorem vNaf_sp : SpOk vNafCode p256Comb.stk := ⟨NoSp.of_all (by lit_decide),by lit_decide⟩

theorem vSave_input (hc : CfgOk p256Comb) {s₀ s : State} {base : Addr}
    (h : VPointInput s₀ base s) : WP isa vSaveCode s (VPointInput s₀ base) := by
  refine h.1.withSp vSave_sp (WP.mono (save_ok hc h.1.scr) (fun t ⟨st,kt,ut,_⟩ ft => ?_))
  refine ⟨⟨st,(kt.gpr _ (by decide)).trans h.1.esp,kt.rd.trans h.1.rd,kt.wr.trans h.1.wr,
    h.1.fixed.unch hc.n10 h.1.scr.nowrap (fixedOk_slW (by decide)) ut,ft,h.1.sp_lo⟩,?_⟩
  apply h.2.transfer
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl <;>
    exact sv_unch ut hc.n10 h.1.scr.nowrap (by decide) (apart_slW (by decide))

theorem vNaf_keep (hc : CfgOk p256Comb) (hC : Law p256Comb.C) (ha : AM3 p256Comb.C)
    {s₀ s : State} {base : Addr} (h : VPointInput s₀ base s) :
    WP isa vNafCode s (Keep p256Comb s₀ base) := by
  have hi := vPointInput_naf hc hC h
  refine h.1.withSp vNaf_sp (WP.mono (windowMulQ_ok hc rfl hC ha h.1.scr h.1.fixed
    (Ecdh.X86.peerPt_onCurve hc _ _ _) hi.px_lt hi.py_lt hi.point) (fun t ⟨kt,ut,_⟩ ft => ?_))
  exact ⟨h.1.scr.of_keeps kt (by decide),(kt.gpr _ (by decide)).trans h.1.esp,
    kt.rd.trans h.1.rd,kt.wr.trans h.1.wr,
    h.1.fixed.unch hc.n10 h.1.scr.nowrap (windowW_fixed rfl) ut,ft,h.1.sp_lo⟩

end VG.Proof.Ecdsa.Verify.X86
