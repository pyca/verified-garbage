import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWinPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacWindow

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg)
variable {c : Cfg}

theorem nafWinMul_ok (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', JacWinMulPost c base P (sv c base s V) s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.nafWinPrep c) (.seq (Naf.window (jacWinCfg c)) rest)) s R := by
  have hmont : ∀ x,c.mont x<c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
  have hk : sv c base s V<2^256 := by
    simpa only [sv,hn4] using wordsVal_lt s.mem base (c.sl V) c.n
  apply WP.seq
  refine WP.mono (nafWinPrep_ok hc hn4 hC hs F hpx hpy hrep)
    fun s₂ ⟨hI,⟨hz,hb,hj⟩,_,_,U₂,rd₂,wr₂⟩ => ?_
  refine WP.seq (WP.mono (nafWindow_ok (jacLay hc hn4) rfl (jacAligned c hn4)
    (unitMod_pow_two hc.p_odd (64*c.n)) hC hc.am3
    (by change c.sl WT<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
    (by change c.sl WB+5≤4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) (hmont 1)
    (toM_cmont hc 1) hk hP hI hz hb hj)
    fun s₃ ⟨K₃,U₃,M₃,L₃,R₃⟩ => h s₃ ?_)
  rw [jacWrites_eq c hn4] at U₃
  have nx0 : Reg.x0 ∉ jacWindowClob (jacWinCfg c) := by
    simp only [jacWindowClob,tcombClob]
    rw [show (jacWinCfg c).M.n=4 from hn4]
    decide
  exact ⟨hI.scr.of_keepRegs K₃ nx0,K₃.rd.trans rd₂,K₃.wr.trans wr₂,U₂.trans U₃,M₃,L₃,R₃⟩

end VG.Proof.Ecdsa.Verify.AArch64
