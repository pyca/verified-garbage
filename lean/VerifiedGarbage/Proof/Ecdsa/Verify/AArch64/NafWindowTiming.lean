import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWinPrep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacWindowTiming

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg nafWinPrep)

theorem nafWinPrep_relCT {c : Cfg} (hc : CfgOk c) (hn4 : c.n=4)
    (checks : NafPrepChecks (jacWinCfg c) (c.sl V)) {base : Addr} {P : Point c.C} {k : Nat} :
    RelCT isa (JacWinPublic c base P k) (nafWinPrep c) (fun _ _ => True) := by
  have h := nafPrep_relCT (jacWinCfg c) (base:=base)
    (by simpa only [hn4] using sl_le c hc.n10 (i:=V) (by decide)) (sl_mod8 c _)
    (by change c.sl WB<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
    (by change c.sl WB+257≤size; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) checks
  exact h.mono (fun _ _ hp => ⟨hp.left.scr,hp.right.scr,hp.sp,by
    rw [←hn4]; exact hp.left.scalar.trans hp.right.scalar.symm⟩) (fun _ _ h => h)

/-- The signature-derived scalar preparation and variable-point window use
only common public scalar bits and public point coordinates. -/
theorem nafWinMul_relCT {c : Cfg} (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C)
    (hchecks : NafWindowChecks (jacWinCfg c))
    {base : Addr} {P : Point c.C} {k : Nat} (hP : onCurve c.C P=true)
    (hprep : RelCT isa (JacWinPublic c base P k) (nafWinPrep c) (fun _ _ => True)) :
    RelCT isa (JacWinPublic c base P k)
      (.seq (nafWinPrep c) (Naf.window (jacWinCfg c)))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,fs⟩ := hp.left.fixed
  obtain ⟨_,ft⟩ := hp.right.fixed
  cases es with | seq ps ws =>
    cases et with | seq pt wt =>
      obtain ⟨_,_,xs,is,bs,vs,ks,_,_,_⟩ := nafWinPrep_ok hc hn4 hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
      obtain ⟨_,_,xt,it,bt,vt,kt,_,_,_⟩ := nafWinPrep_ok hc hn4 hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
      obtain ⟨_,rfl⟩ := Exec.det ps xs
      obtain ⟨_,rfl⟩ := Exec.det pt xt
      have he := (hprep _ _ _ _ _ _ hp ps pt).1
      have pair : FieldPair (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
          (winRo (jacWinCfg c)) _ _ _ :=
        ⟨is,it.congr_env (fun x hx => (vt x hx).trans ((hp.fields x hx).symm.trans (vs x hx).symm)),
          ks.trans (hp.sp.trans kt.symm)⟩
      rw [hp.left.scalar] at bs
      rw [hp.right.scalar] at bt
      have hk : k<2^256 := by
        rw [←hp.left.scalar]
        simpa only [sv,hn4] using wordsVal_lt s.mem base (c.sl V) c.n
      have hmont : ∀ x,c.mont x<c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
      obtain ⟨hw,_,post⟩ := nafWindow_relCT (jacLay hc hn4) rfl (jacAligned c hn4)
        (unitMod_pow_two hc.p_odd (64*c.n)) hC hc.am3
        (by change c.sl WT<4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide)
        (by change c.sl WB+5≤4096; simp (disch := decide) only [sl_eq]; rw [hn4]; decide) (hmont 1)
        (toM_cmont hc 1) hk hchecks hP
        _ _ _ _ _ _ ⟨pair,bs,bt⟩ ws wt
      exact ⟨by rw [he,hw],post.public⟩

end VG.Proof.Ecdsa.Verify.AArch64
