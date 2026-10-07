import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacWinPrep

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (V)
open VG.Impl.Ecdsa.Verify.AArch64.Cfg (jacWinCfg jacWinPrep)

structure JacWinState (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s : State) : Prop where
  scr : Scr s base size
  fixed : ∃ g, Fixed c base g s.mem
  px : sv c base s PX<c.C.p
  py : sv c base s PY<c.C.p
  rep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
    (tmv c.C c.n base s (c.sl ONEP)) P
  scalar : sv c base s V=k

structure JacWinPublic (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s t : State) : Prop where
  left : JacWinState c base P k s
  right : JacWinState c base P k t
  sp : s.sp=t.sp
  px : tmv c.C c.n base s (c.sl PX)=tmv c.C c.n base t (c.sl PX)
  py : tmv c.C c.n base s (c.sl PY)=tmv c.C c.n base t (c.sl PY)

theorem JacWinPublic.fields {c : Cfg} {base : Addr} {P : Point c.C} {k : Nat} {s t : State}
    (h : JacWinPublic c base P k s t) :
    ∀ x∈winRo (jacWinCfg c),tmv c.C c.n base s x=tmv c.C c.n base t x := by
  obtain ⟨_,fs⟩ := h.left.fixed
  obtain ⟨_,ft⟩ := h.right.fixed
  intro x hx
  simp only [winRo,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · change toM _ _ (wordsVal s.mem base (c.sl AP) c.n)=toM _ _ (wordsVal t.mem base (c.sl AP) c.n)
    rw [fs.ap,ft.ap]
  · change toM _ _ (wordsVal s.mem base (c.sl BM) c.n)=toM _ _ (wordsVal t.mem base (c.sl BM) c.n)
    rw [fs.bm,ft.bm]
  · change toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n)=toM _ _ (wordsVal t.mem base (c.sl ZERO) c.n)
    rw [fs.zero,ft.zero]
  · exact h.px
  · exact h.py
  · change toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)=toM _ _ (wordsVal t.mem base (c.sl ONEP) c.n)
    rw [fs.onep,ft.onep]

/-- The signature-derived scalar preparation and variable-point window use
only common public scalar bits and public point coordinates. -/
theorem jacWinMul_relCT {c : Cfg} (hc : CfgOk c) (hn4 : c.n=4) (hC : Law c.C)
    (hprep : FieldCT (jacWinPrep c)) (hchecks : JacWindowChecks (jacWinCfg c))
    {base : Addr} {P : Point c.C} {k : Nat} (hP : onCurve c.C P=true) :
    RelCT isa (JacWinPublic c base P k)
      (.seq (jacWinPrep c) (Jacobian.jacWindow (jacWinCfg c) 5))
      (AArch64.Taint.Agree (Taint.ofRegs [.x0])) := by
  intro s t ts tt s' t' hp es et
  obtain ⟨_,fs⟩ := hp.left.fixed
  obtain ⟨_,ft⟩ := hp.right.fixed
  cases es with | seq ps ws =>
    cases et with | seq pt wt =>
      obtain ⟨_,_,xs,is,bs,vs,ks,_,_,_⟩ := jacWinPrep_ok hc hn4 hC hp.left.scr fs hp.left.px hp.left.py hp.left.rep
      obtain ⟨_,_,xt,it,bt,vt,kt,_,_,_⟩ := jacWinPrep_ok hc hn4 hC hp.right.scr ft hp.right.px hp.right.py hp.right.rep
      obtain ⟨_,rfl⟩ := Exec.det ps xs
      obtain ⟨_,rfl⟩ := Exec.det pt xt
      have he := hprep _ _ _ _ _ _ trivial trivial ⟨hp.sp,fun r hr => by
        simp only [Taint.mem_ofRegs,List.mem_singleton] at hr
        subst hr
        exact hp.left.scr.x0.trans hp.right.scr.x0.symm⟩ ps pt
      have pair : FieldPair (jacWinCfg c).M base size c.C.p (·∈jacWinSlots (jacWinCfg c))
          (winRo (jacWinCfg c)) _ _ _ :=
        ⟨is,it.congr_env (fun x hx => (vt x hx).trans ((hp.fields x hx).symm.trans (vs x hx).symm)),
          ks.trans (hp.sp.trans kt.symm)⟩
      rw [hp.left.scalar] at bs
      rw [hp.right.scalar] at bt
      have hk : k<2^256 := by
        rw [←hp.left.scalar]
        simpa only [sv,hn4] using wordsVal_lt s.mem base (c.sl V) c.n
      have hrec := Window5.recode_lt hk
      have hmont : ∀ x,c.mont x<c.C.p := fun x => Nat.mod_lt _ (by have := hc.p_ge; omega)
      obtain ⟨hw,_,post⟩ := jacWindow_relCT (jacLay hc hn4) rfl (jacAligned c hn4)
        (unitMod_pow_two hc.p_odd (64*c.n)) hC hc.am3
        (by change c.sl WT<4096; rw [sl_eq,hn4]; decide)
        (by change c.sl WB+5≤4096; rw [sl_eq,hn4]; decide) (hmont 1)
        (toM_cmont hc 1) (Nat.le_add_left _ _) hrec hchecks hP
        _ _ _ _ _ _ ⟨pair,bs,bt⟩ ws wt
      exact ⟨by rw [he,hw],post.public⟩

end VG.Proof.Ecdsa.Verify.AArch64
