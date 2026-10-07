import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Input
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Frames
import VerifiedGarbage.Proof.Ecdh.X86_64.Secret.Window

/-! Secret scalar preparation, Jacobian multiplication and inversion as one ECDH phase. -/
namespace VG.Proof.Ecdh.X86_64.Secret
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdh.X86_64.Window5
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)

def mulW (c : Cfg) : List (Nat × Nat) := winX c++windowW c++pwW c

theorem fixedOk_mulW {c : Cfg} (hn : c.n=4) : FixedOk c (mulW c) :=
  (fixedOk_winX.append (fixedOk_windowW hn)).append fixedOk_pwW

theorem apart_mulW {c : Cfg} (hn : c.n=4) {i : Nat} (hi : i∈[D,FLAG]) :
    ∀ w∈mulW c,c.sl i+8*c.n≤w.1 ∨ w.1+w.2≤c.sl i := by
  have hi45 : i<45 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl <;> decide
  have hin : i∉[ACC,PT,TMP] := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl <;> decide
  exact apart_append (apart_append (apart_winX hi45) (apart_windowW hn hi)) (apart_pwW hi45 hin)

structure MulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s t : State) : Prop where
  scr : Scr t base size
  keep : KeepRegs (invClob c.n) s t
  unch : Unch base (mulW c) s.mem t.mem
  point : k<c.C.n → XOnly c.C (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RZ)) (mul k P)
  acc_lt : sv c base t ACC<c.C.p
  acc : toM c.C.p (2^(64*c.n)) (sv c base t ACC)=tmv c.C c.n base t (c.sl RZ)^(c.C.p-2)
  rz_lt : sv c base t RZ<c.C.p

theorem mulPow_ok {c : Cfg} (hc : CfgOk c) (hCurve : c.C=Spec.P256.curve)
    (hL : SecretLay (cfg c) size) (hC : Law c.C) (hO : PeerOrder c.C)
    {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem)
    (hbp : sv c base s BP=c.mont c.C.b) {P : Point c.C} (hP : onCurve c.C P=true)
    (hpx : sv c base s PX<c.C.p) (hpy : sv c base s PY<c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (ht₁ : ∀ t<64*c.n,s.mem (off base (bitsAt c.n 1+t))=if (c.C.p-2).testBit t then 1 else 0) :
    WP isa (.seq (.seq (.block (WinCfg.addConst 4 (c.sl K) c.winK (16*((32^52-1)/31))))
      (bits c.winK c.winBits 40)) (.seq (window (cfg c)) c.pPow)) s
      (MulPost c base P (sv c base s K) s) := by
  have hn : c.n=4 := hL.n
  have hp := hc.p_ge
  have hm := unitMod_pow_two hc.p_odd (64*c.n)
  apply WP.seq
  refine WP.mono (prep_ok hn hs) fun a A => ?_
  have Fₐ := F.unch hc.n10 hs.nowrap fixedOk_winX A.unch
  have ia := A.fields hc F hbp hpx hpy
  obtain ⟨ja,za,pa⟩ := A.peer hc hC F hrep
  have zeroa : tmv c.C c.n base a (cfg c).zero=0 := by
    change toM _ _ (wordsVal a.mem base (c.sl ZERO) c.n)=0
    rw [Fₐ.zero,toM_zero]
  have ht : (cfg c).tbl<2^31 := by change c.sl WT<2^31; rw [sl_eq,hn]; decide
  have ho : (cfg c).one<c.C.p := Nat.mod_lt _ (by omega)
  have hov : toM c.C.p (2^(64*(cfg c).M.n)) (cfg c).one=1 := by
    change toM c.C.p (2^(64*c.n)) (c.mont 1)=1
    rw [toM_cmont hc]
    rfl
  apply WP.seq
  refine WP.mono (window_ok hCurve hL hm hC hc.am3 hO ht ho hov (by change 2≤52; decide)
    A.fit hP pa ia ja za zeroa A.bits) fun b B => ?_
  have ub : Unch base (windowW c) a.mem b.mem := B.keep.unch
  have Fᵦ := Fₐ.unch hc.n10 hs.nowrap (fixedOk_windowW hn) ub
  have rz : sv c base b RZ<c.C.p := B.field.lt _ (by simp [scalarLive,jacCoords,cfg,Cfg.winCfg,Cfg.pt])
  have tb : ∀ t<64*c.n,b.mem (off base (bitsAt c.n 1+t))=if (c.C.p-2).testBit t then 1 else 0 := by
    intro t ht'
    rw [tbl_unch ub hc.n10 hs.nowrap (by decide) ht' (bits_apart_windowW hn (by decide) ht'),
      tbl_unch A.unch hc.n10 hs.nowrap (by decide) ht' (tbl_apart_winX (by decide) ht')]
    exact ht₁ t ht'
  refine WP.mono (pPow_ok hc B.field.scr B.field.mod rz Fᵦ.onep tb) fun t ⟨kt,ut,lt,vt⟩ => ?_
  have et : ∀ {i},i<45 → i∉[ACC,PT,TMP] → sv c base t i=sv c base b i :=
    fun hi he => sv_unch ut hc.n10 hs.nowrap hi (apart_pwW hi he)
  have tv : ∀ {i},i<45 → i∉[ACC,PT,TMP] → tmv c.C c.n base t (c.sl i)=tmv c.C c.n base b (c.sl i) := by
    intro i hi he
    change toM _ _ (sv c base t i)=toM _ _ (sv c base b i)
    rw [et hi he]
  refine ⟨B.field.scr.of_keepRegs kt (rdi_not_invClob _),?_,(A.unch.trans ub).trans ut,?_,lt,?_,?_⟩
  · have ca : ∀ r∈[Reg.rax,.r8,.rdx,.rbx],r∈invClob c.n := by rw [hn]; decide
    have cb : ∀ r∈clob (cfg c).M.n++[Reg.rbx],r∈invClob c.n := by
      change ∀ r∈clob c.n++[Reg.rbx],r∈invClob c.n
      rw [hn]; decide
    exact ((A.keep.mono ca).trans (B.keep.regs.mono cb)).trans kt
  · intro hk
    rw [tv (i:=RX) (by decide) (by decide),tv (i:=RZ) (by decide) (by decide)]
    have ek : wordsVal s.mem base (c.sl K) 4=sv c base s K := by
      change _=wordsVal s.mem base (c.sl K) c.n
      rw [hn]
    have hb := B.point (by rw [ek]; exact hk)
    change XOnly c.C (tmv c.C c.n base b (c.sl RX)) (tmv c.C c.n base b (c.sl RZ))
      (mul (wordsVal s.mem base (c.sl K) 4) P) at hb
    rw [ek] at hb
    exact hb
  · change _=toM _ _ (sv c base t RZ)^_
    rw [et (i:=RZ) (by decide) (by decide)]
    exact vt
  · rw [et (i:=RZ) (by decide) (by decide)]
    exact rz

end VG.Proof.Ecdh.X86_64.Secret
