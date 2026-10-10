import VerifiedGarbage.Proof.P256.EcdhJac.State
import VerifiedGarbage.Proof.Ecdh.AArch64.Window
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.P256.EcdhJac.Finish
import VerifiedGarbage.Proof.P256.EcdhJac.Multiply
import VerifiedGarbage.Proof.P256.EcdhJac.Lit

/-! ## `Prep` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Impl.Ecdsa.AArch64 (p256)
open VG.Proof.Ecdsa.AArch64 (CfgOk sv)
open Spec.Weierstrass

private abbrev c := VG.Impl.Ecdsa.AArch64.p256

def prepWrites : List (Nat×Nat) := [(c.winK,40),(c.winBits,320)]

theorem prep_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base 8192)
    {g : Reg→BitVec 64} (hf : VG.Proof.Ecdsa.AArch64.Fixed c base g s.mem) {P : Point C}
    (hpx : sv c base s VG.Impl.Ecdh.AArch64.PX<C.p)
    (hpy : sv c base s VG.Impl.Ecdh.AArch64.PY<C.p)
    (hrep : Rep C (tmv C 4 base s K.P.x) (tmv C 4 base s K.P.y) (tmv C 4 base s K.P.z) P) :
    WP isa Impl.P256.EcdhJac.prep s fun t=>
      Frame base prepWrites s t ∧ Fixed base P (sv c base s VG.Impl.Ecdsa.AArch64.K) t ∧
      KeepRegs (.x19::clob 4) s t := by
  have hk : wordsVal s.mem base (c.sl VG.Impl.Ecdsa.AArch64.K) 4<2^256 := wordsVal_lt ..
  rw [Impl.P256.EcdhJac.prep]
  refine WP.seq (WP.mono (addConst_ok hs (n:=4) (src:=c.sl VG.Impl.Ecdsa.AArch64.K)
    (dst:=c.winK) (c:=offset) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by
      decide +kernel) (by
      have hb : offset+2^256<2^(64*(4+1)) := by decide +kernel
      omega)) fun s₁ ⟨e₁,k₁,o₁⟩=>?_)
  have hs₁:=hs.of_keepRegs k₁ (x0_not_clob _)
  refine WP.mono (bits_ok hs₁ (n:=5) (src:=c.winK) (dst:=c.winBits)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨b₂,k₂,o₂⟩=>?_
  have unch : Unch base prepWrites s.mem t.mem := o₁.unch.trans o₂.unch
  have frame : Frame base prepWrites s t := ⟨(k₁.mono clob_regs).trans (k₂.mono (by decide)),unch⟩
  have ft := hf.unch hc.n10 hs.nowrap (show VG.Proof.Ecdsa.AArch64.FixedOk c prepWrites from by unfold VG.Proof.Ecdsa.AArch64.FixedOk; decide) unch
  have hw (x : Nat) (hx : x∈ro) : wordsVal t.mem base x 4=wordsVal s.mem base x 4 :=
    unch.wordsVal (by
      have hh : ∀ x∈ro,∀ w∈prepWrites,x+32≤w.1 ∨ w.1+w.2≤x := by decide
      exact hh x hx) (by
      have hh : ∀ x∈ro,x+32≤2^64 := by decide
      exact hh x hx)
  have hv (x : Nat) (hx : x∈ro) : tmv C 4 base t x=tmv C 4 base s x := by
    unfold tmv; rw [hw x hx]
  refine ⟨frame,⟨⟨frame.scr regs_x0 hs,VG.Proof.Ecdsa.AArch64.modP_of hc.toBaseCfgOk ft.mp,
    (by decide),?_,fun _ _=>rfl⟩,ft.zero,?_,?_,?_⟩,(k₁.mono (by decide)).trans (k₂.mono (by decide))⟩
  · intro x hx
    change x∈[c.sl VG.Impl.Ecdsa.AArch64.AP,c.sl VG.Impl.Ecdsa.AArch64.BM,
      c.sl VG.Impl.Ecdsa.AArch64.ZERO,c.sl VG.Impl.Ecdh.AArch64.PX,c.sl VG.Impl.Ecdh.AArch64.PY,
      c.sl VG.Impl.Ecdsa.AArch64.ONEP] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact lt_of_eq_of_lt ft.ap (Nat.mod_lt _ (by have hh:=hc.p_ge; omega))
    · exact lt_of_eq_of_lt ft.bm (Nat.mod_lt _ (by have hh:=hc.p_ge; omega))
    · exact lt_of_eq_of_lt ft.zero (by decide)
    · change wordsVal t.mem base K.P.x 4<C.p
      rw [hw K.P.x (by decide)]; exact hpx
    · change wordsVal t.mem base K.P.y 4<C.p
      rw [hw K.P.y (by decide)]; exact hpy
    · exact lt_of_eq_of_lt ft.onep (Nat.mod_lt _ (by have hh:=hc.p_ge; omega))
  · rw [hv _ (by decide),hv _ (by decide),hv _ (by decide)]; exact hrep
  · change toM c.C.p (2^(64*c.n)) (wordsVal t.mem base (c.sl VG.Impl.Ecdsa.AArch64.ONEP) c.n)=1
    rw [ft.onep]
    change toM c.C.p (2^(64*c.n)) (c.mont 1)=1
    rw [VG.Proof.Ecdsa.AArch64.toM_cmont hc]
    rfl
  · intro i hi
    have hh:=b₂ i (by omega)
    rw [e₁] at hh
    exact hh

end VG.Proof.P256.EcdhJac

end

/-! ## `Adapter` -/

section

namespace VG.Proof.P256.EcdhJac
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdsa.AArch64

theorem mulWithInverse_of_window (hc : CfgOk p256) {ip : Prog isa} {W : List (Nat × Nat)}
    (hfixed : FixedOk p256 W)
    (hslots : ∀ i,i<45 → i∉[VG.Impl.Ecdsa.AArch64.ACC,VG.Impl.Ecdsa.AArch64.TMP] → ∀w∈W,
      p256.sl i+8*p256.n≤w.1 ∨ w.1+w.2≤p256.sl i)
    (hflag : ∀w∈W,p256.sl VG.Impl.Ecdsa.AArch64.FLAG+8≤w.1 ∨ w.1+w.2≤p256.sl VG.Impl.Ecdsa.AArch64.FLAG)
    (hip : ∀ {s : State} {base : Addr},Scr s base 8192 → ModOkA p256.MP' 8192 C.p s.mem base →
      wordsVal s.mem base (p256.sl VG.Impl.Ecdsa.AArch64.RZ) p256.n<C.p →
      WP isa ip s fun t => KeepRegs (powClob p256.n) s t ∧ Unch base W s.mem t.mem ∧
        wordsVal t.mem base (p256.sl VG.Impl.Ecdsa.AArch64.ACC) p256.n<C.p ∧
        toM C.p (2^(64*p256.n)) (wordsVal t.mem base (p256.sl VG.Impl.Ecdsa.AArch64.ACC) p256.n)=
          toM C.p (2^(64*p256.n)) (wordsVal s.mem base (p256.sl VG.Impl.Ecdsa.AArch64.RZ) p256.n)^(C.p-2))
    (hw : ∀ {base : Addr} {P : Point C} {k : Nat} {s : State},onCurve C P=true → k<2^256 →
      Fixed base P k s → WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s)) :
    MulWithInverseOk p256 mq ip := by
  intro base s hs g hf P hP hpx hpy hrep rest R h
  have hk : sv p256 base s VG.Impl.Ecdsa.AArch64.K<2^256 := wordsVal_lt ..
  apply WP.assoc'
  refine WP.seq (WP.mono (prep_ok hc hs hf hpx hpy hrep) fun u ⟨fu,hu,ku⟩=>?_)
  refine WP.seq (WP.mono (wrapped_ok hu (fun v hv=>hw hP hk hv)) fun t ht=>?_)
  have ready : MulReady base g P (sv p256 base s VG.Impl.Ecdsa.AArch64.K) s t := by
    have unch : Unch base (prepWrites++wrappedWrites) s.mem t.mem := fu.unch.trans ht.frame.unch
    refine ⟨ht.field.scr,hf.unch hc.n10 hs.nowrap (by unfold FixedOk; decide) unch,?_,?_,
      ht.frame.regs.rd.trans fu.regs.rd,ht.frame.regs.wr.trans fu.regs.wr,?_,?_,ht.point,?_⟩
    · intro r hr
      rw [ht.restored r (by
        have hh : ∀ r∈[Reg.x26,.x27,.x28],r∈extraRegs := by decide
        exact hh r hr),ku.gpr r (by
        have hh : ∀ r∈[Reg.x26,.x27,.x28],r∉Reg.x19::clob 4 := by decide
        exact hh r hr)]
    · rw [ht.restored .x20 (by decide),ku.gpr .x20 (by decide)]
    · exact unch.word (by decide) (by decide)
    · exact unch.wordsVal (by decide) (by decide)
    · exact ht.field.lt K.R.z (by decide)
  exact finishInverse_ok hc hfixed hslots hflag ready
    (hip ready.scr (modP_of hc.toBaseCfgOk ready.fixed.mp) ready.rz_lt) h

theorem mul_of_window (hc : CfgOk p256)
    (hw : ∀ {base : Addr} {P : Point C} {k : Nat} {s : State},onCurve C P=true → k<2^256 →
      Fixed base P k s → WP isa Impl.P256.EcdhJac.window s (WindowPost base P k s)) :
    MulOk p256 mq :=
  mulWithInverse_of_window hc fixedOk_chainWc (fun _ hi hn => apart_chainWc hi hn)
    (by decide) (pPow_ok hc) hw

end VG.Proof.P256.EcdhJac

end
