import VerifiedGarbage.Proof.P256.EcdhJac.State
import VerifiedGarbage.Proof.Ecdh.AArch64.Window

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
  refine ⟨frame,⟨⟨frame.scr regs_x0 hs,VG.Proof.Ecdsa.AArch64.modP_of hc ft.mp,
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
