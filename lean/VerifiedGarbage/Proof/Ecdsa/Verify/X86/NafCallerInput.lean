import VerifiedGarbage.Proof.Ecdsa.Verify.X86.CombInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86.NafMulTiming

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86 VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open Spec.Weierstrass

abbrev vPeer (c : Cfg) (s₀ : State) : Point c.C :=
  Ecdh.X86.peerPt c (s₀.mem (ptr s₀ 0)=4) (keyX c s₀) (keyY c s₀)
abbrev vScalar (c : Cfg) (s₀ : State) : Nat :=
  (Fin.ofNat c.C.n (sigR c s₀)*Fin.ofNat c.C.n (sigS c s₀)^(c.C.n-2)).val
abbrev vPeerX (c : Cfg) (s₀ : State) : Fe c.C :=
  if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
abbrev vPeerY (c : Cfg) (s₀ : State) : Fe c.C :=
  if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy

abbrev VPointInput (s₀ : State) (base : Addr) (s : State) : Prop :=
  Keep p256Comb s₀ base s ∧ VPublicValues p256Comb s₀ base s

theorem vValues_naf {c : Cfg} (hc : CfgOk c) (hC : Law c.C)
    {s₀ r₀ s : State} {base : Addr} (hs : Keep c r₀ base s)
    (hv : VPublicValues c s₀ base s) :
    NafMulInput c base (vPeer c s₀) (vScalar c s₀) (vPeerX c s₀) (vPeerY c s₀) s :=
  ⟨hs.scr,⟨r₀.gpr,hs.fixed⟩,hv.px_lt,hv.py_lt,hv.point hc hC hs.fixed,hv.px,hv.py,hv.scalar⟩

theorem vPointInput_naf (hc : CfgOk p256Comb) (hC : Law p256Comb.C)
    {s₀ s : State} {base : Addr} (h : VPointInput s₀ base s) :
    NafMulInput p256Comb base (vPeer p256Comb s₀) (vScalar p256Comb s₀) (vPeerX p256Comb s₀) (vPeerY p256Comb s₀) s :=
  vValues_naf hc hC h.1 h.2

theorem vKeepNafWf {s₀ s : State} {extra : List Region} (hp : VPre p256Comb s₀ extra)
    (h : Keep p256Comb s₀ (ptr s₀ 3) s) : VG.X86.Taint.Wf nafτ s := by
  have hw := vKeepCombWf hp h
  exact ⟨hw.lens,hw.bases,hw.wbases,(fun he => (Nat.not_lt_zero _ he).elim),
    hw.argBases,hw.stk,hw.frames,hw.room⟩

theorem vKeepNafPublic {s₀ t₀ s t : State} {extra₁ extra₂ : List Region}
    (hp : VPre p256Comb s₀ extra₁) (hq : VPre p256Comb t₀ extra₂)
    (ks : Keep p256Comb s₀ (ptr s₀ 3) s) (kt : Keep p256Comb t₀ (ptr t₀ 3) t)
    (he : s₀.gpr .esp=t₀.gpr .esp) (ha : ∀ j<4,arg s₀ j=arg t₀ j) : NafPublic s t := by
  refine ⟨vKeepNafWf hp ks,vKeepNafWf hq kt,?_,ks.esp.trans (he.trans kt.esp.symm),?_⟩
  · apply widen32_inj
    exact ks.scr.edi.trans ((congrArg (BitVec.setWidth 64) (ha 3 (by decide))).trans kt.scr.edi.symm)
  · rw [ks.wr,kt.wr,hp.wr,hq.wr]
    simp only [ptr,ha 3 (by decide)]

end VG.Proof.Ecdsa.Verify.X86
