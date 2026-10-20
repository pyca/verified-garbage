module
public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup

import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFinish
import VerifiedGarbage.Proof.Bignum.FoldedPublic
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedDispatch
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedFixed
import VerifiedGarbage.Proof.Bignum.AArch64.FoldedExp
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Both routes finish in ordinary form. The equality of the encoded base
with the ordinary input is only needed for the arithmetic result, not for
safety on malformed cached Montgomery data. -/
theorem phase_ok (M : Mont) {s : State} {B ep : Addr} {Z w N X x u L : Nat} {mi : BitVec 64}
    {eb : List Byte} (hc : ExpCtx s B Z w mi N X) (hZ : slot w 8 ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2^31) (hR : Nat.Coprime (2^(64*w)) N) (hN : 1 < N)
    (hX : X < N) (hx : X % N = x * 2^(64*w) % N)
    (hu : wv s.mem B (slot w aX) w = u) (hone : wv s.mem B (slot w aOne) w = 1)
    (he : word s.mem B (8*sE) = ep) (hlen : word s.mem B (8*sElen) = BitVec.ofNat 64 L)
    (hs : Src s B Z ep eb) (hel : eb.length = L) (hL1 : 1 ≤ L) (hL : L < 2^31) :
    WP isa (.seq (Folded.fastLoop M.mm) (Folded.finishFused M.mm)) s fun t =>
      Good t B Z w mi ∧ wv t.mem B (slot w aY) w < N ∧
      (x % N = u % N → wv t.mem B (slot w aY) w = u^Spec.Rsa.os2ip eb % N) ∧
      Frm B (pExpRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hMod (r : Nat) : r % N < N := Nat.mod_lt r (by omega)
  have hFactor (e : Nat) (hxu : x % N = u % N) :
      x^e * u % N = u^(e+1) % N := factor_congr hxu
  have hb : B.toNat + slot w 8 ≤ 2^64 := by have := hc.good.scr.nowrap; omega
  apply WP.seq
  apply fastLoop_dispatch M hc.good hZ hL he hlen hs hel
  · intro a hm ka _ h65
    have ca := hc.mem hm ka (by decide)
    refine WP.mono (fixedLoop_ok M (x := x) (u := u) ca hZ hw hw' hR hX hx (by rw [hm]; exact hu))
      fun b ⟨cb,yb,mb,fb,kb⟩ => ?_
    refine WP.mono (finish_fast_ok M cb.good hZ mb) fun t ⟨mt,kt⟩ => ?_
    have ct := cb.mem mt kt (by decide)
    refine ⟨ct.good, ?_, ?_, ?_, ((ka.trans kb).trans kt).mono (by decide)⟩
    · rw [mt,yb]; exact hMod (x^65536*u)
    · intro hxu
      rw [mt,yb,h65]
      have hf := hFactor 65536 hxu
      simp only [show (65536:Nat)+1=65537 from rfl] at hf
      exact hf
    · rw [hm] at fb
      rw [mt]
      exact fb
  · intro a hm ka _
    have ca := hc.mem hm ka (by decide)
    have hsa := hs.congrK (by rw [hm]; exact InScr.refl _ _ _) ka
    refine WP.mono (pExpLoop_ok (M := M) (x := x) ca hZ hw hw' hR hX hx
      (by rw [hm]; exact he) (by rw [hm]; exact hlen) hel hL1 hL
      (fun i hi => hsa.rd i (by omega)) (fun i hi => hsa.val i (by omega))
      (fun i hi => hsa.out i (by omega))) fun b ⟨cb,yb,fb,kb⟩ => ?_
    have ob : wv b.mem B (slot w aOne) w = 1 := by
      rw [one_preserved fb hb,hm]; exact hone
    refine WP.mono (finish_slow_ok M cb hZ hw hw' hR hN ob yb) fun t ⟨gt,yt,ft,kt⟩ => ?_
    refine ⟨gt, ?_, ?_, ?_, ((ka.trans kb).trans kt).mono (by decide)⟩
    · rw [yt]; exact hMod _
    · intro hxu
      rw [yt,Nat.pow_mod,hxu,← Nat.pow_mod]
    · rw [hm] at fb
      exact fb.trans (ft.mono (by simp [finRanges,pExpRanges,pBitRanges,bitRanges]))

end VG.Proof.Bignum.AArch64.FoldedPublic
