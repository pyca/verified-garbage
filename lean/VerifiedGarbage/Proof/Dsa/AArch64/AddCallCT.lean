module

public import VerifiedGarbage.Proof.Dsa.AArch64.ProductCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.ProductCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant time of loading and adding DSA scalars -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem callLoad_context {p : PowerCallPublic} {s : State} {a sp sl : Nat}
    {ptr : Addr} {bs : List Byte} (ha : a < 8) (han : a ≠ aN) (hsp : sp < 32) (hsl : sl < 32)
    (h : PowerCallPre p s) (hp : word s.mem p.x.B (8 * sp) = ptr)
    (hl : word s.mem p.x.B (8 * sl) = BitVec.ofNat 64 bs.length)
    (hs : Src s p.x.B p.x.Z ptr bs) (h1 : 1 ≤ bs.length)
    (hfit : (bs.length + 7) / 8 ≤ p.x.wx) :
    WP isa (Arithmetic.load a sp sl) s (PowerCallPre p) := by
  have hlen : bs.length < 2 ^ 31 := by
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega
  exact WP.mono (load_mod_ok h.1 h.2.1 p.lower p.fits p.upper ha han hsp hsl hp hl hs h1 hlen hfit)
    fun t ⟨hc, hm, _, _, hf, hk⟩ => ⟨hc, hm, h.2.2.frame h.1 hf hk⟩

theorem addCall_ct :
    RelCT isa (Two (fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic))
      (seqs [Arithmetic.load aX arg argLen, Arithmetic.load aXm arg2 arg2Len, Crt.addMod aY aX aXm])
      (fun _ _ => True) := by
  unfold seqs
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => (⟨p.x, p.base, p.baseLen⟩ : BPub)) ?_
      (loadArr_ct (j := aX) (sp := arg) (sl := argLen) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, _, bb, _, hp, hl, _, _, hbl, _, hb, _⟩
    refine ⟨p.minv, bb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hbl, hb, hbl ▸ p.basePositive, ?_, hbl ▸ p.baseFits⟩
    have hbw : (bb.length + 7) / 8 ≤ p.x.wx := hbl ▸ p.baseFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega
  · intro p s h
    obtain ⟨bb, _, hp, hl, _, _, hbl, _, hb, _⟩ := h.2.2
    exact callLoad_context (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hbl ▸ p.basePositive) (hbl ▸ p.baseFits)
  refine RelCT.seq (two_post (Ψ := fun p : ProductCallPublic => PowerCallPre p.toPowerCallPublic)
    (two_map (fun p : ProductCallPublic => p.bytes) ?_
      (loadArr_ct (j := aXm) (sp := arg2) (sl := arg2Len) (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
  · intro p s ⟨hc, _, _, eb, _, _, hp, hl, _, hel, _, hb⟩
    refine ⟨p.minv, eb, hc, p.lower, p.fits, p.upper, by decide, by decide, by decide,
      hp, hl, hel, hb, hel ▸ p.expPositive, ?_, hel ▸ p.secondFits⟩
    have hbw : (eb.length + 7) / 8 ≤ p.x.wx := hel ▸ p.secondFits
    have hw48 : p.x.wx ≤ 48 := p.width48
    omega
  · intro p s h
    obtain ⟨_, eb, _, _, hp, hl, _, hel, _, hb⟩ := h.2.2
    exact callLoad_context (by decide) (by decide) (by decide) (by decide)
      h hp hl hb (hel ▸ p.expPositive) (hel ▸ p.secondFits)
  exact two_map (fun p : ProductCallPublic => p.x.ws)
    (fun _ _ h => ⟨_, h.1.good, Nat.le_refl _⟩)
    (addMod_ct (by decide) (by decide) (by decide) (by taint_decide))

end VG.Proof.Dsa.AArch64
