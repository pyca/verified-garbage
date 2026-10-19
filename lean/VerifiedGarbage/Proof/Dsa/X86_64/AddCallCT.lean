module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProductCallCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ProductCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.AddCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.AddCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Constant time of loading and adding DSA scalars -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64 VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
    (fun p _ h => ⟨⟨_, h.1.good, Nat.le_refl _⟩,
      by change 1 ≤ p.x.wx; have hw : 2 ≤ p.x.wx := p.lower; omega,
      by change p.x.wx < 2 ^ 31; have hw : p.x.wx ≤ p.x.w := p.fits; have hw' : p.x.w < 2 ^ 30 := p.upper; omega⟩)
    (addCode_ct (by decide) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.X86_64
