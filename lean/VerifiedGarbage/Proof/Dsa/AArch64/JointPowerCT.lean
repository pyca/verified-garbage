module

public import VerifiedGarbage.Proof.Dsa.AArch64.JointRunCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointRunCT
import VerifiedGarbage.Proof.Dsa.AArch64.JointPrepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointPrepare
import VerifiedGarbage.Proof.Dsa.AArch64.JointPrepareCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointPrepareCT

/-! # Constant time of complete joint DSA exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def JointPowerPre (p : JointPublic) (s : State) : Prop :=
  PowerCallPre p.toPowerCallPublic s ∧ JointScalars p s

theorem JointScalars.frame {p : JointPublic} {s t : State} (h : JointScalars p s)
    (hc : SubCtx s p.x.B p.x.Z p.x.o p.x.w p.x.wx p.minv)
    (hf : Frm (off p.x.B p.x.o) (workRanges p.x.wx) s.mem t.mem) (hk : Keep mmRegs s t) :
    JointScalars p t := by
  obtain ⟨eb, fb, he, hfb, hL, hF, hl⟩ := h
  refine ⟨eb, fb, work_source hc hf hk he, work_source hc hf hk hfb, hL, hF, ?_⟩
  have hnow := hc.scr.nowrap
  have hhi := hc.hi
  have hsmall : 256 ≤ slot p.x.wx 8 := by unfold slot hdrBytes; omega
  rw [hf.word_below (fun r hr => (workRanges_ok p.x.wx r hr).2)
    (by omega) (by omega) (show Field.qLen.offset + 8 ≤ p.x.o from p.parentSpace)]
  exact hl

theorem jointPower_ct (M : Mont) : RelCT isa (Two JointPowerPre) (Joint.power M.mm) (fun _ _ => True) := by
  unfold Joint.power
  refine RelCT.seq (two_post (Ψ := JointRunPre)
    (two_map JointPublic.toProductCallPublic (fun _ _ h => h.1) (jointPrepare_ct M)) ?_)
    (jointRun_ct M)
  intro p s ⟨⟨hc, hm, gb, yb, hg, hgl, hy, hyl, hgL, hyL, hgs, hys⟩, hs⟩
  refine WP.mono (jointPrepare_ok M hc p.lower p.width48 p.fits p.upper p.greater p.odd hm.modulus hm.inverse
    hg hgl hgs (hgL ▸ p.basePositive) (hgL ▸ p.baseFits)
    hy hyl hys (hyL ▸ p.expPositive) (hyL ▸ p.secondFits))
    fun t ⟨hct, hmt, ht, hyt, hot, hft, hkt⟩ => ?_
  exact ⟨hct, hmt, ⟨_, _, ht⟩, hyt, hot, hs.frame hc hft hkt⟩

end VG.Proof.Dsa.AArch64
