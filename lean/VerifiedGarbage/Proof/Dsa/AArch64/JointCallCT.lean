module

public import VerifiedGarbage.Proof.Dsa.AArch64.JointPowerCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointPowerCT
public import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.CallHeadCT
import VerifiedGarbage.Proof.Dsa.AArch64.JointPower
meta import VerifiedGarbage.Proof.Dsa.AArch64.JointPower

/-! # Constant-time binding, execution and storage of a joint call -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure JointCallPublic extends Call3ProductPublic where
  qLen : Nat
  qPositive : 0 < qLen
  qBound : qLen < 2 ^ 31
  parentSpace : 344 ≤ bytes.x.o

def JointCallPublic.joint (p : JointCallPublic) : JointPublic :=
  { p.toPowerCallPublic with
    secondFits := p.secondFits
    qLen := p.qLen
    qPositive := p.qPositive
    qBound := p.qBound
    parentSpace := p.parentSpace }

def JointCallAfter (p : JointCallPublic) (s : State) : Prop :=
  JointPowerPre p.joint s ∧ FinishPre p.toPowerFinishPublic.result s

theorem jointFinish_ct (M : Mont) : RelCT isa (Two JointCallAfter)
    (.seq (Joint.power M.mm) (seqs Core.finish)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun p s => FinishPre p.toPowerFinishPublic.result s)
    (two_map JointCallPublic.joint (fun _ _ h => h.1) (jointPower_ct M)) ?_)
    (two_map (fun p : JointCallPublic => p.toPowerFinishPublic.result) (fun _ _ h => h) finish_ct)
  rintro p s ⟨⟨⟨hc, hm, gb, yb, hg, hgl, hy, hyl, hgL, hyL, hgs, hys⟩,
    eb, fb, he, hf, hL, hF, hl⟩, hout⟩
  exact WP.mono (jointPower_ok M hc p.lower p.width48 p.fits p.upper p.greater p.odd p.parentSpace
    hm.modulus hm.inverse hg hgl hgs (hgL ▸ p.basePositive) (hgL ▸ p.baseFits)
    hy hyl hys (hyL ▸ p.expPositive) (hyL ▸ p.secondFits) he hf (hF.trans hL.symm)
    (hL ▸ p.qPositive) (hL ▸ p.qBound) (hL ▸ hl))
    fun t ⟨hct, _, _, hft, hkt⟩ => hout.work hc hct hft hkt

theorem coreJoint_ct (M : Mont) {a b output : Operand} {o : Nat}
    (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) (ho : pointerFits output.pointer)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block (callHead a b output o)) hc).isSome = true) :
    RelCT isa (Two fun p : JointCallPublic => fun s =>
      Call3Pre a b output p.toCall3Public s ∧ p.x.o = o ∧ JointScalars p.joint s)
      (Core.joint M.mm o a b output) (fun _ _ => True) := by
  change RelCT isa _ (.seq (.block (callHead a b output o))
    (.seq (Joint.power M.mm) (seqs Core.finish))) _
  refine RelCT.seq (two_post (Ψ := JointCallAfter)
    (two_map (fun p : JointCallPublic => p.toCall3Public) (fun _ _ h => h.1) (callHead_ct hT)) ?_)
    (jointFinish_ct M)
  rintro p s ⟨h, heq, eb, fb, he, hf, hL, hF, hl⟩
  rw [← heq]
  refine WP.mono (callHead_run ha hb ho h) fun t ⟨⟨hpre, hout⟩, hframe, hk⟩ => ?_
  have hz : 176 ≤ p.x.Z := Nat.le_trans (by decide) p.extent
  refine ⟨⟨hpre, eb, fb, arguments_source hframe hk hz he,
    arguments_source hframe hk hz hf, hL, hF, ?_⟩, hout⟩
  change word t.mem p.x.B Field.qLen.offset = BitVec.ofNat 64 p.qLen
  rw [hframe.word_eq (by simp [argumentRanges, Field.offset]) (by decide)]
  exact hl

end VG.Proof.Dsa.AArch64
