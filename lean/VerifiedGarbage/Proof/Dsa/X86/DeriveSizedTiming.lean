module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.DeriveFailureTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
import VerifiedGarbage.Proof.Dsa.X86.DeriveBodyTiming

/-! # Derivation branches only on the public domain shape -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem deriveSized_relCT (L : CallLayout) (out : BitVec 32) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8))
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      KeyOutputReady L out s ∧ KeyOutputReady L out t)
      (Generate.deriveSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => (shapeValid L.p L.q → CallPair L s t) ∧
    Scr s L.base L.size ∧ Scr t L.base L.size ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t
  unfold Generate.deriveSized
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf = some (!decide (shapeValid L.p L.q)) ∧
      t.zf = some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S, T, Os, Ot⟩ E F
    have Trace := (shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S, T⟩ E F).1
    obtain ⟨Zs, Ms, Ks, Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt, Mt, Kt, Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    exact ⟨Trace, ⟨fun h => ⟨(Ms h).ready, (Mt h).ready⟩,
      S.scr.of_keeps Ks (by decide), T.scr.of_keeps Kt (by decide), Os.shape Fs Ks, Ot.shape Ft Kt⟩, Zs, Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (deriveBody_relCT L out P Q G X Params ho A).mono
        (fun _ _ H => ⟨H.1 valid, H.2.2.2⟩) (fun _ _ h => h)
    · simp only [valid, decide_false, Bool.not_false, ite_true]
      exact (deriveFailure_relCT L.pLen L.qLen L.base L.size L.saved).mono
        (fun _ _ H => ⟨H.2.1, H.2.2.1, H.2.2.2.1.pointer.trans H.2.2.2.2.pointer.symm⟩) (fun _ _ h => h)

end VG.Proof.Dsa.X86
