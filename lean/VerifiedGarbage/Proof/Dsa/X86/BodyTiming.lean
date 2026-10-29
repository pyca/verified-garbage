module

public import VerifiedGarbage.Proof.Dsa.X86.SignatureTiming

import VerifiedGarbage.Proof.Dsa.X86.SignTiming
import VerifiedGarbage.Proof.Dsa.X86.SignCompute
import VerifiedGarbage.Proof.Dsa.X86.VerifyTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
/-! # Constant-time post-shape DSA bodies, including status and output -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem CallPair.workspace {L : CallLayout} {s t : State} (H : CallPair L s t) :
    VG.X86.Taint.Agree (workspaceTaint false) s t := by
  apply agree_regs (rs := [.edi])
  intro reg hr
  obtain rfl := List.mem_singleton.mp hr
  exact BitVec.eq_of_toNat_eq (H.1.moduli.scr.edi_toNat.trans H.2.moduli.scr.edi_toNat.symm)

theorem callVerifyBody_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen) (Y : CallOperand L (.input .y) L.pLen)
    (R : CallOperand L (.input .signature) L.qLen) (S : CallOperand L .signatureS L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (SignVerify.verifyBody L.pLen L.qLen)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (callVerifyCompute_relCT L P Q G Y R S D hd)
    (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))

theorem signatureReady_compute {L : CallLayout} {out : BitVec 32} {s0 : State}
    (R : CallReady L s0) (O : SignatureReady L out s0)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : ∃ full, (.input .digest, full) ∈ L.inputs ∧ L.digestPrefix ≤ full) (hd : L.digestPrefix ≤ 32) :
    WP isa (SignVerify.signCompute L.pLen L.qLen) s0 (SignatureReady L out) := by
  refine WP.mono (signCompute_ok R.moduli (R.buffers _ G) (R.buffers _ Y)
    (R.buffers _ X) (R.buffers _ K) ((R.buffers _ D.choose_spec.1).prefix D.choose_spec.2) hd R.prefixLen
    rfl rfl rfl rfl rfl) fun sf ⟨M, _, _, F, E⟩ => ?_
  refine ⟨M, ?_, ?_, O.fits, ?_, O.apart⟩
  · obtain ⟨accepted, mask⟩ := O.mask
    rw [mask] at F
    cases accepted
    · simp only [Bool.false_eq_true, ite_false] at F
      exact ⟨false, F.trans BitVec.zero_and⟩
    · simp only [ite_true, BitVec.allOnes_and] at F
      unfold mask32 at F
      split at F
      · exact ⟨true, F⟩
      · exact ⟨false, F⟩
  · rw [runFrame_pointer E.mem E.keeps (by decide) (by decide)]
    exact O.pointer
  · intro e k h
    rw [E.keeps.2.2]
    exact O.write e k h

theorem callSignBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g, L.pLen) ∈ L.inputs) (Y : (.input .y, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : ∃ full, (.input .digest, full) ∈ L.inputs ∧ L.digestPrefix ≤ full) (hd : L.digestPrefix ≤ 32) :
    RelCT isa (fun s t => CallPair L s t ∧ SignatureReady L out s ∧ SignatureReady L out t)
      (SignVerify.signBody L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold SignVerify.signBody
  refine RelCT.seq (M := isa) (R := fun s t => SignatureReady L out s ∧ SignatureReady L out t) ?_ ?_
  · have C := callSignCompute_relCT L P Q (.inl ⟨_, G, Nat.le_refl _⟩)
      (.inl ⟨_, Y, Nat.le_refl _⟩) (.inl ⟨_, K, Nat.le_refl _⟩) (.inl ⟨_, X, Nat.le_refl _⟩)
      (.inl D) (by omega)
    intro s t tr ur sf tf ⟨H, S, T⟩ E F
    exact ⟨(C _ _ _ _ _ _ H E F).1,
      wp_result (signatureReady_compute H.1 S G Y X K D hd) E,
      wp_result (signatureReady_compute H.2 T G Y X K D hd) F⟩
  · apply RelCT.assoc
    exact RelCT.seq (writeSignature_relCT L out) (result_relCT.mono
      (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
      (fun _ _ h => h))

end VG.Proof.Dsa.X86
