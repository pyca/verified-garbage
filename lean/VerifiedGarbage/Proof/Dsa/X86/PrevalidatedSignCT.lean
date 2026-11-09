module

public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.X86.SignLayout
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Dsa.X86.SignatureTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Dsa.X86.CallMinusTiming
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.CheckingDispatchCT
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.X86.LayoutAgreement
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.SignSizedTiming
import VerifiedGarbage.Proof.Dsa.X86.SignTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Framework.RelCTAssoc

-- separate module: the constant-time proof costs more than its imports, and the contract
-- module's satisfiability witness should not re-check it.

/-! # i686 prevalidated signing traces from public arguments

As the signer's, they branch only on the public widths and the shape of the
public domain. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem prevalidatedSignatureReady_compute {L : CallLayout} {out : BitVec 32} {s0 : State}
    (R : CallReady L s0) (O : SignatureReady L out s0)
    (G : (.input .g, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : ∃ full, (.input .digest, full) ∈ L.inputs ∧ L.digestPrefix ≤ full) (hd : L.digestPrefix ≤ 32) :
    WP isa (PrevalidatedSign.compute L.pLen L.qLen) s0 (SignatureReady L out) := by
  refine WP.mono (prevalidatedSignCompute_ok R.moduli (R.buffers _ G)
    (R.buffers _ X) (R.buffers _ K) ((R.buffers _ D.choose_spec.1).prefix D.choose_spec.2) hd R.prefixLen
    rfl rfl rfl rfl) fun sf ⟨M, _, _, F, E⟩ => ?_
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

theorem callPrevalidatedSignCompute_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : CallOperand L (.input .g) L.pLen)
    (K : CallOperand L (.input .nonce) L.qLen) (X : CallOperand L (.input .x) L.qLen)
    (D : CallOperand L (.input .digest) L.digestPrefix) (hd : L.digestPrefix < 2 ^ 32) :
    RelCT isa (CallPair L) (PrevalidatedSign.compute L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have R := CallOperand.localBuffer L r L.qLen (by decide) (by change 14720 + L.qLen ≤ 15712; omega)
  have S := CallOperand.localBuffer L s L.qLen (by decide) (by change 14752 + L.qLen ≤ 15712; omega)
  unfold PrevalidatedSign.compute Core.sequence
  dsimp only [List.foldr]
  exact RelCT.seq (callMinusQ_relCT L qMinusTwo Q (by decide) (by change 14912 + L.qLen ≤ 15712; omega))
    (RelCT.seq (callRange_relCT L L.qLen .q (.input .nonce) false Q K (by omega) (by omega) L.aligned.2)
    (RelCT.seq (callSign_relCT L P Q G K X D hd)
    (RelCT.seq (RelCT.seq
      (callZero_relCT L L.qLen (.local r) true R (by omega) (by omega) L.aligned.2)
      (callZero_relCT L L.qLen (.local s) true S (by omega) (by omega) L.aligned.2))
      (RelCT.block_nil (fun _ _ h => h)))))

theorem callPrevalidatedSignBody_relCT (L : CallLayout) (out : BitVec 32)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : ∃ full, (.input .digest, full) ∈ L.inputs ∧ L.digestPrefix ≤ full) (hd : L.digestPrefix ≤ 32) :
    RelCT isa (fun s t => CallPair L s t ∧ SignatureReady L out s ∧ SignatureReady L out t)
      (PrevalidatedSign.body L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold PrevalidatedSign.body
  refine RelCT.seq (M := isa) (R := fun s t => SignatureReady L out s ∧ SignatureReady L out t) ?_ ?_
  · have C := callPrevalidatedSignCompute_relCT L P Q (.inl ⟨_, G, Nat.le_refl _⟩)
      (.inl ⟨_, K, Nat.le_refl _⟩) (.inl ⟨_, X, Nat.le_refl _⟩) (.inl D) (by omega)
    intro s t tr ur sf tf ⟨H, S, T⟩ E F
    exact ⟨(C _ _ _ _ _ _ H E F).1,
      wp_result (prevalidatedSignatureReady_compute H.1 S G X K D hd) E,
      wp_result (prevalidatedSignatureReady_compute H.2 T G X K D hd) F⟩
  · apply RelCT.assoc
    exact RelCT.seq (writeSignature_relCT L out) (result_relCT.mono
      (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
      (fun _ _ h => h))

theorem prevalidatedSignSized_relCT (L : CallLayout) (digestLen : Nat) (out : BitVec 32)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs)
    (X : (.input .x, L.qLen) ∈ L.inputs) (K : (.input .nonce, L.qLen) ∈ L.inputs)
    (D : (.input .digest, digestLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8)) :
    RelCT isa (fun s t => (ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t) ∧
      OutputCallReady L out s ∧ OutputCallReady L out t)
      (PrevalidatedSign.sized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  unfold PrevalidatedSign.sized
  refine RelCT.seq (signingShape_relCT L digestLen out P Q stable hd)
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  by_cases valid : shapeValid L.p L.q
  · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
    have B := shape_digest_width valid
    have CT := callPrevalidatedSignBody_relCT L out (.inl ⟨_, P, Nat.le_refl _⟩) (.inl ⟨_, Q, Nat.le_refl _⟩)
      G X K ⟨_, D, by rw [hd]; exact Nat.min_le_left _ _⟩ (by rw [hd]; omega)
    exact CT.mono (fun _ _ H => ⟨⟨(H.1.2 True.intro).1.ready, (H.1.2 True.intro).2.ready⟩,
      H.2.1.signature (H.1.2 True.intro).1, H.2.2.signature (H.1.2 True.intro).2⟩) (fun _ _ h => h)
  · simp only [valid, decide_false, Bool.not_false, ite_true]
    exact (signFailure_relCT L.base L.size L.saved).mono
      (fun _ _ H => ⟨H.2.1.scr, H.2.2.scr, H.2.1.pointer.trans H.2.2.pointer.symm,
        H.2.1.qLength.trans H.2.2.qLength.symm⟩) (fun _ _ h => h)

theorem prevalidatedSigningOperation_agrees {s t : State} (A : SigningABI s) (B : SigningABI t)
    (args : ∀ i < 11, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (P : (signKey s).params.p = (signKey t).params.p)
    (Q : (signKey s).params.q = (signKey t).params.q)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PrevalidatedSign.sign s tr sf) (F : Exec isa PrevalidatedSign.sign t ur tf) :
    tr = ur := by
  let L := signLayout s A
  have LayoutEq := signLayout_eq A B args SP P Q
  have Size := args 10 (by decide)
  have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 9 (by decide))
  have PL := args 4 (by decide)
  have QL := args 6 (by decide)
  have DL := args 8 (by decide)
  let R := fun u v =>
    Installed (argumentPointer s 9) ((arg s 10).toNat * 8) Entry.signArguments 2 4 6 s u ∧
    Installed (argumentPointer t 9) ((arg t 10).toNat * 8) Entry.signArguments 2 4 6 t v
  have Invariant : CompareInvariant L.base L.size R := by
    refine ⟨?_, fun _ _ _ _ H K1 K2 O1 O2 => ⟨H.1.compare K1 O1, H.2.compare K2 O2⟩⟩
    intro u v H
    refine ⟨H.1.scr, ?_⟩
    simpa only [L, signLayout, Base, Size] using H.2.scr
  have hp : ∀ u v, R u v → (pointerValue L.base u (.input .pLen)).toNat = L.pLen ∧
      (pointerValue L.base v (.input .pLen)).toNat = L.pLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (4, .pLen) (by decide)), ?_⟩
    simpa only [L, signLayout, Base, PL] using congrArg BitVec.toNat (H.2.arguments (4, .pLen) (by decide))
  have hq : ∀ u v, R u v → (pointerValue L.base u (.input .qLen)).toNat = L.qLen ∧
      (pointerValue L.base v (.input .qLen)).toNat = L.qLen := by
    intro u v H
    refine ⟨congrArg BitVec.toNat (H.1.arguments (6, .qLen) (by decide)), ?_⟩
    simpa only [L, signLayout, Base, QL] using congrArg BitVec.toNat (H.2.arguments (6, .qLen) (by decide))
  have Sized : RelCT isa R (PrevalidatedSign.sized L.pLen L.qLen)
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply (prevalidatedSignSized_relCT L (arg s 8).toNat (arg s 0) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs]) (by simp [L, signLayout, signInputs])
      (by simp [L, signLayout, signInputs])
      (signInputs_shape _ _ _) rfl).mono ?_ (fun _ _ h => h)
    intro u v H
    refine ⟨⟨signingInstalled_ready A H.1, ?_⟩, signingInstalled_output A H.1, ?_⟩
    · simpa only [L, LayoutEq, DL] using signingInstalled_ready B H.2
    · simpa only [L, LayoutEq, args 0 (by decide)] using signingInstalled_output B H.2
  have Dispatch := generationDispatch_relCT PrevalidatedSign.sized
    [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)]
    L.pLen L.qLen L.base L.size R (VG.X86.Taint.Agree (workspaceTaint false)) Invariant L.saved
    (supportedWidths_member A.lengths) (by decide) hp hq Sized
  have Tail := RelCT.seq restore_relCT (RelCT.block_nil (M := isa) (P := fun _ _ => True) (fun _ _ h => h))
  change Exec isa (.seq (.block Entry.signEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) s tr sf at E
  change Exec isa (.seq (.block Entry.signEntry) (.seq _ (.seq (.block Entry.restore) (.block [])))) t ur tf at F
  cases E with
  | seq E1 Erest =>
    cases F with
    | seq F1 Frest =>
      obtain ⟨T1, _⟩ := installEntry_relCT 9 Entry.signArguments _ _ _ _ _ _
        ⟨SP, args 9 (by decide), (A.stackArgument (by decide : 9 < 11)).readSrc,
          (B.stackArgument (by decide : 9 < 11)).readSrc⟩ E1 F1
      have I := wp_result (signingEntry_ok A) E1
      have J := wp_result (signingEntry_ok B) F1
      cases Erest with
      | seq E2 E3 =>
        cases Frest with
        | seq F2 F3 =>
          obtain ⟨T2, Public⟩ := Dispatch _ _ _ _ _ _ ⟨I, J⟩ E2 F2
          have T3 := (Tail _ _ _ _ _ _ Public E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Dsa.X86
