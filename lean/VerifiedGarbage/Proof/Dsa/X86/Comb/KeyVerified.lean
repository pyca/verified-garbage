module

public import Init.Prelude
public import VerifiedGarbage.Impl.Dsa.X86.CombKey
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.X86.Target

import VerifiedGarbage.Proof.Dsa.X86.Comb.GenerationStack
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Verified
import VerifiedGarbage.Impl.Dsa.X86.CombGenerate
import VerifiedGarbage.Proof.Dsa.X86.Comb.StageTiming
import VerifiedGarbage.Proof.Dsa.X86.GenerateTiming
import VerifiedGarbage.Proof.Dsa.X86.GenerateDomain
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Impl.Dsa.X86.Comb
import VerifiedGarbage.Proof.Dsa.X86.CallTiming
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.OutputTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.CheckingLayout
import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
import VerifiedGarbage.Proof.Dsa.X86.CheckingOperationCT
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.Comb.CheckInvoke
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.InvokeInputs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InlineInvokeTiming
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.Basic
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.AllocatedArgs
import VerifiedGarbage.Proof.Dsa.X86.DeriveFailureTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyOutputReady
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveBodyTiming
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.Deriving
import VerifiedGarbage.Proof.Dsa.X86.DerivingLayout
import VerifiedGarbage.Proof.Dsa.X86.DerivingOperationCT
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveInvoke
/-! Full correctness, constant time, and satisfiability for retained-table key generation. -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/ParametersTiming.lean`, which only this module imported.
section

/-! Public parameter preparation may branch only on the public domain values. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def PublicGenerator (L : CallLayout) (s t : State) : Prop :=
  CallPair L s t ∧ operandValue s L.base (.input .g) L.pLen=operandValue t L.base (.input .g) L.pLen

theorem parameters_relCT (L : CallLayout)
    (P : CallOperand L (.input .p) L.pLen) (Q : CallOperand L (.input .q) L.qLen)
    (G : (.input .g,L.pLen)∈L.inputs)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (PublicGenerator L) (parameters L.pLen L.qLen) (CallPair L) := by
  have W := L.lengths
  have Gop : CallOperand L (.input .g) L.pLen := .inl ⟨_,G,Nat.le_refl _⟩
  have bound : t+L.pLen≤usedBytes := by change 14944+L.pLen≤15712; omega
  have T := CallOperand.localBuffer L t L.pLen (by decide) bound
  change RelCT isa (PublicGenerator L) (.seq (Generate.domain L.pLen L.qLen)
    (.seq (power true L.pLen L.qLen .p (.input .g) (.input .q) t)
      (Validate.isOne L.pLen (.local t)))) (CallPair L)
  refine RelCT.seq (R := PublicGenerator L) ?_ (RelCT.seq ?_
    (callOne_relCT L L.pLen (.local t) T (by omega) (by omega) L.aligned.1))
  · intro s t tr ur sf tf ⟨Pair,Eq⟩ E F
    have H := generateDomain_relCT L P Q Gop _ _ _ _ _ _ Pair E F
    have Es := (wp_result (generateDomain_ok Pair.1.moduli (Pair.1.buffers _ G) rfl) E).2.2
    have Et := (wp_result (generateDomain_ok Pair.2.moduli (Pair.2.buffers _ G) rfl) F).2.2
    exact ⟨H.1,H.2,(Es.value (Pair.1.buffers _ G) (by change StablePointer (.input .g); decide) L.extent).trans
      (Eq.trans (Et.value (Pair.2.buffers _ G) (by change StablePointer (.input .g); decide) L.extent).symm)⟩
  · apply (stagePower_relCT true L (.input .g) (.input .q) _ P Gop Q (by decide) fits).mono
      ?_ (fun _ _ H => H)
    intro s t ⟨Pair,Eq⟩
    exact ⟨Pair,fun _ => ⟨Eq,Pair.1.moduli.qValue.trans Pair.2.moduli.qValue.symm⟩,
      fun h => Bool.noConfusion h⟩

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/CheckingSizedTiming.lean`, which only this module imported.
section

/-! The comb checker branches on public shape and public parameter values. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem checkingSized_relCT (L : CallLayout) (digestLen : Nat)
    (P : (.input .p,L.pLen)∈L.inputs) (Q : (.input .q,L.qLen)∈L.inputs)
    (G : (.input .g,L.pLen)∈L.inputs)
    (stable : ∀ input∈L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix=min digestLen (Spec.Dsa.bitLength L.q/8))
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      operandValue s L.base (.input .g) L.pLen=operandValue t L.base (.input .g) L.pLen)
      (checkSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => VG.X86.Taint.Agree (workspaceTaint false) s t ∧
    (shapeValid L.p L.q → PublicGenerator L s t)
  change RelCT isa _ (.seq (Shape.check L.pLen L.qLen) (.ite .e _ _)) _
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf=some (!decide (shapeValid L.p L.q)) ∧
      t.zf=some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S,T,Eq⟩ E F
    have CT := shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S,T⟩ E F
    obtain ⟨Zs,Ms,Ks,Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt,Mt,Kt,Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    have bound : 8248≤L.size := by have := L.extent; change 15712≤L.size at this; omega
    have Es := (S.buffers _ G).value_keep_shape Fs Ks (by decide)
      (by change ShapePointer (.input .g); decide) bound
    have Et := (T.buffers _ G).value_keep_shape Ft Kt (by decide)
      (by change ShapePointer (.input .g); decide) bound
    exact ⟨CT.1,⟨CT.2.1.1,fun h => ⟨⟨(Ms h).ready,(Mt h).ready⟩,Es.trans (Eq.trans Et.symm)⟩⟩,Zs,Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid,decide_true,Bool.not_true,Bool.false_eq_true,ite_false]
      exact (RelCT.seq (parameters_relCT L (.inl ⟨_,P,Nat.le_refl _⟩)
        (.inl ⟨_,Q,Nat.le_refl _⟩) G fits)
        (result_relCT.mono (fun _ _ H => H.workspace) (fun _ _ h => h))).mono
        (fun _ _ H => H.2 valid) (fun _ _ h => h)
    · simp only [valid,decide_false,Bool.not_false,ite_true]
      exact verifyFailure_relCT.mono (fun _ _ H => H.1) (fun _ _ h => h)

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/CheckingOperationTiming.lean`, which only this module imported.
section

/-! Whole checker timing reuses the common entry and dispatch proof. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem checkingInstalled_generator {s t : State} (A : CheckingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat*8) Generate.checkArguments 0 2 3 s t) :
    operandValue t (argumentPointer s 4) (.input .g) (arg s 2).toNat=(checkingParams s).g := by
  have L : 0<(arg s 2).toNat ∧ 0<(arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params,Bytes⟩ := I.input (by decide : (0,.p)∈Generate.checkArguments) A.keyBound
    (by rw [A.rd,A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr,Gptr,_⟩ := I.pointers (by decide)
  obtain ⟨_,_,_,Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  exact (congrArg (fun k : Spec.Dsa.Params => k.g) Value).symm

theorem checkingOperation_agrees {s t : State} (A : CheckingABI s) (B : CheckingABI t)
    (args : ∀ i<6, arg s i=arg t i) (SP : s.gpr .esp=t.gpr .esp)
    (P : (checkingParams s).p=(checkingParams t).p)
    (Q : (checkingParams s).q=(checkingParams t).q)
    (G : (checkingParams s).g=(checkingParams t).g)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa checkParameters s tr sf) (F : Exec isa checkParameters t ur tf) : tr=ur := by
  let L := checkingLayout s A
  have LayoutEq := checkingLayout_eq A B args SP P Q
  have DL := args 2 (by decide)
  refine checkingOperationWith_agrees A B args SP P Q checkSized ?_ E F
  apply (checkingSized_relCT L (arg s 2).toNat
    (by simp [L,checkingLayout,checkingInputs]) (by simp [L,checkingLayout,checkingInputs])
    (by simp [L,checkingLayout,checkingInputs]) (checkingInputs_shape _ _) rfl
    (Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength))).mono ?_
      (fun _ _ h => h)
  intro u v H
  refine ⟨checkingInstalled_ready A H.1,?_,?_⟩
  · simpa only [L,LayoutEq,DL] using checkingInstalled_ready B H.2
  · have V := checkingInstalled_generator B H.2
    have Base := congrArg (fun x : BitVec 32 => x.setWidth 64) (args 4 (by decide))
    change operandValue u (argumentPointer s 4) (.input .g) (arg s 2).toNat = _
    rw [checkingInstalled_generator A H.1,G]
    simpa only [L,checkingLayout,Base,DL] using V.symm

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/CheckInvokeTiming.lean`, which only this module imported.
section

/-! The internal checker receives only public domain values. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

theorem checkInvoke_ct : CheckInvokeCT checkInvoke := by
  intro s t tr ur sf tf ⟨s₀,t₀,A,B,Pub,Key,R,S,C,D⟩ E F
  let u := (allocated 4 s).withRegions (CheckCall.callRd s₀) (CheckCall.callWr s₀)
  let v := (allocated 4 t).withRegions (CheckCall.callRd t₀) (CheckCall.callWr t₀)
  have Au : CheckingABI u := allocated_checkingABI A R C
  have Bv : CheckingABI v := allocated_checkingABI B S D
  obtain ⟨rs,ws⟩ := CheckCall.call_covers A R
  obtain ⟨rt,wt⟩ := CheckCall.call_covers B S
  obtain ⟨uf,Eu⟩ := inlineInvoke_trace rs ws ((checkingOperation_spec Au).mono (fun _ _ => trivial)) E
  obtain ⟨vf,Ev⟩ := inlineInvoke_trace rt wt ((checkingOperation_spec Bv).mono (fun _ _ => trivial)) F
  have SP := esp_of_rf R.rf (pub_rBase Pub ▸ S.rf)
  have args (i : Nat) (hi : i<6) : arg u i=arg v i := by
    rw [check_allocated_args R C i hi,check_allocated_args S D i hi]
    interval_cases i <;> simp only [CheckCall.callVal] <;> exact pub_arg Pub _ (by decide)
  have KeyEq : (rInput s₀).key=(rInput t₀).key :=
    (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) Key
  have Params : checkingParams u=checkingParams v := by
    rw [check_allocated_params A R C,check_allocated_params B S D,
      pub_arg Pub 5 (by decide),pub_arg Pub 6 (by decide),KeyEq]
  exact ⟨checkingOperation_agrees Au Bv args (by change s.gpr .esp-4=t.gpr .esp-4; rw [SP])
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params)
    (congrArg Spec.Dsa.Params.g Params) Eu Ev,trivial⟩

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DeriveSizedTiming.lean`, which only this module imported.
section

/-! # Derivation branches only on the public domain shape -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem deriveSized_relCT (L : CallLayout) (out : BitVec 32) (digestLen : Nat)
    (P : (.input .p, L.pLen) ∈ L.inputs) (Q : (.input .q, L.qLen) ∈ L.inputs)
    (G : (.input .g, L.pLen) ∈ L.inputs) (X : (.input .nonce, L.qLen) ∈ L.inputs)
    (Params : (.input .p, 2 * L.pLen + L.qLen) ∈ L.inputs)
    (stable : ∀ input ∈ L.inputs, ShapePointer input.1)
    (hd : L.digestPrefix = min digestLen (Spec.Dsa.bitLength L.q / 8))
    (ho : out.toNat + (3 * L.pLen + 2 * L.qLen) ≤ 2 ^ 32)
    (A : Region.Disjoint ⟨L.base, L.size⟩ ⟨out.setWidth 64, 3 * L.pLen + 2 * L.qLen⟩)
    (fits : (layout ((L.pLen+7)/8) ((L.qLen+3)/4)).size≤L.size) :
    RelCT isa (fun s t => ShapeCallReady L digestLen s ∧ ShapeCallReady L digestLen t ∧
      KeyOutputReady L out s ∧ KeyOutputReady L out t ∧
      ContextReady L s ∧ ContextReady L t ∧ DomainReady L s ∧ DomainReady L t)
      (deriveSized L.pLen L.qLen) (VG.X86.Taint.Agree (workspaceTaint false)) := by
  let R := fun s t => (shapeValid L.p L.q → CallPair L s t) ∧
    Scr s L.base L.size ∧ Scr t L.base L.size ∧ KeyOutputReady L out s ∧ KeyOutputReady L out t ∧
      ContextReady L s ∧ ContextReady L t ∧ DomainReady L s ∧ DomainReady L t
  change RelCT isa _ (.seq (Shape.check L.pLen L.qLen) (.ite .e _ _)) _
  refine RelCT.seq (M := isa) (R := fun s t => R s t ∧ s.zf = some (!decide (shapeValid L.p L.q)) ∧
      t.zf = some (!decide (shapeValid L.p L.q))) ?_
    (fixedChoice_relCT (!decide (shapeValid L.p L.q)) ?_)
  · intro s t tr ur sf tf ⟨S, T, Os, Ot, Cs, Ct, Ds, Dt⟩ E F
    have Trace := (shapeCall_relCT L digestLen P Q stable hd _ _ _ _ _ _ ⟨S, T⟩ E F).1
    obtain ⟨Zs, Ms, Ks, Fs⟩ := wp_result (shapeCall_ok S P Q stable hd) E
    obtain ⟨Zt, Mt, Kt, Ft⟩ := wp_result (shapeCall_ok T P Q stable hd) F
    have keep {a b : State} (A : ShapeCallReady L digestLen a)
        (K : Keeps shapeClob a b) (O : Outs L.base shapeRanges a.mem b.mem)
        (C : ContextReady L a) (D : DomainReady L a) : ContextReady L b ∧ DomainReady L b := by
      have bound : 8248≤L.size := by have := L.extent; change 15712≤L.size at this; omega
      have V := (A.buffers _ G).value_keep_shape O K (by decide)
        (by change ShapePointer (.input .g); decide) bound
      unfold ContextReady DomainReady at *
      rw [V]
      refine ⟨?_,D⟩
      apply canonical_outs (supported_widths L.widths) C
        (Outs.of_outside (rs := [(0,8248)]) (shapeFrame_outside O) (by simp))
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      apply Or.inr
      change 8248≤context ((L.pLen+7)/8)
      unfold context; split <;> omega
    have Sc := keep S Ks Fs Cs Ds
    have Tc := keep T Kt Ft Ct Dt
    exact ⟨Trace, ⟨fun h => ⟨(Ms h).ready, (Mt h).ready⟩,
      S.scr.of_keeps Ks (by decide), T.scr.of_keeps Kt (by decide), Os.shape Fs Ks, Ot.shape Ft Kt,
      Sc.1,Tc.1,Sc.2,Tc.2⟩, Zs, Zt⟩
  · by_cases valid : shapeValid L.p L.q
    · simp only [valid, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]
      exact (deriveBody_relCT L out P Q G X Params ho A fits).mono
        (fun _ _ H => ⟨H.1 valid, H.2.2.2⟩) (fun _ _ h => h)
    · simp only [valid, decide_false, Bool.not_false, ite_true]
      exact (deriveFailure_relCT L.pLen L.qLen L.base L.size L.saved).mono
        (fun _ _ H => ⟨H.2.1, H.2.2.1, H.2.2.2.1.pointer.trans H.2.2.2.2.1.pointer.symm⟩) (fun _ _ h => h)

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DerivingOperationTiming.lean`, which only this module imported.
section

/-! Whole internal derivation timing retains the validated table through entry and dispatch. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem deriveContext_prefix {s : State} (A : DerivingABI s) {a b : Mem}
    (O : Outside (argumentPointer s 7) 0 8272 a b) (C : deriveContext s a) : deriveContext s b := by
  apply canonical_outs (supported_widths A.lengths) C (Outs.of_outside (rs := [(0,8272)]) O (by simp))
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  apply Or.inr
  change 8272≤context (((arg s 4).toNat+7)/8)
  unfold context; split <;> omega

theorem derivingInstalled_context {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat*8) Generate.deriveArguments 2 4 6 s t)
    (C : deriveContext s t.mem) (D : validParameters s) :
    ContextReady (derivingLayout s A) t ∧ DomainReady (derivingLayout s A) t := by
  have L : 0<(arg s 4).toNat ∧ 0<(arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params,Bytes⟩ := I.input (by decide : (2,.p)∈Generate.deriveArguments) A.keyBound
    (by rw [A.rd,A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr,Gptr,_⟩ := I.pointers (by decide)
  obtain ⟨_,_,_,Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  have G := (congrArg (fun k : Spec.Dsa.Params => k.g) Value).symm
  change operandValue t (argumentPointer s 7) (.input .g) (arg s 4).toNat=(derivingParams s).g at G
  unfold ContextReady DomainReady
  dsimp only [derivingLayout]
  rw [G]
  refine ⟨C,?_⟩
  have H := (generationChecks_spec (parametersValid_shape D)).mpr D
  exact H

theorem derivingOperation_agrees {s t : State} (A : DerivingABI s) (B : DerivingABI t)
    (args : ∀ i<9, arg s i=arg t i) (SP : s.gpr .esp=t.gpr .esp)
    (P : (derivingParams s).p=(derivingParams t).p)
    (Q : (derivingParams s).q=(derivingParams t).q)
    (Ds : validParameters s) (Dt : validParameters t)
    (Cs : deriveContext s s.mem) (Ct : deriveContext t t.mem)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa deriveKey s tr sf) (F : Exec isa deriveKey t ur tf) : tr=ur := by
  let L := derivingLayout s A
  have LayoutEq := derivingLayout_eq A B args SP P Q
  have DL := args 4 (by decide)
  refine derivingOperationWith_agrees A B args SP P Q deriveSized (deriveContext s) (deriveContext t)
    Cs Ct (deriveContext_prefix A) (deriveContext_prefix B) ?_ E F
  apply (deriveSized_relCT L (arg s 0) (arg s 4).toNat
    (by simp [L,derivingLayout,derivingInputs]) (by simp [L,derivingLayout,derivingInputs])
    (by simp [L,derivingLayout,derivingInputs]) (by simp [L,derivingLayout,derivingInputs])
    (by simp [L,derivingLayout,derivingInputs]) (derivingInputs_shape _ _) rfl
    (by change (arg s 0).toNat+(3*(arg s 4).toNat+2*(arg s 6).toNat)≤_
        rw [←A.outLength]; exact A.outBound)
    (by change Region.Disjoint _ ⟨argumentPointer s 0,3*(arg s 4).toNat+2*(arg s 6).toNat⟩
        rw [←A.outLength]; exact A.outScratch.symm)
    (Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength))).mono ?_
      (fun _ _ h => h)
  intro u v ⟨I,J,Ci,Cj⟩
  have SI := derivingInstalled_context A I Ci Ds
  have TJ := derivingInstalled_context B J Cj Dt
  refine ⟨derivingInstalled_ready A I,?_,derivingInstalled_output A I,?_,SI.1,?_,SI.2,?_⟩
  · simpa only [L,LayoutEq,DL] using derivingInstalled_ready B J
  · simpa only [L,LayoutEq,args 0 (by decide)] using derivingInstalled_output B J
  · simpa only [L,LayoutEq] using TJ.1
  · simpa only [L,LayoutEq] using TJ.2

end VG.Proof.Dsa.X86.Comb
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DeriveInvokeTiming.lean`, which only this module imported.
section

/-! The prevalidated internal body runs with public parameters and a secret scalar. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.Comb

theorem deriveInvoke_ct : DeriveInvokeCT deriveInvoke := by
  intro s t tr ur sf tf ⟨s₀,t₀,A,B,Pub,Key,R,S,C,D,_,OkS,OkT,Cs,Ct⟩ E F
  let u := (allocated 4 s).withRegions (callRd s₀) (callWr s₀)
  let v := (allocated 4 t).withRegions (callRd t₀) (callWr t₀)
  have Au : DerivingABI u := allocated_derivingABI A R C
  have Bv : DerivingABI v := allocated_derivingABI B S D
  have Vu := derive_allocated_valid A R C OkS
  have Vv := derive_allocated_valid B S D OkT
  have Cu := derive_allocated_context A R C Cs
  have Cv := derive_allocated_context B S D Ct
  obtain ⟨rs,ws⟩ := call_covers A R
  obtain ⟨rt,wt⟩ := call_covers B S
  obtain ⟨uf,Eu⟩ := inlineInvoke_trace rs ws ((derivingOperation_spec Au Vu Cu).mono (fun _ _ => trivial)) E
  obtain ⟨vf,Ev⟩ := inlineInvoke_trace rt wt ((derivingOperation_spec Bv Vv Cv).mono (fun _ _ => trivial)) F
  have SP := esp_of_rf R.rf (pub_rBase Pub ▸ S.rf)
  have args (i : Nat) (hi : i<9) : arg u i=arg v i := by
    rw [derive_allocated_args R C i hi,derive_allocated_args S D i hi]
    interval_cases i <;> simp only [callVal,SP] <;> exact pub_arg Pub _ (by decide)
  have KeyEq : (rInput s₀).key=(rInput t₀).key :=
    (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) Key
  have Params : derivingParams u=derivingParams v := by
    rw [derive_allocated_params A R C,derive_allocated_params B S D,
      pub_arg Pub 5 (by decide),pub_arg Pub 6 (by decide),KeyEq]
  exact ⟨derivingOperation_agrees Au Bv args (by change s.gpr .esp-4=t.gpr .esp-4; rw [SP])
    (congrArg Spec.Dsa.Params.p Params) (congrArg Spec.Dsa.Params.q Params) Vu Vv Cu Cv Eu Ev,trivial⟩

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Impl.Dsa.X86.Comb

theorem key_verified : Verified target generateKey (Spec.Dsa.generateKeyContract abi 232) :=
  KeyRandom.verifiedWith checkInvoke deriveInvoke keyInvariant_stable
    check_invoke_noSp derive_invoke_noSp checkInvoke_ct deriveInvoke_ct

end VG.Proof.Dsa.X86.Comb
