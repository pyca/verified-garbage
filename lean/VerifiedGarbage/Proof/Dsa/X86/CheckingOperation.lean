module

public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.CheckingABI
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Dsa.X86.Installed
import VerifiedGarbage.Proof.Dsa.X86.Result
import VerifiedGarbage.Proof.Dsa.X86.VerifyingOperation
import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.CheckingResources
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Dsa.X86.CheckingEntry
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! ### `Dsa.X86.CheckingSized`, which this module and modules that import it used -/

section

/-! # The domain checker rejects bad shapes and returns the algebraic mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem checkingSizedWith_spec {base : Addr} {size pLen qLen p q g : Nat}
    {s : State} {params : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (paramsLen : params.length = 2 * pLen + qLen)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩)
    (compute : Nat → Nat → Prog isa) (I : Mem → Prop) (written : Nat) (hwritten : usedBytes≤written)
    (compute_ok : ∀ {t : State}, Moduli base size pLen qLen p q t →
      CallerBuffer t base size (.input .g) pLen → operandValue t base (.input .g) pLen=g →
      WP isa (compute pLen qLen) t fun u =>
        Moduli base size pLen qLen p q u ∧
        flagW base (Layout.field .mask) u=flagW base (Layout.field .mask) t &&&
          mask32 ((1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1) ∧
        ScheduleFrame base written t u ∧ I u.mem) :
    WP isa (Generate.checkSizedWith compute pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes pLen qLen params then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base written s.mem sf.mem ∧
      (Spec.Dsa.checkParametersBytes pLen qLen params=true → I sf.mem) ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega_using [H]
  have value : Spec.Dsa.checkParametersBytes pLen qLen params =
      decide (Spec.Dsa.parametersValid ⟨p, q, g⟩) := by
    simp only [Spec.Dsa.checkParametersBytes, widths, paramsLen, paramsValue, decide_true,
      beq_self_eq_true, Bool.true_and]
  unfold Generate.checkSizedWith
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, _⟩ := M valid
    refine WP.seq (WP.mono (compute_ok Mt
      (G.keep_shape O K (by decide) (by decide))
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg))
      fun u ⟨Mu, Fu, E, Invariant⟩ => ?_)
    have mask : flagW base (Layout.field .mask) u = mask32 (Spec.Dsa.parametersValid ⟨p, q, g⟩) := by
      rw [Fu, F]
      simp only [mask32, valid, ite_true, BitVec.allOnes_and, generationChecks_spec valid]
    refine WP.mono (result_ok Mu.scr Mu.saved (Spec.Dsa.parametersValid ⟨p, q, g⟩) mask)
      fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, ((K.mono (by decide)).trans E.keeps).trans (Kf.mono (by decide)), ?_, by rw [Of]; exact fun _ => Invariant, ?_⟩
    · rw [V, value]
      by_cases h : Spec.Dsa.parametersValid ⟨p, q, g⟩ <;> simp only [h, decide_true, decide_false, ite_true, ite_false] <;> rfl
    · rw [Of]
      intro a ha hstack
      exact (E.outside a ha (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by have : 15712≤written := hwritten; omega_using [ha, this])))
    · intro regs saved
      rw [Of]
      exact E.saved regs (shapeFrame_saved O saved)
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    have invalid : ¬ Spec.Dsa.parametersValid ⟨p, q, g⟩ :=
      fun h => valid (parametersValid_shape h)
    refine WP.mono (verifyFailure_ok t) fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_, ?_⟩
    · rw [V, value]
      simp only [invalid, decide_false]
      rfl
    · rw [Of]
      intro a ha _
      exact (shapeFrame_outside O) a (.inr (by have : 15712≤written := hwritten; omega_using [ha, this]))
    · rw [value]
      simp only [invalid,decide_false,Bool.false_eq_true, false_implies]
    · intro regs saved
      rw [Of]
      exact shapeFrame_saved O saved

theorem checkingSized_spec {base : Addr} {size pLen qLen p q g : Nat}
    {s : State} {params : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (paramsLen : params.length = 2 * pLen + qLen)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩) :
    WP isa (Generate.checkSized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes pLen qLen params then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base usedBytes s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  refine WP.mono (checkingSizedWith_spec scr extent widths P Q G hp hq hg paramsLen paramsValue
    Generate.parameters (fun _ => True) usedBytes (Nat.le_refl _) ?_) ?_
  · intro t M G hg
    exact WP.mono (generateParameters_ok M G hg) fun u ⟨M,F,E⟩ =>
      ⟨M,F,E.schedule (Nat.le_refl _),trivial⟩
  · intro t ⟨V,K,O,_,S⟩
    exact ⟨V,K,O,S⟩

end VG.Proof.Dsa.X86

end

end

/-! # Complete functional and cdecl verification of the x86 domain checker -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CheckingInstalled.lean`, which only this module imported.
section

/-! # Installed domain arguments agree with the caller's packed bytes -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingInstalled_spec {s t : State} (A : CheckingABI s)
    (I : Installed (argumentPointer s 4) ((arg s 5).toNat * 8) Generate.checkArguments 0 2 3 s t) :
    WP isa (Generate.checkSized (arg s 2).toNat (arg s 3).toNat) t fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 4) usedBytes t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 4)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 4)) regs Entry.savedRegisters := by
  have L : 0 < (arg s 2).toNat ∧ 0 < (arg s 3).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (0, .p) ∈ Generate.checkArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  exact checkingSized_spec I.scr A.used A.lengths P Q G rfl rfl rfl
    (by simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using A.keyLength) Value

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem checkingOperationWith_spec (sized : Nat → Nat → Prog isa) (Invariant : State → Mem → Prop)
    (installed : ∀ {s t : State} (_ : CheckingABI s),
      Installed (argumentPointer s 4) ((arg s 5).toNat*8) Generate.checkArguments 0 2 3 s t →
      WP isa (sized (arg s 2).toNat (arg s 3).toNat) t fun sf =>
        (sf.gpr .eax).toNat=(if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
        Keeps powerClob t sf ∧ StackOutside (t.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat*8) t.mem sf.mem ∧
        (Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
          (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)=true → Invariant s sf.mem) ∧
        ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 4)) regs Entry.savedRegisters →
          VG.X86.Spill.Saved sf.mem (off (argumentPointer s 4)) regs Entry.savedRegisters)
    {s : State} (A : CheckingABI s) :
    WP isa (Generate.checkParametersWith sized) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr ∧
      (Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat)=true → Invariant s sf.mem) := by
  have sz : 8272 ≤ (arg s 5).toNat * 8 := by have H : 15712 ≤ (arg s 5).toNat * 8 := A.used; omega_using [H]
  unfold Generate.checkParametersWith Core.sequence
  dsimp only [List.foldr]
  refine WP.seq (WP.mono (checkingEntry_ok A) fun t I => ?_)
  refine WP.seq (generationDispatch_ok sized _ I.scr (by change 8256 ≤ _; omega_using [sz])
    (supportedWidths_member A.lengths) (by decide)
    (congrArg BitVec.toNat (I.arguments (2, .pLen) (by decide)))
    (congrArg BitVec.toNat (I.arguments (3, .qLen) (by decide))) ?_)
  intro u Ku Ou
  have J := I.compare Ku Ou
  refine WP.mono (installed A J) fun v ⟨Value, K, O, Inv, Saved⟩ => ?_
  have Ov : StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem v.mem :=
    fun a ha hstack => (O a ha
      (by rw [J.keeps.1 .esp (by decide)]; exact hstack)).trans (J.outside a (.inr (by simpa only [Nat.zero_add] using ha)))
  have Esp : v.gpr .esp = s.gpr .esp := (K.1 _ (by decide)).trans (J.keeps.1 _ (by decide))
  refine WP.seq (WP.mono (entryRestore_ok (J.scr.of_keeps K (by decide)) sz (Saved s.gpr J.saved))
    fun sf R => WP.block_nil ?_)
  refine ⟨?_, restored_abi R Esp (outside_return Ov A.retScratch A.stackLow), ?_, ?_, ?_, by rw [R.mem]; exact Inv⟩
  · rw [R.other .eax (by decide)]; exact Value
  · rw [R.mem]; exact Ov
  · rw [R.rd, K.2.1, J.keeps.2.1]
  · rw [R.wr, K.2.2, J.keeps.2.2]

theorem checkingOperation_spec {s : State} (A : CheckingABI s) :
    WP isa (Generate.checkParameters) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes (arg s 2).toNat (arg s 3).toNat
        (Spec.Rsa.bytesAt s.mem (argumentPointer s 0) (arg s 1).toNat) then 1 else 0) ∧
      abiPreserved s sf ∧
      StackOutside (s.gpr .esp) (argumentPointer s 4) ((arg s 5).toNat * 8) s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr := by
  refine WP.mono (checkingOperationWith_spec Generate.checkSized (fun _ _ => True) ?_ A) ?_
  · intro s t A I
    exact WP.mono (checkingInstalled_spec A I) fun sf ⟨V,K,O,S⟩ =>
      ⟨V,K,(fun a ha hs => O a (by have := A.used; omega_using [ha, this]) hs), (fun _ => trivial), S⟩
  · intro t ⟨V,K,O,R,W,_⟩
    exact ⟨V,K,O,R,W⟩

end VG.Proof.Dsa.X86
