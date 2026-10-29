module

public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.DerivingABI
public import VerifiedGarbage.Proof.Dsa.X86.Installed

import VerifiedGarbage.Proof.Dsa.X86.InstalledInputs
import VerifiedGarbage.Proof.Dsa.X86.ParameterBuffers
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.DerivingOperation
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Dsa.X86.DerivingResources
import VerifiedGarbage.Proof.Dsa.X86.DeriveSized
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Impl.Dsa.X86.Entry
import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Spec.Dsa.Derive
/-! # Derivation reads the caller's parameters and explicit scalar -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Comb/DerivingSized.lean`, which only this module imported.
section

/-! The internal derivation consumes the retained table under validated parameters. -/

section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

theorem derivingSized_spec {base : Addr} {size pLen qLen p q g x : Nat}
    {s : State} {out : BitVec 32} {params scalar : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (Params : CallerBuffer s base size (.input .p) (2 * pLen + qLen))
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (X : CallerBuffer s base size (.input .nonce) qLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (hx : operandValue s base (.input .nonce) qLen = x)
    (paramBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .p)).setWidth 64) (2 * pLen + qLen) = params)
    (scalarBytes : Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .nonce)).setWidth 64) qLen = scalar)
    (ho : pointerValue base s (.input .out) = out)
    (hf : out.toNat + (3 * pLen + 2 * qLen) ≤ 2 ^ 32)
    (hw : ∀ i < 3 * pLen + 2 * qLen, InRegions s.wr (off (out.setWidth 64) i) 1)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (pa : Region.Disjoint ⟨(pointerValue base s (.input .p)).setWidth 64, 2 * pLen + qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (xa : Region.Disjoint ⟨(pointerValue base s (.input .nonce)).setWidth 64, qLen⟩
      ⟨out.setWidth 64, 3 * pLen + 2 * qLen⟩)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩)
    (valid : Spec.Dsa.parametersValid (Spec.Dsa.paramsBytes pLen qLen params))
    (sizeComb : (layout ((pLen+7)/8) ((qLen+3)/4)).size≤size)
    (C : parameterContext base pLen qLen params s.mem) :
    let result := Spec.Dsa.deriveKeyBytes pLen qLen params scalar
    WP isa (deriveSized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        result.getD (List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have sup := supported_widths widths
  unfold parameterContext at C
  rw [paramsValue] at C valid
  have domain := (generationChecks_spec (parametersValid_shape valid)).mpr valid
  exact deriveSizedWith_spec scr extent widths Params P Q G X hp hq hg hx paramBytes scalarBytes
    ho hf hw ha pa xa paramsValue deriveCompute (canonical ((pLen+7)/8) ((qLen+3)/4) p g base) C
    (fun O C => canonical_outs sup C (Outs.of_outside (rs := [(0,8248)]) (shapeFrame_outside O) (by simp)) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      apply Or.inr
      change 8248≤context ((pLen+7)/8)
      unfold context; split <;> omega))
    (fun M G X hg hx C => deriveCompute_ok M G X hg hx domain sizeComb C)

end VG.Proof.Dsa.X86.Comb
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Comb

def deriveContext (s : State) : Mem → Prop :=
  parameterContext (argumentPointer s 7) (arg s 4).toNat (arg s 6).toNat
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)

def validParameters (s : State) : Prop :=
  Spec.Dsa.parametersValid (Spec.Dsa.paramsBytes (arg s 4).toNat (arg s 6).toNat
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat))

theorem derivingInstalled_spec {s t : State} (A : DerivingABI s)
    (I : Installed (argumentPointer s 7) ((arg s 8).toNat * 8) Generate.deriveArguments 2 4 6 s t)
    (O : Outside (argumentPointer s 7) 0 8272 s.mem t.mem)
    (valid : validParameters s) (C : deriveContext s s.mem) :
    let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
    WP isa (deriveSized (arg s 4).toNat (arg s 6).toNat) t fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      Keeps powerClob t sf ∧ StackOutputFrame (t.gpr .esp) (argumentPointer s 7)
        (argumentPointer s 0) usedBytes (arg s 1).toNat t.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved t.mem (off (argumentPointer s 7)) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off (argumentPointer s 7)) regs Entry.savedRegisters := by
  dsimp only
  have L : 0 < (arg s 4).toNat ∧ 0 < (arg s 6).toNat := by
    have H := A.lengths; unfold Spec.Dsa.lengthsValid at H; omega
  obtain ⟨Params, Bytes⟩ := I.input (by decide : (2, .p) ∈ Generate.deriveArguments) A.keyBound
    (by rw [A.rd, A.wr]; simp) A.keyScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowKey.symm)
  obtain ⟨X, XBytes⟩ := I.input (by decide : (5, .nonce) ∈ Generate.deriveArguments) A.scalarBound
    (by rw [A.rd, A.wr]; simp) A.scalarScratch A.room
    (by rw [callStack_eq A.stackLow]; exact A.belowScalar.symm)
  obtain ⟨Qptr, Gptr, _⟩ := I.pointers (by decide)
  obtain ⟨P, Q, G, Value⟩ := parameters_buffers Params L.1 L.2
    (by have := A.keyLength; omega) Bytes Qptr Gptr
  rw [A.outLength]
  have Ct : deriveContext s t.mem := by
    unfold deriveContext parameterContext at C ⊢
    apply canonical_outs (supported_widths A.lengths) C (Outs.of_outside (rs := [(0,8272)]) O (by simp))
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    apply Or.inr
    change 8272≤context (((arg s 4).toNat+7)/8)
    unfold context; split <;> omega
  have fits := Nat.le_trans (context_fits A.lengths) (Nat.mul_le_mul_right 8 A.scratchLength)
  apply derivingSized_spec (out := arg s 0) I.scr A.used A.lengths
    (by rw [← A.keyLength]; exact Params) P Q G X rfl rfl rfl rfl
    (by rw [← A.keyLength]; exact Bytes) XBytes (I.arguments (0, .out) (by decide))
    (by rw [← A.outLength]; exact A.outBound) ?_ (by rw [← A.outLength]; exact A.outScratch.symm)
    (by rw [I.arguments (2, .p) (by decide), ← A.keyLength, ← A.outLength]; exact A.keyOut)
    (by rw [I.arguments (5, .nonce) (by decide), ← A.outLength]; exact A.scalarOut) Value valid fits Ct
  intro i hi
  rw [I.keeps.2.2, A.wr]
  refine ⟨_, List.mem_cons_self, Offset.contains_base _ (by have := A.outLength; omega) ?_⟩
  have := A.outBound
  have := A.outLength
  omega

theorem derivingOperation_spec {s : State} (A : DerivingABI s)
    (valid : validParameters s) (C : deriveContext s s.mem) :
    let result := Spec.Dsa.deriveKeyBytes (arg s 4).toNat (arg s 6).toNat
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (argumentPointer s 5) (arg s 6).toNat)
    WP isa deriveKey s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (argumentPointer s 0) (arg s 1).toNat =
        result.getD (List.replicate (arg s 1).toNat 0) ∧
      abiPreserved s sf ∧
      StackOutputFrame (s.gpr .esp) (argumentPointer s 7) (argumentPointer s 0) ((arg s 8).toNat * 8) (arg s 1).toNat s.mem sf.mem ∧
      sf.rd = s.rd ∧ sf.wr = s.wr :=
  derivingOperationWith_spec deriveSized A (fun I O => derivingInstalled_spec A I O valid C)

end VG.Proof.Dsa.X86.Comb
