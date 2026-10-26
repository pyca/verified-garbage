module

import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.DeriveFailure
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
public import VerifiedGarbage.Proof.Dsa.X86.Execution
import VerifiedGarbage.Proof.Dsa.X86.DeriveCompute
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.X86.DeriveBytes
import VerifiedGarbage.Proof.Dsa.X86.DeriveSpec
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.ShapeOperands
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set

/-! # Shape checking followed by derivation or full output clearing -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem deriveSizedWith_spec {base : Addr} {size pLen qLen p q g x : Nat}
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
    (compute : Nat → Nat → Prog isa) (I : Mem → Prop) (initial : I s.mem)
    (stable : ∀ {m m'}, Outs base shapeRanges m m' → I m → I m')
    (compute_ok : ∀ {t : State}, Moduli base size pLen qLen p q t →
      CallerBuffer t base size (.input .g) pLen → CallerBuffer t base size (.input .nonce) qLen →
      operandValue t base (.input .g) pLen=g → operandValue t base (.input .nonce) qLen=x → I t.mem →
      WP isa (compute pLen qLen) t fun u =>
        Moduli base size pLen qLen p q u ∧
        flagW base (Layout.field .mask) u=flagW base (Layout.field .mask) t &&&
          mask32 (((1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1) ∧
            (0<x ∧ x<q) ∧ (1<g^x%p ∧ g^x%p<p)) ∧
        operandValue u base (.local t2) pLen=g^x%p ∧ Execution base t u) :
    let result := Spec.Dsa.deriveKeyBytes pLen qLen params scalar
    WP isa (Generate.deriveSizedWith compute pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        result.getD (List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  dsimp only
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega
  have sz : 8272 ≤ size := by have H : 15712 ≤ size := extent; omega
  have L : 128 ≤ pLen ∧ pLen ≤ 384 ∧ 20 ≤ qLen ∧ qLen ≤ 32 := by unfold Spec.Dsa.lengthsValid at widths; omega
  have spec := deriveSpec widths
    (show params.length = 2 * pLen + qLen by rw [← paramBytes]; simp [Spec.Rsa.bytesAt])
    (show scalar.length = qLen by rw [← scalarBytes]; simp [Spec.Rsa.bytesAt]) paramsValue
    (show Spec.Dsa.decodeBE scalar = x by rw [← scalarBytes]; exact hx)
  unfold Generate.deriveSizedWith
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, _⟩ := M valid
    have Ct := compute_ok Mt (G.keep_shape O K (by decide) (by decide))
      (X.keep_shape O K (by decide) (by decide))
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg)
      ((X.value_keep_shape O K (by decide) (by decide) bound).trans hx) (stable O initial)
    refine WP.mono (deriveBytesWith_ok Mt
      (Params.keep_shape O K (by decide) (by decide))
      (X.keep_shape O K (by decide) (by decide))
      (by rw [F]; simp only [mask32, valid, ite_true])
      ((shapeFrame_field O (by decide)).trans ho) hf
      (by rw [K.2.2]; exact hw) ha
      (by rw [shapeFrame_field O (by decide : Field.p ≠ .mask ∧ Field.p ≠ .digestPrefixLen)]; exact pa)
      (by rw [shapeFrame_field O (by decide : Field.nonce ≠ .mask ∧ Field.nonce ≠ .digestPrefixLen)]; exact xa) _ Ct)
      fun sf ⟨V, B, Kf, Of, Saved⟩ => ?_
    rw [Params.bytes_keep_shape O K (by decide) (by decide) bound,
      X.bytes_keep_shape O K (by decide) (by decide) bound, paramBytes, scalarBytes] at B
    rw [spec]
    simp only [valid, true_and]
    refine ⟨?_, ?_, (K.mono (by decide)).trans Kf, ?_, fun regs saved => Saved regs (shapeFrame_saved O saved)⟩
    · rw [V]; split_ifs <;> rfl
    · split_ifs at B ⊢ <;> exact B
    · intro a hb hout hstack
      exact (Of a hb hout (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at hb; omega)))
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (deriveFailure_ok (scr.of_keeps K (by decide)) (by change 8256 ≤ size; omega)
      (by omega) (by omega) ((shapeFrame_field O (by decide)).trans ho) hf
      (by rw [K.2.2]; exact hw)) fun sf ⟨B, V, Of, Kf⟩ => ?_
    have Fout : OutputFrame base (out.setWidth 64) 0 (3 * pLen + 2 * qLen) t.mem sf.mem :=
      fun a _ h => Of a (.inr (by omega))
    rw [spec]
    simp only [valid, false_and, ite_false, Option.getD_none]
    refine ⟨by rw [V]; rfl, B, (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_⟩
    · intro a hb hout _
      exact (Fout a (by omega) hout).trans
        ((shapeFrame_outside O) a (.inr (by change 15712 ≤ ofs base a at hb; omega)))
    · intro regs saved
      exact Fout.saved ha (by decide) sz (by have := scr.nowrap; omega) (shapeFrame_saved O saved)

theorem deriveSized_spec {base : Addr} {size pLen qLen p q g x : Nat}
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
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩) :
    let result := Spec.Dsa.deriveKeyBytes pLen qLen params scalar
    WP isa (Generate.deriveSized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = Spec.Dsa.signStatus result ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) (3 * pLen + 2 * qLen) =
        result.getD (List.replicate (3 * pLen + 2 * qLen) 0) ∧
      Keeps powerClob s sf ∧ StackOutputFrame (s.gpr .esp) base (out.setWidth 64) usedBytes
        (3 * pLen + 2 * qLen) s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters :=
  deriveSizedWith_spec scr extent widths Params P Q G X hp hq hg hx paramBytes scalarBytes
    ho hf hw ha pa xa paramsValue Generate.deriveCompute (fun _ => True) trivial
    (fun _ _ => trivial) (fun M G X hg hx _ => deriveCompute_ok M G X hg hx)

end VG.Proof.Dsa.X86
