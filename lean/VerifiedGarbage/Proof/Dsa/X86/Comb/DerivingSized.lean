module

public import VerifiedGarbage.Proof.Dsa.X86.Comb.Checking
import VerifiedGarbage.Proof.Dsa.X86.DeriveSized
import VerifiedGarbage.Proof.Dsa.X86.Comb.DeriveCompute
import VerifiedGarbage.Proof.Dsa.X86.Comb.StagePower
import VerifiedGarbage.Proof.Dsa.X86.Comb.CanonicalFrame
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Spec.Dsa.Derive

/-! The internal derivation consumes the retained table under validated parameters. -/

@[expose] public section
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
