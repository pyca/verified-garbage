module
public import VerifiedGarbage.Proof.Rsa.X86.KcFrames
public import VerifiedGarbage.Proof.Rsa.X86.KcValidTiming

import VerifiedGarbage.Proof.Rsa.X86.KcExponentTiming
import VerifiedGarbage.Proof.Rsa.X86.KcPublic
import VerifiedGarbage.Proof.Bignum.X86.PublicExponentArgs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Public exponent rejection and width dispatch have matching traces -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Impl.Rsa.X86.KeyCheck

def ExponentPair (g : CallGeometry) (s t : State) : Prop :=
  Pair g s t ∧ ∃ b : Bool, s.gpr .eax = BitVec.ofNat 32 b.toNat ∧ t.gpr .eax = BitVec.ofNat 32 b.toNat

theorem scan_relCT (g : CallGeometry) :
    RelCT isa (fun s t => Pair g s t ∧ inputBytes g s.mem 1 = inputBytes g t.mem 1)
      (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 2)) VG.Impl.Bignum.X86.exponentCheck)
      (ExponentPair g) := by
  intro s t tr ur sf tf ⟨h, same⟩ es et
  have trace := exponent_trace h same es et
  obtain ⟨vs, ms, ks⟩ := wp_result (exponent_ok h.left) es
  obtain ⟨vt, mt, kt⟩ := wp_result (exponent_ok h.right) et
  refine ⟨trace, h.keepMem ks kt (by decide) (by decide) ms mt, _, vs, ?_⟩
  change tf.gpr .eax = BitVec.ofNat 32 (Spec.Rsa.exponentValid (Spec.Rsa.os2ip (inputBytes g s.mem 1))).toNat
  rw [same]; exact vt

theorem flag_relCT (g : CallGeometry) :
    RelCT isa (ExponentPair g) (.block [.alu .cmp .eax (.imm 0)])
      (fun s t => Pair g s t ∧ s.zf = t.zf) := by
  have trace : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 0)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl
  intro s t tr ur sf tf ⟨h, b, vs, vt⟩ es et
  obtain ⟨zs, ms, ks⟩ := wp_result (exponentFlag_ok b vs) es
  obtain ⟨zt, mt, kt⟩ := wp_result (exponentFlag_ok b vt) et
  exact ⟨(trace _ _ _ _ _ _ trivial es et).1,
    h.keepMem ks kt (by simp) (by simp) ms mt, zs.trans zt.symm⟩

theorem failure_relCT : RelCT isa (fun _ _ => True) failure (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
  rfl

theorem checkExponent_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (fun s t => Pair g s t ∧ inputBytes g s.mem 1 = inputBytes g t.mem 1)
      (checkExponent g.full) (fun _ _ => True) := by
  apply VG.RelCT.seq (scan_relCT g)
  apply VG.RelCT.seq (flag_relCT g)
  apply VG.RelCT.ite (M := isa) (c := .e)
  · exact fun _ _ h => h.2
  · exact failure_relCT.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact (valid_relCT g len).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
end VG.Proof.Rsa.X86.KeyCheck
