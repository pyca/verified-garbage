module

public import VerifiedGarbage.Proof.Rsa.X86.KcBranchTiming

/-! # Key-validation timing reveals only the public modulus and exponent -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Impl.Rsa.X86.KeyCheck

theorem modulus_relCT (g : CallGeometry) :
    RelCT isa (Pair g) (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 0))
      (.block VG.Impl.Bignum.X86.modulusCheck)) (fun _ _ => True) := by
  have check : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block VG.Impl.Bignum.X86.modulusCheck)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (loadArguments_relCT 0 1 (g.args 0) (g.args 1)) check).mono
  · intro s t h
    exact ⟨h.agree,
      (h.left.arguments 0 (by cases g.full <;> decide)).readSrc,
      (h.right.arguments 0 (by cases g.full <;> decide)).readSrc,
      (h.left.arguments 1 (by cases g.full <;> decide)).readSrc,
      (h.right.arguments 1 (by cases g.full <;> decide)).readSrc⟩
  · exact fun _ _ h => h

theorem body_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (fun s t => Pair g s t ∧ inputBytes g s.mem 0 = inputBytes g t.mem 0 ∧
      inputBytes g s.mem 1 = inputBytes g t.mem 1) (body g.full) (fun _ _ => True) := by
  let r := fun s t => Pair g s t ∧ inputBytes g s.mem 1 = inputBytes g t.mem 1 ∧ s.zf = t.zf
  have branch : RelCT isa r (.ite .e (checkExponent g.full) failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := r)
    · exact fun _ _ h => h.2.2
    · exact (checkExponent_relCT g len).mono (fun _ _ h => ⟨h.1.1, h.1.2.1⟩) (fun _ _ h => h)
    · exact failure_relCT.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  intro s t tr ur sf tf ⟨h, modulus, exponent⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (modulus_relCT g _ _ _ _ _ _ h e1 f1).1
      obtain ⟨zs, ms, ks⟩ := wp_result (modulus_ok h.left len.lower len.upper) e1
      obtain ⟨zt, mt, kt⟩ := wp_result (modulus_ok h.right len.lower len.upper) f1
      have next := h.keepMem ks kt (by decide) (by decide) ms mt
      have flags : u.zf = v.zf := by
        rw [zs, zt]
        change some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) _) = _
        rw [modulus]; rfl
      have eq2 := (branch _ _ _ _ _ _ ⟨next, by rw [ms, mt]; exact exponent, flags⟩ e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩
end VG.Proof.Rsa.X86.KeyCheck
