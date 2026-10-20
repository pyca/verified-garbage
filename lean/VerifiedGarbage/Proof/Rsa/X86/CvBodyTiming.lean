module
public import VerifiedGarbage.Proof.Rsa.X86.CvBody
public import VerifiedGarbage.Proof.Rsa.X86.CvPair

import VerifiedGarbage.Proof.Rsa.X86.CvModulusTiming
import VerifiedGarbage.Proof.Rsa.X86.CvFailureTiming
import VerifiedGarbage.Proof.Rsa.X86.CvValidTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # CRT branches reveal only the declared public modulus -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.CrtValues

theorem body_relCT (g : CallGeometry) (len : Lengths g) :
    RelCT isa (fun s t => Pair g s t ∧ inputBytes g s.mem 0 = inputBytes g t.mem 0)
      body (fun _ _ => True) := by
  let r := fun s t => Pair g s t ∧ s.zf = t.zf
  have branch : RelCT isa r (.ite .e valid VG.Impl.Rsa.X86.CrtValues.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := r)
    · exact fun _ _ h => h.2
    · exact (valid_relCT g len).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
    · exact (failure_relCT g).mono (fun _ _ h => h.1.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨h, modulus⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := (modulus_relCT g _ _ _ _ _ _ h e1 f1).1
      obtain ⟨zs, ms, ks⟩ := wp_result (modulus_ok h.left len) e1
      obtain ⟨zt, mt, kt⟩ := wp_result (modulus_ok h.right len) f1
      have next := h.keepMem ks kt (by decide) (by decide) ms mt
      have flags : u.zf = v.zf := by rw [zs, zt, modulus]
      have eq2 := (branch _ _ _ _ _ _ ⟨next, flags⟩ e2 f2).1
      exact ⟨by rw [eq1, eq2], trivial⟩

end VG.Proof.Rsa.X86.CrtValues
