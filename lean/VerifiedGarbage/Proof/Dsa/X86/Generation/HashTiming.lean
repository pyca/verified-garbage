module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashReady
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Seed absorption inherits constant time from the selected SHA backend -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

private theorem setup_cert : ∃ hc, (VG.Taint.check taint (τr [])
    (.block [.mov .edx (.reg .esi), .mov .ecx (.reg .edi), .mov .eax (.imm 0)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem hash_absorb_ct {H : Hash} (ok : HashOK H) {st data digest scratch sp : BitVec 32} {len : Nat} :
    RelCT isa (fun s t => HashReady ok st data digest scratch sp len s ∧ HashReady ok st data digest scratch sp len t)
      (Impl.Dsa.X86.Generation.hashAbsorb H) (fun _ _ => True) := by
  have initCT := (init_rel ok (r := .ebx) (sp := sp)
    (P := fun s t => HashReady ok st data digest scratch sp len s ∧ HashReady ok st data digest scratch sp len t)
    (fun _ _ ⟨a, b⟩ => ⟨a.geometry.init_args a.registers, b.geometry.init_args b.registers, a.stack, b.stack⟩)).wp
    (F₁ := HashReady ok st data digest scratch sp len) (F₂ := HashReady ok st data digest scratch sp len)
    (fun _ _ ⟨a, b⟩ => ⟨hash_init_ready a, hash_init_ready b⟩)
  obtain ⟨hc, checked⟩ := setup_cert
  have setupCT := (RelCT.taint (A := taint) (τr [])
    (P := fun s t => True ∧ HashReady ok st data digest scratch sp len s ∧ HashReady ok st data digest scratch sp len t)
    (fun _ _ _ => agree_regs (by simp)) checked).wp
    (F₁ := UpdateReady ok st data digest scratch sp len) (F₂ := UpdateReady ok st data digest scratch sp len)
    (fun _ _ ⟨_, a, b⟩ => ⟨hash_update_ready a, hash_update_ready b⟩)
  have updateCT := upd_rel ok (lo := .eax) (r := .ebx) (sp := sp)
    (P := fun s t => True ∧ UpdateReady ok st data digest scratch sp len s ∧ UpdateReady ok st data digest scratch sp len t)
    (fun _ _ ⟨_, a, b⟩ => ⟨a.geometry.update_args a.registers a.eax a.ecx a.edx,
      b.geometry.update_args b.registers b.eax b.ecx b.edx, a.stack, b.stack⟩)
  exact initCT.seq (setupCT.seq updateCT)

end VG.Proof.Dsa.X86.Generation
