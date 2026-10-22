module

public import VerifiedGarbage.Proof.MillerRabin.X86.BackupTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingContext
public import VerifiedGarbage.Proof.MillerRabin.X86.RestoreProtected

/-! # Restoration and the cdecl epilogue use public pointers -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem restore_pointer_ready {σ s : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (initial : PieceInput base bytes w sp len σ) (facts : RoundFacts σ base bytes w)
    (h : Stage base bytes w σ s) :
    WP isa restoreProtected s fun t => t.gpr .esp = sp ∧ t.gpr .edi = base.setWidth 32 := by
  refine WP.mono (restoreProtected_ok h.context facts.lower facts.upper facts.fit
    (h.width facts.fit facts.width)) ?_
  rintro t ⟨_, _, _, K⟩
  refine ⟨((K.1 _ (by decide)).trans h.stack).trans initial.stack, ?_⟩
  rw [K.1 .edi (by decide)]
  apply BitVec.eq_of_toNat_eq
  have eq := h.context.ws.edi_toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := h.context.ws.nowrap; omega)]
  exact eq

theorem finish_ct : RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ s.gpr .edi = t.gpr .edi)
    (.block finish) (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := finish_cert
  apply RelCT.taint (A := taint) (τr [.esp, .edi]) _ checked
  rintro s t ⟨sp, edi⟩
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sp
  · exact edi

theorem restore_finish_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t)
      (.seq restoreProtected (.seq (.block finish) (.block []))) (fun _ _ => True) := by
  have restoreCT := ((PieceInput.restore_protected_ct (sp := sp) (len := len) C.facts₁.fit).mono
    (P' := fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨C.initial₁.of_stage C.facts₁ h₁, C.initial₂.of_stage C.facts₂ h₂⟩)
    (fun _ _ _ => trivial)).wp
    (F₁ := fun (t : State) => t.gpr .esp = sp ∧ t.gpr .edi = base.setWidth 32)
    (F₂ := fun (t : State) => t.gpr .esp = sp ∧ t.gpr .edi = base.setWidth 32)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨restore_pointer_ready C.initial₁ C.facts₁ h₁,
      restore_pointer_ready C.initial₂ C.facts₂ h₂⟩)
  exact restoreCT.seq ((finish_ct.mono
    (fun _ _ ⟨_, ⟨sp₁, edi₁⟩, ⟨sp₂, edi₂⟩⟩ => ⟨sp₁.trans sp₂.symm, edi₁.trans edi₂.symm⟩)
    (fun _ _ _ => trivial)).seq (RelCT.nil (fun _ _ _ => trivial)))

end VG.Proof.MillerRabin.X86
