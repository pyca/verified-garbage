module

public import VerifiedGarbage.Proof.MillerRabin.X86.CopyTiming
public import VerifiedGarbage.Proof.MillerRabin.X86.TableLoop

/-! # Table initialization uses public copies and a public fixed count -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem table_init_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t) tabInit (fun _ _ => True) := by
  have one := copy_stage_ct C (by decide) (by decide) (by decide)
    (.inr (.inr (.inr ⟨by decide, by decide⟩))) copy_one_cert
  have first := copy_stage_ct C (by decide) (by decide) (by decide)
    (.inr (.inr (.inr ⟨by decide, by decide⟩))) copy_witness_cert
  have acc := copy_stage_ct C (by decide) (by decide) (by decide)
    (.inr (.inl rfl)) copy_accumulator_cert
  unfold tabInit tabCopies seqs
  simp only [List.foldr_cons, List.foldr_nil]
  exact (one.seq (first.seq acc)).seq ((C.pieces table_count_cert).seq (RelCT.nil (fun _ _ _ => trivial)))

theorem TimingContext.stack_word {σ₁ σ₂ : State} {base : Addr} {bytes w d : Nat} {sp len : BitVec 32}
    {c : Prog isa} (C : TimingContext σ₁ σ₂ base bytes w sp len)
    (bound : d + 4 ≤ 1132)
    (cert : ∃ hc, (VG.Taint.check VG.X86.taint (wordTaint [] 0 d) c hc).isSome = true) :
    RelCT isa (fun s t => Stage base bytes w σ₁ s ∧ Stage base bytes w σ₂ t ∧
      s.mem.readW (off (byteAddr sp) d) 32 = t.mem.readW (off (byteAddr sp) d) 32) c (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := cert
  refine RelCT.taint (A := taint) (wordTaint [] 0 d) (fun s t ⟨h₁, h₂, wordEq⟩ => ?_) checked
  have i₁ := C.initial₁.of_stage C.facts₁ h₁
  have i₂ := C.initial₂.of_stage C.facts₂ h₂
  apply i₁.agree_word i₂ bound ?_ (fun _ h => (List.not_mem_nil h).elim)
  dsimp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region]
  rw [i₁.wr, i₂.wr]
  exact wordEq

end VG.Proof.MillerRabin.X86
