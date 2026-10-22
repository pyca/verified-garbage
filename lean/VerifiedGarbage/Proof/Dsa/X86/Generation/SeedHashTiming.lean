module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.SeedHash
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashFinishTiming
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Seed-hash timing follows only public pointers and the public seed length -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

theorem HashReady.absorb {H : Hash} {ok : HashOK H} {st data digest scratch sp : BitVec 32} {len : Nat} {s : State}
    (h : HashReady ok st data digest scratch sp len s) :
    WP isa (Impl.Dsa.X86.Generation.hashAbsorb H) s (HashReady ok st data digest scratch sp len) := by
  refine WP.mono (hash_absorb h.geometry h.registers) ?_
  rintro t ⟨A, R, _⟩
  exact ⟨h.geometry.after A, R, A.esp.trans h.stack⟩

theorem hash_digest_ready {H : Hash} {ok : HashOK H} {st data digest scratch sp : BitVec 32} {len offset : Nat} {s : State}
    (h : HashReady ok st data digest scratch sp len s) (position : scratch + BitVec.ofNat 32 offset = digest) :
    WP isa (.block [.mov .edx (.reg .ebp), .alu .add .edx (.imm (BitVec.ofNat 32 offset))]) s
      (FinishReady ok st data digest scratch sp len) := by
  refine WP.mono (hash_digest_setup h.registers position) ?_
  rintro t ⟨edx, _, K⟩
  exact ⟨⟨h.geometry.of_regions K.2.1 K.2.2 (K.1 _ (by decide)), h.registers.of_keeps K (by decide),
    (K.1 _ (by decide)).trans h.stack⟩, edx⟩

private theorem setup_cert (offset : Nat) : ∃ hc, (VG.Taint.check taint (τr [])
    (.block [.mov .edx (.reg .ebp), .alu .add .edx (.imm (BitVec.ofNat 32 offset))]) hc).isSome = true :=
  ⟨.block [], by rfl⟩

theorem seed_hash_ct {H : Hash} (ok : HashOK H) {st data digest scratch sp : BitVec 32} {len offset : Nat}
    (position : scratch + BitVec.ofNat 32 offset = digest) :
    RelCT isa (fun s t => HashReady ok st data digest scratch sp len s ∧ HashReady ok st data digest scratch sp len t)
      (Impl.Dsa.X86.Generation.seedHash H offset) (fun _ _ => True) := by
  have absorbCT := (hash_absorb_ct ok).wp
    (F₁ := HashReady ok st data digest scratch sp len) (F₂ := HashReady ok st data digest scratch sp len)
    (fun _ _ ⟨a, b⟩ => ⟨a.absorb, b.absorb⟩)
  obtain ⟨hc, checked⟩ := setup_cert offset
  have setupCT := (RelCT.taint (A := taint) (τr [])
    (P := fun s t => True ∧ HashReady ok st data digest scratch sp len s ∧ HashReady ok st data digest scratch sp len t)
    (fun _ _ _ => agree_regs (by simp)) checked).wp
    (F₁ := FinishReady ok st data digest scratch sp len) (F₂ := FinishReady ok st data digest scratch sp len)
    (fun _ _ ⟨_, a, b⟩ => ⟨hash_digest_ready a position, hash_digest_ready b position⟩)
  exact absorbCT.seq (setupCT.seq ((hash_finish_ct ok).mono
    (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩) (fun _ _ _ => trivial)))

end VG.Proof.Dsa.X86.Generation
