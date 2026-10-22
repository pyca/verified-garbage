module

public import VerifiedGarbage.Proof.MillerRabin.X86.AppendReady
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingLoop

/-! # Fourteen table products and appends have a public trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem table_transfer_ct {σ₁ σ₂ : State} {base : Addr} {bytes w n : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hn : n < 14) :
    RelCT isa (fun s t => AppendReady σ₁ base bytes w n s ∧ AppendReady σ₂ base bytes w n t) tabTransfer
      (fun s t => TransferReady σ₁ base bytes w n s ∧ TransferReady σ₂ base bytes w n t) := by
  have native := C.stack_word (by decide : tableCursor + 4 ≤ 1132) table_transfer_cert
  have core := native.mono (P' := fun s t => AppendReady σ₁ base bytes w n s ∧ AppendReady σ₂ base bytes w n t)
    (fun s t ⟨h₁, h₂⟩ => ⟨h₁.stage, h₂.stage, by
      have c₁ : s.mem.readW (off (byteAddr sp) tableCursor) 32 = ptr32 base (arrAt w (13 + n)) := by
        rw [← C.initial₁.stack]
        exact h₁.cursor
      have c₂ : t.mem.readW (off (byteAddr sp) tableCursor) 32 = ptr32 base (arrAt w (13 + n)) := by
        rw [← C.initial₂.stack]
        exact h₂.cursor
      exact c₁.trans c₂.symm⟩) (fun _ _ _ => trivial)
  exact (core.wp (F₁ := TransferReady σ₁ base bytes w n) (F₂ := TransferReady σ₂ base bytes w n)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨table_transfer_ready C.facts₁ h₁ hn, table_transfer_ready C.facts₂ h₂ hn⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩)

theorem table_end_ct {σ₁ σ₂ : State} {base : Addr} {bytes w n : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => TransferReady σ₁ base bytes w n s ∧ TransferReady σ₂ base bytes w n t)
      (.block tabEnd) (fun _ _ => True) := by
  apply (C.header (by decide : sK + 4 ≤ 1600) table_end_cert).mono
  · rintro s t ⟨h₁, h₂⟩
    refine ⟨h₁.stage, h₂.stage, (readW_of_w32 (by omega) h₁.count).trans (readW_of_w32 (by omega) h₂.count).symm, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r
    exact h₁.dest.trans h₂.dest.symm
  · intro _ _ _
    trivial

theorem table_step_ct {σ₁ σ₂ : State} {base : Addr} {bytes w n : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) (hn : n < 14) :
    RelCT isa (fun s t => TableState σ₁ base bytes w n s ∧ TableState σ₂ base bytes w n t) tabStep
      (fun s t => TableState σ₁ base bytes w (n + 1) s ∧ TableState σ₂ base bytes w (n + 1) t ∧
        s.zf = some (decide (n + 1 = 14)) ∧ t.zf = some (decide (n + 1 = 14))) := by
  have productCT := ((C.multiply (o := 6) (a := 6) (b := 5) (by decide) (by decide) (by decide)
    digit_args_cert).mono (P' := fun s t => TableState σ₁ base bytes w n s ∧ TableState σ₂ base bytes w n t)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨⟨h₁.stage, by rw [h₁.witness]; exact C.facts₁.witness⟩,
      ⟨h₂.stage, by rw [h₂.witness]; exact C.facts₂.witness⟩⟩) (fun _ _ _ => trivial)).wp
    (F₁ := AppendReady σ₁ base bytes w n) (F₂ := AppendReady σ₂ base bytes w n)
    (fun _ _ ⟨h₁, h₂⟩ => ⟨table_product_ready C.facts₁ h₁, table_product_ready C.facts₂ h₂⟩)
  have transferCT := (table_transfer_ct C hn).mono
    (P' := fun s t => True ∧ AppendReady σ₁ base bytes w n s ∧ AppendReady σ₂ base bytes w n t)
    (fun _ _ ⟨_, h₁, h₂⟩ => ⟨h₁, h₂⟩) (fun _ _ h => h)
  have core := productCT.seq (transferCT.seq (table_end_ct C))
  exact (core.wp (fun _ _ ⟨h₁, h₂⟩ => ⟨table_state_step C.facts₁ hn h₁, table_state_step C.facts₂ hn h₂⟩)).mono
    (fun _ _ h => h) (fun _ _ ⟨_, ⟨h₁, z₁⟩, ⟨h₂, z₂⟩⟩ => ⟨h₁, h₂, z₁, z₂⟩)

theorem table_loop_ct {σ₁ σ₂ : State} {base : Addr} {bytes w : Nat} {sp len : BitVec 32}
    (C : TimingContext σ₁ σ₂ base bytes w sp len) :
    RelCT isa (fun s t => TableState σ₁ base bytes w 0 s ∧ TableState σ₂ base bytes w 0 t)
      (.loop tabStep .ne) (fun s t => TableState σ₁ base bytes w 14 s ∧ TableState σ₂ base bytes w 14 t) := by
  apply count_loop_ct (by decide) (fun j s t => TableState σ₁ base bytes w j s ∧ TableState σ₂ base bytes w j t)
  intro j hj
  exact (table_step_ct C hj).mono (fun _ _ h => h) (fun _ _ ⟨h₁, h₂, z₁, z₂⟩ => ⟨⟨h₁, h₂⟩, z₁, z₂⟩)

end VG.Proof.MillerRabin.X86
