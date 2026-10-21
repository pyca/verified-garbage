module
public meta import VerifiedGarbage.Impl.Dsa.X86.KeyRandom
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Finish
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CTDefs
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.DrawCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Prepare
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Cleanup branches on status and writes through public output pointers -/

@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

def FinAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => Fin s₀ t ∧ (rResult s₀).status = p.2) p.1

/-! ## The end -/

/-- Test the overall status. -/
theorem finTest_ok {s₀ t : State} (A : KeyABI s₀) (Fi : Fin s₀ t) :
    WP isa (.block [.mov .eax (.mem (sp oStatus)), .alu .cmp .eax (.imm 1)]) t fun u =>
      Ready s₀ u ∧ u.zf = some (decide ((rResult s₀).status = 1)) := by
  have hR := result_status_le A
  refine wp_movS (v := BitVec.ofNat 32 (rResult s₀).status)
    (by rw [Fi.ready.rf.readSlot (by decide)]; exact congrArg some Fi.status)
    fun t₁ u₁ _ => wp_cmpi fun t₂ f₂ _ z₂ => WP.block_nil ⟨(Fi.ready.upd u₁ (by decide)).fupd f₂, ?_⟩
  rw [z₂, u₁.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]

/-- The output's address and length. -/
theorem zeroHead_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    WP isa (.block [.mov .esi (.mem (KeyRandom.arg aOut)), .mov .ecx (.mem (KeyRandom.arg aOutLen)), .mov .eax (.imm 0)])
      t fun u => Ready s₀ u ∧ u.gpr .esi = X86.arg s₀ 0 ∧ u.gpr .ecx = X86.arg s₀ 1 := by
  refine wp_movS (h.argSrc A (j := 0) (by decide)) fun t₁ u₁ _ => ?_
  have h₁ := h.upd u₁ (by decide)
  refine wp_movS (h₁.argSrc A (j := 1) (by decide)) fun t₂ u₂ _ => wp_movS rfl fun t₃ u₃ _ => WP.block_nil ?_
  exact ⟨(h₁.upd u₂ (by decide)).upd u₃ (by decide), by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₃.other _ (by decide), u₂.gpr]⟩

/-- The scalar cleared, and the address of `used`. -/
theorem finPrefix_ok {s₀ t : State} (A : KeyABI s₀) (h : Ready s₀ t) :
    WP isa (.block (clearNonce ++ ([.mov .edx (.mem (KeyRandom.arg aUsed))] : List Instr))) t fun u =>
      Ready s₀ u ∧ u.gpr .edx = X86.arg s₀ 2 := by
  refine clearNonce_ok h.rf fun t₁ _ m₁ k₁ _ => ?_
  have h₁ : Ready s₀ t₁ := h.congr k₁ (by rw [m₁]; exact clearMem_frame s₀ _ 8 (by decide))
  exact wp_movS (h₁.argSrc A (j := 2) (by decide)) fun t₂ u₂ _ => WP.block_nil ⟨h₁.upd u₂ (by decide), u₂.gpr⟩

/-- Ready, with public data `p.1`. -/
def ReadyAt (p : Pub × Nat) : State → Prop := At (fun s₀ t => Ready s₀ t) p.1

theorem zeroOut_ct : RelCT isa (Two fun p s => ReadyAt p s ∧ isa.eval .ne s = some true) zeroOut
    fun _ _ => True := by
  unfold zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => Ready s₀ t ∧ t.gpr .esi = X86.arg s₀ 0 ∧
      t.gpr .ecx = X86.arg s₀ 1) p.1) [.esp] (pins_at' (P := fun _ s₀ t => Ready s₀ t) Prod.fst
      fun _ _ _ h => h) (by taint_decide)
    fun p t ⟨⟨s₀, A, e, h⟩, _⟩ => WP.mono (zeroHead_ok A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.esi, .ecx] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, _, x₁, c₁⟩ := h₁
  obtain ⟨s₂, _, e₂, _, x₂, c₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [x₁, x₂, pub_arg e 0 (by decide)]
  · rw [c₁, c₂, pub_arg e 1 (by decide)]

theorem finalBlock_ct : RelCT isa (Two ReadyAt)
    (.block (clearNonce ++ ([.mov .edx (.mem (KeyRandom.arg aUsed)), .mov .eax (.mem (sp oUsed)),
      .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
      .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
      .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
      .mov .eax (.mem (sp oStatus))] : List Instr))) fun _ _ => True := by
  show RelCT isa _ (.block ((clearNonce ++ [.mov .edx (.mem (KeyRandom.arg aUsed))]) ++
    [.mov .eax (.mem (sp oUsed)), .store (at_ .edx 0) .eax, .mov .eax (.imm 0), .store (at_ .edx 4) .eax,
      .mov .ebx (.mem (sp oSaveEbx)), .mov .esi (.mem (sp oSaveEsi)),
      .mov .edi (.mem (sp oSaveEdi)), .mov .ebp (.mem (sp oSaveEbp)),
      .mov .eax (.mem (sp oStatus))])) _
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := fun p => At (fun s₀ t => Ready s₀ t ∧ t.gpr .edx = X86.arg s₀ 2) p.1)
    [.esp] (pins_at (P := fun _ s₀ t => Ready s₀ t) Prod.fst fun _ _ _ h => h) (by taint_decide)
    fun p t ⟨s₀, A, e, h⟩ => WP.mono (finPrefix_ok A h) fun u hu => ⟨s₀, A, e, hu⟩) ?_
  refine two_taint [.esp, .edx] (fun p t₁ t₂ h₁ h₂ r hr => ?_) (by taint_decide)
  obtain ⟨s₁, _, e₁, r₁, d₁⟩ := h₁
  obtain ⟨s₂, _, e₂, r₂, d₂⟩ := h₂
  have e := e₁.trans e₂.symm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact esp_of_rf r₁.rf (pub_rBase e ▸ r₂.rf)
  · rw [d₁, d₂, pub_arg e 2 (by decide)]

theorem finish_ct : RelCT isa (Two FinAt) finish fun _ _ => True := by
  unfold finish
  refine RelCT.seq (two_piece (Ψ := fun (p : Pub × Nat) => At (fun s₀ t => Ready s₀ t ∧
      t.zf = some (decide (p.2 = 1))) p.1) [.esp]
    (pins_at (P := fun p s₀ t => Fin s₀ t ∧ (rResult s₀).status = p.2) Prod.fst fun _ _ _ h => h.1.ready)
    (by taint_decide) fun p t ⟨s₀, A, e, Fi, st⟩ => WP.mono (finTest_ok A Fi)
      fun u ⟨h, z⟩ => ⟨s₀, A, e, h, by rw [z, st]⟩) ?_
  refine RelCT.seq (R := Two ReadyAt) (two_ite (fun p t₁ t₂ ⟨_, _, _, _, z₁⟩ ⟨_, _, _, _, z₂⟩ => by
    simp only [eval, z₁, z₂]) ?_ ?_) finalBlock_ct
  · exact two_post (Ψ := ReadyAt) (two_map id (fun p t ⟨⟨s₀, A, e, h, _⟩, hb⟩ => ⟨⟨s₀, A, e, h⟩, hb⟩) zeroOut_ct)
      fun p t ⟨⟨s₀, A, e, h, _⟩, _⟩ => WP.mono (zeroOut_ok A h) fun u hu => ⟨s₀, A, e, hu.1⟩
  · exact two_post (Ψ := ReadyAt) (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide))
      fun p t ⟨⟨s₀, A, e, h, _⟩, _⟩ => WP.block_nil ⟨s₀, A, e, h⟩

end VG.Proof.Dsa.X86.KeyRandom
