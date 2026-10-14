module

public import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Iv96
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.BeSetupTo
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Prepared
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PreparedTo
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The prepared loops given the block index: constant time

Untrusted: everything here is checked by Lean. `StitchZH.decR true` loads the
block index from the stack in the middle of its code, after the setup and
the counters' constants. The taint analysis cannot know that value public:
two runs load the same one (`rel_load32`), since they are given the same
index and the code before it writes only the working space, apart from it.
The code before the load and after it is checked by the taint analysis
(`DecRIChecks`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `(a ++ b); c`, related as `a; (b; c)`. -/
theorem rel_seq_block_append {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      rw [Exec.block_iff, execBlock_append] at a₁ a₂
      obtain ⟨⟨m₁, u₁⟩, x₁, y₁⟩ := Option.bind_eq_some_iff.mp a₁
      obtain ⟨⟨m₂, u₂⟩, x₂, y₂⟩ := Option.bind_eq_some_iff.mp a₂
      obtain ⟨⟨n₁, w₁⟩, c₁, d₁⟩ := Option.map_eq_some_iff.mp y₁
      obtain ⟨⟨n₂, w₂⟩, c₂, d₂⟩ := Option.map_eq_some_iff.mp y₂
      simp only [Prod.mk.injEq] at d₁ d₂
      obtain ⟨rfl, rfl⟩ := d₁
      obtain ⟨rfl, rfl⟩ := d₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block x₁) (.seq (.block c₁) b₁))
        (.seq (.block x₂) (.seq (.block c₂) b₂))
      simp only [← List.append_assoc] at ht
      exact ⟨ht, hq⟩

/-- `(a; b); c`, related as `a; (b; c)`. -/
theorem rel_assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq e₁ c₁ =>
    cases e₁ with
    | seq a₁ b₁ =>
      cases e₂ with
      | seq e₂ c₂ =>
        cases e₂ with
        | seq a₂ b₂ =>
          obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
          simp only [← List.append_assoc] at ht
          exact ⟨ht, hq⟩

/-- `mov r10d, [rsp + off]`. -/
theorem load32_ok (off : Nat) {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 off) 4) :
    WP isa (.block [.mov32 .r10 (.mem (at_ .rsp off))]) s fun s' =>
      s'.gpr .r10 = (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 off) 32).setWidth 64 ∧
      ∀ r, r ≠ .r10 → s'.gpr r = s.gpr r := by
  have ea : s.ea (at_ .rsp off) = s.gpr .rsp + BitVec.ofNat 64 off := by
    rw [VG.Proof.Gcm.X86_64.Pclmul.ea_at, BitVec.ofInt_natCast]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, readSrc32, State.load32, ea, hr, ↓reduceIte,
    Option.map_some, State.setReg32, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and]
  intro r hr'
  simp only [RegUpd.gpr_setReg, hr', ↓reduceIte]

/-- A 32-bit load of a stack slot holding the same value in both runs makes
`r10` agree. -/
theorem rel_load32 {P : State → State → Prop} (off : Nat) (rs : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 off) 32 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 off) 32 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 off) 4 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 off) 4)
    (hc : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .r10 (.mem (at_ .rsp off))]) hc).isSome = true) :
    RelCT isa P (.block [.mov32 .r10 (.mem (at_ .rsp off))]) fun s₁ s₂ => ∀ r ∈ .r10 :: rs, s₁.gpr r = s₂.gpr r := by
  have l := RelCT.wpDep (rel_taint (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) hc)
    (F := fun (σ s' : State) => s'.gpr .r10 = (σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 off) 32).setWidth 64 ∧
      ∀ r, r ≠ .r10 → s'.gpr r = σ.gpr r)
    fun s₁ s₂ h => ⟨load32_ok off (hS _ _ h).2.1, load32_ok off (hS _ _ h).2.2⟩
  refine l.mono (fun _ _ h => h) fun s₁ s₂ h r hr => ?_
  obtain ⟨-, σ₁, σ₂, hσ, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ := h
  by_cases hx : r = .r10
  · subst hx; rw [a₁, a₂, (hS _ _ hσ).1]
  · rw [b₁ r hx, b₂ r hx]
    exact hag _ _ hσ r (by simpa [hx] using hr)

/-- The registers public where the prepared loops start: `scratch`'s
working space and the arguments. -/
abbrev regsI : List Reg := [.r11, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

/-- The taint checks of `StitchZH.decR true` around the load of the block
index: the setup from the arguments (`rs` public after it), the constants,
and the rest from `rs` and the index. -/
structure DecRIChecks (rs : List Reg) : Prop where
  rsp : .rsp ∈ rs
  head : ∃ hc, ((taint.check (Taint.ofRegs regsI) Impl.Gcm.X86_64.StitchZH.decRHead hc).map fun τ' =>
    (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  consts : ∃ hc, ((taint.check (Taint.ofRegs rs) (.block ((Impl.Gcm.X86_64.StitchZH.beSetup 0).take 7)) hc).map
    fun τ' => (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  load : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .r10 (.mem (at_ .rsp 16))]) hc).isSome = true
  rest : ∃ hc, (taint.check (Taint.ofRegs (.r10 :: rs)) Impl.Gcm.X86_64.StitchZH.decRBeRest hc).isSome = true

/-- `StitchZH.decR true` in two runs from states with the same arguments and
block index. -/
theorem decRI_rel {rs : List Reg} (hc : DecRIChecks rs) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ regsI, s₁.gpr r = s₂.gpr r) ∧ Gcm.X86_64.Stitch.SPreM CtxMode.prepared s₁ ∧
      Gcm.X86_64.Stitch.SPreM CtxMode.prepared s₂ ∧
      Gcm.X86_64.StitchZ.IdxOk 16 [Gcm.X86_64.Stitch.dR s₁, Gcm.X86_64.Stitch.pR s₁] s₁ ∧
      Gcm.X86_64.StitchZ.IdxOk 16 [Gcm.X86_64.Stitch.dR s₂, Gcm.X86_64.Stitch.pR s₂] s₂ ∧
      s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 16) 32 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 16) 32)
      (Impl.Gcm.X86_64.StitchZH.decR true) fun _ _ => True := by
  intro s₀ s₀' t₁ t₂ u₁ u₂ hP
  obtain ⟨hr, hp, hp', hx, hx', hi⟩ := hP
  revert t₁ t₂ u₁ u₂
  -- The setup, in each run.
  have a := rel_wp (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
    (rel_regs regsI rs false (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hr) hc.head)
    (F₁ := (· = s₀)) (F₂ := (· = s₀')) (fun _ _ h => h)
    (G₁ := fun t => ∃ P, Gcm.X86_64.StitchZ.Ready s₀ P t)
    (G₂ := fun t => ∃ P, Gcm.X86_64.StitchZ.Ready s₀' P t)
    (fun _ e => by subst e; exact WP.mono (Gcm.X86_64.StitchZH.setup_ok hp.toPrepared) fun _ ⟨P, hR, _, _⟩ => ⟨P, hR⟩)
    (fun _ e => by subst e; exact WP.mono (Gcm.X86_64.StitchZH.setup_ok hp'.toPrepared) fun _ ⟨P, hR, _, _⟩ => ⟨P, hR⟩)
  -- The constants, in each run, keeping the index.
  have b := rel_wp (P := fun s₁ s₂ => ((∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ (false = true → s₁.cf = s₂.cf ∧
      s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧ (∃ P, Gcm.X86_64.StitchZ.Ready s₀ P s₁) ∧
      ∃ P, Gcm.X86_64.StitchZ.Ready s₀' P s₂)
    (rel_regs rs rs false (fun _ _ h => h.1.1) hc.consts)
    (F₁ := fun t => ∃ P, Gcm.X86_64.StitchZ.Ready s₀ P t) (F₂ := fun t => ∃ P, Gcm.X86_64.StitchZ.Ready s₀' P t)
    (fun _ _ h => h.2)
    (fun _ ⟨_, hR⟩ => Gcm.X86_64.StitchZH.consts_keep hp.base hx hR)
    (fun _ ⟨_, hR⟩ => Gcm.X86_64.StitchZH.consts_keep hp'.base hx' hR)
  have l := rel_load32 (P := fun s₁ s₂ => ((∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ (false = true → s₁.cf = s₂.cf ∧
      s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 16) 32 = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 32 ∧
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 16) 4) ∧
      (s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 16) 32 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 16) 32 ∧
        InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 16) 4))
    16 rs hc.rsp (fun _ _ h => h.1.1) (fun _ _ h => ⟨by rw [h.2.1.1, h.2.2.1, hi], h.2.1.2, h.2.2.2⟩) hc.load
  have c := rel_taint (P := fun s₁ s₂ => ∀ r ∈ .r10 :: rs, s₁.gpr r = s₂.gpr r) (.r10 :: rs) (fun _ _ h => h)
    hc.rest
  have e : Impl.Gcm.X86_64.StitchZH.decR true = .seq Impl.Gcm.X86_64.StitchZH.decRHead
      (.seq (.block ((Impl.Gcm.X86_64.StitchZH.beSetup 0).take 7 ++ ([.mov32 .r10 (.mem (at_ .rsp 16))] ++
        [.alu32 .sub .r10 (.imm 1), .shift32 .shl .r10 24, .alu .cmp .r9 (.imm 256)])))
        (Impl.Gcm.X86_64.StitchZH.decRTail true)) := rfl
  have whole : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.Gcm.X86_64.StitchZH.decR true) fun _ _ => True := by
    rw [e]
    exact RelCT.seq a (rel_seq_block_append (RelCT.seq b (rel_seq_block_append (RelCT.seq l c))))
  exact fun t₁ t₂ u₁ u₂ e₁ e₂ => whole _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- The taint checks of `StitchZHTo.encR true` around the load of the block
index, as `DecRIChecks`. -/
structure EncRIChecks (rs : List Reg) : Prop where
  rsp : .rsp ∈ rs
  head : ∃ hc, ((taint.check (Taint.ofRegs (.r10 :: regsI)) Impl.Gcm.X86_64.StitchZHTo.encRHead hc).map fun τ' =>
    (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  consts : ∃ hc, ((taint.check (Taint.ofRegs rs) (.block ((Impl.Gcm.X86_64.StitchZH.beSetup 0).take 7)) hc).map
    fun τ' => (RegSet.ofList rs).subset τ'.regs && (!false || τ'.flags)) = some true
  load : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov32 .r10 (.mem (at_ .rsp 32))]) hc).isSome = true
  rest : ∃ hc, (taint.check (Taint.ofRegs (.r10 :: rs)) Impl.Gcm.X86_64.StitchZHTo.encRBeRest hc).isSome = true

/-- `StitchZHTo.encR true` in two runs from states with the same arguments
(the output in `r10`) and block index. -/
theorem encRI_rel {rs : List Reg} (hc : EncRIChecks rs) :
    RelCT isa (fun s₁ s₂ => (∀ r ∈ .r10 :: regsI, s₁.gpr r = s₂.gpr r) ∧
      Gcm.X86_64.Stitch.SPreTo CtxMode.prepared s₁ ∧ Gcm.X86_64.Stitch.SPreTo CtxMode.prepared s₂ ∧
      Gcm.X86_64.StitchZ.IdxOk 32 [Gcm.X86_64.Stitch.oR s₁, Gcm.X86_64.Stitch.pR s₁] s₁ ∧
      Gcm.X86_64.StitchZ.IdxOk 32 [Gcm.X86_64.Stitch.oR s₂, Gcm.X86_64.Stitch.pR s₂] s₂ ∧
      s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 32 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 32)
      (Impl.Gcm.X86_64.StitchZHTo.encR true) fun _ _ => True := by
  intro s₀ s₀' t₁ t₂ u₁ u₂ hP
  obtain ⟨hr, hp, hp', hx, hx', hi⟩ := hP
  revert t₁ t₂ u₁ u₂
  have a := rel_wp (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
    (rel_regs (.r10 :: regsI) rs false (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact hr) hc.head)
    (F₁ := (· = s₀)) (F₂ := (· = s₀')) (fun _ _ h => h)
    (G₁ := fun t => ∃ P, Gcm.X86_64.StitchZTo.ReadyTo s₀ P t)
    (G₂ := fun t => ∃ P, Gcm.X86_64.StitchZTo.ReadyTo s₀' P t)
    (fun _ e => by subst e; exact WP.mono (Gcm.X86_64.StitchZHTo.setup_ok hp) fun _ ⟨P, hR, _, _⟩ => ⟨P, hR⟩)
    (fun _ e => by subst e; exact WP.mono (Gcm.X86_64.StitchZHTo.setup_ok hp') fun _ ⟨P, hR, _, _⟩ => ⟨P, hR⟩)
  have b := rel_wp (P := fun s₁ s₂ => ((∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ (false = true → s₁.cf = s₂.cf ∧
      s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧ (∃ P, Gcm.X86_64.StitchZTo.ReadyTo s₀ P s₁) ∧
      ∃ P, Gcm.X86_64.StitchZTo.ReadyTo s₀' P s₂)
    (rel_regs rs rs false (fun _ _ h => h.1.1) hc.consts)
    (F₁ := fun t => ∃ P, Gcm.X86_64.StitchZTo.ReadyTo s₀ P t)
    (F₂ := fun t => ∃ P, Gcm.X86_64.StitchZTo.ReadyTo s₀' P t)
    (fun _ _ h => h.2)
    (fun _ ⟨_, hR⟩ => Gcm.X86_64.StitchZHTo.constsTo_keep hp hx hR)
    (fun _ ⟨_, hR⟩ => Gcm.X86_64.StitchZHTo.constsTo_keep hp' hx' hR)
  have l := rel_load32 (P := fun s₁ s₂ => ((∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ (false = true → s₁.cf = s₂.cf ∧
      s₁.zf = s₂.zf ∧ s₁.sf = s₂.sf ∧ s₁.of = s₂.of)) ∧
      (s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 32 = s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 32 ∧
        InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 4) ∧
      (s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 32 = s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 32) 32 ∧
        InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 4))
    32 rs hc.rsp (fun _ _ h => h.1.1) (fun _ _ h => ⟨by rw [h.2.1.1, h.2.2.1, hi], h.2.1.2, h.2.2.2⟩) hc.load
  have c := rel_taint (P := fun s₁ s₂ => ∀ r ∈ .r10 :: rs, s₁.gpr r = s₂.gpr r) (.r10 :: rs) (fun _ _ h => h)
    hc.rest
  have e : Impl.Gcm.X86_64.StitchZHTo.encR true = .seq Impl.Gcm.X86_64.StitchZHTo.encRHead
      (.seq (.seq (.block ((Impl.Gcm.X86_64.StitchZH.beSetup 0).take 7 ++ ([.mov32 .r10 (.mem (at_ .rsp 32))] ++
        [.alu32 .sub .r10 (.imm 1), .shift32 .shl .r10 24])))
        (Impl.Gcm.X86_64.StitchZHTo.batchTo 0 (fun _ => []) true)) (Impl.Gcm.X86_64.StitchZHTo.encRTail true)) := rfl
  have whole : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (Impl.Gcm.X86_64.StitchZHTo.encR true)
      fun _ _ => True := by
    rw [e]
    exact RelCT.seq a (rel_assoc' (rel_seq_block_append (RelCT.seq b
      (rel_seq_block_append (RelCT.seq l c)))))
  exact fun t₁ t₂ u₁ u₂ e₁ e₂ => whole _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

end VG.Proof.AesGcm.X86_64
