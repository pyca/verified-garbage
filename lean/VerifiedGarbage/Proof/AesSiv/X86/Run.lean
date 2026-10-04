import VerifiedGarbage.Proof.AesSiv.X86.Env
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-SIV on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-SIV code.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp)
open VG.Proof.AesGcm.X86 (store32_eq store8_eq gpr_setMem mem_setMem rd_setMem wr_setMem cf_setMem zf_setMem
  readW_writeW_off CT)

/-- A word at `p + a`, after a byte written at `p + b` elsewhere. -/
theorem readW_writeB_off (m : Mem) (p : Addr) (v : BitVec 8) {a b : Nat} (h : a + 4 ≤ b ∨ b + 1 ≤ a)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 b) v).readW (p + BitVec.ofNat 64 a) 32 = m.readW (p + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega) (by omega)) (by decide)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Runs a block of the instructions the AES-SIV code uses. The facts given
rewrite the addresses and discharge the permissions. -/
macro "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
    State.ea, at_, imm, slot, argOp, zOff, tailOff, cntOff, ksOff, cbOff, tOff, stOff, dbOff, ctxO, roundsO, adsO, leftO,
    dataO, lenO, strO, slenO, nbO, jO, okO, csOff, dOff, List.cons_append, List.nil_append, List.append_assoc,
    Option.bind_some, Option.map_some, readW_writeW_off, readW_writeB_off, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, mem_setReg,
    mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
    wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem, mem_setMem, rd_setMem,
    wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT,
    Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self, and_true, true_and,
    eq_self_iff_true, Reg8.reg, $ts,*]) <;>
  try rfl)

/-- Reads registers through the writes of a block. -/
macro "cregs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | with_reducible assumption) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
    $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
macro "cmems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
    rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
    zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
    gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, readW_writeB_off, zOff, tailOff, cntOff,
    ksOff, cbOff, tOff, stOff, dbOff, ctxO, roundsO, adsO, leftO, dataO, lenO, strO, slenO, nbO, jO, okO, csOff, dOff,
    Nat.reduceAdd, Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-- A block, then code: the block constant time by the taint analysis from
the registers `rs`, which `I` pins, and the code from what the block leaves
(`F`, from the state it started in). -/
theorem CT.block_seq {I : State → Prop} {is : List Instr} {c : Prog isa} {F : State → State → Prop}
    (rs : List Reg) (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) (.block is) hc).isSome = true)
    (blk : ∀ s, I s → ∃ s', runBlock isa is s = some s' ∧ F s s') (h₂ : CT (fun s' => ∃ s, I s ∧ F s s') c) :
    CT I (.seq (.block is) c) :=
  CT.seq (CT.taint rs hr h) (fun s hs => let ⟨s', r, f⟩ := blk s hs; WP.of_runBlock ⟨s', r, s, hs, f⟩) h₂

/-- `a; (b; (c; d))` from `(a; (b; c)); d`. -/
theorem CT.assoc3 {I : State → Prop} {a b c d : Prog isa}
    (h : Proof.AesGcm.X86.CT I (.seq (.seq a (.seq b c)) d)) : Proof.AesGcm.X86.CT I (.seq a (.seq b (.seq c d))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ e₁ =>
    cases e₁ with
    | seq b₁ e₁ =>
      cases e₁ with
      | seq c₁ d₁ =>
        cases e₂ with
        | seq a₂ e₂ =>
          cases e₂ with
          | seq b₂ e₂ =>
            cases e₂ with
            | seq c₂ d₂ =>
              obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
              simp only [List.append_assoc] at ht
              exact ⟨ht, hq⟩

/-- A register pinned. -/
theorem pin1 {I : State → Prop} {a : Reg} {x : BitVec 32} (h : ∀ s, I s → s.gpr a = x) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- `ebp` pinned. -/
theorem pin_ebp {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- Two registers pinned. -/
theorem pin2 {I : State → Prop} {a b : Reg} {x y : BitVec 32} (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2, (h _ h₂).2]

/-- Three registers pinned. -/
theorem pin3 {I : State → Prop} {a b c : Reg} {x y z : BitVec 32}
    (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y ∧ s.gpr c = z) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b, c], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2.1, (h _ h₂).2.1]
  · rw [(h _ h₁).2.2, (h _ h₂).2.2]

end VG.Proof.AesSiv.X86
