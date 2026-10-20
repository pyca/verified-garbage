module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.AesGcm.X86.CT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.AesSiv.X86
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Env

/-!
# AES-SIV on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-SIV code.
-/

@[expose] public section

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
tactic_template "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := first | decide | omega) only [VG.X86.runBlock_cons, VG.X86.runStep_some,
                     VG.X86.runBlock_nil, VG.X86.exec, VG.X86.readSrc, VG.X86.execAlu, VG.X86.execShift, VG.X86.State.load32, VG.Proof.AesGcm.X86.store32_eq, VG.X86.State.load8, VG.Proof.AesGcm.X86.store8_eq,
                     VG.X86.State.ea, VG.Impl.AesGcm.X86.at_, VG.Impl.AesGcm.X86.imm, VG.Impl.AesGcm.X86.slot, VG.Impl.AesGcm.X86.argOp, VG.Impl.AesSiv.X86.zOff, VG.Impl.AesSiv.X86.tailOff, VG.Impl.AesSiv.X86.ksOff, VG.Impl.AesSiv.X86.cbOff, VG.Impl.AesSiv.X86.tOff, VG.Impl.AesSiv.X86.stOff, VG.Impl.AesSiv.X86.dbOff, VG.Impl.AesSiv.X86.ctxO, VG.Impl.AesSiv.X86.roundsO, VG.Impl.AesSiv.X86.adsO, VG.Impl.AesSiv.X86.leftO,
                     VG.Impl.AesSiv.X86.dataO, VG.Impl.AesSiv.X86.lenO, VG.Impl.AesSiv.X86.strO, VG.Impl.AesSiv.X86.slenO, VG.Impl.AesSiv.X86.nbO, VG.Impl.AesSiv.X86.jO, VG.Impl.AesSiv.X86.okO, VG.Impl.AesSiv.X86.csOff, VG.Impl.AesSiv.X86.dOff, List.cons_append, List.nil_append, List.append_assoc,
                     Option.bind_some, Option.map_some, VG.Proof.AesGcm.X86.readW_writeW_off, VG.Proof.AesSiv.X86.readW_writeB_off, VG.X86.RegUpd.gpr_setReg_self, VG.X86.RegUpd.gpr_setReg_of_ne, VG.X86.RegUpd.gpr_arithFlags, VG.X86.RegUpd.gpr_setFlags, VG.X86.RegUpd.mem_setReg,
                     VG.X86.RegUpd.mem_arithFlags, VG.X86.RegUpd.mem_setFlags, VG.X86.RegUpd.rd_setReg, VG.X86.RegUpd.rd_arithFlags, VG.X86.RegUpd.rd_setFlags, VG.X86.RegUpd.wr_setReg, VG.X86.RegUpd.wr_arithFlags,
                     VG.X86.RegUpd.wr_setFlags, VG.X86.RegUpd.cf_setReg, VG.X86.RegUpd.cf_arithFlags, VG.X86.RegUpd.zf_setReg, VG.X86.RegUpd.zf_arithFlags, VG.Proof.AesGcm.X86.gpr_setMem, VG.Proof.AesGcm.X86.mem_setMem, VG.Proof.AesGcm.X86.rd_setMem,
                     VG.Proof.AesGcm.X86.wr_setMem, VG.Proof.AesGcm.X86.cf_setMem, VG.Proof.AesGcm.X86.zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT,
                     Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self, and_true, true_and,
                     eq_self_iff_true, VG.X86.Reg8.reg, $ts,*]) <;>
                   try rfl)

/-- Reads registers through the writes of a block. -/
tactic_template "cregs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := first | decide | with_reducible assumption) only [VG.Proof.AesGcm.X86.gpr_setMem, VG.X86.RegUpd.gpr_setReg_self, VG.X86.RegUpd.gpr_setReg_of_ne, VG.X86.RegUpd.gpr_arithFlags, VG.X86.RegUpd.gpr_setFlags,
                     $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
tactic_template "cmems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := first | decide | omega) only [VG.Proof.AesGcm.X86.mem_setMem, VG.X86.RegUpd.mem_setReg, VG.X86.RegUpd.mem_arithFlags, VG.X86.RegUpd.mem_setFlags,
                     VG.Proof.AesGcm.X86.rd_setMem, VG.X86.RegUpd.rd_setReg, VG.X86.RegUpd.rd_arithFlags, VG.X86.RegUpd.rd_setFlags, VG.Proof.AesGcm.X86.wr_setMem, VG.X86.RegUpd.wr_setReg, VG.X86.RegUpd.wr_arithFlags, VG.X86.RegUpd.wr_setFlags,
                     VG.Proof.AesGcm.X86.zf_setMem, VG.X86.RegUpd.zf_setReg, VG.X86.RegUpd.zf_arithFlags, VG.Proof.AesGcm.X86.cf_setMem, VG.X86.RegUpd.cf_setReg, VG.X86.RegUpd.cf_arithFlags, VG.Proof.AesGcm.X86.gpr_setMem, VG.X86.RegUpd.gpr_setReg_self,
                     VG.X86.RegUpd.gpr_setReg_of_ne, VG.X86.RegUpd.gpr_arithFlags, VG.X86.RegUpd.gpr_setFlags, VG.Mem.readW_writeW_self32, VG.Proof.AesGcm.X86.readW_writeW_off, VG.Proof.AesSiv.X86.readW_writeB_off, VG.Impl.AesSiv.X86.zOff, VG.Impl.AesSiv.X86.tailOff,
                     VG.Impl.AesSiv.X86.ksOff, VG.Impl.AesSiv.X86.cbOff, VG.Impl.AesSiv.X86.tOff, VG.Impl.AesSiv.X86.stOff, VG.Impl.AesSiv.X86.dbOff, VG.Impl.AesSiv.X86.ctxO, VG.Impl.AesSiv.X86.roundsO, VG.Impl.AesSiv.X86.adsO, VG.Impl.AesSiv.X86.leftO, VG.Impl.AesSiv.X86.dataO, VG.Impl.AesSiv.X86.lenO, VG.Impl.AesSiv.X86.strO, VG.Impl.AesSiv.X86.slenO, VG.Impl.AesSiv.X86.nbO, VG.Impl.AesSiv.X86.jO, VG.Impl.AesSiv.X86.okO, VG.Impl.AesSiv.X86.csOff, VG.Impl.AesSiv.X86.dOff,
                     Nat.reduceAdd, VG.X86.Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

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

/-- A loop of `n` iterations, its body constant time and leaving the
condition to loop back exactly while iterations are left. -/
theorem CT.loopN {body : Prog isa} {c : Cond} (Inv : Nat → State → Prop)
    (hb : ∀ n, Proof.AesGcm.X86.CT (Inv n) body)
    (hw : ∀ n s, Inv n s → WP isa body s fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s'))
    (n : Nat) : Proof.AesGcm.X86.CT (Inv n) (.loop body c) := by
  refine RelCT.loop (M := isa) (Q := fun _ _ => True) (fun n (s₁ s₂ : State) => Inv n s₁ ∧ Inv n s₂) (fun n => ?_) n
  have h := RelCT.wp (hb n) (F₁ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) (F₂ := fun s' => 0 < n ∧ isa.eval c s' = some (decide (n ≠ 1)) ∧
      (n ≠ 1 → Inv (n - 1) s')) fun s₁ s₂ h => ⟨hw n s₁ h.1, hw n s₂ h.2⟩
  refine RelCT.mono h (fun _ _ h => h) fun s₁ s₂ ⟨_, ⟨hn, c₁, i₁⟩, ⟨_, c₂, i₂⟩⟩ => ⟨by rw [c₁, c₂], fun _ => trivial,
    fun ht => ?_⟩
  rw [c₁] at ht
  have h1 : n ≠ 1 := by simpa using ht
  exact ⟨n - 1, by omega, i₁ h1, i₂ h1⟩

end VG.Proof.AesSiv.X86
