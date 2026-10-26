module

public import VerifiedGarbage.Proof.Dsa.Arm.RandomFinish
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.RandomSample
import VerifiedGarbage.Proof.Dsa.Arm.RandomScan
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
import Mathlib.Basic.Logic.Basic

/-!
# The randomized signer's body (32-bit ARM)

From the reserved frame, `entry` saves the callee-saved registers and the
register arguments (`Saved`) and starts the counts (`entry_ok`); `prepare`
scans q, and the attempts run until one returns a status other than 4,
which `finish` returns (`body_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_cmp wp_str op2_imm op2_reg eval_eq eval_ne
  ofNat_beq_zero toNat_imm)

/-! ## The specification's result -/

/-- With valid lengths, the result is the signing loop's. -/
theorem rResult_loop {s₀ : State} (A : RandomABI s₀) :
    rResult s₀ = Spec.Dsa.randomSignLoop (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key (rInput s₀).digest 8
      (rInput s₀).rand := by
  have hk : (rInput s₀).key.length = 3 * (rInput s₀).pLen + 2 * (rInput s₀).qLen := by
    simp only [rInput, rBytes_length, A.keyLength]
  have hl : Spec.Dsa.lengthsValid (rInput s₀).pLen (rInput s₀).qLen := A.lengths
  simp only [rResult, Spec.Dsa.randomSignBytes, hk, hl, decide_true, Bool.not_true, bne_self_eq_false,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte]

/-- q ≤ 1 fails without consuming input. -/
theorem rResult_small {s₀ : State} (A : RandomABI s₀) (hq : ¬ 1 < rq s₀) :
    rResult s₀ = ⟨none, 0, 0, [4]⟩ := by
  rw [rResult_loop A, Spec.Dsa.randomSignLoop]
  have hs : Spec.Dsa.Random.sample (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen
      (rInput s₀).key).params.q 128 (rInput s₀).rand = ⟨none, 0, [4]⟩ := by
    have h1 : (Spec.Dsa.privateKeyBytes (rInput s₀).pLen (rInput s₀).qLen (rInput s₀).key).params.q ≤ 1 := by
      rw [← rQ_decode]; exact Nat.le_of_not_lt hq
    rw [Spec.Dsa.Random.sample]; simp only [h1, ↓reduceIte]
  simp only [hs]
  rfl

theorem rResult_status_le {s₀ : State} (A : RandomABI s₀) : (rResult s₀).status ≤ 2 := by
  rw [rResult_loop A]; exact VG.Proof.Dsa.randomSignLoop_status_le _ _ _ _ _ _

theorem rResult_signature {s₀ : State} (A : RandomABI s₀) :
    (rResult s₀).status ≠ 1 → (rResult s₀).signature = none := by
  rw [rResult_loop A]
  intro h
  have := (VG.Proof.Dsa.randomSignLoop_success _ _ _ _ _ _).not.mp h
  simpa using this

theorem rResult_used_le {s₀ : State} : (rResult s₀).used ≤ (rInput s₀).rand.length :=
  VG.Proof.Dsa.randomSignBytes_used_le _ _ _ _ _

/-! ## The entry -/

/-- Before `r11` holds the frame's base, `r12` does. -/
structure PreR (s₀ t : State) : Prop where
  r12 : t.gpr .r12 = s₀.sp - BitVec.ofNat 32 frameBytes
  sp : t.sp = s₀.sp - BitVec.ofNat 32 frameBytes
  rd : t.rd = s₀.rd
  wr : t.wr = ⟨rBase s₀, frameBytes⟩ :: s₀.wr
  frame : Frame (rWrites s₀) s₀.mem t.mem

/-- `str r, [r12, #d]`, a slot of the frame. -/
theorem wp_strP {s₀ t : State} (A : RandomABI s₀) (P : PreR s₀ t) {r : Reg} {d : Nat} (hd : d + 4 ≤ frameBytes)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, PreR s₀ u → u.mem = t.mem.writeW (off (rBase s₀) d) (t.gpr r) → u.gpr = t.gpr →
      WP isa (.block is) u Q) :
    WP isa (.block (.str r .r12 d :: is)) t Q := by
  have hb := rBase_toNat A
  have hs := A.stackBound
  have hl := A.stackLow
  have ha : State.addr (t.gpr .r12 + BitVec.ofNat 32 d) = off (rBase s₀) d := by
    rw [P.r12, VG.Arm.addr_add (by rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_arith),
      alloc_base A]
  refine wp_str (by unfold frameBytes at hd; omega_arith) ha
    ⟨_, by rw [P.wr]; exact List.mem_cons_self, Offset.contains_base _ hd (by unfold frameBytes at *; omega_arith)⟩
    fun u m => k u ⟨by rw [m.gpr]; exact P.r12, m.sp.trans P.sp, m.rd.trans P.rd, m.wr.trans P.wr,
      P.frame.trans (by
        rw [m.mem]
        exact (frame_store s₀ t.mem hd (t.gpr r)).mono fun x hx => by
          simp only [List.mem_singleton] at hx; subst hx; simp [rWrites])⟩ m.mem m.gpr

theorem entry_eq : entry = [.addSp .r12 0, .str .r4 .r12 0, .str .r5 .r12 4, .str .r6 .r12 8, .str .r7 .r12 12,
    .str .r8 .r12 16, .str .r9 .r12 20, .str .r10 .r12 24, .str .r11 .r12 28, .str .lr .r12 32,
    .mov .r11 (.reg .r12), st .r0 oOut, st .r1 oOutLen, st .r2 oUsedPtr, st .r3 oKey,
    .mov .r0 (.imm 0), st .r0 oUsed, .mov .r0 (.imm 8), st .r0 oAttempts] := rfl

/-- Save the callee-saved registers and the register arguments, and start the counts. -/
theorem entry_ok {s₀ : State} (A : RandomABI s₀) :
    WP isa (.block entry) (allocated frameBytes s₀) fun u => RReady s₀ u ∧ Saved s₀ u.mem ∧
      slot u.mem (rBase s₀) oUsed = 0 ∧ slot u.mem (rBase s₀) oAttempts = 8 ∧
      (∀ r, r ≠ .r0 → r ≠ .r11 → r ≠ .r12 → u.gpr r = s₀.gpr r) := by
  rw [entry_eq]
  refine VG.Proof.X25519.Arm.WP.cons (s' := (allocated frameBytes s₀).setReg .r12
    ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) (by simp [exec]) ?_
  have P₀ : PreR s₀ ((allocated frameBytes s₀).setReg .r12 ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)) :=
    ⟨by simp [State.setReg, allocated], rfl, rfl, by
      show ⟨State.addr (s₀.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ :: s₀.wr = _; rw [alloc_base A],
      Frame.refl _ _⟩
  have g₀ : ∀ r, r ≠ .r12 → ((allocated frameBytes s₀).setReg .r12
      ((allocated frameBytes s₀).sp + BitVec.ofNat 32 0)).gpr r = s₀.gpr r := fun r h => by
    simp [State.setReg, allocated, h]
  refine wp_strP A P₀ (by decide) fun t₁ P₁ m₁ g₁ => wp_strP A P₁ (by decide) fun t₂ P₂ m₂ g₂ =>
    wp_strP A P₂ (by decide) fun t₃ P₃ m₃ g₃ => wp_strP A P₃ (by decide) fun t₄ P₄ m₄ g₄ =>
    wp_strP A P₄ (by decide) fun t₅ P₅ m₅ g₅ => wp_strP A P₅ (by decide) fun t₆ P₆ m₆ g₆ =>
    wp_strP A P₆ (by decide) fun t₇ P₇ m₇ g₇ => wp_strP A P₇ (by decide) fun t₈ P₈ m₈ g₈ =>
    wp_strP A P₈ (by decide) fun t₉ P₉ m₉ g₉ => wp_mov (op2_reg _ _) fun t₁₀ u₁₀ => ?_
  have gg : ∀ r, r ≠ .r12 → t₉.gpr r = s₀.gpr r := fun r h => by
    rw [g₉, g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁]; exact g₀ r h
  have nw : (rBase s₀).toNat + frameBytes + 36 ≤ 2 ^ 32 := by
    rw [rBase_toNat A]; have := A.stackBound; have := A.stackLow; unfold frameBytes; omega_arith
  have h₁₀ : RReady s₀ t₁₀ :=
    ⟨⟨by rw [u₁₀.gpr, P₉.r12, alloc_base A], by rw [u₁₀.wr, P₉.wr]; exact List.mem_cons_self,
      by rw [u₁₀.rd, P₉.rd, A.rd, rBase_args A]; simp, nw⟩,
      u₁₀.sp.trans P₉.sp, u₁₀.rd.trans P₉.rd, u₁₀.wr.trans P₉.wr, by rw [u₁₀.mem]; exact P₉.frame⟩
  refine wp_st h₁₀ (by decide) fun t₁₁ m₁₁ h₁₁ => wp_st h₁₁ (by decide) fun t₁₂ m₁₂ h₁₂ =>
    wp_st h₁₂ (by decide) fun t₁₃ m₁₃ h₁₃ => wp_st h₁₃ (by decide) fun t₁₄ m₁₄ h₁₄ =>
    wp_mov (op2_imm (by decide)) fun t₁₅ u₁₅ => wp_st (h₁₄.upd u₁₅) (by decide) fun t₁₆ m₁₆ h₁₆ =>
    wp_mov (op2_imm (by decide)) fun t₁₇ u₁₇ => wp_st (h₁₆.upd u₁₇) (by decide) fun t₁₈ m₁₈ h₁₈ => WP.block_nil ?_
  have e₁₄ : ∀ r, r ≠ .r11 → r ≠ .r12 → t₁₄.gpr r = s₀.gpr r := fun r h h' => by
    rw [m₁₄.gpr, m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ h]; exact gg r h'
  have hm : t₁₈.mem = ((((((((((((((s₀.mem.writeW (off (rBase s₀) 0) (s₀.gpr .r4)).writeW
      (off (rBase s₀) 4) (s₀.gpr .r5)).writeW (off (rBase s₀) 8) (s₀.gpr .r6)).writeW
      (off (rBase s₀) 12) (s₀.gpr .r7)).writeW (off (rBase s₀) 16) (s₀.gpr .r8)).writeW
      (off (rBase s₀) 20) (s₀.gpr .r9)).writeW (off (rBase s₀) 24) (s₀.gpr .r10)).writeW
      (off (rBase s₀) 28) (s₀.gpr .r11)).writeW (off (rBase s₀) 32) (s₀.gpr .lr)).writeW
      (off (rBase s₀) oOut) (s₀.gpr .r0)).writeW (off (rBase s₀) oOutLen) (s₀.gpr .r1)).writeW
      (off (rBase s₀) oUsedPtr) (s₀.gpr .r2)).writeW (off (rBase s₀) oKey) (s₀.gpr .r3)).writeW
      (off (rBase s₀) oUsed) (0 : BitVec 32)).writeW (off (rBase s₀) oAttempts) (8 : BitVec 32) := by
    have v0 : t₁₀.gpr .r0 = s₀.gpr .r0 := by rw [u₁₀.other _ (by decide)]; exact gg _ (by decide)
    have v1 : t₁₁.gpr .r1 = s₀.gpr .r1 := by rw [m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    have v2 : t₁₂.gpr .r2 = s₀.gpr .r2 := by
      rw [m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    have v3 : t₁₃.gpr .r3 = s₀.gpr .r3 := by
      rw [m₁₃.gpr, m₁₂.gpr, m₁₁.gpr, u₁₀.other _ (by decide)]; exact gg _ (by decide)
    rw [m₁₈.mem, u₁₇.gpr, u₁₇.mem, m₁₆.mem, u₁₅.gpr, u₁₅.mem, m₁₄.mem, m₁₃.mem, m₁₂.mem, m₁₁.mem, v0, v1, v2, v3,
      u₁₀.mem, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁]
    simp only [g₈, g₇, g₆, g₅, g₄, g₃, g₂, g₁, g₀ _ (by decide : Reg.r4 ≠ .r12), g₀ _ (by decide : Reg.r5 ≠ .r12),
      g₀ _ (by decide : Reg.r6 ≠ .r12), g₀ _ (by decide : Reg.r7 ≠ .r12), g₀ _ (by decide : Reg.r8 ≠ .r12),
      g₀ _ (by decide : Reg.r9 ≠ .r12), g₀ _ (by decide : Reg.r10 ≠ .r12), g₀ _ (by decide : Reg.r11 ≠ .r12),
      g₀ _ (by decide : Reg.lr ≠ .r12)]
    rfl
  refine ⟨h₁₈, ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, fun r h0 h11 h12 => ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 := by omega_arith
    all_goals (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; rfl)
  all_goals first
    | (rw [hm]; simp (disch := decide) only [slot_write_self, slot_write_ne]; done)
    | skip
  rw [m₁₈.gpr, u₁₇.other _ h0, m₁₆.gpr, u₁₅.other _ h0]; exact e₁₄ r h11 h12

theorem Att.mem {s₀ t u : State} (A : RandomABI s₀) {used f : Nat} (T : Att s₀ used f t) (hr : RReady s₀ u)
    (hm : u.mem = t.mem) : Att s₀ used f u :=
  let ⟨d, S⟩ := T.smp
  ⟨⟨d, S.mem A hr hm⟩, by rw [hm]; exact T.attempts, by rw [hm]; exact T.saved, T.rel⟩

theorem Done.mem {s₀ t u : State} (A : RandomABI s₀) (D : Done s₀ t) (hr : RReady s₀ u) (hm : u.mem = t.mem) :
    Done s₀ u :=
  let ⟨d, S⟩ := D.smp
  ⟨⟨d, S.mem A hr hm⟩, by rw [hm]; exact D.status, by rw [hm]; exact D.out, by rw [hm]; exact D.saved⟩

theorem body_ok (name : String) {s₀ : State} (A : RandomABI s₀) :
    WP isa (body name (Entry.operation true)) (allocated frameBytes s₀) fun u => Finished s₀ u := by
  have hql := rQBytes_le A
  have hfit := rWidth_le s₀
  have hR := rResult_status_le A
  unfold body
  refine WP.seq (WP.mono (entry_ok A) fun t₁ ⟨h₁, sv₁, us₁, at₁, _⟩ => ?_)
  refine WP.seq (WP.mono (prepare_ok A h₁ sv₁.2.2.2.2) fun t₂ ⟨ax₂, P₂, h₂, o₂, _⟩ => ?_)
  have lo₂ : ∀ d, d + 4 ≤ oQ → slot t₂.mem (rBase s₀) d = slot t₁.mem (rBase s₀) d := fun d hd =>
    outs_low o₂ (by decide) hd (by unfold oQ at hd; omega_arith)
  refine WP.seq (wp_cmp0 fun t₃ f₃ z₃ => WP.block_nil ?_)
  have h₃ := h₂.fupd f₃
  have m₃ : t₃.mem = t₂.mem := f₃.mem
  have sv₃ : Saved s₀ t₃.mem := by rw [m₃]; exact sv₁.of_outs o₂ (by decide)
  have us₃ : slot t₃.mem (rBase s₀) oUsed = 0 := by rw [m₃, lo₂ _ (by decide)]; exact us₁
  have at₃ : slot t₃.mem (rBase s₀) oAttempts = 8 := by rw [m₃, lo₂ _ (by decide)]; exact at₁
  rw [ax₂] at z₃
  suffices H : WP isa (.ite .eq (.block [st .r0 oStatus])
      (.loop (.seq (attempt name (Entry.operation true)) (.block [ld .r0 oStatus, .cmp .r0 (.imm 4)])) .eq))
      t₃ (RFin s₀) from WP.seq (WP.mono H fun u hu => rfinish_ok A hu hR (rResult_signature A))
  by_cases hq : 1 < rq s₀
  · simp only [hq, ↓reduceIte] at z₃
    have P := P₂ hq
    refine WP.ite false (by rw [eval_eq, z₃]; rfl) (fun e => Bool.noConfusion e) (fun _ => ?_)
    have T₀ : Att s₀ 0 8 t₃ := by
      refine ⟨⟨(slot t₃.mem (rBase s₀) oDraws).toNat, ⟨h₃, by rw [m₃]; exact P.q, by rw [m₃]; exact P.width,
        by rw [m₃]; exact P.mask, us₃, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq],
        fun i hi => by rw [m₃]; exact P.nonce i (by omega_arith), Nat.zero_le _⟩⟩, at₃, sv₃, ?_⟩
      have e : VG.Proof.Dsa.randomSignRemaining (rInput s₀) 0 8 = rResult s₀ := by
        rw [rResult_loop A]; rfl
      exact ⟨by rw [e], by rw [e], by rw [e]⟩
    refine WP.loop (M := isa) (fun (n : Nat) (u : State) => ∃ used, 1 ≤ n ∧ n ≤ 8 ∧ Att s₀ used n u)
      (fun n u hu => ?_) 8 t₃ ⟨0, by decide, by decide, T₀⟩
    obtain ⟨used, hn1, hn8, T⟩ := hu
    obtain ⟨f, rfl⟩ : ∃ f, n = f + 1 := ⟨n - 1, by omega_arith⟩
    refine WP.seq (WP.mono (attempt_ok name A T hn8 hq) fun v hv => ?_)
    have hrv : RReady s₀ v := by
      rcases hv with ⟨_, _, T', _⟩ | ⟨_, D, _⟩
      · obtain ⟨_, S⟩ := T'.smp; exact S.ready
      · obtain ⟨_, S⟩ := D.smp; exact S.ready
    refine wp_ld hrv (by decide) fun v₁ uv₁ => wp_cmp (op2_imm (by decide)) fun v₂ fv₂ zv₂ => WP.block_nil ?_
    have hv₂ := (hrv.upd uv₁).fupd fv₂
    have mv₂ : v₂.mem = v.mem := by rw [fv₂.mem, uv₁.mem]
    rw [uv₁.gpr] at zv₂
    rcases hv with ⟨st, h1f, T', _⟩ | ⟨st, D, _⟩
    · right
      refine ⟨by rw [eval_eq, zv₂, st]; rfl, f, by omega_arith, _, h1f, by omega_arith, T'.mem A hv₂ mv₂⟩
    · left
      refine ⟨?_, (D.mem A hv₂ mv₂).rfin⟩
      have hz : (slot v.mem (rBase s₀) oStatus - 4 == 0) = false := by
        rw [D.status, status_beq (by omega_arith), decide_eq_false (by omega_arith)]
      rw [eval_eq, zv₂, hz]
  · simp only [hq, ↓reduceIte] at z₃
    have hR' := rResult_small A hq
    refine WP.ite true (by rw [eval_eq, z₃]; rfl) (fun _ => ?_) (fun e => Bool.noConfusion e)
    refine wp_st h₃ (by decide) fun t₄ m₄ h₄ => WP.block_nil ?_
    have r0 : t₃.gpr .r0 = BitVec.ofNat 32 (rResult s₀).status := by
      rw [f₃.gpr, ax₂, hR']; simp only [hq, ↓reduceIte]; rfl
    rw [r0] at m₄
    refine ⟨h₄, ?_, by rw [m₄.mem, slot_write_self], fun e => by rw [hR'] at e; exact absurd e (by decide),
      sv₃.of_slots fun d hd _ => by rw [m₄.mem, slot_write_ne _ _ _ (by unfold oStatus; omega_arith) (by omega_arith)
        (by decide)]⟩
    rw [m₄.mem, slot_write_ne _ _ _ (by decide) (by decide) (by decide), us₃, hR']; rfl

end VG.Proof.Dsa.Arm
