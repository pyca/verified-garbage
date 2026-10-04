import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Hash
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# Argon2 H′ on ARMv7: the calls, in two runs

The macros calling the BLAKE2b functions leak the same trace in two runs that
pass them the same arguments (`init_rel`, `update_rel`, `finalize_rel`, and
`absorbFixed_rel` and `next_rel` built on them): the instructions before
each call are checked by the taint analysis, and the call (in the frame of
its stack arguments) is related by the callee's constant time
(`RelCT.call`, `frameCall_rel`), from the callee's precondition in both runs
(`init_pre`, `update_pre`, `finalize_pre`).
-/

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Arm.FrameStack
open VG.Impl.Argon2.Arm.HPrime (init update finalize absorbFixed next)
open VG.Proof.Blake2 (initArm updateArm finalizeArm)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)

/-! ## Two runs -/

/-- Two runs, each described by `WP`, of code the taint analysis proves
constant time from the registers `rs` public. -/
theorem rel_regs {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa} (rs : List Reg)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ :=
  rel_agree (Taint.ofRegs rs) (fun s₁ s₂ h₁ h₂ => Taint.agree_ofRegs (hag s₁ s₂ h₁ h₂)) hc hw₁ hw₂

/-- A relation proved from facts of the related states. -/
theorem RelCT.of_pre {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa P c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

/-! ## `init` -/

/-- What `init` needs: the state's context, and the digest length in `r1`. -/
def InitIn (B SP : BitVec 32) (n : Nat) (s : State) : Prop :=
  Ctx B SP s ∧ s.gpr .r1 = BitVec.ofNat 32 n

theorem init_blk {B SP : BitVec 32} {n : Nat} {s : State} (h : InitIn B SP n s) :
    WP isa (.block [.mov .r0 (.reg .r4), .mov .r2 (.reg .r4), .mov .r3 (.imm 0)]) s fun t =>
      Ctx B SP t ∧ t.gpr .r1 = BitVec.ofNat 32 n ∧ t.gpr .r0 = B ∧ t.gpr .r2 = B ∧ t.gpr .r3 = 0 :=
  wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil
      ⟨h.1.of_regs (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
        (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.wr, u₂.wr, u₁.wr]),
       by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.2],
       by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.1.r4],
       by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.1.r4], u₃.gpr⟩

theorem init_rel {B SP : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => InitIn B SP n s₁ ∧ InitIn B SP n s₂) init fun _ _ => True := by
  unfold Impl.Argon2.Arm.HPrime.init
  refine RelCT.seq (rel_regs [.r4, .r1] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.1.r4, h₂.1.r4]
      · rw [h₁.2, h₂.2]) ⟨_, by taint_decide⟩ (fun _ h => init_blk h) (fun _ h => init_blk h)) ?_
  refine RelCT.call init_correct init_ct (initRd B) (initWr B)
    fun s₁ s₂ ⟨⟨c₁, e₁, a₁, x₁, y₁⟩, ⟨c₂, e₂, a₂, x₂, y₂⟩⟩ => ?_
  obtain ⟨p₁, v₁, w₁⟩ := init_pre c₁ e₁ hn₁ hn₂ a₁ x₁ y₁
  obtain ⟨p₂, v₂, w₂⟩ := init_pre c₂ e₂ hn₁ hn₂ a₂ x₂ y₂
  refine ⟨p₁, p₂, ?_, v₁, w₁, v₂, w₂⟩
  simp only [initArm, State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce0, Proof.Blake2.Arm.Stream.ce1,
    Proof.Blake2.Arm.Stream.ce2, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), a₁, a₂, e₁, e₂,
    x₁, x₂, y₁, y₂, and_self]

/-! ## `update` -/

/-- What `update` needs: the state's context, the data at `D`, of `L` bytes,
and the count in `r3:r2`. -/
def UpdateIn (B SP D : BitVec 32) (L : Nat) (lo hi : BitVec 32) (s : State) : Prop :=
  Ctx B SP s ∧ s.gpr .r9 = D ∧ (s.gpr .r10).toNat = L ∧ s.gpr .r2 = lo ∧ s.gpr .r3 = hi ∧
    Covers [⟨State.addr D, L⟩] (s.rd ++ s.wr)

theorem update_blk {B SP D : BitVec 32} {L : Nat} {lo hi : BitVec 32} {s : State}
    (h : UpdateIn B SP D L lo hi s) :
    WP isa (.block [.mov .r0 (.reg .r4), .dp .add .r12 .r4 (.imm 192)]) s fun t =>
      UpdateIn B SP D L lo hi t ∧ t.gpr .r0 = B ∧ t.gpr .r12 = B + 192 := by
  obtain ⟨c, e1, e2, e3, e4, cv⟩ := h
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have o : ∀ r, r ≠ .r0 → r ≠ .r12 → s₂.gpr r = s.gpr r := fun r h0 h12 => by
    rw [u₂.other _ h12, u₁.other _ h0]
  refine ⟨⟨c.of_regs (o _ (by decide) (by decide)) (by rw [u₂.sp, u₁.sp]) (by rw [u₂.wr, u₁.wr]),
    by rw [o _ (by decide) (by decide), e1], by rw [o _ (by decide) (by decide), e2],
    by rw [o _ (by decide) (by decide), e3], by rw [o _ (by decide) (by decide), e4],
    by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact cv⟩, ?_, ?_⟩
  · rw [u₂.other _ (by decide), u₁.gpr, c.r4]
  · rw [u₂.gpr, u₁.other _ (by decide), c.r4]

theorem update_rel {B SP D : BitVec 32} {L : Nat} {lo hi : BitVec 32} (hDfit : D.toNat + L ≤ 2 ^ 32)
    (hDs : Region.Disjoint ⟨State.addr D, L⟩ ⟨State.addr B, 768⟩)
    (hDk : (stkR SP 32).Disjoint ⟨State.addr D, L⟩) :
    RelCT isa (fun s₁ s₂ => UpdateIn B SP D L lo hi s₁ ∧ UpdateIn B SP D L lo hi s₂) update
      fun _ _ => True := by
  unfold update
  refine RelCT.seq (rel_regs [.r4] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.r4, h₂.1.r4]) ⟨_, by taint_decide⟩ (fun _ h => update_blk h) (fun _ h => update_blk h)) ?_
  refine frameCall_rel (rs := upd4) (by decide) update_v.1 update_v.2.1 (updRd D L SP) (updWr B)
    fun s₁ s₂ ⟨⟨⟨c₁, d₁, l₁, x₁, y₁, v₁⟩, a₁, b₁⟩, ⟨⟨c₂, d₂, l₂, x₂, y₂, v₂⟩, a₂, b₂⟩⟩ => ?_
  obtain ⟨p₁, cv₁, cw₁⟩ := update_pre c₁ d₁ l₁ hDfit v₁ hDs hDk a₁ b₁
  obtain ⟨p₂, cv₂, cw₂⟩ := update_pre c₂ d₂ l₂ hDfit v₂ hDs hDk a₂ b₂
  have hlo := c₁.lo
  have hn₁ : 4 * upd4.length ≤ s₁.sp.toNat := by rw [c₁.sp]; simp only [List.length_cons, List.length_nil]; omega
  have hn₂ : 4 * upd4.length ≤ s₂.sp.toNat := by rw [c₂.sp]; simp only [List.length_cons, List.length_nil]; omega
  refine ⟨c₁.sp.trans c₂.sp.symm, p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, c₁.sp, c₂.sp]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a₁, a₂]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2, pushed_gpr, x₁, x₂]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      y₁, y₂]
  · exact pushed_arg_eq hn₁ hn₂ (i := 0) (by decide) (by show s₁.gpr .r9 = s₂.gpr .r9; rw [d₁, d₂])
  · exact pushed_arg_eq hn₁ hn₂ (i := 1) (by decide)
      (by show s₁.gpr .r10 = s₂.gpr .r10; exact BitVec.eq_of_toNat_eq (l₁.trans l₂.symm))
  · exact pushed_arg_eq hn₁ hn₂ (i := 2) (by decide) (by show s₁.gpr .r12 = s₂.gpr .r12; rw [b₁, b₂])

/-! ## `finalize` -/

/-- What `finalize` needs: the state's context and the count in `r3:r2`. -/
def FinalizeIn (B SP lo hi : BitVec 32) (s : State) : Prop :=
  Ctx B SP s ∧ s.gpr .r2 = lo ∧ s.gpr .r3 = hi

theorem finalize_blk {B SP lo hi : BitVec 32} {s : State} (h : FinalizeIn B SP lo hi s) :
    WP isa (.block [.mov .r0 (.reg .r4), .dp .add .r1 .r4 (.imm 768), .dp .add .r12 .r4 (.imm 192)]) s
      fun t => FinalizeIn B SP lo hi t ∧ t.gpr .r0 = B ∧ t.gpr .r1 = B + 768 ∧ t.gpr .r12 = B + 192 := by
  obtain ⟨c, e3, e4⟩ := h
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_add (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have o : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h0 h1 h12 => by
    rw [u₃.other _ h12, u₂.other _ h1, u₁.other _ h0]
  refine ⟨⟨c.of_regs (o _ (by decide) (by decide) (by decide)) (by rw [u₃.sp, u₂.sp, u₁.sp])
    (by rw [u₃.wr, u₂.wr, u₁.wr]), by rw [o _ (by decide) (by decide) (by decide), e3],
    by rw [o _ (by decide) (by decide) (by decide), e4]⟩, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, c.r4]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), c.r4]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.r4]

theorem finalize_rel {B SP lo hi : BitVec 32} :
    RelCT isa (fun s₁ s₂ => FinalizeIn B SP lo hi s₁ ∧ FinalizeIn B SP lo hi s₂) finalize
      fun _ _ => True := by
  unfold finalize
  refine RelCT.seq (rel_regs [.r4] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.r4, h₂.1.r4]) ⟨_, by taint_decide⟩ (fun _ h => finalize_blk h) (fun _ h => finalize_blk h)) ?_
  refine frameCall_rel (rs := fin2) (by decide) finalize_v.1 finalize_v.2.1 (finRd SP) (finWr B)
    fun s₁ s₂ ⟨⟨⟨c₁, x₁, y₁⟩, a₁, i₁, b₁⟩, ⟨⟨c₂, x₂, y₂⟩, a₂, i₂, b₂⟩⟩ => ?_
  obtain ⟨p₁, cv₁, cw₁⟩ := finalize_pre c₁ a₁ i₁ b₁
  obtain ⟨p₂, cv₂, cw₂⟩ := finalize_pre c₂ a₂ i₂ b₂
  have hlo := c₁.lo
  have hn₁ : 4 * fin2.length ≤ s₁.sp.toNat := by rw [c₁.sp]; simp only [List.length_cons, List.length_nil]; omega
  have hn₂ : 4 * fin2.length ≤ s₂.sp.toNat := by rw [c₂.sp]; simp only [List.length_cons, List.length_nil]; omega
  refine ⟨c₁.sp.trans c₂.sp.symm, p₁, p₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, cv₁, cw₁, cv₂, cw₂⟩
  · simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp, c₁.sp, c₂.sp]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce0, pushed_gpr, a₁, a₂]
  · simp only [State.withRegions_gpr, Proof.Blake2.Arm.Stream.ce2, pushed_gpr, x₁, x₂]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), pushed_gpr,
      y₁, y₂]
  · exact pushed_arg_eq hn₁ hn₂ (i := 0) (by decide) (by show s₁.gpr .r1 = s₂.gpr .r1; rw [i₁, i₂])
  · exact pushed_arg_eq hn₁ hn₂ (i := 1) (by decide) (by show s₁.gpr .r12 = s₂.gpr .r12; rw [b₁, b₂])

/-! ## Hashing a fixed buffer, and the digest -/

/-- The instructions before `absorbFixed`'s call of `update`. -/
theorem absorbFixed_blk {B SP : BitVec 32} {s : State} (c : Ctx B SP s) {offset size : Nat}
    (heo : encodable (BitVec.ofNat 32 offset) = true) (hes : encodable (BitVec.ofNat 32 size) = true)
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hs : 0 < size) (hlt : size < 2 ^ 32)
    (hcov : Covers [⟨State.addr B + BitVec.ofNat 64 offset, size⟩] s.wr) :
    WP isa (.block [.mov .r2 (.imm 0), .mov .r3 (.imm 0), .dp .add .r9 .r4 (.imm (BitVec.ofNat 32 offset)),
      .mov .r10 (.imm (BitVec.ofNat 32 size))]) s
      (UpdateIn B SP (B + BitVec.ofNat 32 offset) size 0 0) := by
  have hfit := c.fits
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm heo) fun s₃ u₃ => wp_mov (op2_imm hes) fun s₄ u₄ => WP.block_nil ?_
  have o : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have w : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine ⟨c.of_regs (o _ (by decide) (by decide) (by decide) (by decide)) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) w,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), c.r4]
  · rw [u₄.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [addr_add (by omega), show s₄.rd ++ s₄.wr = s.rd ++ s.wr by
      rw [w, u₄.rd, u₃.rd, u₂.rd, u₁.rd]]
    exact Covers.right hcov

/-- What `absorbFixed` needs: the context, and the buffer writable. -/
def FixedIn (B SP : BitVec 32) (offset size : Nat) (s : State) : Prop :=
  Ctx B SP s ∧ Covers [⟨State.addr B + BitVec.ofNat 64 offset, size⟩] s.wr

/-- The instructions before `absorbFixed`'s call, from `r4` public. -/
abbrev FixedCheck (offset size : Nat) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4]) (.block [.mov .r2 (.imm 0), .mov .r3 (.imm 0),
      .dp .add .r9 .r4 (.imm (BitVec.ofNat 32 offset)), .mov .r10 (.imm (BitVec.ofNat 32 size))]) hc).isSome = true

theorem fixed_check_768 : FixedCheck 768 64 := ⟨_, by taint_decide⟩
theorem fixed_check_832 : FixedCheck 832 4 := ⟨_, by taint_decide⟩

theorem absorbFixed_rel {B SP : BitVec 32} {offset size : Nat}
    (heo : encodable (BitVec.ofNat 32 offset) = true) (hes : encodable (BitVec.ofNat 32 size) = true)
    (ho : B.toNat + offset + size ≤ 2 ^ 32) (hlo : 768 ≤ offset) (hs : 0 < size)
    (hstk : (stkR SP 32).Disjoint ⟨State.addr B + BitVec.ofNat 64 offset, size⟩)
    (hc : FixedCheck offset size) :
    RelCT isa (fun s₁ s₂ => FixedIn B SP offset size s₁ ∧ FixedIn B SP offset size s₂)
      (absorbFixed offset size) fun _ _ => True := by
  have eD : State.addr (B + BitVec.ofNat 32 offset) = State.addr B + BitVec.ofNat 64 offset :=
    addr_add (by omega)
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega)]; omega
  unfold absorbFixed
  refine RelCT.seq (rel_regs [.r4] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.r4, h₂.1.r4]) hc
    (fun s ⟨c, h⟩ => absorbFixed_blk c heo hes ho hs (by omega) h)
    (fun s ⟨c, h⟩ => absorbFixed_blk c heo hes ho hs (by omega) h))
    (update_rel (by rw [dTo]; omega) (by rw [eD]; exact Offset.disjoint_base _ hlo (by omega))
      (by rw [eD]; exact hstk))

/-- `next`, from the context and the digest length in `r1`. -/
theorem next_rel {B SP : BitVec 32} {n : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun s₁ s₂ => InitIn B SP n s₁ ∧ InitIn B SP n s₂) next fun _ _ => True := by
  have st : ∀ s, InitIn B SP n s → WP isa init s fun t =>
      Repr b (Spec.Blake2.init b n 0) t.mem (State.addr B) [] ∧ Ctx B SP t := fun s ⟨c, e⟩ =>
    (init_ok c e hn₁ hn₂).mono fun t ⟨r, cs, _, wr, sp, _⟩ =>
      ⟨r, c.of_regs (cs _ (by decide) (by decide)) sp wr⟩
  have fx : ∀ s, Repr b (Spec.Blake2.init b n 0) s.mem (State.addr B) [] ∧ Ctx B SP s →
      WP isa (absorbFixed 768 64) s fun t => Ctx B SP t := fun s ⟨r, c⟩ =>
    (absorbFixed_ok c (offset := 768) (size := 64) (by decide) (by decide) (by have := c.fits; omega)
      (by decide) (by decide) (by decide) (c.cov (by decide)) (c.stk_sub (by decide)) r).mono
      fun t ⟨_, k⟩ => k.ctx c
  have fin : ∀ s, Ctx B SP s → WP isa (.block [.mov .r2 (.imm 64), .mov .r3 (.imm 0)]) s
      (FinalizeIn B SP 64 0) := fun s c =>
    wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => WP.block_nil
      ⟨c.of_regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.sp, u₁.sp])
        (by rw [u₂.wr, u₁.wr]),
       by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩
  unfold next
  refine RelCT.seq (rel_wp (init_rel hn₁ hn₂) st st)
    (RelCT.seq (R := fun s₁ s₂ => Ctx B SP s₁ ∧ Ctx B SP s₂) ?_
      (RelCT.seq (R := fun s₁ s₂ => FinalizeIn B SP 64 0 s₁ ∧ FinalizeIn B SP 64 0 s₂) ?_ finalize_rel))
  · refine rel_wp (RelCT.of_pre fun s₁ _ ⟨⟨_, c₁⟩, _⟩ =>
      (absorbFixed_rel (B := B) (SP := SP) (offset := 768) (size := 64) (by decide) (by decide)
        (by have := c₁.fits; omega) (by decide) (by decide) (c₁.stk_sub (by decide)) fixed_check_768).mono
      (fun s₁ s₂ ⟨⟨_, c₁⟩, ⟨_, c₂⟩⟩ => ⟨⟨c₁, c₁.cov (by decide)⟩, ⟨c₂, c₂.cov (by decide)⟩⟩)
      fun _ _ h => h) fx fx
  · exact rel_regs [.r4] (fun s₁ s₂ c₁ c₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [c₁.r4, c₂.r4]) ⟨_, by taint_decide⟩ fin fin

end VG.Proof.Argon2.Arm.HPrime
