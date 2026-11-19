module

public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Blake2.Arm.CompressB
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Spec.Argon2.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Blake2.Arm.CompressB
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
import VerifiedGarbage.Proof.Sha512.Arm.Rounds
import VerifiedGarbage.Proof.Argon2.Initial
meta import VerifiedGarbage.Proof.Argon2.Arm.HPrime.Finish
meta import VerifiedGarbage.Proof.Sha512.Arm.Rounds
meta import VerifiedGarbage.Proof.Argon2.Initial
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Argon2.Arm.HPrime.OutputCT`, which this module and modules that import it used -/

section

/-! ### `Argon2.Arm.HPrime.CallsCT`, which this module and modules that import it used -/

section

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

@[expose] public section

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
  have hn₁ : 4 * upd4.length ≤ s₁.sp.toNat := by rw [c₁.sp]; simp only [List.length_cons, List.length_nil]; omega_using [hlo]
  have hn₂ : 4 * upd4.length ≤ s₂.sp.toNat := by rw [c₂.sp]; simp only [List.length_cons, List.length_nil]; omega_using [hlo]
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
  have hn₁ : 4 * fin2.length ≤ s₁.sp.toNat := by rw [c₁.sp]; simp only [List.length_cons, List.length_nil]; omega_using [hlo]
  have hn₂ : 4 * fin2.length ≤ s₂.sp.toNat := by rw [c₂.sp]; simp only [List.length_cons, List.length_nil]; omega_using [hlo]
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
  · rw [addr_add (by omega_using [ho, hs]), show s₄.rd ++ s₄.wr = s.rd ++ s.wr by
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
    addr_add (by omega_using [ho, hs])
  have dTo : (B + BitVec.ofNat 32 offset).toNat = B.toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := offset) (by omega_using [ho, hs])]; omega_using [ho, hs]
  unfold absorbFixed
  refine RelCT.seq (rel_regs [.r4] (fun s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [h₁.1.r4, h₂.1.r4]) hc
    (fun s ⟨c, h⟩ => absorbFixed_blk c heo hes ho hs (by omega_using [ho, hlo]) h)
    (fun s ⟨c, h⟩ => absorbFixed_blk c heo hes ho hs (by omega_using [ho, hlo]) h))
    (update_rel (by rw [dTo]; omega_using [ho]) (by rw [eD]; exact Offset.disjoint_base _ hlo (by omega_using [ho]))
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
    (absorbFixed_ok c (offset := 768) (size := 64) (by decide) (by decide) (by have := c.fits; omega_using [this])
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
        (by have := c₁.fits; omega_using [this]) (by decide) (by decide) (c₁.stk_sub (by decide)) fixed_check_768).mono
      (fun s₁ s₂ ⟨⟨_, c₁⟩, ⟨_, c₂⟩⟩ => ⟨⟨c₁, c₁.cov (by decide)⟩, ⟨c₂, c₂.cov (by decide)⟩⟩)
      fun _ _ h => h) fx fx
  · exact rel_regs [.r4] (fun s₁ s₂ c₁ c₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [c₁.r4, c₂.r4]) ⟨_, by taint_decide⟩ fin fin

end VG.Proof.Argon2.Arm.HPrime

end

end

/-!
# Argon2 H′ on ARMv7: the output, in two runs

Two runs of H′ with the same public data (`Same`: the stack pointer and the
arguments) write their output through the same addresses (`copy_rel`,
`emit_rel`, `copyRemaining_rel`, from states with the same number of output
bytes written), take the same branches (the output length decides them) and
the same number of chain iterations: `finishOutput_rel`.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (copy copyLoop emitPrefix copyRemaining next cmpLeft chain extendDigest
  finishOutput)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

/-- The public data of two runs. -/
structure Same (s₀ s₀' : State) : Prop where
  sp : sp₀ s₀' = sp₀ s₀
  r0 : s₀'.gpr .r0 = s₀.gpr .r0
  r1 : s₀'.gpr .r1 = s₀.gpr .r1
  r2 : s₀'.gpr .r2 = s₀.gpr .r2
  r3 : s₀'.gpr .r3 = s₀.gpr .r3
  scr : scr s₀' = scr s₀

theorem Same.of_pub {s₀ s₀' : State} (h : hPrimeArm.pub s₀ s₀') : Same s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.symm⟩

theorem Same.ol_eq {s₀ s₀' : State} (q : Same s₀ s₀') : ol s₀' = ol s₀ := by
  show (s₀'.gpr .r3).toNat = (s₀.gpr .r3).toNat; rw [q.r3]

theorem Same.inl_eq {s₀ s₀' : State} (q : Same s₀ s₀') : inl s₀' = inl s₀ := by
  show (s₀'.gpr .r1).toNat = (s₀.gpr .r1).toNat; rw [q.r1]

/-- A register write outside `kept` keeps what the hash macros keep. -/
theorem keeps_upd {B SP : BitVec 32} {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hd : d ∉ kept) : Keeps B SP s t :=
  Keeps.same (fun r hr => u.other r fun h => hd (h ▸ hr)) u.sp u.mem u.rd u.wr

/-- The code taint checks from nothing public, in two runs. -/
theorem rel_none {P : State → State → Prop} {c : Prog isa}
    (hc : ∃ hc, (VG.Taint.check taint (Taint.ofRegs []) c hc).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun _ h => nomatch h) hc

theorem rel_nil {P Q : State → State → Prop} (h : ∀ x y, P x y → Q x y) : RelCT isa P (.block []) Q :=
  ((rel_none (P := P) ⟨_, by taint_decide⟩).wpDep (F := fun s t => t = s)
    fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, _, _, hp, e₁, e₂⟩ => e₁ ▸ e₂ ▸ h _ _ hp

/-- `eval .ne`, from `eval .eq`. -/
theorem ne_of_eq {t : State} {p : Prop} [Decidable p] (h : isa.eval .eq t = some (decide p)) :
    isa.eval .ne t = some (!decide p) := by
  have h' : VG.Arm.eval .eq t = _ := h
  rw [MdStream.Arm.eval_eq, Option.some.injEq] at h'
  show VG.Arm.eval .ne t = _
  rw [MdStream.Arm.eval_ne, h']

/-! ## `copy` -/

/-- What `copy` needs: the body, `k` bytes of output written, and `n` to copy. -/
def CopyIn (s₀ : State) (k n : Nat) (s : State) : Prop :=
  Body s₀ s ∧ s.gpr .r7 = op s₀ + BitVec.ofNat 32 k ∧ s.gpr .r10 = BitVec.ofNat 32 n

/-- The registers of the copy loop. -/
def CopyRegs (s₀ : State) (k n : Nat) (t : State) : Prop :=
  t.gpr .r9 = scr s₀ + 768 ∧ t.gpr .r7 = op s₀ + BitVec.ofNat 32 k ∧ t.gpr .r10 = BitVec.ofNat 32 n

theorem copy_blk {s₀ : State} {k n : Nat} {s : State} (h : CopyIn s₀ k n s) :
    WP isa (.block [.dp .add .r9 .r4 (.imm 768)]) s (CopyRegs s₀ k n) := by
  obtain ⟨b, hk, hn⟩ := h
  exact wp_add (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil
    ⟨by rw [u₁.gpr, b.r4], by rw [u₁.other _ (by decide), hk], by rw [u₁.other _ (by decide), hn]⟩

theorem copy_rel {s₀ s₀' : State} (q : Same s₀ s₀') {k n : Nat} :
    RelCT isa (fun t₁ t₂ => CopyIn s₀ k n t₁ ∧ CopyIn s₀' k n t₂) copy fun _ _ => True := by
  unfold copy
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => copy_blk h) (fun _ h => copy_blk h)) ?_
  exact RelCT.taint (A := taint) (Taint.ofRegs [.r9, .r7, .r10])
    (fun t₁ t₂ ⟨⟨a₁, b₁, c₁⟩, ⟨a₂, b₂, c₂⟩⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [a₁, a₂, q.scr]
      · rw [b₁, b₂]; exact congrArg (· + _) q.r2.symm
      · rw [c₁, c₂]) (by taint_decide)

/-- The body, with `L` output bytes written. -/
def OutAt (s₀ : State) (L : Nat) (s : State) : Prop :=
  Body s₀ s ∧ ∃ xs, Out s₀ s xs ∧ xs.length = L

theorem emit_blk {s₀ : State} {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .r10 (.imm 32)]) s (CopyIn s₀ L 32) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact wp_mov (op2_imm (by decide)) fun s₁ u₁ => WP.block_nil
    ⟨b.upd u₁ (by decide) (by decide) (by decide), by rw [u₁.other _ (by decide), o.ptr, hx], u₁.gpr⟩

theorem emit_rel {s₀ s₀' : State} (q : Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) emitPrefix fun _ _ => True := by
  unfold emitPrefix
  exact RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => emit_blk h) (fun _ h => emit_blk h))
    (RelCT.seq (copy_rel q) (rel_none ⟨_, by taint_decide⟩))

theorem rem_blk {s₀ : State} {L : Nat} {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .r10 (.reg .r8)]) s (CopyIn s₀ L (ol s₀ - L)) := by
  obtain ⟨b, xs, o, hx⟩ := h
  exact wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil
    ⟨b.upd u₁ (by decide) (by decide) (by decide), by rw [u₁.other _ (by decide), o.ptr, hx],
      by rw [u₁.gpr, o.left, hx]⟩

theorem copyRemaining_rel {s₀ s₀' : State} (q : Same s₀ s₀') {L : Nat} :
    RelCT isa (fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂) copyRemaining fun _ _ => True := by
  unfold copyRemaining
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => rem_blk h) (fun _ h => rem_blk h)) ?_
  rw [q.ol_eq]
  exact copy_rel q

/-! ## The chain -/

/-- `ChainInv`, for some digest `V` and `r11`. -/
def ChainAt (s₀ : State) (j : Nat) (s : State) : Prop :=
  ∃ (V : List Byte) (e : BitVec 32), V.length = 64 ∧ ChainInv s₀ e V j s

theorem ChainAt.outAt {s₀ : State} {j : Nat} {s : State} (h : ChainAt s₀ j s) :
    OutAt s₀ (32 + 32 * j) s :=
  let ⟨_, _, hV, i⟩ := h
  ⟨i.body, _, i.out, chainOut_length hV j⟩

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

include hp in
theorem OutAt.keeps {L : Nat} {s t : State} (h : OutAt s₀ L s) (k : Keeps (scr s₀) (sp₀ s₀) s t) :
    OutAt s₀ L t :=
  let ⟨b, xs, o, hx⟩ := h
  ⟨b.keeps hp k, xs, o.keeps hp k, hx⟩

include hp in
theorem next_out_ok {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) {s : State}
    (h : InitIn (scr s₀) (sp₀ s₀) n s ∧ OutAt s₀ L s) : WP isa next s (OutAt s₀ L) := by
  obtain ⟨⟨c, e⟩, o⟩ := h
  exact (next_ok c e hn₁ hn₂).mono fun t ⟨_, k⟩ => o.keeps hp k

include hp hp' q in
theorem next_out_rel {n L : Nat} (hn₁ : 1 ≤ n) (hn₂ : n ≤ 64) :
    RelCT isa (fun t₁ t₂ => (InitIn (scr s₀) (sp₀ s₀) n t₁ ∧ OutAt s₀ L t₁) ∧
      (InitIn (scr s₀) (sp₀ s₀) n t₂ ∧ OutAt s₀' L t₂)) next
      fun t₁ t₂ => OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ :=
  rel_wp ((next_rel hn₁ hn₂).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (fun _ h => next_out_ok hp hn₁ hn₂ h)
    (fun _ h => next_out_ok hp' hn₁ hn₂ ⟨by rw [q.scr, q.sp]; exact h.1, h.2⟩)

include hp in
/-- Setting `r1` keeps the body and the output. -/
theorem r1_blk {L n : Nat} (hn : encodable (BitVec.ofNat 32 n) = true) {s : State} (h : OutAt s₀ L s) :
    WP isa (.block [.mov .r1 (.imm (BitVec.ofNat 32 n))]) s fun t =>
      InitIn (scr s₀) (sp₀ s₀) n t ∧ OutAt s₀ L t := by
  refine wp_mov (op2_imm hn) fun s₁ u₁ => WP.block_nil ?_
  have o₁ := h.keeps hp (keeps_upd u₁ (by decide))
  exact ⟨⟨o₁.1.ctx hp, u₁.gpr⟩, o₁⟩

include hp hp' q in
/-- One iteration of the chain. -/
theorem body_rel {j : Nat} :
    RelCT isa (fun t₁ t₂ => ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂)
      (.seq (.block [.mov .r1 (.imm 64)]) (.seq next (.seq emitPrefix (.block cmpLeft))))
      fun _ _ => True := by
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => r1_blk (n := 64) hp (by decide) h.outAt)
    (fun _ h => (r1_blk (n := 64) hp' (by decide) h.outAt).mono fun _ h =>
      ⟨by rw [← q.scr, ← q.sp]; exact h.1, h.2⟩))
    (RelCT.seq (next_out_rel hp hp' q (by decide) (by decide))
      (RelCT.seq (emit_rel q) (rel_none ⟨_, by taint_decide⟩)))

/-- What the chain leaves: `j` iterations, and 33 to 64 bytes left. -/
def ChainDone (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ j, ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂ ∧ 33 ≤ ol s₀ - (32 + 32 * j) ∧
    ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

include hp hp' q in
theorem chain_rel :
    RelCT isa (fun t₁ t₂ => ∃ j, 65 ≤ ol s₀ - (32 + 32 * j) ∧ ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂)
      chain (ChainDone s₀ s₀') := by
  have ho := q.ol_eq
  refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, h65, h₁, h₂⟩ e₁ e₂ =>
    RelCT.loop (M := isa) (Q := ChainDone s₀ s₀')
      (fun m t₁ t₂ => ∃ j, m = ol s₀ - (32 + 32 * j) ∧ 65 ≤ m ∧ ChainAt s₀ j t₁ ∧ ChainAt s₀' j t₂)
      (fun m => ?_) _ s₁ s₂ t₁ t₂ s₁' s₂' ⟨j, rfl, h65, h₁, h₂⟩ e₁ e₂
  refine RelCT.of_pre fun _ _ ⟨j, hm, h65, _, _⟩ => ?_
  subst hm
  have it := (body_rel hp hp' q (j := j)).wp
    (F₁ := fun (t : State) => ChainAt s₀ (j + 1) t ∧
      isa.eval .eq t = some (decide (ol s₀ - (32 + 32 * (j + 1)) ≤ 64)))
    (F₂ := fun (t : State) => ChainAt s₀' (j + 1) t ∧
      isa.eval .eq t = some (decide (ol s₀' - (32 + 32 * (j + 1)) ≤ 64)))
    fun t₁ t₂ ⟨⟨V, e, hV, i₁⟩, ⟨V', e', hV', i₂⟩⟩ =>
      ⟨(iter_ok hp hV i₁ (by omega_arith) (by omega_arith)).mono fun _ h => ⟨⟨V, e, hV, h.1⟩, h.2⟩,
       (iter_ok hp' hV' i₂ (by omega_arith) (by omega_arith)).mono fun _ h => ⟨⟨V', e', hV', h.1⟩, h.2⟩⟩
  refine it.mono (fun t₁ t₂ ⟨j', hj, _, a₁, a₂⟩ => ?_) fun t₁ t₂ ⟨_, ⟨c₁, f₁⟩, ⟨c₂, f₂⟩⟩ => ?_
  · have : j' = j := by omega_arith
    subst this; exact ⟨a₁, a₂⟩
  · rw [ho] at f₂
    have n₁ := ne_of_eq f₁
    have n₂ := ne_of_eq f₂
    refine ⟨by rw [n₁, n₂], fun hf => ?_, fun ht => ?_⟩
    · rw [n₁] at hf
      have : ol s₀ - (32 + 32 * (j + 1)) ≤ 64 := by simpa using hf
      exact ⟨j + 1, c₁, c₂, by omega_arith, by omega_arith, by omega_arith⟩
    · rw [n₁] at ht
      have : ¬ ol s₀ - (32 + 32 * (j + 1)) ≤ 64 := by simpa using ht
      exact ⟨_, by omega_arith, j + 1, rfl, by omega_arith, c₁, c₂⟩

/-! ## Extending the digest -/

/-- The state `finishOutput` starts from. -/
def ExtIn (s₀ s : State) : Prop := Body s₀ s ∧ Out s₀ s []

include hp in
theorem ext_emit {s : State} (h : ExtIn s₀ s) (hol : 32 ≤ ol s₀) :
    WP isa emitPrefix s (ChainAt s₀ 0) := by
  obtain ⟨b, o⟩ := h
  refine (emit_ok hp b o (by simp only [List.length_nil]; omega_arith)).mono fun t ⟨bt, et, ot, dt⟩ =>
    ⟨digest s₀ s, s.gpr .r11, by simp [digest, bytesAt], bt, et, ?_, dt⟩
  rw [List.nil_append] at ot
  simpa [chainOut, chainPrefixes] using ot

include hp in
theorem ChainAt.keeps {j : Nat} {s t : State} (h : ChainAt s₀ j s)
    (k : Keeps (scr s₀) (sp₀ s₀) s t) (m : t.mem = s.mem) : ChainAt s₀ j t :=
  let ⟨V, e, hV, i⟩ := h
  ⟨V, e, hV, i.body.keeps hp k, (k.gpr _ (by decide)).trans i.r11, i.out.keeps hp k,
    by show bytesAt _ _ _ = _; rw [m]; exact i.digest⟩

include hp in
theorem chain_cmp {j : Nat} (hl : 32 + 32 * j < ol s₀) {s : State} (h : ChainAt s₀ j s) :
    WP isa (.block cmpLeft) s fun t => ChainAt s₀ j t ∧
      isa.eval .eq t = some (decide (ol s₀ - (32 + 32 * j) ≤ 64)) := by
  obtain ⟨V, e, hV, i⟩ := h
  refine (cmp_ok i.out (by rw [chainOut_length hV]; exact hl)).mono fun t ⟨cf, k, m⟩ =>
    ⟨ChainAt.keeps hp ⟨V, e, hV, i⟩ k m, ?_⟩
  rw [cf, chainOut_length hV]

include hp in
theorem left_blk {j : Nat} {s : State} (h : ChainAt s₀ j s) :
    WP isa (.block [.mov .r1 (.reg .r8)]) s fun t =>
      InitIn (scr s₀) (sp₀ s₀) (ol s₀ - (32 + 32 * j)) t ∧ OutAt s₀ (32 + 32 * j) t := by
  have o := h.outAt
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => WP.block_nil ?_
  have o₁ := o.keeps hp (keeps_upd u₁ (by decide))
  obtain ⟨_, xs, ox, hx⟩ := o
  exact ⟨⟨o₁.1.ctx hp, by rw [u₁.gpr, ox.left, hx]⟩, o₁⟩

/-- `L` bytes written, and at most 64 left. -/
def Last (s₀ s₀' : State) (t₁ t₂ : State) : Prop :=
  ∃ L, OutAt s₀ L t₁ ∧ OutAt s₀' L t₂ ∧ L < ol s₀ ∧ ol s₀ - L ≤ 64

include hp hp' q in
theorem last_rel :
    RelCT isa (ChainDone s₀ s₀') (.seq (.block [.mov .r1 (.reg .r8)]) next) (Last s₀ s₀') := by
  have ho := q.ol_eq
  refine RelCT.of_pre fun _ _ ⟨j, _, _, l₁, l₂, l₃⟩ => ?_
  refine (RelCT.seq (rel_regs [] (F₁ := ChainAt s₀ j) (F₂ := ChainAt s₀' j)
      (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => left_blk hp h)
      (fun _ h => (left_blk hp' h).mono fun _ h => ⟨by rw [← q.scr, ← q.sp, ← ho]; exact h.1, h.2⟩))
    (next_out_rel hp hp' q (n := ol s₀ - (32 + 32 * j)) (by omega_arith) l₂)).mono ?_ ?_
  · intro t₁ t₂ ⟨j', c₁, c₂, m₁, m₂, m₃⟩
    have : j' = j := by omega_arith
    subst this; exact ⟨c₁, c₂⟩
  · intro t₁ t₂ ⟨o₁, o₂⟩
    exact ⟨_, o₁, o₂, by omega_arith, by omega_arith⟩

include hp hp' q in
theorem extend_rel (hol : 65 ≤ ol s₀) :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) extendDigest (Last s₀ s₀') := by
  have ho := q.ol_eq
  have hol' : 65 ≤ ol s₀' := by rw [ho]; exact hol
  unfold extendDigest
  refine RelCT.seq (rel_wp ((emit_rel q (L := 0)).mono
      (fun _ _ ⟨⟨b₁, o₁⟩, ⟨b₂, o₂⟩⟩ => ⟨⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩⟩) fun _ _ h => h)
      (fun _ h => ext_emit hp h (by omega_arith)) (fun _ h => ext_emit hp' h (by omega_arith))) ?_
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => chain_cmp hp (by omega_arith) h) (fun _ h => chain_cmp hp' (by omega_arith) h)) ?_
  refine RelCT.seq (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, ho])
    (rel_nil fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, ht⟩ => ⟨0, c₁, c₂, by
      rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega_arith,
      by rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega_arith, by omega_arith⟩)
    ((chain_rel hp hp' q).mono (fun _ _ ⟨⟨⟨c₁, f₁⟩, ⟨c₂, _⟩⟩, hf⟩ =>
      ⟨0, by rw [f₁] at hf; have := of_decide_eq_false (Option.some.inj hf); omega_arith, c₁, c₂⟩)
      fun _ _ h => h))
    (last_rel hp hp' q)

include hp in
theorem ext_cmp {s : State} (h : ExtIn s₀ s) :
    WP isa (.block cmpLeft) s fun t => ExtIn s₀ t ∧ isa.eval .eq t = some (decide (ol s₀ ≤ 64)) := by
  obtain ⟨b, o⟩ := h
  refine (cmp_ok o (by have := hp.ol_pos; simp only [List.length_nil]; omega_arith)).mono
    fun t ⟨cf, k, _⟩ => ⟨⟨b.keeps hp k, o.keeps hp k⟩, ?_⟩
  rw [cf]; simp

include hp hp' q in
theorem finishOutput_rel :
    RelCT isa (fun t₁ t₂ => ExtIn s₀ t₁ ∧ ExtIn s₀' t₂) finishOutput fun _ _ => True := by
  have ho := q.ol_eq
  have hpos := hp.ol_pos
  unfold finishOutput
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => ext_cmp hp h) (fun _ h => ext_cmp hp' h)) ?_
  refine RelCT.seq (R := Last s₀ s₀') (RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, ho])
    (rel_nil fun _ _ ⟨⟨⟨⟨b₁, o₁⟩, f₁⟩, ⟨⟨b₂, o₂⟩, _⟩⟩, ht⟩ =>
      ⟨0, ⟨b₁, [], o₁, rfl⟩, ⟨b₂, [], o₂, rfl⟩, by omega_arith,
        by rw [f₁] at ht; have := of_decide_eq_true (Option.some.inj ht); omega_arith⟩)
    (RelCT.of_pre fun _ _ ⟨⟨⟨_, f₁⟩, _⟩, hf⟩ => (extend_rel hp hp' q (by
        rw [f₁] at hf; have := of_decide_eq_false (Option.some.inj hf); omega_arith)).mono
      (fun _ _ ⟨⟨⟨e₁, _⟩, ⟨e₂, _⟩⟩, _⟩ => ⟨e₁, e₂⟩) fun _ _ h => h)) ?_
  exact RelCT.mono (RelCT.exists_ fun L => (copyRemaining_rel q (L := L)).mono
    (fun _ _ h => ⟨h.1, h.2.1⟩) fun _ _ h => h) (fun _ _ ⟨L, h⟩ => ⟨L, h⟩) fun _ _ h => h

end

end VG.Proof.Argon2.Arm.HPrime

end

end

/-! ### `Argon2.Arm.HPrime.Correct`, which only this module used -/

section

/-!
# Argon2 H′ on ARMv7: correctness

`setup_ok` saves the caller's registers in `scratch`, keeps the input, the
output pointer and the bytes left in registers and the length prefix in
`scratch`; `correct` composes it with `first_ok`, `finish_ok` and the
restore of the registers.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (setup restore first finishOutput saved baseSlot pfxOff)
open VG.Proof.MdStream.Arm (Upd Mupd wp_mov wp_str wp_ldrSp op2_reg)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem arg_in : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 0)) 4 := by
  refine ⟨argR s₀, by simp [hp.rd], ?_⟩
  simp [stackArgAddr, Region.Contains]

theorem scr_w {d : Nat} (hd : d + 4 ≤ 16384) : InRegions s₀.wr (P s₀ + BitVec.ofNat 64 d) 4 :=
  ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ hd (by omega_using [hd])⟩

/-- The state after `setup`. -/
theorem setup_ok : WP isa (.block setup) s₀ fun t => Body s₀ t ∧ Out s₀ t [] ∧
    Frame [scrR s₀] s₀.mem t.mem := by
  have hs := hp.scr_fits
  unfold setup
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) rfl (arg_in hp) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .r12 = scr s₀ := by rw [u₁.gpr]; rfl
  refine Spill.save_slots_ok (b := .r12) saveList_slots (by rw [e₁]; omega_using [hs])
    (fun d h₁ h₂ => by rw [e₁, u₁.wr]; exact scr_w hp (by omega_using [h₂])) ?_
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => ?_
  have r4₆ : s₆.gpr .r4 = scr s₀ := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
    exact e₁
  have w₆ : InRegions s₆.wr (State.addr (scr s₀) + BitVec.ofNat 64 pfxOff) 4 := by
    rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
    exact scr_w hp (by decide)
  refine wp_str (by decide) (by rw [r4₆]; exact scr_addr hp (by decide)) w₆ fun t u => WP.block_nil ?_
  -- Values.
  have g₆ : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s₆.gpr r = s₁.gpr r := fun r h4 h5 h6 h7 h8 => by
    rw [u₆.other _ h8, u₅.other _ h7, u₄.other _ h6, u₃.other _ h5, u₂.other _ h4]
  have m₆ : s₆.mem = Spill.saveMem s₁.mem (P s₀) s₁.gpr saveList := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, e₁]
  have gl : ∀ p ∈ saveList, s₁.gpr p.1 = s₀.gpr p.1 := fun p hpm => u₁.other _ (by
    simp only [saveList, saved, baseSlot, List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hv : (s₆.gpr .r3) = s₀.gpr .r3 := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide),
    u₁.other _ (by decide)]
  have mt : t.mem = (Spill.saveMem s₀.mem (P s₀) s₀.gpr saveList).writeW (P s₀ + BitVec.ofNat 64 pfxOff)
      (s₀.gpr .r3) := by
    rw [u.mem, m₆, hv, u₁.mem, Spill.saveMem_congr _ _ _ gl]
  have Ft : Frame [scrR s₀] s₀.mem t.mem := by
    rw [mt]
    exact (Spill.saveMem_frame_of _ _ (List.mem_singleton_self (scrR s₀)) _ _ fun p hpm => by
      have := saveList_slots.bound hpm
      exact Offset.contains_base _ (by omega_using [this]) (by omega_using [this])).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by decide) (by decide))
  have gt : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r12 → t.gpr r = s₀.gpr r :=
    fun r h4 h5 h6 h7 h8 h12 => by rw [u.gpr, g₆ r h4 h5 h6 h7 h8, u₁.other _ h12]
  refine ⟨⟨by rw [u.gpr, r4₆], ?_, ?_, ?_, ?_, ?_, Ft.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩,
      fun q hq => ?_, ?_⟩, ⟨?_, ?_, rfl, Nat.zero_le _⟩, Ft⟩
  · rw [u.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · have hb := saveList_slots.bound hq
    rw [mt, Mem.readW_writeW_sep (Offset.sep _ (by simp only [pfxOff]; omega_using [hb]) (by omega_using [hb]) (by decide)) (by decide)]
    exact Spill.saveMem_saved _ _ _ _ saveList_slots q hq
  · rw [← Proof.Blake2.wordBytes_readW (w := 32) _ _ (.inl rfl), mt,
      show P s₀ + 832 = P s₀ + BitVec.ofNat 64 pfxOff from rfl, Mem.readW_writeW_self32, Spec.Argon2.le32,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [u.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]; simp
  · rw [u.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]; simp [ol]

theorem correct : WP isa Impl.Argon2.Arm.HPrime.code s₀ fun t =>
    (∀ r ∈ preserved, t.gpr r = s₀.gpr r) ∧ t.sp = s₀.sp ∧ hPrimeArm.post s₀ t := by
  have hif := hp.in_fits
  have hs := hp.scr_fits
  unfold Impl.Argon2.Arm.HPrime.code
  refine WP.seq ((setup_ok hp).mono fun s₁ ⟨b₁, o₁, F₁⟩ => ?_)
  have hin : bytesAt s₁.mem (State.addr (inp s₀)) (inl s₀) = bytesAt s₀.mem (State.addr (inp s₀)) (inl s₀) :=
    Proof.Blake2.bytesAt_congr fun i hi => F₁.bytes (R := inR s₀) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega_using [hif]) hi
  refine WP.seq ((first_ok hp ⟨b₁, o₁, hin⟩).mono fun s₂ ⟨⟨b₂, o₂, _⟩, d₂⟩ => ?_)
  refine WP.seq ((finish_ok hp b₂ o₂ d₂).mono fun s₃ ⟨b₃, _, h₃⟩ => ?_)
  unfold restore
  rw [← List.append_nil (List.map _ _)]
  have sv : Spill.Saved s₃.mem (State.addr (s₃.gpr .r4)) s₀.gpr (saved ++ [(.r4, baseSlot)]) := by
    rw [b₃.r4]
    intro p hpm
    exact b₃.saved p (by
      simp only [List.mem_append, List.mem_singleton] at hpm
      rcases hpm with hpm | rfl
      · exact List.mem_cons_of_mem _ hpm
      · exact List.mem_cons_self)
  refine Spill.restoreBase_slots_ok (lo := 840) (hi := 876) (by decide) (by decide) (g := s₀.gpr)
    (by rw [b₃.r4]; omega_using [hs])
    (fun d h₁ h₂ => by rw [b₃.r4, b₃.rd, b₃.wr]; exact VG.Proof.Sha512.Arm.mem_rd (scr_w hp (by omega_using [h₂]))) sv
    fun t ht ho hm hrd hwr hsp => WP.block_nil ⟨fun r hr => ?_, hsp.trans b₃.sp, ?_⟩
  · exact Spill.restored_of ht (by decide) r hr
  · show bytesAt t.mem _ _ = _
    rw [hm]; exact h₃

end

end VG.Proof.Argon2.Arm.HPrime

end

end

/-!
# Argon2 H′ on ARMv7: verified

Constant time, by relating two runs with the same public data piece by piece
(`code_ct`): the setup is checked by the taint analysis from the stack
argument, `first` and `finishOutput` by their pieces; then `hPrime_verified`
against `hPrimeArm`.
-/

@[expose] public section

namespace VG.Proof.Argon2.Arm.HPrime

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Argon2.Arm.HPrime (setup restore first finishOutput chooseLength absorbInput finishInput
  absorbFixed)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_sub wp_cmp op2_reg op2_imm op2_lsr eval_eq)
open VG.Proof.Blake2.Arm.Stream (wp_adds wp_adc)

theorem Same.inp_eq {s₀ s₀' : State} (q : Same s₀ s₀') : inp s₀' = inp s₀ := q.r0

/-! ## The setup -/

theorem agreeS {s₁ s₂ : State} (hp₁ : Pre s₁) (hp₂ : Pre s₂) (q : Same s₁ s₂) :
    VG.Arm.Taint.Agree (argTaint [] 4) s₁ s₂ := by
  have e : ∀ s : State, (argR s) = ⟨State.addr s.sp, 4⟩ := fun s => by simp [argR, stackArgAddr]
  refine agree_argTaint (fun _ h => nomatch h) q.sp.symm ⟨hp₁.sp_hi, fun r hr => ?_⟩
    ⟨hp₂.sp_hi, fun r hr => ?_⟩ (argMem_of (j := 1) q.sp.symm (by have := hp₁.sp_hi; omega) fun i hi => ?_)
  · rw [← e]; rw [hp₁.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp₁.arg_out
    · exact hp₁.arg_scr
  · rw [← e]; rw [hp₂.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp₂.arg_out
    · exact hp₂.arg_scr
  · have : i = 0 := by omega_using [hi]
    subst this; exact q.scr.symm

theorem setup_F0 {s₀ : State} (hp : Pre s₀) : WP isa (.block setup) s₀ (F0 s₀) := by
  have hif := hp.in_fits
  refine (setup_ok hp).mono fun t ⟨b, o, f⟩ => ⟨b, o, ?_⟩
  exact Proof.Blake2.bytesAt_congr fun i hi => f.bytes (R := inR s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.in_scr) (by simp; omega_using [hif]) hi

theorem setup_rel {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀') :
    RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') (.block setup) fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂ :=
  ((RelCT.taint (A := taint) (argTaint [] 4) (fun _ _ ⟨e₁, e₂⟩ => by subst e₁ e₂; exact agreeS hp hp' q)
    (by taint_decide)).wp fun _ _ ⟨e₁, e₂⟩ =>
      ⟨by subst e₁; exact setup_F0 hp, by subst e₂; exact setup_F0 hp'⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## `first` -/

/-- The count `finishInput` passes to `finalize`, low and high words. -/
def cntLo (s₀ : State) : BitVec 32 := s₀.gpr .r1 + 4
def cntHi (s₀ : State) : BitVec 32 :=
  0 + 0 + (if decide (2 ^ 32 ≤ (s₀.gpr .r1).toNat + (4 : BitVec 32).toNat) then 1 else 0)

section
variable {s₀ s₀' : State} (hp : Pre s₀) (hp' : Pre s₀') (q : Same s₀ s₀')

include hp in
theorem choose_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.dp .sub .r1 .r8 (.imm 1), .mov .r1 (.shifted .r1 .lsr 6), .cmp .r1 (.imm 0)]) s
      fun t => F0 s₀ t ∧ isa.eval .eq t = some (decide (ol s₀ ≤ 64)) := by
  have hol := (s₀.gpr .r3).isLt
  have hpos := hp.ol_pos
  have l₀ : s.gpr .r8 = BitVec.ofNat 32 (ol s₀) := by rw [h.out.left]; rfl
  refine wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_lsr (by decide)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ⟨h.keeps hp ?_, ?_⟩
  · exact Keeps.same (fun r hr => by rw [f₃.gpr, u₂.other _ (kept_ne r hr).2.1, u₁.other _ (kept_ne r hr).2.1])
      (by rw [f₃.sp, u₂.sp, u₁.sp]) (by rw [f₃.mem, u₂.mem, u₁.mem]) (by rw [f₃.rd, u₂.rd, u₁.rd])
      (by rw [f₃.wr, u₂.wr, u₁.wr])
  · show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, u₂.gpr, u₁.gpr, l₀]; exact congrArg some (le64_beq hpos hol)

include hp hp' q in
theorem choose_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) chooseLength fun _ _ => True := by
  unfold chooseLength
  refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
    (fun _ h => choose_blk hp h) (fun _ h => choose_blk hp' h)) ?_
  exact RelCT.ite (fun t₁ t₂ ⟨⟨_, f₁⟩, ⟨_, f₂⟩⟩ => by rw [f₁, f₂, q.ol_eq])
    (rel_none ⟨_, by taint_decide⟩) (rel_none ⟨_, by taint_decide⟩)

include hp in
theorem absorbInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .r2 (.imm 4), .mov .r3 (.imm 0), .mov .r9 (.reg .r5), .mov .r10 (.reg .r6)]) s
      (UpdateIn (scr s₀) (sp₀ s₀) (inp s₀) (inl s₀) 4 0) := by
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have o₄ : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other _ h4, u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]
  have k₄ : Keeps (scr s₀) (sp₀ s₀) s s₄ := Keeps.same (fun r hr => o₄ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1 (kept_ne r hr).2.2.2.2.1 (kept_ne r hr).2.2.2.2.2.1)
    (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr])
  have F₄ := h.keeps hp k₄
  refine ⟨F₄.body.ctx hp, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.body.r5]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.body.r6]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [F₄.body.rd, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨inR s₀, by simp, 0, by simp, by simp⟩

include hp in
theorem finishInput_blk {s : State} (h : F0 s₀ s) :
    WP isa (.block [.mov .r3 (.imm 0), .adds .r2 .r6 (.imm 4), .adc .r3 .r3 (.imm 0)]) s
      (FinalizeIn (scr s₀) (sp₀ s₀) (cntLo s₀) (cntHi s₀)) := by
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_adds (op2_imm (by decide)) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => WP.block_nil ?_
  have o₃ : ∀ r, r ≠ .r2 → r ≠ .r3 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h2, u₂.other _ h1, u₁.other _ h2]
  have k₃ : Keeps (scr s₀) (sp₀ s₀) s s₃ := Keeps.same (fun r hr => o₃ r (kept_ne r hr).2.2.1
      (kept_ne r hr).2.2.2.1)
    (by rw [u₃.sp, u₂.sp, u₁.sp]) (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₃.wr, u₂.wr, u₁.wr])
  have r6 : s₁.gpr .r6 = s₀.gpr .r1 := by rw [u₁.other _ (by decide), h.body.r6]
  refine ⟨(h.keeps hp k₃).body.ctx hp, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, r6]; rfl
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, c₂, r6]; rfl

include q in
theorem cnt_eq : cntLo s₀' = cntLo s₀ ∧ cntHi s₀' = cntHi s₀ := by
  simp only [cntLo, cntHi, q.r1, and_self]

include hp hp' q in
theorem first_ct : RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) first fun _ _ => True := by
  have hs := hp.scr_fits
  have nE : nF s₀' = nF s₀ := by simp only [nF, q.ol_eq]
  unfold first
  refine RelCT.seq (rel_wp (choose_rel hp hp' q) (fun _ h => first_choose hp h)
    (fun _ h => first_choose hp' h)) ?_
  refine RelCT.seq (rel_wp ((init_rel (B := scr s₀) (SP := sp₀ s₀) (n := nF s₀) (nF_pos hp)
      (Nat.min_le_right _ _)).mono (fun _ _ ⟨⟨f₁, e₁⟩, ⟨f₂, e₂⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, e₁⟩, by
          have c := f₂.body.ctx hp'
          rw [q.scr, q.sp] at c
          exact ⟨c, by rw [e₂, nE]⟩⟩) fun _ _ h => h)
    (fun _ h => first_init hp h) (fun _ h => first_init hp' h)) ?_
  refine RelCT.seq (rel_wp ((absorbFixed_rel (B := scr s₀) (SP := sp₀ s₀) (offset := 832) (size := 4)
      (by decide) (by decide) (by omega_using [hs]) (by decide) (by decide)
      (hp.stk_scr.sub_right (Offset.sub_base _ (by decide))) fixed_check_832).mono
      (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
        ⟨⟨f₁.body.ctx hp, pfx_cov hp f₁.body⟩, by
          have c := f₂.body.ctx hp'
          have v := pfx_cov hp' f₂.body
          simp only [P] at v
          rw [q.scr, q.sp] at c; rw [q.scr] at v
          exact ⟨c, v⟩⟩) fun _ _ h => h)
    (fun _ h => first_fixed hp h) (fun _ h => first_fixed hp' h)) ?_
  refine RelCT.seq (rel_wp ?_ (fun _ h => first_input hp h) (fun _ h => first_input hp' h)) ?_
  · unfold absorbInput
    refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => absorbInput_blk hp h.1)
      (fun _ h => (absorbInput_blk hp' h.1).mono fun _ h => by
        rw [q.scr, q.sp, q.inp_eq, q.inl_eq] at h; exact h)) ?_
    exact update_rel hp.in_fits (hp.in_scr.sub_right (Region.sub_prefix (by decide))) hp.stk_in
  · unfold finishInput
    refine RelCT.seq (rel_regs [] (fun _ _ _ _ r hr => nomatch hr) ⟨_, by taint_decide⟩
      (fun _ h => finishInput_blk hp h.1)
      (fun _ h => (finishInput_blk hp' h.1).mono fun _ h => by
        rw [q.scr, q.sp, (cnt_eq q).1, (cnt_eq q).2] at h; exact h)) ?_
    exact finalize_rel

include hp hp' q in
theorem first_rel :
    RelCT isa (fun t₁ t₂ => F0 s₀ t₁ ∧ F0 s₀' t₂) first fun t₁ t₂ =>
      (F0 s₀ t₁ ∧ (digest s₀ t₁).take (nF s₀) = Spec.Argon2.H (nF s₀) (Spec.Argon2.le32 (ol s₀) ++ inB s₀)) ∧
      (F0 s₀' t₂ ∧ (digest s₀' t₂).take (nF s₀') =
        Spec.Argon2.H (nF s₀') (Spec.Argon2.le32 (ol s₀') ++ inB s₀')) :=
  rel_wp (first_ct hp hp' q) (fun _ h => first_ok hp h) (fun _ h => first_ok hp' h)

end

/-! ## Constant time -/

theorem code_ct : ConstantTime isa hPrimeArm.pre hPrimeArm.pub Impl.Argon2.Arm.HPrime.code := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    fun s₀ s₀' t₁ t₂ r₁ r₂ ⟨h₀, h₀', hq⟩ e₁ e₂ => ?_
  have hp := pre_of s₀ h₀
  have hp' := pre_of s₀' h₀'
  have q := Same.of_pub hq
  suffices h : RelCT isa (fun t₁ t₂ => t₁ = s₀ ∧ t₂ = s₀') Impl.Argon2.Arm.HPrime.code fun _ _ => True from
    h s₀ s₀' t₁ t₂ r₁ r₂ ⟨rfl, rfl⟩ e₁ e₂
  unfold Impl.Argon2.Arm.HPrime.code
  refine RelCT.seq (setup_rel hp hp' q) (RelCT.seq (first_rel hp hp' q)
    (RelCT.seq (R := fun t₁ t₂ => Body s₀ t₁ ∧ Body s₀' t₂) ?_ ?_))
  · exact rel_wp ((finishOutput_rel hp hp' q).mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ =>
      ⟨⟨f₁.body, f₁.out⟩, ⟨f₂.body, f₂.out⟩⟩) fun _ _ h => h)
      (fun _ ⟨f, d⟩ => (finish_ok hp f.body f.out d).mono fun _ h => h.1)
      (fun _ ⟨f, d⟩ => (finish_ok hp' f.body f.out d).mono fun _ h => h.1)
  · exact RelCT.taint (A := taint) (Taint.ofRegs [.r4]) (fun _ _ ⟨b₁, b₂⟩ => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [b₁.r4, b₂.r4, q.scr]) (by taint_decide)

/-! ## A state satisfying the precondition -/

/-- `input` at `0x1000` (one byte), `out` at `0x2000` (one byte), `scratch`
at `0x10000`, its address the stack argument at `0x5000`. -/
def hSatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5002 then 1 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x2000, 1⟩, ⟨0x10000, 16384⟩]

theorem hSat_pre : hPrimeArm.pre hSatState := by
  have e : stackArg hSatState 0 = 0x10000 := by decide
  have e2 : stackArgAddr hSatState 0 = 0x5000 := by decide
  simp only [hPrimeArm, e, e2]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide,
    by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem hPrime_verified : Verified Arm.target Impl.Argon2.Arm.HPrime.code hPrimeArm := by
  refine ⟨fun s hs => ?_, code_ct, ⟨hSatState, hSat_pre⟩⟩
  obtain ⟨t, s', he, h₁, h₂, h₃⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩

end VG.Proof.Argon2.Arm.HPrime
