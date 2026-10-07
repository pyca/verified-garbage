import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Fn
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT

/-!
# AES-GCM streaming encryption out of place, x86-64: constant time

Untrusted: everything here is checked by Lean. Two runs from states with the
same public arguments go through the same pieces: each load of `work` from
the stack gives both the same pointer (`rel_w`), after which the taint
analysis checks the piece from it; every other value a piece branches on or
addresses memory with is the same in both runs by what correctness says of
each (`step`): the lengths, the bytes done and the pointers; and the calls
get the same public arguments.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-! ## Two runs, piece by piece -/

/-- A piece the taint analysis checks from registers that agree, with what
correctness says of each run after it. -/
theorem step {P : State → State → Prop} {c : Prog isa} {F₁ F₂ G₁ G₂ : State → Prop} (rs : List Reg)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) (hF : ∀ s₁ s₂, P s₁ s₂ → F₁ s₁ ∧ F₂ s₂)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa P c fun s₁ s₂ => G₁ s₁ ∧ G₂ s₂ :=
  (rel_wp (rel_taint rs hag hc) hF hw₁ hw₂).mono (fun _ _ h => h) fun _ _ h => h.2

/-- A fact the related states imply, for the rest of the proof. -/
theorem RelCT.of_imp {P Q : State → State → Prop} {c : Prog isa} (A : Prop) (hA : ∀ s₁ s₂, P s₁ s₂ → A)
    (h : A → RelCT isa P c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h (hA _ _ hp) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂

theorem empty_check : ∃ hc, (taint.check (Taint.ofRegs []) (.block []) hc).isSome = true := ⟨_, by taint_decide⟩

/-- Nothing, in two runs. -/
theorem skip_rel {P Q : State → State → Prop} (h : ∀ s₁ s₂, P s₁ s₂ → Q s₁ s₂) :
    RelCT isa P (.block []) Q :=
  (rel_wp (P := P) (F₁ := fun _ => True) (F₂ := fun _ => True) (G₁ := fun _ => True) (G₂ := fun _ => True)
    (rel_taint [] (fun _ _ _ r hr => by cases hr) empty_check) (fun _ _ _ => ⟨trivial, trivial⟩)
    (fun _ _ => WP.block_nil trivial) (fun _ _ => WP.block_nil trivial)).wpDep
    (F := fun σ s' => s' = σ) (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) |>.mono (fun _ _ h => h)
    fun _ _ ⟨_, σ₁, σ₂, hσ, e₁, e₂⟩ => by rw [e₁, e₂]; exact h _ _ hσ

/-- `work`, loaded from the stack into `r11`. -/
theorem loadW_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 32))]) s fun s' =>
      s'.gpr .r11 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 ∧ ∀ r, r ≠ .r11 → s'.gpr r = s.gpr r := by
  refine WP.of_runBlock ⟨_, by xrun [hr], ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r a; simp [gpr_setReg, a]

theorem loadW_check : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .r11 (.mem (at_ .rsp 32))]) hc).isSome =
    true := ⟨_, by taint_decide⟩

/-- A block that first loads `work` into `r11`, from states that agree on
`rs` (with `rsp`) and hold the same pointer there, checked from `r11` and
`rs`. -/
theorem rel_w {P : State → State → Prop} {l₀ l : List Instr}
    (hl : l₀ = ([.mov .r11 (.mem (at_ .rsp 32))] : List Instr) ++ l) (rs : List Reg) (hrs : .rsp ∈ rs)
    (hag : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hS : ∀ s₁ s₂, P s₁ s₂ → s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 64 =
      s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 8)
    (hc : ∃ hc, (taint.check (Taint.ofRegs (.r11 :: rs)) (.block l) hc).isSome = true) :
    RelCT isa P (.block l₀) fun _ _ => True := by
  subst hl
  have l₁ := RelCT.wpDep (rel_taint (P := P) [.rsp] (fun s₁ s₂ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hag _ _ h _ hrs) loadW_check)
    (F := fun (σ s' : State) => s'.gpr .r11 = σ.mem.readW (σ.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      ∀ r, r ≠ .r11 → s'.gpr r = σ.gpr r)
    fun s₁ s₂ h => ⟨loadW_ok (hS _ _ h).2.1, loadW_ok (hS _ _ h).2.2⟩
  refine rel_block_split (RelCT.seq l₁ (rel_taint (.r11 :: rs) (fun s₁ s₂ h r hr => ?_) hc))
  obtain ⟨-, σ₁, σ₂, hσ, ⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ := h
  rcases List.mem_cons.mp hr with rfl | hr
  · rw [a₁, a₂]; exact (hS _ _ hσ).1
  · by_cases hx : r = .r11
    · subst hx; rw [a₁, a₂]; exact (hS _ _ hσ).1
    · rw [b₁ r hx, b₂ r hx]; exact hag _ _ hσ r hr

/-! ## What each run holds -/

/-- Before `blocks`: nothing done, `work` in `r11`, the text so far in `r8`. -/
def B0 (s : State) (st : State) : Prop := Mid s 0 st ∧ st.gpr .r11 = W s ∧ st.gpr .r8 = TL s

/-- Before the call of the whole blocks. -/
def C5 (s : State) (q : Nat) (st : State) : Prop :=
  Frame (wR s ++ [tR s]) s.mem st.mem ∧ Sem s 0 st.mem ∧ Kept s (16 * q) st.mem ∧ st.gpr .rsp = SP s ∧
    (∀ r ∈ calleeSaved, st.gpr r = s.gpr r) ∧ st.rd = s.rd ∧ st.wr = s.wr ∧
    st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s + BitVec.ofNat 64 48 ∧
    st.gpr .rcx = St s + BitVec.ofNat 64 16 ∧ st.gpr .r8 = Src s ∧ st.gpr .r9 = BitVec.ofNat 64 q ∧
    st.gpr .r10 = Dst s ∧ st.gpr .rax = W s + BitVec.ofNat 64 80

/-- Before the copy of the bytes left. -/
def R2 (s : State) (o : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .rsi = Src s + BitVec.ofNat 64 o ∧ st.gpr .rdi = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .rcx = BitVec.ofNat 64 (L s - o)

/-- Before the call of the bytes left. -/
def R4 (s : State) (o : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = TL s + BitVec.ofNat 64 o ∧ st.gpr .r9 = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .r10 = BitVec.ofNat 64 (L s - o)

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem notCs {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

omit hp in
theorem b1_wp {st : State} (h : B0 s st) :
    WP isa (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) st fun st' =>
      B0 s st' ∧ st'.gpr .rax = TL s ∧ st'.zf = some (TL s == 0) :=
  WP.mono hd1_ok fun _ ⟨ax, z, g, m, rd, wr⟩ =>
    ⟨⟨h.1.regs m (fun r hr => g r (notCs hr).1) rd wr, by rw [g _ (by decide), h.2.1],
      by rw [g _ (by decide), h.2.2]⟩, by rw [ax, h.2.2], by rw [z, h.2.2]⟩

omit hp in
theorem b2_wp {st : State} (h : B0 s st ∧ st.gpr .rax = TL s) :
    WP isa (.block [.alu .and .rax (imm 15)]) st fun st' =>
      B0 s st' ∧ st'.zf = some (BitVec.ofNat 64 ((TL s).toNat % 16) == 0) :=
  WP.mono (hd2_ok h.2) fun _ ⟨z, g, m, rd, wr⟩ =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1) rd wr, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, z⟩

theorem b3_wp {st : State} (h : B0 s st) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 wLen)), .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) st
      fun st' => B0 s st' ∧ st'.gpr .rax = BitVec.ofNat 64 (L s / 16) ∧ st'.zf = some (decide (L s / 16 = 0)) :=
  WP.mono (hd3_ok hp h.2.1 h.1.kept h.1.rd h.1.wr) fun _ ⟨ax, z, g, m, rd, wr⟩ =>
    ⟨⟨h.1.regs m (fun r hr => g r (notCs hr).1) rd wr, by rw [g _ (by decide), h.2.1],
      by rw [g _ (by decide), h.2.2]⟩, ax, z⟩

omit hp in
theorem b4_wp {st : State} (h : B0 s st ∧ st.gpr .rax = BitVec.ofNat 64 (L s / 16)) :
    WP isa (.block blocksLen) st fun st' => B0 s st' ∧ st'.gpr .r9 = BitVec.ofNat 64 (L s / 16) ∧
      st'.gpr .rax = BitVec.ofNat 64 (16 * (L s / 16)) ∧
      st'.cf = some (decide (2 ^ 64 ≤ (TL s).toNat + 16 * (L s / 16))) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have h16 : (BitVec.ofNat 64 (16 * (L s / 16))).toNat = 16 * (L s / 16) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  exact WP.mono (len_ok h.2 h.1.2.2) fun _ ⟨r9, ax, cf, g, m, rd, wr⟩ =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1 (notCs hr).2.2.2.2.2.2.1 (notCs hr).2.1) rd wr,
      by rw [g _ (by decide) (by decide) (by decide), h.1.2.1], by rw [g _ (by decide) (by decide) (by decide), h.1.2.2]⟩,
      r9, ax, by rw [cf, h16]⟩

theorem b5_wp {q : Nat} {st : State}
    (h : B0 s st ∧ st.gpr .r9 = BitVec.ofNat 64 q ∧ st.gpr .rax = BitVec.ofNat 64 (16 * q)) :
    WP isa (.block blocksArgs) st (C5 s q) :=
  WP.mono (blocksArgs_ok hp h.1.2.1 h.2.2 h.1.1.kept h.1.1.rd h.1.1.wr)
    fun _ ⟨di, si, dx, cx, r8, r10, ax, g, k, f, rd, wr⟩ =>
      ⟨h.1.1.frame.trans (frame_kR' f), h.1.1.sem.kR' hp f (Nat.zero_le _), k,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.rsp],
        fun r hr => by
          have n := notCs hr
          rw [g r n.2.2.2.2.1 n.2.2.2.1 n.2.2.1 n.2.1 n.2.2.2.2.2.1 n.2.2.2.2.2.2.2.1 n.1, h.1.1.saved r hr],
        rd.trans h.1.1.rd, wr.trans h.1.1.wr, di, si, dx, cx, r8,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.2.1],
        r10, ax⟩

theorem b6_wp (T : BlkToFn M) {q : Nat} (hq0 : q ≠ 0) (hq : 16 * q ≤ L s) (htl : (TL s).toNat + 16 * q < 2 ^ 64)
    (ht0 : TL s ≠ 0) (ht16 : (TL s).toNat % 16 = 0) {st : State} (h : C5 s q st) :
    WP isa (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st (Mid s (16 * q)) := by
  obtain ⟨f, sem, k, sp, cs, rd, wr, di, si, dx, cx, r8, r9, r10, ax⟩ := h
  exact WP.mono (blkCall_ok hp T hq sp rd wr f di si dx cx r8 r9 r10 ax) fun _ ⟨cs₆, rd₆, wr₆, f₆, o₁, o₂, o₃⟩ =>
    call_mid hp hq0 hq htl ht0 ht16 f sem k sp cs rd wr cs₆ rd₆ wr₆ f₆ o₁ o₂ o₃

theorem r1_wp {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]) st fun st' =>
      Mid s o st' ∧ st'.gpr .r11 = W s ∧ st'.gpr .rcx = BitVec.ofNat 64 (L s - o) ∧
      st'.gpr .rax = BitVec.ofNat 64 o ∧ st'.zf = some (decide (L s - o = 0)) :=
  WP.mono (restHead_ok hp h) fun _ ⟨r11, cx, ax, z, g, m, rd, wr⟩ =>
    ⟨h.regs m (fun r hr => g r (notCs hr).2.2.2.2.2.2.2.2 (notCs hr).2.1 (notCs hr).1) rd wr, r11, cx, ax, z⟩

theorem r2_wp {o : Nat} {st : State}
    (h : Mid s o st ∧ st.gpr .r11 = W s ∧ st.gpr .rcx = BitVec.ofNat 64 (L s - o) ∧ st.gpr .rax = BitVec.ofNat 64 o) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax), .mov .rdi (.mem (at_ .r11 wDst)),
      .alu .add .rdi (.reg .rax)]) st (R2 s o) :=
  WP.mono (restPtrs_ok hp h.1 h.2.1 h.2.2.2) fun _ ⟨si, di, g, m, rd, wr⟩ =>
    ⟨h.1.regs m (fun r hr => g r (notCs hr).2.2.2.1 (notCs hr).2.2.2.2.1) rd wr, si, di,
      by rw [g _ (by decide) (by decide), h.2.2.1]⟩

theorem r3_wp {o : Nat} (ho : o < L s) {st : State} (h : R2 s o st) : WP isa copyLoop st (Mid s o) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  obtain ⟨M₂, si, di, cx⟩ := h
  have ds := dq_sub (s := s) (Nat.le_of_lt ho)
  have ss : Region.Sub ⟨Src s + BitVec.ofNat 64 o, L s - o⟩ (srcR s) := Offset.sub_base _ (by omega)
  have cp : CopyPre st (Src s + BitVec.ofNat 64 o) (Dst s + BitVec.ofNat 64 o) (L s - o) :=
    ⟨si, di, cx, by omega, by omega,
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.rd, M₂.wr, hp.rd]; simp) (by omega) (by omega),
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.wr, hp.wr]; simp) (by omega) (by omega),
      (hp.r_d.sub_left ss).sub_right ds⟩
  exact WP.mono (copyLoopL_ok st cp) fun _ ⟨m₃, g₃, rd₃, wr₃⟩ =>
    M₂.copy hp ho (by rw [m₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _))
      (fun r hr => g₃ r (notCs hr).1 (notCs hr).2.2.2.2.2.2.2.1) rd₃ wr₃

theorem r4_wp {o : Nat} {st : State} (h : Mid s o st) : WP isa (.block restArgs) st (R4 s o) :=
  WP.mono (restArgs_ok hp h) fun _ ⟨di, si, dx, cx, r8, r9, r10, cs, m, rd, wr⟩ =>
    ⟨h.regs m cs rd wr, di, si, dx, cx, r8, r9, r10⟩

end

/-! ## Two runs -/

/-- What two entry states with the same public arguments share. -/
structure Pub (s₀ s₀' : State) : Prop where
  k : K s₀' = K s₀
  rsi : s₀'.gpr .rsi = s₀.gpr .rsi
  st : St s₀' = St s₀
  al : AL s₀' = AL s₀
  tl : TL s₀' = TL s₀
  src : Src s₀' = Src s₀
  sp : SP s₀' = SP s₀
  len : stackArg s₀' 0 = stackArg s₀ 0
  dst : Dst s₀' = Dst s₀
  w : W s₀' = W s₀

theorem Pub.of {s₀ s₀' : State} (h : Proof.AesGcm.streamToPub s₀ s₀') : Pub s₀ s₀' :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm,
    h.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.2.2.2.symm⟩

theorem Pub.eL {s₀ s₀' : State} (pb : Pub s₀ s₀') : L s₀' = L s₀ := by simp only [L, pb.len]

/-- The registers of the arguments, which the entry keeps. -/
def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem entry_check : ∃ hc, (taint.check (Taint.ofRegs (.r11 :: args)) (.block entry.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hd1_check : ∃ hc, (taint.check (Taint.ofRegs [.r8])
    (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem and_check : ∃ hc, (taint.check (Taint.ofRegs [.rax]) (.block [.alu .and .rax (imm 15)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hd3_check : ∃ hc, (taint.check (Taint.ofRegs [.r11])
    (.block [.mov .rax (.mem (at_ .r11 wLen)), .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem len_check : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r8]) (.block blocksLen) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem bargs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rax]) (.block blocksArgs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem rhead_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp])
    (.block [.mov .rcx (.mem (at_ .r11 wLen)), .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax),
      .alu .test .rcx (.reg .rcx)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem ptrs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rax])
    (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax), .mov .rdi (.mem (at_ .r11 wDst)),
      .alu .add .rdi (.reg .rax)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem copy_check : ∃ hc, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx]) copyLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem rargs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block restArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩

section
variable {M : CtxMode} {s₀ s₀' : State} (hp : SP' M s₀) (hp' : SP' M s₀') (pb : Pub s₀ s₀')
include hp hp' pb

/-- `work` on the stack, in two runs at `Mid`. -/
theorem mid_hW {o o' : Nat} {s₁ s₂ : State} (h₁ : Mid s₀ o s₁) (h₂ : Mid s₀' o' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 8 := by
  refine ⟨?_, by rw [h₁.rd, h₁.wr, h₁.rsp]; exact a_in hp (i := 3) (by decide),
    by rw [h₂.rd, h₂.wr, h₂.rsp]; exact a_in hp' (i := 3) (by decide)⟩
  rw [h₁.rsp, h₂.rsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp h₁.frame (by decide),
    keep_a hp' h₂.frame (by decide)]
  exact pb.w.symm

/-- The entry, in two runs. -/
theorem entry_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ =>
    B0 s₀ s₁ ∧ B0 s₀' s₂ := by
  have ea : ∀ r ∈ args, s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pb.k.symm, pb.rsi.symm, pb.st.symm, pb.al.symm, pb.tl.symm, pb.src.symm, pb.sp.symm]
  have toB0 : ∀ {s s₁ : State}, SP' M s → (s₁.gpr .r11 = W s ∧
      (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ Kept s 0 s₁.mem ∧ Frame [kR' s] s.mem s₁.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) → B0 s s₁ := fun hp ⟨h11, hg, hk, hf, hrd, hwr⟩ =>
    ⟨mid_entry hp (hg _ (by decide) (by decide) (by decide)) (fun r hr => hg r (notCs hr).2.2.2.2.2.2.2.2
      (notCs hr).1 (notCs hr).2.2.2.2.2.2.2.1) hk hf hrd hwr, h11, hg _ (by decide) (by decide) (by decide)⟩
  refine (rel_wp (rel_w (l₀ := entry) (l := entry.tail) rfl args (by simp [args])
    (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ea) (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pb.w.symm, a_in hp (i := 3) (by decide), a_in hp' (i := 3) (by decide)⟩) entry_check)
    (fun _ _ h => h) (G₁ := B0 s₀) (G₂ := B0 s₀')
    (fun s h => by subst h; exact WP.mono (entry_ok hp) fun _ h => toB0 hp h)
    (fun s h => by subst h; exact WP.mono (entry_ok hp') fun _ h => toB0 hp' h)).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- The call of the whole blocks, in two runs. -/
theorem blkCall_rel (T : BlkToFn M) {q : Nat} (hq : 16 * q ≤ L s₀) :
    RelCT isa (fun s₁ s₂ => C5 s₀ q s₁ ∧ C5 s₀' q s₂)
      (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hq' : 16 * q ≤ L s₀' := by rw [pb.eL]; exact hq
  refine RelCT.frame (fun _ _ h => by rw [h.1.2.2.2.1, h.2.2.2.2.1, pb.sp])
    (RelCT.callEx (k := Proof.AesGcm.encryptBlocksToX86_64M M) T.ok T.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, h, ha, hb⟩ := hab
  obtain ⟨⟨f₁, -, -, sp₁, -, rd₁, wr₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁, ax₁⟩,
    ⟨f₂, -, -, sp₂, -, rd₂, wr₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂, ax₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁, a₀₁, a₁₁, a₂₁⟩ := blkEntry hp hq sp₁ rd₁ wr₁ f₁ di₁ si₁ dx₁ cx₁ r8₁ r9₁ r10₁ ax₁
  obtain ⟨p₂, c₂, w₂, a₀₂, a₁₂, a₂₂⟩ := blkEntry hp' hq' sp₂ rd₂ wr₂ f₂ di₂ si₂ dx₂ cx₂ r8₂ r9₂ r10₂ ax₂
  subst ha hb
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [pushed_rsp, pushed_rsp, sp₁, sp₂, pb.sp]⟩
  have g : ∀ {t : State} {r : Reg} (rd wr : List Region), r ≠ .rsp →
      ((pushed [.rax, .r9, .r10] t).callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun _ _ h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h, pushed_gpr _ _ h]
  simp only [Proof.AesGcm.encryptBlocksToX86_64M, Proof.AesGcm.blocksToPub, Proof.AesGcm.arg, a₀₁, a₁₁, a₂₁, a₀₂,
    a₁₂, a₂₂, g _ _ (by decide : Reg.rdi ≠ .rsp), g _ _ (by decide : Reg.rsi ≠ .rsp),
    g _ _ (by decide : Reg.rdx ≠ .rsp), g _ _ (by decide : Reg.rcx ≠ .rsp), g _ _ (by decide : Reg.r8 ≠ .rsp),
    g _ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂, r8₁, r8₂, r9₁, r9₂,
    State.withRegions_gpr, State.callEntry_rsp, pushed_rsp, sp₁, sp₂, pb.k, pb.rsi, pb.st, pb.src, pb.sp, pb.dst, pb.w, and_self]

/-- `blocks`, in two runs: the same bytes done. -/
theorem blocks_rel (T : BlkToFn M) :
    RelCT isa (fun s₁ s₂ => B0 s₀ s₁ ∧ B0 s₀' s₂) (blocks T.fn) fun s₁ s₂ => ∃ o, Mid s₀ o s₁ ∧ Mid s₀' o s₂ := by
  have hL : L s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  have none : ∀ {P : State → State → Prop}, (∀ s₁ s₂, P s₁ s₂ → B0 s₀ s₁ ∧ B0 s₀' s₂) →
      RelCT isa P (.block []) fun s₁ s₂ => ∃ o, Mid s₀ o s₁ ∧ Mid s₀' o s₂ :=
    fun h => skip_rel fun _ _ hP => ⟨0, (h _ _ hP).1.1, (h _ _ hP).2.1⟩
  unfold blocks
  refine RelCT.seq (step [.r8] hd1_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.2, h.2.2.2, pb.tl])
    (fun _ _ h => h) (fun _ => b1_wp) (fun _ => b1_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.tl]) (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp (TL s₀ ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun ht0 => ?_
  refine RelCT.seq (step [.rax] and_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.2.1, h.1.2.2.1, pb.tl])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1⟩, ⟨h.1.2.1, h.1.2.2.1⟩⟩) (fun _ => b2_wp) (fun _ => b2_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2, h.2.2, pb.tl]) (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((TL s₀).toNat % 16 = 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2, Option.map_some, Option.some.injEq, Bool.not_eq_false',
      beq_iff_eq] at e
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this) fun ht16 => ?_
  refine RelCT.seq (step [.r11] hd3_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.1.2.1, h.1.2.1.2.1, pb.w])
    (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ => b3_wp hp) (fun _ => b3_wp hp')) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.eL]) (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp (L s₀ / 16 ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hq0 => ?_
  refine RelCT.seq (step [.rax, .r8] len_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.2.1, h.1.2.2.1, pb.eL]
      · rw [h.1.1.1.2.2, h.1.2.1.2.2, pb.tl])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1⟩, ⟨h.1.2.1, h.1.2.2.1⟩⟩) (fun _ => b4_wp) (fun _ => b4_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2.2, h.2.2.2.2, pb.tl, pb.eL])
    (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((TL s₀).toNat + 16 * (L s₀ / 16) < 2 ^ 64) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2.2] at e; simpa using e) fun htl => ?_
  refine RelCT.seq (step [.r11, .rax] bargs_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.1.2.1, h.1.2.1.2.1, pb.w]
      · rw [h.1.1.2.2.1, h.1.2.2.2.1, pb.eL])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1⟩, ⟨h.1.2.1, by rw [h.1.2.2.1, pb.eL],
      by rw [h.1.2.2.2.1, pb.eL]⟩⟩)
    (fun _ => b5_wp hp (q := L s₀ / 16)) (fun _ => b5_wp hp' (q := L s₀ / 16))) ?_
  have hq : 16 * (L s₀ / 16) ≤ L s₀ := by omega
  refine (rel_wp (blkCall_rel hp hp' pb T hq) (fun _ _ h => h)
    (fun _ => b6_wp hp T hq0 hq htl ht0 ht16) (fun _ => b6_wp hp' T hq0
      (by rw [pb.eL]; exact hq) (by rw [pb.tl]; exact htl) (by rw [pb.tl]; exact ht0)
      (by rw [pb.tl]; exact ht16))).mono
    (fun _ _ h => h) fun _ _ h => ⟨16 * (L s₀ / 16), h.2.1, h.2.2⟩

/-- The call of the bytes left, in two runs. -/
theorem encCall_rel (E : EncFn M) {o : Nat} (ho : o < L s₀) :
    RelCT isa (fun s₁ s₂ => R4 s₀ o s₁ ∧ R4 s₀' o s₂)
      (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) fun _ _ => True := by
  have ho' : o < L s₀' := by rw [pb.eL]; exact ho
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp, pb.sp])
    (RelCT.callEx (k := encK M) E.ok E.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, h, ha, hb⟩ := hab
  obtain ⟨⟨M₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁⟩, ⟨M₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁, a₁⟩ := encEntry hp ho M₁.rsp M₁.rd M₁.wr M₁.frame di₁ si₁ dx₁ r9₁ r10₁
  obtain ⟨p₂, c₂, w₂, a₂⟩ := encEntry hp' ho' M₂.rsp M₂.rd M₂.wr M₂.frame di₂ si₂ dx₂ r9₂ r10₂
  subst ha hb
  refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [pushed_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.sp]⟩
  have g : ∀ {t : State} {r : Reg} (rd wr : List Region), r ≠ .rsp →
      ((pushed [.r10] t).callEntry.withRegions rd wr).gpr r = t.gpr r :=
    fun _ _ h => by rw [State.withRegions_gpr, State.callEntry_gpr _ h, pushed_gpr _ _ h]
  simp only [encK, encCallPub, Proof.AesGcm.arg, a₁, a₂, g _ _ (by decide : Reg.rdi ≠ .rsp),
    g _ _ (by decide : Reg.rsi ≠ .rsp), g _ _ (by decide : Reg.rdx ≠ .rsp), g _ _ (by decide : Reg.rcx ≠ .rsp),
    g _ _ (by decide : Reg.r8 ≠ .rsp), g _ _ (by decide : Reg.r9 ≠ .rsp), di₁, di₂, si₁, si₂, dx₁, dx₂, cx₁, cx₂,
    r8₁, r8₂, r9₁, r9₂, State.withRegions_gpr, State.callEntry_rsp, pushed_rsp, M₁.rsp, M₂.rsp, pb.k, pb.rsi,
    pb.st, pb.al, pb.tl, pb.sp, pb.dst, pb.eL, and_self]

/-- `rest`, in two runs with the same bytes done. -/
theorem rest_rel (E : EncFn M) {o : Nat} :
    RelCT isa (fun s₁ s₂ => Mid s₀ o s₁ ∧ Mid s₀' o s₂) (rest E.fn) fun _ _ => True := by
  unfold rest
  refine RelCT.seq ((rel_wp (rel_w (l₀ := [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]) rfl [.rsp]
      (by simp) (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1 h.2) rhead_check)
    (fun _ _ h => h) (fun _ => r1_wp hp) (fun _ => r1_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2.2.2, h.2.2.2.2.2, pb.eL])
    (skip_rel fun _ _ _ => trivial) ?_
  refine RelCT.of_imp (o < L s₀) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2.2.2] at e
    have := h.1.1.1.o_le; simp at e; omega) fun ho => ?_
  refine RelCT.seq (step [.r11, .rax] ptrs_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.2.1, h.1.2.2.1, pb.w]
      · rw [h.1.1.2.2.2.1, h.1.2.2.2.2.1])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1, h.1.1.2.2.2.1⟩, ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2.1,
      h.1.2.2.2.2.1⟩⟩) (fun _ => r2_wp hp) (fun _ => r2_wp hp')) ?_
  refine RelCT.seq (step [.rsi, .rdi, .rcx] copy_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.2.1, h.2.2.1, pb.src]
      · rw [h.1.2.2.1, h.2.2.2.1, pb.dst]
      · rw [h.1.2.2.2, h.2.2.2.2, pb.eL])
    (fun _ _ h => h) (fun _ => r3_wp hp ho) (fun _ => r3_wp hp' (by rw [pb.eL]; exact ho))) ?_
  refine RelCT.seq ((rel_wp (rel_w (l₀ := restArgs) (l := restArgs.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1 h.2) rargs_check)
    (fun _ _ h => h) (fun _ => r4_wp hp) (fun _ => r4_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  exact encCall_rel hp hp' pb E ho

end

theorem encrypt_ct {M : CtxMode} (T : BlkToFn M) (E : EncFn M) :
    ConstantTime isa (Proof.AesGcm.streamEncryptToX86_64M M).pre Proof.AesGcm.streamToPub (encrypt T.fn E.fn) := by
  refine ct_of_rel (k := Proof.AesGcm.streamEncryptToX86_64M M) fun s₀ s₀' h h' hq => ?_
  have hp := SP'.ofM h
  have hp' := SP'.ofM h'
  have pb := Pub.of hq
  exact RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (blocks_rel hp hp' pb T)
    (RelCT.exists_ fun _ => rest_rel hp hp' pb E))

end VG.Proof.AesGcm.X86_64.StreamTo
