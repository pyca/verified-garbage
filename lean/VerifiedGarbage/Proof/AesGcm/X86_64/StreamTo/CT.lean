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

/-- `o` bytes done, `work` in `r11`, the text so far and the bytes done in `r8`. -/
def B0 (s : State) (o : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .r11 = W s ∧ st.gpr .r8 = TL s + BitVec.ofNat 64 o

/-- Before `blocks`' test: `B0`, with `aad_len` in `rcx`. -/
def B0c (s : State) (o : Nat) (st : State) : Prop := B0 s o st ∧ st.gpr .rcx = AL s

/-- `B0`, with `Sel` in `rax`. -/
def B1 (s : State) (o : Nat) (st : State) : Prop := B0 s o st ∧ st.gpr .rax = Sel s o

/-- Before the call of the whole blocks. -/
def C5 (s : State) (o q : Nat) (st : State) : Prop :=
  Frame (wR s ++ [tR s]) s.mem st.mem ∧ Sem s o st.mem ∧ Kept s (o + 16 * q) st.mem ∧ st.gpr .rsp = SP s ∧
    (∀ r ∈ calleeSaved, st.gpr r = s.gpr r) ∧ st.rd = s.rd ∧ st.wr = s.wr ∧
    st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s + BitVec.ofNat 64 48 ∧
    st.gpr .rcx = St s + BitVec.ofNat 64 16 ∧ st.gpr .r8 = Src s + BitVec.ofNat 64 o ∧
    st.gpr .r9 = BitVec.ofNat 64 q ∧ st.gpr .r10 = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .rax = W s + BitVec.ofNat 64 80

/-- Before the copy of the bytes left. -/
def R2 (s : State) (o : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .rsi = Src s + BitVec.ofNat 64 o ∧ st.gpr .rdi = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .rcx = BitVec.ofNat 64 (L s - o)

/-- Before a call of `vg_aes_gcm_stream_encrypt` on `n` bytes after `o`. -/
def R4 (s : State) (o n : Nat) (st : State) : Prop :=
  Mid s o st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = TL s + BitVec.ofNat 64 o ∧ st.gpr .r9 = Dst s + BitVec.ofNat 64 o ∧
    st.gpr .r10 = BitVec.ofNat 64 n

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem notCs {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem b0_wp {o : Nat} {st : State} (h : Mid s o st) : WP isa (.block blocksLoad) st (B0c s o) :=
  WP.mono (blocksLoad_ok hp h) fun _ ⟨r11, cx, r8, g, m, rd, wr⟩ =>
    ⟨⟨h.regs m (fun r hr => g r (notCs hr).2.2.2.2.2.2.2.2 (notCs hr).2.1 (notCs hr).2.2.2.2.2.1 (notCs hr).1)
      rd wr, r11, r8⟩, cx⟩

omit hp in
theorem b1_wp {o : Nat} {st : State} (h : B0c s o st) :
    WP isa (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) st fun st' =>
      B0c s o st' ∧ st'.gpr .rax = TL s + BitVec.ofNat 64 o ∧ st'.zf = some (TL s + BitVec.ofNat 64 o == 0) :=
  WP.mono hd1_ok fun _ ⟨ax, z, g, m, rd, wr⟩ =>
    ⟨⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1) rd wr, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, by rw [g _ (by decide), h.2]⟩, by rw [ax, h.1.2.2], by rw [z, h.1.2.2]⟩

omit hp in
/-- After no text, `aad_len` into `rax`. -/
theorem bsel_wp {o : Nat} {st : State} (h : B0c s o st) (hz : TL s + BitVec.ofNat 64 o = 0) :
    WP isa (.block [.mov .rax (.reg .rcx)]) st (B1 s o) :=
  WP.mono mvc_ok fun _ ⟨ax, g, m, rd, wr⟩ =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1) rd wr, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, by rw [ax, h.2]; simp only [Sel, hz, ite_true]⟩

omit hp in
/-- After some text, the text so far and the bytes done are in `rax` already. -/
theorem bsel_of {o : Nat} {st : State} (h : B0c s o st ∧ st.gpr .rax = TL s + BitVec.ofNat 64 o)
    (hz : TL s + BitVec.ofNat 64 o ≠ 0) : B1 s o st :=
  ⟨h.1.1, by rw [h.2]; simp only [Sel, hz, ite_false]⟩

omit hp in
theorem b2_wp {o : Nat} {st : State} (h : B1 s o st) :
    WP isa (.block [.alu .and .rax (imm 15)]) st fun st' =>
      B0 s o st' ∧ st'.zf = some (BitVec.ofNat 64 ((Sel s o).toNat % 16) == 0) :=
  WP.mono (hd2_ok h.2) fun _ ⟨z, g, m, rd, wr⟩ =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1) rd wr, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, z⟩

theorem b3_wp {o : Nat} {st : State} (h : B0 s o st) :
    WP isa (.block blocksCount) st
      fun st' => B0 s o st' ∧ st'.gpr .rax = BitVec.ofNat 64 ((L s - o) / 16) ∧
        st'.zf = some (decide ((L s - o) / 16 = 0)) :=
  WP.mono (blocksCount_ok hp h.2.1 h.1.kept h.1.o_le h.1.rd h.1.wr) fun _ ⟨ax, z, g, m, rd, wr⟩ =>
    ⟨⟨h.1.regs m (fun r hr => g r (notCs hr).1 (notCs hr).2.1) rd wr, by rw [g _ (by decide) (by decide), h.2.1],
      by rw [g _ (by decide) (by decide), h.2.2]⟩, ax, z⟩

omit hp in
theorem b4_wp {o : Nat} {st : State} (h : B0 s o st ∧ st.gpr .rax = BitVec.ofNat 64 ((L s - o) / 16)) :
    WP isa (.block blocksLen) st fun st' => B0 s o st' ∧ st'.gpr .r9 = BitVec.ofNat 64 ((L s - o) / 16) ∧
      st'.gpr .rax = BitVec.ofNat 64 (16 * ((L s - o) / 16)) ∧
      st'.cf = some (decide (2 ^ 64 ≤ (TL s).toNat + o + 16 * ((L s - o) / 16))) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have h16 : (BitVec.ofNat 64 (16 * ((L s - o) / 16))).toNat = 16 * ((L s - o) / 16) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  exact WP.mono (len_ok h.2 h.1.2.2) fun _ ⟨r9, ax, cf, g, m, rd, wr⟩ =>
    ⟨⟨h.1.1.regs m (fun r hr => g r (notCs hr).1 (notCs hr).2.2.2.2.2.2.1 (notCs hr).2.1) rd wr,
      by rw [g _ (by decide) (by decide) (by decide), h.1.2.1], by rw [g _ (by decide) (by decide) (by decide), h.1.2.2]⟩,
      r9, ax, by rw [cf, h16, tl_add h.1.1.tl]⟩

theorem b5_wp {o q : Nat} {st : State}
    (h : B0 s o st ∧ st.gpr .r9 = BitVec.ofNat 64 q ∧ st.gpr .rax = BitVec.ofNat 64 (16 * q)) :
    WP isa (.block blocksArgs) st (C5 s o q) :=
  WP.mono (blocksArgs_ok hp h.1.2.1 h.2.2 h.1.1.kept h.1.1.rd h.1.1.wr)
    fun _ ⟨di, si, dx, cx, r8, r10, ax, g, k, f, rd, wr⟩ =>
      ⟨h.1.1.frame.trans (frame_kR' f), h.1.1.sem.kR' hp f h.1.1.o_le, k,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.1.1.rsp],
        fun r hr => by
          have n := notCs hr
          rw [g r n.2.2.2.2.1 n.2.2.2.1 n.2.2.1 n.2.1 n.2.2.2.2.2.1 n.2.2.2.2.2.2.2.1 n.1, h.1.1.saved r hr],
        rd.trans h.1.1.rd, wr.trans h.1.1.wr, di, si, dx, cx, r8,
        by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.2.1],
        r10, ax⟩

theorem b6_wp (T : BlkToFn M) {o q : Nat} (hq0 : q ≠ 0) (hq : o + 16 * q ≤ L s)
    (htl : (TL s).toNat + (o + 16 * q) < 2 ^ 64) (ht0 : TL s + BitVec.ofNat 64 o ≠ 0 ∨ (AL s).toNat % 16 = 0)
    (ht16 : ((TL s).toNat + o) % 16 = 0) {st : State} (h : C5 s o q st) :
    WP isa (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) st (Mid s (o + 16 * q)) := by
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
  have ds := dq_sub (s := s) (o := o) (n := L s - o) (by omega)
  have ss : Region.Sub ⟨Src s + BitVec.ofNat 64 o, L s - o⟩ (srcR s) := Offset.sub_base _ (by omega)
  have cp : CopyPre st (Src s + BitVec.ofNat 64 o) (Dst s + BitVec.ofNat 64 o) (L s - o) :=
    ⟨si, di, cx, by omega, by omega,
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.rd, M₂.wr, hp.rd]; simp) (by omega) (by omega),
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.wr, hp.wr]; simp) (by omega) (by omega),
      (hp.r_d.sub_left ss).sub_right ds⟩
  exact WP.mono (copyLoopL_ok st cp) fun _ ⟨m₃, g₃, rd₃, wr₃⟩ =>
    M₂.copy hp (n := L s - o) (by omega) (by rw [m₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _))
      (fun r hr => g₃ r (notCs hr).1 (notCs hr).2.2.2.2.2.2.2.1) rd₃ wr₃

theorem r4_wp {o : Nat} {st : State} (h : Mid s o st) : WP isa (.block restArgs) st (R4 s o (L s - o)) :=
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

theorem Pub.eHd {s₀ s₀' : State} (pb : Pub s₀ s₀') : Hd s₀' = Hd s₀ := by simp only [Hd, pb.tl, pb.eL]

/-- The registers of the arguments, which the entry keeps. -/
def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

theorem entry_check : ∃ hc, (taint.check (Taint.ofRegs (.r11 :: args)) (.block entry.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hlen_check : ∃ hc, (taint.check (Taint.ofRegs [.r8, .r11]) (.block headLen) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hover_check : ∃ hc, (taint.check (Taint.ofRegs [.rax, .r8]) (.block headOver) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hptrs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rax]) (.block headPtrs) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hargs_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block headArgs.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hdone_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block headDone.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem bload_check : ∃ hc, (taint.check (Taint.ofRegs [.r11, .rsp]) (.block blocksLoad.tail) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem hd1_check : ∃ hc, (taint.check (Taint.ofRegs [.r8])
    (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) hc).isSome = true := ⟨_, by taint_decide⟩
theorem mvc_check : ∃ hc, (taint.check (Taint.ofRegs [.rcx]) (.block [.mov .rax (.reg .rcx)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem and_check : ∃ hc, (taint.check (Taint.ofRegs [.rax]) (.block [.alu .and .rax (imm 15)]) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem bcount_check : ∃ hc, (taint.check (Taint.ofRegs [.r11]) (.block blocksCount) hc).isSome = true :=
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

/-- `work` on the stack, in two runs through frames of the regions written. -/
theorem hW_of {s₁ s₂ : State} (sp₁ : s₁.gpr .rsp = SP s₀) (rd₁ : s₁.rd = s₀.rd) (wr₁ : s₁.wr = s₀.wr)
    (f₁ : Frame (wR s₀ ++ [tR s₀]) s₀.mem s₁.mem) (sp₂ : s₂.gpr .rsp = SP s₀') (rd₂ : s₂.rd = s₀'.rd)
    (wr₂ : s₂.wr = s₀'.wr) (f₂ : Frame (wR s₀' ++ [tR s₀']) s₀'.mem s₂.mem) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 8 := by
  obtain ⟨i₁, w₁⟩ := w_stack' hp sp₁ rd₁ wr₁ f₁
  obtain ⟨i₂, w₂⟩ := w_stack' hp' sp₂ rd₂ wr₂ f₂
  exact ⟨by rw [w₁, w₂, pb.w], i₁, i₂⟩

/-- `work` on the stack, in two runs at `Mid`. -/
theorem mid_hW {o o' : Nat} {s₁ s₂ : State} (h₁ : Mid s₀ o s₁) (h₂ : Mid s₀' o' s₂) :
    s₁.mem.readW (s₁.gpr .rsp + BitVec.ofNat 64 32) 64 = s₂.mem.readW (s₂.gpr .rsp + BitVec.ofNat 64 32) 64 ∧
      InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .rsp + BitVec.ofNat 64 32) 8 :=
  hW_of hp hp' pb h₁.rsp h₁.rd h₁.wr h₁.frame h₂.rsp h₂.rd h₂.wr h₂.frame

/-- The entry, in two runs. -/
theorem entry_rel : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block entry) fun s₁ s₂ =>
    HB s₀ s₁ ∧ HB s₀' s₂ := by
  have ea : ∀ r ∈ args, s₀.gpr r = s₀'.gpr r := by
    intro r hr
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [pb.k.symm, pb.rsi.symm, pb.st.symm, pb.al.symm, pb.tl.symm, pb.src.symm, pb.sp.symm]
  have toB0 : ∀ {s s₁ : State}, SP' M s → (s₁.gpr .r11 = W s ∧
      (∀ r, r ≠ .r11 → r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r) ∧ Kept s 0 s₁.mem ∧ Frame [kR' s] s.mem s₁.mem ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr) → HB s s₁ := fun hp ⟨h11, hg, hk, hf, hrd, hwr⟩ =>
    ⟨mid_entry hp (hg _ (by decide) (by decide) (by decide)) (fun r hr => hg r (notCs hr).2.2.2.2.2.2.2.2
      (notCs hr).1 (notCs hr).2.2.2.2.2.2.2.1) hk hf hrd hwr, h11, hg _ (by decide) (by decide) (by decide)⟩
  refine (rel_wp (rel_w (l₀ := entry) (l := entry.tail) rfl args (by simp [args])
    (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ea) (fun _ _ h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pb.w.symm, a_in hp (i := 3) (by decide), a_in hp' (i := 3) (by decide)⟩) entry_check)
    (fun _ _ h => h) (G₁ := HB s₀) (G₂ := HB s₀')
    (fun s h => by subst h; exact WP.mono (entry_ok hp) fun _ h => toB0 hp h)
    (fun s h => by subst h; exact WP.mono (entry_ok hp') fun _ h => toB0 hp' h)).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- The call of `n` bytes after `o`, in two runs. -/
theorem encCall_rel (E : EncFn M) {o n : Nat} (hn : o + n ≤ L s₀) :
    RelCT isa (fun s₁ s₂ => R4 s₀ o n s₁ ∧ R4 s₀' o n s₂)
      (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) fun _ _ => True := by
  have hn' : o + n ≤ L s₀' := by rw [pb.eL]; exact hn
  refine RelCT.frame (fun _ _ h => by rw [h.1.1.rsp, h.2.1.rsp, pb.sp])
    (RelCT.callEx (k := encK M) E.ok E.ct fun _ _ hab => ?_)
  obtain ⟨s₁, s₂, h, ha, hb⟩ := hab
  obtain ⟨⟨M₁, di₁, si₁, dx₁, cx₁, r8₁, r9₁, r10₁⟩, ⟨M₂, di₂, si₂, dx₂, cx₂, r8₂, r9₂, r10₂⟩⟩ := h
  obtain ⟨p₁, c₁, w₁, a₁⟩ := encEntry hp hn M₁.rsp M₁.rd M₁.wr M₁.frame di₁ si₁ dx₁ r9₁ r10₁
  obtain ⟨p₂, c₂, w₂, a₂⟩ := encEntry hp' hn' M₂.rsp M₂.rd M₂.wr M₂.frame di₂ si₂ dx₂ r9₂ r10₂
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

/-- `head`, in two runs: the same bytes done. -/
theorem head_rel (E : EncFn M) :
    RelCT isa (fun s₁ s₂ => HB s₀ s₁ ∧ HB s₀' s₂) (head E.fn) fun s₁ s₂ => ∃ o, Mid s₀ o s₁ ∧ Mid s₀' o s₂ := by
  have hL : L s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  have eHd := pb.eHd
  unfold head
  refine RelCT.seq (step [.r8, .r11] hlen_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.2.2, h.2.2.2, pb.tl]
      · rw [h.1.2.1, h.2.2.1, pb.w])
    (fun _ _ h => h) (fun _ => hl_wp hp) (fun _ => hl_wp hp')) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, eHd])
    (skip_rel fun _ _ h => ⟨0, h.1.1.1.1, h.1.2.1.1⟩) ?_
  refine RelCT.of_imp (Hd s₀ ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hk0 => ?_
  refine RelCT.seq (step [.rax, .r8] hover_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.2.1, h.1.2.2.1, eHd]
      · rw [h.1.1.1.2.2, h.1.2.1.2.2, pb.tl])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1⟩, ⟨h.1.2.1, h.1.2.2.1⟩⟩) (fun _ => ho_wp) (fun _ => ho_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2, h.2.2, eHd, pb.tl])
    (skip_rel fun _ _ h => ⟨0, h.1.1.1.1.1, h.1.2.1.1.1⟩) ?_
  refine RelCT.of_imp ((TL s₀).toNat + Hd s₀ < 2 ^ 64) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2] at e; simpa using e) fun htl => ?_
  refine RelCT.seq (step [.r11, .rax] hptrs_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.1.1.2.1, h.1.2.1.1.2.1, pb.w]
      · rw [h.1.1.1.2, h.1.2.1.2, eHd])
    (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ => hp_wp hp) (fun _ => hp_wp hp')) ?_
  refine RelCT.seq (step [.rsi, .rdi, .rcx] copy_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.2.1, h.2.2.1, pb.src]
      · rw [h.1.2.2.1, h.2.2.2.1, pb.dst]
      · rw [h.1.2.2.2.1, h.2.2.2.2.1, eHd])
    (fun _ _ h => h) (fun _ => hc_wp hp hk0) (fun _ => hc_wp hp' (by rw [eHd]; exact hk0))) ?_
  refine RelCT.seq ((rel_wp (rel_w (l₀ := headArgs) (l := headArgs.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.rsp, h.2.1.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1.1 h.2.1) hargs_check)
    (fun _ _ h => h) (fun _ => ha_wp hp) (fun _ => ha_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.seq ((rel_wp ((encCall_rel hp hp' pb E (o := 0) (n := Hd s₀)
      (by have : Hd s₀ ≤ L s₀ := Nat.min_le_right _ _; omega)).mono
      (fun _ _ h => ⟨⟨h.1.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h.1.2.2.2.2.1, h.1.2.2.2.2.2.1,
        h.1.2.2.2.2.2.2.1, h.1.2.2.2.2.2.2.2⟩, ⟨h.2.1.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
        h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, by rw [h.2.2.2.2.2.2.2.2, eHd]⟩⟩) fun _ _ h => h)
    (fun _ _ h => h) (fun _ => hcall_wp hp E) (fun _ => hcall_wp hp' E)).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine ((rel_wp (rel_w (l₀ := headDone) (l := headDone.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2.1, h.2.2.1, pb.sp])
      (fun _ _ h => hW_of hp hp' pb h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
        h.2.2.2.2.2.1) hdone_check)
    (fun _ _ h => h) (fun _ => hd_wp hp htl) (fun _ => hd_wp hp' (by rw [pb.tl, eHd]; exact htl))).mono
    (fun _ _ h => h) fun _ _ h => ⟨Hd s₀, h.2.1, eHd ▸ h.2.2⟩)

/-- The call of the whole blocks, in two runs. -/
theorem blkCall_rel (T : BlkToFn M) {o q : Nat} (hq : o + 16 * q ≤ L s₀) :
    RelCT isa (fun s₁ s₂ => C5 s₀ o q s₁ ∧ C5 s₀' o q s₂)
      (.frame (.push [.rax, .r9, .r10]) (.call T.fn.name T.fn.code) (.pop .rax 3)) fun _ _ => True := by
  have hq' : o + 16 * q ≤ L s₀' := by rw [pb.eL]; exact hq
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

/-- `blocks`, in two runs with the same bytes done: the same bytes done. -/
theorem blocks_rel (T : BlkToFn M) {o : Nat} :
    RelCT isa (fun s₁ s₂ => Mid s₀ o s₁ ∧ Mid s₀' o s₂) (blocks T.fn) fun s₁ s₂ =>
      ∃ o', Mid s₀ o' s₁ ∧ Mid s₀' o' s₂ := by
  have hL : L s₀ < 2 ^ 64 := (stackArg s₀ 0).isLt
  have none : ∀ {P : State → State → Prop}, (∀ s₁ s₂, P s₁ s₂ → B0 s₀ o s₁ ∧ B0 s₀' o s₂) →
      RelCT isa P (.block []) fun s₁ s₂ => ∃ o', Mid s₀ o' s₁ ∧ Mid s₀' o' s₂ :=
    fun h => skip_rel fun _ _ hP => ⟨o, (h _ _ hP).1.1, (h _ _ hP).2.1⟩
  have esel : Sel s₀' o = Sel s₀ o := by simp only [Sel, pb.tl, pb.al]
  unfold blocks
  refine RelCT.seq ((rel_wp (rel_w (l₀ := blocksLoad) (l := blocksLoad.tail) rfl [.rsp] (by simp)
      (fun _ _ h r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h.1.rsp, h.2.rsp, pb.sp])
      (fun _ _ h => mid_hW hp hp' pb h.1 h.2) bload_check)
    (fun _ _ h => h) (fun _ => b0_wp hp) (fun _ => b0_wp hp')).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.seq (step [.r8] hd1_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.2.2, h.2.1.2.2, pb.tl])
    (fun _ _ h => h) (fun _ => b1_wp) (fun _ => b1_wp)) ?_
  -- `Sel` into `rax`.
  refine RelCT.seq (R := fun s₁ s₂ => B1 s₀ o s₁ ∧ B1 s₀' o s₂)
    (RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.tl]) ?_ ?_) ?_
  · refine RelCT.of_imp (TL s₀ + BitVec.ofNat 64 o = 0) (fun _ _ h => by
      have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hz => ?_
    exact step [.rcx] mvc_check (fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.1.2, h.1.2.1.2, pb.al])
      (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ h => bsel_wp h hz) (fun _ h => bsel_wp h (by rw [pb.tl]; exact hz))
  · refine RelCT.of_imp (TL s₀ + BitVec.ofNat 64 o ≠ 0) (fun _ _ h => by
      have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hz => ?_
    exact skip_rel fun _ _ h => ⟨bsel_of ⟨h.1.1.1, h.1.1.2.1⟩ hz, bsel_of ⟨h.1.2.1, h.1.2.2.1⟩ (by rw [pb.tl]; exact hz)⟩
  refine RelCT.seq (step [.rax] and_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, esel])
    (fun _ _ h => h) (fun _ => b2_wp) (fun _ => b2_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2, h.2.2, esel]) (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((Sel s₀ o).toNat % 16 = 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2, Option.map_some, Option.some.injEq, Bool.not_eq_false',
      beq_iff_eq] at e
    have := congrArg BitVec.toNat e
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this) fun hsel => ?_
  obtain ⟨ht16, ht0⟩ := sel_mod hsel
  refine RelCT.seq (step [.r11] bcount_check (fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.1.1.2.1, h.1.2.1.2.1, pb.w])
    (fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) (fun _ => b3_wp hp) (fun _ => b3_wp hp')) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2, h.2.2.2, pb.eL])
    (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((L s₀ - o) / 16 ≠ 0) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2] at e; simpa using e) fun hq0 => ?_
  refine RelCT.seq (step [.rax, .r8] len_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.2.1, h.1.2.2.1, pb.eL]
      · rw [h.1.1.1.2.2, h.1.2.1.2.2, pb.tl])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1⟩, ⟨h.1.2.1, h.1.2.2.1⟩⟩) (fun _ => b4_wp) (fun _ => b4_wp)) ?_
  refine RelCT.ite (fun _ _ h => by simp only [eval, h.1.2.2.2, h.2.2.2.2, pb.tl, pb.eL])
    (none fun _ _ h => ⟨h.1.1.1, h.1.2.1⟩) ?_
  refine RelCT.of_imp ((TL s₀).toNat + (o + 16 * ((L s₀ - o) / 16)) < 2 ^ 64) (fun _ _ h => by
    have e := h.2; simp only [eval, h.1.1.2.2.2] at e; simp at e; omega) fun htl => ?_
  refine RelCT.of_imp (o ≤ L s₀ ∧ (TL s₀).toNat + o < 2 ^ 64) (fun _ _ h => ⟨h.1.1.1.1.o_le, h.1.1.1.1.tl⟩)
    fun ⟨ho, hto⟩ => ?_
  rw [tl_add hto] at ht16
  refine RelCT.seq (step [.r11, .rax] bargs_check (fun _ _ h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.1.2.1, h.1.2.1.2.1, pb.w]
      · rw [h.1.1.2.2.1, h.1.2.2.2.1, pb.eL])
    (fun _ _ h => ⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1⟩, ⟨h.1.2.1, by rw [h.1.2.2.1, pb.eL],
      by rw [h.1.2.2.2.1, pb.eL]⟩⟩)
    (fun _ => b5_wp hp (q := (L s₀ - o) / 16)) (fun _ => b5_wp hp' (q := (L s₀ - o) / 16))) ?_
  have hq : o + 16 * ((L s₀ - o) / 16) ≤ L s₀ := by omega
  refine (rel_wp (blkCall_rel hp hp' pb T hq) (fun _ _ h => h)
    (fun _ => b6_wp hp T hq0 hq htl ht0 ht16) (fun _ => b6_wp hp' T hq0
      (by rw [pb.eL]; exact hq) (by rw [pb.tl]; exact htl) (by rw [pb.tl, pb.al]; exact ht0)
      (by rw [pb.tl]; exact ht16))).mono
    (fun _ _ h => h) fun _ _ h => ⟨o + 16 * ((L s₀ - o) / 16), h.2.1, h.2.2⟩

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
  exact (encCall_rel hp hp' pb E (o := o) (n := L s₀ - o) (by omega)).mono
    (fun _ _ h => ⟨h.1, by rw [← pb.eL]; exact h.2⟩) fun _ _ h => h

end

theorem encrypt_ct {M : CtxMode} (T : BlkToFn M) (E : EncFn M) :
    ConstantTime isa (Proof.AesGcm.streamEncryptToX86_64M M).pre Proof.AesGcm.streamToPub (encrypt T.fn E.fn) := by
  refine ct_of_rel (k := Proof.AesGcm.streamEncryptToX86_64M M) fun s₀ s₀' h h' hq => ?_
  have hp := SP'.ofM h
  have hp' := SP'.ofM h'
  have pb := Pub.of hq
  exact RelCT.seq (entry_rel hp hp' pb) (RelCT.seq (head_rel hp hp' pb E)
    (RelCT.seq (RelCT.exists_ fun _ => blocks_rel hp hp' pb T) (RelCT.exists_ fun _ => rest_rel hp hp' pb E)))

end VG.Proof.AesGcm.X86_64.StreamTo
