import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Rest

/-!
# AES-GCM streaming encryption out of place, x86-64: the head

Untrusted: everything here is checked by Lean. `head` from `Mid s 0`: if the
text so far ends inside a block, the `Hd` bytes that end it (or all the
plaintext, if fewer), unless the text so far and they would exceed 2⁶⁴
bytes, copied from the plaintext to the output and encrypted there by
`vg_aes_gcm_stream_encrypt` as the continuation of the text so far, leave
`Mid s Hd`; otherwise nothing is done (`head_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- `Mid` through a write of the slot of the head. -/
theorem Mid.slot {o : Nat} {st st' : State} (h : Mid s o st) (hf : Frame [hR s] st.mem st'.mem)
    (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) :
    Mid s o st' := by
  have one : ∀ {r : Region}, r.Disjoint (hR s) → ∀ r' ∈ [hR s], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  refine ⟨h.o_le, h.tl, by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr],
    hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf (one kR'_hR),
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wkR s, by simp, hR_sub⟩),
    fun iv a p hr hal hpl => ?_⟩
  obtain ⟨sr, dd⟩ := h.sem iv a p hr hal hpl
  refine ⟨streamRepr_frame hf (one (hp.st_w.sub_right hR_sub)) sr, ?_⟩
  rw [← dd]
  exact bytesAt_frame hf (one ((hp.d_w.sub_left (Region.sub_prefix h.o_le)).sub_right hR_sub))
    (by have := h.o_le; omega)

end

/-! ## The pieces of the head -/

section
variable (s : State)

/-- Before the head: nothing done, `work` in `r11`, the text so far in `r8`. -/
def HB (st : State) : Prop := Mid s 0 st ∧ st.gpr .r11 = W s ∧ st.gpr .r8 = TL s

/-- The slot of the head holds its number of bytes. -/
abbrev HSlot (m : Mem) : Prop := m.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 (Hd s)

/-- Before the copy of the head. -/
def HC (st : State) : Prop :=
  Mid s 0 st ∧ st.gpr .rsi = Src s + BitVec.ofNat 64 0 ∧ st.gpr .rdi = Dst s + BitVec.ofNat 64 0 ∧
    st.gpr .rcx = BitVec.ofNat 64 (Hd s) ∧ HSlot s st.mem

/-- After the copy of the head. -/
def HA (st : State) : Prop :=
  Mid s 0 st ∧ HSlot s st.mem ∧ bytesAt st.mem (Dst s + BitVec.ofNat 64 0) (Hd s) = pt s (Hd s)

/-- Before the call of the head. -/
def HE (st : State) : Prop :=
  HA s st ∧ st.gpr .rdi = K s ∧ st.gpr .rsi = s.gpr .rsi ∧ st.gpr .rdx = St s ∧ st.gpr .rcx = AL s ∧
    st.gpr .r8 = TL s + BitVec.ofNat 64 0 ∧ st.gpr .r9 = Dst s + BitVec.ofNat 64 0 ∧
    st.gpr .r10 = BitVec.ofNat 64 (Hd s)

/-- After the call of the head. -/
def HD (st : State) : Prop :=
  (∀ r ∈ calleeSaved, st.gpr r = s.gpr r) ∧ st.gpr .rsp = SP s ∧ st.rd = s.rd ∧ st.wr = s.wr ∧
    Frame (wR s ++ [tR s]) s.mem st.mem ∧ Kept s 0 st.mem ∧ HSlot s st.mem ∧ Sem s (Hd s) st.mem

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

omit hp in
theorem notCs' {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .rdi ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem hl_wp {st : State} (h : HB s st) :
    WP isa (.block headLen) st fun st' =>
      HB s st' ∧ st'.gpr .rax = BitVec.ofNat 64 (Hd s) ∧ st'.zf = some (decide (Hd s = 0)) :=
  WP.mono (headLen_ok hp h.2.1 h.2.2 h.1.kept h.1.rd h.1.wr) fun _ ⟨ax, z, g, m, rd, wr⟩ =>
    ⟨⟨h.1.regs m (fun r hr => g r (notCs' hr).1 (notCs' hr).2.1) rd wr, by rw [g _ (by decide) (by decide), h.2.1],
      by rw [g _ (by decide) (by decide), h.2.2]⟩, ax, z⟩

omit hp in
theorem ho_wp {st : State} (h : HB s st ∧ st.gpr .rax = BitVec.ofNat 64 (Hd s)) :
    WP isa (.block headOver) st fun st' =>
      (HB s st' ∧ st'.gpr .rax = BitVec.ofNat 64 (Hd s)) ∧
        st'.cf = some (decide (2 ^ 64 ≤ (TL s).toNat + Hd s)) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  exact WP.mono (headOver_ok h.2 h.1.2.2 (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hL)) fun _ ⟨cf, g, m, rd, wr⟩ =>
    ⟨⟨⟨h.1.1.regs m (fun r hr => g r (notCs' hr).2.1) rd wr, by rw [g _ (by decide), h.1.2.1],
      by rw [g _ (by decide), h.1.2.2]⟩, by rw [g _ (by decide), h.2]⟩, cf⟩

theorem hp_wp {st : State} (h : HB s st ∧ st.gpr .rax = BitVec.ofNat 64 (Hd s)) :
    WP isa (.block headPtrs) st (HC s) :=
  WP.mono (headPtrs_ok hp h.1.2.1 h.2 h.1.1.kept h.1.1.rd h.1.1.wr) fun _ ⟨cx, si, di, k, g, f, rd, wr⟩ =>
    ⟨h.1.1.slot hp f (fun r hr => g r (notCs' hr).2.1 (notCs' hr).2.2.2.1 (notCs' hr).2.2.2.2.1) rd wr,
      by rw [si, BitVec.add_zero], by rw [di, BitVec.add_zero], cx, k⟩

theorem hc_wp (hk0 : Hd s ≠ 0) {st : State} (h : HC s st) : WP isa copyLoop st (HA s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have hHL : Hd s ≤ L s := Nat.min_le_right _ _
  obtain ⟨M₃, si₃, di₃, cx₃, k₃⟩ := h
  have ds := dq_sub (s := s) (o := 0) (n := Hd s) (by omega)
  have ss : Region.Sub ⟨Src s + BitVec.ofNat 64 0, Hd s⟩ (srcR s) := Offset.sub_base _ (by omega)
  have cp : CopyPre st (Src s + BitVec.ofNat 64 0) (Dst s + BitVec.ofNat 64 0) (Hd s) :=
    ⟨si₃, di₃, cx₃, by omega, by omega,
      covers_off (k := L s) (d := 0) (m := Hd s) (by rw [M₃.rd, M₃.wr, hp.rd]; simp) (by omega) (by omega),
      covers_off (k := L s) (d := 0) (m := Hd s) (by rw [M₃.wr, hp.wr]; simp) (by omega) (by omega),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.mono (copyLoopL_ok st cp) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
  have f₄ : Frame [dqR s 0 (Hd s)] st.mem s₄.mem := by
    rw [m₄]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  refine ⟨M₃.copy hp (by omega) f₄ (fun r hr => g₄ r (notCs' hr).1 (notCs' hr).2.2.2.2.2.2.2.1) rd₄ wr₄, ?_, ?_⟩
  · show s₄.mem.readW _ 64 = _
    rw [← k₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.d_w.sub_left ds).sub_right hR_sub).symm) (by decide)
  · have e := bytesAt_writeBytes_self st.mem (Dst s + BitVec.ofNat 64 0)
      (bytesAt st.mem (Src s + BitVec.ofNat 64 0) (Hd s)) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at e
    rw [m₄, e, BitVec.add_zero]
    exact bytesAt_frame M₃.frame (fun r hr => (r_disj hp r hr).sub_left (Region.sub_prefix hHL)) (by omega)

theorem ha_wp {st : State} (h : HA s st) : WP isa (.block headArgs) st (HE s) :=
  WP.mono (headArgs_ok hp h.1 h.2.1) fun _ ⟨di, si, dx, cx, r8, r9, r10, cs, m, rd, wr⟩ =>
    ⟨⟨h.1.regs m cs rd wr, by rw [m]; exact h.2.1, by rw [m]; exact h.2.2⟩, di, si, dx, cx, r8, r9, r10⟩

theorem hcall_wp (E : EncFn M) {st : State} (h : HE s st) :
    WP isa (.frame (.push [.r10]) (.call E.fn.name E.fn.code) (.pop .rax 1)) st (HD s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have hHL : Hd s ≤ L s := Nat.min_le_right _ _
  obtain ⟨⟨M₅, k₅, hX₅⟩, di, si, dx, cx, r8, r9, r10⟩ := h
  have ds := dq_sub (s := s) (o := 0) (n := Hd s) (by omega)
  refine WP.mono (encCall_ok hp E (o := 0) (n := Hd s) (by omega) M₅.rsp M₅.rd M₅.wr M₅.frame
    di si dx cx r8 r9 r10) fun s₆ ⟨cs₆, rd₆, wr₆, f₆, post⟩ => ?_
  have f₆' : Frame (wR s ++ [tR s]) s.mem s₆.mem := M₅.frame.trans (f₆.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨stR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, ds⟩
    · exact ⟨tR s, by simp, fun _ h => h⟩)
  have out : ∀ {r : Region}, r.Sub (wkR s) → ∀ r' ∈ encWr s 0 (Hd s) ++ [tR s], r.Disjoint r' := by
    intro r hs r' hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact hp.st_w.symm.sub_left hs
    · exact (hp.d_w.symm.sub_left hs).sub_right ds
    · exact hp.b_w.symm.sub_left hs
  refine ⟨fun r hr => by rw [cs₆ r hr, M₅.saved r hr], by rw [cs₆ _ (by decide), M₅.rsp], rd₆.trans M₅.rd,
    wr₆.trans M₅.wr, f₆', M₅.kept.frame f₆ (out kR'_sub),
    by show s₆.mem.readW _ 64 = _; rw [← k₅]; exact f₆.readW (Region.contains_self _ _) (out hR_sub) (by decide),
    fun iv a p hr hal hpl => ?_⟩
  obtain ⟨sr₅, -⟩ := M₅.sem iv a p hr hal hpl
  have z : pt s 0 = [] := rfl
  rw [z, List.append_nil] at sr₅
  have hpl' : (TL s + BitVec.ofNat 64 0).toNat = p.length := by rw [BitVec.add_zero]; exact hpl
  obtain ⟨sr₆, dd₆⟩ := post iv a p sr₅ hal hpl'
  rw [hX₅] at sr₆ dd₆
  rw [BitVec.add_zero] at dd₆
  exact ⟨sr₆, dd₆⟩

theorem hd_wp (htl : (TL s).toNat + Hd s < 2 ^ 64) {st : State} (h : HD s st) :
    WP isa (.block headDone) st (Mid s (Hd s)) := by
  obtain ⟨cs₆, sp₆, rd₆, wr₆, f₆, k₆, h72₆, sem₆⟩ := h
  have hHL : Hd s ≤ L s := Nat.min_le_right _ _
  exact WP.mono (headDone_ok hp sp₆ rd₆ wr₆ f₆ k₆ h72₆) fun _ ⟨cs₇, k₇, f₇, rd₇, wr₇⟩ =>
    ⟨hHL, htl, by rw [cs₇ _ (by decide), sp₆], fun r hr => by rw [cs₇ r hr, cs₆ r hr], rd₇.trans rd₆,
      wr₇.trans wr₆, k₇, f₆.trans (frame_kR' f₇), sem₆.kR' hp f₇ hHL⟩

/-- `head`, from `Mid s 0` with `work` in `r11` and the text so far in
`r8`: some bytes done. -/
theorem head_ok (E : EncFn M) {st : State} (h : HB s st) :
    WP isa (head E.fn) st fun st' => ∃ o, Mid s o st' := by
  unfold head
  refine WP.seq (WP.mono (hl_wp hp h) fun s₁ ⟨B₁, ax₁, z₁⟩ => ?_)
  refine WP.ite (decide (Hd s = 0)) (by simp only [eval, z₁]) (fun _ => WP.block_nil ⟨0, B₁.1⟩) (fun e₁ => ?_)
  have hk0 : Hd s ≠ 0 := by simpa using e₁
  refine WP.seq (WP.mono (ho_wp ⟨B₁, ax₁⟩) fun s₂ ⟨B₂, cf₂⟩ => ?_)
  refine WP.ite (decide (2 ^ 64 ≤ (TL s).toNat + Hd s)) (by simp only [eval, cf₂])
    (fun _ => WP.block_nil ⟨0, B₂.1.1⟩) (fun e₂ => ?_)
  have htl : (TL s).toNat + Hd s < 2 ^ 64 := by simpa using e₂
  exact WP.seq (WP.mono (hp_wp hp B₂) fun _ h₃ => WP.seq (WP.mono (hc_wp hp hk0 h₃) fun _ h₄ =>
    WP.seq (WP.mono (ha_wp hp h₄) fun _ h₅ => WP.seq (WP.mono (hcall_wp hp E h₅) fun _ h₆ =>
      WP.mono (hd_wp hp htl h₆) fun _ h₇ => ⟨Hd s, h₇⟩))))

end

end VG.Proof.AesGcm.X86_64.StreamTo
