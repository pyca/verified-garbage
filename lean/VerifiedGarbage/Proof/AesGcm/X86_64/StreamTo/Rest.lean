import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.EncCall
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Copy

/-!
# AES-GCM streaming encryption out of place, x86-64: the bytes left

Untrusted: everything here is checked by Lean. `rest` from `Mid s o`: the
`L - o` bytes left, if any, copied from the plaintext to the output and
encrypted there by `vg_aes_gcm_stream_encrypt` as the continuation of the
text so far and the first `o` bytes, make the whole encryption (`rest_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo VG.WriteBytes
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr gctr inc32 j0)

/-- What the function returns with. -/
def Done (s s' : State) : Prop := gprPreserved s s' ∧ Proof.AesGcm.streamToPost s s'

/-- The encryption of a text in two pieces, past the first `k ≤ |x|` bytes. -/
theorem gctr_drop (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb : Spec.Gcm.Block) {x y : List Byte} {k : Nat}
    (hk : k ≤ x.length) :
    (gctr ciph icb (x ++ y)).drop k = (gctr ciph icb x).drop k ++ (gctr ciph icb (x ++ y)).drop x.length := by
  rw [Proof.Gcm.gctr_append, List.drop_append_of_le_length (by rw [Proof.Gcm.length_gctr]; exact hk),
    List.drop_left' (Proof.Gcm.length_gctr _ _ _)]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- `work` from the stack, and the bytes left, `L - o`. -/
theorem restHead_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block [.mov .r11 (.mem (at_ .rsp 32)), .mov .rcx (.mem (at_ .r11 wLen)),
      .mov .rax (.mem (at_ .r11 wDone)), .alu .sub .rcx (.reg .rax), .alu .test .rcx (.reg .rcx)]) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .rcx = BitVec.ofNat 64 (L s - o) ∧ st'.gpr .rax = BitVec.ofNat 64 o ∧
      st'.zf = some (decide (L s - o = 0)) ∧
      (∀ r, r ≠ .r11 → r ≠ .rcx → r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  have a₃ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 3) (by decide)
  have hW : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
    rw [h.rsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₆ := slot_in hp h.rd h.wr (d := 48) (by decide)
  have r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have hsub := ofNat_sub ho hL
  have hz := and_self_beq (show L s - o < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [wLen, wDone]; xrun [a₃, hW, r₆, r₈, hlen, h.kept.done, hsub], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, hsub]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hsub, hz]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The pointers of the copy: past the `o` bytes done. -/
theorem restPtrs_ok {o : Nat} {st : State} (h : Mid s o st) (h11 : st.gpr .r11 = W s)
    (hax : st.gpr .rax = BitVec.ofNat 64 o) :
    WP isa (.block [.mov .rsi (.mem (at_ .r11 wSrc)), .alu .add .rsi (.reg .rax), .mov .rdi (.mem (at_ .r11 wDst)),
      .alu .add .rdi (.reg .rax)]) st fun st' =>
      st'.gpr .rsi = Src s + BitVec.ofNat 64 o ∧ st'.gpr .rdi = Dst s + BitVec.ofNat 64 o ∧
      (∀ r, r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have r₅ := slot_in hp h.rd h.wr (d := 40) (by decide)
  have r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by simp only [wSrc, wDst]; xrun [h11, hax, r₅, r₇, h.kept.src, h.kept.dst], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags]
  · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The arguments of `vg_aes_gcm_stream_encrypt` on the bytes left. -/
theorem restArgs_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block restArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s ∧ st'.gpr .rcx = AL s ∧
      st'.gpr .r8 = TL s + BitVec.ofNat 64 o ∧ st'.gpr .r9 = Dst s + BitVec.ofNat 64 o ∧
      st'.gpr .r10 = BitVec.ofNat 64 (L s - o) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  have a₃ : InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 := by
    rw [h.rd, h.wr, h.rsp]; exact a_in hp (i := 3) (by decide)
  have hW : st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
    rw [h.rsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp h.frame (by decide)]; rfl
  have r₀ := slot_in hp h.rd h.wr (d := 0) (by decide)
  have r₁ := slot_in hp h.rd h.wr (d := 8) (by decide)
  have r₂ := slot_in hp h.rd h.wr (d := 16) (by decide)
  have r₃ := slot_in hp h.rd h.wr (d := 24) (by decide)
  have r₄ := slot_in hp h.rd h.wr (d := 32) (by decide)
  have r₆ := slot_in hp h.rd h.wr (d := 48) (by decide)
  have r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  have r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  have k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have hsub := ofNat_sub ho hL
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [restArgs, wCtx, wRounds, wState, wAad, wTlen, wLen, wDst, wDone]
    xrun [a₃, hW, r₀, r₁, r₂, r₃, r₄, r₆, r₇, r₈, k0, h.kept.rounds, h.kept.st, h.kept.aad, h.kept.tl, hlen,
      h.kept.dst, h.kept.done, hsub],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags, hsub]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The return address is apart from what the code writes. -/
theorem ret_disj : ∀ r ∈ wR s ++ [tR s], (⟨SP s, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl) | rfl
  exacts [hp.t_st, hp.t_d, hp.t_w, Offset.base_disjoint_below _ (by have := hp.w_sp; omega)]

/-- With every byte done, `Mid` is the end. -/
theorem done_of {st : State} (h : Mid s (L s) st) : Done s st :=
  ⟨⟨h.saved, h.frame.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩,
    fun iv a p hr hal hpl => h.sem iv a p hr hal hpl⟩

/-- `Mid` through the copy, which writes only the output past the `o` bytes done. -/
theorem Mid.copy {o : Nat} {st st' : State} (h : Mid s o st) (hlt : o < L s)
    (hf : Frame [dqR s o] st.mem st'.mem) (hcs : ∀ r ∈ calleeSaved, st'.gpr r = st.gpr r)
    (hrd : st'.rd = st.rd) (hwr : st'.wr = st.wr) : Mid s o st' := by
  have ds := dq_sub (s := s) (Nat.le_of_lt hlt)
  have one : ∀ {r : Region}, r.Disjoint (dqR s o) → ∀ r' ∈ [dqR s o], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd
  refine ⟨h.o_le, h.tl, by rw [hcs _ (by decide), h.rsp], fun r hr => by rw [hcs r hr, h.saved r hr],
    hrd.trans h.rd, hwr.trans h.wr, h.kept.frame hf (one ((hp.d_w.symm.sub_left kR'_sub).sub_right ds)),
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s, by simp, ds⟩),
    fun iv a p hr hal hpl => ?_⟩
  obtain ⟨sr, dd⟩ := h.sem iv a p hr hal hpl
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  refine ⟨streamRepr_frame hf (one (hp.st_d.sub_right ds)) sr, ?_⟩
  rw [← dd]
  exact bytesAt_frame hf (one (Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega))) (by omega)

/-- `rest`, from `Mid s o`: the end. -/
theorem rest_ok (E : EncFn M) {o : Nat} {st : State} (h : Mid s o st) : WP isa (rest E.fn) st (Done s) := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have ho := h.o_le
  unfold rest
  refine WP.seq (WP.mono (restHead_ok hp h) fun s₁ ⟨r11₁, cx₁, ax₁, z₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have M₁ : Mid s o s₁ := h.regs m₁ (fun r hr => g₁ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr) (by rintro rfl; simp [calleeSaved] at hr)) rd₁ wr₁
  refine WP.ite (decide (L s - o = 0)) (by simp only [eval, z₁]) (fun e => ?_) (fun e => ?_)
  · have hoL : o = L s := by simp at e; omega
    exact WP.block_nil (done_of hp (hoL ▸ M₁))
  have hlt : o < L s := by simp at e; omega
  refine WP.seq (WP.mono (restPtrs_ok hp M₁ r11₁ ax₁) fun s₂ ⟨si₂, di₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  have M₂ : Mid s o s₂ := M₁.regs m₂ (fun r hr => g₂ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₂ wr₂
  have ds := dq_sub (s := s) (Nat.le_of_lt hlt)
  have ss : Region.Sub ⟨Src s + BitVec.ofNat 64 o, L s - o⟩ (srcR s) := Offset.sub_base _ (by omega)
  have cp : CopyPre s₂ (Src s + BitVec.ofNat 64 o) (Dst s + BitVec.ofNat 64 o) (L s - o) :=
    ⟨si₂, di₂, by rw [g₂ _ (by decide) (by decide), cx₁], by omega, by omega,
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.rd, M₂.wr, hp.rd]; simp) (by omega) (by omega),
      covers_off (k := L s) (d := o) (m := L s - o) (by rw [M₂.wr, hp.wr]; simp) (by omega) (by omega),
      (hp.r_d.sub_left ss).sub_right ds⟩
  refine WP.seq (WP.mono (copyLoopL_ok s₂ cp) fun s₃ ⟨m₃, g₃, rd₃, wr₃⟩ => ?_)
  have f₃ : Frame [dqR s o] s₂.mem s₃.mem := by
    rw [m₃]; exact writeBytes_frame' _ (length_bytesAt _ _ _)
  have M₃ : Mid s o s₃ := M₂.copy hp hlt f₃ (fun r hr => g₃ r (by rintro rfl; simp [calleeSaved] at hr)
    (by rintro rfl; simp [calleeSaved] at hr)) rd₃ wr₃
  have hX₃ : bytesAt s₃.mem (Dst s + BitVec.ofNat 64 o) (L s - o) = bytesAt s.mem (Src s + BitVec.ofNat 64 o) (L s - o) := by
    have e := bytesAt_writeBytes_self s₂.mem (Dst s + BitVec.ofNat 64 o)
      (bytesAt s₂.mem (Src s + BitVec.ofNat 64 o) (L s - o)) (by rw [length_bytesAt]; omega)
    rw [length_bytesAt] at e
    rw [m₃, e]
    exact bytesAt_frame M₂.frame (fun r hr => (r_disj hp r hr).sub_left ss) (by omega)
  refine WP.seq (WP.mono (restArgs_ok hp M₃) fun s₄ ⟨di, si, dx, cx, r8, r9, r10, cs₄, m₄, rd₄, wr₄⟩ => ?_)
  have M₄ : Mid s o s₄ := M₃.regs m₄ cs₄ rd₄ wr₄
  refine WP.mono (encCall_ok hp E hlt M₄.rsp M₄.rd M₄.wr M₄.frame di si dx cx r8 r9 r10)
    fun s₅ ⟨cs₅, rd₅, wr₅, f₅, post⟩ => ?_
  have f₅' : Frame (wR s ++ [tR s]) s.mem s₅.mem := M₄.frame.trans (f₅.sub fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact ⟨stR s, by simp, fun _ h => h⟩
    · exact ⟨dR s, by simp, ds⟩
    · exact ⟨tR s, by simp, fun _ h => h⟩)
  refine ⟨⟨fun r hr => by rw [cs₅ r hr, M₄.saved r hr],
    f₅'.readW (Region.contains_self _ _) (ret_disj hp) (by decide)⟩, fun iv a p hr hal hpl => ?_⟩
  obtain ⟨sr₄, dd₄⟩ := M₄.sem iv a p hr hal hpl
  have hpl' : (TL s + BitVec.ofNat 64 o).toNat = (p ++ pt s o).length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt M₄.tl,
      List.length_append, length_bytesAt]
    show (TL s).toNat + o = p.length + o
    rw [hpl]
  obtain ⟨sr₅, dd₅⟩ := post iv a (p ++ pt s o) sr₄ hal hpl'
  rw [m₄, hX₃] at sr₅ dd₅
  have hP : p ++ bytesAt s.mem (Src s) (L s) = p ++ pt s o ++ bytesAt s.mem (Src s + BitVec.ofNat 64 o) (L s - o) := by
    rw [List.append_assoc, ← bytesAt_add, Nat.add_sub_cancel' ho]
  show StreamRepr s₅.mem (St s) (ciph s) (hk s) iv a (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (Src s) (L s))) ∧
    bytesAt s₅.mem (Dst s) (L s) = (gctr (ciph s) (inc32 (j0 (hk s) iv)) (p ++ bytesAt s.mem (Src s) (L s))).drop p.length
  rw [hP]
  refine ⟨sr₅, ?_⟩
  have hD : bytesAt s₅.mem (Dst s) o = bytesAt s₄.mem (Dst s) o := by
    refine bytesAt_frame f₅ (fun r hr => ?_) (by omega)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact (hp.st_d.symm.sub_left (Region.sub_prefix ho))
    · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.w_d; omega)
    · exact hp.b_d.symm.sub_left (Region.sub_prefix ho)
  rw [← Nat.add_sub_cancel' ho, bytesAt_add, Nat.add_sub_cancel' ho, hD, dd₄, dd₅,
    gctr_drop (x := p ++ pt s o) (k := p.length) _ _ (by rw [List.length_append]; omega)]

end

end VG.Proof.AesGcm.X86_64.StreamTo
