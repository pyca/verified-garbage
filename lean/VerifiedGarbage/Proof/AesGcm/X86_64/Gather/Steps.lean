import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Mid

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the blocks between the calls

Untrusted: everything here is checked by Lean. What each block of
instructions between the calls does (`aadArgs_ok` … `finArgs_ok`), from the
arguments and the progress kept in `work`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

section
variable {M : CtxMode} {s : State} (hp : SG M s)
include hp

/-- The arguments of `vg_aes_gcm_stream_aad(ctx, state, 0, aad, aad_len)`. -/
theorem aadArgs_ok {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) :
    WP isa (.block aadArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = St s ∧ st'.gpr .rdx = BitVec.ofNat 64 0 ∧ st'.gpr .rcx = Ad s ∧
      st'.gpr .r8 = AL s ∧ (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₀ := h.slot hp (d := 0) (by decide)
  have r₂ := h.slot hp (d := 16) (by decide)
  have r₃ := h.slot hp (d := 24) (by decide)
  have hz : BitVec.setWidth 64 (BitVec.ofNat 32 0) = BitVec.ofNat 64 0 := by decide
  have i104 := imm_eq (n := 104) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [aadArgs, gCtx, gState, gAad, gAlen, imm]
    xrun [a₅, e₅, r₀, r₂, r₃, h.kept.ctx, h.kept.aad, h.kept.alen, hz, i104], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The length of the text, `ZF` if 0. -/
theorem textLen_ok {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) :
    WP isa (.block textLen) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.zf = some (decide (L s = 0)) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₅ := h.slot hp (d := 40) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 (L s) := by
    rw [h.kept.len, ofNat_toNat]
  have hz := and_self_beq (show L s < 2 ^ 64 from (stackArg s 3).isLt)
  apply WP.of_runBlock
  refine ⟨_, by simp only [textLen, gLen]; xrun [a₅, e₅, r₅, hlen], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hz]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- `aad_len` into `rcx`, its remainder modulo 16 into `r8`, `ZF` if 0. -/
theorem padLen_ok {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) (h11 : st.gpr .r11 = W s) :
    WP isa (.block padLen) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .rcx = AL s ∧ st'.gpr .r8 = BitVec.ofNat 64 ((AL s).toNat % 16) ∧
      st'.zf = some (decide ((AL s).toNat % 16 = 0)) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have r₃ := h.slot hp (d := 24) (by decide)
  have e15 := and15 (AL s)
  rw [imm_eq (by decide)] at e15
  have hz := and_self_beq (show (AL s).toNat % 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [padLen, gAlen, imm]; xrun [h11, r₃, h.kept.alen, e15], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, h11]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, reduceCtorEq, ↓reduceIte, hz]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]


/-- The padding's length `16 - r` into `r8`, the padded length kept, and the
arguments of `vg_aes_gcm_stream_aad(ctx, state, aad_len, zeros, 16 - r)`. -/
theorem padArgs_ok {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) (h11 : st.gpr .r11 = W s)
    (hcx : st.gpr .rcx = AL s) (h8 : st.gpr .r8 = BitVec.ofNat 64 ((AL s).toNat % 16)) :
    WP isa (.block padArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = St s ∧ st'.gpr .rdx = AL s ∧
      st'.gpr .rcx = W s + BitVec.ofNat 64 88 ∧ st'.gpr .r8 = BitVec.ofNat 64 (16 - (AL s).toNat % 16) ∧
      Kept s (AL s + BitVec.ofNat 64 (16 - (AL s).toNat % 16)) i st'.mem ∧ Frame [kpR s] st.mem st'.mem ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have r₀ := h.slot hp (d := 0) (by decide)
  have w₁₀ : InRegions st.wr (W s + BitVec.ofNat 64 80) (64 / 8) := by rw [h.wr]; exact w_in hp (by decide)
  have hz : BitVec.setWidth 64 (BitVec.ofNat 32 16) = BitVec.ofNat 64 16 := by decide
  have hsub : BitVec.ofNat 64 16 - BitVec.ofNat 64 ((AL s).toNat % 16) = BitVec.ofNat 64 (16 - (AL s).toNat % 16) :=
    ofNat_sub (by omega) (by decide)
  have i104 := imm_eq (n := 104) (by decide)
  have i88 := imm_eq (n := 88) (by decide)
  have hw := hp.w_w
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [padArgs, gCtx, gState, gAlenP, gZero, imm]
    xrun [h11, hcx, h8, r₀, h.kept.ctx, w₁₀, hz, hsub, i104, i88], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags]; done)
  · simp only [mem_setReg, mem_arithFlags]
    exact ⟨by simp (disch := decide) only [readW_writeW_off, h.kept.ctx],
      by simp (disch := decide) only [readW_writeW_off, h.kept.rounds],
      by simp (disch := decide) only [readW_writeW_off, h.kept.aad],
      by simp (disch := decide) only [readW_writeW_off, h.kept.alen],
      by simp (disch := decide) only [readW_writeW_off, h.kept.dst],
      by simp (disch := decide) only [readW_writeW_off, h.kept.len],
      by simp (disch := decide) only [readW_writeW_off, h.kept.tag],
      by simp (disch := decide) only [readW_writeW_off, h.kept.desc],
      by simp (disch := decide) only [readW_writeW_off, h.kept.left],
      by simp (disch := decide) only [readW_writeW_off, h.kept.off],
      by simp (disch := decide) only [Mem.readW_writeW_self64, gpr_setReg, gpr_arithFlags, reduceCtorEq,
        ↓reduceIte, ite_true],
      by simp (disch := decide) only [readW_writeW_off, h.kept.z₀],
      by simp (disch := decide) only [readW_writeW_off, h.kept.z₁]⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by omega))
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The slices left, `ZF` if none. -/
theorem leftTest_ok {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) :
    WP isa (.block leftTest) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.zf = some (decide (Cnt s - i = 0)) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₈ := h.slot hp (d := 64) (by decide)
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have hz := and_self_beq (show Cnt s - i < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [leftTest, gLeft]; xrun [a₅, e₅, r₈, h.kept.left], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, hz]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The descriptor of slice `i`, readable. -/
theorem desc_in {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) (hi : i < Cnt s) {d : Nat}
    (hd : d + 8 ≤ 16) : InRegions (st.rd ++ st.wr) (Src s + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 d) 8 := by
  rw [h.rd, h.wr, hp.rd, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact ⟨dsR s, by simp, Offset.contains_base _ (by omega) (by have := hp.w_ds; omega)⟩

/-- The arguments of `vg_aes_gcm_stream_encrypt_to` for slice `i`. -/
theorem sliceArgs_ok {ap : BitVec 64} {i : Nat} (hi : i < Cnt s) {st : State} (h : Base s ap i st) :
    WP isa (.block sliceArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s ∧ st'.gpr .rcx = ap ∧
      st'.gpr .r8 = BitVec.ofNat 64 (gl s i) ∧ st'.gpr .r9 = sb s i ∧
      st'.gpr .r10 = Dst s + BitVec.ofNat 64 (gl s i) ∧ st'.gpr .rax = BitVec.ofNat 64 (sl s i) ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₀ := h.slot hp (d := 0) (by decide)
  have r₁ := h.slot hp (d := 8) (by decide)
  have r₄ := h.slot hp (d := 32) (by decide)
  have r₇ := h.slot hp (d := 56) (by decide)
  have r₉ := h.slot hp (d := 72) (by decide)
  have r₁₀ := h.slot hp (d := 80) (by decide)
  have d₀ := desc_in hp h hi (d := 0) (by decide)
  have d₈ := desc_in hp h hi (d := 8) (by decide)
  have v₀ : st.mem.readW (Src s + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 0) 64 = sb s i := by
    simpa using sb_eq hp h.frame hi
  have v₈ := sl_eq hp h.frame hi
  have i104 := imm_eq (n := 104) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [sliceArgs, gCtx, gRounds, gState, gDst, gDesc, gOff, gAlenP, imm]
    xrun [a₅, e₅, r₀, r₁, r₄, r₇, r₉, r₁₀, d₀, d₈, v₀, v₈, h.kept.ctx, h.kept.rounds, h.kept.dst, h.kept.desc,
      h.kept.off, h.kept.alenP, i104], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- Past slice `i`: its bytes done, the next descriptor, one slice fewer
left, `ZF` if none. -/
theorem sliceNext_ok {ap : BitVec 64} {i : Nat} (hi : i < Cnt s) {st : State} (h : Base s ap i st) :
    WP isa (.block sliceNext) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.zf = some (decide (Cnt s - (i + 1) = 0)) ∧
      Kept s ap (i + 1) st'.mem ∧ Frame [kpR s] st.mem st'.mem ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 3).isLt
  have hC : Cnt s < 2 ^ 64 := (stackArg s 1).isLt
  have gsl := gl_succ_le hp hi
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₇ := h.slot hp (d := 56) (by decide)
  have r₈ := h.slot hp (d := 64) (by decide)
  have r₉ := h.slot hp (d := 72) (by decide)
  have w : ∀ d, d + 8 ≤ 104 → InRegions st.wr (W s + BitVec.ofNat 64 d) (64 / 8) := fun d hd => by
    rw [h.wr]; exact w_in hp (by omega)
  have d₈ := desc_in hp h hi (d := 8) (by decide)
  have v₈ := sl_eq hp h.frame hi
  have i16 := imm_eq (n := 16) (by decide)
  have i1 := imm_eq (n := 1) (by decide)
  have eOff : BitVec.ofNat 64 (gl s i) + BitVec.ofNat 64 (sl s i) = BitVec.ofNat 64 (gl s (i + 1)) := by
    rw [ofNat_add_ofNat, gl_succ]
  have eDesc : Src s + BitVec.ofNat 64 (16 * i) + BitVec.ofNat 64 16 = Src s + BitVec.ofNat 64 (16 * (i + 1)) := by
    rw [BitVec.add_assoc, ofNat_add_ofNat]; congr 2
  have eLeft : BitVec.ofNat 64 (Cnt s - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (Cnt s - (i + 1)) := by
    rw [ofNat_sub (by omega) (by omega)]; congr 1
  have hz := and_self_beq (show Cnt s - (i + 1) < 2 ^ 64 by omega)
  have hw := hp.w_w
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [sliceNext, gDesc, gOff, gLeft, imm]
    xrun [a₅, e₅, r₇, r₈, r₉, d₈, v₈, h.kept.desc, h.kept.off, h.kept.left, i16, i1, eOff, eDesc, eLeft,
      w 72 (by decide), w 56 (by decide), w 64 (by decide)], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, reduceCtorEq, ↓reduceIte, hz]
  · simp only [mem_setReg, mem_arithFlags]
    exact ⟨by simp (disch := decide) only [readW_writeW_off, h.kept.ctx],
      by simp (disch := decide) only [readW_writeW_off, h.kept.rounds],
      by simp (disch := decide) only [readW_writeW_off, h.kept.aad],
      by simp (disch := decide) only [readW_writeW_off, h.kept.alen],
      by simp (disch := decide) only [readW_writeW_off, h.kept.dst],
      by simp (disch := decide) only [readW_writeW_off, h.kept.len],
      by simp (disch := decide) only [readW_writeW_off, h.kept.tag],
      by simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64],
      by simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64],
      by simp (disch := decide) only [readW_writeW_off, Mem.readW_writeW_self64],
      by simp (disch := decide) only [readW_writeW_off, h.kept.alenP],
      by simp (disch := decide) only [readW_writeW_off, h.kept.z₀],
      by simp (disch := decide) only [readW_writeW_off, h.kept.z₁]⟩
  · simp only [mem_setReg, mem_arithFlags]
    have c : ∀ d, d + 8 ≤ 104 → (kpR s).Contains (W s + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₂ => Offset.contains_base _ h₂ (by omega)
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 72 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 56 (by decide))).writeW (List.mem_singleton_self _) _ (c 64 (by decide))
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The arguments of `vg_aes_gcm_stream_finish(ctx, rounds, state, aad_len,
len, tag)`. -/
theorem finArgs_ok {ap : BitVec 64} {i : Nat} {st : State} (h : Base s ap i st) :
    WP isa (.block finArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s ∧ st'.gpr .rcx = AL s ∧
      st'.gpr .r8 = stackArg s 3 ∧ st'.gpr .r9 = Tg s ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₅, e₅⟩ := h.w hp
  have r₀ := h.slot hp (d := 0) (by decide)
  have r₁ := h.slot hp (d := 8) (by decide)
  have r₃ := h.slot hp (d := 24) (by decide)
  have r₅ := h.slot hp (d := 40) (by decide)
  have r₆ := h.slot hp (d := 48) (by decide)
  have i104 := imm_eq (n := 104) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [finArgs, gCtx, gRounds, gState, gAlen, gLen, gTag, imm]
    xrun [a₅, e₅, r₀, r₁, r₃, r₅, r₆, h.kept.ctx, h.kept.rounds, h.kept.alen, h.kept.len, h.kept.tag, i104],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg, gpr_arithFlags]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

end VG.Proof.AesGcm.X86_64.Gather
