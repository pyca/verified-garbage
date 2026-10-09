import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Mid
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith

/-!
# AES-GCM streaming encryption out of place, x86-64: the blocks between the calls

Untrusted: everything here is checked by Lean. What each block of
instructions of `blocks` and `rest` does (`hd1_ok` … `restArgs_ok`), from
the arguments kept in `work`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.StreamTo

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.StreamTo
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `stackArg` of the state a call enters, from the caller's stack. -/
theorem stackArg_entry {t : State} {F : Addr} (hsp : t.gpr .rsp = F) (hF : 8 ≤ F.toNat) (rd wr : List Region)
    {i : Nat} (hi : F.toNat + 8 * i + 8 ≤ 2 ^ 64) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (F + BitVec.ofNat 64 (8 * i)) 64 := by
  have hb : F - 8 + BitVec.ofNat 64 (8 * (i + 1)) = F + BitVec.ofNat 64 (8 * i) := by
    rw [show 8 * (i + 1) = 8 + 8 * i by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  have hsep := Offset.sep (F - 8) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show F - 8 + BitVec.ofNat 64 0 = F - 8 from BitVec.add_zero _, hb] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, hb]
  exact Mem.readW_writeW_sep hsep (by decide)

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `test r8, r8`, through `rax`: whether there is no text so far. -/
theorem hd1_ok {st : State} :
    WP isa (.block [.mov .rax (.reg .r8), .alu .test .rax (.reg .rax)]) st fun st' =>
      st'.gpr .rax = st.gpr .r8 ∧ st'.zf = some (st.gpr .r8 == 0) ∧
      (∀ r, r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp only [zf_arithFlags, gpr_setReg, ite_true, BitVec.and_self]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- `mov rax, rcx`: `aad_len`, after no text. -/
theorem mvc_ok {st : State} :
    WP isa (.block [.mov .rax (.reg .rcx)]) st fun st' =>
      st'.gpr .rax = st.gpr .rcx ∧ (∀ r, r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
        st'.rd = st.rd ∧ st'.wr = st.wr := by
  apply WP.of_runBlock
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg]
  · intro r hr; simp [gpr_setReg, hr]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- `and rax, 15`: whether the text so far ends a block. -/
theorem hd2_ok {st : State} {T : BitVec 64} (hax : st.gpr .rax = T) :
    WP isa (.block [.alu .and .rax (imm 15)]) st fun st' =>
      st'.zf = some (BitVec.ofNat 64 (T.toNat % 16) == 0) ∧
      (∀ r, r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have e15 := and15 T
  rw [imm_eq (by decide)] at e15
  apply WP.of_runBlock
  refine ⟨_, by simp only [imm]; xrun [hax], ?_, ?_, ?_, ?_, ?_⟩
  · simp [zf_arithFlags, gpr_setReg, e15]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- `work`'s slot `d`, readable. -/
theorem slot_in {st : State} (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) {d : Nat} (hd : d + 8 ≤ 80) :
    InRegions (st.rd ++ st.wr) (W s + BitVec.ofNat 64 d) 8 := by
  rw [hrd, hwr]; exact w_in' hp (by omega)

/-- `work` from the stack, through a frame of the regions written and the
stack. -/
theorem w_stack' {st : State} (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr)
    (hf : Frame (wR s ++ [tR s]) s.mem st.mem) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s := by
  refine ⟨by rw [hrd, hwr, hsp]; exact a_in hp (i := 3) (by decide), ?_⟩
  rw [hsp, show (32 : Nat) = 8 * (3 + 1) from rfl, keep_a hp hf (by decide)]; rfl

/-- `work` from the stack. -/
theorem w_stack {o : Nat} {st : State} (h : Mid s o st) :
    InRegions (st.rd ++ st.wr) (st.gpr .rsp + BitVec.ofNat 64 32) 8 ∧
      st.mem.readW (st.gpr .rsp + BitVec.ofNat 64 32) 64 = W s :=
  w_stack' hp h.rsp h.rd h.wr h.frame

/-- `work`, `aad_len`, and the text so far and the `o` bytes done. -/
theorem blocksLoad_ok {o : Nat} {st : State} (h : Mid s o st) :
    WP isa (.block blocksLoad) st fun st' =>
      st'.gpr .r11 = W s ∧ st'.gpr .rcx = AL s ∧ st'.gpr .r8 = TL s + BitVec.ofNat 64 o ∧
      (∀ r, r ≠ .r11 → r ≠ .rcx → r ≠ .r8 → r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₃, hW⟩ := w_stack hp h
  have r₃ := slot_in hp h.rd h.wr (d := 24) (by decide)
  have r₄ := slot_in hp h.rd h.wr (d := 32) (by decide)
  have r₈ := slot_in hp h.rd h.wr (d := 64) (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [blocksLoad, wAad, wTlen, wDone]
    xrun [a₃, hW, r₃, r₄, r₈, h.kept.aad, h.kept.tl, h.kept.done], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg, gpr_arithFlags]; done)
  · intro r a b c d; simp [gpr_setReg, gpr_arithFlags, a, b, c, d]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

/-- The number of whole blocks of the plaintext left after the `o` bytes
done, and whether there is none. -/
theorem blocksCount_ok {st : State} {o : Nat} (h11 : st.gpr .r11 = W s) (hk : Kept s o st.mem) (ho : o ≤ L s)
    (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block blocksCount) st
      fun st' => st'.gpr .rax = BitVec.ofNat 64 ((L s - o) / 16) ∧ st'.zf = some (decide ((L s - o) / 16 = 0)) ∧
        (∀ r, r ≠ .rax → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
        st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have q₁ := slot_in hp hrd hwr (d := 48) (by decide)
  have q₂ := slot_in hp hrd hwr (d := 64) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [hk.len, ofNat_toNat]
  have hsub := ofNat_sub ho hL
  have h4 := shr4 (L s - o) (by omega)
  have hz := and_self_beq (show (L s - o) / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [blocksCount, wLen, wDone]; xrun [h11, q₁, q₂, hlen, hk.done, hsub, h4], ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr hr'; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr, hr']
  all_goals simp [mem_arithFlags, mem_setReg, mem_setFlags, rd_arithFlags, rd_setReg, rd_setFlags, wr_arithFlags,
    wr_setReg, wr_setFlags]

end

/-- `16 q`, by doubling four times. -/
theorem dbl (x : Nat) : BitVec.ofNat 64 x + BitVec.ofNat 64 x = BitVec.ofNat 64 (2 * x) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

/-- The number of whole blocks into `r9`, their bytes into `rax`, and
whether the text so far and they would exceed 2⁶⁴ bytes. -/
theorem len_ok {st : State} {q : Nat} {T : BitVec 64} (hax : st.gpr .rax = BitVec.ofNat 64 q) (h8 : st.gpr .r8 = T) :
    WP isa (.block blocksLen) st fun st' =>
      st'.gpr .r9 = BitVec.ofNat 64 q ∧ st'.gpr .rax = BitVec.ofNat 64 (16 * q) ∧
      st'.cf = some (decide (2 ^ 64 ≤ T.toNat + (BitVec.ofNat 64 (16 * q)).toNat)) ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  have d₁ := dbl q
  have d₂ := dbl (2 * q)
  have d₃ := dbl (2 * (2 * q))
  have d₄ := dbl (2 * (2 * (2 * q)))
  have e16 : 2 * (2 * (2 * (2 * q))) = 16 * q := by omega
  rw [e16] at d₄
  apply WP.of_runBlock
  refine ⟨_, by simp only [blocksLen]; xrun [hax, h8, d₁, d₂, d₃, d₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags]
  · simp [gpr_setReg, gpr_arithFlags, d₄]
  · simp only [cf_arithFlags, cf_setReg]
  · intro r a b c; simp [gpr_setReg, gpr_arithFlags, a, b, c]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The bytes done, `o + 16 q`, kept, and the arguments of
`vg_aes_gcm_encrypt_blocks_to`, past the `o` bytes done before. -/
theorem blocksArgs_ok {st : State} {o q : Nat} (h11 : st.gpr .r11 = W s)
    (hax : st.gpr .rax = BitVec.ofNat 64 (16 * q)) (hk : Kept s o st.mem) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block blocksArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s + BitVec.ofNat 64 48 ∧
      st'.gpr .rcx = St s + BitVec.ofNat 64 16 ∧ st'.gpr .r8 = Src s + BitVec.ofNat 64 o ∧
      st'.gpr .r10 = Dst s + BitVec.ofNat 64 o ∧ st'.gpr .rax = W s + BitVec.ofNat 64 80 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → r ≠ .rax → st'.gpr r = st.gpr r) ∧
      Kept s (o + 16 * q) st'.mem ∧ Frame [kR' s] st.mem st'.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have w64 : InRegions st.wr (W s + BitVec.ofNat 64 64) (64 / 8) := by rw [hwr]; exact w_in hp (by decide)
  have r₀ := slot_in hp hrd hwr (d := 0) (by decide)
  have r₁ := slot_in hp hrd hwr (d := 8) (by decide)
  have r₂ := slot_in hp hrd hwr (d := 16) (by decide)
  have r₅ := slot_in hp hrd hwr (d := 40) (by decide)
  have r₇ := slot_in hp hrd hwr (d := 56) (by decide)
  have r₈ := slot_in hp hrd hwr (d := 64) (by decide)
  have sep : ∀ d : Nat, d + 8 ≤ 64 →
      Mem.Sep (W s + BitVec.ofNat 64 d) (64 / 8) (W s + BitVec.ofNat 64 64) (64 / 8) :=
    fun d hd => Offset.sep _ (.inl hd) (by omega) (by have := hp.w_w; omega)
  have s₀ := sep 0 (by decide)
  have s₁ := sep 8 (by decide)
  have s₂ := sep 16 (by decide)
  have s₅ := sep 40 (by decide)
  have s₇ := sep 56 (by decide)
  have k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using hk.ctx
  have hdn := hk.done
  have hsum : BitVec.ofNat 64 (16 * q) + BitVec.ofNat 64 o = BitVec.ofNat 64 (o + 16 * q) := by
    rw [← BitVec.ofNat_add, Nat.add_comm]
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [blocksArgs, wDone, wCtx, wRounds, wState, wSrc, wDst, wScr, imm]
    xrun [h11, hax, w64, r₀, r₁, r₂, r₅, r₇, r₈, s₀, s₁, s₂, s₅, s₇, k0, hk.rounds, hk.st, hk.src, hk.dst, hdn,
      hsum],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rfl, by rfl⟩
  iterate 7
    simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, gpr_arithFlags,
      ite_true, reduceCtorEq, ↓reduceIte, Mem.readW_writeW_sep, k0, hk.rounds, hk.st, hk.src, hk.dst, hdn, h11]
  · intro r a b c d e f g; simp [gpr_setReg, gpr_arithFlags, a, b, c, d, e, f, g]
  · have k : ∀ d, d + 8 ≤ 64 → (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 (o + 16 * q))).readW
        (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
      fun d hd => Mem.readW_writeW_sep (sep d hd) (by decide)
    have k0' : (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 (o + 16 * q))).readW (W s) 64 =
        st.mem.readW (W s) 64 := by simpa using k 0 (by decide)
    simp only [mem_setReg, mem_arithFlags]
    exact ⟨by rw [k0']; exact hk.ctx, by rw [k 8 (by decide)]; exact hk.rounds, by rw [k 16 (by decide)]; exact hk.st,
      by rw [k 24 (by decide)]; exact hk.aad, by rw [k 32 (by decide)]; exact hk.tl,
      by rw [k 40 (by decide)]; exact hk.src, by rw [k 48 (by decide)]; exact hk.len,
      by rw [k 56 (by decide)]; exact hk.dst, Mem.readW_writeW_self64 _ _ _⟩
  · simp only [mem_setReg, mem_arithFlags]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 64 + 64 / 8 ≤ 72 by decide) (by have := hp.w_w; omega))

end

/-! ## The head -/

/-- The bytes of the head: those that end the block the text so far ends
inside, or all the plaintext if fewer. -/
abbrev Hd (s : State) : Nat := min ((16 - (TL s).toNat % 16) % 16) (L s)

/-- `-T mod 16`, as `and` computes it. -/
theorem neg_and15 (T : BitVec 64) : -T &&& 15#64 = BitVec.ofNat 64 ((16 - T.toNat % 16) % 16) := by
  have e := and15 (-T)
  rw [imm_eq (by decide)] at e
  rw [e]
  congr 1
  rw [BitVec.toNat_neg]
  have := T.isLt
  omega

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The bytes of the head into `rax`, and whether there are none. -/
theorem headLen_ok {st : State} {o : Nat} (h11 : st.gpr .r11 = W s) (h8 : st.gpr .r8 = TL s)
    (hk : Kept s o st.mem) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block headLen) st fun st' =>
      st'.gpr .rax = BitVec.ofNat 64 (Hd s) ∧ st'.zf = some (decide (Hd s = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧
      st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have q₁ := slot_in hp hrd hwr (d := 48) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [hk.len, ofNat_toNat]
  have hn := neg_and15 (TL s)
  have hn₀ : BitVec.setWidth 64 (BitVec.ofNat 32 0) - TL s &&& 15#64 =
      BitVec.ofNat 64 ((16 - (TL s).toNat % 16) % 16) := by
    rw [← hn, show BitVec.setWidth 64 (BitVec.ofNat 32 0) = 0#64 from rfl, BitVec.zero_sub]
  have hpad : (BitVec.ofNat 64 ((16 - (TL s).toNat % 16) % 16)).toNat = (16 - (TL s).toNat % 16) % 16 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hLn : (BitVec.ofNat 64 (L s)).toNat = L s := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hL
  have hz := and_self_beq (show Hd s < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hL)
  apply WP.of_runBlock
  by_cases hc : L s < (16 - (TL s).toNat % 16) % 16
  · have e : Hd s = L s := by simp only [Hd]; omega
    refine ⟨_, by
      simp only [headLen, wLen]
      xrun [h11, h8, q₁, hlen, hn₀, hn, execCmov, eval, hpad, hLn, hc, decide_true, e], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, e]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, e] at hz ⊢; rw [hz]
    · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]
  · have e : Hd s = (16 - (TL s).toNat % 16) % 16 := by simp only [Hd]; omega
    refine ⟨_, by
      simp only [headLen, wLen]
      xrun [h11, h8, q₁, hlen, hn₀, hn, execCmov, eval, hpad, hLn, hc, decide_false, e], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, e]
    · simp only [zf_arithFlags, gpr_setReg, ite_true, e] at hz ⊢; rw [hz]
    · intro r a b; simp [gpr_setReg, gpr_arithFlags, a, b]
    all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

end

/-- Whether the text so far and the `k` bytes of the head would exceed 2⁶⁴
bytes. -/
theorem headOver_ok {st : State} {k : Nat} {T : BitVec 64} (hax : st.gpr .rax = BitVec.ofNat 64 k)
    (h8 : st.gpr .r8 = T) (hk : k < 2 ^ 64) :
    WP isa (.block headOver) st fun st' =>
      st'.cf = some (decide (2 ^ 64 ≤ T.toNat + k)) ∧ (∀ r, r ≠ .rcx → st'.gpr r = st.gpr r) ∧
      st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hkn : (BitVec.ofNat 64 k).toNat = k := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hk
  apply WP.of_runBlock
  refine ⟨_, by simp only [headOver]; xrun [hax, h8], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [cf_arithFlags, cf_setReg, hkn]
  · intro r a; simp [gpr_setReg, gpr_arithFlags, a]
  all_goals simp [mem_arithFlags, mem_setReg, rd_arithFlags, rd_setReg, wr_arithFlags, wr_setReg]

section
variable {M : CtxMode} {s : State} (hp : SP' M s)
include hp

/-- The `k` bytes of the head kept in their slot, and the pointers and the
length of their copy. -/
theorem headPtrs_ok {st : State} {o k : Nat} (h11 : st.gpr .r11 = W s) (hax : st.gpr .rax = BitVec.ofNat 64 k)
    (hk : Kept s o st.mem) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block headPtrs) st fun st' =>
      st'.gpr .rcx = BitVec.ofNat 64 k ∧ st'.gpr .rsi = Src s ∧ st'.gpr .rdi = Dst s ∧
      st'.mem.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 k ∧
      (∀ r, r ≠ .rcx → r ≠ .rsi → r ≠ .rdi → st'.gpr r = st.gpr r) ∧ Frame [hR s] st.mem st'.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  have w72 : InRegions st.wr (W s + BitVec.ofNat 64 72) (64 / 8) := by rw [hwr]; exact w_in hp (by decide)
  have r₅ := slot_in hp hrd hwr (d := 40) (by decide)
  have r₇ := slot_in hp hrd hwr (d := 56) (by decide)
  have sep : ∀ d : Nat, d + 8 ≤ 72 →
      Mem.Sep (W s + BitVec.ofNat 64 d) (64 / 8) (W s + BitVec.ofNat 64 72) (64 / 8) :=
    fun d hd => Offset.sep _ (.inl hd) (by omega) (by have := hp.w_w; omega)
  have s₅ := sep 40 (by decide)
  have s₇ := sep 56 (by decide)
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [headPtrs, wHead, wSrc, wDst]
    xrun [h11, hax, w72, r₅, r₇, s₅, s₇, hk.src, hk.dst], ?_, ?_, ?_, ?_, ?_, ?_, by rfl, by rfl⟩
  all_goals try (simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, ite_true,
    reduceCtorEq, ↓reduceIte, Mem.readW_writeW_sep, hk.src, hk.dst, hax]; done)
  · simp only [mem_setReg]; exact Mem.readW_writeW_self64 _ _ _
  · intro r a b c; simp [gpr_setReg, a, b, c]
  · simp only [mem_setReg]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- The arguments of `vg_aes_gcm_stream_encrypt` on the `k` bytes of the
head, their number from its slot. -/
theorem headArgs_ok {o k : Nat} {st : State} (h : Mid s o st)
    (h72 : st.mem.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 k) :
    WP isa (.block headArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s ∧ st'.gpr .rcx = AL s ∧
      st'.gpr .r8 = TL s + BitVec.ofNat 64 0 ∧ st'.gpr .r9 = Dst s + BitVec.ofNat 64 0 ∧
      st'.gpr .r10 = BitVec.ofNat 64 k ∧
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₃, hW⟩ := w_stack hp h
  have r₀ := slot_in hp h.rd h.wr (d := 0) (by decide)
  have r₁ := slot_in hp h.rd h.wr (d := 8) (by decide)
  have r₂ := slot_in hp h.rd h.wr (d := 16) (by decide)
  have r₃ := slot_in hp h.rd h.wr (d := 24) (by decide)
  have r₄ := slot_in hp h.rd h.wr (d := 32) (by decide)
  have r₇ := slot_in hp h.rd h.wr (d := 56) (by decide)
  have r₉ := slot_in hp h.rd h.wr (d := 72) (by decide)
  have k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using h.kept.ctx
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [headArgs, wCtx, wRounds, wState, wAad, wTlen, wDst, wHead]
    xrun [a₃, hW, r₀, r₁, r₂, r₃, r₄, r₇, r₉, k0, h.kept.rounds, h.kept.st, h.kept.aad, h.kept.tl, h.kept.dst, h72],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (simp [gpr_setReg]; done)
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  all_goals simp [mem_setReg, rd_setReg, wr_setReg]

/-- The `k` bytes of the head, from their slot, done. -/
theorem headDone_ok {o k : Nat} {st : State} (hsp : st.gpr .rsp = SP s) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr)
    (hf : Frame (wR s ++ [tR s]) s.mem st.mem) (hk : Kept s o st.mem)
    (h72 : st.mem.readW (W s + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 k) :
    WP isa (.block headDone) st fun st' =>
      (∀ r ∈ calleeSaved, st'.gpr r = st.gpr r) ∧ Kept s k st'.mem ∧ Frame [kR' s] st.mem st'.mem ∧
      st'.rd = st.rd ∧ st'.wr = st.wr := by
  obtain ⟨a₃, hW⟩ := w_stack' hp hsp hrd hwr hf
  have r₉ := slot_in hp hrd hwr (d := 72) (by decide)
  have w64 : InRegions st.wr (W s + BitVec.ofNat 64 64) (64 / 8) := by rw [hwr]; exact w_in hp (by decide)
  have sep : ∀ d : Nat, d + 8 ≤ 64 →
      Mem.Sep (W s + BitVec.ofNat 64 d) (64 / 8) (W s + BitVec.ofNat 64 64) (64 / 8) :=
    fun d hd => Offset.sep _ (.inl hd) (by omega) (by have := hp.w_w; omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [headDone, wHead, wDone]; xrun [a₃, hW, r₉, h72, w64], ?_, ?_, ?_, by rfl, by rfl⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
  · have e : ∀ d, d + 8 ≤ 64 → (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 k)).readW
        (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
      fun d hd => Mem.readW_writeW_sep (sep d hd) (by decide)
    have e0 : (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 k)).readW (W s) 64 =
        st.mem.readW (W s) 64 := by simpa using e 0 (by decide)
    simp only [mem_setReg]
    exact ⟨by rw [e0]; exact hk.ctx, by rw [e 8 (by decide)]; exact hk.rounds, by rw [e 16 (by decide)]; exact hk.st,
      by rw [e 24 (by decide)]; exact hk.aad, by rw [e 32 (by decide)]; exact hk.tl,
      by rw [e 40 (by decide)]; exact hk.src, by rw [e 48 (by decide)]; exact hk.len,
      by rw [e 56 (by decide)]; exact hk.dst, Mem.readW_writeW_self64 _ _ _⟩
  · simp only [mem_setReg]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (show 64 + 64 / 8 ≤ 72 by decide) (by have := hp.w_w; omega))

end

end VG.Proof.AesGcm.X86_64.StreamTo
