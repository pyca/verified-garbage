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
theorem slot_in {st : State} (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) {d : Nat} (hd : d + 8 ≤ 72) :
    InRegions (st.rd ++ st.wr) (W s + BitVec.ofNat 64 d) 8 := by
  rw [hrd, hwr]; exact w_in' hp (by omega)

/-- The number of whole blocks of the plaintext, and whether there is none. -/
theorem hd3_ok {st : State} {o : Nat} (h11 : st.gpr .r11 = W s) (hk : Kept s o st.mem) (hrd : st.rd = s.rd)
    (hwr : st.wr = s.wr) :
    WP isa (.block [.mov .rax (.mem (at_ .r11 wLen)), .shift .shr .rax 4, .alu .test .rax (.reg .rax)]) st
      fun st' => st'.gpr .rax = BitVec.ofNat 64 (L s / 16) ∧ st'.zf = some (decide (L s / 16 = 0)) ∧
        (∀ r, r ≠ .rax → st'.gpr r = st.gpr r) ∧ st'.mem = st.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have hL : L s < 2 ^ 64 := (stackArg s 0).isLt
  have q₁ := slot_in hp hrd hwr (d := 48) (by decide)
  have hlen : st.mem.readW (W s + BitVec.ofNat 64 48) 64 = BitVec.ofNat 64 (L s) := by
    rw [hk.len, ofNat_toNat]
  have h4 := shr4 (L s) hL
  have hz := and_self_beq (show L s / 16 < 2 ^ 64 by omega)
  apply WP.of_runBlock
  refine ⟨_, by simp only [wLen]; xrun [h11, q₁, hlen, h4], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, h4]
  · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, ite_true, h4, hz]
  · intro r hr; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
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

/-- The bytes done, `16 q`, kept, and the arguments of
`vg_aes_gcm_encrypt_blocks_to`. -/
theorem blocksArgs_ok {st : State} {q : Nat} (h11 : st.gpr .r11 = W s) (hax : st.gpr .rax = BitVec.ofNat 64 (16 * q))
    (hk : Kept s 0 st.mem) (hrd : st.rd = s.rd) (hwr : st.wr = s.wr) :
    WP isa (.block blocksArgs) st fun st' =>
      st'.gpr .rdi = K s ∧ st'.gpr .rsi = s.gpr .rsi ∧ st'.gpr .rdx = St s + BitVec.ofNat 64 48 ∧
      st'.gpr .rcx = St s + BitVec.ofNat 64 16 ∧ st'.gpr .r8 = Src s ∧ st'.gpr .r10 = Dst s ∧
      st'.gpr .rax = W s + BitVec.ofNat 64 80 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r10 → r ≠ .rax → st'.gpr r = st.gpr r) ∧
      Kept s (16 * q) st'.mem ∧ Frame [kR' s] st.mem st'.mem ∧ st'.rd = st.rd ∧ st'.wr = st.wr := by
  have w64 : InRegions st.wr (W s + BitVec.ofNat 64 64) (64 / 8) := by rw [hwr]; exact w_in hp (by decide)
  have r₀ := slot_in hp hrd hwr (d := 0) (by decide)
  have r₁ := slot_in hp hrd hwr (d := 8) (by decide)
  have r₂ := slot_in hp hrd hwr (d := 16) (by decide)
  have r₅ := slot_in hp hrd hwr (d := 40) (by decide)
  have r₇ := slot_in hp hrd hwr (d := 56) (by decide)
  have sep : ∀ d : Nat, d + 8 ≤ 64 →
      Mem.Sep (W s + BitVec.ofNat 64 d) (64 / 8) (W s + BitVec.ofNat 64 64) (64 / 8) :=
    fun d hd => Offset.sep _ (.inl hd) (by omega) (by have := hp.w_w; omega)
  have s₀ := sep 0 (by decide)
  have s₁ := sep 8 (by decide)
  have s₂ := sep 16 (by decide)
  have s₅ := sep 40 (by decide)
  have s₇ := sep 56 (by decide)
  have k0 : st.mem.readW (W s + BitVec.ofNat 64 0) 64 = K s := by simpa using hk.ctx
  apply WP.of_runBlock
  refine ⟨_, by
    simp only [blocksArgs, wDone, wCtx, wRounds, wState, wSrc, wDst, wScr, imm]
    xrun [h11, hax, w64, r₀, r₁, r₂, r₅, r₇, s₀, s₁, s₂, s₅, s₇, k0, hk.rounds, hk.st, hk.src, hk.dst],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rfl, by rfl⟩
  all_goals try (simp (disch := first | decide | with_reducible assumption) only [gpr_setReg, gpr_arithFlags,
    ite_true, reduceCtorEq, ↓reduceIte, Mem.readW_writeW_sep, k0, hk.rounds, hk.st, hk.src, hk.dst, h11]; done)
  · intro r a b c d e f g; simp [gpr_setReg, gpr_arithFlags, a, b, c, d, e, f, g]
  · have k : ∀ d, d + 8 ≤ 64 → (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 (16 * q))).readW
        (W s + BitVec.ofNat 64 d) 64 = st.mem.readW (W s + BitVec.ofNat 64 d) 64 :=
      fun d hd => Mem.readW_writeW_sep (sep d hd) (by decide)
    have k0' : (st.mem.writeW (W s + BitVec.ofNat 64 64) (BitVec.ofNat 64 (16 * q))).readW (W s) 64 =
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

end VG.Proof.AesGcm.X86_64.StreamTo
