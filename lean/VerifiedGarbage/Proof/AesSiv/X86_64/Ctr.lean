import VerifiedGarbage.Proof.AesSiv.X86_64.XorBytes
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee

/-!
# AES-SIV on x86-64: CTR (`ctr`)

`ctrWhole` copies the counter `Q` (two byte-reversed words at `W + 64`) to
the counter block at `W + 96` and encrypts the first `k = ⌊L / 16⌋ mod 2³¹`
whole blocks of the data in place by one call of `vg_aes_ctr32`. `Q`'s last
32 bits are below `2³¹` (`Proof.AesSiv.counter_low`) and `k < 2³¹`, so its
counter blocks do not wrap around (`Proof.AesSiv.repeat_inc32`): the data is
then CTR's output on its first `16 k` bytes (`Proof.AesSiv.ctr32_ctrPart`).
It adds `k` to the counter as a 128-bit integer (`add_words`) and advances
the data past those bytes (`ctrWhole_wp`).

The rest (the last `L mod 16` bytes, and more only if `L ≥ 2³⁵`) is done a
block at a time: the counter `Q + i` is copied to the counter block,
`vg_aes_ctr32` writes its cipher to the zeroed keystream block at `W + 80`,
its first `min(16, left)` bytes are XORed into the data (`xorBytes_wp`), and
the counter is incremented as a 128-bit integer (`inc_words`). After block
`i` the data is CTR's output on its first `16 (i + 1)` bytes
(`ctrPart_step`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64 VG.WriteBytes
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat bytesAt_frame k0 zero2 zero2_bytes frame_store2 CallPre CallPost ctr_call
  ctr_rel)
open VG.Proof.CmacAes.Stream.X86_64 (copyMem copyMem_frame copyMem_bytes toNat_ofNat toNat_add_lt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.AesCcm.X86_64 (CtrCall CtrPost)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem ctxCiph_length (m : Mem) (C : Addr) (R : Nat) (y : List Byte) : (Spec.Siv.ctxCiph m C R y).length = 16 :=
  Proof.Cmac.aesWith_length _ _ _

/-! ## The whole blocks -/

/-- The whole blocks `ctrWhole` does, of `left` bytes. -/
abbrev wholeOf (left : Nat) : Nat := left / 16 % 2 ^ 31

theorem count_eq {left : Nat} (hl : left < 2 ^ 64) :
    BitVec.ofNat 64 left >>> 4 &&& BitVec.signExtend 64 (BitVec.ofNat 32 0x7fffffff) =
      BitVec.ofNat 64 (wholeOf left) := by
  rw [sx_ofNat (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hl, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show (0x7fffffff : Nat) < 2 ^ 64 by decide),
    show (0x7fffffff : Nat) = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show (2 : Nat) ^ 4 = 16 from rfl]
  unfold wholeOf
  omega

theorem wholeOf_le (left : Nat) : 16 * wholeOf left ≤ left := by
  show 16 * (left / 16 % 2 ^ 31) ≤ left; omega

theorem wholeOf_lt (left : Nat) : wholeOf left < 2 ^ 31 := Nat.mod_lt _ (by decide)

theorem wholeCount_ok {s : State} {left : Nat} (h14 : s.gpr .r14 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64) :
    ∃ s', runBlock isa wholeCount s = some s' ∧ s'.gpr .rcx = BitVec.ofNat 64 (wholeOf left) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [wholeCount, imm, runBlock_cons, runStep_some, exec, readSrc, execShift, Option.map_some]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [↓reduceIte, gpr_setReg, h14, count_eq hl]
  · intro r hr
    simp only [↓reduceIte, gpr_setReg, gpr_arithFlags, gpr_setFlags, hr]
  all_goals simp only [mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg,
    rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags, wr_setFlags]

/-- The arguments of `vg_aes_ctr32` on the first `k` whole blocks of the data:
`K2`'s schedule, the counter block at `W + 96`, the data, which it may write,
and the working space at `W + 256`. -/
theorem wargs (h : Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hsp : s.gpr .rsp = s₀.gpr .rsp) {k : Nat} (hk : 16 * k ≤ L)
    (rdi : s.gpr .rdi = C + BitVec.ofNat 64 272) (rsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 96) (rcx : s.gpr .rcx = P) (r8 : s.gpr .r8 = BitVec.ofNat 64 k)
    (r9 : s.gpr .r9 = W + BitVec.ofNat 64 256) :
    CtrCall s (C + BitVec.ofNat 64 272) (W + BitVec.ofNat 64 96) P (W + BitVec.ofNat 64 256) R k where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := h.rounds
  wrap := by have := h.wP; omega
  kc := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  kd := (hcp.sub_left (h.sC (by decide))).sub_right (Region.sub_prefix hk)
  ks := (h.c_w.sub_left (h.sC (by decide))).sub_right (h.sW (by decide))
  cd := (h.p_w.symm.sub_left (h.sW (by decide))).sub_right (Region.sub_prefix hk)
  cs := Offset.disjoint W (by omega) (by have := h.wW; omega) (by have := h.wW; omega)
  ds := (h.p_w.sub_left (Region.sub_prefix hk)).sub_right (h.sW (by decide))
  stkK := by rw [hsp]; exact (h.stk_c.sub_right (h.sC (by decide))).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  stkC := by rw [hsp]; exact (h.stk_w.sub_right (h.sW (by decide))).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  stkD := by rw [hsp]; exact (h.stk_p.sub_right (Region.sub_prefix hk)).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  stkS := by rw [hsp]; exact (h.stk_w.sub_right (h.sW (by decide))).sub_left (Offset.sub_below _ (by decide) (by
    have := h.sp; omega))
  reads := by
    rw [hrd, hwr]
    refine Covers.append_left (Covers.cons (cov_off h.ctxIn (by simp)) Covers.nil)
      (Covers.cons (Covers.right (cov_off h.workIn (by simp)))
        (Covers.cons (cov_base h.dataIn hk)
          (Covers.cons (Covers.right (cov_off h.workIn (by simp))) Covers.nil)))
  writes := by
    rw [hwr]
    exact Covers.cons (cov_off h.workIn (by simp)) (Covers.cons (cov_base hPw hk)
      (Covers.cons (cov_off h.workIn (by simp)) Covers.nil))

/-- `wholePre`: the counter block is `Q`, and the arguments of
`vg_aes_ctr32` on the first `wholeOf L` blocks of the data. -/
theorem wholePre_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) :
    ∃ s', runBlock isa wholePre s = some s' ∧ s'.gpr .rdi = C + BitVec.ofNat 64 272 ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 96 ∧ s'.gpr .rcx = P ∧
      s'.gpr .r8 = BitVec.ofNat 64 (wholeOf L) ∧ s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      Regs s₀ C D P W R L s' ∧
      s'.mem = copyMem s.mem (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 64) := by
  have r₀ := h.inRW hr.rd hr.wr (d := cntOff) (n := 8) (by decide)
  have r₈ := h.inRW hr.rd hr.wr (d := cntOff + 8) (n := 8) (by decide)
  have w₀ := h.inW hr.wr (d := cbOff) (n := 8) (by decide)
  have w₈ := h.inW hr.wr (d := cbOff + 8) (n := 8) (by decide)
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .rax (.mem (at_ .r15 cntOff)), .store (at_ .r15 cbOff) .rax,
       .mov .rax (.mem (at_ .r15 (cntOff + 8))), .store (at_ .r15 (cbOff + 8)) .rax] s = some s₁ ∧
      s₁.mem = copyMem s.mem (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 64) ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
        State.load64, State.store64, State.ea, offset_nat, Option.map_some, gpr_setReg,
        mem_setReg, rd_setReg, wr_setReg, hr.r15, r₀, r₈, w₀, w₈]
      rfl, ?_, ?_, ?_, ?_⟩
    · simp only [cbOff, cntOff, copyMem, Offset.add_add]
    · intro r hr'; simp [gpr_setReg, hr']
    all_goals rfl
  have hr₁ : Regs s₀ C D P W R L s₁ := hr.keep (fun r hr' => g₁ r (by rintro rfl; revert hr'; decide)) rd₁ wr₁
  obtain ⟨s₂, run₂, rcx₂, g₂, m₂, rd₂, wr₂⟩ := wholeCount_ok hr₁.r14 h.lt
  have hr₂ : Regs s₀ C D P W R L s₂ := hr₁.keep (fun r hr' => g₂ r (by rintro rfl; revert hr'; decide)) rd₂ wr₂
  obtain ⟨s₃, run₃, rdi, rsi, rdx, rcx, r8, r9, g₃, m₃, rd₃, wr₃⟩ : ∃ s₃, runBlock isa
      [.mov .r8 (.reg .rcx), .mov .rdi (.reg .rbx), .alu .add .rdi (imm 272), .mov .rsi (.reg .rbp),
       .mov .rdx (.reg .r15), .alu .add .rdx (imm cbOff), .mov .rcx (.reg .r13), .mov .r9 (.reg .r15),
       .alu .add .r9 (imm csOff)] s₂ = some s₃ ∧ s₃.gpr .rdi = C + BitVec.ofNat 64 272 ∧
      s₃.gpr .rsi = BitVec.ofNat 64 R ∧ s₃.gpr .rdx = W + BitVec.ofNat 64 96 ∧ s₃.gpr .rcx = P ∧
      s₃.gpr .r8 = BitVec.ofNat 64 (wholeOf L) ∧ s₃.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s₃.gpr r = s₂.gpr r) ∧ s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    refine ⟨_, by
      simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
        Option.map_some]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr' => ?_, ?_, ?_, ?_⟩
    rotate_left 6
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
      rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, hr₂.rbx, hr₂.rbp, hr₂.r13, hr₂.r15,
      rcx₂, cbOff, csOff, sx_ofNat (show 272 < 2 ^ 31 by decide), sx_ofNat (show 96 < 2 ^ 31 by decide),
      sx_ofNat (show 256 < 2 ^ 31 by decide)]
  refine ⟨s₃, by
      rw [wholePre, runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃],
    rdi, rsi, rdx, rcx, r8, r9, hr₂.keep g₃ rd₃ wr₃, by rw [m₃, m₂, m₁]⟩

/-- `wholePost`: `k` again, the counter plus `k` and the data advanced. -/
theorem wholePost_ok {s : State} {Q : Addr} {left : Nat} {hi lo : BitVec 64} (h15 : s.gpr .r15 = W)
    (h13 : s.gpr .r13 = Q) (h14 : s.gpr .r14 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64)
    (hhi : s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi)
    (hlo : s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 cntOff) 8)
    (r₈ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (cntOff + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 cntOff) 8) (w₈ : InRegions s.wr (W + BitVec.ofNat 64 (cntOff + 8)) 8) :
    ∃ s', runBlock isa wholePost s = some s' ∧
      (∃ hi' lo' : BitVec 64, s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (bswap64 hi')).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (bswap64 lo') ∧
        (hi' ++ lo' : BitVec 128) = (hi ++ lo : BitVec 128) + BitVec.ofNat 128 (wholeOf left)) ∧
      s'.gpr .r13 = Q + BitVec.ofNat 64 (16 * wholeOf left) ∧
      s'.gpr .r14 = BitVec.ofNat 64 (left - 16 * wholeOf left) ∧
      s'.zf = some (decide (left - 16 * wholeOf left = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hk := wholeOf_le left
  obtain ⟨s₁, run₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := wholeCount_ok h14 hl
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide), h15]
  have hhi₁ : s₁.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi := by rw [m₁, hhi]
  have hlo₁ : s₁.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo := by rw [m₁, hlo]
  rw [← rd₁, ← wr₁] at r₀ r₈
  rw [← wr₁] at w₀ w₈
  obtain ⟨s₂, run₂, ⟨hi', lo', m₂, hq⟩, r13₂, r14₂, zf₂, g₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .rax (.mem (at_ .r15 (cntOff + 8))), .bswap .rax, .mov .rdx (.mem (at_ .r15 cntOff)), .bswap .rdx,
       .alu .add .rax (.reg .rcx), .alu .adc .rdx (imm 0), .bswap .rax, .bswap .rdx,
       .store (at_ .r15 cntOff) .rdx, .store (at_ .r15 (cntOff + 8)) .rax,
       .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
       .alu .add .rcx (.reg .rcx), .alu .add .r13 (.reg .rcx), .alu .sub .r14 (.reg .rcx)] s₁ = some s₂ ∧
      (∃ hi' lo' : BitVec 64, s₂.mem = (s₁.mem.writeW (W + BitVec.ofNat 64 cntOff) (bswap64 hi')).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (bswap64 lo') ∧
        (hi' ++ lo' : BitVec 128) = (hi ++ lo : BitVec 128) + BitVec.ofNat 128 (wholeOf left)) ∧
      s₂.gpr .r13 = Q + BitVec.ofNat 64 (16 * wholeOf left) ∧
      s₂.gpr .r14 = BitVec.ofNat 64 (left - 16 * wholeOf left) ∧
      s₂.zf = some (decide (left - 16 * wholeOf left = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .r13 → r ≠ .r14 → s₂.gpr r = s₁.gpr r) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
        readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some,
        gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
        cf_setReg, cf_arithFlags, h15₁, r₀, r₈, w₀, w₈]
      rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨_, _, ?_, add_words hi lo (k := wholeOf left) (by have := wholeOf_lt left; omega)⟩
      simp only [mem_setReg, mem_arithFlags, hhi₁, hlo₁, rcx₁,
        Proof.Gcm.X86_64.bswap64_bswap64]
      rfl
    · simp only [reduceCtorEq, ↓reduceIte, gpr_setReg, gpr_arithFlags, rcx₁,
        g₁ _ (by decide : Reg.r13 ≠ .rcx), h13, dbl4 (wholeOf left) (by have := hk; omega)]
    · simp only [↓reduceIte, gpr_setReg, rcx₁,
        g₁ _ (by decide : Reg.r14 ≠ .rcx), h14, dbl4 (wholeOf left) (by have := hk; omega), Offset.ofNat_sub_ofNat hk]
    · simp only [zf_setReg, zf_arithFlags, rcx₁, g₁ _ (by decide : Reg.r14 ≠ .rcx), h14,
        dbl4 (wholeOf left) (by have := hk; omega), Offset.ofNat_sub_ofNat hk]
      rw [Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat (by omega)]
    · intro r h₁ h₂ h₃ h₄ h₅; simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅]
    all_goals rfl
  refine ⟨s₂, by rw [wholePost, runBlock_append, run₁, Option.bind_some, run₂],
    ⟨hi', lo', by rw [m₂, m₁], hq⟩, r13₂, r14₂, zf₂,
    fun r h₁ h₂ h₃ h₄ h₅ => by rw [g₂ r h₁ h₂ h₃ h₄ h₅, g₁ r h₂], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩

/-! ## A block -/

theorem ctrPre_ok (h : Env s₀ C D P W R L) {s : State} (hbx : s.gpr .rbx = C) (hbp : s.gpr .rbp = BitVec.ofNat 64 R)
    (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa ctrPre s = some s' ∧ s'.gpr .rdi = C + BitVec.ofNat 64 272 ∧
      s'.gpr .rsi = BitVec.ofNat 64 R ∧ s'.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s'.gpr .rcx = W + BitVec.ofNat 64 80 ∧ s'.gpr .r8 = 1 ∧ s'.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = copyMem (zero2 s.mem (W + BitVec.ofNat 64 80)) (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ := h.zero16_ok h15 hwr (d := ksOff) (by decide)
  have r₀ := h.inRW (s := s₁) (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (d := cntOff) (n := 8) (by decide)
  have r₈ := h.inRW (s := s₁) (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) (d := cntOff + 8) (n := 8) (by decide)
  have w₀ := h.inW (s := s₁) (by rw [wr₁, hwr]) (d := cbOff) (n := 8) (by decide)
  have w₈ := h.inW (s := s₁) (by rw [wr₁, hwr]) (d := cbOff + 8) (n := 8) (by decide)
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide), h15]
  obtain ⟨s₂, run₂, rdi, rsi, rdx, rcx, r8, r9, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .rax (.mem (at_ .r15 cntOff)), .store (at_ .r15 cbOff) .rax,
       .mov .rax (.mem (at_ .r15 (cntOff + 8))), .store (at_ .r15 (cbOff + 8)) .rax,
       .mov .rdi (.reg .rbx), .alu .add .rdi (imm 272), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15),
       .alu .add .rdx (imm cbOff), .mov .rcx (.reg .r15), .alu .add .rcx (imm ksOff), .mov32 .r8 (imm 1),
       .mov .r9 (.reg .r15), .alu .add .r9 (imm csOff)] s₁ = some s₂ ∧ s₂.gpr .rdi = C + BitVec.ofNat 64 272 ∧
      s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = W + BitVec.ofNat 64 96 ∧
      s₂.gpr .rcx = W + BitVec.ofNat 64 80 ∧ s₂.gpr .r8 = 1 ∧ s₂.gpr .r9 = W + BitVec.ofNat 64 256 ∧
      (∀ r ∈ calleeSaved, s₂.gpr r = s₁.gpr r) ∧
      s₂.mem = copyMem s₁.mem (W + BitVec.ofNat 64 96) (W + BitVec.ofNat 64 64) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by
      simp (config := {decide := true}) only [imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
        readSrc32, execAlu, State.load64, State.store64, State.ea, State.setReg32, offset_nat, Option.bind_some,
        Option.map_some, gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg,
        ite_true, ite_false, h15₁, r₀, r₈, w₀, w₈]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    rotate_left 6
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_setReg]
    all_goals simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags,
      rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags, ite_true, ite_false, g₁ _ (by decide : Reg.rbx ≠ .rax),
      g₁ _ (by decide : Reg.rbp ≠ .rax), hbx, hbp, cbOff, ksOff, csOff, cntOff, copyMem, Offset.add_add,
      sx_ofNat (show 272 < 2 ^ 31 by decide), sx_ofNat (show 96 < 2 ^ 31 by decide),
      sx_ofNat (show 80 < 2 ^ 31 by decide), sx_ofNat (show 256 < 2 ^ 31 by decide)]
    all_goals first | rfl | trivial
  refine ⟨s₂, by rw [ctrPre, runBlock_append, run₁, Option.bind_some, run₂], rdi, rsi, rdx, rcx, r8, r9,
    fun r hr => by rw [g₂ r hr, g₁ r (by rintro rfl; simp [calleeSaved] at hr)], by rw [m₂, m₁]; rfl, by rw [rd₂, rd₁],
    by rw [wr₂, wr₁]⟩

theorem ctrMin_wp {s : State} {left : Nat} (h14 : s.gpr .r14 = BitVec.ofNat 64 left) (hl : left < 2 ^ 64) :
    WP isa ctrMin s fun s' => s'.gpr .rcx = BitVec.ofNat 64 (min 16 left) ∧
      (∀ r, r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, rcx₁, cf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov32 .rcx (imm 16), .alu .cmp .r14 (.reg .rcx)] s
      = some s₁ ∧ s₁.gpr .rcx = BitVec.ofNat 64 16 ∧ s₁.cf = some (decide (left < 16)) ∧
      (∀ r, r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu, State.setReg32,
        Option.bind_some, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · rw [cf_arithFlags]
      simp only [gpr_setReg, ite_false, ite_true, reduceCtorEq, h14, toNat_ofNat hl]
      rfl
    · intro r hr; simp [gpr_setReg, hr]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (left < 16)) cf₁ (fun hb => ?_) (fun hb => WP.block_nil ?_)
  · have hlt : left < 16 := of_decide_eq_true hb
    refine WP.of_runBlock ⟨_, by
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
      rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [gpr_setReg_self, g₁ _ (by decide), h14, Nat.min_eq_right (by omega)]
    · intro r hr; rw [gpr_setReg_of_ne _ _ hr, g₁ r hr]
    · exact m₁
    · exact rd₁
    · exact wr₁
  · have hge : ¬ left < 16 := of_decide_eq_false hb
    exact ⟨by rw [rcx₁, Nat.min_eq_left (by omega)], g₁, m₁, rd₁, wr₁⟩

theorem ctrPost_ok {s : State} {Q : Addr} {left n : Nat} {hi lo : BitVec 64} (h15 : s.gpr .r15 = W)
    (h13 : s.gpr .r13 = Q) (h14 : s.gpr .r14 = BitVec.ofNat 64 left) (hrcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hn : n ≤ left) (hl : left < 2 ^ 64)
    (hhi : s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi)
    (hlo : s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 cntOff) 8)
    (r₈ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 (cntOff + 8)) 8)
    (w₀ : InRegions s.wr (W + BitVec.ofNat 64 cntOff) 8) (w₈ : InRegions s.wr (W + BitVec.ofNat 64 (cntOff + 8)) 8) :
    ∃ s', runBlock isa ctrPost s = some s' ∧
      (∃ hi' lo' : BitVec 64, s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (bswap64 hi')).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (bswap64 lo') ∧
        (hi' ++ lo' : BitVec 128) = (hi ++ lo : BitVec 128) + 1) ∧
      s'.gpr .r13 = Q + BitVec.ofNat 64 16 ∧ s'.gpr .r14 = BitVec.ofNat 64 (left - n) ∧
      s'.zf = some (decide (left - n = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [ctrPost, imm, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc, execAlu, State.load64, State.store64, State.ea, offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, mem_arithFlags, rd_setReg, rd_arithFlags, wr_setReg, wr_arithFlags,
      cf_setReg, cf_arithFlags, ite_true, ite_false, h15, r₀, r₈, w₀, w₈]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨_, _, ?_, inc_words hi lo⟩
    simp (config := {decide := true}) only [mem_setReg, mem_arithFlags,
      hhi, hlo, Proof.Gcm.X86_64.bswap64_bswap64]
    rfl
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h13,
      sx_ofNat (show 16 < 2 ^ 31 by decide)]
  · simp (config := {decide := true}) only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h14, hrcx,
      Offset.ofNat_sub_ofNat hn]
  · simp (config := {decide := true}) only [zf_setReg, zf_arithFlags,
      h14, hrcx, Offset.ofNat_sub_ofNat hn]
    rw [Proof.CmacAes.Stream.X86_64.beq_zero_iff, toNat_ofNat (by omega)]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_setReg, h₁, h₂, h₃, h₄]
  all_goals rfl

/-! ## The loop -/

/-- The regions CTR writes: the data, the counter, keystream and counter
blocks, the working space of `vg_aes_ctr32` and the stack. -/
abbrev ctrRegions (W P : Addr) (L : Nat) (sp : Addr) : List Region :=
  [⟨P, L⟩, ⟨W + BitVec.ofNat 64 64, 48⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩, below sp 16]

/-- The state at the start of block `i`: the data is CTR's output on its
first `16 i` bytes, the counter is `Q + i`, and the context (so the
cipher) is as at the start. -/
structure CInv (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (i : Nat) (s : State) :
    Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r13 : s.gpr .r13 = P + BitVec.ofNat 64 (16 * i)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (L - 16 * i)
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  le : 16 * i ≤ L
  cnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
    s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧
    (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q + BitVec.ofNat 128 i
  data : Spec.Aes.bytesAt s.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i)
  frame : Frame (ctrRegions W P L (s₀.gpr .rsp)) m₀ s.mem

/-- What the setup of a block, the call and the length leave. -/
structure CHead (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q : List Byte) (i : Nat) (s s' : State) :
    Prop where
  rbx : s'.gpr .rbx = C
  rbp : s'.gpr .rbp = BitVec.ofNat 64 R
  r12 : s'.gpr .r12 = D
  r13 : s'.gpr .r13 = P + BitVec.ofNat 64 (16 * i)
  r14 : s'.gpr .r14 = BitVec.ofNat 64 (L - 16 * i)
  r15 : s'.gpr .r15 = W
  rsp : s'.gpr .rsp = s₀.gpr .rsp
  rcx : s'.gpr .rcx = BitVec.ofNat 64 (min 16 (L - 16 * i))
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  ks : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 80) 16 = Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i
  frame : Frame [⟨W + BitVec.ofNat 64 80, 32⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩, below (s₀.gpr .rsp) 16] s.mem s'.mem

theorem ctr_head (v : Ctr32Impl) (h : Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) {m₀ : Mem}
    {q x : List Byte} {i : Nat} {s : State} (hi : CInv s₀ C D P W R L m₀ q x i s) {k : Prog isa} {Q : State → Prop}
    (hk : ∀ s', CHead s₀ C D P W R L m₀ q i s s' → WP isa k s' Q) :
    WP isa (.seq (.block ctrPre) (.seq (.call v.callee.name v.callee.code) (.seq ctrMin k))) s Q := by
  have hwW := h.wW
  have hlt := h.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, g₁, m₁, rd₁, wr₁⟩ := ctrPre_ok h hi.rbx hi.rbp hi.r15 hi.rd hi.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
    Offset.disjoint W hs (by omega) (by omega)
  have s₉₆ : Region.Sub ⟨W + BitVec.ofNat 64 96, 16⟩ ⟨W + BitVec.ofNat 64 80, 32⟩ := by
    rw [show W + BitVec.ofNat 64 96 = W + BitVec.ofNat 64 80 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
    exact Offset.sub_base _ (by decide)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 80, 32⟩] s.mem s₁.mem := by
    rw [m₁, zero2]
    exact ((frame_store2 _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩).trans
      ((copyMem_frame _ _ _).sub fun r hr => ⟨⟨W + BitVec.ofNat 64 80, 32⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact s₉₆⟩)
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 80) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, bytesAt_frame (copyMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dWW 80 16 96 16 (by omega) (by omega) (by omega))
      (by decide), zero2_bytes]
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [g₁ _ (by decide), hi.rsp]
  have hc := h.cargs (s := s₁) (by rw [rd₁, hi.rd]) (by rw [wr₁, hi.wr]) rsp₁ rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ hz
  refine WP.seq (WP.mono (ctr_call v hc) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr : r ∈ calleeSaved) : s₂.gpr r = s.gpr r := by rw [h₂.saved r hr, g₁ r hr]
  refine WP.seq (WP.mono (ctrMin_wp (left := L - 16 * i) (by rw [g₂ _ (by decide), hi.r14]) (by omega))
    fun s₃ ⟨rcx₃, g₃, m₃, rd₃, wr₃⟩ => hk s₃ ?_)
  have g₃' (r : Reg) (hr : r ∈ calleeSaved) : s₃.gpr r = s.gpr r := by
    rw [g₃ r (by rintro rfl; simp [calleeSaved] at hr), g₂ r hr]
  have f₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 80, 16⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩,
      below (s₀.gpr .rsp) 8] s₁.mem s₂.mem := by rw [← rsp₁]; exact h₂.frame
  refine ⟨by rw [g₃' _ (by decide), hi.rbx], by rw [g₃' _ (by decide), hi.rbp], by rw [g₃' _ (by decide), hi.r12],
    by rw [g₃' _ (by decide), hi.r13], by rw [g₃' _ (by decide), hi.r14], by rw [g₃' _ (by decide), hi.r15],
    by rw [g₃' _ (by decide), hi.rsp], rcx₃, by rw [rd₃, h₂.rd, rd₁, hi.rd], by rw [wr₃, h₂.wr, wr₁, hi.wr], ?_, ?_⟩
  · -- The keystream block: the cipher of the counter block, a copy of `Q + i`.
    obtain ⟨hi', lo', hhi, hlo, hq⟩ := hi.cnt
    have dC (r : Region) (hr : r ∈ ctrRegions W P L (s₀.gpr .rsp)) :
        (⟨C + BitVec.ofNat 64 272, 16 * (R + 1)⟩ : Region).Disjoint r := by
      have sub := h.sC (d := 272) (n := 16 * (R + 1)) (by omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hcp.sub_left sub
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
      · exact (h.c_w.sub_left sub).sub_right (h.sW (by decide))
      · exact (h.stk_c.sub_right sub).symm
    have sch : Spec.Aes.bytesAt s₁.mem (C + BitVec.ofNat 64 272) (16 * (R + 1)) =
        Spec.Aes.bytesAt m₀ (C + BitVec.ofNat 64 272) (16 * (R + 1)) := by
      rw [bytesAt_frame f₁ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (h.c_w.sub_left (h.sC (by omega))).sub_right (h.sW (by decide))) (by omega),
        bytesAt_frame hi.frame dC (by omega)]
    have hhi' : s.mem.readW (W + BitVec.ofNat 64 64) 64 = bswap64 hi' := hhi
    have hlo' : s.mem.readW (W + BitVec.ofNat 64 (64 + 8)) 64 = bswap64 lo' := hlo
    have cb : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 96) 16 = Spec.Siv.be128 (Spec.Siv.beNat q + i) := by
      rw [m₁, copyMem_bytes _ (dWW 96 16 64 16 (by omega) (by omega) (by omega)), zero2,
        bytesAt_frame (frame_store2 _ _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dWW 64 16 80 16 (by omega) (by omega) (by omega))
          (by decide),
        Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Offset.add_add, hhi', hlo',
        VG.Proof.CmacAes.X86_64.le8_bswap, hq, be128_add]
    rw [m₃, h₂.out, sch, cb]
    rfl
  · rw [m₃]
    exact (f₁.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, by simp, s₉₆⟩
      · exact ⟨⟨W + BitVec.ofNat 64 80, 32⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, Offset.sub_below _ (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩)

/-- The state after the last block: the data is CTR's output. -/
structure CDone (s₀ : State) (C D P W : Addr) (R L : Nat) (m₀ : Mem) (q x : List Byte) (s : State) : Prop where
  rbx : s.gpr .rbx = C
  rbp : s.gpr .rbp = BitVec.ofNat 64 R
  r12 : s.gpr .r12 = D
  r15 : s.gpr .r15 = W
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : Spec.Aes.bytesAt s.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph m₀ C R) q x
  frame : Frame (ctrRegions W P L (s₀.gpr .rsp)) m₀ s.mem

theorem ctr_tail (h : Env s₀ C D P W R L) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {m₀ : Mem} {q x : List Byte} {i : Nat} {s s₃ : State}
    (hi : CInv s₀ C D P W R L m₀ q x i s) (hiL : 16 * i < L) (hh : CHead s₀ C D P W R L m₀ q i s s₃) :
    WP isa (.seq xorBytes (.block ctrPost)) s₃ fun s' =>
      (L - 16 * i ≤ 16 ∧ s'.zf = some true ∧ CDone s₀ C D P W R L m₀ q x s') ∨
      (16 < L - 16 * i ∧ s'.zf = some false ∧ CInv s₀ C D P W R L m₀ q x (i + 1) s') := by
  have hwW := h.wW
  have hwP := h.wP
  have hlt := h.lt
  have hxL : x.length = L := by
    have := congrArg List.length hi.data
    rw [Proof.Cmac.bytesAt_length, length_ctrPart] at this; exact this.symm
  have hn : 0 < min 16 (L - 16 * i) := by omega
  have hn16 : min 16 (L - 16 * i) ≤ 16 := Nat.min_le_left _ _
  have dP (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region), ⟨W + BitVec.ofNat 64 256, 2048⟩,
      below (s₀.gpr .rsp) 16]) : (⟨P, L⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.p_w.sub_right (h.sW (by decide))
    · exact h.p_w.sub_right (h.sW (by decide))
    · exact h.stk_p.symm
  have data₃ : Spec.Aes.bytesAt s₃.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i) := by
    rw [bytesAt_frame hh.frame dP (by omega), hi.data]
  have sQ : Region.Sub ⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩ ⟨P, L⟩ := h.sP (by omega)
  refine WP.seq (WP.mono (xorBytes_wp s₃ (Q := P + BitVec.ofNat 64 (16 * i)) (K := W + BitVec.ofNat 64 80) hn hn16
    hh.r13 hh.r15 rfl hh.rcx
    (fun j hj => by rw [Offset.add_add]; exact h.inRP hh.rd hh.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inRW hh.rd hh.wr (by omega))
    (fun j hj => by rw [Offset.add_add]; exact h.inWP hPw hh.wr (by omega))
    ((h.p_w.sub_left sQ).sub_right (h.sW (by omega)))
    (by rw [toNat_add_lt P hwP (show 16 * i < L by omega)]; omega)) fun s₄ h₄ => ?_)
  obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hi.cnt
  have hlx : (Spec.Cmac.xor (Spec.Aes.bytesAt s₃.mem (P + BitVec.ofNat 64 (16 * i)) (min 16 (L - 16 * i)))
      (Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)))).length = min 16 (L - 16 * i) := by
    rw [Proof.Cmac.length_xor, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length, Nat.min_self]
  have fx : Frame [⟨P + BitVec.ofNat 64 (16 * i), min 16 (L - 16 * i)⟩] s₃.mem s₄.mem := by
    rw [h₄.mem]; exact writeBytes_frame _ _ _ (by rw [hlx]; exact Region.contains_self _ _)
  have dW (d n : Nat) (hd : d + n ≤ 2560) (r : Region) (hr : r ∈ [(⟨P + BitVec.ofNat 64 (16 * i),
      min 16 (L - 16 * i)⟩ : Region)]) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.p_w.sub_left sQ).symm.sub_left (h.sW hd)
  have dH (d : Nat) (hd : d + 8 ≤ 80) (r : Region) (hr : r ∈ [(⟨W + BitVec.ofNat 64 80, 32⟩ : Region),
      ⟨W + BitVec.ofNat 64 256, 2048⟩, below (s₀.gpr .rsp) 16]) : (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact (h.stk_w.sub_right (h.sW (by omega))).symm
  have c₄ (d : Nat) (hd : d + 8 ≤ 80) : s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [fx.readW (w := 64) (Region.contains_self _ _) (dW d 8 (by omega)) (by decide),
      hh.frame.readW (w := 64) (Region.contains_self _ _) (dH d hd) (by decide)]
  have g₄ (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .rdx) (h₃ : r ≠ .r10) := h₄.other r h₁ h₂ h₃
  obtain ⟨s₅, run₅, ⟨hi₁, lo₁, m₅, hq₁⟩, r13₅, r14₅, zf₅, g₅, rd₅, wr₅⟩ := ctrPost_ok (W := W) (s := s₄)
    (left := L - 16 * i) (n := min 16 (L - 16 * i)) (hi := hi₀) (lo := lo₀)
    (by rw [g₄ _ (by decide) (by decide) (by decide), hh.r15]) (by rw [g₄ _ (by decide) (by decide) (by decide), hh.r13])
    (by rw [g₄ _ (by decide) (by decide) (by decide), hh.r14]) (by rw [g₄ _ (by decide) (by decide) (by decide), hh.rcx])
    (Nat.min_le_right _ _) (by omega) (by rw [c₄ cntOff (by decide)]; exact hhi)
    (by rw [c₄ (cntOff + 8) (by decide)]; exact hlo)
    (h.inRW (by rw [h₄.rd, hh.rd]) (by rw [h₄.wr, hh.wr]) (by decide))
    (h.inRW (by rw [h₄.rd, hh.rd]) (by rw [h₄.wr, hh.wr]) (by decide))
    (h.inW (by rw [h₄.wr, hh.wr]) (by decide)) (h.inW (by rw [h₄.wr, hh.wr]) (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have fp : Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s₄.mem s₅.mem := by
    rw [m₅]
    have c64 : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Contains (W + BitVec.ofNat 64 cntOff) (64 / 8) := by
      show Region.Contains _ (W + BitVec.ofNat 64 64) 8
      simpa using Offset.contains_base (W + BitVec.ofNat 64 64) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c64).writeW
      (List.mem_singleton_self _) _ (by
        rw [show W + BitVec.ofNat 64 (cntOff + 8) = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
          rw [Offset.add_add]; rfl]
        exact Offset.contains_base _ (by decide) (by decide))
  -- The data.
  have kt : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 80) (min 16 (L - 16 * i)) =
      (Siv.ksBlock (Spec.Siv.ctxCiph m₀ C R) q i).take (min 16 (L - 16 * i)) := by
    rw [← hh.ks]
    have := take_bytesAt s₃.mem (W + BitVec.ofNat 64 80) (a := min 16 (L - 16 * i)) (b := 16 - min 16 (L - 16 * i))
    rw [show min 16 (L - 16 * i) + (16 - min 16 (L - 16 * i)) = 16 by omega] at this
    exact this.symm
  have st := ctrPart_step (Spec.Siv.ctxCiph m₀ C R) (ctxCiph_length m₀ C R) q x s₃.mem P (i := i)
    (n := min 16 (L - 16 * i)) (by omega) hn16 (by omega) (by rw [hxL]; exact data₃)
  rw [hxL, ← kt, ← h₄.mem] at st
  have data₅ : Spec.Aes.bytesAt s₅.mem P L = ctrPart (Spec.Siv.ctxCiph m₀ C R) q x (16 * i + min 16 (L - 16 * i)) := by
    rw [bytesAt_frame fp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.p_w.sub_right (h.sW (by decide))) (by omega), st]
  -- The frame.
  have frame : Frame (ctrRegions W P L (s₀.gpr .rsp)) m₀ s₅.mem :=
    ((hi.frame.trans (hh.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
          rw [show W + BitVec.ofNat 64 80 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 16 by rw [Offset.add_add]]
          exact Offset.sub_base _ (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)).trans
      (fx.sub fun r hr => ⟨⟨P, L⟩, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact sQ⟩)).trans
      (fp.sub fun r hr => ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩)
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .rdx) (h₃ : r ≠ .r10) (h₅ : r ≠ .r13) (h₆ : r ≠ .r14) :
      s₅.gpr r = s₃.gpr r := by rw [g₅ r h₁ h₂ h₅ h₆, g₄ r h₁ h₂ h₃]
  by_cases hfin : L - 16 * i ≤ 16
  · left
    have hn' : min 16 (L - 16 * i) = L - 16 * i := Nat.min_eq_right hfin
    refine ⟨hfin, by rw [zf₅, hn']; simp, ⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r12],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rsp],
      by rw [rd₅, h₄.rd, hh.rd], by rw [wr₅, h₄.wr, hh.wr], ?_, frame⟩⟩
    rw [data₅, hn', show 16 * i + (L - 16 * i) = L by omega]
    exact ctrPart_all _ (ctxCiph_length m₀ C R) q x (by omega)
  · right
    have hn' : min 16 (L - 16 * i) = 16 := Nat.min_eq_left (by omega)
    refine ⟨by omega, by rw [zf₅, hn']; simp; omega,
      ⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbx],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rbp],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r12],
      by rw [r13₅, Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega],
      by rw [r14₅, hn', show L - 16 * i - 16 = L - 16 * (i + 1) by omega],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.r15],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hh.rsp],
      by rw [rd₅, h₄.rd, hh.rd], by rw [wr₅, h₄.wr, hh.wr], by omega, ⟨hi₁, lo₁, ?_, ?_, ?_⟩, ?_, frame⟩⟩
    · rw [m₅, Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide)
        (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
    · rw [m₅, Mem.readW_writeW_self64]
    · rw [hq₁, hq, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [data₅, hn', show 16 * i + 16 = 16 * (i + 1) by omega]


/-! ## The whole blocks, by one call -/

/-- `ctrWhole`, from the registers and the counter `Q`, whose last 32 bits
are below `2³¹`: the state at the start of block `wholeOf L` of the rest,
with ZF set when no data is left. -/
theorem ctrWhole_wp (v : Ctr32Impl) (h : Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hr : Regs s₀ C D P W R L s) {q : List Byte}
    (hql : q.length = 16) (hlow : Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31)
    (hcnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q) :
    WP isa (ctrWhole v.callee) s fun t => t.zf = some (decide (L - 16 * wholeOf L = 0)) ∧
      CInv s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) (wholeOf L) t := by
  have hwW := h.wW
  have hwP := h.wP
  have hlt := h.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hk := wholeOf_le L
  have hk31 := wholeOf_lt L
  obtain ⟨hi₀, lo₀, hhi, hlo, hq⟩ := hcnt
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, hr₁, m₁⟩ := wholePre_ok h hr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (Proof.AesCcm.X86_64.ctr_call v
    (wargs h hcp hPw hr₁.rd hr₁.wr hr₁.rsp hk rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁)) fun s₂ h₂ => ?_)
  have hr₂ : Regs s₀ C D P W R L s₂ := hr₁.keep h₂.saved h₂.rd h₂.wr
  have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
      (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
    Offset.disjoint W hs (by omega) (by omega)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩] s.mem s₁.mem := by rw [m₁]; exact copyMem_frame _ _ _
  have f₂ : Frame [⟨W + BitVec.ofNat 64 96, 16⟩, ⟨P, 16 * wholeOf L⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩,
      below (s₀.gpr .rsp) 8] s₁.mem s₂.mem := by rw [← hr₁.rsp]; exact h₂.frame
  have stk8 : Region.Sub (below (s₀.gpr .rsp) 8) (below (s₀.gpr .rsp) 16) :=
    Offset.sub_below _ (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)
  -- What the copy and the call write, and what they do not.
  have dW (d n : Nat) (hd : d + n ≤ 2560) (h1 : d + n ≤ 96 ∨ 112 ≤ d) (h2 : d + n ≤ 256) (r : Region)
      (hr' : r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨P, 16 * wholeOf L⟩, ⟨W + BitVec.ofNat 64 256, 2048⟩,
        below (s₀.gpr .rsp) 8]) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact dWW d n 96 16 h1 hd (by decide)
    · exact (h.p_w.sub_left (Region.sub_prefix hk)).symm.sub_left (h.sW hd)
    · exact dWW d n 256 2048 (.inl h2) hd (by decide)
    · exact ((h.stk_w.sub_right (h.sW hd)).sub_left stk8).symm
  have d₁ (d n : Nat) (hd : d + n ≤ 2560) (h1 : d + n ≤ 96 ∨ 112 ≤ d) (r : Region)
      (hr' : r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)]) : (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    simp only [List.mem_singleton] at hr'; subst hr'; exact dWW d n 96 16 h1 hd (by decide)
  have c₂ (d : Nat) (hd : d + 8 ≤ 96) :
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := by
    rw [f₂.readW (w := 64) (Region.contains_self _ _) (dW d 8 (by omega) (.inl hd) (by omega)) (by decide),
      f₁.readW (w := 64) (Region.contains_self _ _) (d₁ d 8 (by omega) (.inl hd)) (by decide)]
  obtain ⟨s₃, run₃, ⟨hi₁, lo₁, m₃, hq₁⟩, r13₃, r14₃, zf₃, g₃, rd₃, wr₃⟩ := wholePost_ok (W := W) (s := s₂)
    (left := L) (hi := hi₀) (lo := lo₀) hr₂.r15 hr₂.r13 hr₂.r14 hlt
    (by rw [c₂ cntOff (by decide)]; exact hhi) (by rw [c₂ (cntOff + 8) (by decide)]; exact hlo)
    (h.inRW hr₂.rd hr₂.wr (by decide)) (h.inRW hr₂.rd hr₂.wr (by decide)) (h.inW hr₂.wr (by decide))
    (h.inW hr₂.wr (by decide))
  refine WP.of_runBlock ⟨s₃, run₃, zf₃, ?_⟩
  have keep (r : Reg) (h₁ : r ≠ .rax) (h₂ : r ≠ .rcx) (h₃ : r ≠ .rdx) (h₄ : r ≠ .r13) (h₅ : r ≠ .r14) :
      s₃.gpr r = s₂.gpr r := g₃ r h₁ h₂ h₃ h₄ h₅
  have fp : Frame [⟨W + BitVec.ofNat 64 64, 16⟩] s₂.mem s₃.mem := by
    rw [m₃]
    have c64 : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Contains (W + BitVec.ofNat 64 cntOff) (64 / 8) := by
      show Region.Contains _ (W + BitVec.ofNat 64 64) 8
      simpa using Offset.contains_base (W + BitVec.ofNat 64 64) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c64).writeW
      (List.mem_singleton_self _) _ (by
        rw [show W + BitVec.ofNat 64 (cntOff + 8) = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 8 by
          rw [Offset.add_add]; rfl]
        exact Offset.contains_base _ (by decide) (by decide))
  -- The counter block is `Q`, whose counter blocks do not wrap around.
  have hhi' : s.mem.readW (W + BitVec.ofNat 64 64) 64 = bswap64 hi₀ := hhi
  have hlo' : s.mem.readW (W + BitVec.ofNat 64 (64 + 8)) 64 = bswap64 lo₀ := hlo
  have hcb : Spec.Gcm.blockAt s₁.mem (W + BitVec.ofNat 64 96) = Spec.Gcm.ofBytes q := by
    rw [Spec.Gcm.blockAt, m₁, copyMem_bytes _ (dWW 96 16 64 16 (by omega) (by omega) (by omega)),
      Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Offset.add_add, hhi', hlo',
      VG.Proof.CmacAes.X86_64.le8_bswap, hq, Proof.Cmac.ofBytes_toBytes]
  have hc₂ := ctr32_ctrPart (m := s₁.mem) (m' := s₂.mem) (K := C + BitVec.ofNat 64 272)
    (C := W + BitVec.ofNat 64 96) (D := P) (R := R) (q := q) (k := wholeOf L)
    (fun i hi => by rw [hcb]; exact repeat_inc32 hql (k := wholeOf L) (by omega) i hi) h₂.out
  have dC : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)], (⟨C, 512⟩ : Region).Disjoint r := fun r hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact h.c_w.sub_right (h.sW (by decide))
  have dP (a n : Nat) (ha : a + n ≤ L) : ∀ r ∈ [(⟨W + BitVec.ofNat 64 96, 16⟩ : Region)],
      (⟨P + BitVec.ofNat 64 a, n⟩ : Region).Disjoint r := fun r hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'; exact (h.p_w.sub_left (h.sP ha)).sub_right (h.sW (by decide))
  have sch : Spec.Siv.schedCiph s₁.mem (C + BitVec.ofNat 64 272) R = Spec.Siv.ctxCiph s.mem C R := by
    rw [← ctxCiph_frame f₁ dC hRb]; rfl
  have pd₁ : Spec.Aes.bytesAt s₁.mem P (16 * wholeOf L) = Spec.Aes.bytesAt s.mem P (16 * wholeOf L) := by
    have := bytesAt_frame f₁ (dP 0 (16 * wholeOf L) (by omega)) (by omega)
    rwa [k0] at this
  rw [sch, pd₁] at hc₂
  -- The rest of the data, as it was.
  have rest : Spec.Aes.bytesAt s₂.mem (P + BitVec.ofNat 64 (16 * wholeOf L)) (L - 16 * wholeOf L) =
      Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (16 * wholeOf L)) (L - 16 * wholeOf L) := by
    have hsub : Region.Sub ⟨P + BitVec.ofNat 64 (16 * wholeOf L), L - 16 * wholeOf L⟩ ⟨P, L⟩ := h.sP (by omega)
    rw [bytesAt_frame f₂ (fun r hr' => ?_) (by omega), bytesAt_frame f₁ (dP _ _ (by omega)) (by omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact (h.p_w.sub_left hsub).sub_right (h.sW (by decide))
    · exact (Offset.base_disjoint P (e := 16 * wholeOf L) (n := L - 16 * wholeOf L) (k := 16 * wholeOf L)
        (by omega) (by omega)).symm
    · exact (h.p_w.sub_left hsub).sub_right (h.sW (by decide))
    · exact ((h.stk_p.sub_right hsub).sub_left stk8).symm
  have e := Proof.Cmac.Stream.bytesAt_append s₂.mem P (16 * wholeOf L) (L - 16 * wholeOf L)
  rw [show 16 * wholeOf L + (L - 16 * wholeOf L) = L by omega] at e
  have e₀ := Proof.Cmac.Stream.bytesAt_append s.mem P (16 * wholeOf L) (L - 16 * wholeOf L)
  rw [show 16 * wholeOf L + (L - 16 * wholeOf L) = L by omega] at e₀
  have hpa := ctrPart_append (Spec.Siv.ctxCiph s.mem C R) q (Spec.Aes.bytesAt s.mem P (16 * wholeOf L))
    (Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (16 * wholeOf L)) (L - 16 * wholeOf L))
  rw [Proof.Cmac.bytesAt_length] at hpa
  have data : Spec.Aes.bytesAt s₃.mem P L =
      ctrPart (Spec.Siv.ctxCiph s.mem C R) q (Spec.Aes.bytesAt s.mem P L) (16 * wholeOf L) := by
    rw [bytesAt_frame fp (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'; exact h.p_w.sub_right (h.sW (by decide))) (by omega),
      e, hc₂, rest, e₀, hpa]
  -- The frame.
  have s₉₆ : Region.Sub ⟨W + BitVec.ofNat 64 96, 16⟩ ⟨W + BitVec.ofNat 64 64, 48⟩ := by
    rw [show W + BitVec.ofNat 64 96 = W + BitVec.ofNat 64 64 + BitVec.ofNat 64 32 by rw [Offset.add_add]]
    exact Offset.sub_base _ (by decide)
  have frame : Frame (ctrRegions W P L (s₀.gpr .rsp)) s.mem s₃.mem :=
    ((f₁.sub fun r hr' => ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
        simp only [List.mem_singleton] at hr'; subst hr'; exact s₉₆⟩).trans
      (f₂.sub fun r hr' => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl
        · exact ⟨_, by simp, s₉₆⟩
        · exact ⟨⟨P, L⟩, by simp, Region.sub_prefix hk⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨_, by simp, stk8⟩)).trans
      (fp.sub fun r hr' => ⟨⟨W + BitVec.ofNat 64 64, 48⟩, by simp, by
        simp only [List.mem_singleton] at hr'; subst hr'; exact Region.sub_prefix (by decide)⟩)
  refine ⟨by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbx],
    by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rbp],
    by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r12], r13₃, r14₃,
    by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.r15],
    by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hr₂.rsp],
    by rw [rd₃, hr₂.rd], by rw [wr₃, hr₂.wr], hk, ⟨hi₁, lo₁, ?_, ?_, ?_⟩, data, frame⟩
  · rw [m₃, Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide)
      (by decide) (by decide)) (by decide), Mem.readW_writeW_self64]
  · rw [m₃, Mem.readW_writeW_self64]
  · rw [hq₁, hq]

/-! ## The whole -/

/-- What `ctr` leaves: the data is CTR's output, and the registers are back. -/
structure CPost' (s₀ : State) (C D P W : Addr) (R L : Nat) (q : List Byte) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  data : Spec.Aes.bytesAt s'.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) q (Spec.Aes.bytesAt s.mem P L)
  frame : Frame (ctrRegions W P L (s₀.gpr .rsp)) s.mem s'.mem

theorem ctrEnd_ok (h : Env s₀ C D P W R L) {s : State} (h15 : s.gpr .r15 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (h208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P)
    (h216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L) :
    ∃ s', runBlock isa [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))] s = some s' ∧
      s'.gpr .r13 = P ∧ s'.gpr .r14 = BitVec.ofNat 64 L ∧ (∀ r, r ≠ .r13 → r ≠ .r14 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₁ := h.inRW hrd hwr (d := dataOff) (n := 8) (by decide)
  have r₂ := h.inRW hrd hwr (d := lenOff) (n := 8) (by decide)
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h15, r₁, ite_true, gpr_setReg_of_ne _ _ (show Reg.r15 ≠ .r13 by decide), rd_setReg, wr_setReg,
      mem_setReg, r₂]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h208]
  · simp [gpr_setReg, h216]
  · intro r h₁ h₂; simp [gpr_setReg, h₁, h₂]
  all_goals rfl

theorem ctr_wp (v : Ctr32Impl) (h : Env s₀ C D P W R L) (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩)
    (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State} (hr : Regs s₀ C D P W R L s) {q : List Byte}
    (hql : q.length = 16) (hlow : Spec.Siv.beNat q % 2 ^ 32 < 2 ^ 31)
    (hcnt : ∃ hi lo : BitVec 64, s.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = bswap64 hi ∧
      s.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = bswap64 lo ∧ (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes q)
    (h208 : s.mem.readW (W + BitVec.ofNat 64 dataOff) 64 = P)
    (h216 : s.mem.readW (W + BitVec.ofNat 64 lenOff) 64 = BitVec.ofNat 64 L) :
    WP isa (ctr v.callee) s (CPost' s₀ C D P W R L q s) := by
  have hwW := h.wW
  have hlt := h.lt
  -- The slots of the data and its length, outside what CTR writes.
  have dS (d : Nat) (hd : 208 ≤ d) (hd' : d + 8 ≤ 256) (r : Region) (hr' : r ∈ ctrRegions W P L (s₀.gpr .rsp)) :
      (⟨W + BitVec.ofNat 64 d, 8⟩ : Region).Disjoint r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl
    · exact h.p_w.symm.sub_left (h.sW (by omega))
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact Offset.disjoint W (by omega) (by omega) (by omega)
    · exact (h.stk_w.sub_right (h.sW (by omega))).symm
  have finish {t : State} (hd : CDone s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) t) :
      WP isa (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) t
        (CPost' s₀ C D P W R L q s) := by
    obtain ⟨t', run, r13, r14, g, m, rd, wr⟩ := ctrEnd_ok h hd.r15 hd.rd hd.wr
      (by rw [hd.frame.readW (w := 64) (Region.contains_self _ _) (dS dataOff (by decide) (by decide)) (by decide)];
          exact h208)
      (by rw [hd.frame.readW (w := 64) (Region.contains_self _ _) (dS lenOff (by decide) (by decide)) (by decide)];
          exact h216)
    exact WP.of_runBlock ⟨t', run, ⟨by rw [g _ (by decide) (by decide), hd.rbx], by rw [g _ (by decide) (by decide),
      hd.rbp], by rw [g _ (by decide) (by decide), hd.r12], r13, r14, by rw [g _ (by decide) (by decide), hd.r15],
      by rw [g _ (by decide) (by decide), hd.rsp], by rw [rd, hd.rd], by rw [wr, hd.wr]⟩, by rw [m]; exact hd.data,
      by rw [m]; exact hd.frame⟩
  refine WP.seq (WP.mono (ctrWhole_wp v h hcp hPw hr hql hlow hcnt) fun s₁ ⟨zf₁, hi₁⟩ => ?_)
  refine WP.seq (WP.ite (decide (L - 16 * wholeOf L = 0)) zf₁ (fun hb => WP.block_nil ?_) (fun hb => ?_))
  · have h0 : L - 16 * wholeOf L = 0 := of_decide_eq_true hb
    refine finish ⟨hi₁.rbx, hi₁.rbp, hi₁.r12, hi₁.r15, hi₁.rsp, hi₁.rd, hi₁.wr, ?_, hi₁.frame⟩
    rw [hi₁.data]
    exact ctrPart_all _ (ctxCiph_length s.mem C R) q _ (by rw [Proof.Cmac.bytesAt_length]; omega)
  · have h0 : L - 16 * wholeOf L ≠ 0 := of_decide_eq_false hb
    refine WP.loop (M := isa) (c := .ne)
      (fun (n : Nat) (t : State) => ∃ i, n = L - 16 * i ∧ 16 * i < L ∧
        CInv s₀ C D P W R L s.mem q (Spec.Aes.bytesAt s.mem P L) i t) ?_ (L - 16 * wholeOf L) s₁
      ⟨wholeOf L, rfl, by omega, hi₁⟩
    rintro n t ⟨i, rfl, hiL, hi⟩
    refine ctr_head v h hcp hi fun t₃ hh => WP.mono (ctr_tail h hPw hi hiL hh) fun t' ht => ?_
    rcases ht with ⟨_, hz, hd⟩ | ⟨_, hz, hi'⟩
    · exact Or.inl ⟨by simp [eval, hz], finish hd⟩
    · exact Or.inr ⟨by simp [eval, hz], L - 16 * (i + 1), by omega, i + 1, rfl, by omega, hi'⟩

end VG.Proof.AesSiv.X86_64
