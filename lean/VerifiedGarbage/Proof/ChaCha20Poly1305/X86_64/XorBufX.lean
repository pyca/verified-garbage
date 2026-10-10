import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: XORing keystream from a buffer, `2 ^ w` bytes at a time

`xorBufX w d` XORs the `n` bytes at `B` (in `rsi`) into the `n` bytes at `D`
(in `d`), `n` being in `rdx` (`xorBufX_ok`): `N = 2 ^ w` bytes at a time
(16, 32 or 64, through `xmm0` and `xmm1`, `ymm` or `zmm`) while at least
`N` remain (`x_step`, with `XorBuf`'s invariant), then the rest by
`XorBuf.xorBuf` from `rdi = D + N ⌊n / N⌋` and `rsi = B + N ⌊n / N⌋`. Byte `k` of the data becomes its XOR with byte
`k` of the buffer, and nothing else in memory changes; among the
general-purpose registers only `rax`, `rcx`, `rdx`, `rsi`, `rdi` and `r8`
are written.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.XorBufX

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20.X86_64.XorBuf
open VG.Proof.ChaCha20.X86_64.XorBuf (Inv Post inRegions_offset buf_not_data contains_byte xorBuf_ok)

/-! ## Words of `N` bytes -/

/-- Memory after the `N` bytes at offset `i`. -/
abbrev xMem (N : Nat) (m : Mem) (D B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m.readW (D + BitVec.ofNat 64 i) (8 * N) ^^^ m.readW (B + BitVec.ofNat 64 i) (8 * N))

/-- After the `N` bytes at offset `i`. -/
theorem inv_xstep {N : Nat} (hN : N ≤ 64) {D B : Addr} {n : Nat} {s₀ s : State} {i : Nat}
    (h : Inv D B n s₀ i s) (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64) (hi : i + N ≤ n)
    {s' : State} (hm : s'.mem = xMem N s.mem D B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D B n s₀ (i + N) s' := by
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, xMem]
    by_cases hin : i ≤ k ∧ k < i + N
    · have e : ∀ {P : Addr}, P + BitVec.ofNat 64 k = P + BitVec.ofNat 64 i + BitVec.ofNat 64 (k - i) := by
        intro P; rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
      rw [e, writeW_byte _ _ _ (by omega) (by omega), BitVec.extractLsb'_xor, byte_readW _ _ (by omega),
        byte_readW _ _ (by omega), ← e, ← e (P := B), h.buf hd (by omega) hk, h.data k hk,
        ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [writeW_byte_off _ _ _ _ ?_, h.data k hk]
      · by_cases hik : k < i
        · rw [ite_eq_left hik, ite_eq_left (by omega)]
        · rw [ite_eq_right hik, ite_eq_right (by omega)]
      · rw [Offset.sub_toNat' D (by omega) (by omega)]
        split <;> omega
  · rw [hm]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat D (by omega)]; omega

theorem zmm_setZ (t : State) (r : XReg) (l0 l1 l2 l3 : BitVec 128) :
    (t.setZ r l0 l1 l2 l3).zmm r = (l3 ++ l2) ++ (l1 ++ l0) := by
  simp [State.zmm, State.ymm, State.setZ]

theorem halves256 (v u : BitVec 256) :
    (v.extractLsb' 128 128 ^^^ u.extractLsb' 128 128) ++ (v.extractLsb' 0 128 ^^^ u.extractLsb' 0 128) =
      v ^^^ u := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb']
  by_cases h : i < 128
  · simp [h]
  · simp [h, show i - 128 < 128 by omega, show 128 + (i - 128) = i by omega]

theorem quarters512 (v u : BitVec 512) :
    ((v.extractLsb' 384 128 ^^^ u.extractLsb' 384 128) ++ (v.extractLsb' 256 128 ^^^ u.extractLsb' 256 128)) ++
      ((v.extractLsb' 128 128 ^^^ u.extractLsb' 128 128) ++ (v.extractLsb' 0 128 ^^^ u.extractLsb' 0 128)) =
      v ^^^ u := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor, BitVec.getLsbD_extractLsb']
  by_cases h₁ : i < 256
  · by_cases h₂ : i < 128
    · simp [h₁, h₂]
    · simp [h₁, h₂, show i - 128 < 128 by omega, show 128 + (i - 128) = i by omega]
  · by_cases h₂ : i - 256 < 128
    · simp [h₁, h₂, show 256 + (i - 256) = i by omega]
    · simp [h₁, h₂, show i - 256 - 128 < 128 by omega, show 384 + (i - 256 - 128) = i by omega]

/-- The data part of `xBody w`, from `D + i` and `B + i`, for `w` = 4, 5 or 6. -/
theorem xData_ok {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) {d : Reg} {D B : Addr} {i : Nat} {s : State}
    (hD : s.gpr d = D) (hB : s.gpr .rsi = B) (hrcx : s.gpr .rcx = BitVec.ofNat 64 i)
    (o₁ : InRegions s.wr (D + BitVec.ofNat 64 i) (2 ^ w))
    (i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i) (2 ^ w)) :
    WP isa (.block (xData w d)) s fun s' =>
      s'.mem = xMem (2 ^ w) s.mem D B i ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) (2 ^ w) :=
    let ⟨r, hr', hc⟩ := o₁; ⟨r, List.mem_append_right _ hr', hc⟩
  have ea₁ : s.ea (idx d) = D + BitVec.ofNat 64 i := by
    simp [State.ea, idx, hD, hrcx]
  have ea₂ : s.ea (idx .rsi) = B + BitVec.ofNat 64 i := by
    simp [State.ea, idx, hB, hrcx]
  rcases hw with rfl | rfl | rfl <;> simp only [Nat.reducePow] at i₁ i₂ o₁ ⊢ <;> simp only [xMem, Nat.reduceMul]
  · have e₁ : D + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = D + BitVec.ofNat 64 i := by simp
    have e₂ : B + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = B + BitVec.ofNat 64 i := by simp
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, xData, idx, runBlock_cons, runStep_some, runBlock_nil, exec,
      State.ea, State.load128, State.store128, State.setXmm, XOp.exec, XBinOp.eval, hD, hB, hrcx, e₁, e₂,
      i₁, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial⟩
  · apply WP.of_runBlock
    simp only [xData, runBlock_cons, runStep_some, runBlock_nil, exec, ea₁, ea₂, State.load256,
      State.store256_eq, i₁, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', ite_true, VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr, VOp.exec_ea,
      State.setV_gpr, State.setV_mem, State.setV_rd, State.setV_wr, State.setV_ea, State.setMem_gpr,
      State.setMem_mem, State.setMem_rd, State.setMem_wr, State.ymm_eq, lane_vbin256, State.lane_setV256,
      reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, VBinOp.sse, XBinOp.eval, halves256]
    exact ⟨trivial, trivial, trivial, trivial⟩
  · apply WP.of_runBlock
    simp only [xData, runBlock_cons, runStep_some, runBlock_nil, exec, ea₁, ea₂, State.load512,
      State.store512_eq, i₁, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', ite_true, ZOp.exec_gpr, ZOp.exec_mem, ZOp.exec_rd, ZOp.exec_wr, ZOp.exec_ea,
      State.setZ_gpr, State.setZ_mem, State.setZ_rd, State.setZ_wr, State.setZ_ea, State.setMem_gpr,
      State.setMem_mem, State.setMem_rd, State.setMem_wr]
    refine ⟨?_, trivial, trivial, trivial⟩
    simp only [ZOp.exec, zmm_setZ, State.zlane_setZ _ _ _ _ _ _ _ (show 0 < 4 by decide),
      State.zlane_setZ _ _ _ _ _ _ _ (show 1 < 4 by decide), State.zlane_setZ _ _ _ _ _ _ _ (show 2 < 4 by decide),
      State.zlane_setZ _ _ _ _ _ _ _ (show 3 < 4 by decide), pick4, ite_true, reduceCtorEq, ↓reduceIte,
      Nat.reduceEqDiff, ZBinOp.sse, XBinOp.eval, quarters512]

/-! ## The loop -/

section
variable {w : Nat} {d : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx ∧ d ≠ .rdi)
  {D B : Addr} {n : Nat} {s₀ : State}

/-- The registers while the loop runs: `i` bytes done, of the `n` at `D`. -/
structure Regs (d : Reg) (D B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  rd : s.gpr d = D
  rb : s.gpr .rsi = B
  rdx : s.gpr .rdx = BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = s₀.gpr r

theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

theorem pow_cases {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) : 16 ≤ 2 ^ w ∧ 2 ^ w ≤ 64 := by
  rcases hw with rfl | rfl | rfl <;> decide

theorem seW {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) :
    BitVec.signExtend 64 (BitVec.ofNat 32 (2 ^ w)) = BitVec.ofNat 64 (2 ^ w) := by
  rcases hw with rfl | rfl | rfl <;> decide

include hdx in
theorem x_step (hw : w = 4 ∨ w = 5 ∨ w = 6) (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64)
    (hwr : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) {j : Nat} (hj : j < n / 2 ^ w)
    {s : State} (hI : Inv D B n s₀ (2 ^ w * j) s) (hR : Regs d D B n s₀ (2 ^ w * j) s)
    (hax : s.gpr .rax = BitVec.ofNat 64 (n / 2 ^ w - j)) :
    WP isa (.block (xBody w d)) s fun s' =>
      Inv D B n s₀ (2 ^ w * (j + 1)) s' ∧ Regs d D B n s₀ (2 ^ w * (j + 1)) s' ∧
        s'.gpr .rax = BitVec.ofNat 64 (n / 2 ^ w - (j + 1)) ∧
        s'.zf = some (decide (n / 2 ^ w - (j + 1) = 0)) := by
  have hp := pow_cases hw
  have hq' : n / 2 ^ w ≤ n := Nat.div_le_self _ _
  have hi : 2 ^ w * j + 2 ^ w ≤ n := by
    have := Nat.mul_le_of_le_div (2 ^ w) (j + 1) n (by omega)
    rw [Nat.mul_comm] at this; rw [Nat.mul_succ] at this; omega
  have o₁ : InRegions s.wr (D + BitVec.ofNat 64 (2 ^ w * j)) (2 ^ w) := by
    rw [hI.wr]; exact inRegions_offset hwr hi
  have i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (2 ^ w * j)) (2 ^ w) := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hr hi
  have eW : 2 ^ w * (j + 1) = 2 ^ w * j + 2 ^ w := Nat.mul_succ _ _
  refine WP.block_append (WP.mono (xData_ok hw hR.rd hR.rb hR.rcx o₁ i₂)
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setReg, State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se1, seW hw, g₁,
    hR.rcx, hax, reduceCtorEq, ↓reduceIte]
  refine ⟨by rw [eW]; exact inv_xstep hp.2 hI hd hn hi m₁ rd₁ wr₁,
    ⟨by simp [hdx.1, hdx.2.2.1, hR.rd], by simp [hR.rb], by simp [hR.rdx],
    by simp [eW, BitVec.ofNat_add],
    fun r h₁ h₂ => by simp [h₁, h₂, hR.keep r h₁ h₂]⟩, ?_, ?_⟩
  · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega

end

/-! ## The whole -/

/-- What `xorBufX w d` does: byte `k < n` of the data XORed with byte `k` of
the buffer, the rest of memory unchanged, and the registers but `rax`,
`rcx`, `rdx`, `rsi`, `rdi` and `r8`. -/
structure XPost (D B : Addr) (n : Nat) (s₀ s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    s₀.mem (D + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem xorBufX_ok {w : Nat} (hw : w = 4 ∨ w = 5 ∨ w = 6) {d : Reg}
    (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx ∧ d ≠ .rdi)
    {D B : Addr} {n : Nat} {s₀ : State}
    (hD : s₀.gpr d = D) (hB : s₀.gpr .rsi = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩)
    (hwr : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) :
    WP isa (xorBufX w d) s₀ (XPost D B n s₀) := by
  have hp := pow_cases hw
  have hq' : n / 2 ^ w ≤ n := Nat.div_le_self _ _
  -- The prologue.
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax w]) s₀
      fun s => Inv D B n s₀ 0 s ∧ Regs d D B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 2 ^ w) ∧
        s.zf = some (decide (n / 2 ^ w = 0)) := by
    have hc : 1 ≤ w ∧ w ≤ 63 := by omega
    have h1 : w ≠ 1 := by omega
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, readSrc32, execShift, State.setReg, State.setReg32, State.setFlags,
      Option.map_some, Option.some.injEq, exists_eq_left', hrdx, hc, h1, and_true, ite_true, ite_false]
    have hs : BitVec.ofNat 64 n >>> w = BitVec.ofNat 64 (n / 2 ^ w) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]
    refine ⟨⟨fun k hk => by simp, Frame.refl _ _, rfl, rfl⟩,
      ⟨by simp [hdx.1, hdx.2.2.1, hD], by simp [hB], by simp [hrdx], rfl,
      fun r h₁ h₂ => by simp [h₁, h₂]⟩, by simp [hs], ?_⟩
    simp only [hs]
    rw [← Offset.ofNat_sub_ofNat_beq (x := n / 2 ^ w) (y := 0) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)
      (by decide)]
    simp
  -- The loop: `N ⌊n / N⌋` bytes done.
  have h₂ : ∀ s, (Inv D B n s₀ 0 s ∧ Regs d D B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 2 ^ w) ∧
      s.zf = some (decide ((n / 2 ^ w) = 0))) →
      WP isa (.ite .e (.block []) (.loop (.block (xBody w d)) .ne)) s fun s' =>
        Inv D B n s₀ (2 ^ w * (n / 2 ^ w)) s' ∧ Regs d D B n s₀ (2 ^ w * (n / 2 ^ w)) s' := by
    rintro s ⟨hI, hR, hax, hz⟩
    refine WP.ite (decide ((n / 2 ^ w) = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
    · have : (n / 2 ^ w) = 0 := by simpa using h0
      exact WP.block_nil ⟨by rw [this]; exact hI, by rw [this]; exact hR⟩
    · have hq : 0 < (n / 2 ^ w) := Nat.pos_of_ne_zero (by simpa using h0)
      refine WP.loop (M := isa) (body := .block (xBody w d)) (c := .ne)
        (fun (k : Nat) (u : State) => ∃ j, k = (n / 2 ^ w) - j ∧ j < (n / 2 ^ w) ∧ Inv D B n s₀ (2 ^ w * j) u ∧
          Regs d D B n s₀ (2 ^ w * j) u ∧ u.gpr .rax = BitVec.ofNat 64 ((n / 2 ^ w) - j)) ?_ ((n / 2 ^ w) - 0) _
        ⟨0, rfl, hq, hI, hR, by rw [hax, Nat.sub_zero]⟩
      rintro k u ⟨j, rfl, hj, hIu, hRu, haxu⟩
      refine WP.mono (x_step hdx hw hd hn hwr hr hj hIu hRu haxu) fun u' ⟨hI', hR', hax', hz'⟩ => ?_
      by_cases he : j + 1 = (n / 2 ^ w)
      · left
        refine ⟨by simp [eval, hz']; omega, by rw [← he]; exact hI', by rw [← he]; exact hR'⟩
      · right
        exact ⟨by simp [eval, hz']; omega, (n / 2 ^ w) - (j + 1), by omega, j + 1, rfl, by omega, hI', hR', hax'⟩
  refine WP.seq (WP.mono h₁ fun s₁ hs₁ => WP.seq (WP.mono (h₂ s₁ hs₁) fun s₂ hs₂ => ?_))
  obtain ⟨hI₂, hR₂⟩ := hs₂
  have hq : 2 ^ w * (n / 2 ^ w) ≤ n := Nat.mul_div_le n (2 ^ w)
  -- The rest from `D + Nq` and `B + Nq`.
  have h₃ : WP isa (.block [.mov .rdi (.reg d), .alu .add .rdi (.reg .rcx), .alu .add .rsi (.reg .rcx),
      .alu .sub .rdx (.reg .rcx)]) s₂ fun s => s.gpr .rdi = D + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) ∧
        s.gpr .rsi = B + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) ∧
        s.gpr .rdx = BitVec.ofNat 64 (n - 2 ^ w * (n / 2 ^ w)) ∧
        (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → s.gpr r = s₂.gpr r) ∧ s.mem = s₂.mem ∧
        s.rd = s₂.rd ∧ s.wr = s₂.wr := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
      State.setReg, State.setFlags, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', reduceCtorEq, ↓reduceIte, hR₂.rd, hR₂.rb, hR₂.rcx, hR₂.rdx]
    refine ⟨by simp [hdx.2.2.1], by simp, ?_, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial, trivial,
      trivial⟩
    rw [Offset.ofNat_sub_ofNat (by omega)]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨rdi₃, rsi₃, rdx₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  have hsub : ∀ {P : Addr}, Region.Sub ⟨P + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)), n - 2 ^ w * (n / 2 ^ w)⟩ ⟨P, n⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.mono (xorBuf_ok (d := .rdi) (b := .rsi) (by decide) (by decide) rdi₃ rsi₃ rdx₃ (by omega)
    ((hd.sub_left hsub).sub_right hsub)
    (by rw [wr₃, hI₂.wr]; exact inRegions_offset hwr (by omega))
    (by rw [rd₃, wr₃, hI₂.rd, hI₂.wr]; exact inRegions_offset hr (by omega))) fun s' hp' => ?_
  have hdata₂ : ∀ k < n, 2 ^ w * (n / 2 ^ w) ≤ k → s₃.mem (D + BitVec.ofNat 64 k) = s₀.mem (D + BitVec.ofNat 64 k) :=
    fun k hk hle => by rw [m₃, hI₂.data k hk, ite_eq_right (by omega)]
  have hbuf₂ : ∀ k < n, s₃.mem (B + BitVec.ofNat 64 k) = s₀.mem (B + BitVec.ofNat 64 k) :=
    fun k hk => by rw [m₃]; exact hI₂.buf hd (by omega) hk
  refine ⟨fun k hk => ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, by rw [hp'.rd, rd₃, hI₂.rd],
    by rw [hp'.wr, wr₃, hI₂.wr]⟩
  · by_cases hk' : k < 2 ^ w * (n / 2 ^ w)
    · -- Done by the loop: outside the rest.
      rw [hp'.frame (D + BitVec.ofNat 64 k) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains]
        rw [Offset.sub_toNat' D (by omega) (by omega)]
        split <;> omega), m₃, hI₂.data k hk, ite_eq_left hk']
    · have e : ∀ {P : Addr}, P + BitVec.ofNat 64 k =
          P + BitVec.ofNat 64 (2 ^ w * (n / 2 ^ w)) + BitVec.ofNat 64 (k - 2 ^ w * (n / 2 ^ w)) := by
        intro P; rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      rw [e, e (P := B), hp'.data (k - 2 ^ w * (n / 2 ^ w)) (by omega), ← e, ← e (P := B), hdata₂ k hk (by omega),
        hbuf₂ k hk]
  · have f₂ := hI₂.frame
    rw [← m₃] at f₂
    exact f₂.trans (hp'.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩)
  · rw [hp'.keep r h₁ h₂ h₃, g₃ r h₆ h₅ h₄, hR₂.keep r h₁ h₃]

end VG.Proof.ChaCha20Poly1305.X86_64.XorBufX
