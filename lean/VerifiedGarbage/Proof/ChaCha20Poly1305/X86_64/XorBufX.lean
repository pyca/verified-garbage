import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: XORing keystream from a buffer, 16 bytes at a time

`xorBufX d` XORs the `n` bytes at `B` (in `rsi`) into the `n` bytes at `D`
(in `d`), `n` being in `rdx` (`xorBufX_ok`): 16 bytes at a time through
`xmm0` and `xmm1` while at least 16 remain (`x_step`, with `XorBuf`'s
invariant), then the rest by `XorBuf.xorBuf` from `rdi = D + 16 ⌊n / 16⌋`
and `rsi = B + 16 ⌊n / 16⌋`. Byte `k` of the data becomes its XOR with byte
`k` of the buffer, and nothing else in memory changes; among the
general-purpose registers only `rax`, `rcx`, `rdx`, `rsi`, `rdi` and `r8`
are written.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.XorBufX

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64 VG.Impl.ChaCha20.X86_64.XorBuf
open VG.Proof.ChaCha20.X86_64.XorBuf (Inv Post inRegions_offset buf_not_data contains_byte xorBuf_ok)

/-! ## 16-byte words -/

/-- Storing back 16 bytes XORed with `y` XORs each of them with that of `y`. -/
theorem writeW128_xor (m : Mem) (a : Addr) (y : BitVec 128) (x : Addr) :
    m.writeW a (m.readW a 128 ^^^ y) x =
      if (x - a).toNat < 16 then m x ^^^ y.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 16 then ((m.readW a 128 ^^^ y).setWidth 128).extractLsb'
    (8 * (x - a).toNat) 8 else m x) = _
  by_cases h : (x - a).toNat < 16
  · rw [ite_eq_left h, ite_eq_left h, BitVec.setWidth_eq, BitVec.extractLsb'_xor]
    congr 1
    change ((m.read a 16).setWidth 128).extractLsb' (8 * (x - a).toNat) 8 = m x
    rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ h, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Byte `t` of 16 bytes read. -/
theorem readW128_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 16) :
    (m.readW a 128).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  change ((m.read a 16).setWidth 128).extractLsb' (8 * t) 8 = _
  rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ ht]

/-- Memory after the 16 bytes at offset `i`. -/
abbrev xMem (m : Mem) (D B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m.readW (D + BitVec.ofNat 64 i) 128 ^^^ m.readW (B + BitVec.ofNat 64 i) 128)

/-- After the 16 bytes at offset `i`. -/
theorem inv_xstep {D B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D B n s₀ i s)
    (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64) (hi : i + 16 ≤ n) {s' : State}
    (hm : s'.mem = xMem s.mem D B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D B n s₀ (i + 16) s' := by
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, xMem]
    rw [writeW128_xor, Offset.sub_toNat' D (by omega) (by omega)]
    by_cases hin : i ≤ k ∧ k < i + 16
    · rw [ite_eq_left hin.1, ite_eq_left (by omega), readW128_byte _ _ (by omega),
        BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1, h.buf hd (by omega) hk,
        h.data k hk, ite_eq_right (by omega), ite_eq_left (by omega)]
    · rw [h.data k hk]
      by_cases hik : i ≤ k
      · rw [ite_eq_left hik, ite_eq_right (by omega)]
        by_cases hlt : k < i
        · omega
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      · rw [ite_eq_right hik]
        split
        · omega
        · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
  · rw [hm]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat D (by omega)]; omega

/-! ## The loop -/

section
variable {d : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx ∧ d ≠ .rdi)
  {D B : Addr} {n : Nat} {s₀ : State}

/-- The registers while the loop runs: `i` bytes done, of the `n` at `D`. -/
structure Regs (d : Reg) (D B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  rd : s.gpr d = D
  rb : s.gpr .rsi = B
  rdx : s.gpr .rdx = BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .rcx → s.gpr r = s₀.gpr r

theorem se16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

include hdx in
theorem x_step (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64)
    (hw : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) {j : Nat} (hj : j < n / 16)
    {s : State} (hI : Inv D B n s₀ (16 * j) s) (hR : Regs d D B n s₀ (16 * j) s)
    (hax : s.gpr .rax = BitVec.ofNat 64 (n / 16 - j)) :
    WP isa (.block (xBody d)) s fun s' =>
      Inv D B n s₀ (16 * (j + 1)) s' ∧ Regs d D B n s₀ (16 * (j + 1)) s' ∧
        s'.gpr .rax = BitVec.ofNat 64 (n / 16 - (j + 1)) ∧
        s'.zf = some (decide (n / 16 - (j + 1) = 0)) := by
  have hi : 16 * j + 16 ≤ n := by omega
  have ea₁ : D + BitVec.ofNat 64 (16 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      D + BitVec.ofNat 64 (16 * j) := by simp
  have ea₂ : B + BitVec.ofNat 64 (16 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      B + BitVec.ofNat 64 (16 * j) := by simp
  have o₁ : InRegions s.wr (D + BitVec.ofNat 64 (16 * j)) 16 := by rw [hI.wr]; exact inRegions_offset hw hi
  have i₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 (16 * j)) 16 :=
    let ⟨r, hr', hc⟩ := o₁; ⟨r, List.mem_append_right _ hr', hc⟩
  have i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (16 * j)) 16 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hr hi
  have e16 : 16 * (j + 1) = 16 * j + 16 := by omega
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, xBody, idx, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, readSrc, execAlu, arithFlags, State.load128, State.store128, State.setReg,
    State.setFlags, State.setXmm, XOp.exec, XBinOp.eval, hR.rd, hR.rb, hR.rcx, ea₁, ea₂,
    i₁, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se16, se1]
  refine ⟨by rw [e16]; exact inv_xstep hI hd hn hi rfl rfl rfl,
    ⟨by simp [hdx.1, hdx.2.2.1, hR.rd],
    by simp [hR.rb],
    by simp [hR.rdx], by simp [e16, BitVec.ofNat_add],
    fun r h₁ h₂ => by simp [h₁, h₂, hR.keep r h₁ h₂]⟩, ?_, ?_⟩
  · simp only [hax]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [hax, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega

end

/-! ## The whole -/

/-- What `xorBufX d` does: byte `k < n` of the data XORed with byte `k` of
the buffer, the rest of memory unchanged, and the registers but `rax`,
`rcx`, `rdx`, `rsi`, `rdi` and `r8`. -/
structure XPost (D B : Addr) (n : Nat) (s₀ s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    s₀.mem (D + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem se0 : BitVec.ofInt 64 (0 : Int) = 0 := rfl

theorem xorBufX_ok {d : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx ∧ d ≠ .rsi ∧ d ≠ .rdx ∧ d ≠ .rdi)
    {D B : Addr} {n : Nat} {s₀ : State}
    (hD : s₀.gpr d = D) (hB : s₀.gpr .rsi = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩)
    (hw : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) :
    WP isa (xorBufX d) s₀ (XPost D B n s₀) := by
  -- The prologue.
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 4]) s₀
      fun s => Inv D B n s₀ 0 s ∧ Regs d D B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 16) ∧
        s.zf = some (decide (n / 16 = 0)) := by
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, readSrc32, execShift, State.setReg, State.setReg32, State.setFlags,
      Option.map_some, Option.some.injEq, exists_eq_left', hrdx]
    have hs : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨fun k hk => by simp, Frame.refl _ _, rfl, rfl⟩,
      ⟨by simp [hdx.1, hdx.2.2.1, hD], by simp [hB], by simp [hrdx], rfl,
      fun r h₁ h₂ => by simp [h₁, h₂]⟩, by simp [hs], ?_⟩
    simp only [hs]
    rw [← Offset.ofNat_sub_ofNat_beq (x := n / 16) (y := 0) (by omega) (by decide)]
    simp
  -- The 16-byte loop: `16 ⌊n / 16⌋` bytes done.
  have h₂ : ∀ s, (Inv D B n s₀ 0 s ∧ Regs d D B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 16) ∧
      s.zf = some (decide ((n / 16) = 0))) →
      WP isa (.ite .e (.block []) (.loop (.block (xBody d)) .ne)) s fun s' =>
        Inv D B n s₀ (16 * (n / 16)) s' ∧ Regs d D B n s₀ (16 * (n / 16)) s' := by
    rintro s ⟨hI, hR, hax, hz⟩
    refine WP.ite (decide ((n / 16) = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
    · have : (n / 16) = 0 := by simpa using h0
      exact WP.block_nil ⟨by rw [this]; exact hI, by rw [this]; exact hR⟩
    · have hq : 0 < (n / 16) := by have := of_decide_eq_false h0; omega
      refine WP.loop (M := isa) (body := .block (xBody d)) (c := .ne)
        (fun (k : Nat) (u : State) => ∃ j, k = (n / 16) - j ∧ j < (n / 16) ∧ Inv D B n s₀ (16 * j) u ∧
          Regs d D B n s₀ (16 * j) u ∧ u.gpr .rax = BitVec.ofNat 64 ((n / 16) - j)) ?_ ((n / 16) - 0) _
        ⟨0, rfl, hq, hI, hR, by rw [hax, Nat.sub_zero]⟩
      rintro k u ⟨j, rfl, hj, hIu, hRu, haxu⟩
      refine WP.mono (x_step hdx hd hn hw hr hj hIu hRu haxu) fun u' ⟨hI', hR', hax', hz'⟩ => ?_
      by_cases he : j + 1 = (n / 16)
      · left
        refine ⟨by simp [eval, hz']; omega, by rw [← he]; exact hI', by rw [← he]; exact hR'⟩
      · right
        exact ⟨by simp [eval, hz']; omega, (n / 16) - (j + 1), by omega, j + 1, rfl, by omega, hI', hR', hax'⟩
  refine WP.seq (WP.mono h₁ fun s₁ hs₁ => WP.seq (WP.mono (h₂ s₁ hs₁) fun s₂ hs₂ => ?_))
  obtain ⟨hI₂, hR₂⟩ := hs₂
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  -- The rest from `D + 16q` and `B + 16q`.
  have h₃ : WP isa (.block [.mov .rdi (.reg d), .alu .add .rdi (.reg .rcx), .alu .add .rsi (.reg .rcx),
      .alu .sub .rdx (.reg .rcx)]) s₂ fun s => s.gpr .rdi = D + BitVec.ofNat 64 (16 * (n / 16)) ∧
        s.gpr .rsi = B + BitVec.ofNat 64 (16 * (n / 16)) ∧ s.gpr .rdx = BitVec.ofNat 64 (n - 16 * (n / 16)) ∧
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
  have hsub : ∀ {P : Addr}, Region.Sub ⟨P + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩ ⟨P, n⟩ :=
    Offset.sub_base _ (by omega)
  refine WP.mono (xorBuf_ok (d := .rdi) (b := .rsi) (by decide) (by decide) rdi₃ rsi₃ rdx₃ (by omega)
    ((hd.sub_left hsub).sub_right hsub)
    (by rw [wr₃, hI₂.wr]; exact inRegions_offset hw (by omega))
    (by rw [rd₃, wr₃, hI₂.rd, hI₂.wr]; exact inRegions_offset hr (by omega))) fun s' hp' => ?_
  have hdata₂ : ∀ k < n, 16 * (n / 16) ≤ k → s₃.mem (D + BitVec.ofNat 64 k) = s₀.mem (D + BitVec.ofNat 64 k) :=
    fun k hk hle => by rw [m₃, hI₂.data k hk, ite_eq_right (by omega)]
  have hbuf₂ : ∀ k < n, s₃.mem (B + BitVec.ofNat 64 k) = s₀.mem (B + BitVec.ofNat 64 k) :=
    fun k hk => by rw [m₃]; exact hI₂.buf hd (by omega) hk
  refine ⟨fun k hk => ?_, ?_, fun r h₁ h₂ h₃ h₄ h₅ h₆ => ?_, by rw [hp'.rd, rd₃, hI₂.rd],
    by rw [hp'.wr, wr₃, hI₂.wr]⟩
  · by_cases hk' : k < 16 * (n / 16)
    · -- Done by the loop: outside the rest.
      rw [hp'.frame (D + BitVec.ofNat 64 k) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains]
        rw [Offset.sub_toNat' D (by omega) (by omega)]
        split <;> omega), m₃, hI₂.data k hk, ite_eq_left hk']
    · have e : ∀ {P : Addr}, P + BitVec.ofNat 64 k =
          P + BitVec.ofNat 64 (16 * (n / 16)) + BitVec.ofNat 64 (k - 16 * (n / 16)) := by
        intro P; rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      rw [e, e (P := B), hp'.data (k - 16 * (n / 16)) (by omega), ← e, ← e (P := B), hdata₂ k hk (by omega),
        hbuf₂ k hk]
  · have f₂ := hI₂.frame
    rw [← m₃] at f₂
    exact f₂.trans (hp'.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, hsub⟩)
  · rw [hp'.keep r h₁ h₂ h₃, g₃ r h₆ h₅ h₄, hR₂.keep r h₁ h₃]

end VG.Proof.ChaCha20Poly1305.X86_64.XorBufX
