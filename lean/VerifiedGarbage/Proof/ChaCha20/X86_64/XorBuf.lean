import VerifiedGarbage.Impl.ChaCha20.X86_64.XorBuf
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# XORing keystream from a buffer into the data, eight bytes at a time

`XorBuf.xorBuf d b` XORs the `n` bytes at `B` (in `b`) into the `n` bytes at
`D` (in `d`), `n` being in `rdx`: byte `k` of the data becomes its XOR with
byte `k` of the buffer, and nothing else in memory changes. Only `rax`, `r8`,
`rcx` and the flags are written among the registers.
-/

namespace VG.Proof.ChaCha20.X86_64.XorBuf

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.XorBuf

/-! ## Bytes of quadwords -/

/-- Storing back a quadword XORed with `y` XORs each of its bytes with that
of `y`. -/
theorem writeW_xor (m : Mem) (a : Addr) (y : BitVec 64) (x : Addr) :
    m.writeW a (m.readW a 64 ^^^ y) x =
      if (x - a).toNat < 8 then m x ^^^ y.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 8 then ((m.readW a 64 ^^^ y).setWidth 64).extractLsb'
    (8 * (x - a).toNat) 8 else m x) = _
  by_cases h : (x - a).toNat < 8
  · rw [ite_eq_left h, ite_eq_left h, BitVec.setWidth_eq, BitVec.extractLsb'_xor]
    congr 1
    change ((m.read a 8).setWidth 64).extractLsb' (8 * (x - a).toNat) 8 = m x
    rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ h, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h, ite_eq_right h]

/-- Byte `t` of a quadword read. -/
theorem readW64_byte (m : Mem) (a : Addr) {t : Nat} (ht : t < 8) :
    (m.readW a 64).extractLsb' (8 * t) 8 = m (a + BitVec.ofNat 64 t) := by
  change ((m.read a 8).setWidth 64).extractLsb' (8 * t) 8 = _
  rw [BitVec.setWidth_eq, Mem.extractLsb'_read _ _ ht]

/-- A byte store. -/
theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

theorem xor_setWidth (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).setWidth 8 = a ^^^ b := by
  ext i hi; simp

/-! ## Regions -/

/-- A sub-range of a permitted range is permitted. -/
theorem inRegions_offset {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n)
    {i m : Nat} (him : i + m ≤ n) : InRegions rs (a + BitVec.ofNat 64 i) m := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at *
  have e : a + BitVec.ofNat 64 i - r.base = (a - r.base) + BitVec.ofNat 64 i := by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm
      (BitVec.ofNat 64 i), ← BitVec.add_assoc]
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := (a - r.base).isLt
  rcases Nat.lt_or_ge ((a - r.base).toNat + i % 2 ^ 64) (2 ^ 64) with h' | h'
  · rw [Nat.mod_eq_of_lt h']
    have : i % 2 ^ 64 ≤ i := Nat.mod_le _ _
    omega
  · have : ((a - r.base).toNat + i % 2 ^ 64) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have : i % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]
    omega

/-- Byte `k` of a range at `p` is in it. -/
theorem contains_byte (p : Addr) {k n : Nat} (hk : k < n) (hn : n ≤ 2 ^ 64) :
    (⟨p, n⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p (by omega)]; omega

/-- A byte of the buffer is not in the data. -/
theorem buf_not_data {D B : Addr} {n : Nat} (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩)
    (hn : n ≤ 2 ^ 64) {k : Nat} (hk : k < n) : ¬ (⟨D, n⟩ : Region).Contains (B + BitVec.ofNat 64 k) 1 :=
  fun h => hd _ h (contains_byte B hk hn)

/-! ## The invariant -/

section
variable (D B : Addr) (n : Nat) (s₀ : State)

/-- `i` bytes done, of `n` from `B` into `D`. -/
structure Inv (i : Nat) (s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    if k < i then s₀.mem (D + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
    else s₀.mem (D + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

end

/-- The data byte by byte, from the bytes of the data and the buffer. -/
theorem Inv.buf {D B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D B n s₀ i s)
    (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n ≤ 2 ^ 64) {k : Nat} (hk : k < n) :
    s.mem (B + BitVec.ofNat 64 k) = s₀.mem (B + BitVec.ofNat 64 k) := by
  refine h.frame (B + BitVec.ofNat 64 k) ?_
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact buf_not_data hd hn hk

/-- Memory after the quadword at offset `i`. -/
abbrev qMem (m : Mem) (D B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m.readW (D + BitVec.ofNat 64 i) 64 ^^^ m.readW (B + BitVec.ofNat 64 i) 64)

/-- Memory after the byte at offset `i`. -/
abbrev bMem (m : Mem) (D B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m (D + BitVec.ofNat 64 i) ^^^ m (B + BitVec.ofNat 64 i))

/-- After the quadword at offset `i`. -/
theorem Inv.qstep {D B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D B n s₀ i s)
    (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64) (hi : i + 8 ≤ n) {s' : State}
    (hm : s'.mem = qMem s.mem D B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D B n s₀ (i + 8) s' := by
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, qMem]
    rw [writeW_xor, Offset.sub_toNat' D (by omega) (by omega)]
    by_cases hin : i ≤ k ∧ k < i + 8
    · rw [ite_eq_left hin.1, ite_eq_left (by omega), readW64_byte _ _ (by omega),
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

/-- After the byte at offset `i`. -/
theorem Inv.bstep {D B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D B n s₀ i s)
    (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64) (hi : i < n) {s' : State}
    (hm : s'.mem = bMem s.mem D B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D B n s₀ (i + 1) s' := by
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, bMem]
    rw [writeW8_apply]
    by_cases he : k = i
    · subst he
      rw [ite_eq_left rfl, h.buf hd (by omega) hk, h.data k hk, ite_eq_right (by omega),
        ite_eq_left (by omega)]
    · rw [ite_eq_right (Offset.add_ofNat_ne D (by omega) (by omega) he), h.data k hk]
      by_cases h₁ : k < i
      · rw [ite_eq_left h₁, ite_eq_left (by omega)]
      · rw [ite_eq_right h₁, ite_eq_right (by omega)]
  · rw [hm]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat D (by omega)]; omega

/-! ## The loops -/

section
variable {d b : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx) (hbx : b ≠ .rax ∧ b ≠ .r8 ∧ b ≠ .rcx)
  {D B : Addr} {n : Nat} {s₀ : State}

/-- The registers while the loops run: `i` bytes done, of the `n` at `D`. -/
structure Regs (d b : Reg) (D B : Addr) (n : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  rd : s.gpr d = D
  rb : s.gpr b = B
  rdx : s.gpr .rdx = BitVec.ofNat 64 n
  rcx : s.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r

theorem se8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
theorem se1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

include hdx hbx in
theorem q_step (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64)
    (hw : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) {j : Nat} (hj : j < n / 8)
    {s : State} (hI : Inv D B n s₀ (8 * j) s) (hR : Regs d b D B n s₀ (8 * j) s)
    (hax : s.gpr .rax = BitVec.ofNat 64 (n / 8 - j)) :
    WP isa (.block (qBody d b)) s fun s' =>
      Inv D B n s₀ (8 * (j + 1)) s' ∧ Regs d b D B n s₀ (8 * (j + 1)) s' ∧
        s'.gpr .rax = BitVec.ofNat 64 (n / 8 - (j + 1)) ∧
        s'.zf = some (decide (n / 8 - (j + 1) = 0)) ∧
        s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi := by
  have hi : 8 * j + 8 ≤ n := by omega
  have ea₁ : D + BitVec.ofNat 64 (8 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      D + BitVec.ofNat 64 (8 * j) := by simp
  have ea₂ : B + BitVec.ofNat 64 (8 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      B + BitVec.ofNat 64 (8 * j) := by simp
  have o₁ : InRegions s.wr (D + BitVec.ofNat 64 (8 * j)) 8 := by rw [hI.wr]; exact inRegions_offset hw hi
  have i₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 (8 * j)) 8 :=
    let ⟨r, hr', hc⟩ := o₁; ⟨r, List.mem_append_right _ hr', hc⟩
  have i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hr hi
  have e8 : 8 * (j + 1) = 8 * j + 8 := by omega
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, qBody, idx, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, readSrc, execAlu, arithFlags, State.load64, State.store64, State.setReg,
    State.setFlags, hR.rd, hR.rb, hR.rcx, hbx.2.1, hdx.2.1, ea₁, ea₂,
    i₁, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se8, se1]
  refine ⟨by rw [e8]; exact hI.qstep hd hn hi rfl rfl rfl,
    ⟨by simp [hdx.1, hdx.2.1, hdx.2.2, hR.rd],
    by simp [hbx.1, hbx.2.1, hbx.2.2, hR.rb],
    by simp [hR.rdx], by simp [e8, BitVec.ofNat_add],
    fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃, hR.keep r h₁ h₂ h₃]⟩, ?_, ?_, by simp⟩
  · simp only [hax]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [hax, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega

include hdx hbx in
theorem b_step (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64)
    (hw : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) {i : Nat} (hi : i < n)
    {s : State} (hI : Inv D B n s₀ i s) (hR : Regs d b D B n s₀ i s) :
    WP isa (.block (bBody d b)) s fun s' =>
      Inv D B n s₀ (i + 1) s' ∧ Regs d b D B n s₀ (i + 1) s' ∧
        s'.zf = some (decide (i + 1 = n)) ∧
        s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi ∧ s'.zmmHi = s.zmmHi := by
  have ea₁ : D + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = D + BitVec.ofNat 64 i := by
    simp
  have ea₂ : B + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = B + BitVec.ofNat 64 i := by
    simp
  have o₁ : InRegions s.wr (D + BitVec.ofNat 64 i) 1 := by rw [hI.wr]; exact inRegions_offset hw hi
  have i₁ : InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 i) 1 :=
    let ⟨r, hr', hc⟩ := o₁; ⟨r, List.mem_append_right _ hr', hc⟩
  have i₂ : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i) 1 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset hr hi
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, bBody, idx, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8, State.setReg,
    State.setFlags, hR.rd, hR.rb, hR.rcx, hbx.1, hdx.1, hdx.2.1, ea₁, ea₂,
    i₁, i₂, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se1]
  rw [xor_setWidth]
  refine ⟨hI.bstep hd hn hi rfl rfl rfl, ⟨by simp [hdx.1, hdx.2.1, hdx.2.2, hR.rd],
    by simp [hbx.1, hbx.2.1, hbx.2.2, hR.rb],
    by simp [hR.rdx], by simp [BitVec.ofNat_add],
    fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃, hR.keep r h₁ h₂ h₃]⟩, ?_, by simp⟩
  rw [hR.rdx, ← Offset.ofNat_sub_ofNat_beq (x := i + 1) (y := n) (by omega) (by omega),
    BitVec.ofNat_add]
  rfl

end

/-! ## The whole -/

/-- What `xorBuf` does: byte `k < n` of the data XORed with byte `k` of the
buffer, the rest of memory and the registers but `rax`, `r8` and `rcx`
unchanged. -/
structure Post (d b : Reg) (D B : Addr) (n : Nat) (s₀ s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    s₀.mem (D + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm = s₀.xmm
  ymmHi : s.ymmHi = s₀.ymmHi
  zmmHi : s.zmmHi = s₀.zmmHi

theorem xorBuf_ok {d b : Reg} (hdx : d ≠ .rax ∧ d ≠ .r8 ∧ d ≠ .rcx)
    (hbx : b ≠ .rax ∧ b ≠ .r8 ∧ b ≠ .rcx) {D B : Addr} {n : Nat} {s₀ : State}
    (hD : s₀.gpr d = D) (hB : s₀.gpr b = B) (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 64) (hd : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩)
    (hw : InRegions s₀.wr D n) (hr : InRegions (s₀.rd ++ s₀.wr) B n) :
    WP isa (xorBuf d b) s₀ (Post d b D B n s₀) := by
  -- The registers and vector state at each point.
  let V : State → Prop := fun s => s.xmm = s₀.xmm ∧ s.ymmHi = s₀.ymmHi ∧ s.zmmHi = s₀.zmmHi
  have hwr : InRegions s₀.wr D n := hw
  have hI0 : Inv D B n s₀ 0 s₀ :=
    ⟨fun k hk => by simp, Frame.refl _ _, rfl, rfl⟩
  -- The prologue.
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3]) s₀
      fun s => Inv D B n s₀ 0 s ∧ Regs d b D B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 8) ∧
        s.zf = some (decide (n / 8 = 0)) ∧ V s := by
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, readSrc32, execShift, State.setReg, State.setReg32, State.setFlags,
      Option.map_some, Option.some.injEq, exists_eq_left', hrdx]
    have hs : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨hI0.data, hI0.frame, rfl, rfl⟩, ⟨by simp [hdx.1, hdx.2.2, hD],
      by simp [hbx.1, hbx.2.2, hB], by simp [hrdx],
      by simp, fun r h₁ _ h₃ => by simp [h₁, h₃]⟩,
      by simp [hs], ?_, rfl, rfl, rfl⟩
    have hz : (BitVec.ofNat 64 (n / 8) == 0) = decide (n / 8 = 0) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      · intro h; rw [h]; rfl
    rw [hs, hz]
  -- After the quadwords.
  let Q : State → Prop := fun s => Inv D B n s₀ (8 * (n / 8)) s ∧ Regs d b D B n s₀ (8 * (n / 8)) s ∧ V s
  have h₂ : ∀ s, (Inv D B n s₀ 0 s ∧ Regs d b D B n s₀ 0 s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 8) ∧
      s.zf = some (decide (n / 8 = 0)) ∧ V s) →
      WP isa (.ite .e (.block []) (.loop (.block (qBody d b)) .ne)) s Q := by
    rintro s ⟨hI, hR, hax, hz, hV⟩
    refine WP.ite (decide (n / 8 = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨cast (congrArg (fun i => Inv D B n s₀ (8 * i) s) h.symm) hI,
        cast (congrArg (fun i => Regs d b D B n s₀ (8 * i) s) h.symm) hR, hV⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv' : Nat → State → Prop := fun c s => ∃ j, c = n / 8 - j ∧ j < n / 8 ∧
        Inv D B n s₀ (8 * j) s ∧ Regs d b D B n s₀ (8 * j) s ∧ s.gpr .rax = BitVec.ofNat 64 (n / 8 - j) ∧ V s
      have hstep : ∀ c s, Inv' c s → WP isa (.block (qBody d b)) s (fun s' =>
          (eval .ne s' = some false ∧ Q s') ∨ (eval .ne s' = some true ∧ ∃ c' < c, Inv' c' s')) := by
        rintro c s ⟨j, rfl, hj, hI, hR, hax, hV⟩
        refine WP.mono (q_step hdx hbx hd hn hw hr hj hI hR hax)
          fun s' ⟨hI', hR', hax', hz', x₁, x₂, x₃⟩ => ?_
        have hV' : V s' := ⟨x₁.trans hV.1, x₂.trans hV.2.1, x₃.trans hV.2.2⟩
        by_cases hl : n / 8 - (j + 1) = 0
        · have e : j + 1 = n / 8 := by omega
          exact .inl ⟨by simp [eval, hz', hl], cast (congrArg (fun i => Inv D B n s₀ (8 * i) s') e) hI',
            cast (congrArg (fun i => Regs d b D B n s₀ (8 * i) s') e) hR', hV'⟩
        · exact .inr ⟨by simp [eval, hz', hl], n / 8 - (j + 1), by omega, j + 1, rfl, by omega,
            hI', hR', hax', hV'⟩
      exact WP.loop (M := isa) Inv' hstep (n / 8 - 0) s ⟨0, rfl, by omega, hI, hR, by simpa using hax, hV⟩
  -- The bytes.
  let F : State → Prop := fun s => Inv D B n s₀ n s ∧ Regs d b D B n s₀ n s ∧ V s
  have h₃ : ∀ s, Q s → WP isa (.seq (.block [.alu .cmp .rcx (.reg .rdx)])
      (.ite .e (.block []) (.loop (.block (bBody d b)) .ne))) s F := by
    rintro s ⟨hI, hR, hV⟩
    have hle : 8 * (n / 8) ≤ n := by omega
    have hc : WP isa (.block [.alu .cmp .rcx (.reg .rdx)]) s fun s' =>
        Inv D B n s₀ (8 * (n / 8)) s' ∧ Regs d b D B n s₀ (8 * (n / 8)) s' ∧ V s' ∧
          s'.zf = some (decide (8 * (n / 8) = n)) := by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
        State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
      refine ⟨⟨hI.data, hI.frame, hI.rd, hI.wr⟩, ⟨hR.rd, hR.rb, hR.rdx, hR.rcx, hR.keep⟩, hV, ?_⟩
      rw [hR.rcx, hR.rdx, Offset.ofNat_sub_ofNat_beq (by omega) hn]
    refine WP.seq (WP.mono hc fun s₁ ⟨hI₁, hR₁, hV₁, hz₁⟩ => ?_)
    refine WP.ite (decide (8 * (n / 8) = n)) (by simp [eval, hz₁]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨cast (congrArg (fun i => Inv D B n s₀ i s₁) h) hI₁,
        cast (congrArg (fun i => Regs d b D B n s₀ i s₁) h) hR₁, hV₁⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv' : Nat → State → Prop := fun c s => ∃ i, c = n - i ∧ i < n ∧
        Inv D B n s₀ i s ∧ Regs d b D B n s₀ i s ∧ V s
      have hstep : ∀ c s, Inv' c s → WP isa (.block (bBody d b)) s (fun s' =>
          (eval .ne s' = some false ∧ F s') ∨ (eval .ne s' = some true ∧ ∃ c' < c, Inv' c' s')) := by
        rintro c s ⟨i, rfl, hi, hI, hR, hV⟩
        refine WP.mono (b_step hdx hbx hd hn hw hr hi hI hR)
          fun s' ⟨hI', hR', hz', x₁, x₂, x₃⟩ => ?_
        have hV' : V s' := ⟨x₁.trans hV.1, x₂.trans hV.2.1, x₃.trans hV.2.2⟩
        by_cases hl : i + 1 = n
        · exact .inl ⟨by simp [eval, hz', hl], cast (congrArg (fun i => Inv D B n s₀ i s') hl) hI',
            cast (congrArg (fun i => Regs d b D B n s₀ i s') hl) hR', hV'⟩
        · exact .inr ⟨by simp [eval, hz', hl], n - (i + 1), by omega, i + 1, rfl, by omega, hI', hR', hV'⟩
      exact WP.loop (M := isa) Inv' hstep (n - 8 * (n / 8)) s₁ ⟨8 * (n / 8), rfl, by omega, hI₁, hR₁, hV₁⟩
  refine WP.seq (WP.mono h₁ fun s h => WP.seq (WP.mono (h₂ s h) fun s' hq =>
    WP.mono (h₃ s' hq) fun s'' hf => ?_))
  obtain ⟨hI, hR, hV⟩ := hf
  exact ⟨fun k hk => by rw [hI.data k hk, ite_eq_left hk], hI.frame, hR.keep, hI.rd, hI.wr,
    hV.1, hV.2.1, hV.2.2⟩

end VG.Proof.ChaCha20.X86_64.XorBuf
