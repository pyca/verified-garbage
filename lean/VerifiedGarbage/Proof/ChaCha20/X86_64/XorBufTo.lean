import VerifiedGarbage.Proof.ChaCha20.X86_64.XorBuf

/-!
# XORing keystream from a buffer into data out of place

`XorBuf.xorBufTo d s b` writes to the `n` bytes at `D` (in `d`) the `n`
bytes at `S` (in `s`) XORed with the `n` at `B` (in `b`), `n` being in
`rdx`: byte `k` of the output is the XOR of byte `k` of the data and of the
buffer, and nothing else in memory changes. The output overlaps neither.
Only `rax`, `r8`, `rcx` and the flags are written among the registers.
-/

namespace VG.Proof.ChaCha20.X86_64.XorBufTo

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.XorBuf
open VG.Proof.ChaCha20.X86_64.XorBuf (readW64_byte writeW8_apply xor_setWidth inRegions_offset contains_byte
  buf_not_data se8 se1)

/-- A quadword store, byte by byte. -/
theorem writeW64_apply (m : Mem) (a : Addr) (v : BitVec 64) (x : Addr) :
    m.writeW a v x = if (x - a).toNat < 8 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 8 then (v.setWidth 64).extractLsb' (8 * (x - a).toNat) 8 else m x) = _
  rw [BitVec.setWidth_eq]

/-! ## The invariant -/

section
variable (D S B : Addr) (n : Nat) (s₀ : State)

/-- `i` bytes done, of `n` from `S` and `B` to `D`. -/
structure Inv (i : Nat) (s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    if k < i then s₀.mem (S + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
    else s₀.mem (D + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

end

/-- A byte of a range apart from the output keeps its value. -/
theorem Inv.other {D S B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D S B n s₀ i s)
    {X : Addr} (hd : (⟨D, n⟩ : Region).Disjoint ⟨X, n⟩) (hn : n ≤ 2 ^ 64) {k : Nat} (hk : k < n) :
    s.mem (X + BitVec.ofNat 64 k) = s₀.mem (X + BitVec.ofNat 64 k) := by
  refine h.frame (X + BitVec.ofNat 64 k) ?_
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact buf_not_data hd hn hk

/-- Memory after the quadword at offset `i`. -/
abbrev qMem (m : Mem) (D S B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m.readW (S + BitVec.ofNat 64 i) 64 ^^^ m.readW (B + BitVec.ofNat 64 i) 64)

/-- Memory after the byte at offset `i`. -/
abbrev bMem (m : Mem) (D S B : Addr) (i : Nat) : Mem :=
  m.writeW (D + BitVec.ofNat 64 i) (m (S + BitVec.ofNat 64 i) ^^^ m (B + BitVec.ofNat 64 i))

theorem add_off (P : Addr) {i k : Nat} (h : i ≤ k) :
    P + BitVec.ofNat 64 i + BitVec.ofNat 64 (k - i) = P + BitVec.ofNat 64 k := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' h]

/-- After the quadword at offset `i`. -/
theorem Inv.qstep {D S B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D S B n s₀ i s)
    (hdS : (⟨D, n⟩ : Region).Disjoint ⟨S, n⟩) (hdB : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64)
    (hi : i + 8 ≤ n) {s' : State}
    (hm : s'.mem = qMem s.mem D S B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D S B n s₀ (i + 8) s' := by
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, qMem]
    rw [writeW64_apply, Offset.sub_toNat' D (by omega) (by omega)]
    by_cases hin : i ≤ k ∧ k < i + 8
    · rw [ite_eq_left hin.1, ite_eq_left (by omega), BitVec.extractLsb'_xor, readW64_byte _ _ (by omega),
        readW64_byte _ _ (by omega), add_off S hin.1, add_off B hin.1, h.other hdS (by omega) hk,
        h.other hdB (by omega) hk, ite_eq_left (by omega)]
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
theorem Inv.bstep {D S B : Addr} {n : Nat} {s₀ s : State} {i : Nat} (h : Inv D S B n s₀ i s)
    (hdS : (⟨D, n⟩ : Region).Disjoint ⟨S, n⟩) (hdB : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩) (hn : n < 2 ^ 64)
    (hi : i < n) {s' : State}
    (hm : s'.mem = bMem s.mem D S B i) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Inv D S B n s₀ (i + 1) s' := by
  refine ⟨fun k hk => ?_, ?_, hrd.trans h.rd, hwr.trans h.wr⟩
  · simp only [hm, bMem]
    rw [writeW8_apply]
    by_cases he : k = i
    · subst he
      rw [ite_eq_left rfl, h.other hdS (by omega) hk, h.other hdB (by omega) hk, ite_eq_left (by omega)]
    · rw [ite_eq_right (Offset.add_ofNat_ne D (by omega) (by omega) he), h.data k hk]
      by_cases h₁ : k < i
      · rw [ite_eq_left h₁, ite_eq_left (by omega)]
      · rw [ite_eq_right h₁, ite_eq_right (by omega)]
  · rw [hm]
    refine h.frame.writeW (List.mem_singleton_self _) _ ?_
    simp only [Region.Contains]
    rw [Mem.sub_ofNat_toNat D (by omega)]; omega

/-! ## The loops -/

/-- Registers none of `xorBufTo`'s scratch registers. -/
def Free (r : Reg) : Prop := r ≠ .rax ∧ r ≠ .r8 ∧ r ≠ .rcx

section
variable {d s b : Reg} (hdx : Free d) (hsx : Free s) (hbx : Free b) {D S B : Addr} {n : Nat} {s₀ : State}

/-- The registers while the loops run: `i` bytes done, of the `n` at `S`. -/
structure Regs (d s b : Reg) (D S B : Addr) (n : Nat) (s₀ : State) (i : Nat) (σ : State) : Prop where
  rd : σ.gpr d = D
  rs : σ.gpr s = S
  rb : σ.gpr b = B
  rdx : σ.gpr .rdx = BitVec.ofNat 64 n
  rcx : σ.gpr .rcx = BitVec.ofNat 64 i
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → σ.gpr r = s₀.gpr r

/-- What the steps need of the regions. -/
structure Areas (D S B : Addr) (n : Nat) (s₀ : State) : Prop where
  dS : (⟨D, n⟩ : Region).Disjoint ⟨S, n⟩
  dB : (⟨D, n⟩ : Region).Disjoint ⟨B, n⟩
  lt : n < 2 ^ 64
  w : InRegions s₀.wr D n
  rS : InRegions (s₀.rd ++ s₀.wr) S n
  rB : InRegions (s₀.rd ++ s₀.wr) B n

include hdx hsx hbx in
theorem q_step (ha : Areas D S B n s₀) {j : Nat} (hj : j < n / 8)
    {σ : State} (hI : Inv D S B n s₀ (8 * j) σ) (hR : Regs d s b D S B n s₀ (8 * j) σ)
    (hax : σ.gpr .rax = BitVec.ofNat 64 (n / 8 - j)) :
    WP isa (.block (qBodyTo d s b)) σ fun σ' =>
      Inv D S B n s₀ (8 * (j + 1)) σ' ∧ Regs d s b D S B n s₀ (8 * (j + 1)) σ' ∧
        σ'.gpr .rax = BitVec.ofNat 64 (n / 8 - (j + 1)) ∧
        σ'.zf = some (decide (n / 8 - (j + 1) = 0)) ∧
        σ'.xmm = σ.xmm ∧ σ'.ymmHi = σ.ymmHi ∧ σ'.zmmHi = σ.zmmHi := by
  have hn := ha.lt
  have hi : 8 * j + 8 ≤ n := by omega
  have ea : ∀ P : Addr, P + BitVec.ofNat 64 (8 * j) * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      P + BitVec.ofNat 64 (8 * j) := fun _ => by simp
  have o₁ : InRegions σ.wr (D + BitVec.ofNat 64 (8 * j)) 8 := by rw [hI.wr]; exact inRegions_offset ha.w hi
  have i₂ : InRegions (σ.rd ++ σ.wr) (S + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset ha.rS hi
  have i₃ : InRegions (σ.rd ++ σ.wr) (B + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset ha.rB hi
  have e8 : 8 * (j + 1) = 8 * j + 8 := by omega
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, qBodyTo, idx, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, readSrc, execAlu, arithFlags, State.load64, State.store64, State.setReg,
    State.setFlags, hR.rd, hR.rs, hR.rb, hR.rcx, hbx.2.1, hdx.2.1, ea,
    i₂, i₃, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se8, se1]
  refine ⟨by rw [e8]; exact hI.qstep ha.dS ha.dB hn hi rfl rfl rfl,
    ⟨by simp [hdx.1, hdx.2.1, hdx.2.2, hR.rd], by simp [hsx.1, hsx.2.1, hsx.2.2, hR.rs],
    by simp [hbx.1, hbx.2.1, hbx.2.2, hR.rb],
    by simp [hR.rdx], by simp [e8, BitVec.ofNat_add],
    fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃, hR.keep r h₁ h₂ h₃]⟩, ?_, ?_, by simp⟩
  · simp only [hax]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [hax, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    simp only [decide_eq_decide]; omega

include hdx hsx hbx in
theorem b_step (ha : Areas D S B n s₀) {i : Nat} (hi : i < n)
    {σ : State} (hI : Inv D S B n s₀ i σ) (hR : Regs d s b D S B n s₀ i σ) :
    WP isa (.block (bBodyTo d s b)) σ fun σ' =>
      Inv D S B n s₀ (i + 1) σ' ∧ Regs d s b D S B n s₀ (i + 1) σ' ∧
        σ'.zf = some (decide (i + 1 = n)) ∧
        σ'.xmm = σ.xmm ∧ σ'.ymmHi = σ.ymmHi ∧ σ'.zmmHi = σ.zmmHi := by
  have hn := ha.lt
  have ea : ∀ P : Addr, P + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 =
      P + BitVec.ofNat 64 i := fun _ => by simp
  have o₁ : InRegions σ.wr (D + BitVec.ofNat 64 i) 1 := by rw [hI.wr]; exact inRegions_offset ha.w hi
  have i₂ : InRegions (σ.rd ++ σ.wr) (S + BitVec.ofNat 64 i) 1 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset ha.rS hi
  have i₃ : InRegions (σ.rd ++ σ.wr) (B + BitVec.ofNat 64 i) 1 := by
    rw [hI.rd, hI.wr]; exact inRegions_offset ha.rB hi
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, bBodyTo, idx, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.ea, readSrc, execAlu, arithFlags, State.load8, State.store8, State.setReg,
    State.setFlags, hR.rd, hR.rs, hR.rb, hR.rcx, hbx.1, hdx.1, hdx.2.1, ea,
    i₂, i₃, o₁, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se1]
  rw [xor_setWidth]
  refine ⟨hI.bstep ha.dS ha.dB hn hi rfl rfl rfl, ⟨by simp [hdx.1, hdx.2.1, hdx.2.2, hR.rd],
    by simp [hsx.1, hsx.2.1, hsx.2.2, hR.rs], by simp [hbx.1, hbx.2.1, hbx.2.2, hR.rb],
    by simp [hR.rdx], by simp [BitVec.ofNat_add],
    fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃, hR.keep r h₁ h₂ h₃]⟩, ?_, by simp⟩
  rw [hR.rdx, ← Offset.ofNat_sub_ofNat_beq (x := i + 1) (y := n) (by omega) (by omega),
    BitVec.ofNat_add]
  rfl

end

/-! ## The whole -/

/-- What `xorBufTo` does: byte `k < n` of the output is the XOR of byte `k`
of the data and of the buffer, the rest of memory and the registers but
`rax`, `r8` and `rcx` unchanged. -/
structure Post (D S B : Addr) (n : Nat) (s₀ s : State) : Prop where
  data : ∀ k < n, s.mem (D + BitVec.ofNat 64 k) =
    s₀.mem (S + BitVec.ofNat 64 k) ^^^ s₀.mem (B + BitVec.ofNat 64 k)
  frame : Frame [⟨D, n⟩] s₀.mem s.mem
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .rcx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm = s₀.xmm
  ymmHi : s.ymmHi = s₀.ymmHi
  zmmHi : s.zmmHi = s₀.zmmHi

theorem xorBufTo_ok {d s b : Reg} (hdx : Free d) (hsx : Free s) (hbx : Free b) {D S B : Addr} {n : Nat}
    {s₀ : State} (hD : s₀.gpr d = D) (hS : s₀.gpr s = S) (hB : s₀.gpr b = B)
    (hrdx : s₀.gpr .rdx = BitVec.ofNat 64 n) (ha : Areas D S B n s₀) :
    WP isa (xorBufTo d s b) s₀ (Post D S B n s₀) := by
  have hn := ha.lt
  let V : State → Prop := fun σ => σ.xmm = s₀.xmm ∧ σ.ymmHi = s₀.ymmHi ∧ σ.zmmHi = s₀.zmmHi
  have hI0 : Inv D S B n s₀ 0 s₀ :=
    ⟨fun k hk => by simp, Frame.refl _ _, rfl, rfl⟩
  -- The prologue.
  have h₁ : WP isa (.block [.mov32 .rcx (.imm 0), .mov .rax (.reg .rdx), .shift .shr .rax 3]) s₀
      fun σ => Inv D S B n s₀ 0 σ ∧ Regs d s b D S B n s₀ 0 σ ∧ σ.gpr .rax = BitVec.ofNat 64 (n / 8) ∧
        σ.zf = some (decide (n / 8 = 0)) ∧ V σ := by
    apply WP.of_runBlock
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, and_self, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, readSrc32, execShift, State.setReg, State.setReg32, State.setFlags,
      Option.map_some, Option.some.injEq, exists_eq_left', hrdx]
    have hs : BitVec.ofNat 64 n >>> 3 = BitVec.ofNat 64 (n / 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
        Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨hI0.data, hI0.frame, rfl, rfl⟩, ⟨by simp [hdx.1, hdx.2.2, hD], by simp [hsx.1, hsx.2.2, hS],
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
  let Q : State → Prop := fun σ => Inv D S B n s₀ (8 * (n / 8)) σ ∧ Regs d s b D S B n s₀ (8 * (n / 8)) σ ∧ V σ
  have h₂ : ∀ σ, (Inv D S B n s₀ 0 σ ∧ Regs d s b D S B n s₀ 0 σ ∧ σ.gpr .rax = BitVec.ofNat 64 (n / 8) ∧
      σ.zf = some (decide (n / 8 = 0)) ∧ V σ) →
      WP isa (.ite .e (.block []) (.loop (.block (qBodyTo d s b)) .ne)) σ Q := by
    rintro σ ⟨hI, hR, hax, hz, hV⟩
    refine WP.ite (decide (n / 8 = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨cast (congrArg (fun i => Inv D S B n s₀ (8 * i) σ) h.symm) hI,
        cast (congrArg (fun i => Regs d s b D S B n s₀ (8 * i) σ) h.symm) hR, hV⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv' : Nat → State → Prop := fun c σ => ∃ j, c = n / 8 - j ∧ j < n / 8 ∧
        Inv D S B n s₀ (8 * j) σ ∧ Regs d s b D S B n s₀ (8 * j) σ ∧ σ.gpr .rax = BitVec.ofNat 64 (n / 8 - j) ∧
        V σ
      have hstep : ∀ c σ, Inv' c σ → WP isa (.block (qBodyTo d s b)) σ (fun σ' =>
          (eval .ne σ' = some false ∧ Q σ') ∨ (eval .ne σ' = some true ∧ ∃ c' < c, Inv' c' σ')) := by
        rintro c σ ⟨j, rfl, hj, hI, hR, hax, hV⟩
        refine WP.mono (q_step hdx hsx hbx ha hj hI hR hax)
          fun σ' ⟨hI', hR', hax', hz', x₁, x₂, x₃⟩ => ?_
        have hV' : V σ' := ⟨x₁.trans hV.1, x₂.trans hV.2.1, x₃.trans hV.2.2⟩
        by_cases hl : n / 8 - (j + 1) = 0
        · have e : j + 1 = n / 8 := by omega
          exact .inl ⟨by simp [eval, hz', hl], cast (congrArg (fun i => Inv D S B n s₀ (8 * i) σ') e) hI',
            cast (congrArg (fun i => Regs d s b D S B n s₀ (8 * i) σ') e) hR', hV'⟩
        · exact .inr ⟨by simp [eval, hz', hl], n / 8 - (j + 1), by omega, j + 1, rfl, by omega,
            hI', hR', hax', hV'⟩
      exact WP.loop (M := isa) Inv' hstep (n / 8 - 0) σ ⟨0, rfl, by omega, hI, hR, by simpa using hax, hV⟩
  -- The bytes.
  let F : State → Prop := fun σ => Inv D S B n s₀ n σ ∧ Regs d s b D S B n s₀ n σ ∧ V σ
  have h₃ : ∀ σ, Q σ → WP isa (.seq (.block [.alu .cmp .rcx (.reg .rdx)])
      (.ite .e (.block []) (.loop (.block (bBodyTo d s b)) .ne))) σ F := by
    rintro σ ⟨hI, hR, hV⟩
    have hle : 8 * (n / 8) ≤ n := by omega
    have hc : WP isa (.block [.alu .cmp .rcx (.reg .rdx)]) σ fun σ' =>
        Inv D S B n s₀ (8 * (n / 8)) σ' ∧ Regs d s b D S B n s₀ (8 * (n / 8)) σ' ∧ V σ' ∧
          σ'.zf = some (decide (8 * (n / 8) = n)) := by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
        State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
      refine ⟨⟨hI.data, hI.frame, hI.rd, hI.wr⟩, ⟨hR.rd, hR.rs, hR.rb, hR.rdx, hR.rcx, hR.keep⟩, hV, ?_⟩
      rw [hR.rcx, hR.rdx, Offset.ofNat_sub_ofNat_beq (by omega) hn]
    refine WP.seq (WP.mono hc fun σ₁ ⟨hI₁, hR₁, hV₁, hz₁⟩ => ?_)
    refine WP.ite (decide (8 * (n / 8) = n)) (by simp [eval, hz₁]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨cast (congrArg (fun i => Inv D S B n s₀ i σ₁) h) hI₁,
        cast (congrArg (fun i => Regs d s b D S B n s₀ i σ₁) h) hR₁, hV₁⟩
    · simp only [decide_eq_false_iff_not] at h
      let Inv' : Nat → State → Prop := fun c σ => ∃ i, c = n - i ∧ i < n ∧
        Inv D S B n s₀ i σ ∧ Regs d s b D S B n s₀ i σ ∧ V σ
      have hstep : ∀ c σ, Inv' c σ → WP isa (.block (bBodyTo d s b)) σ (fun σ' =>
          (eval .ne σ' = some false ∧ F σ') ∨ (eval .ne σ' = some true ∧ ∃ c' < c, Inv' c' σ')) := by
        rintro c σ ⟨i, rfl, hi, hI, hR, hV⟩
        refine WP.mono (b_step hdx hsx hbx ha hi hI hR)
          fun σ' ⟨hI', hR', hz', x₁, x₂, x₃⟩ => ?_
        have hV' : V σ' := ⟨x₁.trans hV.1, x₂.trans hV.2.1, x₃.trans hV.2.2⟩
        by_cases hl : i + 1 = n
        · exact .inl ⟨by simp [eval, hz', hl], cast (congrArg (fun i => Inv D S B n s₀ i σ') hl) hI',
            cast (congrArg (fun i => Regs d s b D S B n s₀ i σ') hl) hR', hV'⟩
        · exact .inr ⟨by simp [eval, hz', hl], n - (i + 1), by omega, i + 1, rfl, by omega, hI', hR', hV'⟩
      exact WP.loop (M := isa) Inv' hstep (n - 8 * (n / 8)) σ₁ ⟨8 * (n / 8), rfl, by omega, hI₁, hR₁, hV₁⟩
  refine WP.seq (WP.mono h₁ fun σ h => WP.seq (WP.mono (h₂ σ h) fun σ' hq =>
    WP.mono (h₃ σ' hq) fun σ'' hf => ?_))
  obtain ⟨hI, hR, hV⟩ := hf
  exact ⟨fun k hk => by rw [hI.data k hk, ite_eq_left hk], hI.frame, hR.keep, hI.rd, hI.wr,
    hV.1, hV.2.1, hV.2.2⟩

end VG.Proof.ChaCha20.X86_64.XorBufTo
