import VerifiedGarbage.Proof.Mont.X86_64.MulPX

/-!
# Montgomery arithmetic on x86-64: P-521's sums and differences

`addMer o a b` and `subMer o a b` (`Impl/Mont/X86_64.lean`) for `p = 2⁵²¹ - 1`:
the sum `[a] + [b]`, or `[a] + (p - [b])`, below `2p` in `xWin 9`, reduced
below `p` by `xCanon` (`xCanon_ok`, `MulPX.lean`). `p - [b]` (`negMer_ok`) is
the complement of `[b]`'s low eight words and `511 - b₈`.

The loads and the additions are `Chain.lean`'s for registers that may
include `rbp` (`FreshX`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry sub_borrow sbb_borrow)

/-- `loads_ok` for `FreshX` registers. -/
theorem loadsX_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {a : Nat},
    Scr s base size → a + 8 * ts.length ≤ size → FreshX ts →
    WP isa (.block (loads ts a)) s fun s' =>
      regsVal s' ts = wordsVal s.mem base a ts.length ∧ Keeps ts s s'
  | [], s, _, _, _, _, _ => WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, a, hs, ha, hf => by
    simp only [List.length_cons] at ha
    rw [loads, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov t (.mem (sc a))]) s
        (fun s₁ => s₁.gpr t = word s.mem base a ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := a) (by omega),
        Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
    refine WP.mono (loadsX_ok ts hs₁ (a := a + 8) (by omega) hf.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [List.length_cons, regsVal, wordsVal, ht, e₁, e₂, k₁.2.1]

/-- `chainAdc_ok` for `FreshX` registers. -/
theorem chainAdcX_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat} {c : Bool},
    Scr s base size → s.cf = some c → b + 8 * ts.length ≤ size → FreshX ts →
    WP isa (.block (chain .adc .adc ts b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat =
        regsVal s ts + wordsVal s.mem base b ts.length + c.toNat ∧ Keeps ts s s'
  | [], s, _, _, c, _, hc, _, _ => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, c, hs, hc, hb, hf => by
    simp only [List.length_cons] at hb
    rw [chain, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .adc t (.mem (sc b))]) s (fun s₁ =>
        (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat +
          c.toNat)).toNat = (s.gpr t).toNat + (word s.mem base b).toNat + c.toNat ∧
        s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc_sc hs (d := b) (by omega), Option.bind_some, Option.map_some, hc, RegUpd.gpr_setReg,
        RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨adc_carry _ _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
    refine WP.mono (chainAdcX_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR, k₁.2.1] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega

/-- `chainAdd_ok` for `FreshX` registers. -/
theorem chainAddX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hf : FreshX (t :: ts)) :
    WP isa (.block (chain .add .adc (t :: ts) b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' (t :: ts) + 2 ^ (64 * (t :: ts).length) * c'.toNat =
        regsVal s (t :: ts) + wordsVal s.mem base b (t :: ts).length ∧ Keeps (t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  rw [chain, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .add t (.mem (sc b))]) s (fun s₁ =>
      (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat +
        (word s.mem base b).toNat)).toNat = (s.gpr t).toNat + (word s.mem base b).toNat ∧
      s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat)) ∧
      Keeps [t] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc_sc hs (d := b) (by omega), Option.bind_some, RegUpd.gpr_setReg,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨add_carry _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
  refine WP.mono (chainAdcX_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
  rw [hR, k₁.2.1] at e₂
  refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  rw [Nat.mul_assoc]
  omega

/-- `[o] = [a] + [b] mod p` for P-521's `p`. -/
theorem addMer_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a b : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hAB : wordsVal s.mem base a M.n + wordsVal s.mem base b M.n < 2 * m) :
    WP isa (.block (addMer o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base b M.n) % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  have hnw := hs.nowrap
  rw [hn9] at ho ha hb hAB ⊢
  rw [addMer, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadsX_ok (xWin 9) hs (a := a) (by simp [xWin]; omega) (xWin_fresh 9))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [WP.block_append_iff, xWin9]
  refine WP.mono (chainAddX_ok hs₁ (b := b) (by simp [xHi]; omega) (xWin_fresh 9))
    fun s₂ ⟨c₂, _, e₂, k₂⟩ => ?_
  rw [← xWin9] at e₂ k₂
  have hs₂ := hs₁.of_keeps k₂ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [Nat.pow_mul] at e₂
  rw [show (xWin 9).length = 9 from rfl] at e₁ e₂
  rw [e₁, k₁.2.1] at e₂
  have hc : c₂.toNat = 0 := by
    have := Bool.toNat_le c₂
    omega
  rw [hc, Nat.mul_zero, Nat.add_zero] at e₂
  have hW : hval (xg s₂) 9 9 < 2 * m := by rw [← regsVal_xWin, e₂]; exact hAB
  refine WP.mono (xCanon_ok hs₂ (o := o) ho hm hW) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · have hr' : r ∉ Reg.rax :: xRegs := fun h => hr (by rw [hn9]; exact xRegs_clob r (by
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
    have hw : r ∉ xWin 9 := fun h => hr' (List.mem_cons_of_mem _ (xWin_sub 9 r h))
    rw [k₃.gpr r hr', k₂.1 r hw, k₁.1 r hw]
  · rw [k₃.rd, k₂.2.2.1, k₁.2.2.1]
  · rw [k₃.wr, k₂.2.2.2, k₁.2.2.2]
  · rw [hn9] at hx
    rw [O₃ x hx, k₂.2.1, k₁.2.1]
  · rw [e₃, ← regsVal_xWin, e₂]

/-- `xor t, -1`: `t`'s complement. -/
theorem xorNeg_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .xor t (.imm (-1))]) s fun s' =>
      (s'.gpr t).toNat = 2 ^ 64 - 1 - (s.gpr t).toNat ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [show ((-1 : BitVec 32).signExtend 64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes,
      BitVec.toNat_not]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The words `ts` complemented. -/
theorem notWords_ok : ∀ (ts : List Reg) {s : State}, ts.Nodup →
    WP isa (.block (ts.map fun t => .alu .xor t (.imm (-1)))) s fun s' =>
      regsVal s' ts + regsVal s ts + 1 = 2 ^ (64 * ts.length) ∧ Keeps ts s s'
  | [], s, _ => WP.block_nil ⟨by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, hn => by
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (xorNeg_ok s t) fun s₁ ⟨e₁, k₁⟩ => ?_
    have htn := (List.nodup_cons.mp hn).1
    refine WP.mono (notWords_ok ts (List.nodup_cons.mp hn).2) fun s₂ ⟨e₂, k₂⟩ =>
      ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => htn (h ▸ hq))
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t htn
    rw [hR] at e₂
    simp only [regsVal, List.length_cons, ht]
    have := (s.gpr t).isLt
    rw [show 64 * (ts.length + 1) = 64 + 64 * ts.length by omega, Nat.pow_add]
    generalize 2 ^ (64 * ts.length) = Q at *
    generalize regsVal s₂ ts = R₂ at *
    generalize regsVal s ts = R at *
    rw [← e₂]
    have : 2 ^ 64 * (R₂ + R + 1) = 2 ^ 64 * R₂ + 2 ^ 64 * R + 2 ^ 64 := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega

/-- `mov r32, 511`. -/
theorem mov511_ok (s : State) (t : Reg) :
    WP isa (.block [.mov32 t (.imm 511)]) s fun s' => (s'.gpr t).toNat = 511 ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `sub t, [d]`. -/
theorem subMem_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t : Reg) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.alu .sub t (.mem (sc d))]) s fun s' =>
      ∃ c : Bool, (s'.gpr t).toNat + (word s.mem base d).toNat = (s.gpr t).toNat + 2 ^ 64 * c.toNat ∧
        Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs hd,
    Option.bind_some, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨_, VG.Proof.X25519.X86_64.sub_borrow _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem xWin9_split : xWin 9 = xLo8 ++ [xAcc 17] := rfl

theorem xLo8_fresh : FreshX xLo8 := by unfold FreshX; decide

theorem xAcc17_notin : xAcc 17 ∉ xLo8 := by decide

/-- `p - [b]` in `xWin 9`, for `[b] < p`. -/
theorem negMer_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {b m : Nat}
    (hb : b + 72 ≤ size) (hm : m + 1 = 512 * (2 ^ 64) ^ 8) (hB : wordsVal s.mem base b 9 < m) :
    WP isa (.block (negMer b)) s fun s' =>
      regsVal s' (xWin 9) + wordsVal s.mem base b 9 = m ∧ Keeps (xWin 9) s s' := by
  have hnw := hs.nowrap
  rw [negMer, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadsX_ok xLo8 hs (a := b) (by simp [xLo8]; omega) xLo8_fresh) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (notWords_ok xLo8 xLo8_fresh.1) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (mov511_ok s₂ (xAcc 17)) fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (subMem_ok hs₃ (xAcc 17) (d := b + 64) (by omega)) fun s₄ ⟨c₄, e₄, k₄⟩ => ⟨?_, ?_⟩
  · have hL : regsVal s₄ xLo8 = regsVal s₂ xLo8 := regsVal_congr fun q hq => by
      have hq17 : q ≠ xAcc 17 := fun h => xAcc17_notin (h ▸ hq)
      rw [k₄.1 q (by simpa using hq17), k₃.1 q (by simpa using hq17)]
    have hm₃ : s₃.mem = s.mem := k₃.2.1.trans (k₂.2.1.trans k₁.2.1)
    rw [hm₃, show b + 64 = b + 8 * 8 by omega] at e₄
    rw [Nat.pow_mul] at e₂
    rw [show xLo8.length = 8 from rfl] at e₁ e₂
    rw [xWin9_split, regsVal_append, hL, Nat.pow_mul, show xLo8.length = 8 from rfl]
    simp only [regsVal, Nat.mul_zero, Nat.add_zero]
    have hb9 : wordsVal s.mem base b 9 = wordsVal s.mem base b 8 +
        (2 ^ 64) ^ 8 * (word s.mem base (b + 8 * 8)).toNat := wordsVal_succ_last _ _ _ 8
    rw [hb9] at hB ⊢
    rw [← e₁] at hB ⊢
    have h8 := (word s.mem base (b + 8 * 8)).isLt
    have hc := Bool.toNat_le c₄
    have hx := (s₄.gpr (xAcc 17)).isLt
    rw [e₃] at e₄
    generalize (word s.mem base (b + 8 * 8)).toNat = B8 at *
    generalize regsVal s₁ xLo8 = Blo at *
    generalize regsVal s₂ xLo8 = N at *
    generalize (s₄.gpr (xAcc 17)).toNat = T at *
    omega
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · have h1 : r ∉ xLo8 := fun h => hr (by rw [xWin9_split]; exact List.mem_append_left _ h)
      have h2 : r ≠ xAcc 17 := fun h => hr (by rw [xWin9_split, h]; simp)
      rw [k₄.1 r (by simpa using h2), k₃.1 r (by simpa using h2), k₂.1 r h1, k₁.1 r h1]
    · rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
    · rw [k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]

/-- `[o] = [a] - [b] mod p` for P-521's `p`. -/
theorem subMer_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a b : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (subMer o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  have hnw := hs.nowrap
  rw [hn9] at ho ha hb hA hB ⊢
  rw [subMer, List.append_assoc, WP.block_append_iff]
  refine WP.mono (negMer_ok hs (b := b) (by omega) hm hB) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [WP.block_append_iff, xWin9]
  refine WP.mono (chainAddX_ok hs₁ (b := a) (by simp [xHi]; omega) (xWin_fresh 9))
    fun s₂ ⟨c₂, _, e₂, k₂⟩ => ?_
  rw [← xWin9] at e₂ k₂
  have hs₂ := hs₁.of_keeps k₂ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [Nat.pow_mul] at e₂
  rw [show (xWin 9).length = 9 from rfl, k₁.2.1] at e₂
  have hc : c₂.toNat = 0 := by
    have := Bool.toNat_le c₂
    omega
  rw [hc, Nat.mul_zero, Nat.add_zero] at e₂
  have hW : hval (xg s₂) 9 9 < 2 * m := by rw [← regsVal_xWin, e₂]; omega
  refine WP.mono (xCanon_ok hs₂ (o := o) ho hm hW) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · have hr' : r ∉ Reg.rax :: xRegs := fun h => hr (by rw [hn9]; exact xRegs_clob r (by
      rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
    have hw : r ∉ xWin 9 := fun h => hr' (List.mem_cons_of_mem _ (xWin_sub 9 r h))
    rw [k₃.gpr r hr', k₂.1 r hw, k₁.1 r hw]
  · rw [k₃.rd, k₂.2.2.1, k₁.2.2.1]
  · rw [k₃.wr, k₂.2.2.2, k₁.2.2.2]
  · rw [hn9] at hx
    rw [O₃ x hx, k₂.2.1, k₁.2.1]
  · rw [e₃, ← regsVal_xWin, e₂, show regsVal s₁ (xWin 9) + wordsVal s.mem base a 9 =
      wordsVal s.mem base a 9 + m - wordsVal s.mem base b 9 by omega]

end VG.Proof.Mont.X86_64
