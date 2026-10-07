import VerifiedGarbage.Proof.Mont.X86_64.MulPX

/-!
# Montgomery arithmetic on x86-64: P-521's sums and differences

`addMer o a b` and `subMer o a b` (`Impl/Mont/X86_64.lean`) for `p = 2⁵²¹ - 1`:
the sum `[a] + [b]`, or `[a] + (p - [b])`, below `2p`, plus one, in
`xWin 9`, reduced below `p` by `xCanon` (`xCanon_ok`, `MulPX.lean`): the sum
with a carry of one in (`setCF_ok`, `chainAdcX_ok`), and `[a] - [b] + 2⁵²¹`
(`chainSubX_ok`, `add512_ok`).

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

/-- `chainSbb_ok` for `FreshX` registers. -/
theorem chainSbbX_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat} {c : Bool},
    Scr s base size → s.cf = some c → b + 8 * ts.length ≤ size → FreshX ts →
    WP isa (.block (chain .sbb .sbb ts b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + wordsVal s.mem base b ts.length + c.toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * c'.toNat ∧ Keeps ts s s'
  | [], s, _, _, c, _, hc, _, _ => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, c, hs, hc, hb, hf => by
    simp only [List.length_cons] at hb
    rw [chain, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .sbb t (.mem (sc b))]) s (fun s₁ =>
        (s₁.gpr t).toNat + (word s.mem base b).toNat + c.toNat = (s.gpr t).toNat +
          2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base b).toNat + c.toNat)).toNat ∧
        s₁.cf = some (decide ((s.gpr t).toNat < (word s.mem base b).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc_sc hs (d := b) (by omega), Option.bind_some, Option.map_some, hc, RegUpd.gpr_setReg,
        RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      · have := sbb_borrow (s.gpr t) (word s.mem base b) c
        omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
    refine WP.mono (chainSbbX_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR, k₁.2.1] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega

/-- `chainSub_ok` for `FreshX` registers. -/
theorem chainSubX_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hf : FreshX (t :: ts)) :
    WP isa (.block (chain .sub .sbb (t :: ts) b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' (t :: ts) + wordsVal s.mem base b (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * c'.toNat ∧ Keeps (t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  rw [chain, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .sub t (.mem (sc b))]) s (fun s₁ =>
      (s₁.gpr t).toNat + (word s.mem base b).toNat = (s.gpr t).toNat +
        2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base b).toNat)).toNat ∧
      s₁.cf = some (decide ((s.gpr t).toNat < (word s.mem base b).toNat)) ∧
      Keeps [t] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc_sc hs (d := b) (by omega), Option.bind_some, RegUpd.gpr_setReg,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨sub_borrow _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
  refine WP.mono (chainSbbX_ok ts hs₁ c₁ (b := b + 8) (by omega) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
  rw [hR, k₁.2.1] at e₂
  refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  rw [Nat.mul_assoc]
  omega

/-- The registers `addMer` and `subMer` write, but `rax`. -/
theorem xWin_clob {r : Reg} {M : Mod} (hr : r ∉ clob M.n) (hn9 : M.n = 9) :
    r ≠ .rax ∧ r ∉ xWin 9 ∧ r ∉ Reg.rax :: xRegs := by
  have hr' : r ∉ Reg.rax :: xRegs := fun h => hr (by rw [hn9]; exact xRegs_clob r (by
    rcases List.mem_cons.mp h with h | h
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))))
  exact ⟨fun h => hr' (h ▸ List.mem_cons_self ..), fun h => hr' (List.mem_cons_of_mem _ (xWin_sub 9 r h)), hr'⟩

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
  rw [addMer, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadsX_ok (xWin 9) hs (a := a) (by simp [xWin]; omega) (xWin_fresh 9))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [WP.block_append_iff]
  refine WP.mono (setCF_ok s₁) fun s₂ ⟨c₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainAdcX_ok (xWin 9) hs₂ c₂ (b := b) (by simp [xWin]; omega) (xWin_fresh 9))
    fun s₃ ⟨c₃, _, e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  have hR₂ : regsVal s₂ (xWin 9) = regsVal s₁ (xWin 9) := regsVal_congr fun q hq => k₂.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => (xWin_fresh 9).2 q hq |>.1 h)
  rw [Nat.pow_mul, show (xWin 9).length = 9 from rfl, hR₂, e₁, k₂.2.1, k₁.2.1] at e₃
  rw [show (xWin 9).length = 9 from rfl] at e₃
  simp only [Bool.toNat_true] at e₃
  have hc := Bool.toNat_le c₃
  have hT : hval (xg s₃) 9 9 = wordsVal s.mem base a 9 + wordsVal s.mem base b 9 + 1 := by
    rw [← regsVal_xWin]
    omega
  refine WP.mono (xCanon_ok hs₃ (o := o) ho hm (by rw [hT]; omega) (by rw [hT]; omega))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · obtain ⟨ra, hw, hr'⟩ := xWin_clob hr hn9
    rw [k₄.gpr r hr', k₃.1 r hw, k₂.1 r (by simpa using ra), k₁.1 r hw]
  · rw [k₄.rd, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₄.wr, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [hn9] at hx
    rw [O₄ x hx, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [e₄, hT, Nat.add_sub_cancel]

/-- `add t, 512`. -/
theorem add512_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .add t (.imm 512)]) s fun s' =>
      ∃ c : Bool, (s'.gpr t).toNat + 2 ^ 64 * c.toNat = (s.gpr t).toNat + 512 ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨decide (2 ^ 64 ≤ (s.gpr t).toNat + 512), ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h : ((512 : BitVec 32).signExtend 64).toNat = 512 := by decide
    have := add_carry (s.gpr t) ((512 : BitVec 32).signExtend 64)
    rw [h] at this
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

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
  rw [subMer, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadsX_ok (xWin 9) hs (a := a) (by simp [xWin]; omega) (xWin_fresh 9))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [WP.block_append_iff, xWin9]
  refine WP.mono (chainSubX_ok hs₁ (b := b) (by simp [xHi]; omega) (xWin_fresh 9))
    fun s₂ ⟨c₂, _, e₂, k₂⟩ => ?_
  rw [← xWin9] at e₂ k₂
  have hs₂ := hs₁.of_keeps k₂ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [e₁, k₁.2.1, Nat.pow_mul, show (xWin 9).length = 9 from rfl] at e₂
  rw [WP.block_append_iff]
  refine WP.mono (add512_ok s₂ (xAcc 17)) fun s₃ ⟨c₃, e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by simpa using (xAcc_ne 17).2.2.2.1.symm)
  -- `[a] - [b] + 2⁵²¹` in the registers.
  have hlo : hval (xg s₃) 9 8 = hval (xg s₂) 9 8 := hval_congr fun c h1 h2 => by
    simp only [xg]
    rw [k₃.1 _ (by simpa using xAcc_ne_of (show c < 17 by omega) (by omega))]
  have hD : hval (xg s₃) 9 9 = wordsVal s.mem base a 9 + m + 1 - wordsVal s.mem base b 9 := by
    rw [regsVal_xWin, hval_succ_last] at e₂
    rw [hval_succ_last, hlo]
    change xg s₃ 17 + 2 ^ 64 * c₃.toNat = xg s₂ 17 + 512 at e₃
    have h17 := (s₃.gpr (xAcc 17)).isLt
    have hl := hval_lt (f := xg s₂) (k := 9) (n := 8) fun c _ _ => (s₂.gpr _).isLt
    have hc₂ := Bool.toNat_le c₂
    have hc₃ := Bool.toNat_le c₃
    change xg s₃ 17 < 2 ^ 64 at h17
    generalize hval (xg s₂) 9 8 = L at *
    have h17' : xg s₂ 17 < 2 ^ 64 := (s₂.gpr _).isLt
    rw [show (9 : Nat) + 8 = 17 from rfl] at e₂ ⊢
    have hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega
    subst hm'
    omega
  refine WP.mono (xCanon_ok hs₃ (o := o) ho hm (by rw [hD]; omega) (by rw [hD]; omega))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · obtain ⟨_, hw, hr'⟩ := xWin_clob hr hn9
    have h17 : r ≠ xAcc 17 := fun h => hw (h ▸ by decide)
    rw [k₄.gpr r hr', k₃.1 r (by simpa using h17), k₂.1 r hw, k₁.1 r hw]
  · rw [k₄.rd, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₄.wr, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [hn9] at hx
    rw [O₄ x hx, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [e₄, hD, show wordsVal s.mem base a 9 + m + 1 - wordsVal s.mem base b 9 - 1 =
      wordsVal s.mem base a 9 + m - wordsVal s.mem base b 9 by omega]

end VG.Proof.Mont.X86_64
