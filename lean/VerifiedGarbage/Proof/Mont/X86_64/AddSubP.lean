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
  refine WP.mono (xCanon_ok hs₃.toC (o := o) ho hm (by rw [hT]; omega) (by rw [hT]; omega))
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
  refine WP.mono (xCanon_ok hs₃.toC (o := o) ho hm (by rw [hD]; omega) (by rw [hD]; omega))
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

/-! ## Doubling -/

/-- `dblChain .adc` for `FreshX` registers: twice their number, plus the
carry in. -/
theorem dblAdcX_ok : ∀ (ts : List Reg) {s : State} {c : Bool}, s.cf = some c → FreshX ts →
    WP isa (.block (dblChain .adc ts)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat = 2 * regsVal s ts + c.toNat ∧ Keeps ts s s'
  | [], s, c, hc, _ => WP.block_nil ⟨c, hc, by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, c, hc, hf => by
    rw [dblChain, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .adc t (.reg t)]) s (fun s₁ =>
        (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat + (s.gpr t).toNat +
          c.toNat)).toNat = (s.gpr t).toNat + (s.gpr t).toNat + c.toNat ∧
        s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (s.gpr t).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
        Option.map_some, hc, RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
        Option.some.injEq, exists_eq_left']
      refine ⟨adc_carry _ _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    refine WP.mono (dblAdcX_ok ts c₁ hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega

/-- `dblChain .add` for `FreshX` registers: twice their number, its first
word even. -/
theorem dblChainX_ok {s : State} {t : Reg} {ts : List Reg} (hf : FreshX (t :: ts)) :
    WP isa (.block (dblChain .add (t :: ts))) s fun s' => ∃ c' : Bool,
      regsVal s' (t :: ts) + 2 ^ (64 * (t :: ts).length) * c'.toNat = 2 * regsVal s (t :: ts) ∧
      (s'.gpr t).toNat % 2 = 0 ∧ Keeps (t :: ts) s s' := by
  rw [dblChain, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .add t (.reg t)]) s (fun s₁ =>
      (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat + (s.gpr t).toNat)).toNat =
        (s.gpr t).toNat + (s.gpr t).toNat ∧
      s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (s.gpr t).toNat)) ∧ Keeps [t] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.gpr_setReg_self, RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.some.injEq,
      exists_eq_left']
    refine ⟨add_carry _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  refine WP.mono (dblAdcX_ok ts c₁ hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
  rw [hR] at e₂
  refine ⟨c', ?_, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  · simp only [regsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega
  · rw [ht]; omega

/-- `rax = ⌊t / 512⌋`. -/
theorem top_ok (s : State) (t : Reg) :
    WP isa (.block [.mov .rax (.reg t), .shift .shr .rax 9]) s fun s' =>
      (s'.gpr .rax).toNat = (s.gpr t).toNat / 512 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc,
    Option.map_some, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left',
    show 1 ≤ 9 ∧ 9 ≤ 63 from ⟨by decide, by decide⟩, and_self, ite_true]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

/-- `add t, rax`. -/
theorem addRax_ok (s : State) (t : Reg) :
    WP isa (.block [.alu .add t (.reg .rax)]) s fun s' =>
      ∃ c : Bool, (s'.gpr t).toNat + 2 ^ 64 * c.toNat = (s.gpr t).toNat + (s.gpr .rax).toNat ∧
        Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨_, add_carry _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The arithmetic of `dblMer`: `2A = x₉ + 2⁶⁴ (L + 2⁴⁴⁸ x₁₇)` with `x₉`
even, and bit 521 moved into bit 0. -/
theorem dbl_arith {m A L x9 x17 y9 c₂ c₄ : Nat} (hm : m + 1 = 512 * (2 ^ 64) ^ 8)
    (hA : A + A < 2 * m) (e₂ : x9 + 2 ^ 64 * (L + (2 ^ 64) ^ 7 * x17) + (2 ^ 64) ^ 9 * c₂ = 2 * A)
    (ev : x9 % 2 = 0) (hL : L < (2 ^ 64) ^ 7) (hx9 : x9 < 2 ^ 64) (hx17 : x17 < 2 ^ 64)
    (hc₂ : c₂ ≤ 1) (e₄ : y9 + 2 ^ 64 * c₄ = x9 + x17 / 512) :
    y9 + 2 ^ 64 * (L + (2 ^ 64) ^ 7 * (x17 % 512)) = (A + A) % m := by
  have hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega
  subst hm'
  have hc0 : c₂ = 0 := by omega
  subst hc0
  have h17 : x17 < 1024 := by omega
  by_cases hlt : x17 < 512
  · rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt] at *
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [show x17 / 512 = 1 by omega] at e₄
    rw [show x17 % 512 = x17 - 512 by omega, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- `[o] = 2 [a] mod p` for P-521's `p`. -/
theorem dblMer_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size)
    (hAA : wordsVal s.mem base a M.n + wordsVal s.mem base a M.n < 2 * m) :
    WP isa (.block (dblMer o a)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + wordsVal s.mem base a M.n) % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  have hnw := hs.nowrap
  rw [hn9] at ho ha hAA ⊢
  rw [dblMer, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadsX_ok (xWin 9) hs (a := a) (by simp [xWin]; omega) (xWin_fresh 9))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff, xWin9]
  refine WP.mono (dblChainX_ok (s := s₁) (xWin_fresh 9)) fun s₂ ⟨c₂, e₂, ev₂, k₂⟩ => ?_
  rw [← xWin9] at e₂ k₂
  rw [e₁, Nat.pow_mul, show (xWin 9).length = 9 from rfl] at e₂
  rw [show ([.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9, .alu .add (xAcc 9) (.reg .rax),
      .alu .and (xAcc 17) (.imm 511)] : List Instr) = [.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9] ++
      ([.alu .add (xAcc 9) (.reg .rax)] : List Instr) ++ [.alu .and (xAcc 17) (.imm 511)] from rfl,
    List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (top_ok s₂ (xAcc 17)) fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok s₃ (xAcc 9)) fun s₄ ⟨c₄, e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (and511_ok s₄ (xAcc 17)) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hK : Keeps (.rax :: xRegs) s s₅ := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · have hw : r ∉ xWin 9 := fun h => hr (List.mem_cons_of_mem _ (xWin_sub 9 r h))
      rw [k₅.1 r (fun h => hw ((List.mem_singleton.mp h) ▸ by decide)),
        k₄.1 r (fun h => hw ((List.mem_singleton.mp h) ▸ by decide)),
        k₃.1 r (fun h => hr (by simp at h; simp [h])), k₂.1 r hw, k₁.1 r hw]
    · rw [k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
    · rw [k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  have hs₅ : Scr s₅ base size := hs.of_keeps hK (by decide)
  refine WP.mono (stores_ok (xWin 9) hs₅ (o := o) (by simp [xWin]; omega) (xWin_fresh 9).1)
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hK₆ := (Keeps.regs hK).trans (k₆.mono (by simp))
  refine ⟨⟨fun r hr => ?_, hK₆.rd, hK₆.wr, fun x hx _ => ?_⟩, ?_⟩
  · exact hK₆.gpr r (xWin_clob hr hn9).2.2
  · rw [hn9] at hx
    rw [O₆ x (by rw [show (xWin 9).length = 9 from rfl]; exact hx), ← hK.2.1]
  · rw [show (xWin 9).length = 9 from rfl] at e₆
    rw [e₆, regsVal_xWin]
    rw [regsVal_xWin] at e₂
    have n17 : ∀ c, 10 ≤ c → c < 17 → xAcc c ≠ xAcc 17 := fun c h1 h2 => xAcc_ne_of (by omega) (by omega)
    have n9 : ∀ c, 10 ≤ c → c < 18 → xAcc c ≠ xAcc 9 := fun c h1 h2 =>
      (xAcc_ne_of (show 9 < c by omega) (by omega)).symm
    have hL : hval (xg s₅) 10 7 = hval (xg s₂) 10 7 := hval_congr fun c h1 h2 => by
      simp only [xg]
      rw [k₅.1 _ (by simpa using n17 c h1 (by omega)), k₄.1 _ (by simpa using n9 c h1 (by omega)),
        k₃.1 _ (by simpa using (xAcc_ne c).1)]
    have h₅ : hval (xg s₅) 9 9 = xg s₅ 9 + 2 ^ 64 * (hval (xg s₅) 10 7 + (2 ^ 64) ^ 7 * xg s₅ 17) := by
      rw [← hval_succ_last]; rfl
    have h₂ : hval (xg s₂) 9 9 = xg s₂ 9 + 2 ^ 64 * (hval (xg s₂) 10 7 + (2 ^ 64) ^ 7 * xg s₂ 17) := by
      rw [← hval_succ_last]; rfl
    have a₃ : xg s₃ 9 = xg s₂ 9 := by simp only [xg]; rw [k₃.1 _ (by simpa using (xAcc_ne 9).1)]
    have b₄ : xg s₄ 17 = xg s₂ 17 := by
      simp only [xg]
      rw [k₄.1 _ (by simpa using (xAcc_ne_of (show 9 < 17 by omega) (by omega)).symm),
        k₃.1 _ (by simpa using (xAcc_ne 17).1)]
    have a₅ : xg s₅ 9 = xg s₄ 9 := by
      simp only [xg]; rw [k₅.1 _ (by simpa using (xAcc_ne_of (show 9 < 17 by omega) (by omega)))]
    change xg s₅ 17 = xg s₄ 17 % 512 at e₅
    change xg s₄ 9 + 2 ^ 64 * c₄.toNat = xg s₃ 9 + (s₃.gpr .rax).toNat at e₄
    change (s₃.gpr .rax).toNat = xg s₂ 17 / 512 at e₃
    change xg s₂ 9 % 2 = 0 at ev₂
    rw [e₃, a₃] at e₄
    rw [h₂] at e₂
    rw [h₅, hL, a₅, e₅, b₄]
    exact dbl_arith hm hAA e₂ ev₂ (hval_lt fun c _ _ => (s₂.gpr _).isLt) (s₂.gpr _).isLt
      (s₂.gpr _).isLt (Bool.toNat_le _) e₄
end VG.Proof.Mont.X86_64
