import VerifiedGarbage.Proof.Mont.AArch64.Csub

/-!
# Montgomery arithmetic on AArch64: loads, stores and carry chains

Numbers loaded into and stored from registers (`loads_ok`, `stores_ok`), and
the chains of additions and subtractions of a number in the working space
(`chainAdds_ok`, `chainSubs_ok`), word by word through `x2`, with the carry
flag between words (for subtraction, the complement of the borrow).
`addMasked_ok` adds the modulus under a mask.
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

theorem loads_eq : ∀ (ts : List Reg) (a : Nat), loads ts a = loadsR .x0 ts a
  | [], _ => rfl
  | t :: ts, a => by rw [loads, loadsR, loads_eq ts (a + 8)]; rfl

theorem stores_eq : ∀ (ts : List Reg) (o : Nat), stores ts o = storesR .x0 ts o
  | [], _ => rfl
  | t :: ts, o => by rw [stores, storesR, stores_eq ts (o + 8)]; rfl

theorem loadsR_ok {size : Nat} {rn : Reg} : ∀ (ts : List Reg) {s : State} {base : Addr} {a : Nat},
    Ptr s rn base size → a + 8 * ts.length ≤ size → a % 8 = 0 → ts.Nodup → rn ∉ ts →
    WP isa (.block (loadsR rn ts a)) s fun s' =>
      regsVal s' ts = wordsVal s.mem base a ts.length ∧ Keeps ts s s' ∧ s'.c = s.c
  | [], s, _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
  | t :: ts, s, base, a, hs, ha, ha8, hf, hr => by
    simp only [List.length_cons] at ha
    simp only [List.mem_cons, not_or] at hr
    rw [loadsR, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ldR_ok hs (d := a) (by omega) ha8 t) fun s₁ ⟨e₁, k₁, c₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by simpa using hr.1)
    refine WP.mono (loadsR_ok ts hs₁ (a := a + 8) (by omega) (by omega) (List.nodup_cons.mp hf).2 hr.2)
      fun s₂ ⟨e₂, k₂, c₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.gpr t (List.nodup_cons.mp hf).1
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs)), c₂.trans c₁⟩
    rw [List.length_cons, regsVal, wordsVal, ht, e₁, e₂, k₁.mem]

theorem loads_ok {size : Nat} (ts : List Reg) {s : State} {base : Addr} {a : Nat}
    (hs : Scr s base size) (ha : a + 8 * ts.length ≤ size) (ha8 : a % 8 = 0) (hf : Fresh ts) :
    WP isa (.block (loads ts a)) s fun s' =>
      regsVal s' ts = wordsVal s.mem base a ts.length ∧ Keeps ts s s' ∧ s'.c = s.c :=
  loads_eq ts a ▸ loadsR_ok ts hs.ptr ha ha8 hf.1 fun h => (hf.2 _ h) (by simp)

theorem storesR_ok {size : Nat} {rn : Reg} : ∀ (ts : List Reg) {s : State} {base : Addr} {o : Nat},
    PtrW s rn base size → o + 8 * ts.length ≤ size → o % 8 = 0 → ts.Nodup →
    WP isa (.block (storesR rn ts o)) s fun s' =>
      wordsVal s'.mem base o ts.length = regsVal s ts ∧ KeepRegs [] s s' ∧
      Outside base o (8 * ts.length) s.mem s'.mem
  | [], s, _, _, _, _, _, _ => WP.block_nil ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | t :: ts, s, base, o, hs, ho, ho8, hd => by
    have hn := hs.nowrap
    simp only [List.length_cons] at ho
    rw [storesR, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (stR_ok hs (d := o) (by omega) ho8 t) fun s₁ e₁ => ?_
    have hs₁ : PtrW s₁ rn base size := by subst e₁; exact ⟨hs.reg, hs.st, hs.enc, hs.nowrap⟩
    have O₁ : Outside base o 8 s.mem s₁.mem := by rw [e₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (storesR_ok ts hs₁ (o := o + 8) (by omega) (by omega) (List.nodup_cons.mp hd).2)
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    have k₁ : KeepRegs [] s s₁ := by subst e₁; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    refine ⟨?_, k₁.trans k₂, fun x hx => ?_⟩
    · rw [List.length_cons, wordsVal, O₂.word (by omega) (by omega), e₁, word_writeW_self, e₂,
        regsVal, regsVal_congr (s := s) (s' := s₁) fun q _ => by rw [e₁]]
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega), O₁ x (by omega)]

theorem stores_ok {size : Nat} (ts : List Reg) {s : State} {base : Addr} {o : Nat}
    (hs : Scr s base size) (ho : o + 8 * ts.length ≤ size) (ho8 : o % 8 = 0) (hd : ts.Nodup) :
    WP isa (.block (stores ts o)) s fun s' =>
      wordsVal s'.mem base o ts.length = regsVal s ts ∧ KeepRegs [] s s' ∧
      Outside base o (8 * ts.length) s.mem s'.mem :=
  stores_eq ts o ▸ storesR_ok ts hs.ptrW ho ho8 hd

/-- `d = n + m + c` (`adds` with `c` false, or `adcs` with the carry flag),
and its carry out. -/
theorem addc_ok (s : State) (d n m : Reg) (first : Bool) {c : Bool}
    (hc : (if first then false else s.c) = c) :
    WP isa (.block [if first then .adds .x d n m else .adcs .x d n m]) s fun s' =>
      s'.gpr d = Word64.addCarry (s.gpr n) (s.gpr m) c ∧
      s'.c = Word64.carryOut (s.gpr n) (s.gpr m) c ∧ Keeps [d] s s' := by
  subst hc
  apply WP.of_runBlock
  cases first <;>
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Bool.false_eq_true,
      ite_true, ite_false, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

/-- `t += [b] + c`: one word of a chain. -/
theorem addStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t : Reg)
    (ht2 : t ≠ .x2) (first : Bool) {c : Bool} (hc : (if first then false else s.c) = c) {b : Nat}
    (hb : b + 8 ≤ size) (hb8 : b % 8 = 0) :
    WP isa (.block [ld .x2 b, if first then .adds .x t t .x2 else .adcs .x t t .x2]) s fun s' =>
      (s'.gpr t).toNat + 2 ^ 64 * s'.c.toNat = (s.gpr t).toNat + (word s.mem base b).toNat + c.toNat ∧
      Keeps [.x2, t] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hb hb8 .x2) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  refine WP.mono (addc_ok s₁ t t .x2 first (c := c) (by rw [c₁, hc])) fun s₂ ⟨d₂, c₂, k₂⟩ => ?_
  rw [l₁, k₁.gpr t (by simpa using ht2)] at d₂ c₂
  refine ⟨by rw [d₂, c₂]; exact Word64.addCarry_value _ _ c, (k₁.mono (by sub_regs)).trans
    (k₂.mono (by sub_regs))⟩

/-- `ts += [b] + c`, `adcs` throughout, with the carry `c` in and out. -/
theorem chainAdcs_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat},
    Scr s base size → b + 8 * ts.length ≤ size → b % 8 = 0 → Fresh ts →
    WP isa (.block (chain (.adcs .x) (.adcs .x) ts b)) s fun s' =>
      regsVal s' ts + 2 ^ (64 * ts.length) * s'.c.toNat =
        regsVal s ts + wordsVal s.mem base b ts.length + s.c.toNat ∧ Keeps (.x2 :: ts) s s'
  | [], s, _, _, _, _, _, _ => WP.block_nil ⟨by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, hs, hb, hb8, hf => by
    simp only [List.length_cons] at hb
    have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
    rw [chain, WP.block_append_iff]
    refine WP.mono (addStep_ok hs t ht2 false (c := s.c) rfl (b := b) (by omega) hb8)
      fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => by rcases h with h | h <;> [exact absurd h (by decide); exact hf.head.2 (by simp [← h])])
    refine WP.mono (chainAdcs_ok ts hs₁ (b := b + 8) (by omega) (by omega) hf.tail)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.gpr t (by
      simp only [List.mem_cons, not_or]; exact ⟨ht2, hf.head.1⟩)
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, fun h => hf.head.1 (h ▸ hq)⟩)
    rw [hR, k₁.mem] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega

/-- `ts += [b]`, with the carry out. -/
theorem chainAdds_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hb8 : b % 8 = 0)
    (hf : Fresh (t :: ts)) :
    WP isa (.block (chain (.adds .x) (.adcs .x) (t :: ts) b)) s fun s' =>
      regsVal s' (t :: ts) + 2 ^ (64 * (t :: ts).length) * s'.c.toNat =
        regsVal s (t :: ts) + wordsVal s.mem base b (t :: ts).length ∧ Keeps (.x2 :: t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
  rw [chain, WP.block_append_iff]
  refine WP.mono (addStep_ok hs t ht2 true (c := false) rfl (b := b) (by omega) hb8)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => by rcases h with h | h <;> [exact absurd h (by decide); exact hf.head.2 (by simp [← h])])
  refine WP.mono (chainAdcs_ok ts hs₁ (b := b + 8) (by omega) (by omega) hf.tail)
    fun s₂ ⟨e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.gpr t (by
    simp only [List.mem_cons, not_or]; exact ⟨ht2, hf.head.1⟩)
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    have := hf.tail.2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨this.2.2.1, fun h => hf.head.1 (h ▸ hq)⟩)
  rw [hR, k₁.mem] at e₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  simp only [Bool.toNat_false, Nat.add_zero] at e₁
  rw [Nat.mul_assoc]
  omega

/-- `t -= [b] + !c`: one word of a chain (`c` the carry flag in, `subs` with
`c` true). -/
theorem subStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t : Reg)
    (ht2 : t ≠ .x2) (first : Bool) {c : Bool} (hc : (if first then true else s.c) = c) {b : Nat}
    (hb : b + 8 ≤ size) (hb8 : b % 8 = 0) :
    WP isa (.block [ld .x2 b, if first then .subs .x t t .x2 else .sbcs .x t t .x2]) s fun s' =>
      (s'.gpr t).toNat + (word s.mem base b).toNat + (!c).toNat =
        (s.gpr t).toNat + 2 ^ 64 * (!s'.c).toNat ∧ Keeps [.x2, t] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hb hb8 .x2) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  refine WP.mono (subc_ok s₁ t t .x2 first (c := c) (by rw [c₁, hc])) fun s₂ ⟨d₂, c₂, k₂⟩ => ?_
  rw [l₁, k₁.gpr t (by simpa using ht2)] at d₂ c₂
  refine ⟨by rw [d₂, c₂]; exact sub_borrow _ _ c, (k₁.mono (by sub_regs)).trans
    (k₂.mono (by sub_regs))⟩

/-- `ts -= [b] + !c`, `sbcs` throughout, with the borrow `!c` in and out. -/
theorem chainSbcs_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat},
    Scr s base size → b + 8 * ts.length ≤ size → b % 8 = 0 → Fresh ts →
    WP isa (.block (chain (.sbcs .x) (.sbcs .x) ts b)) s fun s' =>
      regsVal s' ts + wordsVal s.mem base b ts.length + (!s.c).toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * (!s'.c).toNat ∧ Keeps (.x2 :: ts) s s'
  | [], s, _, _, _, _, _, _ => WP.block_nil ⟨by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, hs, hb, hb8, hf => by
    simp only [List.length_cons] at hb
    have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
    rw [chain, WP.block_append_iff]
    refine WP.mono (subStep_ok hs t ht2 false (c := s.c) rfl (b := b) (by omega) hb8)
      fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => by rcases h with h | h <;> [exact absurd h (by decide); exact hf.head.2 (by simp [← h])])
    refine WP.mono (chainSbcs_ok ts hs₁ (b := b + 8) (by omega) (by omega) hf.tail)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.gpr t (by
      simp only [List.mem_cons, not_or]; exact ⟨ht2, hf.head.1⟩)
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, fun h => hf.head.1 (h ▸ hq)⟩)
    rw [hR, k₁.mem] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega

/-- `ts -= [b]`, with the borrow `!c` out. -/
theorem chainSubs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hb8 : b % 8 = 0)
    (hf : Fresh (t :: ts)) :
    WP isa (.block (chain (.subs .x) (.sbcs .x) (t :: ts) b)) s fun s' =>
      regsVal s' (t :: ts) + wordsVal s.mem base b (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * (!s'.c).toNat ∧
      Keeps (.x2 :: t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
  rw [chain, WP.block_append_iff]
  refine WP.mono (subStep_ok hs t ht2 true (c := true) rfl (b := b) (by omega) hb8)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => by rcases h with h | h <;> [exact absurd h (by decide); exact hf.head.2 (by simp [← h])])
  refine WP.mono (chainSbcs_ok ts hs₁ (b := b + 8) (by omega) (by omega) hf.tail)
    fun s₂ ⟨e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.gpr t (by
    simp only [List.mem_cons, not_or]; exact ⟨ht2, hf.head.1⟩)
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    have := hf.tail.2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨this.2.2.1, fun h => hf.head.1 (h ▸ hq)⟩)
  rw [hR, k₁.mem] at e₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₁
  rw [Nat.mul_assoc]
  omega

end VG.Proof.Mont.AArch64
