import VerifiedGarbage.Proof.Mont.AArch64.Rounds

/-!
# Montgomery arithmetic on AArch64: the conditional subtraction

`csub M ts top` reduces `ts + 2^(64 n) top < 2m` modulo `m` (`csub_ok`): the
difference with `m` goes to the temporary area (`diffs_ok`, a chain of
`subs` and `sbcs`, in which the carry flag is the complement of the borrow),
the borrow of the top word becomes a mask (`mask_ok`), and the mask selects
each word (`selects_ok`).
-/

namespace VG.Proof.Mont.AArch64

open VG VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.subCarry_value Word64.borrow_mask)

/-! ## The differences -/

/-- `d = n + ~m + c` (`subs` with `c` true, or `sbcs` with the carry flag),
and its carry out, the complement of the borrow. -/
theorem subc_ok (s : State) (d n m : Reg) (first : Bool) {c : Bool}
    (hc : (if first then true else s.c) = c) :
    WP isa (.block [if first then .subs .x d n m else .sbcs .x d n m]) s fun s' =>
      s'.gpr d = Word64.addCarry (s.gpr n) (~~~(s.gpr m)) c ∧
      s'.c = Word64.carryOut (s.gpr n) (~~~(s.gpr m)) c ∧ Keeps [d] s s' := by
  subst hc
  apply WP.of_runBlock
  cases first <;>
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Bool.false_eq_true,
      ite_true, ite_false, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_addWithCarry, hr, ite_false]

/-- `t - b` as `n + ~m + c`, with the borrow `b = !c` in and out. -/
theorem sub_borrow (a b : BitVec 64) (c : Bool) :
    (Word64.addCarry a (~~~b) c).toNat + b.toNat + (!c).toNat =
      a.toNat + 2 ^ 64 * (!Word64.carryOut a (~~~b) c).toNat := by
  have := Word64.subCarry_value a b c
  generalize Word64.carryOut a (~~~b) c = co at this ⊢
  cases c <;> cases co <;> simp only [Bool.not_true, Bool.not_false, Bool.toNat_true,
    Bool.toNat_false] at this ⊢ <;> omega

/-- One word of the difference: `[tmp] = t - [mo] - b` with the borrow
`b = !c` in (`c` the carry flag, true for `subs`), and its borrow out. -/
theorem diff1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t : Reg)
    (ht2 : t ≠ .x2) (first : Bool) {c : Bool} (hc : (if first then true else s.c) = c) {mo tmp : Nat}
    (hmo : mo + 8 ≤ size) (htmp : tmp + 8 ≤ size) (hmo8 : mo % 8 = 0) (htmp8 : tmp % 8 = 0) :
    WP isa (.block [ld .x2 mo, if first then .subs .x .x16 t .x2 else .sbcs .x .x16 t .x2,
        st .x16 tmp]) s
      fun s' => (word s'.mem base tmp).toNat + (word s.mem base mo).toNat + (!c).toNat =
          (s.gpr t).toNat + 2 ^ 64 * (!s'.c).toNat ∧
        s'.c = Word64.carryOut (s.gpr t) (~~~(word s.mem base mo)) c ∧
        KeepRegs [.x2, .x16] s s' ∧ s'.mem = s.mem.writeW (off base tmp) (word s'.mem base tmp) := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hmo hmo8 .x2) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (subc_ok s₁ .x16 t .x2 first (c := c) (by rw [c₁, hc])) fun s₂ ⟨d₂, c₂, k₂⟩ => ?_
  rw [l₁, k₁.gpr t (by simpa using ht2)] at d₂ c₂
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  refine WP.mono (st_ok hs₂ htmp htmp8 .x16) fun s₃ e₃ => ?_
  subst e₃
  refine ⟨?_, c₂, ⟨fun r hr => ?_, by rw [k₂.rd, k₁.rd], by rw [k₂.wr, k₁.wr],
    by rw [k₂.sp, k₁.sp]⟩, ?_⟩
  · simp only [word_writeW_self, k₂.mem, k₁.mem]
    rw [d₂, c₂]
    exact sub_borrow _ _ c
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    show s₂.gpr r = s.gpr r
    rw [k₂.gpr r (by simpa using hr.2), k₁.gpr r (by simpa using hr.1)]
  · simp only [word_writeW_self, k₂.mem, k₁.mem]

/-- The difference of the words `ts` and the words at `mo`, with the borrow
`!c` in (`c` the carry flag), into the words at `tmp`, and its borrow out. -/
theorem diffsSbc_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr}
    {mo tmp : Nat}, Scr s base size → mo + 8 * ts.length ≤ size →
    tmp + 8 * ts.length ≤ size → (mo + 8 * ts.length ≤ tmp ∨ tmp + 8 * ts.length ≤ mo) →
    mo % 8 = 0 → tmp % 8 = 0 → Fresh ts →
    WP isa (.block (diffs false ts mo tmp)) s fun s' =>
      wordsVal s'.mem base tmp ts.length + wordsVal s.mem base mo ts.length + (!s.c).toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * (!s'.c).toNat ∧
      KeepRegs [.x2, .x16] s s' ∧ Outside base tmp (8 * ts.length) s.mem s'.mem
  | [], s, _, _, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [wordsVal, regsVal],
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | t :: ts, s, base, mo, tmp, hs, hmo, htmp, hsep, hmo8, htmp8, hf => by
    have hn := hs.nowrap
    simp only [List.length_cons] at hmo htmp hsep
    have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
    rw [diffs, WP.block_append_iff]
    refine WP.mono (diff1_ok hs t ht2 false (c := s.c) rfl (mo := mo) (tmp := tmp) (by omega)
      (by omega) hmo8 htmp8) fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base tmp 8 s.mem s₁.mem := by
      rw [m₁]; exact writeW_outside _ _ _ (by omega)
    refine WP.mono (diffsSbc_ok ts hs₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
      (by omega) (by omega) (by omega) hf.tail) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, this.2.2.2.2.2.2.2.2.1⟩)
    have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
      O₁.wordsVal (by omega) (by omega)
    have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
    rw [hR, hM] at e₂
    refine ⟨?_, k₁.trans k₂, fun x hx => ?_⟩
    · simp only [wordsVal, regsVal, List.length_cons, pow64_succ, hT]
      rw [Nat.mul_assoc]
      omega
    · simp only [List.length_cons] at hx
      rw [O₂ x (by omega), O₁ x (by omega)]

/-- The difference of the words `t :: ts` and the words at `mo` into the words
at `tmp`, and its borrow `!c` (`c` the carry flag after it). -/
theorem diffs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts : List Reg} {mo tmp : Nat} (hmo : mo + 8 * (t :: ts).length ≤ size)
    (htmp : tmp + 8 * (t :: ts).length ≤ size)
    (hsep : mo + 8 * (t :: ts).length ≤ tmp ∨ tmp + 8 * (t :: ts).length ≤ mo)
    (hmo8 : mo % 8 = 0) (htmp8 : tmp % 8 = 0) (hf : Fresh (t :: ts)) :
    WP isa (.block (diffs true (t :: ts) mo tmp)) s fun s' =>
      wordsVal s'.mem base tmp (t :: ts).length + wordsVal s.mem base mo (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * (!s'.c).toNat ∧
      KeepRegs [.x2, .x16] s s' ∧ Outside base tmp (8 * (t :: ts).length) s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.length_cons] at hmo htmp hsep ⊢
  have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
  rw [diffs, WP.block_append_iff]
  refine WP.mono (diff1_ok hs t ht2 true (c := true) rfl (mo := mo) (tmp := tmp) (by omega)
    (by omega) hmo8 htmp8) fun s₁ ⟨e₁, c₁, k₁, m₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have O₁ : Outside base tmp 8 s.mem s₁.mem := by
    rw [m₁]; exact writeW_outside _ _ _ (by omega)
  refine WP.mono (diffsSbc_ok ts hs₁ (mo := mo + 8) (tmp := tmp + 8) (by omega) (by omega)
    (by omega) (by omega) (by omega) hf.tail) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    have := hf.tail.2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
    exact ⟨this.2.2.1, this.2.2.2.2.2.2.2.2.1⟩)
  have hM : wordsVal s₁.mem base (mo + 8) ts.length = wordsVal s.mem base (mo + 8) ts.length :=
    O₁.wordsVal (by omega) (by omega)
  have hT : word s₂.mem base tmp = word s₁.mem base tmp := O₂.word (by omega) (by omega)
  rw [hR, hM] at e₂
  refine ⟨?_, k₁.trans k₂, fun x hx => ?_⟩
  · simp only [wordsVal, regsVal, pow64_succ, hT]
    simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₁
    rw [Nat.mul_assoc]
    omega
  · rw [O₂ x (by omega), O₁ x (by omega)]

/-! ## The mask and the selection -/

/-- The top word less the borrow `!c`, and its borrow as a mask in `x17`: all
ones if it borrows. -/
theorem mask_ok (s : State) (top : Reg) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.sbcs .x .x16 top .x7, .sbc .x .x17 .x7 .x7]) s fun s' =>
      s'.gpr .x17 = (if (s.gpr top).toNat < (!s.c).toNat then BitVec.allOnes 64 else 0) ∧
      Keeps [.x16, .x17] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq, ite_true, ite_false,
    reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · dsimp only [Size.bits]
    have h0 : (~~~(0 : BitVec 64)).toNat = 2 ^ 64 - 1 := rfl
    have := (s.gpr top).isLt
    rw [h0]
    have key : decide (2 ^ 64 ≤ (s.gpr top).toNat + (2 ^ 64 - 1) + s.c.toNat) =
        !decide ((s.gpr top).toNat < (!s.c).toNat) := by
      cases s.c
      · simp only [Bool.toNat_false, Bool.not_false, Bool.toNat_true, Nat.add_zero]
        by_cases h : (s.gpr top).toNat < 1
        · rw [decide_eq_false (by omega), decide_eq_true h]; rfl
        · rw [decide_eq_true (by omega), decide_eq_false h]; rfl
      · simp only [Bool.toNat_true, Bool.not_true, Bool.toNat_false]
        rw [decide_eq_true (by omega), decide_eq_false (by omega)]; rfl
    rw [key]
    by_cases h : (s.gpr top).toNat < (!s.c).toNat <;> simp only [h, decide_true, decide_false,
      Bool.not_true, Bool.not_false, ite_true, ite_false] <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2, ite_false]

theorem select_val (t d : BitVec 64) (k : Bool) :
    d ^^^ ((t ^^^ d) &&& (if k then BitVec.allOnes 64 else 0)) = if k then t else d := by
  cases k
  · simp
  · simp only [ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm t d, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- Each word of `ts` kept if the mask `x17` is all ones (`k`), and replaced by
the word at `tmp` if it is zero. -/
theorem selects_ok {size : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {tmp : Nat} (k : Bool),
    Scr s base size → tmp + 8 * ts.length ≤ size → tmp % 8 = 0 → Fresh ts →
    s.gpr .x17 = (if k then BitVec.allOnes 64 else 0) →
    WP isa (.block (selects ts tmp)) s fun s' =>
      regsVal s' ts = (if k then regsVal s ts else wordsVal s.mem base tmp ts.length) ∧
      Keeps (.x2 :: .x16 :: ts) s s'
  | [], s, _, _, k, _, _, _, _, _ => WP.block_nil ⟨by cases k <;> rfl, fun _ _ => rfl, rfl, rfl, rfl,
      rfl⟩
  | t :: ts, s, base, tmp, k, hs, htmp, htmp8, hf, hk => by
    obtain ⟨htn, hto⟩ := hf.head
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hto
    simp only [List.length_cons] at htmp
    rw [selects, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs (d := tmp) (by omega) htmp8 .x16) fun s₀ ⟨l₀, k₀, _⟩ => ?_
    refine WP.mono (show WP isa (.block [.logic .eor .x .x2 t .x16, .logic .and .x .x2 .x2 .x17,
        .logic .eor .x t .x16 .x2]) s₀ (fun s₁ =>
        s₁.gpr t = (if k then s.gpr t else word s.mem base tmp) ∧ Keeps [.x2, t] s₀ s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
        BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
      rw [l₀, k₀.gpr t (by simpa using Ne.symm hto.2.2.2.2.2.2.2.2.1 |>.symm),
        k₀.gpr .x17 (by decide), hk]
      refine ⟨select_val _ _ k, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have k₀₁ := (k₀.mono (show ∀ r ∈ [Reg.x16], r ∈ [Reg.x2, .x16, t] by sub_regs)).trans
      (k₁.mono (show ∀ r ∈ [Reg.x2, t], r ∈ [Reg.x2, .x16, t] by sub_regs))
    have hs₁ := hs.of_keeps k₀₁ (by simp [Ne.symm hto.1])
    have hk₁ : s₁.gpr .x17 = (if k then BitVec.allOnes 64 else 0) := by
      rw [k₀₁.gpr _ (by simp [Ne.symm hto.2.2.2.2.2.2.2.2.2]), hk]
    refine WP.mono (selects_ok ts k hs₁ (tmp := tmp + 8) (by omega) (by omega) hf.tail hk₁)
      fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₀₁.gpr q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, this.2.2.2.2.2.2.2.2.1, fun h => htn (h ▸ hq)⟩)
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t (by simp [htn, hto.2.2.1, hto.2.2.2.2.2.2.2.2.1])
    refine ⟨?_, (k₀₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [regsVal, ht₂, e₁, e₂, hR, k₀₁.mem]
    cases k <;> rfl

/-! ## The conditional subtraction -/

/-- `csub`: `ts + 2^(64 n) top < 2m` reduced modulo `m`, with `x7 = 0`. -/
theorem csub_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (hf : Fresh (top :: ts))
    (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (hsep : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo) (hmo8 : M.mo % 8 = 0)
    (htmp8 : M.tmp % 8 = 0) (hz : s.gpr .x7 = 0) {m : Nat}
    (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csub M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      KeepRegs (.x2 :: .x16 :: .x17 :: ts) s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htop
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [csub, List.append_assoc, WP.block_append_iff]
  refine WP.mono (diffs_ok hs (mo := M.mo) (tmp := M.tmp) (by rw [hlen]; omega) (by rw [hlen]; omega)
    (by rw [hlen]; omega) hmo8 htmp8 hft) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hz₁ : s₁.gpr .x7 = 0 := by rw [k₁.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (mask_ok s₁ top hz₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top (by simp [htop.2.2.2.1,
    htop.2.2.2.2.2.2.2.2.2.1])
  rw [htop₁] at x₂
  refine WP.mono (selects_ok _ (decide ((s.gpr top).toNat < (!s₁.c).toNat)) hs₂ (tmp := M.tmp)
    (by rw [hlen]; omega) htmp8 hft (by rw [x₂]; simp only [decide_eq_true_eq]))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have hR₂ : regsVal s₂ (t :: ts') = regsVal s (t :: ts') := by
    rw [regsVal_congr fun q hq => k₂.gpr q (by
      have := hft.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2⟩)]
    exact regsVal_congr fun q hq => k₁.gpr q (by
      have := hft.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, this.2.2.2.2.2.2.2.2.1⟩)
  rw [hlen] at e₁ e₃
  rw [hm] at e₁
  rw [k₂.mem] at e₃
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (((Keeps.regs k₂).mono (by sub_regs)).trans
    ((Keeps.regs k₃).mono (by sub_regs))), fun x hx => ?_⟩
  · rw [e₃, hR₂]
    simp only [decide_eq_true_eq]
    exact csub_arith (b := !s₁.c) hmX (wordsVal_lt _ _ _ _) hV e₁
  · rw [k₃.mem, k₂.mem, O₁ x (by rw [hlen]; exact hx)]

end VG.Proof.Mont.AArch64
