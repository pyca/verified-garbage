import VerifiedGarbage.Proof.Mont.AArch64.Rounds

/-!
# Montgomery arithmetic on AArch64: the conditional subtraction

`csubR M ts top` reduces `ts + 2^(64 n) top < 2m` modulo `m` (`csubR_ok`):
the difference with `m` goes to the registers `dRegs n` (`diffsR_ok`, a chain
of `subs` and `sbcs`, in which the carry flag is the complement of the
borrow), the borrow of the top word becomes a mask (`maskR_ok`), and the mask
selects each word (`selectsR_ok`).
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

/-- The registers for the difference. -/
abbrev dPool : List Reg := [.x1, .x3, .x4, .x5, .x6, .x16]

/-- Registers for the difference: distinct, from `dPool`. -/
def DRegs (ds : List Reg) : Prop := ds.Nodup ∧ ∀ d ∈ ds, d ∈ dPool

theorem dPool_ne : ∀ d ∈ dPool, d ≠ .x2 ∧ d ≠ .x17 ∧ d ≠ .x7 ∧ d ≠ .x0 := by decide

theorem dPool_sub : ∀ d ∈ dPool, d ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17] := by
  decide

/-- A register of the pool is not a fresh one. -/
theorem dPool_fresh {d t : Reg} (hd : d ∈ dPool)
    (ht : t ∉ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x16, .x17]) : d ≠ t := fun h =>
  ht (h ▸ dPool_sub d hd)

theorem dRegs_ok : ∀ n < 7, DRegs (dRegs n) ∧ (n ≤ 6 → (dRegs n).length = n) := by
  unfold DRegs dRegs; decide

theorem DRegs.tail {d : Reg} {ds : List Reg} (h : DRegs (d :: ds)) : DRegs ds :=
  ⟨(List.nodup_cons.mp h.1).2, fun q hq => h.2 q (List.mem_cons_of_mem _ hq)⟩

/-- One word of the difference: `d = t - [mo] - b` with the borrow `b = !c` in
(`c` the carry flag, true for `subs`), and its borrow out. -/
theorem diffR1_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (t d : Reg)
    (ht2 : t ≠ .x2) (first : Bool) {c : Bool} (hc : (if first then true else s.c) = c)
    {mo : Nat} (hmo : mo + 8 ≤ size) (hmo8 : mo % 8 = 0) :
    WP isa (.block [ld .x2 mo, if first then .subs .x d t .x2 else .sbcs .x d t .x2]) s
      fun s' => (s'.gpr d).toNat + (word s.mem base mo).toNat + (!c).toNat =
          (s.gpr t).toNat + 2 ^ 64 * (!s'.c).toNat ∧ Keeps [.x2, d] s s' := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs hmo hmo8 .x2) fun s₁ ⟨l₁, k₁, c₁⟩ => ?_
  refine WP.mono (subc_ok s₁ d t .x2 first (c := c) (by rw [c₁, hc])) fun s₂ ⟨d₂, c₂, k₂⟩ => ?_
  rw [l₁, k₁.gpr t (by simpa using ht2)] at d₂ c₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  rw [d₂, c₂]
  exact sub_borrow _ _ c

/-- The difference of the words `ts` and the words at `mo`, with the borrow
`!c` in (`c` the carry flag), into `ds`, and its borrow out. -/
theorem diffsRSbc_ok {size : Nat} : ∀ (ts ds : List Reg) {s : State} {base : Addr} {mo : Nat},
    Scr s base size → ts.length = ds.length → mo + 8 * ts.length ≤ size → mo % 8 = 0 → Fresh ts →
    DRegs ds →
    WP isa (.block (diffsR false ts ds mo)) s fun s' =>
      regsVal s' ds + wordsVal s.mem base mo ts.length + (!s.c).toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * (!s'.c).toNat ∧ Keeps (.x2 :: ds) s s'
  | [], [], s, _, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [wordsVal, regsVal],
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, _, _, hl, _, _, _, _ => absurd hl (by simp)
  | t :: ts, d :: ds, s, base, mo, hs, hl, hmo, hmo8, hf, hd => by
    simp only [List.length_cons] at hmo hl
    have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
    have hdP := hd.2 d (List.mem_cons_self ..)
    rw [diffsR, WP.block_append_iff]
    refine WP.mono (diffR1_ok hs t d ht2 false (c := s.c) rfl (mo := mo)
      (by omega) hmo8) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨by decide, Ne.symm (dPool_ne d hdP).2.2.2⟩)
    refine WP.mono (diffsRSbc_ok ts ds hs₁ (mo := mo + 8) (by omega) (by omega) (by omega) hf.tail
      hd.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have hq' := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hq' (by simp [h]), fun h => dPool_fresh hdP hq' h.symm⟩)
    have hd₂ : s₂.gpr d = s₁.gpr d := k₂.gpr d (by
      simp only [List.mem_cons, not_or]
      exact ⟨(dPool_ne d hdP).1, (List.nodup_cons.mp hd.1).1⟩)
    rw [hR, k₁.mem] at e₂
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [wordsVal, regsVal, List.length_cons, pow64_succ, hd₂]
    rw [Nat.mul_assoc]
    omega

/-- The difference of the words `t :: ts` and the words at `mo` into `ds`, and
its borrow `!c` (`c` the carry flag after it). -/
theorem diffsR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {t : Reg}
    {ts ds : List Reg} {mo : Nat} (hl : (t :: ts).length = ds.length)
    (hmo : mo + 8 * (t :: ts).length ≤ size) (hmo8 : mo % 8 = 0) (hf : Fresh (t :: ts))
    (hd : DRegs ds) :
    WP isa (.block (diffsR true (t :: ts) ds mo)) s fun s' =>
      regsVal s' ds + wordsVal s.mem base mo (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * (!s'.c).toNat ∧ Keeps (.x2 :: ds) s s' := by
  obtain ⟨d, ds', rfl⟩ : ∃ d ds', ds = d :: ds' := by
    cases ds with
    | nil => simp at hl
    | cons d ds' => exact ⟨d, ds', rfl⟩
  simp only [List.length_cons] at hmo hl ⊢
  have ht2 : t ≠ .x2 := fun h => hf.head.2 (by simp [h])
  have hdP := hd.2 d (List.mem_cons_self ..)
  rw [diffsR, WP.block_append_iff]
  refine WP.mono (diffR1_ok hs t d ht2 true (c := true) rfl (mo := mo)
    (by omega) hmo8) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, Ne.symm (dPool_ne d hdP).2.2.2⟩)
  refine WP.mono (diffsRSbc_ok ts ds' hs₁ (mo := mo + 8) (by omega) (by omega) (by omega) hf.tail
    hd.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
    have hq' := hf.tail.2 q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨fun h => hq' (by simp [h]), fun h => dPool_fresh hdP hq' h.symm⟩)
  have hd₂ : s₂.gpr d = s₁.gpr d := k₂.gpr d (by
    simp only [List.mem_cons, not_or]
    exact ⟨(dPool_ne d hdP).1, (List.nodup_cons.mp hd.1).1⟩)
  rw [hR, k₁.mem] at e₂
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [wordsVal, regsVal, pow64_succ, hd₂]
  simp only [Bool.not_true, Bool.toNat_false, Nat.add_zero] at e₁
  rw [Nat.mul_assoc]
  omega

/-! ## The mask and the selection -/

/-- The top word less the borrow `!c`, and its borrow as a mask in `x17`: all
ones if it borrows. -/
theorem maskR_ok (s : State) (top : Reg) (hz : s.gpr .x7 = 0) :
    WP isa (.block [.sbcs .x .x2 top .x7, .sbc .x .x17 .x7 .x7]) s fun s' =>
      s'.gpr .x17 = (if (s.gpr top).toNat < (!s.c).toNat then BitVec.allOnes 64 else 0) ∧
      Keeps [.x2, .x17] s s' := by
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
the word of `ds` if it is zero. -/
theorem selectsR_ok : ∀ (ts ds : List Reg) {s : State} (k : Bool), ts.length = ds.length → Fresh ts →
    DRegs ds → s.gpr .x17 = (if k then BitVec.allOnes 64 else 0) →
    WP isa (.block (selectsR ts ds)) s fun s' =>
      regsVal s' ts = (if k then regsVal s ts else regsVal s ds) ∧ Keeps (.x2 :: ts) s s'
  | [], [], s, k, _, _, _, _ => WP.block_nil ⟨by cases k <;> rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | [], _ :: _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, hl, _, _, _ => absurd hl (by simp)
  | t :: ts, d :: ds, s, k, hl, hf, hd, hk => by
    obtain ⟨htn, hto⟩ := hf.head
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hto
    have hdP := hd.2 d (List.mem_cons_self ..)
    have hdt : d ≠ t := dPool_fresh hdP (by simp [hto.1, hto.2.1, hto.2.2.1, hto.2.2.2.1,
      hto.2.2.2.2.1, hto.2.2.2.2.2.1, hto.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.1,
      hto.2.2.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.2.2])
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [selectsR, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.logic .eor .x .x2 t d, .logic .and .x .x2 .x2 .x17,
        .logic .eor .x t d .x2]) s (fun s₁ =>
        s₁.gpr t = (if k then s.gpr t else s.gpr d) ∧ Keeps [.x2, t] s s₁) by
      apply WP.of_runBlock
      have ht2' : t ≠ .x2 := hto.2.2.1
      have hdx2 : d ≠ .x2 := (dPool_ne d hdP).1
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
        BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left',
        hk, ht2', hdx2]
      refine ⟨select_val _ _ k, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hk₁ : s₁.gpr .x17 = (if k then BitVec.allOnes 64 else 0) := by
      rw [k₁.gpr _ (by simp [Ne.symm hto.2.2.2.2.2.2.2.2.2]), hk]
    refine WP.mono (selectsR_ok ts ds k hl hf.tail hd.tail hk₁) fun s₂ ⟨e₂, k₂⟩ => ?_
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.gpr q (by
      have := hf.tail.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, fun h => htn (h ▸ hq)⟩)
    have hD : regsVal s₁ ds = regsVal s ds := regsVal_congr fun q hq => k₁.gpr q (by
      have hqP := hd.2 q (List.mem_cons_of_mem _ hq)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨(dPool_ne q hqP).1, dPool_fresh hqP (by simp [hto.1, hto.2.1, hto.2.2.1, hto.2.2.2.1,
        hto.2.2.2.2.1, hto.2.2.2.2.2.1, hto.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.1,
        hto.2.2.2.2.2.2.2.2.1, hto.2.2.2.2.2.2.2.2.2])⟩)
    have ht₂ : s₂.gpr t = s₁.gpr t := k₂.gpr t (by simp [htn, hto.2.2.1])
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [regsVal, regsVal, regsVal, ht₂, e₁, e₂, hR, hD]
    cases k <;> rfl

/-! ## The conditional subtraction -/

/-- `csubR`: `ts + 2^(64 n) top < 2m` reduced modulo `m`, with `x7 = 0`. -/
theorem csubR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {ts : List Reg} {top : Reg} (hlen : ts.length = M.n) (hn : 0 < M.n) (h7 : M.n < 7)
    (hf : Fresh (top :: ts)) (hmo : M.mo + 8 * M.n ≤ size) (hmo8 : M.mo % 8 = 0)
    (hz : s.gpr .x7 = 0) {m : Nat} (hm : wordsVal s.mem base M.mo M.n = m)
    (hV : regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat < 2 * m) :
    WP isa (.block (csubR M ts top)) s fun s' =>
      regsVal s' ts = (regsVal s ts + 2 ^ (64 * M.n) * (s.gpr top).toNat) % m ∧
      Keeps (.x2 :: .x17 :: ts ++ dRegs M.n) s s' := by
  obtain ⟨t, ts', rfl⟩ : ∃ t ts', ts = t :: ts' := by
    cases ts with
    | nil => simp at hlen; omega
    | cons t ts' => exact ⟨t, ts', rfl⟩
  have hft := hf.tail
  have htop := hf.head
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at htop
  obtain ⟨hD, hDl⟩ := dRegs_ok M.n h7
  have hDl' := hDl (by omega)
  have hmX : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  rw [csubR, List.append_assoc, WP.block_append_iff]
  refine WP.mono (diffsR_ok hs (mo := M.mo) (ds := dRegs M.n) (by rw [hlen, hDl']) (by rw [hlen]; omega)
    hmo8 hft hD) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact absurd h (by decide)
    · exact (dPool_ne _ (hD.2 _ h)).2.2.2 rfl)
  have hz₁ : s₁.gpr .x7 = 0 := by
    rw [k₁.gpr _ (by
      intro h
      rcases List.mem_cons.mp h with h | h
      · exact absurd h (by decide)
      · exact (dPool_ne _ (hD.2 _ h)).2.2.1 rfl), hz]
  rw [WP.block_append_iff]
  refine WP.mono (maskR_ok s₁ top hz₁) fun s₂ ⟨x₂, k₂⟩ => ?_
  have htopP : ∀ d ∈ dRegs M.n, d ≠ top := fun d hd => dPool_fresh (hD.2 d hd) (by
    simp [htop.2.1, htop.2.2.1, htop.2.2.2.1, htop.2.2.2.2.1, htop.2.2.2.2.2.1, htop.2.2.2.2.2.2.1,
      htop.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.1, htop.2.2.2.2.2.2.2.2.2.2])
  have htop₁ : s₁.gpr top = s.gpr top := k₁.gpr top (by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact htop.2.2.2.1 h
    · exact htopP _ h rfl)
  rw [htop₁] at x₂
  have hDs : ∀ q ∈ dRegs M.n, q ∉ [Reg.x2, .x17] := fun q hq hq' => by
    have := dPool_ne q (hD.2 q hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with h | h
    · exact this.1 h
    · exact this.2.1 h
  refine WP.mono (selectsR_ok _ (dRegs M.n) (decide ((s.gpr top).toNat < (!s₁.c).toNat))
    (s := s₂) (by rw [hlen, hDl']) hft hD (by rw [x₂]; simp only [decide_eq_true_eq]))
    fun s₃ ⟨e₃, k₃⟩ => ?_
  have hR₂ : regsVal s₂ (t :: ts') = regsVal s (t :: ts') := by
    rw [regsVal_congr fun q hq => k₂.gpr q (by
      have := hft.2 q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.2.2.1, this.2.2.2.2.2.2.2.2.2⟩)]
    exact regsVal_congr fun q hq => k₁.gpr q (by
      have hq' := hft.2 q hq
      intro h
      rcases List.mem_cons.mp h with h | h
      · exact hq' (by simp [h])
      · exact dPool_fresh (hD.2 _ h) hq' rfl)
  have hD₂ : regsVal s₂ (dRegs M.n) = regsVal s₁ (dRegs M.n) :=
    regsVal_congr fun q hq => k₂.gpr q (hDs q hq)
  rw [hlen] at e₁
  rw [hm] at e₁
  refine ⟨?_, ((k₁.mono (by
      intro r hr; rcases List.mem_cons.mp hr with h | h
      · subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ h)))).trans
      ((k₂.mono (by sub_regs)).trans (k₃.mono (by
      intro r hr; rcases List.mem_cons.mp hr with h | h
      · subst h; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ h))))))⟩
  rw [e₃, hR₂, hD₂]
  simp only [decide_eq_true_eq]
  have hDlt := regsVal_lt s₁ (dRegs M.n)
  rw [hDl'] at hDlt
  exact csub_arith (b := !s₁.c) hmX hDlt hV e₁

end VG.Proof.Mont.AArch64
