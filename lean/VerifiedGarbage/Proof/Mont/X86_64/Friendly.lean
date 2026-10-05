import VerifiedGarbage.Proof.Mont.X86_64.Round

/-!
# Montgomery arithmetic on x86-64: the reduction for a friendly modulus

For `m ≡ -1 (mod 2⁶⁴)` (`Red.friendly ws`, `ws` the words of
`m' = (m + 1) / 2⁶⁴`), the reduction of a round adds `t₀ m'` to the words of
the window above `t₀` and clears `t₀`: `2⁶⁴ T' = T + t₀ m` (`redF_ok`), the
reduction by `u = t₀`. A word of `m'` is multiplied by `t₀` into `rdx:rax`
and added at its place, its carry up the window (`addProd_ok`, `adcZeros_ok`);
words of zero are skipped (`redWords_ok`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry toNat_ofBool)

theorem mov32zero_ok (s : State) (t : Reg) :
    WP isa (.block [.mov32 t (.imm 0)]) s fun s' => s'.gpr t = 0 ∧ s'.cf = s.cf ∧ Keeps [t] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left',
    RegUpd.cf_setReg]
  refine ⟨rfl, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- `adc r, 0`. -/
theorem adc0_ok (s : State) (r : Reg) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .adc r (.imm 0)]) s fun s' => ∃ c', s'.cf = some c' ∧
      (s'.gpr r).toNat + 2 ^ 64 * c'.toNat = (s.gpr r).toNat + c.toNat ∧ Keeps [r] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hc, RegUpd.gpr_setReg, RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun q hq => ?_, rfl, rfl, rfl⟩
  · have hz : (0 : BitVec 64).toNat = 0 := rfl
    have := adc_carry (s.gpr r) 0 c
    rw [hz, Nat.add_zero] at this ⊢
    exact this
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hq, ite_false]

/-- The carry `c` up the words `rest`, if it does not overflow them. -/
theorem adcZeros_ok : ∀ (rest : List Reg) {s : State} {c : Bool}, s.cf = some c → rest.Nodup →
    regsVal s rest + c.toNat < 2 ^ (64 * rest.length) →
    WP isa (.block (rest.map fun r => Instr.alu .adc r (.imm 0))) s fun s' =>
      regsVal s' rest = regsVal s rest + c.toNat ∧ Keeps rest s s'
  | [], s, c, _, _, hb => WP.block_nil ⟨by
      simp only [regsVal, List.length_nil, Nat.mul_zero, Nat.pow_zero] at hb ⊢; omega,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | r :: rest, s, c, hc, hnd, hb => by
    obtain ⟨hr, hnd'⟩ := List.nodup_cons.mp hnd
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (adc0_ok s r hc) fun s₁ ⟨c', cf₁, e₁, k₁⟩ => ?_
    have hR : regsVal s₁ rest = regsVal s rest :=
      regsVal_congr fun q hq => k₁.1 q (by simp only [List.mem_singleton]; exact fun h => hr (h ▸ hq))
    have hb' : regsVal s₁ rest + c'.toNat < 2 ^ (64 * rest.length) := by
      have hX := (s.gpr r).isLt
      have hX₁ := (s₁.gpr r).isLt
      simp only [regsVal, List.length_cons, pow64_succ] at hb
      have : 2 ^ 64 * (regsVal s rest + c'.toNat) < 2 ^ 64 * 2 ^ (64 * rest.length) := by
        rw [Nat.mul_add]; omega
      rw [hR]; exact Nat.lt_of_mul_lt_mul_left this
    refine WP.mono (adcZeros_ok rest cf₁ hnd' hb') fun s₂ ⟨e₂, k₂⟩ => ⟨?_, ?_⟩
    · have g : s₂.gpr r = s₁.gpr r := k₂.1 r hr
      simp only [regsVal, g, e₂, hR]
      rw [Nat.mul_add]; omega
    · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- `rdx:rax = t₀ w`. -/
theorem mulImm_ok (s : State) {t0 : Reg} (w : BitVec 64) (h0 : t0 ≠ .rax) :
    WP isa (.block [.movImm64 .rax w, .mul t0]) s fun s' =>
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = w.toNat * (s.gpr t0).toNat ∧
      Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execMul, RegUpd.gpr_setReg,
    RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, h0, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have := (w.toNat * (s.gpr t0).toNat).div_add_mod (2 ^ 64)
    have hlt : w.toNat * (s.gpr t0).toNat / 2 ^ 64 < 2 ^ 64 := by
      have := w.isLt; have := (s.gpr t0).isLt
      exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega))
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

/-- `t:t' += rdx:rax`, the carry out in `CF`. -/
theorem addPair_ok (s : State) {t t' : Reg} (htt : t ≠ t') (ht : t ≠ .rax ∧ t ≠ .rdx) :
    WP isa (.block [.alu .add t (.reg .rax), .alu .adc t' (.reg .rdx)]) s fun s' => ∃ c, s'.cf = some c ∧
      (s'.gpr t).toNat + 2 ^ 64 * (s'.gpr t').toNat + 2 ^ 128 * c.toNat =
        (s.gpr t).toNat + 2 ^ 64 * (s.gpr t').toNat + (s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat ∧
      Keeps [t, t'] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    ite_true, ite_false, htt, Ne.symm htt, Ne.symm ht.2, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e0 := add_carry (s.gpr t) (s.gpr .rax)
    have e1 := adc_carry (s.gpr t') (s.gpr .rdx) (decide (2 ^ 64 ≤ (s.gpr t).toNat + (s.gpr .rax).toNat))
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- `ts += t₀ w`, if it does not overflow. -/
theorem addProd_ok (s : State) {t0 : Reg} (w : BitVec 64) {ts : List Reg} (hl : 2 ≤ ts.length)
    (hf : Fresh ts) (ht0 : t0 ∉ ts) (h0 : t0 ≠ .rax ∧ t0 ≠ .rdx)
    (hb : regsVal s ts + (s.gpr t0).toNat * w.toNat < 2 ^ (64 * ts.length)) :
    WP isa (.block (addProd t0 w ts)) s fun s' =>
      regsVal s' ts = regsVal s ts + (s.gpr t0).toNat * w.toNat ∧ Keeps (.rax :: .rdx :: ts) s s' := by
  match ts, hl, hf, ht0, hb with
  | t :: t' :: rest, _, hf, ht0, hb =>
    obtain ⟨htn, hta, -, htd, -, -⟩ := hf.head
    obtain ⟨htn', hta', -, htd', -, -⟩ := hf.tail.head
    have hnd := hf.tail.tail.1
    have htt : t ≠ t' := fun h => htn (h ▸ List.mem_cons_self ..)
    rw [addProd, WP.block_append_iff, show ([.movImm64 .rax w, .mul t0, .alu .add t (.reg .rax),
        .alu .adc t' (.reg .rdx)] : List Instr) = [.movImm64 .rax w, .mul t0] ++
        [.alu .add t (.reg .rax), .alu .adc t' (.reg .rdx)] from rfl, WP.block_append_iff]
    refine WP.mono (mulImm_ok s w h0.1) fun s₁ ⟨e₁, k₁⟩ => ?_
    refine WP.mono (addPair_ok s₁ htt ⟨hta, htd⟩) fun s₂ ⟨c, cf₂, e₂, k₂⟩ => ?_
    have g₁ : ∀ q, q ≠ .rax → q ≠ .rdx → s₁.gpr q = s.gpr q := fun q h1 h2 => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
    have hR : regsVal s₂ rest = regsVal s rest := regsVal_congr fun q hq => by
      have hq' := hf.2 q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
      rw [k₂.1 q (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => htn (h ▸ List.mem_cons_of_mem _ hq), fun h => htn' (h ▸ hq)⟩),
        g₁ q hq'.1 hq'.2.2.1]
    rw [g₁ t hta htd, g₁ t' hta' htd'] at e₂
    rw [Nat.mul_comm w.toNat] at e₁
    simp only [regsVal, List.length_cons] at hb
    rw [show 64 * (rest.length + 1 + 1) = 128 + 64 * rest.length by omega, Nat.pow_add] at hb
    generalize hA : 2 ^ (64 * rest.length) = A at hb
    generalize (s.gpr t0).toNat * w.toNat = P at hb e₁ ⊢
    have hb' : regsVal s₂ rest + c.toNat < 2 ^ (64 * rest.length) := by
      rw [hR, hA]
      have : 2 ^ 128 * (regsVal s rest + c.toNat) < 2 ^ 128 * A := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    refine WP.mono (adcZeros_ok rest cf₂ hnd hb') fun s₃ ⟨e₃, k₃⟩ => ⟨?_, ?_⟩
    · have gt : s₃.gpr t = s₂.gpr t := k₃.1 t (fun h => htn (List.mem_cons_of_mem _ h))
      have gt' : s₃.gpr t' = s₂.gpr t' := k₃.1 t' (fun h => htn' h)
      simp only [regsVal, gt, gt', e₃, hR]
      omega
    · exact ((k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans (k₃.mono (by sub_regs))

/-- A word of `m'` other than zero, as the code multiplies by it. -/
theorem mword_lt {w : MWord} (h : w.ok = true) : w.val < 2 ^ 64 := by
  cases w with
  | zero => decide
  | one => decide
  | pow2 k =>
    simp only [MWord.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    exact Nat.pow_lt_pow_right (by decide) h.2
  | gen v => simpa [MWord.ok, MWord.val] using h

/-- `ts += t₀ m'` for the words `ws` of `m'`, if it does not overflow. -/
theorem redWords_ok (t0 : Reg) : ∀ (ws : List MWord) {s : State} {ts : List Reg},
    ws.length + 1 ≤ ts.length → Fresh ts → t0 ∉ ts → t0 ≠ .rax ∧ t0 ≠ .rdx → ws.all MWord.ok = true →
    regsVal s ts + (s.gpr t0).toNat * mwVal ws < 2 ^ (64 * ts.length) →
    WP isa (.block (redWords t0 ws ts)) s fun s' =>
      regsVal s' ts = regsVal s ts + (s.gpr t0).toNat * mwVal ws ∧ Keeps (.rax :: .rdx :: ts) s s'
  | [], s, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [mwVal], fun _ _ => rfl, rfl, rfl, rfl⟩
  | w :: ws, s, ts, hl, hf, ht0, h0, hok, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    have hw := mword_lt hok.1
    match ts, hl, hf, ht0, hb with
    | t :: ts', hl, hf, ht0, hb =>
      have htn := hf.head.1
      have ht0' : t0 ∉ ts' := fun h => ht0 (List.mem_cons_of_mem _ h)
      have hT : t0 ≠ t := fun h => ht0 (h ▸ List.mem_cons_self ..)
      simp only [List.length_cons] at hl
      -- The first word.
      have hfirst : WP isa (.block (if w = .zero then [] else addProd t0 (BitVec.ofNat 64 w.val) (t :: ts'))) s
          fun s₁ => regsVal s₁ (t :: ts') = regsVal s (t :: ts') + (s.gpr t0).toNat * w.val ∧
            Keeps (.rax :: .rdx :: t :: ts') s s₁ := by
        split
        · rename_i hz
          subst hz
          exact WP.block_nil ⟨by simp [MWord.val], fun _ _ => rfl, rfl, rfl, rfl⟩
        · have hv : (BitVec.ofNat 64 w.val).toNat = w.val := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
          refine WP.mono (addProd_ok s _ (by simp only [List.length_cons]; omega) hf ht0 h0 ?_)
            fun s₁ ⟨e₁, k₁⟩ => ⟨by rw [e₁, hv], k₁⟩
          rw [hv]
          have : (s.gpr t0).toNat * w.val ≤ (s.gpr t0).toNat * mwVal (w :: ws) :=
            Nat.mul_le_mul_left _ (by simp only [mwVal]; omega)
          omega
      rw [redWords, WP.block_append_iff]
      refine WP.mono hfirst fun s₁ ⟨e₁, k₁⟩ => ?_
      have g0 : s₁.gpr t0 = s.gpr t0 := k₁.1 t0 (by
        simp only [List.mem_cons, not_or]; exact ⟨h0.1, h0.2, hT, ht0'⟩)
      have hR := regsVal_lt s₁ [t]
      simp only [regsVal, List.length_cons, List.length_nil, Nat.mul_zero, Nat.add_zero] at e₁ hR hb
      rw [List.tail_cons]
      have hb' : regsVal s₁ ts' + (s₁.gpr t0).toNat * mwVal ws < 2 ^ (64 * ts'.length) := by
        rw [g0]
        rw [pow64_succ] at hb
        have hm : (s.gpr t0).toNat * mwVal (w :: ws) =
            (s.gpr t0).toNat * w.val + 2 ^ 64 * ((s.gpr t0).toNat * mwVal ws) := by
          simp only [mwVal, Nat.mul_add, Nat.mul_left_comm]
        rw [hm] at hb
        have : 2 ^ 64 * (regsVal s₁ ts' + (s.gpr t0).toNat * mwVal ws) < 2 ^ 64 * 2 ^ (64 * ts'.length) := by
          rw [Nat.mul_add]; omega
        exact Nat.lt_of_mul_lt_mul_left this
      refine WP.mono (redWords_ok t0 ws (s := s₁) (ts := ts') (by omega) hf.tail ht0' h0 hok.2 hb')
        fun s₂ ⟨e₂, k₂⟩ => ⟨?_, ?_⟩
      · have gt : s₂.gpr t = s₁.gpr t := k₂.1 t (by
          simp only [List.mem_cons, not_or]; exact ⟨hf.head.2.1, hf.head.2.2.2.1, htn⟩)
        simp only [regsVal, gt, e₂, g0]
        have hm : (s.gpr t0).toNat * mwVal (w :: ws) =
            (s.gpr t0).toNat * w.val + 2 ^ 64 * ((s.gpr t0).toNat * mwVal ws) := by
          simp only [mwVal, Nat.mul_add, Nat.mul_left_comm]
        rw [hm]
        omega
      · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-- The reduction of a round for a friendly modulus: `2⁶⁴ T' = T + t₀ m`. -/
theorem redF_ok {s : State} {n i m : Nat} (hn : n < 7) {ws : List MWord}
    (hr : (Red.friendly ws).ok n m = true) (hm : m < 2 ^ (64 * n))
    (hb : regsVal s (wins n i) + (s.gpr (win n i 0)).toNat * m < 2 ^ 64 * (2 * m)) :
    WP isa (.block (redWords (win n i 0) ws (wins n i).tail ++ ([.mov32 (win n i 0) (.imm 0)] : List Instr))) s
      fun s' => 2 ^ 64 * regsVal s' (wins n (i + 1)) = regsVal s (wins n i) + (s.gpr (win n i 0)).toNat * m ∧
        Keeps (.rax :: .rdx :: wins n i) s s' := by
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨⟨⟨hlen, hm1⟩, hmv⟩, hok⟩ := hr
  have hf := fresh_wins hn i
  have hcons := wins_cons n i
  generalize ht : (List.range (n + 1)).map (fun j => win n i (j + 1)) = tail at hcons
  have hf' : Fresh (win n i 0 :: tail) := hcons ▸ hf
  have htl : tail.length = n + 1 := by rw [← ht]; simp
  have h0 := hf'.head
  -- `2⁶⁴ m' = m + 1`.
  have hm' : 2 ^ 64 * mwVal ws = m + 1 := by
    rw [hmv]; have := Nat.div_add_mod (m + 1) (2 ^ 64)
    have : (m + 1) % 2 ^ 64 = 0 := by omega
    omega
  rw [hcons, List.tail_cons, WP.block_append_iff]
  generalize hx : (s.gpr (win n i 0)).toNat = x at hb
  have hT : regsVal s (win n i 0 :: tail) = x + 2 ^ 64 * regsVal s tail := by rw [regsVal, hx]
  rw [hcons, hT] at hb
  refine WP.mono (redWords_ok (win n i 0) ws (s := s) (ts := tail) (by omega) hf'.tail h0.1
    ⟨h0.2.1, h0.2.2.2.1⟩ hok (by
      rw [hx, htl, pow64_succ]
      have : 2 ^ 64 * (regsVal s tail + x * mwVal ws) < 2 ^ 64 * (2 ^ 64 * 2 ^ (64 * n)) := by
        rw [Nat.mul_add, Nat.mul_left_comm, hm', Nat.mul_add, Nat.mul_one]
        omega
      exact Nat.lt_of_mul_lt_mul_left this)) fun s₁ ⟨e₁, k₁⟩ => ?_
  have g0 : s₁.gpr (win n i 0) = s.gpr (win n i 0) := k₁.1 _ (by
    simp only [List.mem_cons, not_or]; exact ⟨h0.2.1, h0.2.2.2.1, h0.1⟩)
  refine WP.mono (mov32zero_ok s₁ (win n i 0)) fun s₂ ⟨z₂, _, k₂⟩ => ⟨?_, ?_⟩
  · rw [wins_succ, ht, regsVal_append, htl]
    have : regsVal s₂ tail = regsVal s₁ tail := regsVal_congr fun q hq => k₂.1 q (by
      simp only [List.mem_singleton]; exact fun h => h0.1 (h ▸ hq))
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [regsVal, z₂, hz, Nat.mul_zero, Nat.add_zero, this, e₁, hx]
    have key : 2 ^ 64 * (x * mwVal ws) = x * m + x := by
      rw [Nat.mul_left_comm, hm', Nat.mul_add, Nat.mul_one]
    omega
  · exact (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))

/-! ## A round -/

/-- Round `i` of the multiplication by `mul`: `2⁶⁴ T' = T + a_i B + u m`, and
`T' < 2m` if `T < 2m`. -/
theorem roundM_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : M.n < 7) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (hm : wordsVal s.mem base M.mo M.n = m)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) (hred : M.red.ok M.n m = true)
    (hB : wordsVal s.mem base b M.n < m) (hT : regsVal s (wins M.n i) < 2 * m) :
    WP isa (.block (roundM M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m ∧
      Keeps (.rax :: .rcx :: .rdx :: .rbp :: wins M.n i) s s' := by
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hA := (word s.mem base (a + 8 * i)).isLt
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  rw [show roundM M a b i = (([.mov .rcx (.mem (sc (a + 8 * i)))] : List Instr) ++
      (mulRow ((List.range M.n).map (win M.n i)) b ++ carryUp (win M.n i M.n) (win M.n i (M.n + 1)))) ++
        redRound M i by simp only [roundM, List.append_assoc], WP.block_append_iff]
  refine WP.mono (prod_ok hs hn ha hb hm' hB hT) fun s₂ ⟨e₂, hs₂, k₂⟩ => ?_
  have hmem : s₂.mem = s.mem := k₂.2.1
  -- From `2⁶⁴ T' = T + a_i B + u m` for a word `u`.
  have fin : ∀ {s' : State} (u : Nat), u < 2 ^ 64 →
      2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s₂ (wins M.n i) + u * m →
      (∃ u, 2 ^ 64 * regsVal s' (wins M.n (i + 1)) = regsVal s (wins M.n i) +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      regsVal s' (wins M.n (i + 1)) < 2 * m := fun u hu e => by
    rw [e₂] at e
    have hum : u * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    refine ⟨⟨u, e⟩, Nat.lt_of_mul_lt_mul_left (a := 2 ^ 64) ?_⟩
    rw [e]; omega
  unfold redRound
  split
  · rename_i hg
    refine WP.mono (redGen_ok hs₂ hn hmo (by rw [hmem, hm]) hinv (by rw [e₂]; omega))
      fun s' ⟨⟨u, hu, eu⟩, k⟩ => ⟨(fin u hu eu).1, (fin u hu eu).2, k₂.trans k⟩
  · rename_i ws hf
    rw [hf] at hred
    have ht0 := (s₂.gpr (win M.n i 0)).isLt
    have hum : (s₂.gpr (win M.n i 0)).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
    refine WP.mono (redF_ok hn hred hm' (by rw [e₂]; omega)) fun s' ⟨e, k⟩ =>
      ⟨(fin _ ht0 e).1, (fin _ ht0 e).2, k₂.trans (k.mono (by sub_regs))⟩

end VG.Proof.Mont.X86_64
