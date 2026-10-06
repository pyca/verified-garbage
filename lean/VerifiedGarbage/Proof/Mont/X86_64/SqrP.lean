import VerifiedGarbage.Proof.Mont.X86_64.MulP

/-!
# Montgomery arithmetic on x86-64: P-521's square by columns

`sqrP o a` (`Impl/Mont/X86_64.lean`) is `mulP o a a` with each product of
two different words computed once and added twice: a term adds its product
once or twice (`sTerm_ok`, the second time `rdx:rax` again, `sAdd_ok`), a
column its terms (`sCol_ok`), whose sums over the eighteen columns are
`a²` and the reduction's `2⁵²¹ U` (`sColSum_total`), so that `prodCols_ok`
gives `sqrP_ok`.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry)

/-- `r0–r2 += rdx:rax`, for distinct `r0–r2` other than `rax`, `rcx`, `rdx`,
if the sum fits. -/
theorem sAdd_ok (s : State) {r0 r1 r2 : Reg} (hd : [r0, r1, r2, .rax, .rcx, .rdx, .rdi].Nodup)
    (hb : regsVal s [r0, r1, r2] + ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat) < 2 ^ 192) :
    WP isa (.block [.alu .add r0 (.reg .rax), .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]) s fun s' =>
      regsVal s' [r0, r1, r2] = regsVal s [r0, r1, r2] + ((s.gpr .rax).toNat + 2 ^ 64 * (s.gpr .rdx).toNat) ∧
      Keeps [r0, r1, r2] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0c, h0d, h0i⟩, ⟨h12, h1a, h1c, h1d, h1i⟩, ⟨h2a, h2c, h2d, h2i⟩, -⟩ := hd
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, ite_false, Ne.symm h01, Ne.symm h02, Ne.symm h12, Ne.symm h0d,
    Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, ite_false,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12, Nat.mul_zero, Nat.add_zero]
    have e0 := add_carry (s.gpr r0) (s.gpr .rax)
    generalize decide (2 ^ 64 ≤ (s.gpr r0).toNat + (s.gpr .rax).toNat) = c0 at e0 ⊢
    have e1 := adc_carry (s.gpr r1) (s.gpr .rdx) c0
    generalize decide (2 ^ 64 ≤ (s.gpr r1).toNat + (s.gpr .rdx).toNat + c0.toNat) = c1 at e1 ⊢
    have e2 := adc_carry (s.gpr r2) 0 c1
    generalize decide (2 ^ 64 ≤ (s.gpr r2).toNat + (0 : BitVec 64).toNat + c1.toNat) = c2 at e2
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hb
    have z : (0 : BitVec 64).toNat = 0 := rfl
    have := Bool.toNat_le c2
    have := (s.gpr r0 + s.gpr .rax).isLt; have := (s.gpr r1 + s.gpr .rdx + (BitVec.ofBool c0).setWidth 64).isLt
    have := (s.gpr r2 + 0 + (BitVec.ofBool c1).setWidth 64).isLt
    rw [z] at e2
    rcases Nat.lt_or_ge c2.toNat 1 with h | h <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

/-- A term's multiplicity. -/
abbrev mult (two : Bool) : Nat := if two then 2 else 1

/-- A squaring's term: `acc += [dx] · y`, twice if `two`. -/
theorem sTerm_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Nat) {dx : Nat}
    (hdx : dx + 8 ≤ size) {dy : Option Nat} (hdy : ∀ d, dy = some d → d + 8 ≤ size) (two : Bool)
    (hb : regsVal s (pAccs c) + mult two * ((word s.mem base dx).toNat * pY s.mem base dy) < 2 ^ 192) :
    WP isa (.block (sTerm c dx dy two)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + mult two * ((word s.mem base dx).toNat * pY s.mem base dy) ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s' := by
  rw [sTerm, WP.block_append_iff]
  refine WP.mono (pTerm_ok hs c hdx hdy (by cases two <;> simp only [mult, Bool.false_eq_true, ↓reduceIte] at hb <;> omega))
    fun s₁ ⟨e₁, k₁, x₁⟩ => ?_
  cases two with
  | false => exact WP.block_nil ⟨by rw [e₁]; simp [mult], k₁⟩
  | true =>
    simp only [ite_true]
    have hok := pAccs_ok c
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    refine WP.mono (sAdd_ok s₁ hok.1 (by
      rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₁, x₁]
      simp only [mult, ↓reduceIte] at hb; omega)) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans (k₂.mono (by simp [pAccs]))⟩
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₁, x₁] at e₂
    rw [e₂]; simp only [mult, ↓reduceIte]; omega

/-- The sum of a squaring's terms, with their multiplicities. -/
def sSum (m : Mem) (base : Addr) (ts : List (Nat × Option Nat × Bool)) : Nat :=
  (ts.map fun t => mult t.2.2 * ((word m base t.1).toNat * pY m base t.2.1)).sum

/-- A squaring's column's terms, by induction on them. -/
theorem sTerms_ok (c : Nat) {size : Nat} : ∀ (ts : List (Nat × Option Nat × Bool)) {s : State} {base : Addr},
    Scr s base size → (∀ t ∈ ts, PIn size (t.1, t.2.1)) → regsVal s (pAccs c) + sSum s.mem base ts < 2 ^ 192 →
    WP isa (.block (ts.flatMap fun t => sTerm c t.1 t.2.1 t.2.2)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + sSum s.mem base ts ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s'
  | [], s, _, _, _, _ => WP.block_nil ⟨by simp [sSum], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, hs, hin, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have ht := hin t List.mem_cons_self
    simp only [sSum, List.map_cons, List.sum_cons] at hb
    refine WP.mono (sTerm_ok hs c (dx := t.1) (dy := t.2.1) ht.1 ht.2 t.2.2 (by omega)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by have := (pAccs_ok c).2; simp only [List.mem_cons, not_or]; grind)
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    refine WP.mono (sTerms_ok c ts hs₁ (fun t' ht' => hin t' (List.mem_cons_of_mem _ ht'))
      (by rw [e₁, hm₁]; simp only [sSum] at hb ⊢; omega)) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    rw [e₂, e₁, hm₁]
    simp only [sSum, List.map_cons, List.sum_cons]
    omega

/-- Column `c` of `sqrP`: its terms, and its low word stored at
`[tmp + 8 (c mod 9)]`; the rest of the accumulator is the next column's. -/
theorem sCol_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {a c : Nat}
    (htmp : M.tmp + 72 ≤ size) (hin : ∀ t ∈ sTerms M a c, PIn size (t.1, t.2.1))
    (hb : regsVal s (pAccs c) + sSum s.mem base (sTerms M a c) < 2 ^ 192) :
    WP isa (.block (sCol M a c)) s fun s' =>
      (word s'.mem base (M.tmp + 8 * (c % 9))).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) =
        regsVal s (pAccs c) + sSum s.mem base (sTerms M a c) ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (M.tmp + 8 * (c % 9)) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hc9 := Nat.mod_lt c (show 0 < 9 by decide)
  have hsub := (pAccs_ok c).2
  rw [sCol, WP.block_append_iff]
  refine WP.mono (sTerms_ok c _ hs hin hb) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by simp only [List.mem_cons, not_or]; grind)
  refine WP.mono (pEnd_ok hs₁ c (t := M.tmp + 8 * (c % 9)) (by omega)) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [m₂, word_writeW_self, ← e₂, e₁]
  · refine ⟨fun r hr => ?_, k₂.rd.trans k₁.2.2.1, k₂.wr.trans k₁.2.2.2⟩
    have hr' : r ∉ pAccs c := fun h => hr (by
      have := hsub r h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      grind)
    have h1 : r ∉ Reg.rax :: Reg.rcx :: Reg.rdx :: pAccs c := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨hr.1, hr.2.1, hr.2.2.1, hr'⟩
    have h2 : r ∉ [pAcc c 0] := fun h => hr' (by
      simp only [List.mem_singleton] at h
      simp [h, pAccs])
    rw [k₂.gpr r h2, k₁.1 r h1]
  · rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega)

/-! ## The columns' arithmetic -/

/-- Column `c`'s sum: its products `2 A i · A j` (`i < j`, `i + j = c`), its
square `A (c / 2)²` for even `c`, and for `8 ≤ c ≤ 16` `512 l_{c-8}`. -/
def sColSum (A l : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map fun i => 2 * (A i * A (c - i))).sum +
    ((if c % 2 = 0 ∧ c / 2 < 9 then A (c / 2) * A (c / 2) else 0) +
    if 8 ≤ c ∧ c ≤ 16 then l (c - 8) * 512 else 0)

/-- The eighteen columns: the square, and `2⁵²¹ Σ_{k<9} 2^(64 k) l_k`. -/
theorem sColSum_total (A l : Nat → Nat) :
    hval (sColSum A l) 0 18 = hval A 0 9 * hval A 0 9 + 512 * (2 ^ 64) ^ 8 * hval l 0 9 := by
  simp only [hval, sColSum, List.range, List.range.loop, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul,
    Nat.reduceMod, Nat.reduceDiv, and_true, and_false, ↓reduceIte, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  generalize 2 ^ 64 = X
  grind

/-- A squaring's column's terms' sum, from the words they read. -/
theorem sSum_sTerms {m : Mem} {base : Addr} {M : Mod} {a c : Nat} {A l : Nat → Nat}
    (hA : ∀ i < 9, (word m base (a + 8 * i)).toNat = A i)
    (hl : 8 ≤ c → c ≤ 16 → (word m base (M.tmp + 8 * (c - 8))).toNat = l (c - 8)) :
    sSum m base (sTerms M a c) = sColSum A l c := by
  simp only [sSum, sTerms, sColSum, List.map_append, List.sum_append, List.map_map]
  have e1 : (((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map
      ((fun t : Nat × Option Nat × Bool => mult t.2.2 * ((word m base t.1).toNat * pY m base t.2.1)) ∘
        fun i => (a + 8 * i, some (a + 8 * (c - i)), true))).sum =
      (((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map fun i => 2 * (A i * A (c - i))).sum := by
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    simp only [Function.comp, pY, mult, ↓reduceIte, hA i hi.1, hA (c - i) hi.2.2]
  rw [e1, Nat.add_assoc]
  refine congrArg (_ + ·) (congrArg₂ (· + ·) ?_ ?_)
  · split
    · rename_i h
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, pY, mult,
        Bool.false_eq_true, ↓reduceIte, Nat.one_mul, hA _ h.2]
    · simp
  · split
    · rename_i h
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, pY, mult,
        Bool.false_eq_true, ↓reduceIte, Nat.one_mul, hl h.1 h.2]
    · simp

/-- `sqrP`'s column sums. -/
theorem colSum_s (A : Nat → Nat) (hA : ∀ i, A i < 2 ^ 64) : ColSum (sColSum A) where
  congr l l' c h := by
    unfold sColSum
    by_cases hc : 8 ≤ c ∧ c ≤ 16
    · rw [h hc.1 hc.2]
    · simp only [hc, ↓reduceIte]
  lt l c h := by
    unfold sColSum
    have hAA : ∀ i j, A i * A j ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := fun i j =>
      Nat.mul_le_mul (by have := hA i; omega) (by have := hA j; omega)
    have h1 := sum_le_mul (L := ((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map
        fun i => 2 * (A i * A (c - i))) (K := 2 * ((2 ^ 64 - 1) * (2 ^ 64 - 1))) fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact Nat.mul_le_mul_left _ (hAA i (c - i))
    have h2 : (((List.range 9).filter fun i => 2 * i < c ∧ c - i < 9).map
        fun i => 2 * (A i * A (c - i))).length ≤ 9 := by
      rw [List.length_map]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp)
    have h3 := Nat.mul_le_mul_right (2 * ((2 ^ 64 - 1) * (2 ^ 64 - 1))) h2
    have h4 : (if c % 2 = 0 ∧ c / 2 < 9 then A (c / 2) * A (c / 2) else 0) ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
      split
      · exact hAA _ _
      · exact Nat.zero_le _
    have h5 : (if 8 ≤ c ∧ c ≤ 16 then l (c - 8) * 512 else 0) < 2 ^ 64 * 512 := by
      split
      · rename_i hc; have := h hc.1 hc.2; omega
      · omega
    have : 9 * (2 * ((2 ^ 64 - 1) * (2 ^ 64 - 1))) + (2 ^ 64 - 1) * (2 ^ 64 - 1) + 2 ^ 64 * 512 ≤ 2 ^ 133 := by
      decide
    omega

/-- `sqrP`'s columns. -/
theorem sCol_colOk {base : Addr} {size : Nat} {m₀ : Mem} {M : Mod} {a : Nat}
    (htmp : M.tmp + 72 ≤ size) (ha : a + 72 ≤ size) (haT : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a) :
    ColOk M base size m₀ (sCol M a) (sColSum fun i => (word m₀ base (a + 8 * i)).toNat) :=
  fun c hc s l hsS O hacc hL => by
    have hnw := hsS.nowrap
    have hA : ∀ i < 9, (word s.mem base (a + 8 * i)).toNat = (word m₀ base (a + 8 * i)).toNat :=
      fun i hi => by rw [O.word (by omega) (by omega)]
    have hsum := sSum_sTerms (M := M) (c := c) hA hL
    have hcol := (colSum_s (fun i => (word m₀ base (a + 8 * i)).toNat) (fun _ => (word _ _ _).isLt)).lt l c
      fun h1 h2 => by rw [← hL h1 h2]; exact (word _ _ _).isLt
    have hin : ∀ t ∈ sTerms M a c, PIn size (t.1, t.2.1) := by
      intro t ht
      simp only [sTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with (⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht) | ht
      · exact ⟨by omega, fun d hd => by simp only [Option.some.injEq] at hd; omega⟩
      · split at ht
        · rename_i h
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by omega, fun d hd => by simp only [Option.some.injEq] at hd; omega⟩
        · simp at ht
      · split at ht
        · simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by omega, fun d hd => by simp at hd⟩
        · simp at ht
    refine WP.mono (sCol_ok hsS htmp hin (by rw [hsum]; omega)) fun s' ⟨e', k', O'⟩ =>
      ⟨by rw [e', hsum], k', O'⟩

/-- `[o] = [a]² R⁻¹ mod p` for P-521's `p`, `R = 2⁵⁷⁶`. -/
theorem sqrP_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o) (hB : wordsVal s.mem base a M.n < m) :
    WP isa (.block (sqrP M o a)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base a M.n % m := by
  have hn9 := (p521_of_red hred hM.red).1
  have htmp := hM.tmp
  rw [hn9] at ha haT htmp
  have hv : wordsVal s.mem base a M.n = hval (fun i => (word s.mem base (a + 8 * i)).toNat) 0 9 := by
    rw [hn9, ← wordsVal_hval s.mem base a 0 9, Nat.mul_zero, Nat.add_zero]
  rw [sqrP, hv]
  exact prodCols_ok hs hM hred ho hoT hoM (colSum_s _ fun _ => (word _ _ _).isLt)
    (sCol_colOk (by omega) (by omega) (by omega)) (by rw [← hv]; exact wordsVal_lt _ _ _ _)
    (by rw [← hv]; exact hB) fun l => sColSum_total _ l

end VG.Proof.Mont.X86_64
