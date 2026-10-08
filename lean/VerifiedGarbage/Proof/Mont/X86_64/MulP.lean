import VerifiedGarbage.Proof.Mont.X86_64.WideOps

/-!
# Montgomery arithmetic on x86-64: P-521's product by columns

`mulP o a b` (`Impl/Mont/X86_64.lean`) for P-521's `p = 2⁵²¹ - 1`: a term
adds a product to the three-word accumulator (`pTerm_ok`), a column adds its
terms and stores its low word (`pCol_ok`), and the eighteen columns
(`pCols_ok`, by induction on them) leave `(a b + U p) / 2⁵⁷⁶` in the
temporary area and `r9`, for the reduction's `U < 2⁵⁷⁶`: the low words of the
first nine columns, each of which column `k + 8` adds 512 times. Then
`csubW` (`mulP_ok`).
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 add_carry adc_carry mulx_arith)

/-! ## The accumulator -/

/-- The accumulator of column `c`, lowest word first. -/
def pAccs (c : Nat) : List Reg := [pAcc c 0, pAcc c 1, pAcc c 2]

theorem pAcc_mod (c k : Nat) : pAcc c k = [Reg.r9, .r10, .r11].getD ((c + k) % 3) .r9 := rfl

theorem pAccs_cases (c : Nat) :
    pAccs c = [.r9, .r10, .r11] ∨ pAccs c = [.r10, .r11, .r9] ∨ pAccs c = [.r11, .r9, .r10] := by
  simp only [pAccs, pAcc_mod]
  rcases (by omega : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2) with h | h | h <;>
  simp only [Nat.add_mod c, h] <;> simp

theorem pAccs_succ (c : Nat) : pAccs (c + 1) = [pAcc c 1, pAcc c 2, pAcc c 0] := by
  simp only [pAccs, pAcc_mod]
  refine List.cons_eq_cons.mpr ⟨by rw [Nat.add_right_comm], List.cons_eq_cons.mpr
    ⟨by rw [Nat.add_assoc], List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩
  rw [show c + 1 + 2 = c + 3 by omega, Nat.add_mod_right, Nat.add_zero]

/-- The accumulator's registers are distinct, and none of `rax`, `rcx`,
`rdx`, `rdi`. -/
theorem pAccs_ok (c : Nat) :
    [pAcc c 0, pAcc c 1, pAcc c 2, .rax, .rcx, .rdx, .rdi].Nodup ∧
      ∀ r ∈ pAccs c, r ∈ [Reg.r9, .r10, .r11] := by
  have := pAccs_cases c
  simp only [pAccs, List.cons.injEq, and_true] at this ⊢
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [h0, h1, h2] <;> decide

/-! ## A term -/

/-- The value of a term's second factor: the word at `dy`, or 512. -/
def pY (m : Mem) (base : Addr) : Option Nat → Nat
  | some d => (word m base d).toNat
  | none => 512

/-- `rcx = y`. -/
theorem pLoadY_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dy : Option Nat}
    (hdy : ∀ d, dy = some d → d + 8 ≤ size) :
    WP isa (.block [.mov .rcx (pSrc dy)]) s
      fun s' => (s'.gpr .rcx).toNat = pY s.mem base dy ∧ Keeps [.rcx] s s' := by
  cases dy with
  | some d =>
    rw [pSrc]
    refine WP.mono (movRcx_ok hs (hdy d rfl)) fun s' ⟨e, k⟩ => ⟨by rw [e]; rfl, k⟩
  | none =>
    apply WP.of_runBlock
    simp only [pSrc, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- `rdx:rax = [dx] · rcx`, then `r0–r2 += rdx:rax`, for distinct `r0–r2`
other than `rax`, `rcx`, `rdx`, if the sum fits. -/
theorem pMulAcc_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {r0 r1 r2 : Reg}
    (hd : [r0, r1, r2, .rax, .rcx, .rdx, .rdi].Nodup) {dx : Nat} (hdx : dx + 8 ≤ size)
    (hb : regsVal s [r0, r1, r2] + (word s.mem base dx).toNat * (s.gpr .rcx).toNat < 2 ^ 192) :
    WP isa (.block [.mov .rax (.mem (sc dx)), .mul .rcx, .alu .add r0 (.reg .rax),
      .alu .adc r1 (.reg .rdx), .alu .adc r2 (.imm 0)]) s fun s' =>
      regsVal s' [r0, r1, r2] = regsVal s [r0, r1, r2] + (word s.mem base dx).toNat * (s.gpr .rcx).toNat ∧
      Keeps [.rax, .rdx, r0, r1, r2] s s' ∧
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = (word s.mem base dx).toNat * (s.gpr .rcx).toNat := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h0a, h0c, h0d, h0i⟩, ⟨h12, h1a, h1c, h1d, h1i⟩, ⟨h2a, h2c, h2d, h2i⟩, -⟩ := hd
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, load_sc hs hdx, readSrc, execMul,
    execAlu, Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false,
    reduceCtorEq, Ne.symm h01, Ne.symm h02, Ne.symm h12, h0a, h1a, h2a, h0d, h1d, h2d,
    Ne.symm h0d, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp only [regsVal, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, ite_true, ite_false,
      h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12, Nat.mul_zero, Nat.add_zero]
    have em := mulx_arith (word s.mem base dx) (s.gpr .rcx)
    generalize BitVec.ofNat 64 ((word s.mem base dx).toNat * (s.gpr .rcx).toNat) = lo at em ⊢
    generalize BitVec.ofNat 64 ((word s.mem base dx).toNat * (s.gpr .rcx).toNat / 2 ^ 64) = hi at em ⊢
    have e0 := add_carry (s.gpr r0) lo
    generalize decide (2 ^ 64 ≤ (s.gpr r0).toNat + lo.toNat) = c0 at e0 ⊢
    have e1 := adc_carry (s.gpr r1) hi c0
    generalize decide (2 ^ 64 ≤ (s.gpr r1).toNat + hi.toNat + c0.toNat) = c1 at e1 ⊢
    have e2 := adc_carry (s.gpr r2) 0 c1
    generalize decide (2 ^ 64 ≤ (s.gpr r2).toNat + (0 : BitVec 64).toNat + c1.toNat) = c2 at e2
    simp only [regsVal, Nat.mul_zero, Nat.add_zero] at hb
    have z : (0 : BitVec 64).toNat = 0 := rfl
    have := Bool.toNat_le c2
    have := (s.gpr r0 + lo).isLt; have := (s.gpr r1 + hi + (BitVec.ofBool c0).setWidth 64).isLt
    have := (s.gpr r2 + 0 + (BitVec.ofBool c1).setWidth 64).isLt
    rw [z] at e2
    rcases Nat.lt_or_ge c2.toNat 1 with h | h <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2, ite_false]
  · simp only [Ne.symm h0a, Ne.symm h1a, Ne.symm h2a, Ne.symm h1d, Ne.symm h2d, ite_false]
    exact mulx_arith (word s.mem base dx) (s.gpr .rcx)

/-- A term: `acc += [dx] · y`. -/
theorem pTerm_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Nat) {dx : Nat}
    (hdx : dx + 8 ≤ size) {dy : Option Nat} (hdy : ∀ d, dy = some d → d + 8 ≤ size)
    (hb : regsVal s (pAccs c) + (word s.mem base dx).toNat * pY s.mem base dy < 2 ^ 192) :
    WP isa (.block (pTerm c dx dy)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + (word s.mem base dx).toNat * pY s.mem base dy ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s' ∧
      (s'.gpr .rax).toNat + 2 ^ 64 * (s'.gpr .rdx).toNat = (word s.mem base dx).toNat * pY s.mem base dy := by
  have hok := pAccs_ok c
  rw [pTerm, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (pLoadY_ok hs hdy) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hacc : regsVal s₁ (pAccs c) = regsVal s (pAccs c) := regsVal_congr fun r hr => k₁.1 r (by
    have := hok.2 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    rcases this with rfl | rfl | rfl <;> decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  refine WP.mono (pMulAcc_ok hs₁ hok.1 hdx (by
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, hm₁, e₁]; exact hb))
    fun s₂ ⟨e₂, k₂, x₂⟩ => ⟨?_, ?_, ?_⟩
  · rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, hacc, hm₁, e₁] at e₂
    exact e₂
  · exact (k₁.mono (by simp)).trans (k₂.mono (by simp [pAccs]))
  · rw [x₂, hm₁, e₁]

/-- The sum of terms. -/
def pSum (m : Mem) (base : Addr) (ts : List (Nat × Option Nat)) : Nat :=
  (ts.map fun t => (word m base t.1).toNat * pY m base t.2).sum

/-- Where a term reads: in the working space. -/
def PIn (size : Nat) (t : Nat × Option Nat) : Prop := t.1 + 8 ≤ size ∧ ∀ d, t.2 = some d → d + 8 ≤ size

/-- A column's terms, by induction on them. -/
theorem pTerms_ok (c : Nat) {size : Nat} : ∀ (ts : List (Nat × Option Nat)) {s : State} {base : Addr},
    Scr s base size → (∀ t ∈ ts, PIn size t) → regsVal s (pAccs c) + pSum s.mem base ts < 2 ^ 192 →
    WP isa (.block (ts.flatMap fun t => pTerm c t.1 t.2)) s fun s' =>
      regsVal s' (pAccs c) = regsVal s (pAccs c) + pSum s.mem base ts ∧
      Keeps (.rax :: .rcx :: .rdx :: pAccs c) s s'
  | [], s, _, _, _, _ => WP.block_nil ⟨by simp [pSum], fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, hs, hin, hb => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have ht := hin t List.mem_cons_self
    simp only [pSum, List.map_cons, List.sum_cons] at hb
    refine WP.mono (pTerm_ok hs c ht.1 ht.2 (by omega)) fun s₁ ⟨e₁, k₁, _⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by have := (pAccs_ok c).2; simp only [List.mem_cons, not_or]; grind)
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    refine WP.mono (pTerms_ok c ts hs₁ (fun t' ht' => hin t' (List.mem_cons_of_mem _ ht'))
      (by rw [e₁, hm₁]; simp only [pSum] at hb ⊢; omega)) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    rw [e₂, e₁, hm₁]
    simp only [pSum, List.map_cons, List.sum_cons]
    omega

/-- A column's end: its low word stored at `t` and cleared. -/
theorem pEnd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Nat) {t : Nat}
    (ht : t + 8 ≤ size) :
    WP isa (.block [.store (sc t) (pAcc c 0), .mov32 (pAcc c 0) (.imm 0)]) s fun s' =>
      s'.mem = s.mem.writeW (off base t) (s.gpr (pAcc c 0)) ∧
      regsVal s (pAccs c) = (s.gpr (pAcc c 0)).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) ∧
      KeepRegs [pAcc c 0] s s' := by
  have hok := pAccs_ok c
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hok
  obtain ⟨⟨h01, h02, -, -, -, -⟩, ⟨h12, -, -, -, -⟩, -, -⟩ := hok.1
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, store_sc hs ht, readSrc32,
    Option.map_some, State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · rw [pAccs_succ]
    simp only [pAccs, regsVal, RegUpd.gpr_setReg, ite_true, Ne.symm h01, Ne.symm h02, ite_false,
      Nat.mul_zero, Nat.add_zero]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]

/-- Column `c`: its terms, and its low word stored at `[tmp + 8 (c mod 9)]`;
the rest of the accumulator is the next column's. -/
theorem pCol_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {a b c : Nat}
    (htmp : M.tmp + 72 ≤ size) (hin : ∀ t ∈ pTerms M a b c, PIn size t)
    (hb : regsVal s (pAccs c) + pSum s.mem base (pTerms M a b c) < 2 ^ 192) :
    WP isa (.block (pCol M a b c)) s fun s' =>
      (word s'.mem base (M.tmp + 8 * (c % 9))).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) =
        regsVal s (pAccs c) + pSum s.mem base (pTerms M a b c) ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (M.tmp + 8 * (c % 9)) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  have hc9 := Nat.mod_lt c (show 0 < 9 by decide)
  have hsub := (pAccs_ok c).2
  rw [pCol, WP.block_append_iff]
  refine WP.mono (pTerms_ok c _ hs hin hb) fun s₁ ⟨e₁, k₁⟩ => ?_
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

theorem pow64_succ' (n : Nat) : (2 ^ 64) ^ (n + 1) = 2 ^ 64 * (2 ^ 64) ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- `Σ_{j<n} 2^(64 j) f (k + j)`, in Horner form. -/
def hval (f : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, n + 1 => f k + 2 ^ 64 * hval f (k + 1) n

theorem hval_succ_last (f : Nat → Nat) : ∀ k n, hval f k (n + 1) = hval f k n + (2 ^ 64) ^ n * f (k + n)
  | k, 0 => by simp [hval]
  | k, n + 1 => by
    rw [hval, hval_succ_last f (k + 1) n, hval, pow64_succ', show k + 1 + n = k + (n + 1) by omega]
    generalize (2 ^ 64) ^ n = Q
    grind

theorem hval_congr {f g : Nat → Nat} : ∀ {k n : Nat}, (∀ c, k ≤ c → c < k + n → f c = g c) →
    hval f k n = hval g k n
  | _, 0, _ => rfl
  | k, n + 1, h => by
    rw [hval, hval, h k (Nat.le_refl _) (by omega), hval_congr fun c h1 h2 => h c (by omega) (by omega)]

theorem hval_lt {f : Nat → Nat} : ∀ {k n : Nat}, (∀ c, k ≤ c → c < k + n → f c < 2 ^ 64) →
    hval f k n < (2 ^ 64) ^ n
  | _, 0, _ => Nat.one_pos
  | k, n + 1, h => by
    rw [hval, pow64_succ']
    exact word_add_lt (h k (Nat.le_refl _) (by omega)) (hval_lt fun c h1 h2 => h c (by omega) (by omega))

theorem hval_add (f : Nat → Nat) : ∀ k n m, hval f k (n + m) = hval f k n + (2 ^ 64) ^ n * hval f (k + n) m
  | k, 0, m => by simp [hval]
  | k, n + 1, m => by
    rw [show n + 1 + m = (n + m) + 1 by omega, hval, hval_add f (k + 1) n m, hval, pow64_succ',
      show k + 1 + n = k + (n + 1) by omega]
    generalize (2 ^ 64) ^ n = Q
    grind

theorem wordsVal_hval (m : Mem) (base : Addr) (d : Nat) : ∀ k n,
    wordsVal m base (d + 8 * k) n = hval (fun j => (word m base (d + 8 * j)).toNat) k n
  | _, 0 => rfl
  | k, n + 1 => by
    rw [wordsVal, hval, show d + 8 * k + 8 = d + 8 * (k + 1) by omega, wordsVal_hval m base d (k + 1) n]

/-- Column `c`'s sum: its products `A i · B j` (`i + j = c`) and, for
`8 ≤ c ≤ 16`, `512 l_{c-8}`. -/
def pColSum (A B l : Nat → Nat) (c : Nat) : Nat :=
  (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map fun i => A i * B (c - i)).sum +
    if 8 ≤ c ∧ c ≤ 16 then l (c - 8) * 512 else 0

/-- The eighteen columns: the product, and `2⁵²¹ Σ_{k<9} 2^(64 k) l_k`. -/
theorem pColSum_total (A B l : Nat → Nat) :
    hval (pColSum A B l) 0 18 = hval A 0 9 * hval B 0 9 + 512 * (2 ^ 64) ^ 8 * hval l 0 9 := by
  simp only [hval, pColSum, List.range, List.range.loop, List.filter_cons, List.filter_nil,
    decide_eq_true_eq, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceSub, Nat.reduceAdd, and_true, and_false,
    ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.zero_add]
  generalize 2 ^ 64 = X
  grind

theorem sum_le_mul {L : List Nat} {K : Nat} (h : ∀ x ∈ L, x ≤ K) : L.sum ≤ L.length * K := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    omega

/-- A column's sum is below `10 · 2¹²⁸`, for words. -/
theorem pColSum_lt {A B l : Nat → Nat} (c : Nat) (hA : ∀ i, A i < 2 ^ 64) (hB : ∀ j, B j < 2 ^ 64)
    (hl : 8 ≤ c → c ≤ 16 → l (c - 8) < 2 ^ 64) : pColSum A B l c < 10 * 2 ^ 128 := by
  unfold pColSum
  have h1 := sum_le_mul (L := ((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map
      fun i => A i * B (c - i)) (K := 2 ^ 128) fun x hx => by
    simp only [List.mem_map] at hx
    obtain ⟨i, -, rfl⟩ := hx
    have := Nat.mul_le_mul (Nat.le_of_lt (hA i)) (Nat.le_of_lt (hB (c - i)))
    exact Nat.le_trans this (by decide)
  have h2 : (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map fun i => A i * B (c - i)).length ≤ 9 := by
    rw [List.length_map]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have h3 := Nat.mul_le_mul_right (2 ^ 128) h2
  split
  · have := hl (by omega) (by omega); omega
  · omega

/-- A column's terms' sum, from the words they read. -/
theorem pSum_pTerms {m : Mem} {base : Addr} {M : Mod} {a b c : Nat} {A B l : Nat → Nat}
    (hA : ∀ i < 9, (word m base (a + 8 * i)).toNat = A i)
    (hB : ∀ j < 9, (word m base (b + 8 * j)).toNat = B j)
    (hl : 8 ≤ c → c ≤ 16 → (word m base (M.tmp + 8 * (c - 8))).toNat = l (c - 8)) :
    pSum m base (pTerms M a b c) = pColSum A B l c := by
  simp only [pSum, pTerms, pColSum, List.map_append, List.sum_append, List.map_map]
  have e1 : (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map ((fun t : Nat × Option Nat =>
      (word m base t.1).toNat * pY m base t.2) ∘ fun i => (a + 8 * i, some (b + 8 * (c - i))))).sum =
      (((List.range 9).filter fun i => i ≤ c ∧ c - i < 9).map fun i => A i * B (c - i)).sum := by
    refine congrArg List.sum (List.map_congr_left fun i hi => ?_)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hi
    simp only [Function.comp, pY, hA i hi.1, hB (c - i) hi.2.2]
  rw [e1]
  refine congrArg (_ + ·) ?_
  split
  · rename_i h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, pY,
      hl h.1 h.2]
  · simp

/-- A family of column sums `S l c` (given the reduction's `u`s, `l`): column
`c`'s depends on `l` only at `c - 8` (for `8 ≤ c ≤ 16`), and is below
`2¹³³` if that is a word. -/
structure ColSum (S : (Nat → Nat) → Nat → Nat) : Prop where
  congr : ∀ l l' c, (8 ≤ c → c ≤ 16 → l (c - 8) = l' (c - 8)) → S l c = S l' c
  lt : ∀ l c, (8 ≤ c → c ≤ 16 → l (c - 8) < 2 ^ 64) → S l c < 2 ^ 133

/-- What column `c < 18` of a product by columns `col` does, from a state
whose memory differs from `m₀` only in the temporary area, which holds the
reduction's `u_{c-8}` (`l`): it adds its sum `S l c` to the accumulator
(below `2¹²⁸`) and stores its low word at `[tmp + 8 (c mod 9)]`. -/
def ColOk (M : Mod) (base : Addr) (size : Nat) (m₀ : Mem) (col : Nat → List Instr)
    (S : (Nat → Nat) → Nat → Nat) (P : State → Prop := fun _ => True) : Prop :=
  ∀ c < 18, ∀ (s : State) (l : Nat → Nat), Scr s base size → P s → Outside base M.tmp 72 m₀ s.mem →
    regsVal s (pAccs c) < 2 ^ 128 →
    (8 ≤ c → c ≤ 16 → (word s.mem base (M.tmp + 8 * (c - 8))).toNat = l (c - 8)) →
    WP isa (.block (col c)) s fun s' =>
      (word s'.mem base (M.tmp + 8 * (c % 9))).toNat + 2 ^ 64 * regsVal s' (pAccs (c + 1)) =
        regsVal s (pAccs c) + S l c ∧
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' ∧
      Outside base (M.tmp + 8 * (c % 9)) 8 s.mem s'.mem

/-- The first `n` columns: the low words (`l`) of those not yet overwritten in
the temporary area, and the accumulator, `hval (S l) 0 n =
hval l 0 n + 2^(64 n) acc`. -/
theorem cols_ok {s₀ : State} {base : Addr} {size : Nat} (hs : Scr s₀ base size) {M : Mod}
    {col : Nat → List Instr} {S : (Nat → Nat) → Nat → Nat} {P : State → Prop} (htmp : M.tmp + 72 ≤ size)
    (hS : ColSum S) (hcol : ColOk M base size s₀.mem col S P) (hP₀ : P s₀)
    (hP : ∀ s s', P s → KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s s' → P s')
    (h0 : regsVal s₀ (pAccs 0) = 0) :
    ∀ n ≤ 18, WP isa (.block ((List.range n).flatMap col)) s₀ fun s =>
      KeepRegs [.rax, .rcx, .rdx, .r9, .r10, .r11] s₀ s ∧ Outside base M.tmp 72 s₀.mem s.mem ∧
      regsVal s (pAccs n) < 2 ^ 128 ∧
      ∃ l : Nat → Nat, (∀ c < n, l c < 2 ^ 64) ∧
        (∀ c < n, n ≤ c + 9 → (word s.mem base (M.tmp + 8 * (c % 9))).toNat = l c) ∧
        hval (S l) 0 n = hval l 0 n + (2 ^ 64) ^ n * regsVal s (pAccs n)
  | 0, _ => WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _, by rw [h0]; decide,
      fun _ => 0, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      by simp [hval, h0]⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (cols_ok hs htmp hS hcol hP₀ hP h0 n (by omega))
      fun s ⟨k, O, hacc, l, hl64, hlm, e⟩ => ?_
    have hnw := hs.nowrap
    have hsS : Scr s base size := hs.of_keepRegs k (by decide)
    have hL : 8 ≤ n → n ≤ 16 → (word s.mem base (M.tmp + 8 * (n - 8))).toNat = l (n - 8) :=
      fun h1 h2 => by
        have := hlm (n - 8) (by omega) (by omega)
        rwa [Nat.mod_eq_of_lt (show n - 8 < 9 by omega)] at this
    have hcl := hS.lt l n fun h1 h2 => hl64 _ (by omega)
    have hn9 := Nat.mod_lt n (show 0 < 9 by decide)
    refine WP.mono (hcol n (by omega) s l hsS (hP _ _ hP₀ k) O hacc hL) fun s' ⟨e', k', O'⟩ => ?_
    refine ⟨k.trans k', O.trans (O'.mono (by omega) (by omega)), by omega,
      fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c, ?_, ?_, ?_⟩
    · intro c hc
      by_cases h : c = n
      · simp only [h, ite_true]; exact (word _ _ _).isLt
      · simp only [h, ite_false]; exact hl64 c (by omega)
    · intro c hc hc9
      by_cases h : c = n
      · subst h; simp
      · simp only [h, ite_false]
        have hc9' := Nat.mod_lt c (show 0 < 9 by decide)
        have hne : c % 9 ≠ n % 9 := by omega
        rw [O'.word (by omega) (by omega)]
        exact hlm c (by omega) (by omega)
    · rw [hval_succ_last, hval_succ_last, Nat.zero_add]
      simp only [↓reduceIte]
      have hcs : ∀ c, 0 ≤ c → c < 0 + n →
          S (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c) c = S l c :=
        fun c _ hc => hS.congr _ _ c fun _ _ => by simp only [show c - 8 ≠ n by omega, ite_false]
      have hcn : S (fun c => if c = n then (word s'.mem base (M.tmp + 8 * (n % 9))).toNat else l c) n =
          S l n := hS.congr _ _ n fun _ _ => by simp only [show n - 8 ≠ n by omega, ite_false]
      rw [hval_congr hcs, hcn, e, hval_congr (g := l) (fun c _ hc => ite_eq_right_iff.mpr (fun h => absurd h (by omega))), pow64_succ']
      rw [Nat.mul_comm (2 ^ 64) ((2 ^ 64) ^ n), Nat.mul_assoc]
      generalize (2 ^ 64) ^ n = Q
      rw [Nat.add_assoc, ← Nat.mul_add, ← e', Nat.mul_add]
      omega

/-- `mulP`'s column sums. -/
theorem colSum_p (A B : Nat → Nat) (hA : ∀ i, A i < 2 ^ 64) (hB : ∀ j, B j < 2 ^ 64) :
    ColSum (pColSum A B) where
  congr l l' c h := by
    unfold pColSum
    split
    · rename_i hc; rw [h hc.1 hc.2]
    · rfl
  lt l c h := Nat.lt_of_lt_of_le (pColSum_lt c hA hB h) (by decide)

/-- `mulP`'s columns. -/
theorem pCol_colOk {base : Addr} {size : Nat} {m₀ : Mem} {M : Mod} {a b : Nat}
    (htmp : M.tmp + 72 ≤ size) (ha : a + 72 ≤ size) (hb : b + 72 ≤ size)
    (haT : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a) (hbT : b + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ b) :
    ColOk M base size m₀ (pCol M a b)
      (pColSum (fun i => (word m₀ base (a + 8 * i)).toNat) (fun j => (word m₀ base (b + 8 * j)).toNat)) :=
  fun c hc s l hsS _ O hacc hL => by
    have hnw := hsS.nowrap
    have hA : ∀ i < 9, (word s.mem base (a + 8 * i)).toNat = (word m₀ base (a + 8 * i)).toNat :=
      fun i hi => by rw [O.word (by omega) (by omega)]
    have hB : ∀ j < 9, (word s.mem base (b + 8 * j)).toNat = (word m₀ base (b + 8 * j)).toNat :=
      fun j hj => by rw [O.word (by omega) (by omega)]
    have hsum := pSum_pTerms (M := M) (c := c) hA hB hL
    have hcol := pColSum_lt (A := fun i => (word m₀ base (a + 8 * i)).toNat)
      (B := fun j => (word m₀ base (b + 8 * j)).toNat) (l := l) c (fun i => (word _ _ _).isLt)
      (fun j => (word _ _ _).isLt) (fun h1 h2 => by rw [← hL h1 h2]; exact (word _ _ _).isLt)
    have hin : ∀ t ∈ pTerms M a b c, PIn size t := by
      intro t ht
      simp only [pTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with ⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht
      · exact ⟨by omega, fun d hd => by simp only [Option.some.injEq] at hd; omega⟩
      · split at ht
        · simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by omega, fun d hd => by simp at hd⟩
        · simp at ht
    refine WP.mono (pCol_ok hsS htmp hin (by rw [hsum]; omega)) fun s' ⟨e', k', O'⟩ =>
      ⟨by rw [e', hsum], k', O'⟩

theorem hval_shift (f : Nat → Nat) (d : Nat) : ∀ k n, hval f (k + d) n = hval (fun j => f (j + d)) k n
  | _, 0 => rfl
  | k, n + 1 => by
    rw [hval, hval, show k + d + 1 = (k + 1) + d by omega, hval_shift f d (k + 1) n]

/-- The modulus of a friendly reduction by `p521Ws` is P-521's `p = 2⁵²¹ - 1`,
with `2⁵²¹ = 512 (2⁶⁴)⁸`. -/
theorem p521_of_red {M : Mod} {m : Nat} (hred : M.red = .friendly p521Ws) (h : M.ok m = true) :
    M.n = 9 ∧ m + 1 = 512 * (2 ^ 64) ^ 8 := by
  have h' := Mod.ok_red h
  rw [hred] at h'
  simp only [Red.ok, Bool.and_eq_true, beq_iff_eq] at h'
  obtain ⟨⟨⟨hn, hm⟩, hw⟩, -⟩ := h'
  have h1 : (m + 1) % 2 ^ 64 = 0 := by omega
  have hw' : mwVal p521Ws = 2 ^ 9 * (2 ^ 64) ^ 7 := by
    simp only [mwVal, p521Ws, MWord.val, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  have h2 := Nat.div_add_mod (m + 1) (2 ^ 64)
  rw [← hw, hw', h1, Nat.add_zero] at h2
  refine ⟨by rw [← hn]; rfl, ?_⟩
  rw [← h2, Nat.pow_succ]

/-- The arithmetic of `mulP`: from the columns' value `A B + 2⁵²¹ U =
U + 2⁵⁷⁶ W + 2¹¹⁵² acc` (`X = 2⁶⁴`), the top `acc` is zero and
`2⁵⁷⁶ W = A B + U p < 2⁵⁷⁶ · 2p`. -/
theorem mulP_arith {X A B U W m acc : Nat} (hX : 1024 ≤ X) (hm : m + 1 = 512 * X ^ 8)
    (hA : A < X ^ 9) (hB : B < m) (hU : U < X ^ 9)
    (e : A * B + 512 * X ^ 8 * U = U + X ^ 9 * W + X ^ 9 * X ^ 9 * acc) :
    acc = 0 ∧ W < 2 * m ∧ X ^ 9 * W = A * B + U * m := by
  have hX9 : X ^ 9 = X * X ^ 8 := by rw [Nat.pow_succ, Nat.mul_comm]
  have hUm : U * (m + 1) = U * m + U := by rw [Nat.mul_add, Nat.mul_one]
  have eT : X ^ 9 * (W + X ^ 9 * acc) = A * B + U * m := by
    rw [hm] at hUm
    rw [Nat.mul_add, ← Nat.mul_assoc]
    have : 512 * X ^ 8 * U = U * (512 * X ^ 8) := Nat.mul_comm _ _
    omega
  have hAB : A * B < X ^ 9 * m := Nat.mul_lt_mul'' hA hB
  have hUm' : U * m < X ^ 9 * m := Nat.mul_lt_mul_of_pos_right hU (by omega)
  have hT : W + X ^ 9 * acc < 2 * m := by
    have : X ^ 9 * (W + X ^ 9 * acc) < X ^ 9 * (2 * m) := by rw [eT, Nat.mul_left_comm]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  have h2m : 2 * m < X ^ 9 := by
    have : 1024 * X ^ 8 ≤ X * X ^ 8 := Nat.mul_le_mul_right _ hX
    omega
  have hacc : acc = 0 := by
    rcases Nat.eq_zero_or_pos acc with h | h
    · exact h
    · have : X ^ 9 * 1 ≤ X ^ 9 * acc := Nat.mul_le_mul_left _ h
      omega
  rw [hacc, Nat.mul_zero, Nat.add_zero] at eT hT
  exact ⟨hacc, hT, eT⟩

/-- `[o] = A B R⁻¹ mod p` for P-521's `p`, `R = 2⁵⁷⁶`, by columns whose sums
add up to `A B` and the reduction's `2⁵²¹ U`. -/
theorem prodCols_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o : Nat}
    (ho : o + 8 * M.n ≤ size) (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o)
    (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o) {col : Nat → List Instr}
    {S : (Nat → Nat) → Nat → Nat} (hS : ColSum S) (hcol : ColOk M base size s.mem col S) {A B : Nat}
    (hA : A < 2 ^ (64 * M.n)) (hB : B < m)
    (htot : ∀ l, hval (S l) 0 18 = A * B + 512 * (2 ^ 64) ^ 8 * hval l 0 9) :
    WP isa (.block (prodCols M o col)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧ wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m = A * B % m := by
  obtain ⟨hn9, hm⟩ := p521_of_red hred hM.red
  rw [Nat.pow_mul]
  have hnw := hs.nowrap
  have hmo := hM.mo
  have htmp := hM.tmp
  have hsep := hM.sep
  rw [Nat.pow_mul, hn9] at hA
  rw [hn9] at ho hoT hoM hmo htmp hsep ⊢
  rw [prodCols, List.append_assoc, WP.block_append_iff,
    show ([.mov32 .r9 (.imm 0), .mov32 .r10 (.imm 0), .mov32 .r11 (.imm 0)] : List Instr) =
      zeros [.r9, .r10, .r11] from rfl]
  refine WP.mono (zeros_ok s [.r9, .r10, .r11]) fun s₁ ⟨z₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h0 : regsVal s₁ (pAccs 0) = 0 := by
    simp only [show pAccs 0 = [.r9, .r10, .r11] from rfl, regsVal, z₁ .r9 (by simp),
      z₁ .r10 (by simp), z₁ .r11 (by simp)]
    rfl
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (cols_ok hs₁ (M := M) (by omega) hS (by rw [hm₁]; exact hcol) trivial (fun _ _ _ _ => trivial)
    h0 18 (Nat.le_refl _))
    fun s₂ ⟨k₂, O₂, _, l, hl64, hlm, e₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- The value of the columns.
  rw [htot, hval_add l 0 9 9, Nat.zero_add,
    show (2 ^ 64) ^ 18 = (2 ^ 64) ^ 9 * (2 ^ 64) ^ 9 by rw [← Nat.pow_add]] at e₂
  have hW : wordsVal s₂.mem base M.tmp 9 = hval l 9 9 := by
    rw [show M.tmp = M.tmp + 8 * 0 from rfl, wordsVal_hval s₂.mem base M.tmp 0 9,
      show (9 : Nat) = 0 + 9 from rfl, hval_shift l 9 0 9]
    exact hval_congr fun c _ hc => by
      have := hlm (c + 9) (by omega) (by omega)
      rwa [show (c + 9) % 9 = c by omega] at this
  have hU : hval l 0 9 < (2 ^ 64) ^ 9 := hval_lt fun c _ hc => hl64 c (by omega)
  rw [← hW, show pAccs 18 = [.r9, .r10, .r11] from rfl] at e₂
  obtain ⟨hacc0, hT2, eT⟩ := mulP_arith (by decide) hm hA hB hU e₂
  have hr9 : (s₂.gpr .r9).toNat = 0 := by simp only [regsVal] at hacc0; omega
  have hmo₂ : wordsVal s₂.mem base M.mo 9 = m := by
    rw [O₂.wordsVal (by omega) (by omega), hm₁, ← hn9, hM.val]
  refine WP.mono (csubW_ok hs₂ (M := M) (o := o) (m := m) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by rw [hn9]; exact hmo₂)
    (by rw [hr9, Nat.mul_zero, Nat.add_zero, hn9]; exact hT2)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hr9, Nat.mul_zero, Nat.add_zero, hn9] at e₃
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx hx' => ?_⟩, ?_, ?_⟩
  · have hcl : ∀ q ∈ [Reg.rax, .rcx, .rdx, .r8, .r9, .r10, .r11], q ∈ clob M.n := by
      rw [hn9]; decide
    rw [k₃.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₂.gpr r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind))),
      k₁.1 r (fun h => hr (hcl r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)))]
  · rw [k₃.rd, k₂.rd, k₁.2.2.1]
  · rw [k₃.wr, k₂.wr, k₁.2.2.2]
  · rw [O₃ x (by omega), O₂ x (by omega), hm₁]
  · rw [e₃]; exact Nat.mod_lt _ (m_pos hB)
  · rw [e₃, Nat.mod_mul_mod, Nat.mul_comm, eT]
    simp only [Nat.add_mul_mod_self_right]

/-- `[o] = [a] [b] R⁻¹ mod p` for P-521's `p`, `R = 2⁵⁷⁶`. -/
theorem mulP_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hM : ModOkW M size m s.mem base) (hred : M.red = .friendly p521Ws) {o a b : Nat}
    (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hoT : o + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ o) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b) (hoM : o + 8 * M.n ≤ M.mo ∨ M.mo + 8 * M.n ≤ o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (mulP M o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n < m ∧
      wordsVal s'.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have hn9 := (p521_of_red hred hM.red).1
  have htmp := hM.tmp
  rw [hn9] at ha hb haT hbT htmp
  have hv : ∀ x, wordsVal s.mem base x M.n = hval (fun i => (word s.mem base (x + 8 * i)).toNat) 0 9 := fun x => by
    rw [hn9, ← wordsVal_hval s.mem base x 0 9, Nat.mul_zero, Nat.add_zero]
  rw [mulP, hv a, hv b]
  exact prodCols_ok hs hM hred ho hoT hoM (colSum_p _ _ (fun _ => (word _ _ _).isLt) (fun _ => (word _ _ _).isLt))
    (pCol_colOk (by omega) (by omega) (by omega) (by omega) (by omega)) (by rw [← hv a]; exact wordsVal_lt _ _ _ _)
    (by rw [← hv b]; exact hB) fun l => pColSum_total _ _ l

end VG.Proof.Mont.X86_64
