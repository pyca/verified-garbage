module

public import VerifiedGarbage.Proof.Mont.X86_64.OpsReg
import VerifiedGarbage.Proof.Mont.X86_64.CsubS
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86_64.MulPX
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Mont.X86_64.MulP
import Batteries.Logic

/-! ### `Mont.X86_64.SqrP`, which the modules that import this one used -/

section

/-!
# Montgomery arithmetic on x86-64: P-521's square by columns

`sqrP o a` (`Impl/Mont/X86_64.lean`) is `mulP o a a` with each product of
two different words computed once and added twice: a term adds its product
once or twice (`sTerm_ok`, the second time `rdx:rax` again, `sAdd_ok`), a
column its terms (`sCol_ok`), whose sums over the eighteen columns are
`a²` and the reduction's `2⁵²¹ U` (`sColSum_total`), so that `prodCols_ok`
gives `sqrP_ok`.
-/

@[expose] public section

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
    rcases Nat.lt_or_ge c2.toNat 1 with h | h <;> omega_arith
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
  refine WP.mono (pTerm_ok hs c hdx hdy (by cases two <;> simp only [mult, Bool.false_eq_true, ↓reduceIte] at hb <;> omega_arith))
    fun s₁ ⟨e₁, k₁, x₁⟩ => ?_
  cases two with
  | false => exact WP.block_nil ⟨by rw [e₁]; simp [mult], k₁⟩
  | true =>
    simp only [ite_true]
    have hok := pAccs_ok c
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    refine WP.mono (sAdd_ok s₁ hok.1 (by
      rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₁, x₁]
      simp only [mult, ↓reduceIte] at hb; omega_arith)) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans (k₂.mono (by simp [pAccs]))⟩
    rw [show [pAcc c 0, pAcc c 1, pAcc c 2] = pAccs c from rfl, e₁, x₁] at e₂
    rw [e₂]; simp only [mult, ↓reduceIte]; omega_arith

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
    refine WP.mono (sTerm_ok hs c (dx := t.1) (dy := t.2.1) ht.1 ht.2 t.2.2 (by omega_arith)) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by have := (pAccs_ok c).2; simp only [List.mem_cons, not_or]; grind)
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    refine WP.mono (sTerms_ok c ts hs₁ (fun t' ht' => hin t' (List.mem_cons_of_mem _ ht'))
      (by rw [e₁, hm₁]; simp only [sSum] at hb ⊢; omega_arith)) fun s₂ ⟨e₂, k₂⟩ => ⟨?_, k₁.trans k₂⟩
    rw [e₂, e₁, hm₁]
    simp only [sSum, List.map_cons, List.sum_cons]
    omega_arith

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
  refine WP.mono (pEnd_ok hs₁ c (t := M.tmp + 8 * (c % 9)) (by omega_arith)) fun s₂ ⟨m₂, e₂, k₂⟩ => ?_
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
  · rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega_arith)

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
      Nat.mul_le_mul (by have := hA i; omega_arith) (by have := hA j; omega_arith)
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
      · rename_i hc; have := h hc.1 hc.2; omega_arith
      · omega_arith
    have : 9 * (2 * ((2 ^ 64 - 1) * (2 ^ 64 - 1))) + (2 ^ 64 - 1) * (2 ^ 64 - 1) + 2 ^ 64 * 512 ≤ 2 ^ 133 := by
      decide
    omega_arith

/-- `sqrP`'s columns. -/
theorem sCol_colOk {base : Addr} {size : Nat} {m₀ : Mem} {M : Mod} {a : Nat}
    (htmp : M.tmp + 72 ≤ size) (ha : a + 72 ≤ size) (haT : a + 72 ≤ M.tmp ∨ M.tmp + 72 ≤ a) :
    ColOk M base size m₀ (sCol M a) (sColSum fun i => (word m₀ base (a + 8 * i)).toNat) :=
  fun c hc s l hsS _ O hacc hL => by
    have hnw := hsS.nowrap
    have hA : ∀ i < 9, (word s.mem base (a + 8 * i)).toNat = (word m₀ base (a + 8 * i)).toNat :=
      fun i hi => by rw [O.word (by omega_arith) (by omega_arith)]
    have hsum := sSum_sTerms (M := M) (c := c) hA hL
    have hcol := (colSum_s (fun i => (word m₀ base (a + 8 * i)).toNat) (fun _ => (word _ _ _).isLt)).lt l c
      fun h1 h2 => by rw [← hL h1 h2]; exact (word _ _ _).isLt
    have hin : ∀ t ∈ sTerms M a c, PIn size (t.1, t.2.1) := by
      intro t ht
      simp only [sTerms, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq] at ht
      rcases ht with (⟨i, ⟨hi, -, hj⟩, rfl⟩ | ht) | ht
      · exact ⟨by omega_arith, fun d hd => by simp only [Option.some.injEq] at hd; omega_arith⟩
      · split at ht
        · rename_i h
          simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by omega_arith, fun d hd => by simp only [Option.some.injEq] at hd; omega_arith⟩
        · simp at ht
      · split at ht
        · simp only [List.mem_singleton] at ht
          subst ht
          exact ⟨by omega_arith, fun d hd => by simp at hd⟩
        · simp at ht
    refine WP.mono (sCol_ok hsS htmp hin (by rw [hsum]; omega_arith)) fun s' ⟨e', k', O'⟩ =>
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
    (sCol_colOk (by omega_arith) (by omega_arith) (by omega_arith)) (by rw [← hv]; exact wordsVal_lt _ _ _ _)
    (by rw [← hv]; exact hB) fun l => sColSum_total _ l

end VG.Proof.Mont.X86_64

end

end

/-! ### `Mont.X86_64.AddSubP`, which the modules that import this one used -/

section

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

@[expose] public section

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry sub_borrow sbb_borrow)

/-- `loads_ok` for `FreshX` registers. -/
theorem loadsX_ok {size c₀ : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {a : Nat},
    ScrC s base size c₀ → a + 8 * ts.length ≤ size → FreshX ts →
    WP isa (.block (loadsC c₀ ts a)) s fun s' =>
      regsVal s' ts = wordsVal s.mem base a ts.length ∧ Keeps ts s s'
  | [], s, _, _, _, _, _ => WP.block_nil ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, a, hs, ha, hf => by
    simp only [List.length_cons] at ha
    rw [loadsC, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov t (.mem (rc c₀ a))]) s
        (fun s₁ => s₁.gpr t = word s.mem base a ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_rc hs (d := a) (by omega_arith),
        Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
    refine WP.mono (loadsX_ok ts hs₁ (a := a + 8) (by omega_arith) hf.tail) fun s₂ ⟨e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    rw [List.length_cons, regsVal, wordsVal, ht, e₁, e₂, k₁.2.1]

/-- `chainAdc_ok` for `FreshX` registers. -/
theorem chainAdcX_ok {size c₀ : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat} {c : Bool},
    ScrC s base size c₀ → s.cf = some c → b + 8 * ts.length ≤ size → FreshX ts →
    WP isa (.block (chainC c₀ .adc .adc ts b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + 2 ^ (64 * ts.length) * c'.toNat =
        regsVal s ts + wordsVal s.mem base b ts.length + c.toNat ∧ Keeps ts s s'
  | [], s, _, _, c, _, hc, _, _ => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, c, hs, hc, hb, hf => by
    simp only [List.length_cons] at hb
    rw [chainC, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .adc t (.mem (rc c₀ b))]) s (fun s₁ =>
        (s₁.gpr t).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat +
          c.toNat)).toNat = (s.gpr t).toNat + (word s.mem base b).toNat + c.toNat ∧
        s₁.cf = some (decide (2 ^ 64 ≤ (s.gpr t).toNat + (word s.mem base b).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc_rc hs (d := b) (by omega_arith), Option.bind_some, Option.map_some, hc, RegUpd.gpr_setReg,
        RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨adc_carry _ _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
    refine WP.mono (chainAdcX_ok ts hs₁ c₁ (b := b + 8) (by omega_arith) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR, k₁.2.1] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega_arith

/-- `chainSbb_ok` for `FreshX` registers. -/
theorem chainSbbX_ok {size c₀ : Nat} : ∀ (ts : List Reg) {s : State} {base : Addr} {b : Nat} {c : Bool},
    ScrC s base size c₀ → s.cf = some c → b + 8 * ts.length ≤ size → FreshX ts →
    WP isa (.block (chainC c₀ .sbb .sbb ts b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' ts + wordsVal s.mem base b ts.length + c.toNat =
        regsVal s ts + 2 ^ (64 * ts.length) * c'.toNat ∧ Keeps ts s s'
  | [], s, _, _, c, _, hc, _, _ => WP.block_nil ⟨c, hc, by simp [regsVal, wordsVal],
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts, s, base, b, c, hs, hc, hb, hf => by
    simp only [List.length_cons] at hb
    rw [chainC, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.alu .sbb t (.mem (rc c₀ b))]) s (fun s₁ =>
        (s₁.gpr t).toNat + (word s.mem base b).toNat + c.toNat = (s.gpr t).toNat +
          2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base b).toNat + c.toNat)).toNat ∧
        s₁.cf = some (decide ((s.gpr t).toNat < (word s.mem base b).toNat + c.toNat)) ∧
        Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
        readSrc_rc hs (d := b) (by omega_arith), Option.bind_some, Option.map_some, hc, RegUpd.gpr_setReg,
        RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨?_, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
      · have := sbb_borrow (s.gpr t) (word s.mem base b) c
        omega_arith
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
    refine WP.mono (chainSbbX_ok ts hs₁ c₁ (b := b + 8) (by omega_arith) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
    have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
    have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
    rw [hR, k₁.2.1] at e₂
    refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    simp only [regsVal, wordsVal, List.length_cons, pow64_succ, ht]
    rw [Nat.mul_assoc]
    omega_arith

/-- `chainSub_ok` for `FreshX` registers. -/
theorem chainSubX_ok {s : State} {base : Addr} {size c₀ : Nat} (hs : ScrC s base size c₀) {t : Reg}
    {ts : List Reg} {b : Nat} (hb : b + 8 * (t :: ts).length ≤ size) (hf : FreshX (t :: ts)) :
    WP isa (.block (chainC c₀ .sub .sbb (t :: ts) b)) s fun s' => ∃ c' : Bool, s'.cf = some c' ∧
      regsVal s' (t :: ts) + wordsVal s.mem base b (t :: ts).length =
        regsVal s (t :: ts) + 2 ^ (64 * (t :: ts).length) * c'.toNat ∧ Keeps (t :: ts) s s' := by
  simp only [List.length_cons] at hb ⊢
  rw [chainC, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.alu .sub t (.mem (rc c₀ b))]) s (fun s₁ =>
      (s₁.gpr t).toNat + (word s.mem base b).toNat = (s.gpr t).toNat +
        2 ^ 64 * (decide ((s.gpr t).toNat < (word s.mem base b).toNat)).toNat ∧
      s₁.cf = some (decide ((s.gpr t).toNat < (word s.mem base b).toNat)) ∧
      Keeps [t] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc_rc hs (d := b) (by omega_arith), Option.bind_some, RegUpd.gpr_setReg,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨sub_borrow _ _, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.2.2.2.2 h.symm)
  refine WP.mono (chainSbbX_ok ts hs₁ c₁ (b := b + 8) (by omega_arith) hf.tail) fun s₂ ⟨c', c₂, e₂, k₂⟩ => ?_
  have ht : s₂.gpr t = s₁.gpr t := k₂.1 t hf.head.1
  have hR : regsVal s₁ ts = regsVal s ts := regsVal_congr fun q hq => k₁.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun h => hf.head.1 (h ▸ hq))
  rw [hR, k₁.2.1] at e₂
  refine ⟨c', c₂, ?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  simp only [regsVal, wordsVal, pow64_succ, ht]
  rw [Nat.mul_assoc]
  omega_arith

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
  rw [addMer]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rdiAdd_ok hs (cOf_lt a)) fun s₀ ⟨hs₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadsX_ok (xWin 9) hs₀ (a := a) (by simp [xWin]; omega_arith) (xWin_fresh 9))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [WP.block_append_iff]
  refine WP.mono (rdiMove_ok hs₁ (cOf_lt a) (cOf_lt b)) fun s₁' ⟨hs₁', k₁'⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setCF_ok s₁') fun s₂ ⟨c₂, _, k₂⟩ => ?_
  have hs₂ := hs₁'.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainAdcX_ok (xWin 9) hs₂ c₂ (b := b) (by simp [xWin]; omega_arith) (xWin_fresh 9))
    fun s₃ ⟨c₃, _, e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  have hR₂ : regsVal s₂ (xWin 9) = regsVal s₁ (xWin 9) := regsVal_congr fun q hq => by
    rw [k₂.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (xWin_fresh 9).2 q hq |>.1 h), k₁'.1 q (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact fun h => (xWin_fresh 9).2 q hq |>.2.2.2 h)]
  rw [Nat.pow_mul, show (xWin 9).length = 9 from rfl, hR₂, e₁, k₂.2.1, k₁'.2.1, k₁.2.1, k₀.2.1] at e₃
  rw [show (xWin 9).length = 9 from rfl] at e₃
  simp only [Bool.toNat_true] at e₃
  have hc := Bool.toNat_le c₃
  rw [WP.block_append_iff]
  refine WP.mono (rdiMove_ok hs₃ (cOf_lt b) (cOf_lt o)) fun s₃' ⟨hs₃', k₃'⟩ => ?_
  have hT : hval (xg s₃') 9 9 = wordsVal s.mem base a 9 + wordsVal s.mem base b 9 + 1 := by
    rw [show hval (xg s₃') 9 9 = hval (xg s₃) 9 9 from hval_congr fun c _ _ => by
      simp only [xg]; rw [k₃'.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]]
    rw [← regsVal_xWin]
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (xCanon_ok hs₃' (o := o) ho hm (by rw [hT]; omega_arith) (by rw [hT]; omega_arith))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  refine WP.mono (rdiSub_ok (hs₃'.of_keepRegs k₄ (by decide)) (cOf_lt o)) fun s₅ ⟨hs₅, k₅⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · obtain ⟨ra, hw, hr'⟩ := xWin_clob hr hn9
    by_cases hrd : r = .rdi
    · rw [hrd, hs₅.rdi, hs.rdi]
    · have hd : r ∉ [Reg.rdi] := by simpa using hrd
      rw [k₅.1 r hd, k₄.gpr r hr', k₃'.1 r hd, k₃.1 r hw, k₂.1 r (by simpa using ra), k₁'.1 r hd,
        k₁.1 r hw, k₀.1 r hd]
  · rw [k₅.2.2.1, k₄.rd, k₃'.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁'.2.2.1, k₁.2.2.1, k₀.2.2.1]
  · rw [k₅.2.2.2, k₄.wr, k₃'.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁'.2.2.2, k₁.2.2.2, k₀.2.2.2]
  · rw [hn9] at hx
    rw [k₅.2.1, O₄ x hx, k₃'.2.1, k₃.2.1, k₂.2.1, k₁'.2.1, k₁.2.1, k₀.2.1]
  · rw [k₅.2.1, e₄, hT, Nat.add_sub_cancel]

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
  rw [subMer]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rdiAdd_ok hs (cOf_lt a)) fun s₀ ⟨hs₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadsX_ok (xWin 9) hs₀ (a := a) (by simp [xWin]; omega_arith) (xWin_fresh 9))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs₀.of_keeps k₁ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [WP.block_append_iff]
  refine WP.mono (rdiMove_ok hs₁ (cOf_lt a) (cOf_lt b)) fun s₁' ⟨hs₁', k₁'⟩ => ?_
  have hR₁ : regsVal s₁' (xWin 9) = regsVal s₁ (xWin 9) := regsVal_congr fun q hq => k₁'.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => (xWin_fresh 9).2 q hq |>.2.2.2 h)
  rw [WP.block_append_iff, xWin9]
  refine WP.mono (chainSubX_ok hs₁' (b := b) (by simp [xHi]; omega_arith) (xWin_fresh 9))
    fun s₂ ⟨c₂, _, e₂, k₂⟩ => ?_
  rw [← xWin9] at e₂ k₂
  have hs₂ := hs₁'.of_keeps k₂ (fun h => by
    have := xWin_sub 9 .rdi h
    simp [xRegs] at this)
  rw [hR₁, e₁, k₁'.2.1, k₁.2.1, k₀.2.1, Nat.pow_mul, show (xWin 9).length = 9 from rfl] at e₂
  rw [WP.block_append_iff]
  refine WP.mono (add512_ok s₂ (xAcc 17)) fun s₃ ⟨c₃, e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by simpa using (xAcc_ne 17).2.2.2.1.symm)
  -- `[a] - [b] + 2⁵²¹` in the registers.
  have hlo : hval (xg s₃) 9 8 = hval (xg s₂) 9 8 := hval_congr fun c h1 h2 => by
    simp only [xg]
    rw [k₃.1 _ (by simpa using xAcc_ne_of (show c < 17 by omega_arith) (by omega_arith))]
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
    have hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega_arith
    subst hm'
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (rdiMove_ok hs₃ (cOf_lt b) (cOf_lt o)) fun s₃' ⟨hs₃', k₃'⟩ => ?_
  have hx₃ : hval (xg s₃') 9 9 = hval (xg s₃) 9 9 := hval_congr fun c _ _ => by
    simp only [xg]; rw [k₃'.1 _ (by simpa using (xAcc_ne c).2.2.2.1)]
  rw [← hx₃] at hD
  rw [WP.block_append_iff]
  refine WP.mono (xCanon_ok hs₃' (o := o) ho hm (by rw [hD]; omega_arith) (by rw [hD]; omega_arith))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  refine WP.mono (rdiSub_ok (hs₃'.of_keepRegs k₄ (by decide)) (cOf_lt o)) fun s₅ ⟨hs₅, k₅⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · obtain ⟨_, hw, hr'⟩ := xWin_clob hr hn9
    have h17 : r ≠ xAcc 17 := fun h => hw (h ▸ by decide)
    by_cases hrd : r = .rdi
    · rw [hrd, hs₅.rdi, hs.rdi]
    · have hd : r ∉ [Reg.rdi] := by simpa using hrd
      rw [k₅.1 r hd, k₄.gpr r hr', k₃'.1 r hd, k₃.1 r (by simpa using h17), k₂.1 r hw, k₁'.1 r hd,
        k₁.1 r hw, k₀.1 r hd]
  · rw [k₅.2.2.1, k₄.rd, k₃'.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁'.2.2.1, k₁.2.2.1, k₀.2.2.1]
  · rw [k₅.2.2.2, k₄.wr, k₃'.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁'.2.2.2, k₁.2.2.2, k₀.2.2.2]
  · rw [hn9] at hx
    rw [k₅.2.1, O₄ x hx, k₃'.2.1, k₃.2.1, k₂.2.1, k₁'.2.1, k₁.2.1, k₀.2.1]
  · rw [k₅.2.1, e₄, hD, show wordsVal s.mem base a 9 + m + 1 - wordsVal s.mem base b 9 - 1 =
      wordsVal s.mem base a 9 + m - wordsVal s.mem base b 9 by omega_arith]

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
    omega_arith

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
    omega_arith
  · rw [ht]; omega_arith

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
  have hm' : m = 512 * (2 ^ 64) ^ 8 - 1 := by omega_arith
  subst hm'
  have hc0 : c₂ = 0 := by omega_arith
  subst hc0
  have h17 : x17 < 1024 := by omega_arith
  by_cases hlt : x17 < 512
  · rw [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt] at *
    rw [Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [show x17 / 512 = 1 by omega_arith] at e₄
    rw [show x17 % 512 = x17 - 512 by omega_arith, Nat.mod_eq_sub_mod (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith

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
  rw [dblMer]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (rdiAdd_ok hs (cOf_lt a)) fun s₀ ⟨hs₀, k₀⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadsX_ok (xWin 9) hs₀ (a := a) (by simp [xWin]; omega_arith) (xWin_fresh 9))
    fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [k₀.2.1] at e₁
  rw [WP.block_append_iff, xWin9]
  refine WP.mono (dblChainX_ok (s := s₁) (xWin_fresh 9)) fun s₂ ⟨c₂, e₂, ev₂, k₂⟩ => ?_
  rw [← xWin9] at e₂ k₂
  rw [e₁, Nat.pow_mul, show (xWin 9).length = 9 from rfl] at e₂
  rw [← List.append_assoc, show ([.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9, .alu .add (xAcc 9) (.reg .rax),
      .alu .and (xAcc 17) (.imm 511)] : List Instr) = [.mov .rax (.reg (xAcc 17)), .shift .shr .rax 9] ++
      ([.alu .add (xAcc 9) (.reg .rax)] : List Instr) ++ [.alu .and (xAcc 17) (.imm 511)] from rfl,
    List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (top_ok s₂ (xAcc 17)) fun s₃ ⟨e₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addRax_ok s₃ (xAcc 9)) fun s₄ ⟨c₄, e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (and511_ok s₄ (xAcc 17)) fun s₅ ⟨e₅, k₅⟩ => ?_
  have hK : Keeps (.rax :: xRegs) s₀ s₅ := by
    refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
    · have hw : r ∉ xWin 9 := fun h => hr (List.mem_cons_of_mem _ (xWin_sub 9 r h))
      rw [k₅.1 r (fun h => hw ((List.mem_singleton.mp h) ▸ by decide)),
        k₄.1 r (fun h => hw ((List.mem_singleton.mp h) ▸ by decide)),
        k₃.1 r (fun h => hr (by simp at h; simp [h])), k₂.1 r hw, k₁.1 r hw]
    · rw [k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
    · rw [k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
    · rw [k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  have hs₅ := hs₀.of_keeps hK (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (rdiMove_ok hs₅ (cOf_lt a) (cOf_lt o)) fun s₅' ⟨hs₅', k₅'⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (storesC_ok (xWin 9) hs₅' (o := o) (by simp [xWin]; omega_arith) (xWin_fresh 9).1)
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  refine WP.mono (rdiSub_ok (hs₅'.of_keepRegs k₆ (by decide)) (cOf_lt o)) fun s₇ ⟨hs₇, k₇⟩ => ?_
  have hR₅ : regsVal s₅' (xWin 9) = regsVal s₅ (xWin 9) := regsVal_congr fun q hq => k₅'.1 q (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact fun h => (xWin_fresh 9).2 q hq |>.2.2.2 h)
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · by_cases hrd : r = .rdi
    · rw [hrd, hs₇.rdi, hs.rdi]
    · have hd : r ∉ [Reg.rdi] := by simpa using hrd
      rw [k₇.1 r hd, k₆.gpr r (by simp), k₅'.1 r hd, hK.1 r (xWin_clob hr hn9).2.2, k₀.1 r hd]
  · rw [k₇.2.2.1, k₆.rd, k₅'.2.2.1, hK.2.2.1, k₀.2.2.1]
  · rw [k₇.2.2.2, k₆.wr, k₅'.2.2.2, hK.2.2.2, k₀.2.2.2]
  · rw [hn9] at hx
    rw [k₇.2.1, O₆ x (by rw [show (xWin 9).length = 9 from rfl]; exact hx), k₅'.2.1, hK.2.1, k₀.2.1]
  · rw [show (xWin 9).length = 9 from rfl] at e₆
    rw [k₇.2.1, e₆, hR₅, regsVal_xWin]
    rw [regsVal_xWin] at e₂
    have n17 : ∀ c, 10 ≤ c → c < 17 → xAcc c ≠ xAcc 17 := fun c h1 h2 => xAcc_ne_of (by omega_arith) (by omega_arith)
    have n9 : ∀ c, 10 ≤ c → c < 18 → xAcc c ≠ xAcc 9 := fun c h1 h2 =>
      (xAcc_ne_of (show 9 < c by omega_arith) (by omega_arith)).symm
    have hL : hval (xg s₅) 10 7 = hval (xg s₂) 10 7 := hval_congr fun c h1 h2 => by
      simp only [xg]
      rw [k₅.1 _ (by simpa using n17 c h1 (by omega_arith)), k₄.1 _ (by simpa using n9 c h1 (by omega_arith)),
        k₃.1 _ (by simpa using (xAcc_ne c).1)]
    have h₅ : hval (xg s₅) 9 9 = xg s₅ 9 + 2 ^ 64 * (hval (xg s₅) 10 7 + (2 ^ 64) ^ 7 * xg s₅ 17) := by
      rw [← hval_succ_last]; rfl
    have h₂ : hval (xg s₂) 9 9 = xg s₂ 9 + 2 ^ 64 * (hval (xg s₂) 10 7 + (2 ^ 64) ^ 7 * xg s₂ 17) := by
      rw [← hval_succ_last]; rfl
    have a₃ : xg s₃ 9 = xg s₂ 9 := by simp only [xg]; rw [k₃.1 _ (by simpa using (xAcc_ne 9).1)]
    have b₄ : xg s₄ 17 = xg s₂ 17 := by
      simp only [xg]
      rw [k₄.1 _ (by simpa using (xAcc_ne_of (show 9 < 17 by omega_arith) (by omega_arith)).symm),
        k₃.1 _ (by simpa using (xAcc_ne 17).1)]
    have a₅ : xg s₅ 9 = xg s₄ 9 := by
      simp only [xg]; rw [k₅.1 _ (by simpa using (xAcc_ne_of (show 9 < 17 by omega_arith) (by omega_arith)))]
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

end

end

/-!
# P-384 field subtraction on x86-64

The difference of six words, and P-384's `p` masked by its borrow added back,
the mask's words in `rcx`, `rdx`, `rbp` and `rax` (`p384Mask_ok`,
`p384Add_ok`): no temporary memory is written. The inputs may alias the
output.
-/

@[expose] public section

namespace VG.Proof.Mont.X86_64
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- Subtraction modulo P-384's `p`. -/
theorem sub384_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m : Nat}
    (hn6 : M.n = 6)
    (hm : m =
      39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
    {o a b : Nat} (ho : o + 8 * M.n ≤ size) (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size)
    (hA : wordsVal s.mem base a M.n < m) (hB : wordsVal s.mem base b M.n < m) :
    WP isa (.block (sub384 o a b)) s fun s' => OpKeep M base o s s' ∧
      wordsVal s'.mem base o M.n = (wordsVal s.mem base a M.n + m - wordsVal s.mem base b M.n) % m := by
  simp only [hn6] at ho ha hb hA hB ⊢
  have hf : Fresh (low 6) := (fresh_top_low (n := 6) (by decide)).tail
  have hl : (low 6).length = 6 := rfl
  have hsub : ∀ r ∈ low 6, r ∈ clob M.n := by rw [hn6]; decide
  have hW : 2 ^ (64 * 6) = 2 ^ 128 * 2 ^ 256 :=
    calc 2 ^ (64 * 6) = 2 ^ (128 + 256) := congrArg (2 ^ ·) rfl
      _ = 2 ^ 128 * 2 ^ 256 := Nat.pow_add 2 128 256
  rw [sub384, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loads_ok (low 6) hs (a := a) (by simpa only [hl] using ha) hf)
    fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (chainSub_ok hs₁ (t := .r8) (ts := [.r9, .r10, .r11, .r12, .r13]) (b := b) hb hf)
    fun s₂ ⟨c, c₂, e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₂ c₂) fun s₃ ⟨x₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p384Mask_ok s₃ c x₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (p384Add_ok s₄ hl hf) fun s₅ ⟨c', _, e₅, k₅⟩ => ?_
  have hs₅ := ((hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  refine WP.mono (stores_ok (low 6) hs₅ (o := o) (by simpa only [hl] using ho) hf.1)
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [hl] at e₁ e₆ O₆
  have hR₄ : regsVal s₄ (low 6) = regsVal s₂ (low 6) := by
    apply regsVal_congr
    intro r hr
    rw [k₄.1 r (by revert r; decide), k₃.1 r (by revert r; decide)]
  rw [hR₄, e₄, ← hm] at e₅
  have hlow : low 6 = [.r8, .r9, .r10, .r11, .r12, .r13] := rfl
  rw [← hlow, hl, e₁, k₁.2.1, hW] at e₂
  refine ⟨⟨fun r hr => ?_, ?_, ?_, fun x hx _ => ?_⟩, ?_⟩
  · have hr' : r ∉ low 6 := fun h => hr (hsub r h)
    have h4 : r ∉ [.rcx, .rdx, .rbp] := by
      intro h; apply hr; rw [hn6]
      exact (by decide : ∀ r : Reg, r ∈ [.rcx, .rdx, .rbp] → r ∈ clob 6) r h
    have h3 : r ∉ [.rax] := by
      intro h; apply hr; rw [hn6]
      exact (by decide : ∀ r : Reg, r ∈ [.rax] → r ∈ clob 6) r h
    rw [k₆.gpr r (by simp), k₅.1 r hr', k₄.1 r h4, k₃.1 r h3, k₂.1 r hr', k₁.1 r hr']
  · rw [k₆.rd, k₅.2.2.1, k₄.2.2.1, k₃.2.2.1, k₂.2.2.1, k₁.2.2.1]
  · rw [k₆.wr, k₅.2.2.2, k₄.2.2.2, k₃.2.2.2, k₂.2.2.2, k₁.2.2.2]
  · rw [O₆ x (by simpa only [hn6] using hx), k₅.2.1, k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  · rw [e₆]
    have hR₂ := regsVal_lt s₂ (low 6)
    have hR₅ := regsVal_lt s₅ (low 6)
    rw [hl, hW] at hR₂ hR₅
    subst hm
    cases c <;> cases c' <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero,
      Nat.mul_one, Nat.add_zero, Bool.false_eq_true, ite_false, ite_true] at e₂ e₅ <;> omega_arith

end VG.Proof.Mont.X86_64
