module

import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Mont.AArch64.Row
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product

/-! ### `Mont.AArch64.P384Sqr.Rows`, which this module and modules that import it used -/

section

/-!
# P-384's Montgomery square on AArch64: the products of distinct words

`offDiag` (`Impl/Mont/AArch64/P384Sqr.lean`) clears the accumulator and runs
a `row` for each word `a_i`, `i < 5`, adding `2^(64 (2i + 1)) a_i [a_(i+1) … a_5]`
(`sqRow_ok`, one symbolic execution for any `i`), so that the accumulator holds
`odd [a]`, the sum of `2^(64 (i + j)) a_i a_j` over `i < j` (`offDiag_ok`).
-/

@[expose] public section

-- Powers of two up to `2^768` (the accumulator) are evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Mont.AArch64.P384Sqr

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P384Sqr VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P384Mul (rwVal_regs)
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)

/-- `[a]`'s words after word `i`, as a row multiplies by them. -/
abbrev sqWords (i : Nat) : List RWord := (aRegs.drop (i + 1)).map fun r => .gen (.reg r)

/-- The multiplier of row `i`. -/
abbrev sqX (i : Nat) : Reg := aRegs.getD i .x4

/-- What row `i` needs of its registers. -/
theorem sqRow_facts : ∀ i < 5, (P384Mul.accRegs.take (2 * i + 1)).length = 2 * i + 1 ∧
    (sqRowRegs i).length = 6 - i ∧ (aRegs.drop (i + 1)).length = 5 - i ∧
    P384Mul.accRegs = P384Mul.accRegs.take (2 * i + 1) ++ (sqRowRegs i ++ P384Mul.accRegs.drop (7 + i)) ∧
    (sqRowRegs i).Nodup ∧
    (∀ t ∈ sqRowRegs i, t ≠ .x0 ∧ t ≠ .x2 ∧ t ≠ .x3 ∧ t ≠ .x7 ∧ t ≠ sqX i) ∧
    (∀ r ∈ aRegs.drop (i + 1), r ∉ sqRowRegs i ∧ r ≠ .x2 ∧ r ≠ .x3) ∧
    sqX i ≠ .x2 ∧ sqX i ≠ .x3 ∧
    Reg.x7 ∉ Reg.x2 :: .x3 :: sqRowRegs i ∧ sqX i ∉ Reg.x2 :: .x3 :: sqRowRegs i ∧
    (∀ r ∈ aRegs, r ∉ Reg.x2 :: .x3 :: sqRowRegs i) ∧
    (∀ r ∈ P384Mul.accRegs.take (2 * i + 1), r ∉ Reg.x2 :: .x3 :: sqRowRegs i) ∧
    (∀ r ∈ P384Mul.accRegs.drop (7 + i), r ∉ Reg.x2 :: .x3 :: sqRowRegs i) ∧
    (∀ r ∈ Reg.x2 :: .x3 :: sqRowRegs i, r ∈ Reg.x2 :: .x3 :: P384Mul.accRegs) := by
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem sqRowOk {size i : Nat} (hi : i < 5) : RowOk size (sqX i) (sqRowRegs i) (sqWords i) := by
  obtain ⟨-, -, -, -, hnd, hregs, hrd, hx2, hx3, -⟩ := sqRow_facts i hi
  have hw : ∀ w ∈ sqWords i, ∃ r ∈ aRegs.drop (i + 1), w = .gen (.reg r) := fun w hw => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
    exact ⟨r, hr, rfl⟩
  refine ⟨hnd, hregs, fun w h => ?_, fun w h q hq => ?_, hx2, hx3⟩
  · obtain ⟨r, hr, rfl⟩ := hw w h
    exact ⟨(hrd r hr).2.1, (hrd r hr).2.2⟩
  · obtain ⟨r, hr, rfl⟩ := hw w h
    simp only [RWord.reads, Src.reads, Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hrd _ hr

/-- What the rows need of their base register. -/
abbrev RmOk (rm : Reg) : Prop := rm ∉ Reg.x2 :: .x3 :: .x7 :: P384Mul.accRegs

theorem RmOk.row {rm : Reg} (h : RmOk rm) : ∀ i < 5, rm ∉ Reg.x2 :: .x3 :: sqRowRegs i := by
  have : ∀ i < 5, ∀ r ∈ Reg.x2 :: .x3 :: sqRowRegs i, r ∈ Reg.x2 :: .x3 :: .x7 :: P384Mul.accRegs := by
    decide
  exact fun i hi hm => h (this i hi _ hm)

/-- Row `i`: `[acc] += 2^(64 (2i + 1)) a_i [a_(i+1) … a_5]`, the accumulator
being below `2^(64 (6 + i))` before and `2^(64 (7 + i))` after. -/
theorem sqRow_ok {rm : Reg} (hrm : RmOk rm) {i : Nat} (hi : i < 5) {s : State} {base : Addr} {size : Nat}
    (hp : Ptr s rm base size) (hz : s.gpr .x7 = 0) (hv : regsVal s P384Mul.accRegs < 2 ^ (64 * (6 + i))) :
    WP isa (.block (sqRowAt rm i)) s fun t =>
      regsVal t P384Mul.accRegs = regsVal s P384Mul.accRegs +
        2 ^ (64 * (2 * i + 1)) * ((s.gpr (sqX i)).toNat * regsVal s (aRegs.drop (i + 1))) ∧
      regsVal t P384Mul.accRegs < 2 ^ (64 * (7 + i)) ∧
      Keeps (.x2 :: .x3 :: sqRowRegs i) s t := by
  obtain ⟨hlen, hrl, hwl, hsplit, -, -, -, -, -, -, -, -, flo, fhi, -⟩ := sqRow_facts i hi
  have f27 := hrm.row i hi
  have hR := sqRowOk (size := size) hi
  -- The accumulator around the row's words.
  have hv' := hv
  rw [hsplit, regsVal_append, regsVal_append, hlen, hrl] at hv'
  have hQ : 2 ^ (64 * (6 + i)) = 2 ^ (64 * (2 * i + 1)) * 2 ^ (64 * (5 - i)) := by
    rw [← Nat.pow_add]; congr 1; omega_using [hi]
  have hQ' : 2 ^ (64 * (6 - i)) = 2 ^ 64 * 2 ^ (64 * (5 - i)) := by
    rw [← Nat.pow_add]; congr 1; omega_using [hi]
  have hQ'' : 2 ^ (64 * (7 + i)) = 2 ^ (64 * (2 * i + 1)) * (2 ^ 64 * 2 ^ (64 * (5 - i))) := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_using [hi]
  generalize hP : 2 ^ (64 * (2 * i + 1)) = P at hQ hQ'' hv' ⊢
  generalize hQv : 2 ^ (64 * (5 - i)) = Q at hQ hQ' hQ''
  have hPpos : 0 < P := hP ▸ Nat.two_pow_pos _
  generalize hL : regsVal s (P384Mul.accRegs.take (2 * i + 1)) = L at hv'
  generalize hT : regsVal s (sqRowRegs i) = T at hv'
  generalize hRst : regsVal s (P384Mul.accRegs.drop (7 + i)) = Rst at hv'
  rw [hQ', hQ] at hv'
  have hin : T + 2 ^ 64 * Q * Rst < Q := by
    refine Nat.lt_of_mul_lt_mul_left (a := P) ?_
    have : P * (T + 2 ^ 64 * Q * Rst) ≤ L + P * (T + 2 ^ 64 * Q * Rst) := Nat.le_add_left _ _
    omega_using [hv']
  have hRst0 : Rst = 0 := by
    rcases Nat.eq_zero_or_pos Rst with h | h
    · exact h
    · have : 2 ^ 64 * Q ≤ 2 ^ 64 * Q * Rst := Nat.le_mul_of_pos_right _ h
      omega_using [hin, this]
  have hW := regsVal_lt s (aRegs.drop (i + 1))
  rw [hwl, hQv] at hW
  have hx := (s.gpr (sqX i)).isLt
  have hxW : (s.gpr (sqX i)).toNat * regsVal s (aRegs.drop (i + 1)) ≤
      (2 ^ 64 - 1) * regsVal s (aRegs.drop (i + 1)) := Nat.mul_le_mul_right _ (by omega_using [])
  refine WP.mono (row_ok hp hz hR (fun e => f27 (by simp [e])) (fun e => f27 (by simp [e]))
    (fun h => f27 (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ h))) (by simp only [List.length_map, hwl, hrl]; omega_using [hi])
    (by rw [rwVal_regs, hT, hrl, hQ']; simp only [sqX] at hxW ⊢; omega_using [hin, hW, hxW])) fun t ⟨e, k⟩ => ?_
  rw [rwVal_regs, hT] at e
  have hlo : regsVal t (P384Mul.accRegs.take (2 * i + 1)) = L :=
    hL ▸ regsVal_congr fun r hr => k.gpr r (flo r hr)
  have hhi : regsVal t (P384Mul.accRegs.drop (7 + i)) = Rst :=
    hRst ▸ regsVal_congr fun r hr => k.gpr r (fhi r hr)
  have hLlt : L < P := by
    have := regsVal_lt s (P384Mul.accRegs.take (2 * i + 1)); rw [hlen, hP, hL] at this; exact this
  have hacc : regsVal t P384Mul.accRegs = L + P * (T + (s.gpr (sqX i)).toNat *
      regsVal s (aRegs.drop (i + 1))) := by
    rw [hsplit, regsVal_append, regsVal_append, hlen, hrl, hlo, hhi, e, hRst0, hP]; simp
  have hs : regsVal s P384Mul.accRegs = L + P * T := by
    rw [hsplit, regsVal_append, regsVal_append, hlen, hrl, hL, hT, hRst, hRst0, hP]; simp
  have hT' : T + (s.gpr (sqX i)).toNat * regsVal s (aRegs.drop (i + 1)) ≤ 2 ^ 64 * Q - 1 := by omega_using [hin, hW, hxW]
  have h1 := Nat.mul_le_mul_left P hT'
  have h2 : P * (2 ^ 64 * Q - 1) + P = P * (2 ^ 64 * Q) := by
    rw [Nat.mul_sub_one, Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (by
      have : 0 < Q := hQv ▸ Nat.two_pow_pos _; exact Nat.mul_pos (by decide) this))]
  refine ⟨by rw [hacc, hs, Nat.mul_add, Nat.add_assoc], by rw [hacc, hQ'']; omega_using [hLlt, h1, h2], k⟩

end VG.Proof.Mont.AArch64.P384Sqr

end

end

/-!
# P-384's Montgomery square on AArch64: the square

`sq` (`Impl/Mont/AArch64/P384Sqr.lean`) leaves `[acc] = [a]^2`
(`sq_ok`): the products of distinct words (`offDiag_ok`), doubled (`dbl_ok`),
plus the squares of the words (`diag_ok`), as `[a]^2 = 2 odd + diagSum`
(`sq_identity`).
-/

@[expose] public section

-- Powers of two up to `2^768` (the accumulator) are evaluated.
set_option exponentiation.threshold 1024

namespace VG.Proof.Mont.AArch64.P384Sqr

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P384Sqr VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open VG.Proof.Ed25519 (Word64.addCarry Word64.carryOut Word64.addCarry_value)

/-- The products of distinct words, `Σ_{i<j} 2^(64 (i + j)) a_i a_j`, as the rows add them. -/
def odd (s : State) : Nat :=
  2 ^ (64 * 1) * ((s.gpr (sqX 0)).toNat * regsVal s (aRegs.drop 1)) +
  2 ^ (64 * 3) * ((s.gpr (sqX 1)).toNat * regsVal s (aRegs.drop 2)) +
  2 ^ (64 * 5) * ((s.gpr (sqX 2)).toNat * regsVal s (aRegs.drop 3)) +
  2 ^ (64 * 7) * ((s.gpr (sqX 3)).toNat * regsVal s (aRegs.drop 4)) +
  2 ^ (64 * 9) * ((s.gpr (sqX 4)).toNat * regsVal s (aRegs.drop 5))

/-- The squares of the words, `Σ_i 2^(128 i) a_i^2`. -/
def diagSum (s : State) : Nat :=
  ((List.range 6).map fun i => 2 ^ (128 * i) * ((s.gpr (sqX i)).toNat * (s.gpr (sqX i)).toNat)).sum

theorem sq_identity (s : State) : regsVal s aRegs * regsVal s aRegs = 2 * odd s + diagSum s := by
  simp only [odd, diagSum, aRegs, P384Mul.bRegs384, regsVal, List.drop, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.range, List.range.loop, List.map, List.sum_cons,
    List.sum_nil, sqX]
  generalize (s.gpr .x4).toNat = x0
  generalize (s.gpr .x5).toNat = x1
  generalize (s.gpr .x16).toNat = x2
  generalize (s.gpr .x17).toNat = x3
  generalize (s.gpr .x21).toNat = x4
  generalize (s.gpr .x22).toNat = x5
  grind

/-! ## The products of distinct words -/

theorem sqX_mem (i : Nat) : sqX i ∈ aRegs := by
  unfold sqX
  rw [List.getD_eq_getElem?_getD]
  cases h : aRegs[i]? with
  | none => decide
  | some r => exact List.mem_of_getElem? h

theorem offDiag_eq (rm : Reg) : offDiagAt rm = zeros P384Mul.accRegs ++ (sqRowAt rm 0 ++ (sqRowAt rm 1 ++
    (sqRowAt rm 2 ++ (sqRowAt rm 3 ++ sqRowAt rm 4)))) := by
  simp only [offDiagAt, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `[acc] = odd`, from any accumulator, `x7` being zero. -/
theorem offDiag_ok {rm : Reg} (hrm : RmOk rm) {s : State} {base : Addr} {size : Nat} (hp : Ptr s rm base size)
    (hz : s.gpr .x7 = 0) :
    WP isa (.block (offDiagAt rm)) s fun t => regsVal t P384Mul.accRegs = odd s ∧
      Keeps (.x2 :: .x3 :: P384Mul.accRegs) s t := by
  have ka : ∀ {t t' : State} {rs : List Reg}, Keeps rs t t' → (∀ r ∈ aRegs, r ∉ rs) →
      ∀ i, regsVal t' (aRegs.drop i) = regsVal t (aRegs.drop i) ∧ t'.gpr (sqX i) = t.gpr (sqX i) :=
    fun k h i => ⟨regsVal_congr fun r hr => k.gpr r (h r (List.mem_of_mem_drop hr)),
      k.gpr _ (h _ (sqX_mem i))⟩
  rw [offDiag_eq, WP.block_append_iff]
  have f27₀ := hrm.row 0 (by decide)
  have f27₁ := hrm.row 1 (by decide)
  have f27₂ := hrm.row 2 (by decide)
  have f27₃ := hrm.row 3 (by decide)
  have hr7 : rm ∉ P384Mul.accRegs := fun h => hrm (by simp [h])
  refine WP.mono (zeros_ok s P384Mul.accRegs) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hv₀ : regsVal s₀ P384Mul.accRegs = 0 := regsVal_zero z₀
  have hp₀ := hp.of_keeps k₀ hr7
  have hz₀ : s₀.gpr .x7 = 0 := by rw [k₀.gpr _ (by decide), hz]
  have a₀ := ka k₀ (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f7₀, -, fa₀, -, -, fs₀⟩ := sqRow_facts 0 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f7₁, -, fa₁, -, -, fs₁⟩ := sqRow_facts 1 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f7₂, -, fa₂, -, -, fs₂⟩ := sqRow_facts 2 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f7₃, -, fa₃, -, -, fs₃⟩ := sqRow_facts 3 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, fa₄, -, -, fs₄⟩ := sqRow_facts 4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok hrm (i := 0) (by decide) hp₀ hz₀ (by rw [hv₀]; exact Nat.two_pow_pos _))
    fun s₁ ⟨e₁, b₁, k₁⟩ => ?_
  have a₁ := ka k₁ fa₀
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok hrm (i := 1) (by decide) (hp₀.of_keeps k₁ f27₀) (by rw [k₁.gpr _ f7₀, hz₀]) b₁)
    fun s₂ ⟨e₂, b₂, k₂⟩ => ?_
  have a₂ := ka k₂ fa₁
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok hrm (i := 2) (by decide) ((hp₀.of_keeps k₁ f27₀).of_keeps k₂ f27₁)
    (by rw [k₂.gpr _ f7₁, k₁.gpr _ f7₀, hz₀]) b₂) fun s₃ ⟨e₃, b₃, k₃⟩ => ?_
  have a₃ := ka k₃ fa₂
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok hrm (i := 3) (by decide) (((hp₀.of_keeps k₁ f27₀).of_keeps k₂ f27₁).of_keeps k₃ f27₂)
    (by rw [k₃.gpr _ f7₂, k₂.gpr _ f7₁, k₁.gpr _ f7₀, hz₀]) b₃) fun s₄ ⟨e₄, b₄, k₄⟩ => ?_
  have a₄ := ka k₄ fa₃
  refine WP.mono (sqRow_ok hrm (i := 4) (by decide)
    ((((hp₀.of_keeps k₁ f27₀).of_keeps k₂ f27₁).of_keeps k₃ f27₂).of_keeps k₄ f27₃)
    (by rw [k₄.gpr _ f7₃, k₃.gpr _ f7₂, k₂.gpr _ f7₁, k₁.gpr _ f7₀, hz₀]) b₄) fun t ⟨e₅, _, k₅⟩ => ?_
  refine ⟨?_, (k₀.mono (by sub_regs)).trans ((k₁.mono fs₀).trans ((k₂.mono fs₁).trans
    ((k₃.mono fs₂).trans ((k₄.mono fs₃).trans (k₅.mono fs₄)))))⟩
  rw [e₅, e₄, e₃, e₂, e₁, hv₀]
  simp only [odd, (a₄ _).1, (a₄ _).2, (a₃ _).1, (a₃ _).2, (a₂ _).1, (a₂ _).2, (a₁ _).1, (a₁ _).2,
    (a₀ _).1, (a₀ _).2, Nat.zero_add]

/-! ## Doubling -/

/-- `ts += ts` with the carry flag in, `adcs` throughout, and its carry out. -/
theorem dblAdcs_ok : ∀ (ts : List Reg) (s : State), ts.Nodup →
    WP isa (.block (dblIn false ts)) s fun t =>
      regsVal t ts + 2 ^ (64 * ts.length) * t.c.toNat = 2 * regsVal s ts + s.c.toNat ∧ Keeps ts s t
  | [], s, _ => WP.block_nil ⟨by simp [regsVal], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | t :: ts, s, hnd => by
    rw [dblIn, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addc_ok s t t t false (c := s.c) rfl) fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
    have htn : t ∉ ts := (List.nodup_cons.mp hnd).1
    refine WP.mono (dblAdcs_ok ts s₁ (List.nodup_cons.mp hnd).2) fun s₂ ⟨e₂, k₂⟩ => ?_
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have g₁ : s₂.gpr t = s₁.gpr t := k₂.gpr t htn
    have gt : regsVal s₁ ts = regsVal s ts := regsVal_congr fun r hr => k₁.gpr r (by
      simp only [List.mem_singleton]; rintro rfl; exact htn hr)
    have ev := Word64.addCarry_value (s.gpr t) (s.gpr t) s.c
    rw [← v₁, ← c₁] at ev
    rw [gt] at e₂
    simp only [regsVal, List.length_cons, g₁, pow64_succ]
    simp only [Nat.mul_assoc] at ev ⊢
    omega_arith

/-- The accumulator doubled, its carry out in the flag. -/
theorem dbl_ok (s : State) :
    WP isa (.block dbl) s fun t =>
      regsVal t P384Mul.accRegs + 2 ^ 768 * t.c.toNat = 2 * regsVal s P384Mul.accRegs ∧
      Keeps P384Mul.accRegs s t := by
  rw [dbl, show P384Mul.accRegs = .x8 :: P384Mul.accRegs.tail from rfl, dblIn, ← List.singleton_append,
    WP.block_append_iff]
  refine WP.mono (addc_ok s .x8 .x8 .x8 true (c := false) rfl) fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
  refine WP.mono (dblAdcs_ok P384Mul.accRegs.tail s₁ (by decide)) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
  have g₁ : s₂.gpr .x8 = s₁.gpr .x8 := k₂.gpr _ (by decide)
  have gt : regsVal s₁ P384Mul.accRegs.tail = regsVal s P384Mul.accRegs.tail :=
    regsVal_congr fun r hr => k₁.gpr r (by revert r; decide)
  have ev := Word64.addCarry_value (s.gpr .x8) (s.gpr .x8) false
  rw [← v₁, ← c₁] at ev
  rw [gt, show 64 * P384Mul.accRegs.tail.length = 704 from rfl] at e₂
  simp only [regsVal, g₁, Bool.toNat_false] at ev ⊢
  omega_arith

/-! ## The squares of the words -/

/-- The squares of the words of `as`, `Σ_i 2^(128 i) a_i^2`. -/
def dgList (s : State) : List Reg → Nat
  | [] => 0
  | a :: as => (s.gpr a).toNat * (s.gpr a).toNat + 2 ^ 128 * dgList s as

/-- `[hi lo] += a^2` with the carry in: `mul`, `adds` or `adcs`, `umulh`, `adcs`. -/
theorem diagStep_ok (s : State) {a lo hi : Reg} (first : Bool) (ha : a ≠ .x2) (hl : lo ≠ .x2)
    (hh : hi ≠ .x2) (hlh : lo ≠ hi) (hal : a ≠ lo) :
    WP isa (.block [.mul .x .x2 a a, if first then .adds .x lo lo .x2 else .adcs .x lo lo .x2,
        .umulh .x2 a a, .adcs .x hi hi .x2]) s fun t =>
      (t.gpr lo).toNat + 2 ^ 64 * (t.gpr hi).toNat + 2 ^ 128 * t.c.toNat =
        (s.gpr lo).toNat + 2 ^ 64 * (s.gpr hi).toNat + (s.gpr a).toNat * (s.gpr a).toNat +
          (if first then 0 else s.c.toNat) ∧
      Keeps [.x2, lo, hi] s t := by
  have hm := VG.Proof.Ed25519.AArch64.mul_lo_hi (s.gpr a) (s.gpr a)
  simp only [VG.Proof.Ed25519.AArch64.mulHi] at hm
  rw [← List.singleton_append, WP.block_append_iff]
  have hmul : WP isa (.block [.mul .x .x2 a a]) s fun t => t.gpr .x2 = s.gpr a * s.gpr a ∧
      t.c = s.c ∧ Keeps [.x2] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write,
      BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  refine WP.mono hmul fun s₁ ⟨v₁, c₁, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (addc_ok s₁ lo lo .x2 first rfl) fun s₂ ⟨v₂, c₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have humulh : WP isa (.block [.umulh .x2 a a]) s₂ fun t =>
      t.gpr .x2 = BitVec.ofNat 64 ((s₂.gpr a).toNat * (s₂.gpr a).toNat / 2 ^ 64) ∧
      t.c = s₂.c ∧ Keeps [.x2] s₂ t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_write,
      BitVec.setWidth_eq, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]
  refine WP.mono humulh fun s₃ ⟨v₃, c₃, k₃⟩ => ?_
  refine WP.mono (addc_ok s₃ hi hi .x2 false (c := s₃.c) rfl) fun t ⟨v₄, c₄, k₄⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs)).trans ((k₂.mono (by sub_regs)).trans ((k₃.mono (by sub_regs)).trans
    (k₄.mono (by sub_regs))))⟩
  have ne : ∀ {x y : Reg}, x ≠ y → y ∉ [x] := fun h h' => h (List.mem_singleton.mp h').symm
  have a₂ : s₂.gpr a = s.gpr a := by rw [k₂.gpr _ (ne (Ne.symm hal)), k₁.gpr _ (ne (Ne.symm ha))]
  have lo₁ : s₁.gpr lo = s.gpr lo := k₁.gpr _ (ne (Ne.symm hl))
  have hi₂ : s₂.gpr hi = s.gpr hi := by rw [k₂.gpr _ (ne hlh), k₁.gpr _ (ne (Ne.symm hh))]
  have hi₃ : s₃.gpr hi = s.gpr hi := by rw [k₃.gpr _ (ne (Ne.symm hh)), hi₂]
  have x₂₂ : s₂.gpr .x2 = s.gpr a * s.gpr a := by rw [k₂.gpr _ (ne hl), v₁]
  have lo₃ : s₃.gpr lo = s₂.gpr lo := k₃.gpr _ (ne (Ne.symm hl))
  have lo₄ : t.gpr lo = s₂.gpr lo := by rw [k₄.gpr _ (ne (Ne.symm hlh)), lo₃]
  have e₂ := Word64.addCarry_value (s₁.gpr lo) (s₁.gpr .x2) (if first then false else s₁.c)
  rw [← v₂, ← c₂, lo₁, v₁, c₁] at e₂
  have e₄ := Word64.addCarry_value (s₃.gpr hi) (s₃.gpr .x2) s₃.c
  rw [← v₄, ← c₄, hi₃, v₃, c₃, a₂] at e₄
  have hhi : (BitVec.ofNat 64 ((s.gpr a).toNat * (s.gpr a).toNat / 2 ^ 64)).toNat =
      (s.gpr a).toNat * (s.gpr a).toNat / 2 ^ 64 := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_arith)
  rw [hhi] at e₄
  rw [lo₄]
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.toNat_false] at e₂ ⊢ <;> omega_arith

/-- `ts += Σ_i 2^(128 i) a_i^2` with the carry in (unless `first`), and its carry out. -/
theorem diagIn_ok : ∀ (as ts : List Reg) (first : Bool) (s : State), ts.length = 2 * as.length →
    (first = true → as ≠ []) → (Reg.x2 :: ts).Nodup → (∀ a ∈ as, a ≠ .x2 ∧ a ∉ ts) →
    WP isa (.block (diagIn first as ts)) s fun t =>
      regsVal t ts + 2 ^ (64 * ts.length) * t.c.toNat =
        regsVal s ts + dgList s as + (if first then 0 else s.c.toNat) ∧ Keeps (.x2 :: ts) s t
  | [], [], first, s, _, hne, _, _ => by
    cases first
    · exact WP.block_nil ⟨by simp [regsVal, dgList], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · exact absurd rfl (hne rfl)
  | [], _ :: _, _, _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [], _, _, hl, _, _, _ => absurd hl (by simp)
  | _ :: _, [_], _, _, hl, _, _, _ => by simp at hl; omega_arith
  | a :: as, lo :: hi :: ts, first, s, hl, _, hnd, ha => by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨h2l, h2h, h2t⟩, ⟨hlh, hlt⟩, hht, hnd⟩ := hnd
    obtain ⟨ha2, hal⟩ := ha a (List.mem_cons_self ..)
    simp only [List.mem_cons, not_or] at hal
    obtain ⟨hal, hah, hat⟩ := hal
    rw [diagIn, WP.block_append_iff]
    refine WP.mono (diagStep_ok s first ha2 (Ne.symm h2l) (Ne.symm h2h) hlh hal) fun s₁ ⟨e₁, k₁⟩ => ?_
    have has : ∀ b ∈ as, b ≠ .x2 ∧ b ∉ ts := fun b hb => by
      obtain ⟨h1, h2⟩ := ha b (List.mem_cons_of_mem _ hb)
      simp only [List.mem_cons, not_or] at h2
      exact ⟨h1, h2.2.2⟩
    refine WP.mono (diagIn_ok as ts false s₁ (by simp at hl; omega_arith) (by simp)
      (List.nodup_cons.mpr ⟨h2t, hnd⟩) has) fun t ⟨e₂, k₂⟩ => ?_
    refine ⟨?_, (k₁.mono (by sub_regs)).trans (k₂.mono (by sub_regs))⟩
    have gt : regsVal s₁ ts = regsVal s ts := regsVal_congr fun r hr => k₁.gpr r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => h2t (h ▸ hr), fun h => hlt (h ▸ hr), fun h => hht (h ▸ hr)⟩)
    have gd : ∀ bs : List Reg, (∀ b ∈ bs, b ≠ .x2 ∧ b ∉ ts ∧ b ≠ lo ∧ b ≠ hi) →
        dgList s₁ bs = dgList s bs := by
      intro bs hbs
      induction bs with
      | nil => rfl
      | cons b bs ih =>
        obtain ⟨b2, -, bl, bh⟩ := hbs b (List.mem_cons_self ..)
        have : s₁.gpr b = s.gpr b := k₁.gpr b (by simp [b2, bl, bh])
        simp only [dgList, this, ih fun c hc => hbs c (List.mem_cons_of_mem _ hc)]
    have hdg := gd as fun b hb => by
      obtain ⟨h1, h2⟩ := ha b (List.mem_cons_of_mem _ hb)
      simp only [List.mem_cons, not_or] at h2
      exact ⟨h1, h2.2.2, h2.1, h2.2.1⟩
    have glo : t.gpr lo = s₁.gpr lo := k₂.gpr _ (by simp [Ne.symm h2l, hlt])
    have ghi : t.gpr hi = s₁.gpr hi := k₂.gpr _ (by simp [Ne.symm h2h, hht])
    rw [gt, hdg] at e₂
    simp only [regsVal, dgList, List.length_cons, glo, ghi, pow64_succ, Bool.false_eq_true,
      ite_false] at e₁ e₂ ⊢
    simp only [Nat.mul_add, Nat.mul_assoc] at e₁ e₂ ⊢
    omega_arith

/-- The squares of the words added to the accumulator, its carry out in the flag. -/
theorem diag_ok (s : State) :
    WP isa (.block diag) s fun t =>
      regsVal t P384Mul.accRegs + 2 ^ 768 * t.c.toNat = regsVal s P384Mul.accRegs + diagSum s ∧
      Keeps (.x2 :: P384Mul.accRegs) s t := by
  refine WP.mono (diagIn_ok aRegs P384Mul.accRegs true s rfl (by decide) (by decide) (by decide))
    fun t ⟨e, k⟩ => ⟨?_, k⟩
  have hd : dgList s aRegs = diagSum s := by
    simp only [dgList, diagSum, aRegs, P384Mul.bRegs384, sqX, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.range, List.range.loop, List.map, List.sum_cons,
      List.sum_nil]
    omega_arith
  rw [← hd]
  simpa only [ite_true, Nat.add_zero, show 64 * P384Mul.accRegs.length = 768 from rfl] using e

/-! ## The square -/

theorem sq_eq (rm : Reg) : sqAt rm = offDiagAt rm ++ (dbl ++ diag) := by
  simp only [sqAt, List.append_assoc]

/-- The square: `[acc] = [a]^2`, `x7` being zero. -/
theorem sqAt_ok {rm : Reg} (hrm : RmOk rm) {s : State} {base : Addr} {size : Nat} (hp : Ptr s rm base size)
    (hz : s.gpr .x7 = 0) :
    WP isa (.block (sqAt rm)) s fun t => regsVal t P384Mul.accRegs = regsVal s aRegs * regsVal s aRegs ∧
      Keeps (.x2 :: .x3 :: P384Mul.accRegs) s t := by
  rw [sq_eq, WP.block_append_iff]
  refine WP.mono (offDiag_ok hrm hp hz) fun s₁ ⟨e₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (dbl_ok s₁) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine WP.mono (diag_ok s₂) fun t ⟨e₃, k₃⟩ => ?_
  refine ⟨?_, (k₁.trans ((k₂.mono (by sub_regs)).trans (k₃.mono (by sub_regs))))⟩
  have ha : ∀ r ∈ aRegs, s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr r (by revert r; decide), k₁.gpr r (by revert r; decide)]
  have hdg : diagSum s₂ = diagSum s := by
    simp only [diagSum, sqX, aRegs, P384Mul.bRegs384, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.range, List.range.loop, List.map, List.sum_cons,
      List.sum_nil, ha .x4 (by decide), ha .x5 (by decide), ha .x16 (by decide), ha .x17 (by decide),
      ha .x21 (by decide), ha .x22 (by decide)]
  rw [hdg] at e₃
  rw [e₁] at e₂
  have hid := sq_identity s
  have hlt : regsVal s aRegs * regsVal s aRegs < 2 ^ 768 := by
    have := regsVal_lt s aRegs
    rw [show 64 * aRegs.length = 384 from rfl] at this
    calc regsVal s aRegs * regsVal s aRegs < 2 ^ 384 * 2 ^ 384 := Nat.mul_lt_mul'' this this
      _ = 2 ^ 768 := by rw [← Nat.pow_add]
  have := Bool.toNat_le s₂.c
  have := Bool.toNat_le t.c
  rcases Nat.eq_zero_or_pos s₂.c.toNat with h | h <;> rcases Nat.eq_zero_or_pos t.c.toNat with h' | h' <;>
    omega_arith

/-- The square as `vg_p384_sqr_mod_p` computes it. -/
theorem sq_ok {s : State} {base : Addr} (hp : Ptr s .x27 base 48) (hz : s.gpr .x7 = 0) :
    WP isa (.block sq) s fun t => regsVal t P384Mul.accRegs = regsVal s aRegs * regsVal s aRegs ∧
      Keeps (.x2 :: .x3 :: P384Mul.accRegs) s t :=
  sqAt_ok (by decide) hp hz

end VG.Proof.Mont.AArch64.P384Sqr
