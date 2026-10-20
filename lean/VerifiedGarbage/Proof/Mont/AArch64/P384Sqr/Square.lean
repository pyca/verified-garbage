module

public import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Rows
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.Exec

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

theorem offDiag_eq : offDiag = zeros P384Mul.accRegs ++ (sqRow 0 ++ (sqRow 1 ++ (sqRow 2 ++
    (sqRow 3 ++ sqRow 4)))) := by
  simp only [offDiag, List.range, List.range.loop, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- `[acc] = odd`, from any accumulator, `x7` being zero. -/
theorem offDiag_ok {s : State} {base : Addr} (hp : Ptr s .x27 base 48) (hz : s.gpr .x7 = 0) :
    WP isa (.block offDiag) s fun t => regsVal t P384Mul.accRegs = odd s ∧
      Keeps (.x2 :: .x3 :: P384Mul.accRegs) s t := by
  have ka : ∀ {t t' : State} {rs : List Reg}, Keeps rs t t' → (∀ r ∈ aRegs, r ∉ rs) →
      ∀ i, regsVal t' (aRegs.drop i) = regsVal t (aRegs.drop i) ∧ t'.gpr (sqX i) = t.gpr (sqX i) :=
    fun k h i => ⟨regsVal_congr fun r hr => k.gpr r (h r (List.mem_of_mem_drop hr)),
      k.gpr _ (h _ (sqX_mem i))⟩
  rw [offDiag_eq, WP.block_append_iff]
  refine WP.mono (zeros_ok s P384Mul.accRegs) fun s₀ ⟨z₀, k₀⟩ => ?_
  have hv₀ : regsVal s₀ P384Mul.accRegs = 0 := regsVal_zero z₀
  have hp₀ := hp.of_keeps k₀ (by decide)
  have hz₀ : s₀.gpr .x7 = 0 := by rw [k₀.gpr _ (by decide), hz]
  have a₀ := ka k₀ (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f27₀, f7₀, -, fa₀, -, -, fs₀⟩ := sqRow_facts 0 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f27₁, f7₁, -, fa₁, -, -, fs₁⟩ := sqRow_facts 1 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f27₂, f7₂, -, fa₂, -, -, fs₂⟩ := sqRow_facts 2 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, f27₃, f7₃, -, fa₃, -, -, fs₃⟩ := sqRow_facts 3 (by decide)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, fa₄, -, -, fs₄⟩ := sqRow_facts 4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok (i := 0) (by decide) hp₀ hz₀ (by rw [hv₀]; exact Nat.two_pow_pos _))
    fun s₁ ⟨e₁, b₁, k₁⟩ => ?_
  have a₁ := ka k₁ fa₀
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok (i := 1) (by decide) (hp₀.of_keeps k₁ f27₀) (by rw [k₁.gpr _ f7₀, hz₀]) b₁)
    fun s₂ ⟨e₂, b₂, k₂⟩ => ?_
  have a₂ := ka k₂ fa₁
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok (i := 2) (by decide) ((hp₀.of_keeps k₁ f27₀).of_keeps k₂ f27₁)
    (by rw [k₂.gpr _ f7₁, k₁.gpr _ f7₀, hz₀]) b₂) fun s₃ ⟨e₃, b₃, k₃⟩ => ?_
  have a₃ := ka k₃ fa₂
  rw [WP.block_append_iff]
  refine WP.mono (sqRow_ok (i := 3) (by decide) (((hp₀.of_keeps k₁ f27₀).of_keeps k₂ f27₁).of_keeps k₃ f27₂)
    (by rw [k₃.gpr _ f7₂, k₂.gpr _ f7₁, k₁.gpr _ f7₀, hz₀]) b₃) fun s₄ ⟨e₄, b₄, k₄⟩ => ?_
  have a₄ := ka k₄ fa₃
  refine WP.mono (sqRow_ok (i := 4) (by decide)
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
    omega

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
  omega

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
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  rw [hhi] at e₄
  rw [lo₄]
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true, Bool.toNat_false] at e₂ ⊢ <;> omega

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
  | _ :: _, [_], _, _, hl, _, _, _ => by simp at hl; omega
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
    refine WP.mono (diagIn_ok as ts false s₁ (by simp at hl; omega) (by simp)
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
    omega

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
    omega
  rw [← hd]
  simpa only [ite_true, Nat.add_zero, show 64 * P384Mul.accRegs.length = 768 from rfl] using e

/-! ## The square -/

theorem sq_eq : sq = offDiag ++ (dbl ++ diag) := by simp only [sq, List.append_assoc]

/-- The square: `[acc] = [a]^2`, `x7` being zero. -/
theorem sq_ok {s : State} {base : Addr} (hp : Ptr s .x27 base 48) (hz : s.gpr .x7 = 0) :
    WP isa (.block sq) s fun t => regsVal t P384Mul.accRegs = regsVal s aRegs * regsVal s aRegs ∧
      Keeps (.x2 :: .x3 :: P384Mul.accRegs) s t := by
  rw [sq_eq, WP.block_append_iff]
  refine WP.mono (offDiag_ok hp hz) fun s₁ ⟨e₁, k₁⟩ => ?_
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
    omega

end VG.Proof.Mont.AArch64.P384Sqr
