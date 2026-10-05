import VerifiedGarbage.Proof.Mont.X86_64.Wide

/-!
# Montgomery arithmetic on x86-64: the multiplication with the accumulator in memory

The accumulator of `mulW` is `T = [tmp] + 2^(64 n) (r9 + 2⁶⁴ r10)` (`accW`). A
row of `rcx · [d]` and its carry add `rcx [d]` to it (`memRowCarry_ok`); a
round makes `2⁶⁴ T' = T + a_i B + u m` and keeps `T < 2m` (`roundW_ok`), as
`round_ok` does with the accumulator in registers; `n` rounds from zero give
`2^(64 n) T = A B + U m` (`roundsW_ok`). Then `csubW` reduces `T` below `m`
into `[o]` (`csubW_ok`), and `mulW_ok` is `mul_ok` for any number of words.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono se0 sub_borrow sbb_borrow)

/-- The accumulator: `[tmp] + 2^(64 n) (r9 + 2⁶⁴ r10)`. -/
def accW (s : State) (base : Addr) (M : Mod) : Nat :=
  wordsVal s.mem base M.tmp M.n + 2 ^ (64 * M.n) * ((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat)

/-- The registers a round changes. -/
abbrev roundRegs : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10]

/-- A row of `rcx · [d]` into the accumulator, and its carry into `r9` and
`r10`, if the sum fits. -/
theorem memRowCarry_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    {d : Nat} (htmp : M.tmp + 8 * M.n ≤ size) (hd : d + 8 * M.n ≤ size)
    (hsep : d + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ d)
    (hb : accW s base M + (s.gpr .rcx).toNat * wordsVal s.mem base d M.n < 2 ^ (64 * M.n) * 2 ^ 128) :
    WP isa (.block (memRow M.n M.tmp d ++ carryUp .r9 .r10)) s fun s' =>
      accW s' base M = accW s base M + (s.gpr .rcx).toNat * wordsVal s.mem base d M.n ∧
      KeepRegs [.r8, .rbp, .rax, .rdx, .r9, .r10] s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (memRow_ok hs htmp hd hsep) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have g9 : s₁.gpr .r9 = s.gpr .r9 := k₁.gpr .r9 (by decide)
  have g10 : s₁.gpr .r10 = s.gpr .r10 := k₁.gpr .r10 (by decide)
  simp only [accW] at hb ⊢
  generalize hP : 2 ^ (64 * M.n) = P at hb e₁ ⊢
  have hP0 : 0 < P := hP ▸ Nat.two_pow_pos _
  have hc : (s₁.gpr .r9).toNat + 2 ^ 64 * (s₁.gpr .r10).toNat + (s₁.gpr .rbp).toNat < 2 ^ 128 := by
    rw [g9, g10]
    have h' : P * (((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat) + (s₁.gpr .rbp).toNat) <
        P * 2 ^ 128 := by
      rw [Nat.mul_add]; omega
    exact Nat.lt_of_mul_lt_mul_left h'
  refine WP.mono (carryUp_ok s₁ (by decide) hc) fun s₂ ⟨e₂, k₂⟩ => ?_
  refine ⟨?_, (k₁.mono (by sub_regs')).trans ((Keeps.regs k₂).mono (by sub_regs')),
    fun x hx => by rw [k₂.2.1, O₁ x hx]⟩
  rw [k₂.2.1, e₂, g9, g10, Nat.mul_add P _ (s₁.gpr .rbp).toNat]
  omega

/-- Round `i` of `mulW`: `2⁶⁴ T' = T + a_i B + u m`, and `T' < 2m` if `T < 2m`. -/
theorem roundW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod}
    (hn : 0 < M.n) {a b i m : Nat} (ha : a + 8 * i + 8 ≤ size) (hb : b + 8 * M.n ≤ size)
    (hmo : M.mo + 8 * M.n ≤ size) (htmp : M.tmp + 8 * M.n ≤ size)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b)
    (hmT : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo)
    (hm : wordsVal s.mem base M.mo M.n = m) (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wordsVal s.mem base b M.n < m) (hT : accW s base M < 2 * m) :
    WP isa (.block (roundW M a b i)) s fun s' =>
      (∃ u, 2 ^ 64 * accW s' base M = accW s base M +
        (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n + u * m) ∧
      accW s' base M < 2 * m ∧ s'.gpr .r10 = 0 ∧
      KeepRegs roundRegs s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem := by
  have hnw := hs.nowrap
  have hm' : m < 2 ^ (64 * M.n) := hm ▸ wordsVal_lt _ _ _ _
  have hP : 2 ^ (64 * M.n) * 2 ^ 128 = 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by rw [Nat.mul_assoc]
  have hlim : (2 ^ 64 + 1) * m ≤ 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
    have : (2 ^ 64 + 1) * m ≤ (2 ^ 64 + 1) * 2 ^ (64 * M.n) := Nat.mul_le_mul_left _ (by omega)
    have h2 : (2 ^ 64 + 1) * 2 ^ (64 * M.n) ≤ 2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64 := by
      rw [Nat.mul_comm (2 ^ 64 + 1), Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by decide)
    omega
  simp only [roundW, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rcx ha) fun s₁ ⟨c₁, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hA := (word s.mem base (a + 8 * i)).isLt
  have hAB : (word s.mem base (a + 8 * i)).toNat * wordsVal s.mem base b M.n ≤ (2 ^ 64 - 1) * m :=
    Nat.mul_le_mul (by omega) (by omega)
  have hT₁ : accW s₁ base M = accW s base M := by
    simp only [accW, hm₁, k₁.1 .r9 (by decide), k₁.1 .r10 (by decide)]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (memRowCarry_ok hs₁ (d := b) htmp hb hbT (by
      rw [hT₁, c₁, hm₁, hP]; omega)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hT₁, c₁, hm₁] at e₂
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- `u = t₀ m' mod 2⁶⁴`.
  rw [WP.block_append_iff, show ([.mov .r8 (.mem (sc M.tmp)), .mov .rax (.reg .r8), .movImm64 .rcx M.minv,
      .mul .rcx, .mov .rcx (.reg .rax)] : List Instr) = [.mov .r8 (.mem (sc M.tmp))] ++
      [.mov .rax (.reg .r8), .movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)] from rfl,
    WP.block_append_iff]
  refine WP.mono (movMem_ok hs₂ .r8 (d := M.tmp) (by omega)) fun s₃ ⟨l₃, _, k₃⟩ => ?_
  refine WP.mono (uBlock_ok s₃ .r8 M.minv) fun s₄ ⟨u₄, k₄⟩ => ?_
  have hs₄ := (hs₂.of_keeps k₃ (by decide)).of_keeps k₄ (by decide)
  have hm₄ : s₄.mem = s₂.mem := by rw [k₄.2.1, k₃.2.1]
  have hT₄ : accW s₄ base M = accW s₂ base M := by
    simp only [accW, hm₄, k₄.1 .r9 (by decide), k₄.1 .r10 (by decide), k₃.1 .r9 (by decide),
      k₃.1 .r10 (by decide)]
  have hmo₂ : wordsVal s₂.mem base M.mo M.n = m := by
    rw [O₂.wordsVal hmT (by omega), hm₁, hm]
  have hu := (s₄.gpr .rcx).isLt
  have hum : (s₄.gpr .rcx).toNat * m ≤ (2 ^ 64 - 1) * m := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (memRowCarry_ok hs₄ (d := M.mo) htmp hmo hmT (by
      rw [hT₄, e₂, hm₄, hmo₂, hP]; omega)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  rw [hT₄, e₂, hm₄, hmo₂] at e₅
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- The low word is zero.
  have hlow : (word s₅.mem base M.tmp).toNat = 0 := by
    have hmod : ∀ u : State, accW u base M % 2 ^ 64 = (word u.mem base M.tmp).toNat := by
      intro u
      obtain ⟨n', hn'⟩ : ∃ n', M.n = n' + 1 := ⟨M.n - 1, by omega⟩
      simp only [accW, hn', wordsVal, pow64_succ]
      rw [Nat.mul_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (word u.mem base M.tmp).isLt
    have hl := mont_low (word s₂.mem base M.tmp).toNat M.minv.toNat m hinv
    rw [l₃] at u₄
    rw [← u₄] at hl
    have h₂ := hmod s₂
    have h₅ := hmod s₅
    have e₅' : accW s₅ base M = accW s₂ base M + (s₄.gpr .rcx).toNat * m := by rw [e₅, e₂]
    omega
  refine WP.mono (shiftDown_ok hs₅ hn htmp) fun s₆ ⟨e₆, r9₆, r10₆, k₆, O₆⟩ => ?_
  have hshift : 2 ^ 64 * accW s₆ base M = accW s₅ base M := by
    obtain ⟨n', hn'⟩ : ∃ n', M.n = n' + 1 := ⟨M.n - 1, by omega⟩
    have hw5 : wordsVal s₅.mem base M.tmp M.n =
        (word s₅.mem base M.tmp).toNat + 2 ^ 64 * wordsVal s₅.mem base (M.tmp + 8) (M.n - 1) := by
      rw [hn']; rfl
    have hp : 2 ^ (64 * M.n) = 2 ^ 64 * 2 ^ (64 * (M.n - 1)) := by
      rw [hn', pow64_succ, Nat.add_sub_cancel]
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [accW]
    rw [e₆, r9₆, r10₆, hw5, hlow, hz, hp]
    grind
  refine ⟨⟨(s₄.gpr .rcx).toNat, by rw [hshift, e₅]⟩, ?_, r10₆, ?_, fun x hx => ?_⟩
  · have : 2 ^ 64 * accW s₆ base M < 2 ^ 64 * (2 * m) := by rw [hshift, e₅]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  · exact ((((((Keeps.regs k₁).mono (by sub_regs')).trans (k₂.mono (by sub_regs'))).trans
      ((Keeps.regs k₃).mono (by sub_regs'))).trans ((Keeps.regs k₄).mono (by sub_regs'))).trans
      (k₅.mono (by sub_regs'))).trans (k₆.mono (by sub_regs'))
  · rw [O₆ x hx, O₅ x hx, hm₄, O₂ x hx, hm₁]

/-- `k` rounds of `mulW`, from a cleared accumulator. -/
theorem roundsW_ok {M : Mod} (hn : 0 < M.n) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (htmp : M.tmp + 8 * M.n ≤ size) (haT : a + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ a)
    (hbT : b + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ b)
    (hmT : M.mo + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ M.mo)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, Scr s base size →
      wordsVal s.mem base M.mo M.n = m → wordsVal s.mem base b M.n < m → accW s base M = 0 →
      s.gpr .r10 = 0 →
      WP isa (.block ((List.range k).flatMap (roundW M a b))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * accW s' base M =
          wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m) ∧
        accW s' base M < 2 * m ∧ s'.gpr .r10 = 0 ∧
        KeepRegs roundRegs s s' ∧ Outside base M.tmp (8 * M.n) s.mem s'.mem
  | 0, _, s, _, _, _, hB, h0, h10 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega,
      h10, ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, hk, s, base, hs, hm, hB, h0, h10 => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (roundsW_ok hn ha hb hmo htmp haT hbT hmT hinv k (by omega) hs hm hB h0 h10)
      fun s₁ ⟨⟨U, eU⟩, hT, _, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hm₁ : wordsVal s₁.mem base M.mo M.n = m := by rw [O₁.wordsVal hmT (by omega), hm]
    have hB₁ : wordsVal s₁.mem base b M.n = wordsVal s.mem base b M.n := O₁.wordsVal hbT (by omega)
    have hA₁ : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) :=
      O₁.word (by omega) (by omega)
    refine WP.mono (roundW_ok hs₁ hn (i := k) (by omega) hb hmo htmp hbT hmT hm₁ hinv
      (by rw [hB₁]; exact hB) hT) fun s₂ ⟨⟨u, eu⟩, hT₂, h10₂, k₂, O₂⟩ => ?_
    rw [hB₁, hA₁] at eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, h10₂, k₁.trans k₂, fun x hx => by rw [O₂ x hx, O₁ x hx]⟩
    calc 2 ^ (64 * (k + 1)) * accW s₂ base M
        = 2 ^ (64 * k) * (2 ^ 64 * accW s₂ base M) := by
          rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
      _ = 2 ^ (64 * k) * accW s₁ base M +
          2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat * wordsVal s.mem base b M.n +
          2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
      _ = (wordsVal s.mem base a k + 2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat) *
          wordsVal s.mem base b M.n + (U + 2 ^ (64 * k) * u) * m := by
          rw [eU, Nat.add_mul, Nat.add_mul]; omega
      _ = _ := by rw [wordsVal_succ_top]

end VG.Proof.Mont.X86_64
