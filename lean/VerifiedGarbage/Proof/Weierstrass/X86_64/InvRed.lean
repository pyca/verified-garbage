import VerifiedGarbage.Proof.Weierstrass.X86_64.InvWords
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy

/-!
# Inversion by divsteps on x86-64: the reduction of the coefficients

The reduction `mredC` of a signed number of `n + 1` words to `Divstep.mred`
(`mredC_ok`): `k = t₀ m`, `[t]` sign-extended and plus `k p`, then its words
`1 … n + 1` brought into `[0, p)` by carry chains with `p` under masks.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono add_carry adc_carry sub_borrow sbb_borrow)

theorem sext0 : (0 : BitVec 32).signExtend 64 = 0 := by decide

/-- `rcx = t₀ m mod 2^64`. -/
theorem kOf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t : Nat}
    (ht : t + 8 ≤ size) :
    WP isa (.block (kOf M t)) s fun u =>
      (u.gpr .rcx).toNat = (word s.mem base t).toNat * M.minv.toNat % 2 ^ 64 ∧
      Keeps [.rax, .rcx, .rdx] s u := by
  rw [kOf, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax ht) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  have h : WP isa (.block [.movImm64 .rcx M.minv, .mul .rcx, .mov .rcx (.reg .rax)]) s₁ fun u =>
      u.gpr .rcx = BitVec.ofNat 64 ((s₁.gpr .rax).toNat * M.minv.toNat) ∧ Keeps [.rax, .rcx, .rdx] s₁ u := by
    irun [RegUpd.gpr_setReg_self]
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2, ite_false]
  refine WP.mono h fun u ⟨c, k⟩ => ⟨?_, (k₁.mono (by decide)).trans k⟩
  rw [c, BitVec.toNat_ofNat, l₁]

/-- Word `n + 1` of `[t]`: word `n`'s sign. -/
theorem sextTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) :
    WP isa (.block (sextTop M t)) s fun u =>
      wordsVal u.mem base t (M.n + 2) =
        wordsVal s.mem base t (M.n + 1) + 2 ^ (64 * (M.n + 1)) * sgnW (word s.mem base (t + 8 * M.n)) ∧
      KeepRegs [.rax, .rdx, .r8] s u ∧ Outside base (t + 8 * (M.n + 1)) 8 s.mem u.mem := by
  have hn := hs.nowrap
  rw [sextTop, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rdx (d := t + 8 * M.n) (by omega)) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .r8) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  refine WP.mono (storeReg_ok hs₂ .r8 (d := t + 8 * (M.n + 1)) (by omega)) fun u ⟨mu, _, _, ku⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  have O := writeW_outside s₂.mem base (d := t + 8 * (M.n + 1)) (s₂.gpr .r8) (by omega)
  refine ⟨?_, (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
    (ku.mono (by decide)), by rw [mu, ← hm₂]; exact O⟩
  rw [show M.n + 2 = M.n + 1 + 1 from rfl, mu, wordsVal_succ_top, word_writeW_self,
    O.wordsVal (by omega) (by omega), hm₂, g₂, smask_toNat, l₁]

/-- `[d] += rbp` (two words), modulo `2^128`. -/
theorem carry2_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 16 ≤ size) :
    WP isa (.block (carry2 d)) s fun u =>
      wordsVal u.mem base d 2 = (wordsVal s.mem base d 2 + (s.gpr .rbp).toNat) % 2 ^ 128 ∧
      KeepRegs [.r8] s u ∧ Outside base d 16 s.mem u.mem := by
  have hn := hs.nowrap
  rw [carry2, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 (d := d) (by omega)) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have ha : WP isa (.block [.alu .add .r8 (.reg .rbp)]) s₁ fun v =>
      v.gpr .r8 = s₁.gpr .r8 + s₁.gpr .rbp ∧
        v.cf = some (decide (2 ^ 64 ≤ (s₁.gpr .r8).toNat + (s₁.gpr .rbp).toNat)) ∧ Keeps [.r8] s₁ v := by
    irun
    exact ⟨rfl, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono ha fun s₂ ⟨a₂, c₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeReg_ok hs₂ .r8 (d := d) (by omega)) fun s₃ ⟨m₃, g₃, f₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs₃ .r8 (d := d + 8) (by omega)) fun s₄ ⟨l₄, f₄, k₄⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have hc : WP isa (.block [.alu .adc .r8 (.imm 0)]) s₄ fun v =>
      v.gpr .r8 = s₄.gpr .r8 + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ (s₁.gpr .r8).toNat + (s₁.gpr .rbp).toNat))).setWidth 64 ∧
        Keeps [.r8] s₄ v := by
    irun [f₄, f₃, c₂, sext0]
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono hc fun s₅ ⟨a₅, k₅⟩ => ?_
  have hs₅ := (hs₃.of_keeps k₄ (by decide)).of_keeps k₅ (by decide)
  refine WP.mono (storeReg_ok hs₅ .r8 (d := d + 8) (by omega)) fun u ⟨mu, _, _, ku⟩ => ?_
  have O₃ := writeW_outside s₂.mem base (d := d) (s₂.gpr .r8) (by omega)
  have O₅ := writeW_outside s₅.mem base (d := d + 8) (s₅.gpr .r8) (by omega)
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  have hm₅ : s₅.mem = s₃.mem := by rw [k₅.2.1, k₄.2.1]
  refine ⟨?_, ((((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (k₃.mono (by decide))).trans (((Keeps.regs k₄).trans
    (Keeps.regs k₅)).trans (ku.mono (by decide)))).mono (by decide), fun x hx => ?_⟩
  · have w0 : word u.mem base d = s₂.gpr .r8 := by
      rw [mu, O₅.word (by omega) (by omega), hm₅, m₃, word_writeW_self]
    have w1 : word u.mem base (d + 8) = s₅.gpr .r8 := by rw [mu, word_writeW_self]
    have e₄ : s₄.gpr .r8 = word s.mem base (d + 8) := by
      rw [l₄, m₃, O₃.word (by omega) (by omega), hm₂]
    have hrbp : s₁.gpr .rbp = s.gpr .rbp := k₁.1 .rbp (by decide)
    have h1 := add_carry (s₁.gpr .r8) (s₁.gpr .rbp)
    simp only [wordsVal, Nat.add_zero, Nat.mul_zero]
    rw [w0, w1, a₂, a₅, e₄, l₁, hrbp]
    rw [l₁, hrbp] at h1
    have := (word s.mem base d + s.gpr .rbp).isLt
    generalize decide (2 ^ 64 ≤ (word s.mem base d).toNat + (s.gpr .rbp).toNat) = c at *
    have h2 := adc_carry (word s.mem base (d + 8)) 0 c
    generalize decide (2 ^ 64 ≤ (word s.mem base (d + 8)).toNat + (0 : BitVec 64).toNat + c.toNat) = c' at h2
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at h2
    have := (word s.mem base (d + 8) + 0 + (BitVec.ofBool c).setWidth 64).isLt
    have := Bool.toNat_le c
    have := Bool.toNat_le c'
    omega
  · rw [mu, O₅ x (by omega), hm₅, m₃, O₃ x (by omega), hm₂]

theorem zext0' : (0 : BitVec 32).setWidth 64 = 0 := by decide
theorem sextm1 : (-1 : BitVec 32).signExtend 64 = BitVec.allOnes 64 := by decide

/-- `[U + 8 n] = 0`. -/
theorem zeroTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {U n : Nat}
    (hU : U + 8 * n + 8 ≤ size) :
    WP isa (.block (zeroTop U n)) s fun u =>
      word u.mem base (U + 8 * n) = 0 ∧ KeepRegs [.r8] s u ∧ Outside base (U + 8 * n) 8 s.mem u.mem := by
  have hn := hs.nowrap
  rw [zeroTop, ← List.singleton_append, WP.block_append_iff]
  have h : WP isa (.block [.mov32 .r8 (.imm 0)]) s fun v => v.gpr .r8 = 0 ∧ Keeps [.r8] s v := by
    irun [zext0']
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h fun s₁ ⟨g₁, k₁⟩ => ?_
  refine WP.mono (storeReg_ok (hs.of_keeps k₁ (by decide)) .r8 (d := U + 8 * n) (by omega))
    fun u ⟨mu, _, _, ku⟩ => ⟨by rw [mu, word_writeW_self, g₁], (Keeps.regs k₁).trans (ku.mono (by decide)),
      by rw [mu, ← k₁.2.1]; exact writeW_outside _ _ _ (by omega)⟩

theorem masked_allOnes (v : Nat) : masked (BitVec.allOnes 64) v = v := by simp [masked]

/-- A number of words and its carry out. -/
theorem mod_of_carry {X Y M c : Nat} (h : X + M * c = Y) (hX : X < M) : X = Y % M := by
  rw [← h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hX]

/-- `2^(64 (n + 1)) = A B` with `A = 2^(64 n)` and `B = 2^64`. -/
theorem pow64_succ' (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by
  rw [pow64_succ, Nat.mul_comm]

/-- `[t + 8] += p` (`n + 1` words, modulo `2^(64 (n + 1))`) if it is negative. -/
theorem addIfNeg_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t U : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hU : U + 8 * (M.n + 1) ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (htU : t + 8 * (M.n + 2) ≤ U ∨ U + 8 * (M.n + 1) ≤ t)
    (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (hU0 : word s.mem base (U + 8 * M.n) = 0) :
    WP isa (.block (addIfNeg M t U)) s fun u =>
      wordsVal u.mem base (t + 8) (M.n + 1) =
        (wordsVal s.mem base (t + 8) (M.n + 1) +
          if 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base (t + 8) (M.n + 1) then wordsVal s.mem base M.mo M.n
          else 0) % (2 ^ (64 * M.n) * 2 ^ 64) ∧
      KeepRegs [.rax, .rdx, .r8, .r13] s u ∧ Unch base [(t + 8, 8 * (M.n + 1)), (U, 8 * M.n)] s.mem u.mem := by
  have hn := hs.nowrap
  rw [addIfNeg, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rdx (d := t + 8 * (M.n + 1)) (by omega)) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .r13) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (maskCopy_ok (m := .r13) (by decide) M.n hs₂ (dst := U) (src := M.mo)
    (by rw [g₂]; exact smask_isMask _) (by omega) hmo (by omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (chainWAdd_ok (M.n + 1) hs₃ (op := .add) (c := false) (t := t + 8) (a := t + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega)) (by omega) (by omega) (by omega) (.inl rfl) (by unfold Near; omega))
    fun u ⟨c, _, e, ku, Ou⟩ => ⟨?_, (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((k₃.mono (by decide)).trans (ku.mono (by decide))), ?_⟩
  · have hR : wordsVal s₃.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) := by
      rw [O₃.wordsVal (by omega) (by omega), hm₂]
    have hUv : wordsVal s₃.mem base U (M.n + 1) =
        if 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base (t + 8) (M.n + 1) then wordsVal s.mem base M.mo M.n
        else 0 := by
      rw [wordsVal_succ_top, e₃, O₃.word (by omega) (by omega), hm₂, hU0, g₂, masked_smask, l₁,
        show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega, show (0 : BitVec 64).toNat = 0 from rfl,
        Nat.mul_zero, Nat.add_zero]
      by_cases h : 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base (t + 8) (M.n + 1)
      · have h' := (sgn_iff s.mem base (t + 8) M.n).mpr h
        simp only [h, h', ↓reduceIte]
      · have h' := mt (sgn_iff s.mem base (t + 8) M.n).mp h
        simp only [h, h', ↓reduceIte]
    simp only [Bool.toNat_false, Nat.add_zero] at e
    rw [hR, hUv, pow64_succ'] at e
    have hlt : wordsVal u.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
    exact mod_of_carry e hlt
  · rw [← hm₂]
    refine (O₃.unch.trans Ou.unch).mono fun v hv => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    rcases hv with h | h <;> simp [h]

/-- `[t + 8] -= p` (`n + 1` words, modulo `2^(64 (n + 1))`). -/
theorem subP_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (M : Mod) {t U : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hU : U + 8 * (M.n + 1) ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (htU : t + 8 * (M.n + 2) ≤ U ∨ U + 8 * (M.n + 1) ≤ t)
    (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    (hU0 : word s.mem base (U + 8 * M.n) = 0) :
    WP isa (.block (subP M t U)) s fun u =>
      (wordsVal u.mem base (t + 8) (M.n + 1) + wordsVal s.mem base M.mo M.n) % (2 ^ (64 * M.n) * 2 ^ 64) =
        wordsVal s.mem base (t + 8) (M.n + 1) ∧
      KeepRegs [.r8, .r13] s u ∧ Unch base [(t + 8, 8 * (M.n + 1)), (U, 8 * M.n)] s.mem u.mem := by
  have hn := hs.nowrap
  rw [subP, List.append_assoc, WP.block_append_iff]
  have h : WP isa (.block [.mov .r13 (.imm (-1))]) s fun v => v.gpr .r13 = BitVec.allOnes 64 ∧ Keeps [.r13] s v := by
    irun [sextm1]
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h fun s₁ ⟨g₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maskCopy_ok (m := .r13) (by decide) M.n hs₁ (dst := U) (src := M.mo)
    (by rw [g₁]; exact Or.inr rfl) (by omega) hmo (by omega)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (chainWSub_ok (M.n + 1) hs₂ (op := .sub) (c := false) (t := t + 8) (a := t + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega)) (by omega) (by omega) (by omega) (.inl rfl) (by unfold Near; omega))
    fun u ⟨c, _, e, ku, Ou⟩ => ⟨?_, ((Keeps.regs k₁).mono (by decide)).trans
      ((k₂.mono (by decide)).trans (ku.mono (by decide))), ?_⟩
  · have hR : wordsVal s₂.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) := by
      rw [O₂.wordsVal (by omega) (by omega), k₁.2.1]
    have hUv : wordsVal s₂.mem base U (M.n + 1) = wordsVal s.mem base M.mo M.n := by
      rw [wordsVal_succ_top, e₂, O₂.word (by omega) (by omega), k₁.2.1, hU0, g₁, masked_allOnes,
        show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero]
    simp only [Bool.toNat_false, Nat.add_zero] at e
    rw [hR, hUv, pow64_succ'] at e
    have hlt : wordsVal s.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
      rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
    exact (mod_of_carry e.symm hlt).symm
  · rw [← k₁.2.1]
    refine (O₂.unch.trans Ou.unch).mono fun v hv => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    rcases hv with h | h <;> simp [h]

/-- A low part below `A` and a high part modulo `Q`. -/
theorem low_high_mod {L A y Q : Nat} (hL : L < A) (hQ : 0 < Q) : L + A * (y % Q) = (L + A * y) % (A * Q) := by
  have h1 : L + A * (y % Q) < A * Q := by
    have h2 : A * (y % Q + 1) ≤ A * Q := Nat.mul_le_mul_left A (Nat.mod_lt y hQ)
    rw [Nat.mul_succ] at h2
    omega
  conv => rhs; rw [← Nat.mod_add_div y Q, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt h1).symm

/-- Apart from each range of a list written out. -/
local macro "apart" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
  forall_eq_or_imp, forall_eq] <;> omega))

/-- `[dst] = mred p m T` (`n` words), for `[t]` (`n + 1` words) holding `T`, `|T| ≤ 2^63 p`. -/
theorem mredC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkW M size p s.mem base) {dst t U : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hd : dst + 8 * M.n ≤ size) (hU : U + 8 * (M.n + 1) ≤ size)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t) (hdt : dst + 8 * M.n ≤ t ∨ t + 8 * (M.n + 2) ≤ dst)
    (htU : t + 8 * (M.n + 2) ≤ U ∨ U + 8 * (M.n + 1) ≤ t) (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    {T : Int} (hT : |T| ≤ 2 ^ 63 * p)
    (hW : (wordsVal s.mem base t (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (mredC M dst t U)) s fun u =>
      (wordsVal u.mem base dst M.n : Int) = Divstep.mred p M.minv.toNat T ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s u ∧
      Unch base [(t, 8 * (M.n + 2)), (U, 8 * (M.n + 1)), (dst, 8 * M.n)] s.mem u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [mredC, List.append_assoc]
  -- `rcx = k`.
  rw [WP.block_append_iff]
  refine WP.mono (kOf_ok hs M (t := t) (by omega)) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  -- `[t]` sign-extended.
  rw [WP.block_append_iff]
  refine WP.mono (sextTop_ok hs₁ M ht) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- `[t] += k p`.
  rw [WP.block_append_iff]
  refine WP.mono (memRow_ok hs₂ (k := M.n) (t := t) (d := M.mo) (by omega) hmo (by omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry2_ok hs₃ (d := t + 8 * M.n) (by omega)) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- `[U + 8 n] = 0`.
  rw [WP.block_append_iff]
  refine WP.mono (zeroTop_ok hs₄ (U := U) (n := M.n) (by omega)) fun s₅ ⟨z₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have U₅ : Unch base [(t, 8 * (M.n + 2)), (U + 8 * M.n, 8)] s.mem s₅.mem := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [O₅ x (by omega), O₄ x (by omega), O₃ x (by omega), O₂ x (by omega), k₁.2.1]
  have P₅ : wordsVal s₅.mem base M.mo M.n = p := by rw [U₅.wordsVal (by apart) (by omega), hP]
  -- `R₁ = R + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (addIfNeg_ok hs₅ M ht hU hmo htU hUm htm z₅) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have P₆ : wordsVal s₆.mem base M.mo M.n = p := by rw [O₆.wordsVal (by apart) (by omega), P₅]
  have z₆ : word s₆.mem base (U + 8 * M.n) = 0 := by rw [O₆.word (by apart) (by omega), z₅]
  -- `R₂ = R₁ - p`.
  rw [WP.block_append_iff]
  refine WP.mono (subP_ok hs₆ M ht hU hmo htU hUm z₆) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  have P₇ : wordsVal s₇.mem base M.mo M.n = p := by rw [O₇.wordsVal (by apart) (by omega), P₆]
  have z₇ : word s₇.mem base (U + 8 * M.n) = 0 := by rw [O₇.word (by apart) (by omega), z₆]
  -- `R₃ = R₂ + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (addIfNeg_ok hs₇ M ht hU hmo htU hUm htm z₇) fun s₈ ⟨e₈, k₈, O₈⟩ => ?_
  have hs₈ := hs₇.of_keepRegs k₈ (by decide)
  -- `[dst] = R₃`.
  refine WP.mono (copy_ok M.n hs₈ (o := dst) (a := t + 8) hd (by omega) (by omega)) fun u ⟨eu, ku, Ou⟩ => ?_
  refine ⟨?_, (((((((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (k₅.mono (by decide))).trans (k₆.mono (by decide))).trans
    (k₇.mono (by decide))).trans (k₈.mono (by decide))).trans (ku.mono (by decide)), fun x hx => ?_⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [Ou x (by omega), O₈ x (by apart), O₇ x (by apart), O₆ x (by apart), U₅ x (by apart)]
  -- The arithmetic.
  have hp0 : 0 < p := by
    have := hM.inv
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at this; exact absurd this (by decide)
    · exact h
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hrcx : s₂.gpr .rcx = s₁.gpr .rcx := k₂.gpr .rcx (by decide)
  -- `E`.
  have P₂ : wordsVal s₂.mem base M.mo M.n = p := by rw [O₂.wordsVal (by omega) (by omega), hm₁, hP]
  rw [hrcx, P₂] at e₃
  rw [hm₁, pow64_succ', sgnW_top] at e₂
  have eL : wordsVal s₄.mem base t M.n = wordsVal s₃.mem base t M.n := O₄.wordsVal (by omega) (by omega)
  have eH : wordsVal s₃.mem base (t + 8 * M.n) 2 = wordsVal s₂.mem base (t + 8 * M.n) 2 :=
    O₃.wordsVal (by omega) (by omega)
  have sp₂ := wordsVal_split s₂.mem base t M.n 2
  have sp₄ := wordsVal_split s₄.mem base t M.n 2
  rw [e₄, eH, eL] at sp₄
  have hL₃ := wordsVal_lt s₃.mem base t M.n
  have hE : wordsVal s₄.mem base t (M.n + 2) =
      (wordsVal s.mem base t (M.n + 1) + 2 ^ (64 * M.n) * 2 ^ 64 *
        (if 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base t (M.n + 1) then 2 ^ 64 - 1 else 0) +
        (s₁.gpr .rcx).toNat * p) % (2 ^ (64 * M.n) * 2 ^ 64 * 2 ^ 64) := by
    rw [sp₄, low_high_mod hL₃ (by decide), Nat.mul_assoc (2 ^ (64 * M.n)) (2 ^ 64) (2 ^ 64),
      show (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 by rw [← Nat.pow_add], ← e₂, sp₂]
    generalize (2 : Nat) ^ (64 * M.n) * 2 ^ 128 = Q
    generalize (s₃.gpr .rbp).toNat = r at *
    generalize (s₁.gpr .rcx).toNat * p = kp at *
    generalize (2 : Nat) ^ (64 * M.n) = A at *
    rw [Nat.mul_add, show wordsVal s₃.mem base t M.n + (A * wordsVal s₂.mem base (t + 8 * M.n) 2 + A * r) =
      wordsVal s₂.mem base t M.n + A * wordsVal s₂.mem base (t + 8 * M.n) 2 + kp by omega]
  -- `R = E / 2^64` and the corrections.
  have eR : wordsVal s₄.mem base t (M.n + 2) =
      (word s₄.mem base t).toNat + 2 ^ 64 * wordsVal s₄.mem base (t + 8) (M.n + 1) := rfl
  have hR : wordsVal s₄.mem base (t + 8) (M.n + 1) = wordsVal s₄.mem base t (M.n + 2) / 2 ^ 64 := by
    rw [eR, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (BitVec.isLt _), Nat.zero_add]
  have R₅ : wordsVal s₅.mem base (t + 8) (M.n + 1) = wordsVal s₄.mem base (t + 8) (M.n + 1) :=
    O₅.wordsVal (by omega) (by omega)
  rw [R₅, P₅] at e₆
  rw [P₆] at e₇
  rw [P₇] at e₈
  have hk : (s₁.gpr .rcx).toNat = wordsVal s.mem base t (M.n + 1) % 2 ^ 64 * M.minv.toNat % 2 ^ 64 := by
    rw [x₁, wordsVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
  have hW1 : wordsVal s.mem base t (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  have hR₂1 : wordsVal s₇.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  have key := Divstep.mred_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := M.minv.toNat)
    (t := T) (W := wordsVal s.mem base t (M.n + 1)) (k := (s₁.gpr .rcx).toNat)
    (E := wordsVal s₄.mem base t (M.n + 2)) (R := wordsVal s₄.mem base (t + 8) (M.n + 1))
    (R₁ := wordsVal s₆.mem base (t + 8) (M.n + 1)) (R₂ := wordsVal s₇.mem base (t + 8) (M.n + 1))
    (R₃ := wordsVal s₈.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hp0 hpA hM.inv hT hW1 (by rw [← pow64_succ']; exact hW) hk hE hR e₆ hR₂1 e₇ e₈
  obtain ⟨r0, r1⟩ := Divstep.mred_range (p := p) (m := M.minv.toNat) (t := T) (by exact_mod_cast hp0)
    (by exact_mod_cast hM.inv) hT
  have hR₃ : wordsVal s₈.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) := by omega
  have hlow : wordsVal s₈.mem base (t + 8) M.n = wordsVal s₈.mem base (t + 8) (M.n + 1) := by
    have h := congrArg (· % 2 ^ (64 * M.n)) (wordsVal_succ_top s₈.mem base (t + 8) M.n)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _), Nat.mod_eq_of_lt hR₃] at h
    exact h.symm
  rw [eu, hlow, key]

end VG.Proof.Weierstrass.X86_64
