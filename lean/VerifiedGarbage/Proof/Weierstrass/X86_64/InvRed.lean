module

import VerifiedGarbage.Proof.Weierstrass.X86_64.InvWords
import VerifiedGarbage.Proof.Divstep.TcS
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Weierstrass.InvMask
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import VerifiedGarbage.Proof.Divstep.Alg
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import Aesop.BuiltinRules

/-!
# Inversion by divsteps on x86-64: the reduction of the coefficients

The reduction `mredS` of a signed number of `n + 1` words to `Divstep.mredRaw`
(`mredS_ok`): `k = t₀ m`, `[t]` sign-extended and plus `k p`, then its words
`1 … n + 1`; and the normalization `normC` of a signed number of `n + 1` words
in `(-p, 2p)` to `Divstep.norm` (`normC_ok`), by carry chains with `p` under masks.
-/

@[expose] public section

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
  refine WP.mono (movMem_ok hs .rdx (d := t + 8 * M.n) (by omega_using [ht])) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .r8) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  refine WP.mono (storeReg_ok hs₂ .r8 (d := t + 8 * (M.n + 1)) (by omega_using [ht])) fun u ⟨mu, _, _, ku⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  have O := writeW_outside s₂.mem base (d := t + 8 * (M.n + 1)) (s₂.gpr .r8) (by omega_using [ht, hn])
  refine ⟨?_, (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
    (ku.mono (by decide)), by rw [mu, ← hm₂]; exact O⟩
  rw [show M.n + 2 = M.n + 1 + 1 from rfl, mu, wordsVal_succ_top, word_writeW_self,
    O.wordsVal (by omega_using []) (by omega_using [ht, hn]), hm₂, g₂, smask_toNat, l₁]

/-- `[d] += rbp` (two words), modulo `2^128`. -/
theorem carry2_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 16 ≤ size) :
    WP isa (.block (carry2 d)) s fun u =>
      wordsVal u.mem base d 2 = (wordsVal s.mem base d 2 + (s.gpr .rbp).toNat) % 2 ^ 128 ∧
      KeepRegs [.r8] s u ∧ Outside base d 16 s.mem u.mem := by
  have hn := hs.nowrap
  rw [carry2, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 (d := d) (by omega_using [hd])) fun s₁ ⟨l₁, _, k₁⟩ => ?_
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
  refine WP.mono (storeReg_ok hs₂ .r8 (d := d) (by omega_using [hd])) fun s₃ ⟨m₃, g₃, f₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs₃ .r8 (d := d + 8) (by omega_using [hd])) fun s₄ ⟨l₄, f₄, k₄⟩ => ?_
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
  refine WP.mono (storeReg_ok hs₅ .r8 (d := d + 8) (by omega_using [hd])) fun u ⟨mu, _, _, ku⟩ => ?_
  have O₃ := writeW_outside s₂.mem base (d := d) (s₂.gpr .r8) (by omega_using [hd, hn])
  have O₅ := writeW_outside s₅.mem base (d := d + 8) (s₅.gpr .r8) (by omega_using [hd, hn])
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  have hm₅ : s₅.mem = s₃.mem := by rw [k₅.2.1, k₄.2.1]
  refine ⟨?_, ((((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (k₃.mono (by decide))).trans (((Keeps.regs k₄).trans
    (Keeps.regs k₅)).trans (ku.mono (by decide)))).mono (by decide), fun x hx => ?_⟩
  · have w0 : word u.mem base d = s₂.gpr .r8 := by
      rw [mu, O₅.word (by omega_using []) (by omega_using [hd, hn]), hm₅, m₃, word_writeW_self]
    have w1 : word u.mem base (d + 8) = s₅.gpr .r8 := by rw [mu, word_writeW_self]
    have e₄ : s₄.gpr .r8 = word s.mem base (d + 8) := by
      rw [l₄, m₃, O₃.word (by omega_using []) (by omega_using [hd, hn]), hm₂]
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
    omega_using [h1, h2]
  · rw [mu, O₅ x (by omega_using [hx]), hm₅, m₃, O₃ x (by omega_using [hx]), hm₂]

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
  refine WP.mono (storeReg_ok (hs.of_keeps k₁ (by decide)) .r8 (d := U + 8 * n) (by omega_using [hU]))
    fun u ⟨mu, _, _, ku⟩ => ⟨by rw [mu, word_writeW_self, g₁], (Keeps.regs k₁).trans (ku.mono (by decide)),
      by rw [mu, ← k₁.2.1]; exact writeW_outside _ _ _ (by omega_using [hU, hn])⟩

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
  refine WP.mono (movMem_ok hs .rdx (d := t + 8 * (M.n + 1)) (by omega_arith)) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₁ (d := .r13) (src := .rdx) (by decide)) fun s₂ ⟨g₂, k₂⟩ => ?_
  have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := by rw [k₂.2.1, k₁.2.1]
  rw [WP.block_append_iff]
  refine WP.mono (maskCopy_ok (m := .r13) (by decide) M.n hs₂ (dst := U) (src := M.mo)
    (by rw [g₂]; exact smask_isMask _) (by omega_arith) hmo (by omega_arith)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (chainWAdd_ok (M.n + 1) hs₃ (op := .add) (c := false) (t := t + 8) (a := t + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith) (.inl rfl) (by unfold Near; omega_arith))
    fun u ⟨c, _, e, ku, Ou⟩ => ⟨?_, (((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((k₃.mono (by decide)).trans (ku.mono (by decide))), ?_⟩
  · have hR : wordsVal s₃.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) := by
      rw [O₃.wordsVal (by omega_arith) (by omega_arith), hm₂]
    have hUv : wordsVal s₃.mem base U (M.n + 1) =
        if 2 ^ (64 * M.n) * 2 ^ 63 ≤ wordsVal s.mem base (t + 8) (M.n + 1) then wordsVal s.mem base M.mo M.n
        else 0 := by
      rw [wordsVal_succ_top, e₃, O₃.word (by omega_arith) (by omega_arith), hm₂, hU0, g₂, masked_smask, l₁,
        show t + 8 * (M.n + 1) = t + 8 + 8 * M.n by omega_arith, show (0 : BitVec 64).toNat = 0 from rfl,
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
    (by rw [g₁]; exact Or.inr rfl) (by omega_using [hU]) hmo (by omega_using [hUm])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (chainWSub_ok (M.n + 1) hs₂ (op := .sub) (c := false) (t := t + 8) (a := t + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega_using [])) (by omega_using [ht]) (by omega_using [ht]) (by omega_using [hU]) (.inl rfl) (by unfold Near; omega_using [htU]))
    fun u ⟨c, _, e, ku, Ou⟩ => ⟨?_, ((Keeps.regs k₁).mono (by decide)).trans
      ((k₂.mono (by decide)).trans (ku.mono (by decide))), ?_⟩
  · have hR : wordsVal s₂.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) := by
      rw [O₂.wordsVal (by omega_using [htU]) (by omega_using [ht, hn]), k₁.2.1]
    have hUv : wordsVal s₂.mem base U (M.n + 1) = wordsVal s.mem base M.mo M.n := by
      rw [wordsVal_succ_top, e₂, O₂.word (by omega_using []) (by omega_using [hU, hn]), k₁.2.1, hU0, g₁, masked_allOnes,
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
    omega_using [hL, h2]
  conv => rhs; rw [← Nat.mod_add_div y Q, Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc, Nat.add_mul_mod_self_left]
  exact (Nat.mod_eq_of_lt h1).symm

/-- Apart from each range of a list written out. -/
tactic_template "inv_apart_arith" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
                   forall_eq_or_imp, forall_eq] <;> omega_arith))

/-- `[dst] = mredRaw p m T` (`n + 1` words, signed), for `[t]` (`n + 1` words) holding `T`,
`|T| ≤ 2^63 p`. -/
theorem mredS_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkW M size p s.mem base) {dst t : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hd : dst + 8 * (M.n + 1) ≤ size)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (hdt : dst + 8 * (M.n + 1) ≤ t ∨ t + 8 * (M.n + 2) ≤ dst)
    {T : Int} (hT : |T| ≤ 2 ^ 63 * p)
    (hW : (wordsVal s.mem base t (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (mredS M dst t)) s fun u =>
      (wordsVal u.mem base dst (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
        Divstep.mredRaw p M.minv.toNat T % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s u ∧
      Unch base [(t, 8 * (M.n + 2)), (dst, 8 * (M.n + 1))] s.mem u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [mredS, List.append_assoc]
  -- `rcx = k`.
  rw [WP.block_append_iff]
  refine WP.mono (kOf_ok hs M (t := t) (by omega_using [ht])) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  -- `[t]` sign-extended.
  rw [WP.block_append_iff]
  refine WP.mono (sextTop_ok hs₁ M ht) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  -- `[t] += k p`.
  rw [WP.block_append_iff]
  refine WP.mono (memRow_ok hs₂ (k := M.n) (t := t) (d := M.mo) (by omega_using [ht]) hmo (by omega_using [htm])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry2_ok hs₃ (d := t + 8 * M.n) (by omega_using [ht])) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- `[dst] = R`.
  refine WP.mono (copy_ok (M.n + 1) hs₄ (o := dst) (a := t + 8) hd (by omega_using [ht]) (by omega_using [hdt]))
    fun u ⟨eu, ku, Ou⟩ => ?_
  refine ⟨?_, (((((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))).trans
    (k₃.mono (by decide))).trans (k₄.mono (by decide))).trans (ku.mono (by decide)), fun x hx => ?_⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [Ou x (by omega_using [hx]), O₄ x (by omega_using [hx]), O₃ x (by omega_using [hx]), O₂ x (by omega_using [hx]),
      k₁.2.1]
  -- The arithmetic.
  have hp0 : 0 < p := by
    have := hM.inv
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, Nat.zero_mul] at this; exact absurd this (by decide)
    · exact h
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hrcx : s₂.gpr .rcx = s₁.gpr .rcx := k₂.gpr .rcx (by decide)
  have P₂ : wordsVal s₂.mem base M.mo M.n = p := by rw [O₂.wordsVal (by omega_using [htm]) (by omega_using [hn, hmo]), hm₁, hP]
  rw [hrcx, P₂] at e₃
  rw [hm₁, pow64_succ', sgnW_top] at e₂
  have eL : wordsVal s₄.mem base t M.n = wordsVal s₃.mem base t M.n := O₄.wordsVal (by omega_using []) (by omega_using [ht, hn])
  have eH : wordsVal s₃.mem base (t + 8 * M.n) 2 = wordsVal s₂.mem base (t + 8 * M.n) 2 :=
    O₃.wordsVal (by omega_using []) (by omega_using [ht, hn])
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
      wordsVal s₂.mem base t M.n + A * wordsVal s₂.mem base (t + 8 * M.n) 2 + kp by omega_using [e₃]]
  have eR : wordsVal s₄.mem base t (M.n + 2) =
      (word s₄.mem base t).toNat + 2 ^ 64 * wordsVal s₄.mem base (t + 8) (M.n + 1) := rfl
  have hR : wordsVal s₄.mem base (t + 8) (M.n + 1) = wordsVal s₄.mem base t (M.n + 2) / 2 ^ 64 := by
    rw [eR, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (BitVec.isLt _), Nat.zero_add]
  have hk : (s₁.gpr .rcx).toNat = wordsVal s.mem base t (M.n + 1) % 2 ^ 64 * M.minv.toNat % 2 ^ 64 := by
    rw [x₁, wordsVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
  have hW1 : wordsVal s.mem base t (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  have key := Divstep.mredRaw_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (m := M.minv.toNat)
    (t := T) (W := wordsVal s.mem base t (M.n + 1)) (k := (s₁.gpr .rcx).toNat)
    (E := wordsVal s₄.mem base t (M.n + 2)) (R := wordsVal s₄.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hp0 hpA hM.inv hT hW1 (by rw [← pow64_succ']; exact hW) hk hE hR
  rw [eu, pow64_succ']
  exact key

/-- `[t + 8]` (`n + 1` words) holding `r ∈ (-p, 2p)` brought to `norm p r` (its low `n` words). -/
theorem normC_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {p : Nat}
    (hM : ModOkW M size p s.mem base) {t U : Nat}
    (ht : t + 8 * (M.n + 2) ≤ size) (hU : U + 8 * (M.n + 1) ≤ size)
    (htm : t + 8 * (M.n + 2) ≤ M.mo ∨ M.mo + 8 * M.n ≤ t)
    (htU : t + 8 * (M.n + 2) ≤ U ∨ U + 8 * (M.n + 1) ≤ t) (hUm : U + 8 * (M.n + 1) ≤ M.mo ∨ M.mo + 8 * M.n ≤ U)
    {r : Int} (hr0 : -(p : Int) < r) (hr1 : r < 2 * p)
    (hR : (wordsVal s.mem base (t + 8) (M.n + 1) : Int) % ((2 ^ (64 * (M.n + 1)) : Nat) : Int) =
      r % ((2 ^ (64 * (M.n + 1)) : Nat) : Int)) :
    WP isa (.block (normC M t U)) s fun u =>
      (wordsVal u.mem base (t + 8) M.n : Int) = Divstep.norm p r ∧
      KeepRegs [.rax, .rdx, .r8, .r13] s u ∧
      Unch base [(t + 8, 8 * (M.n + 1)), (U, 8 * (M.n + 1))] s.mem u.mem := by
  have hn := hs.nowrap
  have hP : wordsVal s.mem base M.mo M.n = p := hM.val
  have hmo := hM.mo
  simp only [normC, List.append_assoc]
  -- `[U + 8 n] = 0`.
  rw [WP.block_append_iff]
  refine WP.mono (zeroTop_ok hs (U := U) (n := M.n) (by omega_using [hU])) fun s₅ ⟨z₅, k₅, O₅⟩ => ?_
  have hs₅ := hs.of_keepRegs k₅ (by decide)
  have P₅ : wordsVal s₅.mem base M.mo M.n = p := by
    rw [O₅.wordsVal (by omega_using [hUm]) (by omega_using [hn, hmo]), hP]
  have R₅ : wordsVal s₅.mem base (t + 8) (M.n + 1) = wordsVal s.mem base (t + 8) (M.n + 1) :=
    O₅.wordsVal (by omega_using [htU]) (by omega_using [ht, hn])
  -- `R₁ = R + (p if negative)`.
  rw [WP.block_append_iff]
  refine WP.mono (addIfNeg_ok hs₅ M ht hU hmo htU hUm htm z₅) fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have P₆ : wordsVal s₆.mem base M.mo M.n = p := by rw [O₆.wordsVal (by inv_apart_arith) (by omega_using [hn, hmo]), P₅]
  have z₆ : word s₆.mem base (U + 8 * M.n) = 0 := by rw [O₆.word (by inv_apart_arith) (by omega_using [hU, hn]), z₅]
  -- `R₂ = R₁ - p`.
  rw [WP.block_append_iff]
  refine WP.mono (subP_ok hs₆ M ht hU hmo htU hUm z₆) fun s₇ ⟨e₇, k₇, O₇⟩ => ?_
  have hs₇ := hs₆.of_keepRegs k₇ (by decide)
  have P₇ : wordsVal s₇.mem base M.mo M.n = p := by rw [O₇.wordsVal (by inv_apart_arith) (by omega_using [hn, hmo]), P₆]
  have z₇ : word s₇.mem base (U + 8 * M.n) = 0 := by rw [O₇.word (by inv_apart_arith) (by omega_using [hU, hn]), z₆]
  -- `R₃ = R₂ + (p if negative)`.
  refine WP.mono (addIfNeg_ok hs₇ M ht hU hmo htU hUm htm z₇) fun u ⟨e₈, k₈, O₈⟩ => ?_
  refine ⟨?_, ((k₅.mono (by decide)).trans (k₆.mono (by decide))).trans ((k₇.mono (by decide)).trans
    (k₈.mono (by decide))), fun x hx => ?_⟩
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [O₈ x (by inv_apart_arith), O₇ x (by inv_apart_arith), O₆ x (by inv_apart_arith), O₅ x (by omega_using [hx])]
  have hpA : p < 2 ^ (64 * M.n) := hP ▸ wordsVal_lt _ _ _ _
  rw [R₅, P₅] at e₆
  rw [P₆] at e₇
  rw [P₇] at e₈
  have hR₂1 : wordsVal s₇.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  have hR1 : wordsVal s.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) * 2 ^ 64 := by
    rw [← pow64_succ']; exact wordsVal_lt _ _ _ _
  have key := Divstep.norm_nat (A := 2 ^ (64 * M.n)) (B := 2 ^ 64) (H := 2 ^ 63) (p := p) (r := r)
    (R := wordsVal s.mem base (t + 8) (M.n + 1)) (R₁ := wordsVal s₆.mem base (t + 8) (M.n + 1))
    (R₂ := wordsVal s₇.mem base (t + 8) (M.n + 1)) (R₃ := wordsVal u.mem base (t + 8) (M.n + 1))
    rfl rfl (Nat.two_pow_pos _) hpA hr0 hr1 hR1 (by rw [← pow64_succ']; exact hR) e₆ hR₂1 e₇ e₈
  obtain ⟨r0, r1⟩ := Divstep.norm_range hr0 hr1
  have hR₃ : wordsVal u.mem base (t + 8) (M.n + 1) < 2 ^ (64 * M.n) := by
    have : (wordsVal u.mem base (t + 8) (M.n + 1) : Int) < 2 ^ (64 * M.n) := by
      rw [key]; have : (p : Int) < 2 ^ (64 * M.n) := by exact_mod_cast hpA
      omega
    exact_mod_cast this
  have hlow : wordsVal u.mem base (t + 8) M.n = wordsVal u.mem base (t + 8) (M.n + 1) := by
    have h := congrArg (· % 2 ^ (64 * M.n)) (wordsVal_succ_top u.mem base (t + 8) M.n)
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (wordsVal_lt _ _ _ _), Nat.mod_eq_of_lt hR₃] at h
    exact h.symm
  rw [hlow, key]

end VG.Proof.Weierstrass.X86_64
