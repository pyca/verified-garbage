module

public import VerifiedGarbage.Impl.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags

/-! # Correct masks for arbitrary-width DSA components -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
open VG.Proof.Ecdsa.X86 VG.Impl.Dsa.X86

theorem nonzero_ok (n : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) :
    WP isa (.block (nonzero n a)) s fun s' =>
      s'.gpr .edx = mask32 (wordsVal s.mem base a n ≠ 0) ∧ Keeps [.ecx, .edx] s s' ∧ s'.mem = s.mem := by
  simp only [nonzero, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs (d := a) (by omega)) fun s₁ u₁ _ => ?_
  have hs₁ := hs.of_keeps u₁.keeps (by decide)
  refine WP.block_append (WP.mono (ors_ok hs₁ (2 * n - 1) (by omega)) fun s₂ ⟨e₂, k₂, m₂⟩ => ?_)
  rw [u₁.gpr, u₁.mem] at e₂
  have hz : s₂.gpr .edx = 0 ↔ wordsVal s.mem base a n = 0 := by
    rw [e₂, wordsVal_eq_val32, val32_eq_zero_iff]
    have hw : (s.mem.readW (off base a) 32 = 0) ↔ w32 s.mem base a = 0 :=
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hw]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega)
    · intro h
      exact ⟨by simpa using h 0 (by omega), fun j hj => h (j + 1) (by omega)⟩
  refine wp_movS rfl fun s₃ u₃ _ => ?_
  refine wp_subS rfl fun s₄ u₄ c₄ => ?_
  refine wp_sbbS rfl c₄ fun s₅ u₅ _ => WP.block_nil ⟨?_, ?_, by rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]⟩
  · rw [u₅.gpr, sbb_mask, u₃.gpr, u₃.other _ (by decide)]
    have : ((0 : BitVec 32).toNat < (s₂.gpr .edx).toNat) ↔ s₂.gpr .edx ≠ 0 :=
      ⟨fun h e => by rw [e] at h; exact Nat.lt_irrefl _ h,
        fun h => Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq e)⟩
    simp only [mask32, decide_eq_true_eq, this, ne_eq, hz]
  · exact ((((u₁.keeps.mono (by decide)).widen k₂).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps

theorem lessThan_ok (n : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (hm : m + 8 * n ≤ size) :
    WP isa (.block (lessThan n a m)) s fun s' =>
      s'.gpr .eax = mask32 (wordsVal s.mem base a n < wordsVal s.mem base m n) ∧
      Keeps [.eax, .edx] s s' ∧ s'.mem = s.mem := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
  change WP isa (.block ((List.range (2 * n)).flatMap (ltStep a m) ++
    ([.alu .sbb .eax (.reg .eax)] : List Instr))) s _
  rw [hk]
  refine WP.block_append (WP.mono (ltSteps_ok hs k (by omega) (by omega)) fun s₁ ⟨c₁, k₁, m₁⟩ => ?_)
  refine wp_sbbS rfl c₁ fun s₂ u₂ _ => WP.block_nil ⟨?_, (k₁.mono (by decide)).widen u₂.keeps,
    by rw [u₂.mem, m₁]⟩
  rw [u₂.gpr, sbb_mask, wordsVal_eq_val32, wordsVal_eq_val32, hk]
  simp only [mask32, decide_eq_true_eq]

theorem equal_ok (n : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a b : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (hb : b + 8 * n ≤ size) :
    WP isa (.block (equal n a b)) s fun t =>
      t.gpr .edx = mask32 (wordsVal s.mem base a n = wordsVal s.mem base b n) ∧
      Keeps [.eax, .ebx, .edx] s t ∧ t.mem = s.mem := by
  simp only [equal, List.append_assoc, List.singleton_append]
  refine WP.block_append (WP.mono (lessThan_ok n hs hn ha hb) fun u ⟨eu, ku, mu⟩ => ?_)
  refine wp_movS rfl fun v uv _ => ?_
  have kv : Keeps [.eax, .ebx, .edx] s v := (ku.mono (by decide)).widen uv.keeps
  refine WP.block_append (WP.mono (lessThan_ok n (hs.of_keeps kv (by decide)) hn hb ha)
    fun w ⟨ew, kw, mw⟩ => ?_)
  refine wp_orS rfl fun x ux => ?_
  refine wp_logicS (.inr rfl) rfl fun y uy => ?_
  refine wp_movS rfl fun t ut _ => WP.block_nil ⟨?_, ((((kv.widen kw).widen ux.keeps).widen uy.keeps).widen ut.keeps),
    by rw [ut.mem, uy.mem, ux.mem, mw, uv.mem, mu]⟩
  rw [ut.gpr, uy.gpr, ux.gpr, ew, kw.1 _ (by decide), uv.gpr, eu, uv.mem, mu]
  by_cases hab : wordsVal s.mem base a n < wordsVal s.mem base b n
  · have hba : ¬ wordsVal s.mem base b n < wordsVal s.mem base a n := by omega
    have he : wordsVal s.mem base a n ≠ wordsVal s.mem base b n := by omega
    simp only [mask32, hab, hba, he, ite_true, ite_false]
    decide
  · by_cases hba : wordsVal s.mem base b n < wordsVal s.mem base a n
    · have he : wordsVal s.mem base a n ≠ wordsVal s.mem base b n := by omega
      simp only [mask32, hab, hba, he, ite_true, ite_false]
      decide
    · have he : wordsVal s.mem base a n = wordsVal s.mem base b n := by omega
      simp only [mask32, he, Nat.lt_irrefl, ite_true, ite_false]
      decide

abbrev flagW (base : Addr) (flag : Nat) (s : State) : BitVec 32 :=
  s.mem.readW (off base flag) 32

theorem andFlag_ok (flag : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : flag + 4 ≤ size) :
    WP isa (.block (andFlag flag)) s fun s' =>
      flagW base flag s' = flagW base flag s &&& s.gpr .edx ∧
      Keeps [.eax] s s' ∧ Outside base (flag) 4 s.mem s'.mem := by
  simp only [andFlag]
  refine wp_movS (readSrc_sc hs (d := flag) hf) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := u₁.keeps.trans u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  refine wp_storeS (hs₂.ea (d := flag) (by omega)) (hs₂.write hf) fun s₃ m₃ => WP.block_nil
    ⟨?_, k₂.trans (m₃.keeps _), ?_⟩
  · rw [flagW, flagW, m₃.mem, Mem.readW_writeW_self32, u₂.gpr, u₁.gpr, u₁.other _ (by decide)]
    simp only [ite_true]
  · rw [m₃.mem, u₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

/-- `checkRange a`: the flag `&=` the mask of `0 < [a] < [MN]`. -/
theorem checkRange_ok (n flag : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a m : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (hm : m + 8 * n ≤ size) (hf : flag + 4 ≤ size) :
    WP isa (.block (checkRange n a m flag)) s fun s' =>
      flagW base flag s' = flagW base flag s &&&
        mask32 (0 < wordsVal s.mem base a n ∧ wordsVal s.mem base a n < wordsVal s.mem base (m) n) ∧
      Keeps [.eax, .ebx, .ecx, .edx] s s' ∧ Outside base (flag) 4 s.mem s'.mem := by
  simp only [checkRange, List.append_assoc, List.singleton_append]
  refine WP.block_append (WP.mono (lessThan_ok n hs hn ha hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.eax, .ebx, .ecx, .edx] s s₂ := (k₁.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (nonzero_ok n hs₂ hn ha) fun s₃ ⟨e₃, k₃, m₃⟩ => ?_)
  refine wp_logicS (.inl rfl) rfl fun s₄ u₄ => ?_
  have k₄ : Keeps [.eax, .ebx, .ecx, .edx] s s₄ := (k₂.widen k₃).widen u₄.keeps
  have hs₄ := hs.of_keeps k₄ (by decide)
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
  refine WP.mono (andFlag_ok flag hs₄ hf) fun s₅ ⟨e₅, k₅, O₅⟩ => ⟨?_, k₄.widen k₅, by rw [← mem₄]; exact O₅⟩
  rw [e₅, flagW, flagW, mem₄, u₄.gpr, e₃, k₃.1 _ (by decide), u₂.gpr, e₁, u₂.mem, m₁]
  simp only [ite_true]
  rw [mask32_and]
  simp only [Nat.pos_iff_ne_zero]

/-- `checkNonzero a`: the flag `&=` the mask of `[a] ≠ 0`. -/
theorem checkNonzero_ok (n flag : Nat) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < n) (ha : a + 8 * n ≤ size) (hf : flag + 4 ≤ size) :
    WP isa (.block (checkNonzero n a flag)) s fun s' =>
      flagW base flag s' = flagW base flag s &&& mask32 (wordsVal s.mem base a n ≠ 0) ∧
      Keeps [.eax, .ecx, .edx] s s' ∧ Outside base (flag) 4 s.mem s'.mem := by
  rw [checkNonzero]
  refine WP.block_append (WP.mono (nonzero_ok n hs hn ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_)
  refine WP.mono (andFlag_ok flag (hs.of_keeps k₁ (by decide)) hf) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine ⟨by rw [e₂, e₁, flagW, flagW, m₁], (k₁.mono (by decide)).widen k₂, by rw [← m₁]; exact O₂⟩

end VG.Proof.Dsa.X86
