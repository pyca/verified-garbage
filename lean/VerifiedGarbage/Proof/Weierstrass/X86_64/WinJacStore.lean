import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacLay

/-!
# The Jacobian window method on x86-64: storing an entry

`entryAddr` forms entry `rbx`'s address `rdi + tbl + 40 n (rbx - 1)` with `mul`
(`entryAddr_ok`), and `storeEntry` copies `T`'s `5 n` words there, word by
word through `rax` (`storeWords_ok`, `jstoreEntry_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- `rdx = rdi + tbl + st (m - 1)` for `rbx = m ≥ 1`. -/
theorem entryAddr_ok (K : JacWinCfg) (s : State) {base : Addr} {m : Nat} (hb : s.gpr .rdi = base)
    (hm : s.gpr .rbx = BitVec.ofNat 64 m) (h1 : 1 ≤ m) (hm' : m < 2 ^ 32) (ht : K.tbl < 2 ^ 31)
    (hst : K.st < 2 ^ 31) :
    WP isa (.block K.entryAddr) s fun t =>
      t.gpr .rdx = off base (K.tbl + K.st * (m - 1)) ∧ Keeps [.rax, .rcx, .rdx] s t := by
  apply WP.of_runBlock
  simp only [JacWinCfg.entryAddr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, execMul, State.setReg32, imm32_sext ht, hm, hb, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.gpr_setFlags, Option.map_some, Option.bind_some, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e1 : (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 := by decide
    have hs : BitVec.ofNat 64 m - BitVec.ofNat 64 1 = BitVec.ofNat 64 (m - 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    have hmul : BitVec.ofNat 64 ((BitVec.ofNat 64 (m - 1)).toNat *
        ((BitVec.ofNat 32 K.st).setWidth 64).toNat) = BitVec.ofNat 64 (K.st * (m - 1)) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      rw [Nat.mod_eq_of_lt (show K.st < 2 ^ 32 by omega), Nat.mod_eq_of_lt (show m - 1 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show K.st < 2 ^ 64 by omega), Nat.mul_comm]
    rw [e1, hs, hmul, Offset.add_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
      ite_false]

/-- The words `src + 8 i`, `i < m`, to `A + 8 i`, for `rdx = base + A`. -/
theorem storeWords_ok {base : Addr} {size A src : Nat} : ∀ (m : Nat) (s : State), Scr s base size →
    s.gpr .rdx = off base A → A + 8 * m ≤ size → src + 8 * m ≤ size → (A + 8 * m ≤ src ∨ src + 8 * m ≤ A) →
    WP isa (.block ((List.range m).flatMap fun i =>
      [.mov .rax (.mem (sc (src + 8 * i))), .store (tblAt (8 * i)) .rax])) s fun t =>
      (∀ i < m, word t.mem base (A + 8 * i) = word s.mem base (src + 8 * i)) ∧ KeepRegs [.rax] s t ∧
        Outside base A (8 * m) s.mem t.mem
  | 0, _, _, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | m + 1, s, hs, hx, hA, hsrc, hsep => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (storeWords_ok m s hs hx (by omega) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hx₁ : s₁.gpr .rdx = off base A := by rw [k₁.gpr _ (by decide), hx]
    have hea : off base A + BitVec.ofNat 64 (8 * m) = off base (A + 8 * m) := by
      unfold off; rw [Offset.add_add]
    have hw : InRegions s₁.wr (off base (A + 8 * m)) 8 := st_sc hs₁ (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      State.load64, State.store64, ea_sc, ea_tblAt, hx₁, hea, hw, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      RegUpd.mem_setReg, reduceCtorEq, ite_true, ite_false, hs₁.rdi, ld_sc hs₁ (d := src + 8 * m) (by omega),
      Option.some.injEq, exists_eq_left']
    have O₂ := writeW_outside s₁.mem base (word s₁.mem base (src + 8 * m)) (d := A + 8 * m) (by omega)
    refine ⟨fun i hi => ?_, ⟨fun r hr => ?_, k₁.rd, k₁.wr⟩, fun x h => by
      rw [O₂ x (by omega), O₁ x (by omega)]⟩
    · by_cases him : i = m
      · subst him
        rw [word_writeW_self]; exact O₁.word (by omega) (by omega)
      · rw [O₂.word (by omega) (by omega), e₁ i (by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]
      exact k₁.gpr r (by simp [hr])

/-- `T`'s five coordinates into entry `m = rbx`, `1 ≤ m ≤ 16`. -/
theorem jstoreEntry_ok {K : JacWinCfg} {size : Nat} (hL : JacWinLay K size) {s : State} {base : Addr}
    (hs : Scr s base size) {m : Nat} (hm : s.gpr .rbx = BitVec.ofNat 64 m) (h1 : 1 ≤ m) (h16 : m ≤ 16) :
    WP isa (.block K.storeEntry) s fun t =>
      (∀ c < 5, wordsVal t.mem base (jg K (5 * (m - 1) + c)) K.M.n =
        wordsVal s.mem base (jg K (80 + c)) K.M.n) ∧
      KeepRegs [.rax, .rcx, .rdx] s t ∧ Outside base (jg K (5 * (m - 1))) (40 * K.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  have h4 := hL.n4
  have hg := hL.grid_le
  have ht := hL.tbl31
  rw [JacWinCfg.storeEntry, WP.block_append_iff]
  refine WP.mono (entryAddr_ok K s hs.rdi hm h1 (by omega) ht (by unfold JacWinCfg.st; omega))
    fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hA : K.tbl + K.st * (m - 1) = jg K (5 * (m - 1)) := by
    have := entry_addr K m 0; simpa using this
  rw [hA] at x₁
  have hT : K.T = jg K 80 := hL.T80
  have hgl : jg K (5 * (m - 1)) + 8 * (5 * K.M.n) ≤ jg K 80 := by
    unfold jg; have := Nat.mul_le_mul_left (8 * K.M.n) (show 5 * (m - 1) + 5 ≤ 80 by omega)
    rw [Nat.mul_add] at this; rw [h4] at this ⊢; omega
  have hTl : jg K 80 + 8 * (5 * K.M.n) ≤ size := by unfold jg; rw [h4] at hg ⊢; omega
  rw [hT]
  refine WP.mono (storeWords_ok (A := jg K (5 * (m - 1))) (src := jg K 80) (5 * K.M.n) s₁ hs₁ x₁
    (by omega) hTl (Or.inl hgl)) fun t ⟨e, k₂, O⟩ => ⟨fun c hc => ?_, ?_, ?_⟩
  · rw [← k₁.2.1]
    refine wordsVal_congr₂ _ _ _ fun i hi => ?_
    have e1 : jg K (5 * (m - 1) + c) + 8 * i = jg K (5 * (m - 1)) + 8 * (K.M.n * c + i) := by
      unfold jg; rw [Nat.mul_add, Nat.mul_add]; rw [h4]; omega
    have e2 : jg K (80 + c) + 8 * i = jg K 80 + 8 * (K.M.n * c + i) := by
      unfold jg; rw [Nat.mul_add, Nat.mul_add]; rw [h4]; omega
    rw [e1, e2, e _ (by rw [h4] at hi ⊢; omega)]
  · exact ((Keeps.regs k₁).mono (by decide)).trans (k₂.mono (by decide))
  · rw [k₁.2.1] at O
    rw [show 40 * K.M.n = 8 * (5 * K.M.n) by omega]
    exact O

end VG.Proof.Weierstrass.X86_64
