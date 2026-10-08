import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStore

/-!
# The Jacobian window method on x86-64: selecting an entry

`JacWinCfg.select` keeps every entry of the table under the mask of its index,
as the comb's selection does: for four-word numbers an entry is ten 16-byte
pieces, the pass `selPassAt` (or `selPassY`, 32 bytes at a time) of a comb
whose entries are ten words wide (`selTc`), so `selPass_ok` and
`selPassY_ok` apply. `T` then holds entry `a`'s five coordinates for
`1 ≤ a ≤ 16`, and zeros for `a = 0` (`jselect_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- A comb whose selection is the Jacobian window method's: entries of ten
words (`np = 10` pieces), selected into `T`. -/
def selTc (K : JacWinCfg) : TCombCfg where
  M := { K.M with n := 10 }
  S := K.S
  A := K.R
  E := ⟨K.T, K.T, K.T⟩
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.bits
  kbytes := 0
  tsym := ""
  w := 5
  J := 1
  start := (0, 0)
  one := 0

theorem selPassAt_congr (o H st np : Nat) {po po' : Nat → Nat} (h : ∀ c < np, po c = po' c) :
    selPassAt o H st np po = selPassAt o H st np po' := by
  have e1 : ∀ m : Nat, ((List.range np).flatMap fun c =>
      [Instr.movdquLoad .xmm14 (tblAt (st * (m - 1) + po c)), .xop (.bin .pand .xmm14 .xmm15),
        .xop (.bin .por (selAcc c) .xmm14)]) = ((List.range np).flatMap fun c =>
      [Instr.movdquLoad .xmm14 (tblAt (st * (m - 1) + po' c)), .xop (.bin .pand .xmm14 .xmm15),
        .xop (.bin .por (selAcc c) .xmm14)]) := fun m => by
    simp only [List.flatMap_def]
    congr 1
    exact List.map_congr_left fun c hc => by rw [h c (List.mem_range.mp hc)]
  have e2 : ((List.range np).map fun c => Instr.movdquStore (sc (o + po c)) (selAcc c)) =
      (List.range np).map fun c => Instr.movdquStore (sc (o + po' c)) (selAcc c) :=
    List.map_congr_left fun c hc => by rw [h c (List.mem_range.mp hc)]
  unfold selPassAt selEntryAt
  rw [e2]
  simp only [e1]

/-- The selection: `T`'s five coordinates are entry `a`'s, or zero for `a = 0`. -/
theorem jselect_ok {K : JacWinCfg} {size : Nat} (hL : JacWinLay K size) {s : State} {base : Addr}
    (hs : Scr s base size) {a : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : a ≤ 16) :
    WP isa (.block K.select) s fun t =>
      (∀ c < 5, wordsVal t.mem base (jg K (80 + c)) K.M.n =
        if 1 ≤ a then wordsVal s.mem base (jg K (5 * (a - 1) + c)) K.M.n else 0) ∧
      KeepRegs [.rcx, .rdx] s t ∧ Outside base (jg K 80) (40 * K.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  have h4 := hL.n4
  have hg := hL.grid_le
  have ht := hL.tbl31
  rw [h4] at hg
  rw [JacWinCfg.select, WP.block_append_iff]
  -- `rdx = rdi + tbl`.
  refine WP.mono (show WP isa (.block [.mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 K.tbl))]) s
      (fun s₁ => s₁.gpr .rdx = base + BitVec.ofNat 64 K.tbl ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.map_some, imm32_sext ht, hs.rdi, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨x₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hT : K.T = jg K 80 := hL.T80
  have hTe : (selTc K).E.x = K.T := rfl
  have hE : (selTc K).E.x + 16 * (selTc K).M.n ≤ size := by
    rw [hTe, hT]; show jg K 80 + 16 * 10 ≤ size; unfold jg; rw [h4]; omega
  have hH : (selTc K).H = 16 := rfl
  have hn10 : (selTc K).M.n = 10 := rfl
  -- The pass, as the comb's.
  have hpass : WP isa (.block (if K.avx2 then selPassY K.T 16 K.st K.np32 (qY K.np16)
      else selPassAt K.T 16 K.st K.np16 K.po)) s₁ fun t =>
      (∀ c < 10, t.mem.readW (off base (K.T + 16 * c)) 128 =
        accVal s₁.mem (base + BitVec.ofNat 64 K.tbl) (16 * 10) (16 * ·) a 16 c) ∧
      Outside base K.T (16 * 10) s₁.mem t.mem ∧ KeepRegs [.rcx] s₁ t := by
    have hst : K.st = 16 * 10 := by unfold JacWinCfg.st; rw [h4]
    have hnp : K.np16 = 10 := by unfold JacWinCfg.np16; rw [h4]
    have hr : ∀ e < (selTc K).H, ∀ c < (selTc K).M.n, InRegions (s₁.rd ++ s₁.wr)
        (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (16 * (selTc K).M.n * e + 16 * c)) 16 := by
      intro e he c hc
      rw [hH] at he; rw [hn10] at hc ⊢
      rw [Offset.add_add]
      have := Nat.mul_le_mul_left 160 (show e + 1 ≤ 16 by omega)
      exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega) (by decide)⟩
    split
    · have e : selPassY K.T 16 K.st K.np32 (qY K.np16) = selPassY (selTc K).E.x (selTc K).H
          (16 * (selTc K).M.n) (((selTc K).M.n + 1) / 2) (qY (selTc K).M.n) := by
        rw [hTe, hH, hn10, hst, show K.np32 = (K.np16 + 1) / 2 from rfl, hnp]
      rw [e]
      refine selPassY_ok (selTc K) hs₁ (by rw [hn10]; decide) (by rw [hn10]; decide) (by rw [hH]; decide)
        (by omega) (by rw [hn10, hH]; decide) h8₁ x₁
        ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (d := K.tbl) (by rw [hn10, hH]; omega)
          (by rw [hn10, hH]; decide)⟩ hE
    · have e : selPassAt K.T 16 K.st K.np16 K.po = selPassAt (selTc K).E.x (selTc K).H
          (16 * (selTc K).M.n) (selTc K).M.n (16 * ·) := by
        rw [hTe, hH, hn10, hst, hnp]
        refine selPassAt_congr _ _ _ _ fun c hc => ?_
        unfold JacWinCfg.po
        rw [hnp, hst]
        split <;> omega
      rw [e]
      exact selPass_ok (selTc K) hs₁ (by rw [hn10]; decide) (by rw [hH]; decide) (by omega) h8₁ x₁ hr hE
  refine WP.mono hpass fun t ⟨a₂, O₂, k₂⟩ => ⟨fun c hc => ?_, ?_, ?_⟩
  · have hw := accVal_word (mem := s₁.mem) (mem' := t.mem) (base := base) (n := 10) (o := K.T) a₂
    have hX : ∀ d, word s₁.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
      rw [k₁.2.1, Mont.word, Mont.word, off, off, Offset.add_add]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      refine wordsVal_congr₂ _ _ _ fun i hi => ?_
      rw [h4] at hi
      have e := hw (4 * c + i) (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), hX] at e
      rw [show jg K (80 + c) + 8 * i = K.T + 8 * (4 * c + i) by rw [hT]; unfold jg; rw [h4]; omega, e]
      congr 1; unfold jg; rw [h4]; rw [Nat.mul_add]; omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      refine wordsVal_zeros fun i hi => ?_
      rw [h4] at hi
      have e := hw (4 * c + i) (by omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at e
      rw [show jg K (80 + c) + 8 * i = K.T + 8 * (4 * c + i) by rw [hT]; unfold jg; rw [h4]; omega, e]
  · refine ⟨fun r hr => ?_, by rw [k₂.rd, k₁.2.2.1], by rw [k₂.wr, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₂.gpr r (by simp [hr.1]), k₁.1 r (by simp [hr.2])]
  · rw [← hT, h4, show 40 * 4 = 16 * 10 from rfl, ← k₁.2.1]; exact O₂

end VG.Proof.Weierstrass.X86_64
