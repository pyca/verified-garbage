import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacStore

/-!
# The Jacobian window method on x86-64: selecting an entry

`JacWinCfg.select` keeps every entry of the table under the mask of its index,
as the comb's selection does: an entry is ten 16-byte pieces for four-word
numbers and fifteen for six, the pass `selPassAt` (`selPassAt_ok`, in two
passes for fifteen pieces, which the 14 accumulators do not hold) or
`selPassY` (32 bytes at a time) of a comb whose entries are that many words
wide (`selTc`, `selPassY_ok`). `T` then holds entry `a`'s five coordinates for
`1 ≤ a ≤ 16`, and zeros for `a = 0` (`jselect_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- A comb whose selection is the Jacobian window method's: entries of
`np16` pieces (ten for four words, fifteen for six), selected into `T`. -/
def selTc (K : JacWinCfg) : TCombCfg where
  M := { K.M with n := K.np16 }
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

/-- An entry's pieces: ten for four words, fifteen for six; the entries are
`16 np16` bytes apart. -/
theorem np16_eq {K : JacWinCfg} {size : Nat} (hL : JacWinLay K size) :
    (K.np16 = 10 ∨ K.np16 = 15) ∧ K.st = 16 * K.np16 ∧ 2 * K.np16 = 5 * K.M.n := by
  unfold JacWinCfg.np16 JacWinCfg.st
  rcases hL.n46 with h | h <;> rw [h] <;> decide

/-- The selection: `T`'s five coordinates are entry `a`'s, or zero for `a = 0`. -/
theorem jselect_ok {K : JacWinCfg} {size : Nat} (hL : JacWinLay K size) {s : State} {base : Addr}
    (hs : Scr s base size) {a : Nat} (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (ha : a ≤ 16) :
    WP isa (.block K.select) s fun t =>
      (∀ c < 5, wordsVal t.mem base (jg K (80 + c)) K.M.n =
        if 1 ≤ a then wordsVal s.mem base (jg K (5 * (a - 1) + c)) K.M.n else 0) ∧
      KeepRegs [.rcx, .rdx] s t ∧ Outside base (jg K 80) (40 * K.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  have hg := hL.grid_le
  have ht := hL.tbl31
  have h6 := hL.n6
  obtain ⟨hnp, hst, h2n⟩ := np16_eq hL
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
  have hTl : K.T + 16 * K.np16 ≤ size := by rw [hT]; unfold jg; omega
  have hTt : K.T = K.tbl + 16 * K.st := hL.T
  have hH : (selTc K).H = 16 := rfl
  have hnt : (selTc K).M.n = K.np16 := rfl
  have hreg : InRegions (s₁.rd ++ s₁.wr) (base + BitVec.ofNat 64 K.tbl) (16 * K.np16 * 16) :=
    ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (d := K.tbl) (by omega) (by omega)⟩
  have hr : ∀ e < 16, ∀ c < K.np16, InRegions (s₁.rd ++ s₁.wr)
      (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (K.st * e + 16 * c)) 16 := by
    intro e he c hc
    rw [Offset.add_add]
    have := Nat.mul_le_mul_left K.st (show e + 1 ≤ 16 by omega)
    rw [Nat.mul_succ] at this
    exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega) (by decide)⟩
  -- The pass, as the comb's.
  have hpass : WP isa (.block (if K.avx2 then selPassY K.T 16 K.st K.np32 (qY K.np16)
      else if K.np16 ≤ 14 then selPassAt K.T 16 K.st K.np16 K.po
      else selPassAt K.T 16 K.st 8 (16 * ·) ++ selPassAt K.T 16 K.st (K.np16 - 8) (fun c => 16 * (8 + c)))) s₁
      fun t =>
      (∀ c < K.np16, t.mem.readW (off base (K.T + 16 * c)) 128 =
        accVal s₁.mem (base + BitVec.ofNat 64 K.tbl) (16 * K.np16) (16 * ·) a 16 c) ∧
      Outside base K.T (16 * K.np16) s₁.mem t.mem ∧ KeepRegs [.rcx] s₁ t := by
    split
    · have e : selPassY K.T 16 K.st K.np32 (qY K.np16) = selPassY (selTc K).E.x (selTc K).H
          (16 * (selTc K).M.n) (((selTc K).M.n + 1) / 2) (qY (selTc K).M.n) := by
        rw [hTe, hH, hnt, hst]; rfl
      rw [e]
      refine selPassY_ok (selTc K) hs₁ (by rw [hnt]; omega) (by rw [hnt]; omega) (by rw [hH]; decide)
        (by omega) (by rw [hnt, hH]; omega) h8₁ x₁ hreg (by rw [hTe, hnt]; exact hTl)
    · split
      · next hle =>
        rw [selPassAt_congr _ _ _ _ (po' := (16 * ·)) (fun c hc => by unfold JacWinCfg.po; rw [hst]; split <;> omega),
          hst]
        exact (selPassAt_ok (d := 0) hs₁ hle (by decide) (by omega) h8₁ x₁ (fun c _ => by omega)
          (fun e he c hc => by have := hr e he c hc; rw [hst] at this; exact this) (by omega)).mono
          fun t ⟨a₂, O₂, k₂⟩ => ⟨fun c hc => by rw [← a₂ c hc, Nat.add_zero], by rw [← Nat.add_zero K.T]; exact O₂, k₂⟩
      · next hle =>
        have h15 : K.np16 = 15 := by omega
        rw [WP.block_append_iff]
        refine WP.mono (selPassAt_ok (X := base + BitVec.ofNat 64 K.tbl) (a := a) (d := 0) (np := 8) (po := (16 * ·)) hs₁ (by decide) (by decide) (by omega)
          h8₁ x₁ (fun c _ => by omega) (fun e he c hc => hr e he c (by omega)) (by omega))
          fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
        have hs₂ : Scr s₂ base size := hs₁.of_keepRegs k₂ (by decide)
        refine WP.mono (selPassAt_ok (X := base + BitVec.ofNat 64 K.tbl) (a := a) (d := 128) (np := K.np16 - 8) (po := fun c => 16 * (8 + c)) hs₂ (by omega)
          (by decide) (by omega) (by rw [k₂.gpr _ (by decide), h8₁]) (by rw [k₂.gpr _ (by decide), x₁])
          (fun c _ => by omega) (fun e he c hc => by
            rw [k₂.rd, k₂.wr]; have := hr e he (8 + c) (by omega); rw [hst] at this ⊢; exact this)
          (by omega)) fun t ⟨a₃, O₃, k₃⟩ => ⟨fun c hc => ?_, ?_, k₂.trans k₃⟩
        · have tb : ∀ y, y + 16 ≤ 16 * K.st → s₂.mem.readW (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 y) 128 =
              s₁.mem.readW (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 y) 128 := fun y hy => by
            rw [Offset.add_add]; exact O₂.read128 (by omega) (by omega)
          rw [hst] at a₂
          by_cases h8c : c < 8
          · rw [O₃.read128 (by omega) (by omega), ← Nat.add_zero K.T, a₂ c h8c]
          · obtain ⟨c', rfl⟩ : ∃ c', c = 8 + c' := ⟨c - 8, by omega⟩
            rw [show K.T + 16 * (8 + c') = K.T + 128 + 16 * c' by omega, a₃ c' (by omega)]
            unfold accVal
            dsimp only
            split
            · next hb =>
              rw [tb _ (by
                have := Nat.mul_le_mul_left K.st (show a - 1 + 1 ≤ 16 by omega)
                rw [Nat.mul_succ] at this; omega), hst]
            · rfl
        · refine (O₂.mono (Nat.le_refl _) (by omega)).trans (O₃.mono (by omega) (by omega))
  refine WP.mono hpass fun t ⟨a₂, O₂, k₂⟩ => ⟨fun c hc => ?_, ?_, ?_⟩
  · have hw := accVal_word (mem := s₁.mem) (mem' := t.mem) (base := base) (n := K.np16) (o := K.T) a₂
    have hX : ∀ d, word s₁.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
      rw [k₁.2.1, Mont.word, Mont.word, off, off, Offset.add_add]
    have hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 5 by omega)
    rw [Nat.mul_succ] at hcn
    have eT : ∀ i, jg K (80 + c) + 8 * i = K.T + 8 * (K.M.n * c + i) := fun i => by
      rw [hT]; unfold jg; rw [Nat.mul_add, Nat.mul_add, Nat.mul_assoc 8 K.M.n c]; omega
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      refine wordsVal_congr₂ _ _ _ fun i hi => ?_
      have e := hw (K.M.n * c + i) (by omega)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), hX] at e
      rw [eT, e, ← hst]
      congr 1; unfold jg JacWinCfg.st
      rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
        rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
        Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c]
      omega
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      refine wordsVal_zeros fun i hi => ?_
      have e := hw (K.M.n * c + i) (by omega)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at e
      rw [eT, e]
  · refine ⟨fun r hr => ?_, by rw [k₂.rd, k₁.2.2.1], by rw [k₂.wr, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₂.gpr r (by simp [hr.1]), k₁.1 r (by simp [hr.2])]
  · rw [← hT, show 40 * K.M.n = 16 * K.np16 by omega, ← k₁.2.1]; exact O₂

end VG.Proof.Weierstrass.X86_64
