module

public import VerifiedGarbage.Proof.Weierstrass.Window5
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY
import VerifiedGarbage.Proof.Mont.Words128
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! ### `Weierstrass.X86_64.WinJacSelect`, which this module and modules that import it used -/

section

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

@[expose] public section

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
  obtain e1 : ∀ m : Nat, ((List.range np).flatMap fun c =>
      [Instr.movdquLoad .xmm14 (tblAt (st * (m - 1) + po c)), .xop (.bin .pand .xmm14 .xmm15),
        .xop (.bin .por (selAcc c) .xmm14)]) = ((List.range np).flatMap fun c =>
      [Instr.movdquLoad .xmm14 (tblAt (st * (m - 1) + po' c)), .xop (.bin .pand .xmm14 .xmm15),
        .xop (.bin .por (selAcc c) .xmm14)]) := fun m => by
    simp only [List.flatMap_def]
    congr 1
    exact List.map_congr_left fun c hc => by rw [h c (List.mem_range.mp hc)]
  obtain e2 : ((List.range np).map fun c => Instr.movdquStore (sc (o + po c)) (selAcc c)) =
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
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hT : K.T = jg K 80 := hL.T80
  have hTe : (selTc K).E.x = K.T := rfl
  obtain hTl : K.T + 16 * K.np16 ≤ size := by rw [hT]; unfold jg; omega_arith
  have hTt : K.T = K.tbl + 16 * K.st := hL.T
  have hH : (selTc K).H = 16 := rfl
  have hnt : (selTc K).M.n = K.np16 := rfl
  obtain hreg : InRegions (s₁.rd ++ s₁.wr) (base + BitVec.ofNat 64 K.tbl) (16 * K.np16 * 16) :=
    ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (d := K.tbl) (by omega_arith) (by omega_arith)⟩
  obtain hr : ∀ e < 16, ∀ c < K.np16, InRegions (s₁.rd ++ s₁.wr)
      (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 (K.st * e + 16 * c)) 16 := by
    intro e he c hc
    rw [Offset.add_add]
    have := Nat.mul_le_mul_left K.st (show e + 1 ≤ 16 by omega_arith)
    rw [Nat.mul_succ] at this
    exact ⟨_, List.mem_append_right _ (k₁.2.2.2 ▸ hs.wr), hs.contains (by omega_arith) (by decide)⟩
  -- The pass, as the comb's.
  obtain hpass : WP isa (.block (if K.avx2 then selPassY K.T 16 K.st K.np32 (qY K.np16)
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
      refine selPassY_ok (selTc K) hs₁ (by rw [hnt]; omega_arith) (by rw [hnt]; omega_arith) (by rw [hH]; decide)
        (by omega_arith) (by rw [hnt, hH]; omega_arith) h8₁ x₁ hreg (by rw [hTe, hnt]; exact hTl)
    · split
      · next hle =>
        rw [selPassAt_congr _ _ _ _ (po' := (16 * ·)) (fun c hc => by unfold JacWinCfg.po; rw [hst]; split <;> omega_arith),
          hst]
        exact (selPassAt_ok (d := 0) hs₁ hle (by decide) (by omega_arith) h8₁ x₁ (fun c _ => by omega_arith)
          (fun e he c hc => by have := hr e he c hc; rw [hst] at this; exact this) (by omega_arith)).mono
          fun t ⟨a₂, O₂, k₂⟩ => ⟨fun c hc => by rw [← a₂ c hc, Nat.add_zero], by rw [← Nat.add_zero K.T]; exact O₂, k₂⟩
      · next hle =>
        obtain h15 : K.np16 = 15 := by omega_arith
        rw [WP.block_append_iff]
        refine WP.mono (selPassAt_ok (X := base + BitVec.ofNat 64 K.tbl) (a := a) (d := 0) (np := 8) (po := (16 * ·)) hs₁ (by decide) (by decide) (by omega_arith)
          h8₁ x₁ (fun c _ => by omega_arith) (fun e he c hc => hr e he c (by omega_arith)) (by omega_arith))
          fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
        obtain hs₂ : Scr s₂ base size := hs₁.of_keepRegs k₂ (by decide)
        refine WP.mono (selPassAt_ok (X := base + BitVec.ofNat 64 K.tbl) (a := a) (d := 128) (np := K.np16 - 8) (po := fun c => 16 * (8 + c)) hs₂ (by omega_arith)
          (by decide) (by omega_arith) (by rw [k₂.gpr _ (by decide), h8₁]) (by rw [k₂.gpr _ (by decide), x₁])
          (fun c _ => by omega_arith) (fun e he c hc => by
            rw [k₂.rd, k₂.wr]; have := hr e he (8 + c) (by omega_arith); rw [hst] at this ⊢; exact this)
          (by omega_arith)) fun t ⟨a₃, O₃, k₃⟩ => ⟨fun c hc => ?_, ?_, k₂.trans k₃⟩
        · have tb : ∀ y, y + 16 ≤ 16 * K.st → s₂.mem.readW (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 y) 128 =
              s₁.mem.readW (base + BitVec.ofNat 64 K.tbl + BitVec.ofNat 64 y) 128 := fun y hy => by
            rw [Offset.add_add]; exact O₂.read128 (by omega_arith) (by omega_arith)
          rw [hst] at a₂
          by_cases h8c : c < 8
          · rw [O₃.read128 (by omega_arith) (by omega_arith), ← Nat.add_zero K.T, a₂ c h8c]
          · obtain ⟨c', rfl⟩ : ∃ c', c = 8 + c' := ⟨c - 8, by omega_arith⟩
            rw [show K.T + 16 * (8 + c') = K.T + 128 + 16 * c' by omega_arith, a₃ c' (by omega_arith)]
            unfold accVal
            dsimp only
            split
            · next hb =>
              rw [tb _ (by
                have := Nat.mul_le_mul_left K.st (show a - 1 + 1 ≤ 16 by omega_arith)
                rw [Nat.mul_succ] at this; omega_arith), hst]
            · rfl
        · refine (O₂.mono (Nat.le_refl _) (by omega_arith)).trans (O₃.mono (by omega_arith) (by omega_arith))
  refine WP.mono hpass fun t ⟨a₂, O₂, k₂⟩ => ⟨fun c hc => ?_, ?_, ?_⟩
  · have hw := accVal_word (mem := s₁.mem) (mem' := t.mem) (base := base) (n := K.np16) (o := K.T) a₂
    obtain hX : ∀ d, word s₁.mem (base + BitVec.ofNat 64 K.tbl) d = word s.mem base (K.tbl + d) := fun d => by
      rw [k₁.2.1, Mont.word, Mont.word, off, off, Offset.add_add]
    obtain hcn := Nat.mul_le_mul_left K.M.n (show c + 1 ≤ 5 by omega_arith)
    rw [Nat.mul_succ] at hcn
    obtain eT : ∀ i, jg K (80 + c) + 8 * i = K.T + 8 * (K.M.n * c + i) := fun i => by
      rw [hT]; unfold jg; rw [Nat.mul_add, Nat.mul_add, Nat.mul_assoc 8 K.M.n c]; omega_arith
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      refine wordsVal_congr₂ _ _ _ fun i hi => ?_
      obtain e := hw (K.M.n * c + i) (by omega_arith)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩), hX] at e
      rw [eT, e, ← hst]
      congr 1; unfold jg JacWinCfg.st
      rw [show 40 * K.M.n * (a - 1) = 8 * K.M.n * (5 * (a - 1)) by
        rw [Nat.mul_assoc, Nat.mul_assoc, show 40 = 8 * 5 from rfl, Nat.mul_assoc, Nat.mul_left_comm 5],
        Nat.mul_add (8 * K.M.n), Nat.mul_assoc 8 K.M.n c]
      omega_arith
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      refine wordsVal_zeros fun i hi => ?_
      obtain e := hw (K.M.n * c + i) (by omega_arith)
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))] at e
      rw [eT, e]
  · refine ⟨fun r hr => ?_, by rw [k₂.rd, k₁.2.2.1], by rw [k₂.wr, k₁.2.2.2]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k₂.gpr r (by simp [hr.1]), k₁.1 r (by simp [hr.2])]
  · rw [← hT, show 40 * K.M.n = 16 * K.np16 by omega_arith, ← k₁.2.1]; exact O₂

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# The Jacobian window method on x86-64: the entry of a digit

Digit `j = rbx` as the comb reads it (`digit_ok`, windows of 5 bits of
`k' = k + offset J`): its magnitude `a = |k'_j - 16|` selects entry `a` of the
table into `T` (`jselect_ok`, zeros for `a = 0`), whose `Y` is negated for a
negative digit (`negY`, as the comb's), so that `T` holds digit `j`'s point
`winPt` with its powers, or `Z = 0` for the digit zero (`jentry_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The table of bits survives the method. -/
theorem JFrame.bits (hL : JacWinLay K size) {base : Addr} {s₀ s : State} {P : Point C} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) (hf : JFrame K C base size s₀ s) :
    ∀ t < 5 * K.J, s.mem (off base (K.bits + t)) = if (k + JacWinCfg.offset K.J).testBit t then 1 else 0 := by
  intro t ht
  have hb := hL.bits
  have hn := hf.scr.nowrap
  rw [hf.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_using [ht, this]) (by omega_using [ht, hb, hn])]
  exact hF.bits t ht

/-- What `T` holds after the selection and the negation, from `s`: its powers
always (zero for a zero digit), and digit `j`'s point for a nonzero one,
whose `Z` is the selected entry's. -/
structure JEnt (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k' j : Nat) (s t : State) : Prop where
  fr : JFrame K C base size s₀ t
  unch : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem t.mem
  keep : KeepRegs (clob K.M.n) s t
  lt : ∀ c < 5, wordsVal t.mem base (TS K c) K.M.n < C.p
  z2 : tmv C K.M.n base t (TS K 3) = tmv C K.M.n base t (TS K 2) * tmv C K.M.n base t (TS K 2)
  z3 : tmv C K.M.n base t (TS K 4) = tmv C K.M.n base t (TS K 3) * tmv C K.M.n base t (TS K 2)
  ent : 1 ≤ magH 16 (Window5.nib k' j) → JPt C K.M.n base t (TS K) (Window5.winPt C P k' j)
  zero : magH 16 (Window5.nib k' j) = 0 → tmv C K.M.n base t (TS K 2) = 0
  zent : 1 ≤ magH 16 (Window5.nib k' j) → wordsVal t.mem base (TS K 2) K.M.n =
    wordsVal s.mem base (entS K (magH 16 (Window5.nib k' j)) 2) K.M.n

theorem jent_loopW (K : JacWinCfg) : ∀ w ∈ (List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ jwLoopW K := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact other_loopW (by jw_mem)
    · exact tmp_loopW

/-- Digit `j`'s entry into `T`, negated for a negative digit. -/
theorem jentry_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixed K C base s₀ P k) {s : State} {j : Nat} (hj : j < K.J)
    (hf : JFrame K C base size s₀ s) (hT : JTblOk K C base P 16 s) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (K.tc.digit ++ K.select)) s fun s₂ =>
      WP isa (.block K.tc.negY) s₂ (JEnt K C base size P s₀ (k + JacWinCfg.offset K.J) j s) := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hbl := hL.bits
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  obtain hbits := hf.bits hL hF
  generalize hk' : k + JacWinCfg.offset K.J = k' at hbits
  obtain hwj : 5 * j + 5 ≤ 5 * K.J := by omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (digit_ok K.tc hs (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 9; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_arith) hb hbits) fun s₁ ⟨_, r₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  obtain hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  have hH : K.tc.H = 16 := rfl
  rw [hwin, hH] at r₁
  generalize ha : magH 16 (Window5.nib k' j) = a at r₁
  obtain ha16 : a ≤ 16 := by rw [← ha]; exact magH_le (by have := Window5.nib_lt k' j; omega_arith)
  refine WP.mono (jselect_ok hL hs₁ r₁ ha16) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at e₂
  obtain U₂ : Unch base (jwLoopW K) s.mem s₂.mem := by
    rw [← m₁]; exact (outside_grid5 (b := 80) O₂).mono fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  obtain F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) U₂ (jwLoopW_sub K)
  -- The negation.
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  obtain hneg : K.neg ∈ jwSlots K := by jw_mem
  obtain hzero : K.zero ∈ jwSlots K := by jw_mem
  obtain hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by rw [F₂.ro hL (by jw_mem)]; exact hF.zero
  obtain hy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by
    rw [← ty, e₂ 1 (by decide)]
    split
    · exact (hT a (by omega_arith) ha16).lt 1 (by decide)
    · exact hp0
  obtain hyneg : K.E.y + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ K.E.y := by
    rw [hL.Ty]; exact (hL.jg_apart (x := K.neg) (by jw_mem) (by decide)).symm
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ F₂.mod (o := K.neg) (a := K.zero) (b := K.E.y) (hL.le hneg) (hL.le hzero)
    (hL.le my) (hL.lay.tmp _ hneg) (hL.lay.tmp _ hzero) (hL.lay.tmp _ my) (hL.lay.mo _ hneg)
    (by rw [hz₂]; exact hp0) hy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  obtain hs₃ := k₃.scr hs₂
  obtain hbits₃ : ∀ t < 5 * K.J, s₃.mem (off base (K.bits + t)) = if k'.testBit t then 1 else 0 := by
    intro t ht
    rw [k₃.unch.byte (fun w hw => by
      obtain hw' : w ∈ jwW K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact mem_jwW_ws (other_ws (by jw_mem))
        · exact mem_jwW_tmp
      have := hL.bits_w w hw'; omega_arith) (by omega_arith)]
    have := F₂.bits hL hF t ht; rw [hk'] at this; exact this
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc hs₃ (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 2 ^ 31; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_arith) (by rw [k₃.gpr _ (rbx_not_clob _), k₂.gpr _ (by decide),
      k₁.1 _ (by decide), hb]) hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  rw [hwin] at x₄
  refine WP.mono (sel_ok (decide (Window5.nib k' j < 2 ^ (K.tc.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) (hL.le my) (hL.le my) (hL.le hneg) (Or.inl (Nat.le_refl _))
    (by omega_arith)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  obtain b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  -- `T`'s words: as at `s₂` but `Y`.
  obtain keepT : ∀ c < 5, c ≠ 1 → wordsVal s₅.mem base (TS K c) K.M.n = wordsVal s₂.mem base (TS K c) K.M.n := by
    intro c hc h1
    obtain hy : TS K c + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ TS K c := by
      rw [hL.Ty]; exact jg_sep K (by omega_arith)
    rw [O₅.wordsVal hy (b64 _ (jg_mem (by omega_arith))), m₄, k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (hL.jg_apart (x := K.neg) (by jw_mem) (i := 80 + c) (by omega_arith)).symm
      · exact hL.lay.tmp _ (jg_mem (by omega_arith))) (b64 _ (jg_mem (by omega_arith)))]
  obtain y₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyneg
      · exact hL.lay.tmp _ my) (b64 _ my)
  obtain keepY : wordsVal s₅.mem base (TS K 1) K.M.n = if decide (Window5.nib k' j < 2 ^ (K.tc.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [ty, e₅, m₄, e₃, hz₂, y₃]
  obtain tv : ∀ {x y : Nat}, wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base y K.M.n →
      tmv C K.M.n base s₅ x = tmv C K.M.n base s₂ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  -- `T` at `s₂`: entry `a`, or zeros.
  obtain e₂' : ∀ c < 5, wordsVal s₂.mem base (TS K c) K.M.n =
      if 1 ≤ a then wordsVal s.mem base (entS K a c) K.M.n else 0 := fun c hc => e₂ c hc
  obtain T₂z : ∀ c < 5, ¬ 1 ≤ a → tmv C K.M.n base s₂ (TS K c) = 0 := fun c hc h => by
    show toM _ _ _ = _; rw [e₂' c hc, ite_eq_right_of_eq_false _ _ (eq_false h)]; exact toM_zero _ _
  obtain T₂ : 1 ≤ a → JPt C K.M.n base s₂ (TS K) (mul a P) := fun h =>
    (hT a h ha16).congr fun c hc => by rw [e₂' c hc, ite_eq_left_of_eq_true _ _ (eq_true h)]
  obtain hU : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
      [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem s₅.mem := by
    rw [← m₁]
    refine (((outside_grid5 (b := 80) O₂).trans k₃.unch).trans (m₄ ▸ O₅.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h, hL.Ty]; exact Or.inl (List.mem_map.mpr ⟨1, by decide, rfl⟩)
  obtain hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  obtain kk : KeepRegs (clob K.M.n) s s₅ :=
    ((((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))).trans
      ((⟨k₃.gpr, k₃.rd, k₃.wr⟩ : KeepRegs (clob K.M.n) s₂ s₃).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h])))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  have h16 : (2 : Nat) ^ (K.tc.w - 1) = 16 := rfl
  rw [h16] at keepY
  obtain lt₂ : ∀ c < 5, wordsVal s₂.mem base (TS K c) K.M.n < C.p := fun c hc => by
    rw [e₂' c hc]; split
    · exact (hT a ‹_› ha16).lt c hc
    · exact hp0
  obtain tz : ∀ c < 5, c ≠ 1 → tmv C K.M.n base s₅ (TS K c) = tmv C K.M.n base s₂ (TS K c) :=
    fun c hc h1 => tv (keepT c hc h1)
  refine ⟨hf.next hL hs₅ (kk.mono clob_powClob) hU (fun w hw => jwLoopW_sub K w (jent_loopW K w hw)), hU,
    kk, fun c hc => ?_, ?_, ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · by_cases h1 : c = 1
    · subst h1; rw [keepY]; split
      · exact Nat.mod_lt _ hp0
      · exact hy₂
    · rw [keepT c hc h1]; exact lt₂ c hc
  · rw [tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]
    by_cases h1 : 1 ≤ a
    · exact (T₂ h1).z2
    · rw [T₂z 3 (by decide) h1, T₂z 2 (by decide) h1]; exact (Lean.Grind.Semiring.mul_zero 0).symm
  · rw [tz 4 (by decide) (by decide), tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]
    by_cases h1 : 1 ≤ a
    · exact (T₂ h1).z3
    · rw [T₂z 4 (by decide) h1, T₂z 3 (by decide) h1, T₂z 2 (by decide) h1]
      exact (Lean.Grind.Semiring.mul_zero 0).symm
  · rw [ha] at h
    obtain J₂ := T₂ h
    rw [Window5.winPt_mag, ha]
    by_cases hng : Window5.nib k' j < 16
    · simp only [decide_eq_true hng, ↓reduceIte]
      simp only [decide_eq_true hng, ↓reduceIte] at keepY
      obtain hy : tmv C K.M.n base s₅ (TS K 1) = -tmv C K.M.n base s₂ (TS K 1) := by
        show toM _ _ _ = -toM _ _ _
        rw [keepY, toM_sub (by omega_arith), toM_zero, ty]
        grind
      refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
      · by_cases h1 : c = 1
        · subst h1; rw [keepY]; exact Nat.mod_lt _ hp0
        · rw [keepT c hc h1]; exact lt₂ c hc
      · rw [tz 0 (by decide) (by decide), tz 2 (by decide) (by decide), hy]; exact J₂.jac.negY
      · rw [tz 2 (by decide) (by decide)]; exact J₂.z
      · rw [tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]; exact J₂.z2
      · rw [tz 4 (by decide) (by decide), tz 3 (by decide) (by decide), tz 2 (by decide) (by decide)]
        exact J₂.z3
    · simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte]
      simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte] at keepY
      rw [← ty] at keepY
      exact J₂.congr fun c hc => by
        by_cases h1 : c = 1
        · subst h1; exact keepY
        · exact keepT c hc h1
  · rw [tz 2 (by decide) (by decide)]
    exact T₂z 2 (by decide) (by rw [ha] at h; omega_arith)
  · rw [ha] at h ⊢
    rw [keepT 2 (by decide) (by decide), e₂' 2 (by decide), ite_eq_left_of_eq_true _ _ (eq_true h)]

end VG.Proof.Weierstrass.X86_64
