module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacOddState
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WinJacOdd
public import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacSelect
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.JacAdd
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# The odd window method on x86-64: the entry of a digit

Digit `j = rbx`: its window `e` of `oq J k`, read as the comb reads one
(`winIndex`, `hornerBits`), gives the entry `magO e = ((e ⊕ s) ∧ 15) + 1`
(`magnitudeO_ok`, `digitO_ok`), never zero, which is selected into `T`
(`jselect_ok`) and its `Y` negated for `e < 16` (`negY`, as the comb's), so
that `T` holds digit `j`'s point `oddPt` with its powers (`jentryO_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

variable {K : JacWinCfg} {size : Nat} {C : Curve}

/-- The entry of the odd digit of window `v`: `v - 15` for `v ≥ 16`, else `16 - v`. -/
def magO (v : Nat) : Nat := if 16 ≤ v then v - 15 else 16 - v

private theorem magO_fact : ∀ v < 32,
    ((BitVec.ofNat 64 v ^^^ BitVec.ofNat 64 v >>> 4 - BitVec.signExtend 64 (1 : BitVec 32)) &&&
        BitVec.signExtend 64 (15 : BitVec 32)) + BitVec.signExtend 64 (1 : BitVec 32) =
      BitVec.ofNat 64 (magO v) := by
  decide +kernel

/-- `rax = r8 = magO v` from the window `v < 32` in `rax`, through `rdx`. -/
theorem magnitudeO_ok (s : State) {v : Nat} (hv : v < 32) (hx : s.gpr .rax = BitVec.ofNat 64 v) :
    WP isa (.block JacWinCfg.magnitudeO) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (magO v) ∧ t.gpr .r8 = BitVec.ofNat 64 (magO v) ∧
        Keeps [.rax, .rdx, .r8] s t := by
  crun [JacWinCfg.magnitudeO, hx]
  rw [magO_fact v hv]
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2,
    ite_false]

theorem magO_pos {v : Nat} (hv : v < 32) : 1 ≤ magO v ∧ magO v ≤ 16 := by
  unfold magO; split <;> omega_arith

/-- The entry `magO e` of digit `rbx = j` into `rax` and `r8`, from window `j`
of `k` in its table of bits at `K.bits`. -/
theorem digitO_ok (K : JacWinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {k j N : Nat} (hj : 5 * j + 5 ≤ N) (hN : K.bits + N ≤ size)
    (hx : s.gpr .rbx = BitVec.ofNat 64 j)
    (hbits : ∀ t < N, s.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (.block K.digitO) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (magO (Window5.nib k j)) ∧
      t.gpr .r8 = BitVec.ofNat 64 (magO (Window5.nib k j)) ∧ Keeps [.rax, .rcx, .rdx, .r8] s t := by
  have hn := hs.nowrap
  have hj32 : j < 2 ^ 64 := by omega_arith
  rw [JacWinCfg.digitO, List.append_assoc, WP.block_append_iff]
  refine WP.mono (winIndex_ok s (by decide) hj32 hx) fun a ⟨a1, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hv : ∀ i, (fun t => (k.testBit (5 * j + (t - K.bits))).toNat) i ≤ 1 := fun _ => Bool.toNat_le _
  refine WP.mono (hornerBits_ok hv 5 K.bits (s := a) (by decide) fun i hi => ?_)
    fun b ⟨b2, kb⟩ => ?_
  · have he : a.ea (winByte (K.bits + i)) = off base (K.bits + (5 * j + i)) := by
      rw [ea_winByte ((ka.1 .rdi (by decide)).trans hs.rdi) a1]
      exact congrArg (off base) (by omega_arith)
    refine ⟨by rw [he]; exact ⟨_, List.mem_append_right _ (ka.2.2.2 ▸ hs.wr), hs.contains (by omega_arith) (by decide)⟩, ?_⟩
    rw [he, ka.2.1, hbits _ (by omega_arith), show K.bits + i - K.bits = i by omega_arith]
    cases k.testBit (5 * j + i) <;> rfl
  · have hw' : hornerVal (fun t => (k.testBit (5 * j + (t - K.bits))).toNat) K.bits 5 = Window5.nib k j := by
      have := hornerVal_eq k 5 j 5 (Nat.le_refl _)
      rw [Nat.sub_self, Nat.add_zero] at this
      rw [← Window5.combWin_five, combWin, ← this]
      exact hornerVal_congr fun i _ => by simp only [show K.bits + i - K.bits = i by omega_arith]
    refine WP.mono (magnitudeO_ok b (Window5.nib_lt k j) (by rw [b2, hw'])) fun t ⟨t1, t2, kt⟩ =>
      ⟨t1, t2, ((ka.mono (by decide)).trans (kb.mono (by decide))).trans (kt.mono (by decide))⟩

/-- The table of bits survives the method. -/
theorem JFrame.bitsO (hL : JacWinLay K size) {base : Addr} {s₀ s : State} {P : Point C} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) (hf : JFrame K C base size s₀ s) :
    ∀ t < 5 * K.J, s.mem (off base (K.bits + t)) = if (OddWin.oq K.J k).testBit t then 1 else 0 := by
  intro t ht
  have hb := hL.bits
  have hn := hf.scr.nowrap
  rw [hf.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_arith) (by omega_arith)]
  exact hF.bits t ht

/-- What `T` holds after the selection and the negation, from `s`: digit
`j`'s point with its powers. -/
structure JEntO (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (k j : Nat) (s t : State) : Prop where
  fr : JFrame K C base size s₀ t
  unch : Unch base ((List.range 5).map (fun c => (jg K (80 + c), 8 * K.M.n)) ++
    [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)]) s.mem t.mem
  keep : KeepRegs (clob K.M.n) s t
  ent : JPt C K.M.n base t (TS K) (OddWin.oddPt C P K.J k j)

/-- `T` holding entry `a = magO e` of digit `j`'s window `e`, its `Y` negated
for `e < 16`: `T` then holds digit `j`'s point with its powers. -/
theorem jnegO_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) {s₂ : State} {j : Nat} (hj : j < K.J)
    (F₂ : JFrame K C base size s₀ s₂) (hb : s₂.gpr .rbx = BitVec.ofNat 64 j)
    (T₂ : JPt C K.M.n base s₂ (TS K) (mul (2 * magO (Window5.nib (OddWin.oq K.J k) j) - 1) P)) :
    WP isa (.block K.tc.negY) s₂ fun s₅ => JFrame K C base size s₀ s₅ ∧
      Unch base [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)] s₂.mem s₅.mem ∧
      KeepRegs (clob K.M.n) s₂ s₅ ∧ JPt C K.M.n base s₅ (TS K) (OddWin.oddPt C P K.J k j) := by
  have hs₂ := F₂.scr
  have hn := hs₂.nowrap
  have hbl := hL.bits
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) (hF.ro_lt K.P.x (by simp))
  have hbits := F₂.bitsO hL hF
  generalize hk' : OddWin.oq K.J k = k' at hbits T₂
  generalize ha : magO (Window5.nib k' j) = a at T₂
  have hwj : 5 * j + 5 ≤ 5 * K.J := by omega_arith
  obtain ⟨tx, ty, tz, t2, t3⟩ := hL.TS_eq
  obtain ⟨mx, my, mz, m2, m3⟩ := hL.T_mem
  have hneg : K.neg ∈ jwSlots K := by jw_mem
  have hzero : K.zero ∈ jwSlots K := by jw_mem
  have hz₂ : wordsVal s₂.mem base K.zero K.M.n = 0 := by rw [F₂.ro hL (by jw_mem)]; exact hF.zero
  have hy₂ : wordsVal s₂.mem base K.E.y K.M.n < C.p := by rw [← ty]; exact T₂.lt 1 (by decide)
  have hyneg : K.E.y + 8 * K.M.n ≤ K.neg ∨ K.neg + 8 * K.M.n ≤ K.E.y := by
    rw [hL.Ty]; exact (hL.jg_apart (x := K.neg) (by jw_mem) (by decide)).symm
  rw [TCombCfg.negY, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sub_ok hs₂ F₂.mod (o := K.neg) (a := K.zero) (b := K.E.y) (hL.le hneg) (hL.le hzero)
    (hL.le my) (hL.lay.tmp _ hneg) (hL.lay.tmp _ hzero) (hL.lay.tmp _ my) (hL.lay.mo _ hneg)
    (by rw [hz₂]; exact hp0) hy₂) fun s₃ ⟨k₃, e₃⟩ => ?_
  have hs₃ := k₃.scr hs₂
  have hbits₃ : ∀ t < 5 * K.J, s₃.mem (off base (K.bits + t)) = if k'.testBit t then 1 else 0 := by
    intro t ht
    rw [k₃.unch.byte (fun w hw => by
      have hw' : w ∈ jwW K := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact mem_jwW_ws (other_ws (by jw_mem))
        · exact mem_jwW_tmp
      have := hL.bits_w w hw'; omega_arith) (by omega_arith)]
    exact hbits t ht
  rw [WP.block_append_iff]
  refine WP.mono (signMask_ok K.tc hs₃ (k := k') (j := j) (N := 5 * K.J) (by show 1 ≤ 5; decide)
    (by show 5 < 2 ^ 31; decide) hwj (by show K.bits + 5 * K.J ≤ size; omega_arith)
    (by rw [k₃.gpr _ (rbx_not_clob _), hb]) hbits₃) fun s₄ ⟨x₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have hwin : combWin K.tc.w k' j = Window5.nib k' j := Window5.combWin_five k' j
  rw [hwin] at x₄
  refine WP.mono (sel_ok (decide (Window5.nib k' j < 2 ^ (K.tc.w - 1))) K.M.n hs₄ x₄ (o := K.E.y)
    (a := K.E.y) (b := K.neg) (hL.le my) (hL.le my) (hL.le hneg) (Or.inl (Nat.le_refl _))
    (by omega_arith)) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have m₄ : s₄.mem = s₃.mem := k₄.2.1
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  have b64 : ∀ x ∈ jwSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by have := hL.le hx; omega_arith
  -- `T`'s words: as at `s₂` but `Y`.
  have keepT : ∀ c < 5, c ≠ 1 → wordsVal s₅.mem base (TS K c) K.M.n = wordsVal s₂.mem base (TS K c) K.M.n := by
    intro c hc h1
    have hy : TS K c + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ TS K c := by
      rw [hL.Ty]; exact jg_sep K (by omega_arith)
    rw [O₅.wordsVal hy (b64 _ (jg_mem (by omega_arith))), m₄, k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact (hL.jg_apart (x := K.neg) (by jw_mem) (i := 80 + c) (by omega_arith)).symm
      · exact hL.lay.tmp _ (jg_mem (by omega_arith))) (b64 _ (jg_mem (by omega_arith)))]
  have y₃ : wordsVal s₃.mem base K.E.y K.M.n = wordsVal s₂.mem base K.E.y K.M.n :=
    k₃.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hyneg
      · exact hL.lay.tmp _ my) (b64 _ my)
  have keepY : wordsVal s₅.mem base (TS K 1) K.M.n = if decide (Window5.nib k' j < 2 ^ (K.tc.w - 1)) then
      (0 + C.p - wordsVal s₂.mem base K.E.y K.M.n) % C.p else wordsVal s₂.mem base K.E.y K.M.n := by
    rw [ty, e₅, m₄, e₃, hz₂, y₃]
  have h16 : (2 : Nat) ^ (K.tc.w - 1) = 16 := rfl
  rw [h16] at keepY
  have hU : Unch base [(K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n), (jg K 81, 8 * K.M.n)] s₂.mem s₅.mem := by
    refine (k₃.unch.trans (m₄ ▸ O₅.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [h, hL.Ty]; exact Or.inr (Or.inr rfl)
  have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp [clob]
    · simp [clob]
    · simp [clob]
    · exact r8_mem_clob _
  have kk : KeepRegs (clob K.M.n) s₂ s₅ :=
    ((⟨k₃.gpr, k₃.rd, k₃.wr⟩ : KeepRegs (clob K.M.n) s₂ s₃).trans ((Keeps.regs k₄).mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))).trans
      (k₅.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))
  have tv : ∀ {x y : Nat}, wordsVal s₅.mem base x K.M.n = wordsVal s₂.mem base y K.M.n →
      tmv C K.M.n base s₅ x = tmv C K.M.n base s₂ y := fun h => by show toM _ _ _ = toM _ _ _; rw [h]
  have tz' : ∀ c < 5, c ≠ 1 → tmv C K.M.n base s₅ (TS K c) = tmv C K.M.n base s₂ (TS K c) :=
    fun c hc h1 => tv (keepT c hc h1)
  have hUL : Unch base (jwLoopW K) s₂.mem s₅.mem := hU.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_append_left _ (by jw_mem)))
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact T_loopW K (show 1 < 5 by decide)
  refine ⟨F₂.next hL hs₅ (kk.mono clob_powClob) hUL (jwLoopW_sub K), hU, kk, ?_⟩
  -- The point.
  have hoe : OddWin.oe K.J k j = Window5.nib k' j := by rw [← hk']; rfl
  rw [OddWin.oddPt, hoe]
  have hlt := Window5.nib_lt k' j
  have ha16 := magO_pos hlt
  rw [ha] at ha16
  by_cases hng : Window5.nib k' j < 16
  · have ha' : a = 16 - Window5.nib k' j := by
      rw [← ha, magO, ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), show 31 - 2 * Window5.nib k' j = 2 * a - 1 by omega_arith]
    simp only [decide_eq_true hng, ↓reduceIte] at keepY
    have hy : tmv C K.M.n base s₅ (TS K 1) = -tmv C K.M.n base s₂ (TS K 1) := by
      show toM _ _ _ = -toM _ _ _
      rw [keepY, toM_sub (by omega_arith), toM_zero, ty]
      grind
    refine ⟨fun c hc => ?_, ?_, ?_, ?_, ?_⟩
    · by_cases h1 : c = 1
      · subst h1; rw [keepY]; exact Nat.mod_lt _ hp0
      · rw [keepT c hc h1]; exact T₂.lt c hc
    · rw [tz' 0 (by decide) (by decide), tz' 2 (by decide) (by decide), hy]; exact T₂.jac.negY
    · rw [tz' 2 (by decide) (by decide)]; exact T₂.z
    · rw [tz' 3 (by decide) (by decide), tz' 2 (by decide) (by decide)]; exact T₂.z2
    · rw [tz' 4 (by decide) (by decide), tz' 3 (by decide) (by decide), tz' 2 (by decide) (by decide)]
      exact T₂.z3
  · have ha' : a = Window5.nib k' j - 15 := by
      rw [← ha, magO, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)), show 2 * Window5.nib k' j - 31 = 2 * a - 1 by omega_arith]
    simp only [decide_eq_false hng, Bool.false_eq_true, ↓reduceIte] at keepY
    rw [← ty] at keepY
    exact T₂.congr fun c hc => by
      by_cases h1 : c = 1
      · subst h1; exact keepY
      · exact keepT c hc h1

/-- Digit `j`'s entry into `T`, negated for a negative digit. -/
theorem jentryO_ok (hL : JacWinLay K size) {base : Addr} {P : Point C} {s₀ : State} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) {s : State} {j : Nat} (hj : j < K.J)
    (hf : JFrame K C base size s₀ s) (hT : JTblOkO K C base P 16 s) (hb : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (K.digitO ++ K.select)) s fun s₂ =>
      WP isa (.block K.tc.negY) s₂ (JEntO K C base size P s₀ k j s) := by
  have hs := hf.scr
  have hn := hs.nowrap
  have hbits := hf.bitsO hL hF
  have hwj : 5 * j + 5 ≤ 5 * K.J := by omega_arith
  have hbl := hL.bits
  rw [WP.block_append_iff]
  refine WP.mono (digitO_ok K hs (k := OddWin.oq K.J k) (j := j) (N := 5 * K.J) hwj
    (by omega_arith) hb hbits) fun s₁ ⟨_, r₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have ha16 := magO_pos (Window5.nib_lt (OddWin.oq K.J k) j)
  refine WP.mono (jselect_ok hL hs₁ r₁ ha16.2) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  rw [m₁] at e₂
  have U₂ : Unch base (jwLoopW K) s.mem s₂.mem := by
    rw [← m₁]; exact (outside_grid5 (b := 80) O₂).mono fun w hw => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw; exact T_loopW K (List.mem_range.mp hc)
  have F₂ := hf.next hL hs₂ (((Keeps.regs k₁).mono (sub_powClob (by decide))).trans
    (k₂.mono (sub_powClob (by decide)))) U₂ (jwLoopW_sub K)
  have e₂' : ∀ c < 5, wordsVal s₂.mem base (TS K c) K.M.n =
      wordsVal s.mem base (entS K (magO (Window5.nib (OddWin.oq K.J k) j)) c) K.M.n :=
    fun c hc => by rw [show TS K c = jg K (80 + c) from rfl, e₂ c hc, ite_eq_left_of_eq_true _ _ (eq_true ha16.1)]
  have T₂ := (hT _ ha16.1 ha16.2).congr fun c hc => e₂' c hc
  have hb₂ : s₂.gpr .rbx = BitVec.ofNat 64 j := by rw [k₂.gpr _ (by decide), k₁.1 _ (by decide), hb]
  refine WP.mono (jnegO_ok hL hF hj F₂ hb₂ T₂) fun s₅ ⟨F₅, U₅, kk₅, P₅⟩ => ⟨F₅, ?_, ?_, P₅⟩
  · rw [← m₁]
    refine ((outside_grid5 (b := 80) O₂).trans U₅).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · rw [h]; exact Or.inl (List.mem_map.mpr ⟨1, by decide, rfl⟩)
  · have hcl : ∀ r ∈ [Reg.rax, .rcx, .rdx, .r8], r ∈ clob K.M.n := by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · simp [clob]
      · simp [clob]
      · simp [clob]
      · exact r8_mem_clob _
    exact (((Keeps.regs k₁).mono hcl).trans (k₂.mono fun r hr => hcl r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h]))).trans kk₅

end VG.Proof.Weierstrass.X86_64
