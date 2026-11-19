module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Front
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Pieces
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
public import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Rsa.AArch64.InvLaw
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.Shared
meta import VerifiedGarbage.Proof.RsaKeyGen.KeyMath
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Key.State
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Spec.RsaKeyGen
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `RsaKeyGen.AArch64.Key.Lcm`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.AArch64.Key.Halve`, which only this module used -/

section

/-!
# An RSA key from its primes on AArch64: `φ` and the halving

`φ = (p − 1)(q − 1)` (`phi_k`), and a step of the halving of `u`, `v` and
`φ` while `u` and `v` are both even (`twoStep_k`, `halveStep`): the mask in
`x15`, and `halfIf` (`shr_ok` into `aT`, then `selLoop_ok`) on each.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## `φ` -/

/-- `phi`: `[aL] := [aPm] [aQm]` (`mulTo_k`). -/
theorem phi_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs phi) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aL] s.mem t.mem ∧
      wv t.mem I.B (slot I.W aL) (I.W + 2) = a * b :=
  mulTo_k h hW (o := aL) (a := aPm) (b := aQm) (by decide) (by decide) (by decide) (by decide) (by decide)
    ha hb ha' hb'

/-! ## Halving -/

theorem halve_shr {X x0 y : Nat} (h : 2 * y + x0 % 2 = X) (hx : X % 2 = x0 % 2) : y = X / 2 := by omega_arith

/-- `halfIf j`: `[j] := x15 ? [j] / 2 : [j]` (`shr_ok` into `aT`, then
`selLoop_ok`); word `W` of `[j]` must be 0 (`shrBody` reads it). -/
theorem halfIf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {c : Bool} (h15 : s.gpr .x15 = mask c) (htop : atop I s.mem j = 0) :
    WP isa (seqs (halfIf j)) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr j, .arr aT] s.mem t.mem ∧
      av I t.mem j = (if c then av I s.mem j / 2 else av I s.mem j) ∧ atop I t.mem j = 0 ∧
      Keep [.x3, .x4, .x11, .x12, .x14, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  obtain sj := h.ws.sl hj
  obtain sT := h.ws.sl (j := aT) (by decide)
  obtain sp := slot_sep (w := I.W) hjT
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  have hZ := h.hZ
  simp only [halfIf, seqs]
  rw [List.append_assoc]
  -- `[aT] := [j] / 2`.
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h.ws) fun s₁ ⟨⟨h12, h11, h14, m₁, _⟩, k₁⟩ =>
    WP.mono (base2_ok j aT .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_))
  obtain k12 := k₁.trans k₂
  refine WP.seq (WP.mono (shr_ok (h.ws.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14) hw1
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨hv₃, _, o₃, k₃⟩ => ?_)
  rw [m₂, m₁] at hv₃ o₃
  obtain f₃ := KF.arr1 (B := I.B) (W := I.W) (j := aT) o₃ (Nat.le_refl _) (by omega_arith)
  obtain k13 := k12.trans k₃
  obtain h₃ := h.step f₃ (all_mut_arr (by decide)) k13
  have htop' : word s.mem I.B (slot I.W j + 8 * I.W) = 0 := htop
  rw [htop'] at hv₃
  obtain hT₃ : av I s₃.mem aT = av I s.mem j / 2 := by
    refine halve_shr (x0 := (word s.mem I.B (slot I.W j)).toNat) (by simpa using hv₃) ?_
    exact (word_mod2 hw1).symm
  obtain hok : [Rc.arr aT].all Rc.ok = true := by decide
  obtain hj₃ : av I s₃.mem j = av I s.mem j := f₃.av hok hj (by simp [hjT]) hZ
  obtain tj₃ : atop I s₃.mem j = 0 := by rw [← htop]; exact f₃.at hok hj (by simp [hjT]) hZ
  -- `[j] := x15 ? [aT] : [j]`.
  rw [List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h₃.ws) fun s₄ ⟨⟨_, h11₄, h14₄, m₄, _⟩, k₄⟩ =>
    WP.mono (base2_ok aT j .x16 .x17 ((k₄.gpr .x0 (by decide)).trans h₃.ws.x0) h11₄)
      fun s₅ ⟨⟨h16₅, h17₅, m₅, _⟩, k₅⟩ => ?_))
  obtain k45 := k₄.trans k₅
  refine WP.mono (selLoop_ok (h₃.ws.scr.congr k45.wr) h16₅ h17₅ ((k₅.gpr .x14 (by decide)).trans h14₄)
    ((k13.trans k45).gpr .x15 (by decide) |>.trans h15) hw1 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨hv, o, k₆⟩ => ?_
  rw [m₅, m₄] at hv o
  obtain f := KF.arr1 (B := I.B) (W := I.W) (j := j) o (Nat.le_refl _) (by omega_arith)
  refine ⟨h₃.step f (all_mut_arr hj) (k45.trans k₆), (f₃.trans f).mono (by simp), ?_, ?_,
    ((k13.trans k45).trans k₆).mono (by decide)⟩
  · dsimp only [av] at hv hT₃ hj₃ ⊢
    rw [hv]
    cases c
    · exact hj₃
    · exact hT₃
  · dsimp only [atop] at tj₃ ⊢; rw [o.word (Or.inr (Nat.le_refl _)) (by omega_arith)]; exact tj₃

/-- The mask of `x` and `y` both even. -/
theorem halve_twoMask (x y : BitVec 64) :
    ((x ||| y) &&& BitVec.setWidth 64 1#16) - BitVec.ofNat 64 1 =
      mask (decide (x.toNat % 2 = 0 ∧ y.toNat % 2 = 0)) := by
  obtain e : ∀ z : BitVec 64, z &&& BitVec.setWidth 64 1#16 = BitVec.ofNat 64 (z.toNat % 2) := fun z => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.setWidth 64 1#16).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat]
    omega_arith
  rw [BitVec.and_or_distrib_right, e, e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y.toNat with hy | hy <;> rw [hx, hy] <;> decide

/-- What a step of the halving keeps and changes (x86's, without `sMo`). -/
def TwoP (I : KIn) (s₀ s t : State) : Prop :=
  KS I s₀ t ∧ KF I.B I.W [.arr aU, .arr aV, .arr aL, .arr aT] s.mem t.mem ∧
    atop I t.mem aU = 0 ∧ atop I t.mem aV = 0 ∧ atop I t.mem aL = 0

theorem TwoP.trans {I : KIn} {s₀ s t u : State} (h₁ : TwoP I s₀ s t) (h₂ : TwoP I s₀ t u) : TwoP I s₀ s u :=
  ⟨h₂.1, (h₁.2.1.trans h₂.2.1).mono (by decide), h₂.2.2⟩

/-- The mask of `u` and `v` both even into `x15`. -/
theorem twoMask_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ (base aU .x16 ++ (base aV .x17 ++ ([ld .x3 .x16, ld .x4 .x17,
      .logic .orr .x .x3 .x3 .x4, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr))))) s
      fun t => (t.mem = s.mem ∧ t.gpr .x15 = mask (decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0))) ∧
        Keep [.x3, .x4, .x11, .x12, .x15, .x16, .x17] s t := by
  have hn := h.ws.scr.nowrap
  obtain sU := h.ws.sl (j := aU) (by decide)
  obtain sV := h.ws.sl (j := aV) (by decide)
  obtain hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (wsBase16_ok h aU) fun s₁ ⟨⟨h16, _, h11, m₁⟩, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aV .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11) fun s₂ ⟨⟨h17, m₂, _⟩, k₂⟩ => ?_
  obtain hs₂ := h.ws.scr.congr (k₁.trans k₂).wr
  obtain h16₂ : s₂.gpr .x16 = off I.B (slot I.W aU) := (k₂.gpr .x16 (by decide)).trans h16
  obtain hm₂ : s₂.mem = s.mem := m₂.trans m₁
  refine WP.mono (WP.keep [.x3, .x4, .x15] (Q := fun t => t.mem = s.mem ∧
      t.gpr .x15 = mask (decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0))) (by
    brun [h16₂, h17, hs₂.ld (d := slot I.W aU) (by omega_arith), hs₂.ld (d := slot I.W aV) (by omega_arith), hm₂,
      halve_twoMask, word_mod2 (j := aU) hw1, word_mod2 (j := aV) hw1])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨q, k₃⟩ => ⟨q, ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- One step: the mask of `u` and `v` both even into `x15`
(`((u | v) & 1) − 1`), the three halvings, and `x6` counted down. -/
theorem twoStep_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa twoStep s fun t => TwoP I s₀ s t ∧ t.gpr .x6 = s.gpr .x6 - BitVec.ofNat 64 1 ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveStep (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hZ := h.hZ
  unfold twoStep
  simp only [List.append_assoc]
  generalize hc : decide (av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0) = c
  refine wp_seqs_append (by simp) (by simp [halfIf]) (WP.mono (twoMask_k h) fun s₁ ⟨⟨m₁, h15₁⟩, k₁⟩ => ?_)
  rw [hc] at h15₁
  obtain h₁ := h.regs m₁ k₁
  -- `u`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₁ (j := aU) (by decide)
    (by decide) h15₁ (by rw [m₁]; exact hU0)) fun s₂ ⟨h₂, f₂, vU₂, tU₂, k₂⟩ => ?_)
  obtain hok2 : [Rc.arr aU, Rc.arr aT].all Rc.ok = true := by decide
  obtain tV₂ : atop I s₂.mem aV = 0 := by rw [← hV0, ← m₁]; exact f₂.at hok2 (by decide) (by decide) hZ
  obtain tL₂ : atop I s₂.mem aL = 0 := by rw [← hL0, ← m₁]; exact f₂.at hok2 (by decide) (by decide) hZ
  obtain vV₂ : av I s₂.mem aV = av I s.mem aV := by rw [← m₁]; exact f₂.av hok2 (by decide) (by decide) hZ
  obtain vL₂ : av I s₂.mem aL = av I s.mem aL := by rw [← m₁]; exact f₂.av hok2 (by decide) (by decide) hZ
  -- `v`.
  refine wp_seqs_append (by simp [halfIf]) (by simp [halfIf]) (WP.mono (halfIf_k h₂ (j := aV) (by decide)
    (by decide) ((k₂.gpr .x15 (by decide)).trans h15₁) tV₂) fun s₃ ⟨h₃, f₃, vV₃, tV₃, k₃⟩ => ?_)
  obtain hok3 : [Rc.arr aV, Rc.arr aT].all Rc.ok = true := by decide
  obtain tU₃ : atop I s₃.mem aU = 0 := by rw [← tU₂]; exact f₃.at hok3 (by decide) (by decide) hZ
  obtain tL₃ : atop I s₃.mem aL = 0 := by rw [← tL₂]; exact f₃.at hok3 (by decide) (by decide) hZ
  obtain vU₃ : av I s₃.mem aU = av I s₂.mem aU := f₃.av hok3 (by decide) (by decide) hZ
  obtain vL₃ : av I s₃.mem aL = av I s.mem aL := by rw [← vL₂]; exact f₃.av hok3 (by decide) (by decide) hZ
  -- `φ`.
  refine wp_seqs_append (by simp [halfIf]) (by simp) (WP.mono (halfIf_k h₃ (j := aL) (by decide)
    (by decide) (((k₂.trans k₃).gpr .x15 (by decide)).trans h15₁) tL₃) fun s₄ ⟨h₄, f₄, vL₄, tL₄, k₄⟩ => ?_)
  obtain hok4 : [Rc.arr aL, Rc.arr aT].all Rc.ok = true := by decide
  obtain tU₄ : atop I s₄.mem aU = 0 := by rw [← tU₃]; exact f₄.at hok4 (by decide) (by decide) hZ
  obtain tV₄ : atop I s₄.mem aV = 0 := by rw [← tV₃]; exact f₄.at hok4 (by decide) (by decide) hZ
  obtain vU₄ : av I s₄.mem aU = av I s₂.mem aU := by rw [← vU₃]; exact f₄.av hok4 (by decide) (by decide) hZ
  obtain vV₄ : av I s₄.mem aV = av I s₃.mem aV := f₄.av hok4 (by decide) (by decide) hZ
  obtain k14 := ((k₁.trans k₂).trans k₃).trans k₄
  simp only [seqs]
  refine WP.mono (dec_ok s₄ .x6) fun t ⟨⟨h6, hm, _⟩, k₅⟩ => ⟨⟨h₄.regs hm k₅,
    by rw [hm, ← m₁]; exact (((f₂.trans f₃).trans f₄)).mono (by decide),
    by rw [hm]; exact tU₄, by rw [hm]; exact tV₄, by rw [hm]; exact tL₄⟩,
    by rw [h6, k14.gpr .x6 (by decide)], ?_⟩
  rw [hm, vU₄, vU₂, vV₄, vV₃, vL₄, vV₂, vL₃, m₁]
  unfold halveStep
  dsimp only
  rw [← hc]
  by_cases hb : av I s.mem aU % 2 = 0 ∧ av I s.mem aV % 2 = 0
  · simp [hb]
  · simp only [hb, decide_false, Bool.false_eq_true, ite_false]

end VG.Proof.RsaKeyGen.AArch64.Key

end

end


/-!
# An RSA key from its primes on AArch64: `lcm(p − 1, q − 1)`

The halving's loop (`twos_k`), `gcd(u, v)` after it (`gcdUV_k`), and
`lcmPart` (`lcm_k`): `[aL] := lcm(p − 1, q − 1)` (`lcm_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The loop -/

theorem lcm_ofNat_shl6 {W : Nat} (hW : W < 2 ^ 24) : BitVec.ofNat 64 W <<< 6 = BitVec.ofNat 64 (64 * W) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show W < 2 ^ 64 by omega_using [hW]), show (2 : Nat) ^ 6 = 64 from rfl, Nat.mul_comm]

/-- `ws` and `x6 := 64 W`. -/
theorem twosInit_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (.block (ws ++ ([.lsl .x .x6 .x12 6] : List Instr))) s fun t =>
      (t.gpr .x6 = BitVec.ofNat 64 (64 * I.W) ∧ t.mem = s.mem) ∧ Keep [.x6, .x11, .x12] s t := by
  have hw2 := h.ws.w2
  rw [WP.block_append_iff]
  refine WP.mono h.ws.ws_ok fun s₁ ⟨⟨h12, _, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (WP.keep [.x6] (Q := fun t => t.gpr .x6 = BitVec.ofNat 64 (64 * I.W) ∧ t.mem = s₁.mem)
    (by brun [h12, lcm_ofNat_shl6 hw2]) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h6, m₂⟩, k₂⟩ => ?_
  exact ⟨⟨h6, m₂.trans m₁⟩, (k₁.trans k₂).mono (by decide)⟩

/-- `64 W` steps (`x6 := W << 6`, then `wp_countdown` on `x6`). -/
theorem twos_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hV0 : atop I s.mem aV = 0) (hL0 : atop I s.mem aL = 0) :
    WP isa (seqs twos) s fun t => TwoP I s₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) =
        halveIter (64 * I.W) (av I s.mem aU, av I s.mem aV, av I s.mem aL) := by
  have hw1 := h.ws.w1
  have hw2 := h.ws.w2
  simp only [twos, seqs]
  refine WP.seq (WP.mono (twosInit_k h) fun s₁ ⟨⟨h6, m₁⟩, k₁⟩ => ?_)
  obtain h₁ := h.regs m₁ k₁
  refine WP.mono (wp_countdown (N := 64 * I.W) (by omega_using [hw2]) (by omega_using [hw1])
    (fun j t => TwoP I s₀ s t ∧
      (av I t.mem aU, av I t.mem aV, av I t.mem aL) = halveIter j (av I s.mem aU, av I s.mem aV, av I s.mem aL))
    (fun j _ t ⟨tp, tv⟩ _ => WP.mono (twoStep_k tp.1 tp.2.2.1 tp.2.2.2.1 tp.2.2.2.2)
      fun t' ⟨tp', h6', tv'⟩ => ⟨⟨tp.trans tp', by rw [tv', tv, halveIter_succ']⟩, h6'⟩)
    ⟨⟨h₁, KF.of_eq m₁, by rw [m₁]; exact hU0, by rw [m₁]; exact hV0, by rw [m₁]; exact hL0⟩, by rw [m₁]; rfl⟩ h6)
    fun t ht => ht

/-! ## `gcd(u, v)` -/

/-- `gcdUV`'s swap: `v` made odd (if it is even, `u` and `v` swapped). -/
theorem gcdSwap_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) :
    WP isa (seqs [.block (evenMaskOf aV ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17))),
      countLoop .x14 cswapBody]) s fun t => KS I s₀ t ∧ KF I.B I.W [.arr aU, .arr aV] s.mem t.mem ∧
      av I t.mem aU = (if av I s.mem aV % 2 = 0 then av I s.mem aV else av I s.mem aU) ∧
      av I t.mem aV = (if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV) ∧
      atop I t.mem aU = atop I s.mem aU := by
  have hn := h.ws.scr.nowrap
  obtain sU := h.ws.sl (j := aU) (by decide)
  obtain sV := h.ws.sl (j := aV) (by decide)
  obtain sp := slot_sep (w := I.W) (j := aU) (k := aV) (by decide)
  simp only [seqs]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (evenMaskOf_k h (j := aV) (by decide))
    fun s₁ ⟨h₁, m₁, h15, h12, h11, k₁⟩ => WP.block_append_iff.mpr (WP.mono (WP.keep [.x14]
      (Q := fun t => t.gpr .x14 = BitVec.ofNat 64 I.W ∧ t.mem = s₁.mem) (by brun [h12]) (by decide) (by decide)
      (by decide +kernel)) fun s₂ ⟨⟨h14, m₂⟩, k₂⟩ =>
    WP.mono (base2_ok aU aV .x16 .x17 ((k₂.gpr .x0 (by decide)).trans h₁.ws.x0) ((k₂.gpr .x11 (by decide)).trans h11))
      fun s₃ ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ?_)))
  obtain k13 := (k₁.trans k₂).trans k₃
  refine WP.mono (cswap_ok (h.ws.scr.congr k13.wr) h16 h17 (((k₂.trans k₃).gpr .x15 (by decide)).trans h15)
    ((k₃.gpr .x14 (by decide)).trans h14) (by have := h.ws.w1; omega_using [this]) (by have := h.ws.w2; omega_using [this]) (by omega_using [sU])
    (by omega_using [sV]) (by omega_using [sp])) fun t ⟨hX, hY, hf, k₄⟩ => ?_
  obtain hm : s₃.mem = s.mem := by rw [m₃, m₂, m₁]
  rw [hm] at hX hY hf
  simp only [decide_eq_true_eq] at hX hY
  obtain f : KF I.B I.W [.arr aU, .arr aV] s.mem t.mem :=
    KF.of_frm hf fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨.arr aU, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_using []⟩
      · exact ⟨.arr aV, by simp, by simp [Rc.range], by simp only [Rc.range]; omega_using []⟩
  refine ⟨h.step f (all_mut_arrs (js := [aU, aV]) (by decide)) (k13.trans k₄), f, hX, hY, ?_⟩
  exact hf.word_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega_using [sp]) (by omega_using [hn, sU])

/-- `ldh .x15 kOk`. -/
theorem ldOk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {c : Bool} (hok : word s.mem I.B (8 * kOk) = mask c) :
    WP isa (.block [ldh .x15 kOk]) s fun t => KS I s₀ t ∧ t.mem = s.mem ∧ t.gpr .x15 = mask c ∧
      Keep [.x15] s t := by
  obtain hld := h.ws.scr.ld (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  refine WP.mono (WP.keep [.x15] (Q := fun t => t.gpr .x15 = mask c ∧ t.mem = s.mem) (by
    brun [h.ws.x0, hdr_enc (show kOk < 32 by decide), hld, hok]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨h15, hm⟩, k⟩ => ⟨h.regs hm k, hm, h15, k⟩

/-- `gcdUV`: `v` made odd by a swap (`evenMaskOf_k`), the mask of `v < 2`
into `kOk`, `inverse` modulo `v` (3 if `v < 2`, by `selC_k`), and 1 for
`v < 2`. -/
theorem gcdUV_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KS I s₀ s) (hU0 : atop I s.mem aU = 0)
    (hodd : let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV; 2 ≤ v → v % 2 = 1) :
    WP isa (seqs gcdUV) s fun t => KS I s₀ t ∧
      KF I.B I.W [.arr aU, .arr aV, .arr aC, .arr aM, .arr aX₁, .arr aX₂, .arr aT, .hdr kOk] s.mem t.mem ∧
      av I t.mem aV =
        (let u := if av I s.mem aV % 2 = 0 then av I s.mem aV else av I s.mem aU
         let v := if av I s.mem aV % 2 = 0 then av I s.mem aU else av I s.mem aV
         if v ≤ 1 then 1 else Nat.gcd u v) := by
  have hw1 := h.ws.w1
  have hZ := h.hZ
  unfold gcdUV
  simp only [List.append_assoc]
  -- The swap.
  refine wp_seqs_append (by simp) (by simp [constA]) (WP.mono (gcdSwap_k h) fun s₂ ⟨h₂, f₂, hX, hY, tU⟩ => ?_)
  generalize hu0 : av I s.mem aU = u0 at hodd hX hY
  generalize hv0 : av I s.mem aV = v0 at hodd hX hY
  generalize hu1 : (if v0 % 2 = 0 then v0 else u0) = u1 at hX
  generalize hv1 : (if v0 % 2 = 0 then u0 else v0) = v1 at hodd hY
  dsimp only at hodd ⊢
  obtain tU₂ : atop I s₂.mem aU = 0 := tU.trans hU0
  -- `kOk := ` the mask of `v < 2`.
  refine wp_seqs_append (by simp [constA]) (by simp [ltA, cmpA]) (WP.mono (constA_k h₂ (x := 2) (by decide))
    fun s₃ ⟨h₃, f₃, c₃, _⟩ => ?_)
  obtain hokC : [Rc.arr aC].all Rc.ok = true := by decide
  obtain c2 : av I s₃.mem aC = 2 := av_of_full c₃ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega_using [hw1])))
  obtain vV₃ : av I s₃.mem aV = v1 := by rw [← hY]; exact f₃.av hokC (by decide) (by decide) hZ
  refine wp_seqs_append (by simp [ltA, cmpA]) (by simp) (WP.mono (ltA_k h₃ (a := aV) (b := aC) (by decide)
    (by decide)) fun s₄ ⟨h₄, m₄, h15₄, _, _⟩ => ?_)
  rw [vV₃, c2] at h15₄
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  obtain hst := h₄.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_using [this])
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₄.mem.writeW (off I.B (8 * kOk)) (mask (decide (v1 < 2))))
    (by brun [h₄.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15₄]) rfl rfl rfl) fun s₅ ⟨hm₅, k₅⟩ => ?_
  obtain ⟨h₅, f₅, ok₅⟩ := h₄.hdrW (i := kOk) (by unfold kOk sFn; omega_using []) hm₅ k₅
  obtain hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  -- `[aV] := 3` for `v < 2`.
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₅ (x := 3) (by decide))
    fun s₆ ⟨h₆, f₆, c₆, _⟩ => ?_)
  obtain c3 : av I s₆.mem aC = 3 := av_of_full c₆ (Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide)
    (show 2 ≤ 64 * I.W by omega_using [hw1])))
  obtain vV₆ : av I s₆.mem aV = v1 := by
    rw [← vV₃, f₆.av hokC (by decide) (by decide) hZ, f₅.av hokO (by decide) (by decide) hZ, m₄]
  obtain ok₆ : word s₆.mem I.B (8 * kOk) = mask (decide (v1 < 2)) := by
    rw [f₆.word hokC (by decide) (by decide), ok₅]
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.mono (ldOk_k h₆ ok₆) fun s₆' ⟨h₆', m₆', h15₆, _⟩ => ?_
  refine wp_seqs_append (by simp [selC]) (by simp) (WP.mono (selC_k h₆' (j := aV) (by decide) (by decide) h15₆)
    fun s₇ ⟨h₇, f₇, vV₇, _, _⟩ => ?_)
  rw [m₆', vV₆, c3] at vV₇
  generalize hM : (if decide (v1 < 2) = true then 3 else v1) = M at vV₇
  obtain hMo : M % 2 = 1 ∧ 1 < M := by
    rw [← hM]
    by_cases hv : v1 < 2
    · simp [hv]
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false]; exact ⟨hodd (by omega_using [hv]), by omega_using [hv]⟩
  -- The inverse modulo `M`.
  refine wp_seqs_append (by simp) (by simp [constA]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₇ (j := aM) (by decide)) fun s₇' ⟨h₇', f₇', _, _⟩ =>
    WP.seq (WP.mono (copyA_k h₇' (o := aM) (a := aV) (by decide) (by decide) (by decide))
    fun s₈ ⟨h₈, f₈', vM₈, _, _⟩ => WP.seq (WP.mono (zeroA_k h₈ (j := aX₁) (by decide)) fun s₉ ⟨h₉, f₉, z₉, _⟩ =>
      WP.seq (WP.mono (setOne_k h₉ (j := aX₁) (by decide) z₉) fun s₁₀ ⟨h₁₀, f₁₀, o₁₀, _⟩ =>
        WP.seq (WP.mono (zeroA_k h₁₀ (j := aX₂) (by decide)) fun s₁₁ ⟨h₁₁, f₁₁, z₁₁, _⟩ => ?_)))))
  obtain hokM : [Rc.arr aM].all Rc.ok = true := by decide
  obtain f₈ : KF I.B I.W [.arr aM] s₇.mem s₈.mem := (f₇'.trans f₈').mono (by decide)
  rw [f₇'.av hokM (j := aV) (by decide) (by decide) hZ] at vM₈
  obtain hok1 : [Rc.arr aX₁].all Rc.ok = true := by decide
  obtain hok2 : [Rc.arr aX₂].all Rc.ok = true := by decide
  obtain pres : ∀ j, j < 16 → j ≠ aM → j ≠ aX₁ → j ≠ aX₂ → av I s₁₁.mem j = av I s₇.mem j := fun j hj h1 h2 h3 => by
    rw [f₁₁.av hok2 hj (by simp [h3]) hZ, f₁₀.av hok1 hj (by simp [h2]) hZ, f₉.av hok1 hj (by simp [h2]) hZ,
      f₈.av hokM hj (by simp [h1]) hZ]
  obtain vU₁₁ : av I s₁₁.mem aU = u1 := by
    rw [pres aU (by decide) (by decide) (by decide) (by decide), ← hX,
      f₇.av (by decide) (j := aU) (by decide) (by decide) hZ, m₆', f₆.av hokC (by decide) (by decide) hZ,
      f₅.av hokO (by decide) (by decide) hZ, m₄, f₃.av hokC (by decide) (by decide) hZ]
  obtain vV₁₁ : av I s₁₁.mem aV = M := by rw [pres aV (by decide) (by decide) (by decide) (by decide), vV₇]
  obtain vM₁₁ : av I s₁₁.mem aM = M := by
    rw [f₁₁.av hok2 (by decide) (by decide) hZ, f₁₀.av hok1 (by decide) (by decide) hZ,
      f₉.av hok1 (by decide) (by decide) hZ, vM₈, vV₇]
  obtain vX₁ : av I s₁₁.mem aX₁ = 1 := by
    rw [f₁₁.av hok2 (by decide) (by decide) hZ]
    exact av_of_full o₁₀ (Nat.one_lt_two_pow (by omega_using [hw1]))
  obtain vX₂ : av I s₁₁.mem aX₂ = 0 := (wv_zero2 z₁₁).1
  obtain tU₁₁ : atop I s₁₁.mem aU = 0 := by
    rw [f₁₁.at hok2 (by decide) (by decide) hZ, f₁₀.at hok1 (by decide) (by decide) hZ,
      f₉.at hok1 (by decide) (by decide) hZ, f₈.at hokM (by decide) (by decide) hZ,
      f₇.at (by decide) (j := aU) (by decide) (by decide) hZ, m₆', f₆.at hokC (by decide) (by decide) hZ,
      f₅.at hokO (by decide) (by decide) hZ, m₄, f₃.at hokC (by decide) (by decide) hZ, tU₂]
  refine WP.mono (inverse_k h₁₁ (iU := aU) (iV := aV) (iX₁ := aX₁) (iX₂ := aX₂) (iM := aM) (iT := aT)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) tU₁₁ (by rw [vV₁₁, vM₁₁]) vX₁ vX₂) fun s₁₂ ⟨h₁₂, f₁₂, hinv⟩ => ?_
  rw [vM₁₁, vU₁₁] at hinv
  obtain hg := (hinv hMo.1 hMo.2).1
  -- The result 1 for `v < 2`.
  refine wp_seqs_append (by simp [constA]) (by simp) (WP.mono (constA_k h₁₂ (x := 1) (by decide))
    fun s₁₃ ⟨h₁₃, f₁₃, c₁₃, _⟩ => ?_)
  obtain c1 : av I s₁₃.mem aC = 1 := av_of_full c₁₃ (Nat.one_lt_two_pow (by omega_using [hw1]))
  obtain hokI : [Rc.arr aU, Rc.arr aV, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT].all Rc.ok = true := by decide
  obtain ok₁₃ : word s₁₃.mem I.B (8 * kOk) = mask (decide (v1 < 2)) := by
    rw [f₁₃.word hokC (by decide) (by decide), f₁₂.word hokI (by decide) (by decide),
      f₁₁.word hok2 (by decide) (by decide), f₁₀.word hok1 (by decide) (by decide),
      f₉.word hok1 (by decide) (by decide), f₈.word hokM (by decide) (by decide),
      f₇.word (by decide) (by decide) (by decide), m₆', ok₆]
  refine wp_seqs_append (by simp) (by simp [selC]) ?_
  simp only [seqs]
  refine WP.mono (ldOk_k h₁₃ ok₁₃) fun s₁₄ ⟨h₁₄, m₁₄, h15₁₄, _⟩ => ?_
  refine WP.mono (selC_k h₁₄ (j := aV) (by decide) (by decide) h15₁₄) fun t ⟨ht, f₁₅, vV, _, _⟩ => ?_
  obtain f₅' : KF I.B I.W [.hdr kOk] s₃.mem s₅.mem := by rw [← m₄]; exact f₅
  obtain f₇'' : KF I.B I.W [.arr aV] s₆.mem s₇.mem := by rw [← m₆']; exact f₇
  obtain f₁₅' : KF I.B I.W [.arr aV] s₁₃.mem t.mem := by rw [← m₁₄]; exact f₁₅
  refine ⟨ht, ?_, ?_⟩
  · exact (((((((((((f₂.trans f₃).trans f₅').trans f₆).trans f₇'').trans f₈).trans f₉).trans f₁₀).trans f₁₁).trans
      f₁₂).trans f₁₃).trans f₁₅').mono (by decide)
  · rw [vV, m₁₄, c1, f₁₃.av hokC (by decide) (by decide) hZ, hg]
    by_cases hv : v1 < 2
    · simp [hv, show v1 ≤ 1 by omega_using [hv]]
    · simp only [hv, decide_false, Bool.false_eq_true, ite_false, show ¬ v1 ≤ 1 by omega_using [hv]]
      rw [← hM]; simp [hv]

/-! ## The lcm -/

/-- Word `W` of a number of `W + 2` words below `2^(64 W)`. -/
theorem lcm_topZero {m : Mem} {B : Addr} {d W : Nat} (h : wv m B d (W + 2) < 2 ^ (64 * W)) :
    word m B (d + 8 * W) = 0 := by
  obtain e := wv_add m B d W 2
  have : wv m B (d + 8 * W) 2 = 0 := by
    rcases Nat.eq_zero_or_pos (wv m B (d + 8 * W) 2) with h0 | h0
    · exact h0
    · have := Nat.le_mul_of_pos_right (2 ^ (64 * W)) h0; omega_using [h, e, this]
  have := (wv_eq_zero_iff _ _ _ _).mp this 0 (by decide)
  simpa using this

theorem lcmPart_eq : lcmPart = phi ++ (([zeroA aU, copyA aU aPm, zeroA aV, copyA aV aQm] : List (Prog isa)) ++
    (twos ++ (gcdUV ++ ([divmod aL aR aV aT] : List (Prog isa))))) := by
  simp only [lcmPart, List.append_assoc]

/-- `lcmPart`: `[aL] := lcm(a, b)`. -/
theorem lcm_k [VG.Proof.Rsa.AArch64.InvLaw] {I : KIn} {s₀ s : State} (h : KS I s₀ s) {w : Nat} (hW : I.W = 2 * w)
    {a b : Nat} (ha : av I s.mem aPm = a) (hb : av I s.mem aQm = b) (ha' : a < 2 ^ (64 * w))
    (hb' : b < 2 ^ (64 * w)) :
    WP isa (seqs lcmPart) s fun t => KS I s₀ t ∧ KF I.B I.W csL s.mem t.mem ∧ av I t.mem aL = Nat.lcm a b := by
  have hZ := h.hZ
  have hw1 := h.ws.w1
  obtain hab : a * b < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * w) = 64 * w + 64 * w by omega_using [], Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le ha' (by omega_using [hb']) (Nat.two_pow_pos _)
  rw [lcmPart_eq]
  refine wp_seqs_append (by simp [phi, mulTo]) (by simp) (WP.mono (phi_k h hW ha hb ha' hb') fun s₁ ⟨h₁, f₁, v₁⟩ => ?_)
  obtain hokL : [Rc.arr aL].all Rc.ok = true := by decide
  obtain vL₁ : av I s₁.mem aL = a * b := av_of_full v₁ hab
  obtain tL₁ : atop I s₁.mem aL = 0 := lcm_topZero (by rw [v₁]; exact hab)
  obtain vP₁ : av I s₁.mem aPm = a := by rw [f₁.av hokL (by decide) (by decide) hZ]; exact ha
  obtain vQ₁ : av I s₁.mem aQm = b := by rw [f₁.av hokL (by decide) (by decide) hZ]; exact hb
  refine wp_seqs_append (by simp) (by simp [twos]) ?_
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_k h₁ (j := aU) (by decide)) fun s₂ ⟨h₂, f₂, z₂, _⟩ =>
    WP.seq (WP.mono (copyA_k h₂ (o := aU) (a := aPm) (by decide) (by decide) (by decide)) fun s₃ ⟨h₃, f₃, v₃, t₃, _⟩ =>
      WP.seq (WP.mono (zeroA_k h₃ (j := aV) (by decide)) fun s₄ ⟨h₄, f₄, z₄, _⟩ =>
        WP.mono (copyA_k h₄ (o := aV) (a := aQm) (by decide) (by decide) (by decide))
          fun s₅ ⟨h₅, f₅, v₅, t₅, _⟩ => ?_)))
  obtain hU : [Rc.arr aU].all Rc.ok = true := by decide
  obtain hV : [Rc.arr aV].all Rc.ok = true := by decide
  obtain vU₅ : av I s₅.mem aU = a := by
    rw [f₅.av hV (by decide) (by decide) hZ, f₄.av hV (by decide) (by decide) hZ, v₃,
      f₂.av hU (by decide) (by decide) hZ, vP₁]
  obtain vV₅ : av I s₅.mem aV = b := by
    rw [v₅, f₄.av hV (by decide) (by decide) hZ, f₃.av hU (by decide) (by decide) hZ,
      f₂.av hU (by decide) (by decide) hZ, vQ₁]
  obtain vL₅ : av I s₅.mem aL = a * b := by
    rw [f₅.av hV (by decide) (by decide) hZ, f₄.av hV (by decide) (by decide) hZ,
      f₃.av hU (by decide) (by decide) hZ, f₂.av hU (by decide) (by decide) hZ, vL₁]
  obtain tU₅ : atop I s₅.mem aU = 0 := by
    rw [f₅.at hV (by decide) (by decide) hZ, f₄.at hV (by decide) (by decide) hZ, t₃]; exact (wv_zero2 z₂).2
  obtain tV₅ : atop I s₅.mem aV = 0 := by rw [t₅]; exact (wv_zero2 z₄).2
  obtain tL₅ : atop I s₅.mem aL = 0 := by
    rw [f₅.at hV (by decide) (by decide) hZ, f₄.at hV (by decide) (by decide) hZ,
      f₃.at hU (by decide) (by decide) hZ, f₂.at hU (by decide) (by decide) hZ, tL₁]
  -- The halving.
  refine wp_seqs_append (by simp [twos]) (by simp [gcdUV]) (WP.mono (twos_k h₅ tU₅ tV₅ tL₅)
    fun s₆ ⟨⟨h₆, f₆, tU₆, _, _⟩, hv₆⟩ => ?_)
  rw [vU₅, vV₅, vL₅] at hv₆
  obtain hK : a < 2 ^ (64 * I.W) ∧ b < 2 ^ (64 * I.W) := by
    rw [hW]; exact ⟨Nat.lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by decide) (by omega_using [])),
      Nat.lt_of_lt_of_le hb' (Nat.pow_le_pow_right (by decide) (by omega_using []))⟩
  obtain hle := lcm_eq hK.1 hK.2
  dsimp only at hle
  generalize halveIter (64 * I.W) (a, b, a * b) = st at hv₆ hle
  obtain ⟨x, y, f⟩ := st
  simp only [Prod.mk.injEq] at hv₆
  obtain ⟨hx, hy, hf⟩ := hv₆
  dsimp only at hle
  -- `gcd(u, v)`.
  refine wp_seqs_append (by simp [gcdUV]) (by simp) (WP.mono (gcdUV_k h₆ tU₆ (by rw [hx, hy]; exact hle.1))
    fun s₇ ⟨h₇, f₇, vV₇⟩ => ?_)
  rw [hx, hy] at vV₇
  dsimp only at vV₇
  obtain hokG : [Rc.arr aU, Rc.arr aV, Rc.arr aC, Rc.arr aM, Rc.arr aX₁, Rc.arr aX₂, Rc.arr aT,
    Rc.hdr kOk].all Rc.ok = true := by decide
  obtain vL₇ : av I s₇.mem aL = f := by rw [f₇.av hokG (by decide) (by decide) hZ, hf]
  generalize hg : (if (if y % 2 = 0 then x else y) ≤ 1 then 1 else
    Nat.gcd (if y % 2 = 0 then y else x) (if y % 2 = 0 then x else y)) = g at vV₇ hle
  obtain hg0 : 0 < g := by
    rw [← hg]
    generalize (if y % 2 = 0 then x else y) = v
    generalize (if y % 2 = 0 then y else x) = u
    by_cases hv : v ≤ 1
    · simp [hv]
    · simp only [hv, ite_false]; exact Nat.gcd_pos_of_pos_right _ (by omega_using [hv])
  simp only [seqs]
  refine WP.mono (divmod_k h₇ (iQ := aL) (iR := aR) (iD := aV) (iT := aT) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun t ⟨ht, f₈, hd⟩ => ⟨ht, ?_, ?_⟩
  · have f₂₅ := ((f₂.trans f₃).trans f₄).trans f₅
    exact ((((f₁.trans f₂₅).trans f₆).trans f₇).trans f₈).mono (by decide)
  · rw [vV₇] at hd
    rw [(hd hg0).2, vL₇, hle.2]

end VG.Proof.RsaKeyGen.AArch64.Key

end

end

/-!
# An RSA key from its primes on AArch64: constant time, `lcm(p − 1, q − 1)`

The product (`mulTo_ct0`, `phi_ct`), the copies of `p − 1` and `q − 1`
(`zc_ct`, which leave their top words zero, as the halving and `inverse`
need of `u`), the halving's loop (`twos_ct`, by `two_loop` over the steps,
whose count `x6` correctness ties to the public `W`), `gcdUV` (`gcdUV_ct`)
and the division; the facts after `lcmPart` from `lcm_k` (`lcmPart_ct`, to
`KG LF`).

`halfIf`'s two halves each reload `w` and the stride: the first is checked
from `KG`, the second from `KS` after the first (`shrHalf_k`), and the
facts after both come from `halfIf_k`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Key
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero ne_zero_iff)
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## The product -/

theorem mulTo_eq (o a b : Nat) : seqs (mulTo o a b) = .seq (zeroA o) (.seq (.block (ws ++ (base b .x9 ++
    (base o .x8 ++ (base a .x16 ++ ([mov .x11 .x16, .lsr .x .x12 .x12 1, mov .x13 .x12, movi .x7 0] :
      List Instr)))))) VG.Impl.Rsa.AArch64.Crt.mulRows) := by
  simp only [mulTo, seqs, List.append_assoc]

/-- `[o] := [a] [b]`, as `phi` and `nPart` compute it, with no
postcondition. -/
theorem mulTo_ct0 {F : KIn → State → Prop} {o a b : Nat} (ho : o < 16) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base o .x8 ++ ([movi .x7 0] : List Instr)))
      zeroAcc) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base b .x9 ++ (base o .x8 ++ (base a .x16 ++
      ([mov .x11 .x16, .lsr .x .x12 .x12 1, mov .x13 .x12, movi .x7 0] : List Instr)))))
      VG.Impl.Rsa.AArch64.Crt.mulRows) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (mulTo o a b)) fun _ _ => True := by
  rw [mulTo_eq]
  exact kg_then (G := NF) (zeroA_ct0 ht₁) (fun I _ s h _ _ => WP.mono (zeroA_k h ho) fun _ ⟨ht, _⟩ =>
    ⟨ht, trivial⟩) (kg_ws0 ht₂)

theorem lt_pow_half {I : KIn} {x : Nat} (hx : x < 2 ^ (64 * (I.pl / 8))) (y : Nat) :
    x - y < 2 ^ (64 * (I.pl / 8)) :=
  Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx

/-- `phi`, from the front, with word `W` of `φ` zero. -/
theorem phi_ct : RelCT isa (Two (KG PF)) (seqs phi) (Two (KG (TopZ aL))) :=
  kg_ct (mulTo_ct0 (by decide) (by taint_decide) (by taint_decide)) fun I _ s h L ⟨_, _, hPm, hQm, _⟩ => by
    have hPw := lt_pow_half L.P_lt 1
    have hQw := lt_pow_half L.Q_lt 1
    have hW := L.W
    refine WP.mono (phi_k h hW hPm hQm hPw hQw) fun t ⟨ht, _, v⟩ => ⟨ht, lcm_topZero ?_⟩
    rw [v, hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega_arith, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hPw (by omega_arith) (Nat.two_pow_pos _)

/-! ## The halving -/

/-- The registers `halfIf` changes. -/
abbrev hfRegs : List Reg := [.x3, .x4, .x11, .x12, .x14, .x16, .x17]

theorem halfIf_eq (j : Nat) : seqs (halfIf j) = .seq (.block (ws ++ (([mov .x14 .x12] : List Instr) ++
    (base j .x16 ++ base aT .x17)))) (.seq (countLoop .x14 shrBody) (.seq (.block (ws ++
      (([mov .x14 .x12] : List Instr) ++ (base aT .x16 ++ base j .x17)))) VG.Impl.Rsa.AArch64.Crt.selLoop)) := by
  simp only [halfIf, seqs, List.append_assoc]

/-- `halfIf`'s first half: `[aT] := [j] / 2`. -/
theorem shrHalf_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {j : Nat} (hj : j < 16) (hjT : j ≠ aT) :
    WP isa (.seq (.block (ws ++ (([mov .x14 .x12] : List Instr) ++ (base j .x16 ++ base aT .x17))))
      (countLoop .x14 shrBody)) s (KS I s₀) := by
  have hn := h.ws.scr.nowrap
  have sj := h.ws.sl hj
  have sT := h.ws.sl (j := aT) (by decide)
  have sp := slot_sep (w := I.W) hjT
  have hw1 : 1 ≤ I.W := by have := h.ws.w1; omega_arith
  have hw2 := h.ws.w2
  rw [← List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (wsMov_ok h.ws) fun s₁ ⟨⟨_, h11, h14, m₁, _⟩, k₁⟩ =>
    WP.mono (base2_ok j aT .x16 .x17 ((k₁.gpr .x0 (by decide)).trans h.ws.x0) h11)
      fun s₂ ⟨⟨h16, h17, m₂, _⟩, k₂⟩ => ?_))
  have k12 := k₁.trans k₂
  refine WP.mono (shr_ok (h.ws.scr.congr k12.wr) h16 h17 ((k₂.gpr .x14 (by decide)).trans h14) hw1
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨_, _, o₃, k₃⟩ => ?_
  rw [m₂, m₁] at o₃
  have f₃ := KF.arr1 (B := I.B) (W := I.W) (j := aT) o₃ (Nat.le_refl _) (by omega_arith)
  exact h.step f₃ (all_mut_arr (by decide)) (k12.trans k₃)

theorem halfIf_ct0 {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base j .x16 ++ base aT .x17))) (countLoop .x14 shrBody)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base aT .x16 ++ base j .x17))) VG.Impl.Rsa.AArch64.Crt.selLoop) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (halfIf j)) fun _ _ => True := by
  rw [halfIf_eq]
  exact RelCT.assoc (kg_then (G := NF) (kg_ws0 ht₁) (fun I _ s h _ _ => WP.mono (shrHalf_k h hj hjT) fun t ht =>
    ⟨ht, trivial⟩) (kg_ws0 ht₂))

/-- `halfIf j`, from a mask in `x15` and word `W` of `[j]` zero, for facts
`F` that its changes keep. -/
theorem halfIf_ct {F : KIn → State → Prop} {j : Nat} (hj : j < 16) (hjT : j ≠ aT)
    (h0 : ∀ I s, F I s → X15M I s ∧ TopZ j I s)
    (hFG : ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → F I s → KF I.B I.W [.arr j, .arr aT] s.mem t.mem → Keep hfRegs s t →
      TopZ j I t → F I t)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base j .x16 ++ base aT .x17))) (countLoop .x14 shrBody)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (([mov .x14 .x12] : List Instr) ++
      (base aT .x16 ++ base j .x17))) VG.Impl.Rsa.AArch64.Crt.selLoop) hc₂).isSome = true) :
    RelCT isa (Two (KG F)) (seqs (halfIf j)) (Two (KG F)) :=
  kg_ct (halfIf_ct0 hj hjT ht₁ ht₂) fun I _ s h _ hf => by
    obtain ⟨⟨_, h15⟩, t0⟩ := h0 I s hf
    exact WP.mono (halfIf_k h hj hjT h15 t0) fun t ⟨ht, f, _, tj, k⟩ => ⟨ht, hFG I s t h.hZ hf f k tj⟩

/-- Words `W` of `u`, `v` and `φ` zero: what a step of the halving needs. -/
abbrev TwB : KIn → State → Prop := fun I t => TopZ aU I t ∧ TopZ aV I t ∧ TopZ aL I t

/-- `TwB` and a mask in `x15`: between the parts of a step. -/
abbrev TwM : KIn → State → Prop := fun I t => TwB I t ∧ X15M I t

theorem twb_mem {I : KIn} {s t : State} (h : TwB I s) (hm : t.mem = s.mem) : TwB I t := by
  obtain ⟨a, b, c⟩ := h
  have e : ∀ j, atop I t.mem j = atop I s.mem j := fun j => by rw [hm]
  exact ⟨(e aU).trans a, (e aV).trans b, (e aL).trans c⟩

/-- `TwM` after `halfIf j`. -/
theorem twm_step {j : Nat} (hj : j < 16) :
    ∀ I s t, slot I.W 16 ≤ 2 ^ 64 → TwM I s → KF I.B I.W [.arr j, .arr aT] s.mem t.mem → Keep hfRegs s t →
      TopZ j I t → TwM I t := fun I s t hZ ⟨⟨tU, tV, tL⟩, c, h15⟩ f k tj => by
  have hok : [Rc.arr j, Rc.arr aT].all Rc.ok = true := by
    simp only [List.all_cons, List.all_nil, Rc.ok, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hj, by decide⟩
  have top : ∀ i, i < 16 → i ≠ aT → atop I s.mem i = 0 → atop I t.mem i = 0 := fun i hi hiT h0 =>
    if e : i = j then by rw [e]; exact tj else (f.at hok hi (by simp [e, hiT]) hZ).trans h0
  exact ⟨⟨top aU (by decide) (by decide) tU, top aV (by decide) (by decide) tV, top aL (by decide) (by decide) tL⟩,
    c, (k.gpr .x15 (by decide)).trans h15⟩

theorem twoStep_eq : twoStep = seqs (([.block (ws ++ (base aU .x16 ++ (base aV .x17 ++ ([ld .x3 .x16, ld .x4 .x17,
    .logic .orr .x .x3 .x3 .x4, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] : List Instr))))] :
    List (Prog isa)) ++ (halfIf aU ++ (halfIf aV ++ (halfIf aL ++
      ([.block [.subImm .x .x6 .x6 1]] : List (Prog isa)))))) := by
  simp only [twoStep, List.append_assoc]

/-- A step of the halving, with no postcondition. -/
theorem twoStep_ct0 : RelCT isa (Two (KG TwB)) twoStep fun _ _ => True := by
  rw [twoStep_eq]
  refine rs_app (R := Two (KG TwM)) (by simp) (by simp [halfIf])
    (show RelCT isa _ (seqs [.block _]) _ from kg_wsb (by taint_decide) fun I _ s h _ hf =>
      WP.mono (twoMask_k h) fun t ⟨⟨hm, h15⟩, k⟩ => ⟨h.regs hm k, twb_mem hf hm, _, h15⟩) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide)
    (fun _ _ ⟨⟨t, _⟩, c⟩ => ⟨c, t⟩) (twm_step (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp [halfIf]) (halfIf_ct (by decide) (by decide)
    (fun _ _ ⟨⟨_, t, _⟩, c⟩ => ⟨c, t⟩) (twm_step (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp [halfIf]) (by simp) (halfIf_ct (by decide) (by decide)
    (fun _ _ ⟨⟨_, _, t⟩, c⟩ => ⟨c, t⟩) (twm_step (by decide)) (by taint_decide) (by taint_decide)) ?_
  exact (two_taint [.x0] (pins_kg TwM) (by taint_decide) :
    RelCT isa _ (.block [.subImm .x .x6 .x6 1]) fun _ _ => True)

/-- Before step `j` of the halving: `TwB`, and `64 W − j` steps left in `x6`. -/
abbrev TwX (j : Nat) : KIn → State → Prop := fun I t => TwB I t ∧ t.gpr .x6 = BitVec.ofNat 64 (64 * I.W - j)

theorem twos_eq : seqs twos = .seq (.block (ws ++ ([.lsl .x .x6 .x12 6] : List Instr)))
    (.loop twoStep (.nonzero .x .x6)) := rfl

theorem ofNat_sub_one_k {p : Nat} (hp : 1 ≤ p) (hp' : p < 2 ^ 64) :
    BitVec.ofNat 64 p - BitVec.ofNat 64 1 = BitVec.ofNat 64 (p - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp',
    Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show p - 1 < 2 ^ 64 by omega_arith)]
  omega_arith

/-- The halving's loop: `64 W` steps, a public count. -/
theorem twosLoop_ct : RelCT isa (Two (KG (TwX 0))) (.loop twoStep (.nonzero .x .x6)) (Two (KG (TopZ aU))) := by
  refine (two_loop (Φ := fun p j s => KG (TwX j) p s) (Ψ := KG (TopZ aU)) (fun p : KP => 64 * p.q.W)
    (two_map Prod.fst (fun _ _ h => h.2.imp fun _ h => h.1) twoStep_ct0) ?_).mono ?_ fun _ _ h => h
  · intro p j s hj ⟨I, s₀, he, hst, hk, L, O, ⟨tU, tV, tL⟩, h6⟩
    have hW := KIn.pub_W he
    have hw2 := hk.ws.w2
    refine WP.mono (twoStep_k hk tU tV tL) fun t ⟨⟨ht, _, tU', tV', tL'⟩, h6', _⟩ => ?_
    have e6 : t.gpr .x6 = BitVec.ofNat 64 (64 * I.W - (j + 1)) := by
      rw [h6', h6, ofNat_sub_one_k (by omega_arith) (by omega_arith), Nat.sub_sub]
    refine ⟨?_, fun _ => ⟨I, s₀, he, hst, ht, L, O, ⟨tU', tV', tL'⟩, e6⟩,
      fun _ => ⟨I, s₀, he, hst, ht, L, O, tU'⟩⟩
    rw [eval_nonzero, e6, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  · intro s₁ s₂ h
    refine two_mono (fun p s h => ⟨?_, h⟩) h
    obtain ⟨I, _, he, -, hk, -⟩ := h
    have := hk.ws.w1
    rw [← KIn.pub_W he]; omega_arith

/-- The halving: `x6 := 64 W`, then the loop. -/
theorem twos_ct : RelCT isa (Two (KG TwB)) (seqs twos) (Two (KG (TopZ aU))) := by
  rw [twos_eq]
  exact RelCT.seq (kg_wsb (G := TwX 0) (by taint_decide) fun I _ s h _ hf =>
    WP.mono (twosInit_k h) fun t ⟨⟨h6, hm⟩, k⟩ => ⟨h.regs hm k, twb_mem hf hm, by rw [h6, Nat.sub_zero]⟩)
    twosLoop_ct

/-! ## `gcd(u, v)` -/

/-- `x15`'s mask into `kOk`. -/
theorem stOk_k {I : KIn} {s₀ s : State} (h : KS I s₀ s) {c : Bool} (h15 : s.gpr .x15 = mask c) :
    WP isa (.block [sth .x15 kOk]) s fun t => KS I s₀ t ∧ KF I.B I.W [.hdr kOk] s.mem t.mem ∧
      word t.mem I.B (8 * kOk) = mask c ∧ Keep [] s t := by
  have hst := h.ws.scr.st (d := 8 * kOk) (by have := h.ws.h256; unfold kOk sFn; omega_arith)
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off I.B (8 * kOk)) (mask c))
    (by brun [h.ws.x0, hdr_enc (show kOk < 32 by decide), hst, h15]) rfl rfl rfl) fun t ⟨hm, k⟩ => ?_
  obtain ⟨ht, f, hw⟩ := h.hdrW (i := kOk) (by unfold kOk sFn; omega_arith) hm k
  exact ⟨ht, f, hw, k⟩

/-- `stOk_k`, for facts `F` that survive it. -/
theorem stOk_ct {F : KIn → State → Prop} (hF : Stab F [.hdr kOk] []) :
    RelCT isa (Two (KG fun I t => F I t ∧ X15M I t)) (.block [sth .x15 kOk])
      (Two (KG fun I t => F I t ∧ KokM I t)) :=
  kg_x0 (by taint_decide) fun I _ s h _ ⟨hf, _, h15⟩ => WP.mono (stOk_k h h15) fun t ⟨ht, f, hw, k⟩ =>
    ⟨ht, hF I s t h.hZ hf f k, _, hw⟩

/-- `ldOk_k`, for facts `F`: `kOk`'s mask into `x15`. -/
theorem ldOk_ct {F : KIn → State → Prop} (hF : ∀ I s t, F I s → t.mem = s.mem → Keep [.x15] s t → F I t) :
    RelCT isa (Two (KG fun I t => F I t ∧ KokM I t)) (.block [ldh .x15 kOk])
      (Two (KG fun I t => (F I t ∧ KokM I t) ∧ X15M I t)) :=
  kg_x0 (by taint_decide) fun I _ s h _ ⟨hf, c, hk⟩ => WP.mono (ldOk_k h hk) fun t ⟨ht, hm, h15, k⟩ =>
    ⟨ht, ⟨hF I s t hf hm k, c, by rw [hm]; exact hk⟩, _, h15⟩

/-- `inverse`'s start from the copy into `[o]` of `[a]`: `x₁ := 1`,
`x₂ := 0`. -/
theorem invStart_ct {F : KIn → State → Prop} {o a : Nat} (ho : o < 16) (ha : a < 16) (hoa : o ≠ a)
    (ho1 : o ≠ aX₁) (ho2 : o ≠ aX₂) (ha1 : a ≠ aX₁) (ha2 : a ≠ aX₂) (hF : Stab F [.arr o, .arr aX₁, .arr aX₂] allR)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0, .x12, .x11]) (.seq (.block (base a .x16 ++ base o .x17)) copyWords)
      hc).isSome = true) :
    RelCT isa (Two (KG F)) (seqs [copyA o a, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂])
      (Two (KG fun I t => F I t ∧ AvEq o a I t ∧ AvIs aX₁ 1 I t ∧ AvIs aX₂ 0 I t)) := by
  have sE : ∀ (cs : List Rc), cs.all Rc.ok = true → .arr o ∉ cs → .arr a ∉ cs → Stab (AvEq o a) cs allR :=
    fun _ hok h1 h2 => stab_aveq _ ho ha hok h1 h2
  have ok1 : [Rc.arr aX₁].all Rc.ok = true := by decide
  have ok2 : [Rc.arr aX₂].all Rc.ok = true := by decide
  simp only [seqs]
  refine RelCT.seq (R := Two (KG fun I t => F I t ∧ AvEq o a I t)) (kg_ct (copyA_ct0 ht) fun I _ s h _ hf =>
    WP.mono (copyA_k h ho ha hoa) fun t ⟨ht, f, v, _, k⟩ =>
      ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
        by dsimp only [AvEq]; rw [v, f.av (by simp [Rc.ok, ho]) ha (by simp [hoa.symm]) h.hZ]⟩) ?_
  refine RelCT.seq (zeroAZ_ct (F := fun I t => F I t ∧ AvEq o a I t) (by decide)
    (stab_and (hF.mono (by simp) (by decide)) ((sE [.arr aX₁] ok1 (by simp [ho1]) (by simp [ha1])).sub))
    (by taint_decide)) ?_
  refine RelCT.seq (setOne_ct (G := fun I t => F I t ∧ AvEq o a I t ∧ AvIs aX₁ 1 I t) (by decide)
    (fun I s t hZ _ ⟨hf, he⟩ f k v =>
    ⟨hF I s t hZ hf (f.mono (by simp)) (k.mono (by decide)),
      sE [.arr aX₁] ok1 (by simp [ho1]) (by simp [ha1]) I s t hZ he f (k.mono (by decide)), v⟩) (by taint_decide)) ?_
  exact kg_ct (zeroA_ct0 (by taint_decide)) fun I _ s h _ ⟨hf, he, h1⟩ => WP.mono (zeroA_k h (j := aX₂) (by decide))
    fun t ⟨ht, f, z, _, k⟩ => ⟨ht, hF I s t h.hZ hf (f.mono (by simp)) (k.mono (by decide)),
      sE [.arr aX₂] ok2 (by simp [ho2]) (by simp [ha2]) I s t h.hZ he f (k.mono (by decide)),
      stab_av _ (by decide) (by decide) (by decide) I s t h.hZ h1 f k, av_of_full z (Nat.two_pow_pos _)⟩

theorem gcdSwap_eq : evenMaskOf aV ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17)) =
    ws ++ (base aV .x16 ++ (([ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1] :
      List Instr) ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17)))) := by
  simp only [evenMaskOf, List.append_assoc]

theorem gcdUV_eq2 : gcdUV = ([.block (evenMaskOf aV ++ (([mov .x14 .x12] : List Instr) ++ (base aU .x16 ++ base aV .x17))),
    countLoop .x14 cswapBody] : List (Prog isa)) ++ (constA 2 ++ (ltA aV aC ++
    (([.block [sth .x15 kOk]] : List (Prog isa)) ++ (constA 3 ++ (([.block [ldh .x15 kOk]] : List (Prog isa)) ++
    (selC aV ++ (([zeroA aM, copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂, inverse aU aV aX₁ aX₂ aM aT] :
      List (Prog isa)) ++ (constA 1 ++ (([.block [ldh .x15 kOk]] : List (Prog isa)) ++ selC aV))))))))) := by
  simp only [gcdUV, List.append_assoc]

/-- `gcdUV`, from word `W` of `u` zero. -/
theorem gcdUV_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG (TopZ aU))) (seqs gcdUV) (Two (KG NF)) := by
  have sT : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .arr aU ∉ cs → Stab (TopZ aU) cs rs :=
    fun _ rs hok hn => stab_top rs (by decide) hok hn
  have sK : ∀ (cs : List Rc) (rs : List Reg), cs.all Rc.ok = true → .hdr kOk ∉ cs → Stab KokM cs rs :=
    fun _ rs hok hn => stab_kok rs hok hn
  rw [gcdUV_eq2]
  -- `v` made odd by a swap.
  refine rs_app (R := Two (KG (TopZ aU))) (by simp) (by simp [constA])
    (show RelCT isa _ (seqs [.block _, countLoop .x14 cswapBody]) _ from by
      show RelCT isa _ (.seq (.block _) (countLoop .x14 cswapBody)) _
      rw [gcdSwap_eq]
      exact kg_ws (by taint_decide) fun I _ s h _ hf => by
        rw [← gcdSwap_eq]
        exact WP.mono (gcdSwap_k h) fun t ⟨ht, _, _, _, tt⟩ => ⟨ht, tt.trans hf⟩) ?_
  -- The mask of `v < 2` into `kOk`.
  refine rs_app (by simp [constA]) (by simp [ltA, cmpA]) (constA_ct 2 (by decide)
    (sT [.arr aC] _ (by decide) (by decide)) (by taint_decide) (by taint_decide)) ?_
  refine rs_app (R := Two (KG fun I t => TopZ aU I t ∧ X15M I t)) (by simp [ltA, cmpA]) (by simp)
    (ltA_ct (by decide) (by decide) (fun I s t _ hf hm _ h15 => ⟨by dsimp only [TopZ, atop] at hf ⊢; rw [hm]; exact hf,
      _, h15⟩) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [constA]) (show RelCT isa _ (seqs [.block [sth .x15 kOk]]) _ from
    stOk_ct (sT [.hdr kOk] [] (by decide) (by decide))) ?_
  -- `[aV] := 3` for `v < 2`.
  refine rs_app (by simp [constA]) (by simp) (constA_ct 3 (by decide)
    (stab_and (sT [.arr aC] _ (by decide) (by decide)) (sK [.arr aC] _ (by decide) (by decide)))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [.block [ldh .x15 kOk]]) _ from
    ldOk_ct (F := TopZ aU) fun I s t hf hm _ => by dsimp only [TopZ, atop] at hf ⊢; rw [hm]; exact hf) ?_
  refine rs_app (by simp [selC]) (by simp) (selC_ct (by decide) (by decide)
    (stab_and (sT [.arr aV] _ (by decide) (by decide)) (sK [.arr aV] _ (by decide) (by decide))) (by taint_decide)) ?_
  -- `inverse` modulo `[aM] = v`.
  refine rs_app (R := Two (KG KokM)) (by simp) (by simp [constA]) ?_ ?_
  · show RelCT isa _ (seqs ([zeroA aM] ++ ([copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂] ++
      [inverse aU aV aX₁ aX₂ aM aT]))) _
    refine rs_app (by simp) (by simp) (zeroA_ct (by decide)
      (stab_and (sT [.arr aM] _ (by decide) (by decide)) (sK [.arr aM] _ (by decide) (by decide))) (by taint_decide)) ?_
    refine rs_app (by simp) (by simp) (invStart_ct (o := aM) (a := aV) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (stab_and (sT [.arr aM, .arr aX₁, .arr aX₂] _ (by decide) (by decide))
        (sK [.arr aM, .arr aX₁, .arr aX₂] _ (by decide) (by decide))) (by taint_decide)) ?_
    exact (inverse_ct (F := KokM) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sK _ _ (by decide) (by decide))
      (by taint_decide)).mono (fun _ _ h => two_kg (fun _ _ ⟨⟨tU, hk⟩, he, h1, h2⟩ => ⟨hk, tU, he.symm, h1, h2⟩) h)
      fun _ _ h => h
  -- The result 1 for `v < 2`.
  refine rs_app (by simp [constA]) (by simp) (constA_ct 1 (by decide) (sK [.arr aC] _ (by decide) (by decide))
    (by taint_decide) (by taint_decide)) ?_
  refine rs_app (by simp) (by simp [selC]) (show RelCT isa _ (seqs [.block [ldh .x15 kOk]]) _ from
    (ldOk_ct (F := NF) fun _ _ _ _ _ _ => trivial).mono (fun _ _ h => two_kg (fun _ _ h => ⟨trivial, h⟩) h)
      fun _ _ h => h) ?_
  exact (selC_ct (F := NF) (by decide) (by decide) (stab_nf _ _) (by taint_decide)).mono
    (fun _ _ h => two_kg (fun _ _ ⟨⟨_, _⟩, c⟩ => ⟨trivial, c⟩) h) fun _ _ h => h

/-! ## The lcm -/

/-- After `lcmPart`: the front's facts, and `L` in `aL`. -/
abbrev LF : KIn → State → Prop := fun I t => PF I t ∧ av I t.mem aL = I.L

/-- `lcmPart` leaks the same in runs with the same public data, and leaves
`LF` (`lcm_k`). -/
theorem lcmPart_ct [VG.Proof.Rsa.AArch64.InvLaw] : RelCT isa (Two (KG PF)) (seqs lcmPart) (Two (KG LF)) := by
  refine kg_ct ?_ fun I _ s h L hf => by
    have hPw := lt_pow_half L.P_lt 1
    have hQw := lt_pow_half L.Q_lt 1
    refine WP.mono (lcm_k h L.W hf.2.2.1 hf.2.2.2.1 hPw hQw) fun t ⟨ht, f, v⟩ => ⟨ht, ?_, v⟩
    exact PF.frame (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h.hZ hf f
  rw [lcmPart_eq]
  refine RelCT.drop (Q := Two (KG NF)) (rs_app (by simp [phi, mulTo]) (by simp) phi_ct ?_)
  refine rs_app (R := Two (KG TwB)) (by simp) (by simp [twos]) ?_ ?_
  · show RelCT isa _ (seqs ([zeroA aU, copyA aU aPm] ++ [zeroA aV, copyA aV aQm])) _
    refine rs_app (by simp) (by simp) (show RelCT isa _ (seqs [zeroA aU, copyA aU aPm]) _ from
      zc_ct (by decide) (by decide) (by decide) (stab_top _ (by decide) (by decide) (by decide))
        (by taint_decide) (by taint_decide)) ?_
    exact (show RelCT isa _ (seqs [zeroA aV, copyA aV aQm]) _ from
      zc_ct (by decide) (by decide) (by decide) (stab_and (stab_top _ (by decide) (by decide) (by decide))
        (stab_top _ (by decide) (by decide) (by decide))) (by taint_decide) (by taint_decide)).mono
      (fun _ _ h => h) fun _ _ h => two_kg (fun _ _ ⟨⟨tL, tU⟩, tV⟩ => ⟨tU, tV, tL⟩) h
  refine rs_app (by simp [twos]) (by simp [gcdUV]) twos_ct ?_
  refine rs_app (by simp [gcdUV]) (by simp) gcdUV_ct ?_
  exact divmod_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (stab_nf _ _) (by taint_decide) (by taint_decide)

end VG.Proof.RsaKeyGen.AArch64.Key
