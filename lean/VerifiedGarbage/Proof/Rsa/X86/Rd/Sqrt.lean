module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Count
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFlags
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The integer square root of Appendix C.2 on i686

`RecoverDetRt.sqrt`: `32 W / 2` steps of `RecoverDet.sqrtStep`, the
radicand wide in `wR` and shifted up two bits at a time, the remainder and
the root narrow in `aRm` and `aY`; then whether the remainder is zero.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet (sqrtStep)
open VG.Proof.Rsa (b2n b2n_le sub32)

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- A chain's carry into a header word. -/
theorem KS.carryTo_ok {sl : Nat} {c : Bool} (h : KS g s0 A live AW liveW V ls s)
    (hc : s.gpr .ecx = cmask c) (hsl : SlotOk sl) :
    WP isa (.block (carryTo sl)) s fun t => KS g s0 A live AW liveW (upd V sl (b2n c)) (sl :: ls) t := by
  unfold carryTo
  refine wp_movS rfl fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inl rfl) rfl fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = b2n c := by
    rw [D.gpr, ite_eq_left rfl, U.gpr]
    change (s.gpr .ecx &&& 1#32).toNat = _
    rw [hc]
    cases c <;> decide
  refine WP.mono (hv.storeSlot hsl .eax) fun t ⟨ht, _, _⟩ => ?_
  rw [value] at ht
  exact ht

end

/-- The carry out of doubling `x < M`. -/
theorem carry_double {x M : Nat} (hx : x < M) : b2n (decide (M ≤ x + x)) = 2 * x / M := by
  unfold b2n
  by_cases c : M ≤ x + x
  · simp only [c, decide_true, ↓reduceIte]
    exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
  · simp only [c, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (Nat.div_eq_of_lt (by omega)).symm

/-- A doubled number modulo an even `M`, plus one, is below `M`. -/
theorem double_mod_lt {k w : Nat} (hw : 1 ≤ w) (b : Nat) (hb : b ≤ 1) :
    2 * k % 2 ^ (32 * w) + b < 2 ^ (32 * w) := by
  have hM : 2 ^ (32 * w) = 2 * 2 ^ (32 * w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  rw [hM, Nat.mul_mod_mul_left]
  have := Nat.mod_lt k (Nat.two_pow_pos (32 * w - 1))
  omega

theorem double_mod_even {k w : Nat} (hw : 1 ≤ w) : (k + k) % 2 ^ (32 * w) % 2 = 0 := by
  have hM : 2 ^ (32 * w) = 2 * 2 ^ (32 * w - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  rw [← Nat.two_mul, hM, Nat.mul_mod_mul_left]
  omega

/-- One step's values, as the code computes them. -/
theorem sqrt_step_eq {w wb xs rm y : Nat} (hx : xs < 2 ^ wb) (hw : 1 ≤ w) :
    sqrtStep (32 * w) wb (xs, rm, y) =
      ((((xs + xs) % 2 ^ wb) + ((xs + xs) % 2 ^ wb)) % 2 ^ wb,
        if b2n (decide ((((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs))) +
              ((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs)))) % 2 ^ (32 * w) +
              b2n (decide (2 ^ wb ≤ (xs + xs) % 2 ^ wb + (xs + xs) % 2 ^ wb)) <
            2 * (((y + y) % 2 ^ (32 * w) + (y + y) % 2 ^ (32 * w)) % 2 ^ (32 * w) / 2) + 1)) = 0 then
          sub32 w ((((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs))) +
              ((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs)))) % 2 ^ (32 * w) +
              b2n (decide (2 ^ wb ≤ (xs + xs) % 2 ^ wb + (xs + xs) % 2 ^ wb)))
            (2 * (((y + y) % 2 ^ (32 * w) + (y + y) % 2 ^ (32 * w)) % 2 ^ (32 * w) / 2) + 1)
        else (((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs))) +
              ((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs)))) % 2 ^ (32 * w) +
              b2n (decide (2 ^ wb ≤ (xs + xs) % 2 ^ wb + (xs + xs) % 2 ^ wb)),
        (y + y) % 2 ^ (32 * w) + b2n (!decide ((((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs))) +
              ((rm + rm) % 2 ^ (32 * w) + b2n (decide (2 ^ wb ≤ xs + xs)))) % 2 ^ (32 * w) +
              b2n (decide (2 ^ wb ≤ (xs + xs) % 2 ^ wb + (xs + xs) % 2 ^ wb)) <
            2 * (((y + y) % 2 ^ (32 * w) + (y + y) % 2 ^ (32 * w)) % 2 ^ (32 * w) / 2) + 1))) := by
  have x1 : (xs + xs) % 2 ^ wb < 2 ^ wb := Nat.mod_lt _ (Nat.two_pow_pos _)
  have ev := double_mod_even (k := (y + y) % 2 ^ (32 * w)) hw
  rw [show 2 * (((y + y) % 2 ^ (32 * w) + (y + y) % 2 ^ (32 * w)) % 2 ^ (32 * w) / 2) + 1 =
    ((y + y) % 2 ^ (32 * w) + (y + y) % 2 ^ (32 * w)) % 2 ^ (32 * w) + 1 by omega]
  rw [carry_double hx, carry_double x1]
  unfold sqrtStep
  simp only [← Nat.two_mul]
  have lo : 2 * (2 * xs % 2 ^ wb) / 2 ^ wb ≤ 1 := by
    have := carry_double x1
    simp only [← Nat.two_mul] at this
    rw [← this]; exact b2n_le _
  have rlt := double_mod_lt (k := 2 * rm % 2 ^ (32 * w) + 2 * xs / 2 ^ wb) hw _ lo
  generalize 2 * (2 * rm % 2 ^ (32 * w) + 2 * xs / 2 ^ wb) % 2 ^ (32 * w) + 2 * (2 * xs % 2 ^ wb) / 2 ^ wb = r at *
  generalize 2 * (2 * y % 2 ^ (32 * w)) % 2 ^ (32 * w) + 1 = t
  by_cases c : r < t
  · simp [c, b2n]
  · have : sub32 w r t = r - t := by
      unfold sub32
      rw [show r + 2 ^ (32 * w) - t = (r - t) + 2 ^ (32 * w) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    simp [c, b2n, this]

abbrev sqLive : List Nat := [aRm, aY, aD, aZero]
abbrev sqSlots : List Nat := [sK, sOkDE, sLt, sExact, sOk4]

/-- The square root after `i` steps: `(xs, rm, y)`. -/
def SqS (g : Geo) (s0 : State) (A : Nat → Nat) (AW : Nat → Nat) (V : Nat → Nat) (K i : Nat)
    (st : Nat × Nat × Nat) (u : State) : Prop :=
  KS g s0 (upd (upd A aRm st.2.1) aY st.2.2) sqLive (upd AW wR st.1) [wR] (upd V sK (K - i)) sqSlots u

theorem sqrtBody_ok {g : Geo} {s0 u : State} {A AW V : Nat → Nat} {K i : Nat} {st : Nat × Nat × Nat}
    (hi : i < K) (hK : K < 2 ^ 32) (hx : st.1 < 2 ^ (32 * g.W)) (h : SqS g s0 A AW V K i st u) :
    WP isa sqrtBody u fun v =>
      SqS g s0 A AW V K (i + 1) (sqrtStep (32 * g.w) (32 * g.W) st) v ∧
      v.zf = some (decide (K - i - 1 = 0)) := by
  obtain ⟨XS, Rm, Y⟩ := st
  unfold SqS at h
  simp only at h hx
  have wpos : 1 ≤ g.w := by change 1 ≤ 2 * g.n + 2; omega
  rw [sqrt_step_eq hx wpos]
  unfold sqrtBody
  simp only [seqs]
  -- The radicand's top bit into the remainder.
  refine WP.seq (WP.mono (h.add_W (o := wR) (a := wR) (b := wR) (by decide) (by simp) (by simp) (by decide))
    fun u1 ⟨h1, c1⟩ => ?_)
  refine WP.seq (WP.mono (h1.carryTo_ok c1 (sl := sHi) (by decide)) fun u2 h2 => ?_)
  refine WP.seq (WP.mono (h2.add_w (o := aRm) (a := aRm) (b := aRm) (by decide) (by simp) (by simp) (by decide))
    fun u3 ⟨h3, _⟩ => ?_)
  refine WP.seq (WP.mono (h3.addLow_w (j := aRm) (sl := sHi) (by simp) (by simp)
    (by simp only [upd_self]; exact double_mod_even wpos) (by simp only [upd_self]; exact b2n_le _) (by decide))
    fun u4 h4 => ?_)
  -- The next bit.
  refine WP.seq (WP.mono (h4.add_W (o := wR) (a := wR) (b := wR) (by decide) (by simp) (by simp) (by decide))
    fun u5 ⟨h5, c5⟩ => ?_)
  refine WP.seq (WP.mono (h5.carryTo_ok c5 (sl := sLo) (by decide)) fun u6 h6 => ?_)
  refine WP.seq (WP.mono (h6.add_w (o := aRm) (a := aRm) (b := aRm) (by decide) (by simp) (by simp) (by decide))
    fun u7 ⟨h7, _⟩ => ?_)
  refine WP.seq (WP.mono (h7.addLow_w (j := aRm) (sl := sLo) (by simp) (by simp)
    (by simp only [upd_self]; exact double_mod_even wpos) (by simp only [upd_self]; exact b2n_le _) (by decide))
    fun u8 h8 => ?_)
  -- `4 y + 1`.
  refine WP.seq (WP.mono (h8.add_w (o := aTy) (a := aY) (b := aY) (by decide) (by simp) (by simp) (by decide))
    fun u9 ⟨h9, _⟩ => ?_)
  refine WP.seq (WP.mono (h9.add_w (o := aTy) (a := aTy) (b := aTy) (by decide) (by simp) (by simp) (by decide))
    fun u10 ⟨h10, _⟩ => ?_)
  refine WP.seq (WP.mono (h10.orOne_w (j := aTy) (by simp) (by decide)) fun u11 h11 => ?_)
  -- The comparison.
  refine WP.seq (WP.mono (h11.subWrap (o := aDf) (a := aRm) (b := aTy) (by decide) (by simp) (by simp)
    (by decide) (by decide) (by decide)) fun u12 ⟨h12, b12⟩ => ?_)
  refine WP.seq (WP.mono (h12.storeSlot (d := sBb) (by decide) .ebx) fun u13 ⟨h13, _, _⟩ => ?_)
  rw [b12] at h13
  refine WP.seq (WP.mono (h13.flagNot_ok (d := sNb) (a := sBb) (by decide) (by simp) (by rw [upd_self])) fun u14 h14 => ?_)
  refine WP.seq (WP.mono (h14.sel_w (o := aRm) (a := aDf) (b := aRm) (sl := sBb) (by decide) (by simp) (by simp)
    (by simp) (by simp [upd, sNb, sBb]; exact b2n_le _) (.inl (by decide)) (by decide)) fun u15 ⟨h15, _⟩ => ?_)
  refine WP.seq (WP.mono (h15.add_w (o := aY) (a := aY) (b := aY) (by decide) (by simp) (by simp) (by decide))
    fun u16 ⟨h16, _⟩ => ?_)
  refine WP.seq (WP.mono (h16.addLow_w (j := aY) (sl := sNb) (by simp) (by simp)
    (by simp only [upd_self]; exact double_mod_even wpos) (by simp [upd]; exact b2n_le _) (by decide))
    fun u17 h17 => ?_)
  have cnt : ∀ c, upd (upd (upd (upd (upd V sK (K - i)) sHi c) sLo c) sBb c) sNb c sK = K - i := fun c => by
    simp [upd, sK, sHi, sLo, sBb, sNb]
  refine WP.mono (h17.countNext_ok (by simp) (by simp [upd, sK, sHi, sLo, sBb, sNb]; omega)
    (by simp [upd, sK, sHi, sLo, sBb, sNb]; omega))
    fun v ⟨hv, zv⟩ => ⟨?_, by rw [zv]; simp [upd, sK, sHi, sLo, sBb, sNb]⟩
  unfold SqS
  refine hv.mono (fun j hj => ⟨by simp at hj ⊢; omega, ?_⟩) (fun j hj => ⟨by simp at hj ⊢; omega, ?_⟩)
    (fun d hd => ⟨by simp at hd ⊢; omega, ?_⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> simp [upd, aRm, aY, aD, aZero, aTy, aDf, sBb, sNb, sHi, sLo]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj; simp [upd]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [upd, sBb, sNb, sHi, sLo, sK, sOkDE, sLt, sExact, sOk4]
    omega

theorem sqrtIter_lt {nb wb X : Nat} (hX : X < 2 ^ wb) :
    ∀ i, ((sqrtStep nb wb)^[i] (X, 0, 0)).1 < 2 ^ wb
  | 0 => hX
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    generalize (sqrtStep nb wb)^[i] (X, 0, 0) = st
    unfold sqrtStep
    dsimp only
    split <;> exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The square root of the wide `[wR]`, `X`: the root in `aY`, and whether the remainder is
zero in `sOk5`. -/
theorem sqrt_ok {g : Geo} {s0 u : State} {A AW V : Nat → Nat} {X : Nat}
    (h : KS g s0 A [aD, aZero] AW [wR] V sqSlots u) (z : A aZero = 0) (hX : AW wR = X) :
    WP isa sqrt u fun v => ∃ A' AW',
      KS g s0 A' [aY, aD, aZero] AW' [] (upd (upd V sK 0) sOk5
        (if ((sqrtStep (32 * g.w) (32 * g.W))^[16 * g.W] (X, 0, 0)).2.1 = 0 then 1 else 0))
        (sOk5 :: sqSlots) v ∧
      A' aY = ((sqrtStep (32 * g.w) (32 * g.W))^[16 * g.W] (X, 0, 0)).2.2 ∧ A' aD = A aD ∧ A' aZero = 0 := by
  have up := h.upper
  have Xlt : X < 2 ^ (32 * g.W) := by rw [← hX, ← h.arrsW wR (by simp)]; exact val32_lt _ _ _ _
  have z' : A 10 = 0 := z
  unfold sqrt
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := aRm) (a := aZero) (by decide) (by simp) (by decide) (by decide))
    fun u1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (WP.mono (h1.copy_w (o := aY) (a := aZero) (by decide) (by simp) (by decide) (by decide))
    fun u2 ⟨h2, _, _⟩ => ?_)
  refine WP.seq (WP.mono h2.countW_ok fun u3 h3 => ?_)
  have h3' : SqS g s0 A AW V (16 * g.W) 0 (X, 0, 0) u3 := by
    unfold SqS
    refine h3.mono (fun j hj => ⟨by simp at hj ⊢; omega, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨?_, ?_⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> simp [upd, z', aRm, aY, aD, aZero]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; subst hj; simp [upd, hX]
    · simp at hd ⊢; omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl <;> simp [upd]
  refine WP.seq (WP.mono (countLoop (P := fun i v => SqS g s0 A AW V (16 * g.W) i
      ((sqrtStep (32 * g.w) (32 * g.W))^[i] (X, 0, 0)) v) (by change 0 < 16 * (2 * (2 * g.n + 2) + 2); omega) h3'
    fun i v hi hv => WP.mono (sqrtBody_ok hi (by change 16 * (2 * (2 * g.n + 2) + 2) < _; omega)
      (sqrtIter_lt Xlt i) hv) fun w ⟨hw, zw⟩ => ⟨by rw [Function.iterate_succ_apply']; exact hw, zw⟩)
    fun u4 h4 => ?_)
  unfold SqS at h4
  refine WP.mono (h4.eqS_w (d := sOk5) (a := aRm) (b := aZero) (by simp) (by simp) (by decide) (by decide)
    (by decide) (by decide)) fun v ⟨hv, _⟩ => ?_
  refine ⟨_, AW, hv.mono (fun j hj => ⟨by simp at hj ⊢; omega, rfl⟩) (fun j hj => by simp at hj)
    (fun d hd => ⟨by simp at hd ⊢; omega, ?_⟩), by simp [upd, aY], by simp [upd, aD, aY, aRm],
    by simp [upd, aZero, aY, aRm, z']⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [upd, z', aRm, aZero, aY, sOk5, sK, sOkDE, sLt, sExact, sOk4]

end VG.Proof.Rsa.X86.Recover
