module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
public import VerifiedGarbage.Proof.Bignum.X86_64.OpAt
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledRaw
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFinish8
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Redc
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRaw
public import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcChoice
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
public import VerifiedGarbage.Impl.Bignum.X86_64.Adx
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.Math

/-! ### `Bignum.X86_64.AdxSquareMont`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86_64.AdxSquareFinish`, which this module and modules that import it used -/

section

/-! The final conditional subtraction, shared with the ADX multiplier. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Reduce the result below `2 m` by the existing constant-time subtraction
and selection, for the slot `sArr co` holding the base of `o`. -/
theorem finishV_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (h10 : s.gpr .r10 = off B (slot w aN))
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co o : Nat} (po : (co, o) ∈ ps)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hTlt : wv s.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w) :
    WP isa (Adx.finish co) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w aTmp) (w + 2) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => Nat.le_trans (slot_le hj) hZ
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega_using []
  have hTs := sl aTmp (by decide)
  have sNX : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_using []
  have soX : slot w o + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := by
    have := slot_sep (w := w) ho1; have := slot_sep (w := w) ho2; unfold slot aAcc aTmp at *; omega_arith
  unfold Adx.finish
  refine WP.seq (WP.mono (finishBasesV_ok hs hdi hH hZ (hv.at po) (hv.lt po)) fun s₁ ⟨h12, h8, hsi, hbx, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (subMod_ok (hs.congr k₁.2.2) h8 ((k₁.gpr (by decide)).trans h10) hsi h12 (by omega_using [hw1]) hw
    (by omega_using [hTs]) (by have := sl aN (by decide); omega_using [hAT, hTs, sNX]) (by omega_using [hAT, hTs]) (by omega_using [hAT]) (by omega_using [sNX]))
    fun s₂ ⟨c, lt, hbp, hlt, hD, ho₂, k₂⟩ => ?_)
  rw [hm₁] at hlt hD ho₂
  have k12 := k₁.trans k₂
  refine WP.mono (selectAcc_ok (hs.congr k12.2.2) ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans hsi)
    ((k₂.gpr (by decide)).trans hbx) ((k₂.gpr (by decide)).trans h12) hbp (by omega_using [hw1]) hw (by omega_using [hTs]) (by omega_using [hAT, hTs])
    (by have := sl o ho; omega_using [this]) (by omega_using [hAT, soX]) (by omega_using [hAT, soX])) fun t ⟨hv, hot, kt⟩ => ?_
  have hT₂ : wv s₂.mem B (slot w aTmp) w = wv s.mem B (slot w aTmp) w := ho₂.wv (by omega_using [hAT]) (by omega_using [hn, hTs])
  refine ⟨?_, ?_, (k12.trans kt).mono (by decide)⟩
  · rw [hv, hT₂, hlt, wv_top2]
    have h := VG.Proof.Bignum.csub_result (Tl := wv s.mem B (slot w aTmp) w)
      (Tw := (word s.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₂.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w aN) w; omega_using [this]) (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _)
      (by rw [← wv_top2]; exact hTlt) hD
    rw [← h]
    by_cases h : (word s.mem B (slot w aTmp + 8 * w)).toNat < c.toNat <;> simp [h]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx o (by simp)
    exact (hot x (by omega_using [h2])).trans (ho₂ x (by omega_using [h1]))

/-- Reduce the result below `2 m` by the existing constant-time subtraction
and selection. -/
theorem finish_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (h10 : s.gpr .r10 = off B (slot w aN))
    {o : Nat} (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hTlt : wv s.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w) :
    WP isa (Adx.finish o) s fun t =>
      wv t.mem B (slot w o) w = wv s.mem B (slot w aTmp) (w + 2) % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, o] s.mem t.mem ∧ Keep mmRegs s t :=
  finishV_ok hs hdi hH hZ hw1 hw h10 (hH.ops (ps := [(o, o)]) (by simp; omega_using [ho])) (List.mem_singleton_self _)
    ho ho1 ho2 hTlt

end VG.Proof.Bignum.X86_64.AdxSquare

end

end

/-! Correctness of Montgomery squaring with BMI2 and ADX. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- Montgomery reduction of `X < m R` produces a value below `2 m`. -/
theorem redc_lt {R T X q m : Nat} (hm : 0 < m) (hq : q < R)
    (hX : X < m * R) (he : R * T = X + q * m) : T < 2 * m := by
  have hqm : q * m < R * m := Nat.mul_lt_mul_of_pos_right hq hm
  have hb : R * T < R * (2 * m) := by
    rw [he]
    have h1 : m * R = R * m := Nat.mul_comm _ _
    have h2 : R * (2 * m) = R * m + R * m := by grind
    omega_using [hX, hqm, h1, h2]
  exact Nat.lt_of_mul_lt_mul_left hb

/-- Squaring has the same reduced-result, congruence and memory contract as
Montgomery multiplication with equal operands. -/
theorem montSquareWith_ok {diag red : Prog isa} {P : Nat → Prop} (hd : DiagOk diag P) (hr : RedOk red P)
    {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (hP : P w)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxSquare.montSquareWith diag red o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hg : hdrBytes ≤ slot w aAcc + 16 := by unfold slot; omega_using []
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_using []
  have hmpos : 0 < wv s.mem B (slot w aN) w := by omega_using [hA]
  unfold AdxSquare.montSquareWith
  refine WP.seq (WP.mono (rawSquareWith_ok hd hs hdi hH hZ hw1 hw hP ha ha1 ha2) fun s₁ ⟨_, hv₁, ho₁, k₁⟩ => ?_)
  have hH₁ := hH.of_outside ho₁ hg
  have hn₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  refine WP.seq (WP.mono (hr.ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hH₁ hZ hw1 hw
    (by rw [hn₁]; exact hinv) hP) fun s₂ ⟨⟨q, hq, heq⟩, ho₂, k₂⟩ => ?_)
  have hN₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  rw [hv₁, hN₁] at heq
  have ho12 := (ho₁.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega_using []) (by omega_using [])).trans ho₂
  have hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho12.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho12 (by unfold slot; omega_using [])
  have hTlt : wv s₂.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w :=
    redc_lt hmpos hq (Nat.mul_lt_mul'' hA (wv_lt _ _ _ _)) heq
  have hsrc : readSrc s₂ (.mem (hdr (sArr aN))) = some (off B (slot w aN)) := by
    rw [readSrc_word (d := 8 * sArr aN) hs₂ (by simp only [State.ea, hdr, (k12.gpr (by decide)).trans hdi, hdrOff])
      (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_using [hZ, this]), hH₂.harr aN (by decide)]
  refine WP.seq (WP.mono (movMem_ok s₂ (dst := .r10) hsrc) fun s₃ ⟨h10, _, _, k₃⟩ => ?_)
  have k123 := k12.trans k₃.keep
  refine WP.mono (finish_ok (hs.congr k123.2.2) ((k123.gpr (by decide)).trans hdi)
    (k₃.2.1 ▸ hH₂) hZ hw1 hw h10 ho ho1 ho2 (by rw [k₃.2.1, hN₂]; exact hTlt))
    fun t ⟨hv, hf, kt⟩ => ?_
  rw [k₃.2.1, hN₂] at hv
  refine ⟨?_, ?_, ?_, (k123.trans kt).mono (by decide)⟩
  · rw [hv]; exact Nat.mod_lt _ hmpos
  · rw [hv, Nat.mod_mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    have hfin : t.mem x = s₃.mem x := hf x (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h1
      · exact h3)
    rw [hfin, k₃.2.1]
    exact ho12 x (by
      have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega_using []
      omega_using [h1, h2, hAT])


/-- `montSquare4`: `montSquare` for `w` a multiple of 4. -/
theorem montSquare4_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hw1 : 2 ≤ w) (hw : w < 2 ^ 31)
    {o a : Nat} (ho : o < 8) (ha : a < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hA : wv s.mem B (slot w a) w < wv s.mem B (slot w aN) w) (h4 : w % 4 = 0) :
    WP isa (AdxSquare.montSquare4 o a) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w a) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t :=
  montSquareWith_ok diagonal4_diag (redc_red _) hs hdi hH hZ hw1 hw h4 ho ha ho1 ho2 ha1 ha2 hinv hA

end VG.Proof.Bignum.X86_64.AdxSquare

end

end

/-! Correctness of Montgomery squaring with BMI2 and ADX. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-- A product of a word-width number and one below `m`, below `m R`. -/
theorem mul_lt_mont {a b m R : Nat} (ha : a < R) (hb : b < m) : a * b < m * R := by
  have h := Nat.mul_lt_mul'' ha hb
  rw [Nat.mul_comm R] at h
  exact h

/-- The reduction and the final subtraction after a raw product `X` in the
accumulator: what the multiplication and the squaring both end with. -/
theorem redcFinish_ok {s s₁ : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co o : Nat} (po : (co, o) ∈ ps)
    (ho : o < 8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {X : Nat} (hX : X < wv s.mem B (slot w aN) w * 2 ^ (64 * w))
    (hv₁ : wv s₁.mem B (slot w aAcc + 16) (2 * w) = X)
    (ho₁ : Outside B (slot w aAcc) (16*w+32) s.mem s₁.mem) (k₁ : Keep mmRegs s s₁) :
    WP isa (AdxTiledProduct.redcFinish co) s₁ fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w = X % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hw1 : 2 ≤ w := by omega_using [hwN, hnN]
  have hg : hdrBytes ≤ slot w aAcc := by unfold slot; omega_using []
  have hsep : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega_using []
  have hmpos : 0 < wv s.mem B (slot w aN) w :=
    Nat.pos_of_ne_zero fun h => by rw [h, Nat.zero_mul] at hX; omega_using [hdi, hZ, hwN, hnN, hw, ho, ho1, ho2, hinv, hX, hv₁, hn, hNs, hw1, hg, hsep, h]
  have hH₁ := hH.of_outside ho₁ hg
  have hn₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := ho₁.word (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  unfold AdxTiledProduct.redcFinish
  refine WP.seq (WP.mono (AdxRotate8.redc_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) hH₁ hZ hwN hnN)
    fun s₂ ⟨vred,ho₂,k₂⟩ => ?_)
  obtain ⟨q,hq,heq⟩ := vred (by rw [hn₁]; exact hinv)
  have hN₁ : wv s₁.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho₁.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  rw [hv₁, hN₁] at heq
  have ho12 := (ho₁.mono (o' := slot w aAcc) (n' := 16 * w + 32) (by omega_using []) (by omega_using [])).trans ho₂
  have hN₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := ho12.wv (by omega_using [hsep]) (by omega_using [hZ, hn, hNs])
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hH₂ := hH.of_outside ho12 (by unfold slot; omega_using [])
  have hTlt : wv s₂.mem B (slot w aTmp) (w + 2) < 2 * wv s.mem B (slot w aN) w :=
    AdxSquare.redc_lt hmpos hq hX heq
  have hsrc : readSrc s₂ (.mem (hdr (sArr aN))) = some (off B (slot w aN)) := by
    rw [readSrc_word (d := 8 * sArr aN) hs₂ (by simp only [State.ea, hdr, (k12.gpr (by decide)).trans hdi, hdrOff])
      (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_using [hZ, this]), hH₂.harr aN (by decide)]
  refine WP.seq (WP.mono (movMem_ok s₂ (dst := .r10) hsrc) fun s₃ ⟨h10, _, _, k₃⟩ => ?_)
  have k123 := k12.trans k₃.keep
  have hv₂ : Ops s₂.mem B w ps := hv.of_outside ho12 (by unfold slot sFn hdrBytes; omega_using [])
  refine WP.mono (finish8V_ok (hs.congr k123.2.2) ((k123.gpr (by decide)).trans hdi)
    (k₃.2.1 ▸ hH₂) hZ hwN hnN hw h10 (k₃.2.1 ▸ hv₂) po ho ho1 ho2 (by rw [k₃.2.1, hN₂]; exact hTlt))
    fun t ⟨hv, hf, kt⟩ => ?_
  rw [k₃.2.1, hN₂] at hv
  refine ⟨?_, ?_, ?_, (k123.trans kt).mono (by decide)⟩
  · rw [hv]; exact Nat.mod_lt _ hmpos
  · rw [hv, Nat.mod_mul_mod, Nat.mul_comm, heq, Nat.add_mul_mod_self_right]
  · intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    have hfin : t.mem x = s₃.mem x := hf x (by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact h1
      · exact h3)
    rw [hfin, k₃.2.1]
    exact ho12 x (by
      have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega_using []
      omega_using [h1, h2, hAT])

/-- Tiled multiplication preserves the general Montgomery contract: the right
operand is reduced; the left operand may be any word-width value. -/
theorem montMul_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (hwN : w=8*n) (hnN : 0<n) (hw : w < 2 ^ 31)
    {ps : List (Nat × Nat)} (hv : Ops s.mem B w ps) {co ca cb o a b : Nat} (po : (co, o) ∈ ps)
    (pa : (ca, a) ∈ ps) (pb : (cb, b) ∈ ps)
    (ho : o < 8) (ha : a < 8) (hb : b<8) (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b≠aAcc) (hb2 : b≠aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (AdxTiledProduct.montMul co ca cb) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  unfold AdxTiledProduct.montMul
  refine WP.seq (WP.mono (rawProduct_ok hs hdi hH hv pa pb hZ hw hwN hnN ha hb ha1 ha2 hb1 hb2)
    fun s₁ ⟨_, hv₁, ho₁, k₁⟩ => ?_)
  exact redcFinish_ok hs hdi hH hZ hwN hnN hw hv po ho ho1 ho2 hinv (mul_lt_mont (wv_lt _ _ _ _) hB) hv₁ ho₁ k₁

end VG.Proof.Bignum.X86_64.AdxTiledProduct
