module

public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual

/-! ### `Dsa.X86_64.RangeHead`, which this module and modules that import it used -/

section

/-! # Public loop bounds and addresses for DSA range checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem rangeHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
      .mov .r10 (.mem (hdr (sArr aN))), .mov32 .rbp (.imm 0)]) s fun u =>
      u.gpr .r12 = BitVec.ofNat 64 w ∧ u.gpr .rbx = off B (slot w aX) ∧
      u.gpr .r10 = off B (slot w aN) ∧ u.gpr .rbp = mask false ∧ u.mem = s.mem ∧
      Keep [.r12, .rbx, .r10, .rbp] s u := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (Nat.le_trans (hdr_lt_slot w 8 hi) hZ)
  refine WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun u =>
    u.gpr .r12 = BitVec.ofNat 64 w ∧ u.gpr .rbx = off B (slot w aX) ∧
    u.gpr .r10 = off B (slot w aN) ∧ u.gpr .rbp = mask false ∧ u.mem = s.mem) ?_ rfl)
    fun u ⟨⟨hw, hx, hn, hb, hm⟩, hk⟩ => ⟨hw, hx, hn, hb, hm, hk⟩
  xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aX) (by decide),
    hl (sArr aN) (by decide), hg.hdr.hw, hg.hdr.harr aX (by decide), hg.hdr.harr aN (by decide)]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.RangeLow`, which only this module used -/

section

/-! # The low boundary of DSA scalar and group-element ranges -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def rangeLow (aboveOne : Bool) (x : BitVec 64) : BitVec 64 := if aboveOne then x >>> 1 else x

theorem rangeLow_zero (aboveOne : Bool) (x : BitVec 64) :
    rangeLow aboveOne x = 0 ↔ x.toNat ≤ (if aboveOne then 1 else 0) := by
  cases aboveOne
  · simp only [rangeLow, Bool.false_eq_true, ite_false, Nat.le_zero]
    exact ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  · simp only [rangeLow, ite_true]
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight]
    change x.toNat / 2 = 0 ↔ x.toNat ≤ 1
    omega_using []

/-- OR-ing all high limbs and testing the adjusted low limb characterizes
exactly the rejected lower interval: zero, or zero and one. -/
theorem rangeLow_words {mem : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) (aboveOne : Bool) :
    (rangeLow aboveOne (word mem B d) = 0 ∧
      ∀ i, 1 ≤ i → i < w → word mem B (d + 8 * i) = 0) ↔
      wv mem B d w ≤ (if aboveOne then 1 else 0) := by
  cases aboveOne
  · rw [rangeLow_zero]
    simp only [Bool.false_eq_true, ite_false, Nat.le_zero]
    rw [wv_eq_zero_iff]
    constructor
    · rintro ⟨h0, h⟩ i hi
      by_cases hz : i = 0
      · subst i
        simpa only [Nat.mul_zero, Nat.add_zero] using BitVec.eq_of_toNat_eq h0
      · exact h i (by omega_using [hz]) hi
    · intro h
      exact ⟨congrArg BitVec.toNat (by simpa using h 0 (by omega_using [hw])), fun i _ hi => h i hi⟩
  · simp only [ite_true]
    rw [VG.Proof.RsaKeyGen.wv_le_one hw, VG.Proof.RsaKeyGen.and_m2_eq_zero, rangeLow_zero]
    rfl

/-- Load the low limb and optionally ignore its least significant bit. -/
theorem rangeLow_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hbx : s.gpr .rbx = off B e) (he : e + 8 ≤ Z) (aboveOne : Bool) :
    WP isa (.block (([.mov .r15 (.mem (at0 .rbx))] : List Instr) ++
      (if aboveOne then [.shift .shr .r15 1] else []))) s fun t =>
      t.gpr .r15 = rangeLow aboveOne (word s.mem B e) ∧
      t.mem = s.mem ∧ Keep [.r15] s t := by
  refine WP.mono (WP.keep [.r15] (Q := fun t =>
    t.gpr .r15 = rangeLow aboveOne (word s.mem B e) ∧ t.mem = s.mem) ?_ ?_)
    fun t ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  · cases aboveOne <;> simp only [Bool.false_eq_true, ite_false, ite_true, List.append_nil, List.cons_append, List.nil_append, rangeLow]
    all_goals xrun [State.ea, at0, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hs.ld he]
  · cases aboveOne <;> rfl

end VG.Proof.Dsa.X86_64

end

end

/-! # Exact scalar range masks without secret-dependent branches -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The range mask is all ones exactly for 0 < X < N, or 1 < X < N.
The value and modulus can have leading zero limbs. -/
theorem rangeMask_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (aboveOne : Bool) :
    WP isa (Checks.rangeMask aboveOne) s fun t =>
      t.gpr .rax = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
        wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep [.rax, .r12, .rbx, .r10, .rbp, .r14, .r15] s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  unfold Checks.rangeMask seqs
  refine WP.seq (WP.mono (rangeHead_ok hg hZ)
    fun u ⟨hu12, hubx, hu10, hubp, hum, hku⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hg.scr.congr hku.2.2) hubx hu10 hu12 hubp (by omega_using [hw])
    hw' (by omega_using [hx]) (by omega_using [hn])) fun v ⟨hvbp, hvm, hkv⟩ => ?_)
  have hkuv := hku.trans hkv
  have hvbx := (hkv.gpr (show Reg.rbx ∉ [Reg.rax, Reg.rbp, Reg.r14] by decide)).trans hubx
  have hv12 := (hkv.gpr (show Reg.r12 ∉ [Reg.rax, Reg.rbp, Reg.r14] by decide)).trans hu12
  rw [hum] at hvbp
  refine WP.seq (WP.mono (rangeLow_ok (hg.scr.congr hkuv.2.2) hvbx (by omega_using [hx]) aboveOne)
    fun z ⟨hz15, hzm, hkz⟩ => ?_)
  have hzbx := (hkz.gpr (show Reg.rbx ∉ [Reg.r15] by decide)).trans hvbx
  have hz12 := (hkz.gpr (show Reg.r12 ∉ [Reg.r15] by decide)).trans hv12
  have hlow : z.gpr .r15 = 0 ↔ rangeLow aboveOne (word z.mem B (slot w aX)) = 0 := by rw [hz15, hzm]
  refine WP.seq (WP.mono (orWords_ok (hg.scr.congr (hkuv.trans hkz).2.2) hzbx hz12 hlow hw hw'
    (by omega_using [hx])) fun f ⟨hf15, hfm, hkf⟩ => ?_)
  rw [rangeLow_words (by omega_using [hw]) aboveOne, hzm, hvm, hum] at hf15
  have hfbp := (hkf.gpr (show Reg.rbp ∉ [Reg.rax, Reg.r15, Reg.r14] by decide)).trans
    ((hkz.gpr (show Reg.rbp ∉ [Reg.r15] by decide)).trans hvbp)
  refine WP.mono (WP.keep [.rax, .r15] (Q := fun t =>
    t.gpr .rax = mask (decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
      wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) ∧ t.mem = f.mem) ?_ rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hfm.trans (hzm.trans (hvm.trans hum))),
        ((((hku.trans hkv).trans hkz).trans hkf).trans hkt).mono (by decide)⟩
  have he : (!decide (f.gpr .r15 = 0) &&
      decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) =
      decide ((if aboveOne then 1 else 0) < wv s.mem B (slot w aX) w ∧
        wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w) := by
    rw [decide_eq_decide.mpr hf15, ← decide_not, ← Bool.decide_and]
    exact decide_eq_decide.mpr (by omega_using [])
  xrun [show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl, mask_sbb, mask_lt_one,
    show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl,
    mask_complement, hfbp, mask_intersect, he]
  change (mask (decide ((f.gpr .r15).toNat < 1)) ^^^ BitVec.allOnes 64) &&&
    mask (decide (wv s.mem B (slot w aX) w < wv s.mem B (slot w aN) w)) = _
  rw [mask_lt_one, mask_complement, mask_intersect, he]

end VG.Proof.Dsa.X86_64
