module

public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import VerifiedGarbage.Proof.Dsa.Words
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.ZeroMask`, which the modules that import this one used -/

section

/-! # Turning a zero or equality accumulator into an acceptance mask -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Compare an accumulator with zero without branching, optionally invert
the predicate. Used for both zero tests and byte-string equality. -/
theorem zeroMask_ok (r : Reg) (invert : Bool) {s : State} :
    WP isa (.block (([.alu .cmp r (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      (if invert then [.alu .xor .rax (.imm (-1))] else []))) s fun t =>
      t.gpr .rax = mask (if invert then !decide (s.gpr r = 0) else decide (s.gpr r = 0)) ∧
      t.mem = s.mem ∧ Keep [.rax, r] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, r] (Q := fun u =>
    u.gpr .rax = mask (decide (s.gpr r = 0)) ∧ u.mem = s.mem) ?_ ?_)
    fun u ⟨⟨hua, hum⟩, hku⟩ => ?_
  · xrun [show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl]
    change mask (decide ((s.gpr r).toNat < 1)) = _
    rw [mask_lt_one]
  · cases r <;> rfl
  · refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.gpr .rax = mask (if invert then !decide (s.gpr r = 0) else decide (s.gpr r = 0)) ∧
      t.mem = u.mem) ?_ ?_) fun t ⟨⟨hta, htm⟩, hkt⟩ =>
        ⟨hta, htm.trans hum, (hku.trans hkt).mono (by simp)⟩
    · cases invert <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact WP.block_nil ⟨hua, rfl⟩
      · xrun [hua, show BitVec.signExtend 64 (-1 : BitVec 32) = BitVec.allOnes 64 from rfl, mask_complement]
    · cases invert <;> rfl

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA subgroup checks against the ordinary value one -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev oneScanHead : List Instr := [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))),
  .mov .r15 (.mem (at0 .rbx)), .alu .xor .r15 (.imm 1)]

theorem oneScanHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block oneScanHead) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w aX) ∧
      t.gpr .r15 = word s.mem B (slot w aX) ^^^ 1 ∧ t.mem = s.mem ∧
      Keep [.r12, .rbx, .r15] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (Nat.le_trans (hdr_lt_slot w 8 hi) hZ)
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  refine WP.mono (WP.keep [.r12, .rbx, .r15] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rbx = off B (slot w aX) ∧
    t.gpr .r15 = word s.mem B (slot w aX) ^^^ 1 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨h12, hbx, h15, hm⟩, hk⟩ => ⟨h12, hbx, h15, hm, hk⟩
  unfold oneScanHead
  xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aX) (by decide),
    hg.hdr.hw, hg.hdr.harr aX (by decide), hg.scr.ld (show slot w aX + 8 ≤ Z by omega_using [hx]),
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]

/-- Fixed-count comparison with one, retaining the boolean in the accumulator. -/
theorem oneScan_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (.seq (.block oneScanHead)
      (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)])) s fun t =>
      (t.gpr .r15 = 0 ↔ wv s.mem B (slot w aX) w = 1) ∧ t.mem = s.mem ∧
      Keep [.rax, .r12, .rbx, .r15, .r14] s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  refine WP.seq (WP.mono (oneScanHead_ok hg hZ) fun u ⟨hu12, hubx, hu15, hum, hku⟩ => ?_)
  have hlow : u.gpr .r15 = 0 ↔ (word u.mem B (slot w aX) ^^^ 1) = 0 := by rw [hu15, hum]
  refine WP.mono (orWords_ok (hg.scr.congr hku.2.2) hubx hu12 hlow hw hw' (by omega_using [hx]))
    fun t ⟨ht, htm, hkt⟩ => ?_
  rw [VG.Proof.Dsa.words_eq_one (by omega_using [hw]), hum] at ht
  exact ⟨ht, htm.trans hum, (hku.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
