module

import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import Batteries.Logic
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCalls
import VerifiedGarbage.Proof.Dsa.Layout
public import VerifiedGarbage.Proof.Dsa.X86_64.Call
public import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Dsa.Words
import VerifiedGarbage.Proof.Dsa.X86_64.OrWords
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.ZeroHead`, which this module and modules that import it used -/

section

/-! # Resolving the operand of a DSA zero check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem zeroHead_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (a : Operand) (ha : pointerFits a.pointer) :
    WP isa (.block (Core.pointer a.pointer ++ ([.mov .rsi (.reg .rax),
      .mov .rcx (.mem (Core.field a.length)), .mov32 .r8 (.imm 0)] : List Instr))) s fun t =>
      t.gpr .rsi = pointerValue s.mem B a.pointer ∧ t.gpr .rcx = word s.mem B a.length.offset ∧
      t.gpr .r8 = 0 ∧ t.mem = s.mem ∧ Keep [.rax, .rsi, .rcx, .r8] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  have hudi := (hku.gpr (show Reg.rdi ∉ [Reg.rax] by decide)).trans hdi
  have hul : word u.mem B a.length.offset = word s.mem B a.length.offset := by rw [hum]
  have hus := hs.congr hku.2.2
  refine WP.mono (WP.keep [.rsi, .rcx, .r8] (Q := fun v =>
    v.gpr .rsi = pointerValue s.mem B a.pointer ∧ v.gpr .rcx = word s.mem B a.length.offset ∧
    v.gpr .r8 = 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨hvp, hvn, hv8, hvm⟩, hkv⟩ =>
      ⟨hvp, hvn, hv8, hvm.trans hum, (hku.trans hkv).mono (by decide)⟩
  xrun [hua, State.ea, Core.field, hudi, fieldAddress, hul,
    hus.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds a.length).2 hZ)]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.OneScan`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.X86_64.EqualHead`, which this module and modules that import it used -/

section

/-! # Resolving both operands of a DSA equality check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem equalHead_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) :
    WP isa (.block (Core.pointer a.pointer ++ ([.mov .rsi (.reg .rax)] : List Instr) ++
      Core.pointer b.pointer ++ ([.mov .rdx (.reg .rax), .mov .rcx (.mem (Core.field a.length)),
        .mov32 .r8 (.imm 0)] : List Instr))) s fun t =>
      t.gpr .rsi = pointerValue s.mem B a.pointer ∧ t.gpr .rdx = pointerValue s.mem B b.pointer ∧
      t.gpr .rcx = word s.mem B a.length.offset ∧ t.gpr .r8 = 0 ∧ t.mem = s.mem ∧
      Keep [.rax, .rsi, .rdx, .rcx, .r8] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok hs hdi hZ a.pointer ha) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun v => v.gpr .rsi = pointerValue s.mem B a.pointer ∧ v.mem = u.mem)
    (by xrun [hua]) rfl) fun v ⟨⟨hvsi, hvm⟩, hkv⟩ => ?_
  have hks := hku.trans hkv
  rw [WP.block_append_iff]
  refine WP.mono (pointer_ok (hs.congr hks.2.2) ((hks.gpr (by decide)).trans hdi) hZ b.pointer hb)
    fun z ⟨hza, hzm, hkz⟩ => ?_
  rw [hvm, hum] at hza
  have hzsi := (hkz.gpr (show Reg.rsi ∉ [Reg.rax] by decide)).trans hvsi
  have hksz := hks.trans hkz
  have hzdi := (hksz.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have hzlen : word z.mem B a.length.offset = word s.mem B a.length.offset := by rw [hzm, hvm, hum]
  refine WP.mono (WP.keep [.rdx, .rcx, .r8] (Q := fun t =>
    t.gpr .rdx = pointerValue s.mem B b.pointer ∧ t.gpr .rcx = word s.mem B a.length.offset ∧
    t.gpr .r8 = 0 ∧ t.mem = z.mem) ?_ rfl) fun t ⟨⟨htd, htc, ht8, htm⟩, hkt⟩ =>
      ⟨(hkt.gpr (by decide)).trans hzsi, htd, htc, ht8, htm.trans (hzm.trans (hvm.trans hum)),
        (hksz.trans hkt).mono (by decide)⟩
  xrun [hza, State.ea, Core.field, hzdi, fieldAddress, hzlen,
    (hs.congr hksz.2.2).ld (Nat.le_trans (VG.Proof.Dsa.field_bounds a.length).2 hZ)]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Minus`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.MinusCore`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.MinusHead`, which only this module used -/

section

/-! # The first limb of DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev minusHead (amount : Nat) : List Instr :=
  [.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
    .mov .rbx (.mem (hdr (sArr aY))), .mov .rax (.mem (at0 .rsi)),
    .alu .sub .rax (.imm (BitVec.ofNat 32 amount)), .store (at0 .rbx) .rax, cfToRbp]

theorem minusHead_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (ha : amount < 2 ^ 31) :
    WP isa (.block (minusHead amount)) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w aN) ∧
      t.gpr .rbx = off B (slot w aY) ∧ Outside B (slot w aY) 8 s.mem t.mem ∧
      (∃ c : Bool, t.gpr .rbp = mask c ∧
        wv t.mem B (slot w aY) 1 + amount = wv s.mem B (slot w aN) 1 + 2 ^ 64 * c.toNat) ∧
      Keep [.r12, .rsi, .rbx, .rax, .rbp] s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (Nat.le_trans (hdr_lt_slot w 8 hi) hZ)
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hbound := hg.scr.nowrap
  refine WP.mono (WP.keep [.r12, .rsi, .rbx, .rax, .rbp] (Q := fun t =>
    t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w aN) ∧
    t.gpr .rbx = off B (slot w aY) ∧ ∃ c : Bool, t.gpr .rbp = mask c ∧
    ∃ r : BitVec 64, t.mem = s.mem.writeW (off B (slot w aY)) r ∧
      r.toNat + amount = (word s.mem B (slot w aN)).toNat + 2 ^ 64 * c.toNat) ?_ rfl)
    fun t ⟨⟨ht12, htsi, htbx, c, htc, r, htm, hval⟩, hk⟩ => ?_
  · unfold minusHead cfToRbp
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aN) (by decide),
      hl (sArr aY) (by decide), hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide),
      hg.scr.ld (show slot w aN + 8 ≤ Z by omega_using [hn]), hg.scr.st (show slot w aY + 8 ≤ Z by omega_using [hy]),
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, sx_ofNat ha]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have h := sbb_toNat (word s.mem B (slot w aN)) (BitVec.ofNat 64 amount) false
    simpa only [Bool.toNat_false, Nat.add_zero,
      show (BitVec.ofBool false).setWidth 64 = 0#64 from rfl, BitVec.sub_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show amount < 2 ^ 64 by omega_using [ha])] using h
  · refine ⟨ht12, htsi, htbx, ?_, ⟨c, htc, ?_⟩, hk⟩
    · rw [htm]; exact writeW_outside _ _ _ (by omega_using [hy, hbound])
    · rw [htm]
      simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul,
        word_writeW_self] using hval

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.MinusStep`, which only this module used -/

section

/-! # Borrow propagation when forming DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- After `j` words of `modulusMinus`'s loop: `Y_j + amount = N_j + 2^(64 j) c`. -/
structure MinusInv (s₀ : State) (B : Addr) (Z eN eY amount : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eY (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eY j + amount = wv s₀.mem B eN j + 2 ^ (64 * j) * c.toNat

theorem minusStep_ok {s₀ : State} {B : Addr} {Z w eN eY amount : Nat}
    (hbx : s₀.gpr .rbx = off B eY) (hsi : s₀.gpr .rsi = off B eN) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hY : eY + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eY + 8 * w ≤ eN ∨ eN + 8 * w ≤ eY) {j : Nat} (hj : j < w) {t : State}
    (hI : MinusInv s₀ B Z eN eY amount j t) :
    WP isa (.block (([cfFromRbp, .mov .rax (.mem (ix .rsi .r14)), .alu .sbb .rax (.imm 0),
        .store (ix .rbx .r14) .rax, cfToRbp] : List Instr) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ MinusInv s₀ B Z eN eY amount (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eY := (hI.keep.gpr (by decide)).trans hbx
  have tsi : t.gpr .rsi = off B eN := (hI.keep.gpr (by decide)).trans hsi
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eY + 8 * j)) r ∧
        r.toNat + c.toNat = (word t.mem B (eN + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 tsi hI.r14, hbp, cf_mask, sx0,
      hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_arith), hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega_arith)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have := sbb_toNat (word t.mem B (eN + 8 * j)) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, Nat.zero_add] at this ⊢
    exact this
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega_arith) (by omega_arith)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega_arith) (by omega_arith)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)
  · have hlow : wv t.mem B eY j = wv (t.mem.writeW (off B (eY + 8 * j)) r) B eY j :=
      ((writeW_outside t.mem B r (by omega_arith)).wv (Or.inl (by omega_arith)) (by omega_arith)).symm
    rw [hm', hm]
    simp only [wv]
    rw [← hlow, word_writeW_self, pow64_succ]
    grind

end VG.Proof.Dsa.X86_64

end

end


/-! # Complete subtraction for DSA modulus-minus constants -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev minusTail : List Instr := [cfFromRbp, .mov .rax (.mem (ix .rsi .r14)), .alu .sbb .rax (.imm 0),
  .store (ix .rbx .r14) .rax, cfToRbp]

/-- Copy the modulus minus a small constant into the ordinary result array.
The input modulus is preserved, including its leading-zero padding. -/
theorem minusCore_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : amount < 2 ^ 31) (hm : amount ≤ wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) s fun t =>
      wv t.mem B (slot w aY) w = wv s.mem B (slot w aN) w - amount ∧
      Outside B (slot w aY) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnowrap := hg.scr.nowrap
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hsep := slot_sep (w := w) (show aY ≠ aN by decide)
  refine WP.seq (WP.mono (minusHead_ok hg hZ ha) fun u ⟨hu12, husi, hubx, hfu, hval, hku⟩ => ?_)
  have huN : ∀ k ≤ w, wv u.mem B (slot w aN) k = wv s.mem B (slot w aN) k :=
    fun k hk => hfu.wv (by omega_using [hsep, hk]) (by omega_using [hnowrap, hn, hk])
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = u.mem → Keep [.r14] u t → t.cf = u.cf →
      MinusInv u B Z (slot w aN) (slot w aY) amount 1 t := by
    intro t ht14 htm hkt _
    obtain ⟨c, huc, huv⟩ := hval
    refine ⟨hg.scr.congr (hkt.2.2.trans hku.2.2), hkt.mono (by decide), ht14,
      by rw [htm]; exact Outside.refl _ _ _ _, ⟨c, (hkt.gpr (by decide)).trans huc, ?_⟩⟩
    rw [htm, huN 1 (by omega_using [hw])]
    exact huv
  refine WP.mono (wordLoop_ok (start := 1) (N := w) (by omega_using [hw]) hw'
    (MinusInv u B Z (slot w aN) (slot w aY) amount) h0
    (fun j _ hj t hi => minusStep_ok hubx husi hu12 (by omega_using [hw']) (by omega_using [hy]) (by omega_using [hn]) (by omega_using [hsep]) hj hi))
    fun t ht => ?_
  obtain ⟨c, _, hv⟩ := ht.val
  rw [huN w (Nat.le_refl _)] at hv
  have hvlt := wv_lt t.mem B (slot w aY) w
  refine ⟨?_, (hfu.mono (Nat.le_refl _) (by omega_using [hw])).trans ht.out, (hku.trans ht.keep).mono (by decide)⟩
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
    omega_using [hv]
  · simp only [Bool.toNat_true, Nat.mul_one] at hv
    omega_using [hm, hvlt, hv]

end VG.Proof.Dsa.X86_64

end

end

/-! # Modulus-minus constants in a linked DSA workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem minus_ok {s : State} {B : Addr} {Z o w wx m amount : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 31) (ham : amount ≤ m) :
    WP isa (.seq (.block (minusHead amount)) (wordLoop 1 minusTail)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = m - amount ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (minusCore_ok hc.good (Nat.le_refl _) hw hw' ha (by rw [hm.modulus]; exact ham))
    fun t ⟨ht, hf, hk⟩ => ?_
  have harr : Arrays (off B o) wx [aY] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aY) hf (Nat.le_refl _) (by omega_using [])
  have hct := arrays_context hc harr (by decide) hk
  have hz := hc.good.scr.nowrap
  have hn := (harr.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hm.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [harr.word0_of_not_mem (by decide) (by decide) hz (by omega_using [hw])]
    exact hm.inverse
  rw [hm.modulus] at ht
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, arrays_work harr (by decide), hk⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CheckEffects`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.CheckCall`, which only this module used -/

section

/-! ### `Dsa.X86_64.MaskContext`, which this module and modules that import it used -/

section

/-! # Acceptance-mask writes preserve reusable arithmetic state -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem maskWrite_good {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hf : Outside B Field.mask.offset 8 s.mem t.mem)
    (hk : Keep [.rax] s t) : Good t B Z w minv := by
  have he : ∀ i < 32, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    hf.word (Or.inl (by change 8 * i + 8 ≤ 360; omega_using [hi])) (by omega_using [hi])
  exact ⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi,
    ⟨(he _ (by decide)).trans hg.hdr.hw, (he _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (he _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)⟩⟩

theorem maskWrite_child {mem mem' : Mem} {B : Addr} {o wx m : Nat} {minv : BitVec 64}
    (child : ChildReady mem B o wx m minv) (hf : Outside B Field.mask.offset 8 mem mem')
    (ho : 368 ≤ o) (hbound : o + slot wx 8 ≤ 2 ^ 64) : ChildReady mem' B o wx m minv := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  have he : ∀ d, o + d + 8 ≤ 2 ^ 64 → word mem' (off B o) d = word mem (off B o) d := by
    intro d hd
    rw [word_off, word_off]
    exact hf.word (Or.inr (by change 368 ≤ o + d; omega_using [ho])) hd
  have hN := slot_le (w := wx) (show aN < 8 by decide)
  refine ⟨child.header.of_words (fun i hi => he _ (by omega_using [hbound, hslot, hi])), ?_, ?_⟩
  · rw [wv_congr (m := mem) (m' := mem') (fun i hi => he _ (by omega_using [hbound, hN, hi]))]
    exact child.modulus
  · rw [he _ (by omega_using [hbound, hN])]
    exact child.inverse

/-- The mask store leaves the parent and selected child ready for another call. -/
theorem accumulate_context {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (ho : 368 ≤ o) (hhi : o + slot wx 8 ≤ Z) {a b : Bool}
    (ha : s.gpr .rax = mask a) (hb : word s.mem B Field.mask.offset = mask b) :
    WP isa (.block Checks.accumulate) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (a && b) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.rax] s t := by
  have hn := hg.scr.nowrap
  exact WP.mono (accumulate_ok hg.scr hg.rdi hZ ha hb) fun t ⟨ht, hf, hk⟩ =>
    ⟨maskWrite_good hg hf hk, maskWrite_child child hf ho (by omega_using [hhi, hn]), ht, hf, hk⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.CheckFrame`, which this module and modules that import it used -/

section

/-! # Memory changed by a DSA validation call -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum

def RangeFrame (B : Addr) (o wx : Nat) (mem mem' : Mem) : Prop :=
  ∀ x, (∀ r ∈ callRanges arg argLen, ofs B x < r.1 ∨ r.1 + r.2 ≤ ofs B x) →
    (∀ r ∈ workRanges wx, ofs (off B o) x < r.1 ∨ r.1 + r.2 ≤ ofs (off B o) x) →
    (ofs B x < Field.mask.offset ∨ Field.mask.offset + 8 ≤ ofs B x) → mem' x = mem x

end VG.Proof.Dsa.X86_64

end

end

/-! # Returning DSA validation predicates through the parent workspace -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- A verified check body returns its boolean mask to the parent and leaves
the modulus ready for the next operation. -/
theorem checkCall_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (a : Operand) (ha : pointerFits a.pointer) {body : Prog isa} {accepted valid : Bool}
    (hmask : word s.mem B Field.mask.offset = mask valid)
    (run : ∀ u, SubCtx u B Z o w wx minv → ModCtx u (off B o) (slot wx 8) wx minv m →
      word u.mem B (8 * arg) = pointerValue s.mem B a.pointer →
      word u.mem B (8 * argLen) = word s.mem B a.length.offset →
      Frm B (callRanges arg argLen) s.mem u.mem → Keep coreRegs s u →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧ ModCtx v (off B o) (slot wx 8) wx minv m ∧
        v.gpr .rax = mask accepted ∧ Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (.seq (.block (Core.operand arg argLen a ++ Core.enter o))
      (.seq body (.block (([Crt.leave] : List Instr) ++ Checks.accumulate)))) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (accepted && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have hn := hg.scr.nowrap
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ a ha (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hua, hul, hfields, hfu, hku⟩ => ?_
  have hchild := call_ready child hfu (by decide) (by decide) (by omega_using [hfield]) (by omega_using [hhi, hn])
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hvm, hkv⟩ => ?_
  have hmv : ModCtx v (off B o) (slot wx 8) wx minv m :=
    ⟨hcv.good, by rw [hvm]; exact hchild.modulus, by rw [hvm]; exact hchild.inverse⟩
  have hks : Keep coreRegs s v := (hku.trans hkv).mono (by decide)
  have hfv : Frm B (callRanges arg argLen) s.mem v.mem := by rw [hvm]; exact hfu
  refine WP.seq (WP.mono (run v hcv hmv (by rw [hvm]; exact hua)
    (by rw [hvm]; exact hul) hfv hks) fun f ⟨hcf, hmf, hfmask, hff, hkf⟩ => ?_)
  rw [WP.block_append_iff]
  have hpm : word f.mem B (8 * sMinv) = parentMinv :=
    (work_parent hcv hff (by decide)).trans (by rw [hvm]; exact hgu.hdr.hminv)
  have hmaskf : word f.mem B Field.mask.offset = mask valid := by
    rw [hff.word_below (fun r hr => (workRanges_ok wx r hr).2) (by omega_using [hhi, hn]) (by omega_using [ho])
      (show Field.mask.offset + 8 ≤ o from hfield), hvm, hfields .mask]
    exact hmask
  refine WP.mono (leave_ok hcf hpm) fun l ⟨hgl, hlm, hkl⟩ => ?_
  have hcl : ChildReady l.mem B o wx m minv :=
    ⟨by rw [hlm]; exact ⟨hcf.hdr, hcf.link⟩, by rw [hlm]; exact hmf.modulus,
      by rw [hlm]; exact hmf.inverse⟩
  refine WP.mono (accumulate_context (b := valid) hgl hcl hZ hfield (by omega_using [hhi])
    ((hkl.gpr (by decide)).trans hfmask) (by rw [hlm]; exact hmaskf))
    fun t ⟨hgt, hct, htmask, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htmask, ?_, ((((hku.trans hkv).trans hkf).trans hkl).trans hkt).mono (by decide)⟩
  intro x hxarg hxwork hxmask
  rw [hft x hxmask, hlm]
  exact (hff x hxwork).trans (by rw [hvm]; exact hfu x hxarg)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ReadyChecks`, which only this module used -/

section

/-! # Preserving both DSA arithmetic contexts across validation checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem nonmask_field (f : Field) (h : f ≠ .mask) : f.offset + 8 ≤ Field.mask.offset := by
  cases f <;> first | decide | exact False.elim (h rfl)

theorem rangeFrame_local {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : RangeFrame B o wx mem mem') (ho : o + slot wx 8 + tabBytes wx ≤ 2 ^ 64) :
    Frm B (localCallRanges o wx Field.mask.offset 8) mem mem' := by
  have hslot : 256 ≤ slot wx 8 := by unfold slot hdrBytes; omega_using []
  intro x hx
  apply hf x
  · intro r hr
    have h := hx (128, 48) (by simp [localCallRanges])
    simp only [callRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [arg, argLen] <;> omega_using [h]
  · intro r hr
    simp only [workRanges, List.mem_singleton] at hr
    subst r
    have h := hx (o + 136, slot wx 8 + tabBytes wx - 136) (by simp [localCallRanges])
    rcases ofs_rebase B x (o := o) (by omega_using [ho, hslot]) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only at * <;> omega_arith
  · exact hx (Field.mask.offset, 8) (by simp [localCallRanges])

theorem checkFrame_field {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx Field.mask.offset 8) mem mem') (ho : pWorkspace ≤ o)
    (f : Field) (hm : f ≠ .mask) : word mem' B f.offset = word mem B f.offset := by
  have hb := VG.Proof.Dsa.field_bounds f
  have hm' := nonmask_field f hm
  apply hf.word_eq _ (Nat.le_trans hb.2 (by decide))
  intro r hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · right; omega_using [hb]
  · left; omega_using [ho, hb]
  · exact Or.inl hm'

theorem Ready.afterCheck {L : ExecutionLayout} {s t : State} (side : ModulusSide)
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hc : ChildReady t.mem L.base side.offset (side.words L) (side.value L) (side.inverse L))
    (hf : RangeFrame L.base side.offset (side.words L) s.mem t.mem)
    (hk : Keep coreRegs s t) : Ready L t := by
  obtain ⟨_, _, _, _, _, hpHi, hqHi, _⟩ := VG.Proof.Dsa.workspace_bounds L.lengths
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ qWorkspace at hpHi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqHi
  have hqa : qWorkspace ≤ activeBytes := by decide
  have hau : activeBytes ≤ usedBytes := by decide
  have hn := h.scratch.nowrap
  have hhi := (side.bounds L).2.2.2.2.1
  have ho : pWorkspace ≤ side.offset := by cases side <;> decide
  have hlf := rangeFrame_local hf (by omega_using [hau, hn, hhi])
  have hfields : ∀ f, f ≠ .mask → word t.mem L.base f.offset = L.fields f :=
    fun f hm => (checkFrame_field hlf ho f hm).trans (h.fields f hm)
  cases side
  · exact ⟨hp, h.scratch.congr hk.2.2, hfields, hc,
      localCall_ready hlf h.qChild (by decide) (by omega_using [hqHi, hau, hn]) (Or.inr hpHi) (Or.inr (by decide))⟩
  · exact ⟨hp, h.scratch.congr hk.2.2, hfields,
      localCall_ready hlf h.pChild (by decide) (by omega_using [hpHi, hqHi, hau, hn]) (Or.inl (by change pWorkspace + slot L.pWords 8 ≤ qWorkspace; omega_using [hpHi])) (Or.inr (by decide)), hc⟩

theorem Ready.afterMask {L : ExecutionLayout} {s t : State}
    (h : Ready L s) (hp : Good t L.base activeBytes outerWords 0)
    (hf : Outside L.base Field.mask.offset 8 s.mem t.mem) (hk : Keep coreRegs s t) : Ready L t := by
  have hhi := (ModulusSide.p.bounds L).2.2.2.2.1
  have hqi := (ModulusSide.q.bounds L).2.2.2.2.1
  change pWorkspace + slot L.pWords 8 + tabBytes L.pWords ≤ activeBytes at hhi
  change qWorkspace + slot L.qWords 8 + tabBytes L.qWords ≤ activeBytes at hqi
  have hn := h.scratch.nowrap
  have hau : activeBytes ≤ usedBytes := by decide
  refine ⟨hp, h.scratch.congr hk.2.2, ?_,
    maskWrite_child h.pChild hf (by decide) (by omega_using [hhi, hn, hau]),
    maskWrite_child h.qChild hf (by decide) (by omega_using [hqi, hn, hau])⟩
  intro f hm
  exact (hf.word (Or.inl (nonmask_field f hm))
    (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))).trans (h.fields f hm)

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ModulusMinus`, which only this module used -/

section

/-! ### `Dsa.X86_64.ResultCall`, which only this module used -/

section

/-! # DSA calls with a result binding and implicit modulus input -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem resultCall_ok {s : State} {B : Addr} {Z o w wx m value k : Nat}
    {minv parentMinv : BitVec 64} {body : Prog isa}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (output : Operand) (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j))
    (run : ∀ u, SubCtx u B Z o w wx minv → ModCtx u (off B o) (slot wx 8) wx minv m →
      WP isa body u fun v => SubCtx v B Z o w wx minv ∧ ModCtx v (off B o) (slot wx 8) wx minv m ∧
        wv v.mem (off B o) (slot wx aY) wx = value ∧
        Frm (off B o) (workRanges wx) u.mem v.mem ∧ Keep mmRegs u v) :
    WP isa (.seq (.block (Core.operand result resultLen output ++ Core.enter o))
      (.seq body (seqs Core.finish))) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k value ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have hslot : 256 ≤ slot w 8 := by unfold slot hdrBytes; omega_using []
  have hn := hg.scr.nowrap
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (operand_context hg hZ output houtp (by decide) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨hgu, hup, hul, _, hf, hk⟩ => ?_
  have hchild := call_ready child hf (by decide) (by decide) (by omega_using [hlo, hslot]) (by omega_using [hhi, hn])
  refine WP.mono (enter_ok hgu hchild.header hlo hhi ho) fun v ⟨hcv, hmem, hkv⟩ => ?_
  have hm : ModCtx v (off B o) (slot wx 8) wx minv m :=
    ⟨hcv.good, by rw [hmem]; exact hchild.modulus, by rw [hmem]; exact hchild.inverse⟩
  have hks : Keep coreRegs s v := (hk.trans hkv).mono (by decide)
  refine WP.mono (returnAfter_ok (parentMinv := parentMinv) hcv (run v hcv hm)
    (by rw [hmem]; exact hgu.hdr.hminv) (by rw [hmem]; exact hup) (by rw [hmem]; exact hul.trans hl)
    hk1 hk' hkw (fun j hj => by rw [hks.2.2]; exact hout j hj) hprefix)
    fun t ⟨hgt, hct, htout, _, hft, hkt⟩ => ?_
  refine ⟨hgt, hct, htout, ?_, (hks.trans hkt).mono (by decide)⟩
  intro x hx hc hxout
  rw [hft x hc hxout, hmem]
  apply (call_argument_frame hf (by decide) (by decide)) x
  intro r hr
  simp only [argumentRanges, List.mem_singleton] at hr
  subst r
  exact hx

end VG.Proof.Dsa.X86_64

end

end

/-! # Encoded p-minus-one and q-minus-two for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Form and encode a modulus-minus constant without changing the modulus. -/
theorem modulusMinus_ok {s : State} {B : Addr} {Z o w wx m k amount : Nat}
    {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 31) (ham : amount ≤ m)
    (output : Operand) (houtp : pointerFits output.pointer)
    (hl : word s.mem B output.length.offset = BitVec.ofNat 64 k)
    (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31) (hkw : wx = (k + 7) / 8)
    (hout : ∀ j < k, InRegions s.wr (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j) 1)
    (hprefix : ∀ j < k, Z ≤ ofs B (pointerValue s.mem B output.pointer + BitVec.ofNat 64 j)) :
    WP isa (Checks.modulusMinus o amount output) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      Spec.Rsa.bytesAt t.mem (pointerValue s.mem B output.pointer) k = Spec.Dsa.encodeBE k (m - amount) ∧
      CallFrame B o wx (pointerValue s.mem B output.pointer) k s.mem t.mem ∧ Keep coreRegs s t := by
  have run := resultCall_ok hg child hZ hlo hhi ho output houtp hl hk1 hk' hkw hout hprefix
    (fun _ hc hm => minus_ok hc hm hw hw' ha ham)
  change WP isa (.seq (.block ((Core.operand result resultLen output ++ Core.enter o) ++ minusHead amount))
    (.seq (wordLoop 1 minusTail) (seqs Core.finish))) s _
  rw [WP.seq_iff, WP.block_append_iff]
  exact WP.mono (WP.seq_iff.mp run) fun u hu =>
    WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv => WP.seq hv

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Equal`, which only this module used -/

section

/-! ### `Dsa.X86_64.EqualLoop`, which only this module used -/

section

/-! # Fixed-length equality scans for DSA signatures and keys -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev equalByte : List Instr := [.movzx8 .rax (at0 .rsi), .movzx8 .r9 (at0 .rdx),
  .alu .xor .rax (.reg .r9), .alu .or .r8 (.reg .rax),
  .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]

theorem byte_widen_eq (a b : Byte) : a.zeroExtend 64 = b.zeroExtend 64 ↔ a = b := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (a.setWidth 64).toNat = (b.setWidth 64).toNat at he
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans a.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; rw [h]

theorem equalByte_ok {s : State} {p q : Addr} {n : Nat}
    (hp : s.gpr .rsi = p) (hq : s.gpr .rdx = q) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1)
    (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block equalByte) s fun t =>
      t.gpr .rsi = p + 1 ∧ t.gpr .rdx = q + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ s.mem p = s.mem q) ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem ∧ Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := by
  have hsub := ofNat64_pred h1 h64
  have hz : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega_using [h64]), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega_using [h1]
  refine WP.mono (WP.keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] (Q := fun t =>
    t.gpr .rsi = p + 1 ∧ t.gpr .rdx = q + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .r8 = s.gpr .r8 ||| ((s.mem p).zeroExtend 64 ^^^ (s.mem q).zeroExtend 64) ∧
    t.zf = some (decide (n = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨htp, htq, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold equalByte
    xrun [State.ea, at0, hp, hq, hn, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hrp, hrq, hsub, hz]
  · refine ⟨htp, htq, htn, ?_, htz, htm, hk⟩
    rw [ht8]
    exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (BitVec.xor_eq_zero_iff.trans (byte_widen_eq _ _)))

/-- Both buffers are read completely, even after the first unequal byte. -/
theorem equalLoop_ok {s : State} {B p q : Addr} {Z : Nat} {as bs : List Byte}
    (hp : s.gpr .rsi = p) (hq : s.gpr .rdx = q) (hn : s.gpr .rcx = BitVec.ofNat 64 as.length)
    (ha : Src s B Z p as) (hb : Src s B Z q bs) (hlen : as.length = bs.length)
    (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64) :
    WP isa (.loop (.block equalByte) .ne) s fun t =>
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ as = bs) ∧ t.mem = s.mem ∧
      Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := by
  let target := s.gpr .r8 = 0 ∧ as = bs
  let Inv := fun n t => ∃ (pa pb : Addr) (aa bb : List Byte),
    aa.length = n ∧ bb.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧
    t.gpr .rsi = pa ∧ t.gpr .rdx = pb ∧ t.gpr .rcx = BitVec.ofNat 64 aa.length ∧
    Src t B Z pa aa ∧ Src t B Z pb bb ∧
    ((t.gpr .r8 = 0 ∧ aa = bb) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t
  refine WP.loop (M := isa) (body := .block equalByte) (c := .ne) Inv ?_ as.length s ?_
  · intro n u ⟨pa, pb, aa, bb, hla, hlb, hpos, hbnd, hup, huq, hun, hua, hub, htarget, hum, hku⟩
    cases aa with
    | nil => simp only [List.length_nil] at hla; omega
    | cons a aa =>
      cases bb with
      | nil => simp only [List.length_nil] at hlb; omega
      | cons b bb =>
        have hrp : InRegions (u.rd ++ u.wr) pa 1 := by simpa using hua.rd 0 (by simp)
        have hrq : InRegions (u.rd ++ u.wr) pb 1 := by simpa using hub.rd 0 (by simp)
        have va : u.mem pa = a := by
          have he := hua.val 0 (by simp)
          change u.mem (pa + 0) = a at he
          exact (congrArg u.mem (BitVec.add_zero pa)).symm.trans he
        have vb : u.mem pb = b := by
          have he := hub.val 0 (by simp)
          change u.mem (pb + 0) = b at he
          exact (congrArg u.mem (BitVec.add_zero pb)).symm.trans he
        refine WP.mono (equalByte_ok hup huq hun hrp hrq (by simp) (by omega_using [hbnd, hla]))
          fun t ⟨htp, htq, htn, ht8, htz, htm, hkt⟩ => ?_
        rw [va, vb] at ht8
        have htarget' : (t.gpr .r8 = 0 ∧ aa = bb) ↔ target := by
          rw [ht8, ← htarget, List.cons.injEq]
          exact and_assoc
        have hk : Keep [.rax, .r9, .r8, .rsi, .rdx, .rcx] s t := (hku.trans hkt).mono (by decide)
        by_cases he : aa.length = 0
        · left
          refine ⟨?_, ?_, htm.trans hum, hk⟩
          · change VG.X86_64.eval .ne t = some false
            simp only [VG.X86_64.eval, htz, List.length_cons, he, decide_true, Option.map_some, Bool.not_true]
          · have heb : bb.length = 0 := by simp only [List.length_cons] at hla hlb; omega_using [hla, hlb, he]
            simpa only [List.length_eq_zero_iff.mp he, List.length_eq_zero_iff.mp heb, and_true] using htarget'
        · right
          refine ⟨?_, aa.length, by simp only [List.length_cons] at hla; omega_using [hla],
            pa + 1, pb + 1, aa, bb, rfl, by simp only [List.length_cons] at hla hlb; omega_using [hla, hlb],
            by omega_using [he], by simp only [List.length_cons] at hla; omega_using [hbnd, hla], htp, htq, ?_,
            source_tail (hua.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt),
            source_tail (hub.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
          · change VG.X86_64.eval .ne t = some true
            simp only [VG.X86_64.eval, htz, List.length_cons, Nat.add_eq_right, he, decide_false, Option.map_some, Bool.not_false]
          · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, q, as, bs, rfl, hlen.symm, h1, h64, hp, hq, hn, ha, hb, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64

end

end


/-! # Complete byte-buffer equality and inequality checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem equal_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) {as bs : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 as.length)
    (has : Src s B Z (pointerValue s.mem B a.pointer) as)
    (hbs : Src s B Z (pointerValue s.mem B b.pointer) bs)
    (helen : as.length = bs.length) (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64)
    (unequal : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.equal a b unequal) s fun t =>
      Good t B Z w minv ∧ word t.mem B Field.mask.offset =
        mask ((if unequal then !decide (as = bs) else decide (as = bs)) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Checks.equal seqs
  refine WP.seq (WP.mono (equalHead_ok hg.scr hg.rdi hZ a b ha hb)
    fun u ⟨hup, huq, hun, hu8, hum, hku⟩ => ?_)
  rw [hlen] at hun
  have hua := has.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  have hub := hbs.congrK (by rw [hum]; exact InScr.refl _ _ _) hku
  refine WP.seq (WP.mono (equalLoop_ok hup huq hun hua hub helen h1 h64) fun f ⟨hf8, hfm, hkf⟩ => ?_)
  have he : decide (f.gpr .r8 = 0) = decide (as = bs) := by
    apply decide_eq_decide.mpr
    simpa only [hu8, true_and] using hf8
  change WP isa (.block _) f _
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .r8 unequal) fun l ⟨hla, hlm, hkl⟩ => ?_
  rw [he] at hla
  have hks := (hku.trans hkf).trans hkl
  have hlmem : l.mem = s.mem := hlm.trans (hfm.trans hum)
  have hgl : Good l B Z w minv :=
    ⟨hg.scr.congr hks.2.2, (hks.gpr (by decide)).trans hg.rdi, hlmem ▸ hg.hdr⟩
  refine WP.mono (accumulate_ok (b := valid) hgl.scr hgl.rdi hZ hla (by rw [hlmem]; exact hmask))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨maskWrite_good hgl hf hk, ht, by rw [← hlmem]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Range`, which only this module used -/

section

/-! ### `Dsa.X86_64.LoadRange`, which only this module used -/

section

/-! # Scalar range checks on caller or scratch byte buffers -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem loadRange_ok {s : State} {B p : Addr} {Z o w wx m sp sl : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hsp : sp < 32) (hsl : sl < 32) {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    (aboveOne : Bool) :
    WP isa (.seq (Arithmetic.load aX sp sl) (Checks.rangeMask aboveOne)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      t.gpr .rax = mask (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < m)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hsp hsl
    hp hl hs h1 (by omega_using [hw48, hfit]) hfit) fun u ⟨hcu, hmu, hv, _, hf, hk⟩ => ?_)
  refine WP.mono (rangeMask_ok hcu.good (Nat.le_refl _) hw2 (by omega_using [hw48]) aboveOne)
    fun t ⟨ht, hmem, hkt⟩ => ?_
  have hft : Frm (off B o) (workRanges wx) u.mem t.mem := by rw [hmem]; exact Frm.refl _ _ _
  have hct := hcu.of_frmT hft (workRanges_ok wx) hkt.2.2 (hkt.gpr (by decide))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by rw [hmem]; exact hmu.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem]; exact hmu.inverse
  rw [hv, hmu.modulus] at ht
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA range validation through the parent calling convention -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Range validation always completes the same load and scans, then combines
its result with the existing mask and returns to the parent workspace. -/
theorem range_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    (aboveOne : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.range o a aboveOne) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < m) && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have run := checkCall_ok hg child hZ hlo hfield hhi ho a ha hmask
    (body := .seq (Arithmetic.load aX arg argLen) (Checks.rangeMask aboveOne))
    (accepted := decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧ Spec.Dsa.decodeBE bytes < m)) ?_
  · unfold Checks.range seqs
    exact WP.seq (WP.mono (WP.seq_iff.mp run) fun u hu =>
      WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv => WP.seq hv))
  intro u hc hm hp hl hf hk
  exact loadRange_ok hc hm hw2 hw48 hwx hw30 (by decide) (by decide) hp (hl.trans hlen)
    (call_source hf hk (by decide) (by decide) (Nat.le_trans (by decide) hZ) hsrc) h1 hfit aboveOne

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Zero`, which only this module used -/

section

/-! ### `Dsa.X86_64.ZeroLoop`, which only this module used -/

section

/-! # Fixed-length bytewise zero tests for DSA acceptance masks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev zeroByte : List Instr := [.movzx8 .rax (at0 .rsi), .alu .or .r8 (.reg .rax),
  .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]

theorem byte_widen_zero (b : Byte) : b.zeroExtend 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    change (b.setWidth 64).toNat = 0 at he
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (show 2 ^ 8 < 2 ^ 64 by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; subst b; rfl

theorem zeroByte_ok {s : State} {p : Addr} {n : Nat}
    (hp : s.gpr .rsi = p) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (hr : InRegions (s.rd ++ s.wr) p 1) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64) :
    WP isa (.block zeroByte) s fun t =>
      t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ s.mem p = 0) ∧
      t.zf = some (decide (n = 1)) ∧ t.mem = s.mem ∧ Keep [.rax, .r8, .rsi, .rcx] s t := by
  have hsub := ofNat64_pred h1 h64
  have hz : (BitVec.ofNat 64 (n - 1) == 0) = decide (n = 1) := by
    rw [ofNat_beq_zero (by omega_using [h64]), Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    omega_using [h1]
  refine WP.mono (WP.keep [.rax, .r8, .rsi, .rcx] (Q := fun t =>
    t.gpr .rsi = p + 1 ∧ t.gpr .rcx = BitVec.ofNat 64 (n - 1) ∧
    t.gpr .r8 = s.gpr .r8 ||| (s.mem p).zeroExtend 64 ∧ t.zf = some (decide (n = 1)) ∧ t.mem = s.mem)
    ?_ rfl) fun t ⟨⟨htp, htn, ht8, htz, htm⟩, hk⟩ => ?_
  · unfold zeroByte
    xrun [State.ea, at0, hp, hn, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hr, hsub, hz]
  · exact ⟨htp, htn, by rw [ht8]; exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (byte_widen_zero _)), htz, htm, hk⟩

/-- A positive-length zero scan reads every byte, including leading zeros. -/
theorem zeroLoop_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hp : s.gpr .rsi = p) (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (h1 : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa (.loop (.block zeroByte) .ne) s fun t =>
      (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ ∀ b ∈ bs, b = 0) ∧ t.mem = s.mem ∧
      Keep [.rax, .r8, .rsi, .rcx] s t := by
  let target := s.gpr .r8 = 0 ∧ ∀ b ∈ bs, b = 0
  let Inv := fun n t => ∃ (ptr : Addr) (rest : List Byte),
    rest.length = n ∧ 0 < n ∧ n < 2 ^ 64 ∧ t.gpr .rsi = ptr ∧
    t.gpr .rcx = BitVec.ofNat 64 rest.length ∧ Src t B Z ptr rest ∧
    ((t.gpr .r8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target) ∧ t.mem = s.mem ∧
    Keep [.rax, .r8, .rsi, .rcx] s t
  refine WP.loop (M := isa) (body := .block zeroByte) (c := .ne) Inv ?_ bs.length s ?_
  · intro n u ⟨ptr, rest, hlen, hpos, hbnd, hup, hun, hus, htarget, hum, hku⟩
    cases rest with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons b rest =>
      have hr : InRegions (u.rd ++ u.wr) ptr 1 := by simpa using hus.rd 0 (by simp)
      have hbyte : u.mem ptr = b := by
        have he := hus.val 0 (by simp)
        change u.mem (ptr + 0) = b at he
        exact (congrArg u.mem (BitVec.add_zero ptr)).symm.trans he
      refine WP.mono (zeroByte_ok hup hun hr (by simp) (by omega_using [hbnd, hlen]))
        fun t ⟨htp, htn, ht8, htz, htm, hkt⟩ => ?_
      rw [hbyte] at ht8
      have htarget' : (t.gpr .r8 = 0 ∧ ∀ b ∈ rest, b = 0) ↔ target := by
        rw [ht8, ← htarget]
        simp only [List.mem_cons, forall_eq_or_imp]
        exact and_assoc
      have hk : Keep [.rax, .r8, .rsi, .rcx] s t := (hku.trans hkt).mono (by decide)
      by_cases he : rest.length = 0
      · left
        refine ⟨?_, ?_, htm.trans hum, hk⟩
        · change VG.X86_64.eval .ne t = some false
          simp only [VG.X86_64.eval, htz, List.length_cons, he, decide_true, Option.map_some, Bool.not_true]
        · simpa only [List.length_eq_zero_iff.mp he, List.not_mem_nil, forall_const, false_implies, implies_true, and_true] using htarget'
      · right
        refine ⟨?_, rest.length, by simp only [List.length_cons] at hlen; omega_using [hlen],
          ptr + 1, rest, rfl, by omega_using [he], by simp only [List.length_cons] at hlen; omega_using [hbnd, hlen],
          htp, ?_, source_tail (hus.congrK (by rw [htm]; exact InScr.refl _ _ _) hkt), htarget', htm.trans hum, hk⟩
        · change VG.X86_64.eval .ne t = some true
          simp only [VG.X86_64.eval, htz, List.length_cons, Nat.add_eq_right, he, decide_false, Option.map_some, Bool.not_false]
        · simpa only [List.length_cons, Nat.add_sub_cancel] using htn
  · exact ⟨p, bs, rfl, h1, h64, hp, hn, hs, Iff.rfl, rfl, Keep.refl _ _⟩

end VG.Proof.Dsa.X86_64

end

end


/-! # Complete byte-buffer zero and nonzero checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- Scan every byte and intersect the acceptance mask with the requested
zero/nonzero predicate. No input or temporary scalar buffer is modified. -/
theorem zero_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : pWorkspace ≤ Z)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64)
    (nonzero : Bool) {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.zero a nonzero) s fun t =>
      Good t B Z w minv ∧ word t.mem B Field.mask.offset =
        mask ((if nonzero then !decide (∀ b ∈ bytes, b = 0) else decide (∀ b ∈ bytes, b = 0)) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep coreRegs s t := by
  unfold Checks.zero seqs
  refine WP.seq (WP.mono (zeroHead_ok hg.scr hg.rdi hZ a ha)
    fun v ⟨hvp, hvn, hv8, hvm, hks⟩ => ?_)
  rw [hlen] at hvn
  have hvs : Src v B Z (pointerValue s.mem B a.pointer) bytes :=
    hsrc.congrK (by rw [hvm]; exact InScr.refl _ _ _) hks
  refine WP.seq (WP.mono (zeroLoop_ok hvp hvn hvs h1 h64) fun f ⟨hf8, hfm, hkf⟩ => ?_)
  have he : decide (f.gpr .r8 = 0) = decide (∀ b ∈ bytes, b = 0) := by
    apply decide_eq_decide.mpr
    simpa only [hv8, true_and] using hf8
  change WP isa (.block _) f _
  rw [WP.block_append_iff]
  refine WP.mono (zeroMask_ok .r8 nonzero) fun l ⟨hla, hlm, hkl⟩ => ?_
  rw [he] at hla
  have hkl' := (hks.trans hkf).trans hkl
  have hlmem : l.mem = s.mem := hlm.trans (hfm.trans hvm)
  have hgl : Good l B Z w minv :=
    ⟨hg.scr.congr hkl'.2.2, (hkl'.gpr (by decide)).trans hg.rdi, hlmem ▸ hg.hdr⟩
  refine WP.mono (accumulate_ok (b := valid) hgl.scr hgl.rdi hZ hla (by rw [hlmem]; exact hmask))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨maskWrite_good hgl hf hk, ht, by rw [← hlmem]; exact hf, (hkl'.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.IsOne`, which only this module used -/

section

/-! ### `Dsa.X86_64.LoadOne`, which only this module used -/

section

/-! # Testing a byte-encoded DSA subgroup result against one -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem loadOne_ok {s : State} {B p : Addr} {Z o w wx m sp sl : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hsp : sp < 32) (hsl : sl < 32) {bytes : List Byte}
    (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bytes.length)
    (hs : Src s B Z p bytes) (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx) :
    WP isa (.seq (Arithmetic.load aX sp sl) (.seq (.seq (.block oneScanHead)
      (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)]))
      (.block [.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax)]))) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      t.gpr .rax = mask (decide (Spec.Dsa.decodeBE bytes = 1)) ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hsp hsl
    hp hl hs h1 (by omega_using [hw48, hfit]) hfit) fun u ⟨hcu, hmu, hv, _, hf, hk⟩ => ?_)
  refine WP.seq (WP.mono (oneScan_ok hcu.good (Nat.le_refl _) hw2 (by omega_using [hw48]))
    fun v ⟨hv15, hvm, hkv⟩ => ?_)
  rw [hv] at hv15
  refine WP.mono (zeroMask_ok .r15 false) fun t ⟨ht, htm, hkt⟩ => ?_
  change t.gpr .rax = mask (decide (v.gpr .r15 = 0)) at ht
  rw [decide_eq_decide.mpr hv15] at ht
  have hmem : t.mem = u.mem := htm.trans hvm
  have hft : Frm (off B o) (workRanges wx) u.mem t.mem := by rw [hmem]; exact Frm.refl _ _ _
  have hku : Keep mmRegs u t := (hkv.trans hkt).mono (by decide)
  have hct := hcu.of_frmT hft (workRanges_ok wx) hku.2.2 (hku.gpr (by decide))
  have hn : wv t.mem (off B o) (slot wx aN) wx = m := by rw [hmem]; exact hmu.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hmem]; exact hmu.inverse
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, hf.trans hft, (hk.trans hku).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Complete checks of DSA subgroup exponentiation results -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem isOne_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv parentMinv : BitVec 64}
    (hg : Good s B Z w parentMinv) (child : ChildReady s.mem B o wx m minv)
    (hZ : pWorkspace ≤ Z) (hlo : slot w 8 ≤ o) (hfield : 368 ≤ o)
    (hhi : o + slot wx 8 + tabBytes wx ≤ Z) (ho : o < 2 ^ 31)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hlen : word s.mem B a.length.offset = BitVec.ofNat 64 bytes.length)
    (hsrc : Src s B Z (pointerValue s.mem B a.pointer) bytes)
    (h1 : 1 ≤ bytes.length) (hfit : (bytes.length + 7) / 8 ≤ wx)
    {valid : Bool} (hmask : word s.mem B Field.mask.offset = mask valid) :
    WP isa (Checks.isOne o a) s fun t =>
      Good t B Z w parentMinv ∧ ChildReady t.mem B o wx m minv ∧
      word t.mem B Field.mask.offset = mask (decide (Spec.Dsa.decodeBE bytes = 1) && valid) ∧
      RangeFrame B o wx s.mem t.mem ∧ Keep coreRegs s t := by
  have run := checkCall_ok hg child hZ hlo hfield hhi ho a ha hmask
    (body := .seq (Arithmetic.load aX arg argLen) (.seq (.seq (.block oneScanHead)
      (wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .r15 (.reg .rax)]))
      (.block [.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax)])))
    (accepted := decide (Spec.Dsa.decodeBE bytes = 1)) ?_
  · unfold Checks.isOne seqs
    refine WP.seq (WP.mono (WP.seq_iff.mp run) fun u hu => ?_)
    refine WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hu)) fun v hv => ?_)
    refine WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp hv)) fun z hz => ?_)
    refine WP.seq (WP.mono hz fun f hf => ?_)
    change WP isa (.block (([.alu .cmp .r15 (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++
      (([Crt.leave] : List Instr) ++ Checks.accumulate))) f _
    exact WP.block_append_iff.mpr hf
  intro u hc hm hp hl hf hk
  exact loadOne_ok hc hm hw2 hw48 hwx hw30 (by decide) (by decide) hp (hl.trans hlen)
    (call_source hf hk (by decide) (by decide) (Nat.le_trans (by decide) hZ) hsrc) h1 hfit

end VG.Proof.Dsa.X86_64

end

end


/-! # Validation effects shared by the DSA key-check schedules -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure CheckEffect (L : ExecutionLayout) (valid : Bool) (s t : State) : Prop where
  ready : Ready L t
  mask : word t.mem L.base Field.mask.offset = VG.Proof.Bignum.mask valid
  frame : Outside L.base 128 (activeBytes - 128) s.mem t.mem
  keep : Keep coreRegs s t

theorem checkFrame_outside {B : Addr} {o wx : Nat} {mem mem' : Mem}
    (hf : Frm B (localCallRanges o wx Field.mask.offset 8) mem mem')
    (ho : pWorkspace ≤ o) (hhi : o + slot wx 8 + tabBytes wx ≤ activeBytes) :
    Outside B 128 (activeBytes - 128) mem mem' := by
  have hslot : 136 ≤ slot wx 8 + tabBytes wx := by unfold slot hdrBytes; omega_using []
  have hlo : 128 ≤ pWorkspace := by decide
  have hma : Field.mask.offset + 8 ≤ activeBytes := by decide
  have hml : 128 ≤ Field.mask.offset := by decide
  intro x hx
  apply hf x
  intro range hr
  simp only [localCallRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only at * <;> omega_arith

theorem readyRange_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes)
    (h1 : 1 ≤ bytes.length) (hw : (bytes.length + 7) / 8 ≤ side.words L)
    (aboveOne : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.range side.offset a aboveOne) s
      (CheckEffect L (decide ((if aboveOne then 1 else 0) < Spec.Dsa.decodeBE bytes ∧
        Spec.Dsa.decodeBE bytes < side.value L) && valid) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, _, _⟩ := side.bounds L
  have hfield : 368 ≤ side.offset := by cases side <;> decide
  have hpw : pWorkspace ≤ side.offset := by cases side <;> decide
  refine WP.mono (range_ok h.parent (h.child side) (by decide) hlo hfield hhi ho
    hw2 hw48 hw48 (by decide) a ha hb.length hb.source h1 hw aboveOne hm) ?_
  intro t ⟨hp, hc, hm', hf, hk⟩
  exact ⟨h.afterCheck side hp hc hf hk, hm',
    checkFrame_outside (rangeFrame_local hf (Nat.le_trans hhi (by decide))) hpw hhi, hk⟩

theorem readyIsOne_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes)
    (h1 : 1 ≤ bytes.length) (hw : (bytes.length + 7) / 8 ≤ side.words L)
    {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.isOne side.offset a) s
      (CheckEffect L (decide (Spec.Dsa.decodeBE bytes = 1) && valid) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, _, _⟩ := side.bounds L
  have hfield : 368 ≤ side.offset := by cases side <;> decide
  have hpw : pWorkspace ≤ side.offset := by cases side <;> decide
  refine WP.mono (isOne_ok h.parent (h.child side) (by decide) hlo hfield hhi ho
    hw2 hw48 hw48 (by decide) a ha hb.length hb.source h1 hw hm) ?_
  intro t ⟨hp, hc, hm', hf, hk⟩
  exact ⟨h.afterCheck side hp hc hf hk, hm',
    checkFrame_outside (rangeFrame_local hf (Nat.le_trans hhi (by decide))) hpw hhi, hk⟩

theorem readyZero_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a : Operand) (ha : pointerFits a.pointer) {bytes : List Byte}
    (hb : OperandBytes s L.base activeBytes a bytes) (h1 : 0 < bytes.length) (h64 : bytes.length < 2 ^ 64)
    (nonzero : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.zero a nonzero) s
      (CheckEffect L ((if nonzero then !decide (∀ b ∈ bytes, b = 0) else decide (∀ b ∈ bytes, b = 0)) && valid) s) := by
  refine WP.mono (zero_ok h.parent (by decide) a ha hb.length hb.source h1 h64 nonzero hm) ?_
  intro t ⟨hp, hm', hf, hk⟩
  exact ⟨h.afterMask hp hf hk, hm', hf.mono (by decide) (by decide), hk⟩

theorem readyEqual_ok {L : ExecutionLayout} {s : State} (h : Ready L s)
    (a b : Operand) (ha : pointerFits a.pointer) (hb : pointerFits b.pointer) {as bs : List Byte}
    (has : OperandBytes s L.base activeBytes a as) (hbs : OperandBytes s L.base activeBytes b bs)
    (hlen : as.length = bs.length) (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64)
    (unequal : Bool) {valid : Bool} (hm : word s.mem L.base Field.mask.offset = mask valid) :
    WP isa (Checks.equal a b unequal) s
      (CheckEffect L ((if unequal then !decide (as = bs) else decide (as = bs)) && valid) s) := by
  refine WP.mono (equal_ok h.parent (by decide) a b ha hb has.length has.source hbs.source hlen h1 h64 unequal hm) ?_
  intro t ⟨hp, hm', hf, hk⟩
  exact ⟨h.afterMask hp hf hk, hm', hf.mono (by decide) (by decide), hk⟩

theorem readyMinus_ok {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (amount : Nat) (ha : amount < 2 ^ 31) (ham : amount ≤ side.value L)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    WP isa (Checks.modulusMinus side.offset amount ⟨.local d, side.lengthField⟩) s
      (CallResult L side d (side.value L - amount) s) := by
  obtain ⟨hw2, hw48, hlo, ho, hhi, hk1, hk31⟩ := side.bounds L
  have hdp : pointerFits (.local d) := by
    change d < 2 ^ 31
    have : usedBytes < 2 ^ 31 := by decide
    omega_using [hend, this]
  refine WP.mono (modulusMinus_ok h.parent (h.child side) (by decide) hlo hhi ho hw2
    (Nat.lt_of_le_of_lt hw48 (by decide)) ha ham ⟨.local d, side.lengthField⟩ hdp
    (h.length side) hk1 hk31 rfl (h.local_write hend) (h.local_out hd hend)) ?_
  intro t ⟨hp, hc, hv, hf, hk⟩
  exact ⟨h.afterCall side hp hc hf hk hd hend, hv, hf, hk⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Validation preserves every operand outside the arithmetic prefix -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def stablePointer : Pointer → Prop
  | .input f => f ≠ .mask
  | _ => True

theorem Ready.pointer_eq {L : ExecutionLayout} {s t : State} (hs : Ready L s) (ht : Ready L t)
    (p : Pointer) (hp : stablePointer p) : pointerValue t.mem L.base p = pointerValue s.mem L.base p := by
  cases p with
  | input f => exact (ht.fields f hp).trans (hs.fields f hp).symm
  | «local» _ => rfl
  | signatureS =>
    exact congrArg₂ (· + ·)
      ((ht.fields .signature (by decide)).trans (hs.fields .signature (by decide)).symm)
      ((ht.fields .qLen (by decide)).trans (hs.fields .qLen (by decide)).symm)

theorem CheckEffect.preserve {L : ExecutionLayout} {s t : State} {valid : Bool}
    (h : CheckEffect L valid s t) (hs : Ready L s)
    {a : Operand} {bytes : List Byte} {Z : Nat} (hZ : activeBytes ≤ Z)
    (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (hb : OperandBytes s L.base Z a bytes) : OperandBytes t L.base Z a bytes := by
  refine ⟨(h.ready.fields a.length ha).trans ((hs.fields a.length ha).symm.trans hb.length), ?_⟩
  rw [hs.pointer_eq h.ready a.pointer hp]
  have hlo : 128 ≤ activeBytes := by decide
  exact hb.source.congrK (InScr.of_outside h.frame (by omega_using [hZ, hlo])) h.keep

theorem CheckEffect.scheduleFrame {L : ExecutionLayout} {s t : State} {valid : Bool}
    (h : CheckEffect L valid s t) : Outside L.base 128 (usedBytes - 128) s.mem t.mem :=
  h.frame.mono (by decide) (by decide)

end VG.Proof.Dsa.X86_64
