module

public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeFrame
import VerifiedGarbage.Proof.Dsa.AArch64.Masks
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import Mathlib.Order.Lattice
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.AArch64.ScanField
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Spec.Dsa
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Dsa.AArch64.ZeroMask
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
import VerifiedGarbage.Proof.Dsa.Layout

/-! ### `Dsa.AArch64.OddCheck`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.LastByte`, which this module and modules that import it used -/

section

/-! # Reading the final encoded modulus byte for oddness validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem lastByte_ok {s : State} {B p : Addr} {Z n : Nat} {b : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (fp fl : Field) (r : Reg) (hp : word s.mem B fp.offset = p)
    (hl : word s.mem B fl.offset = BitVec.ofNat 64 n) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (n - 1)) 1)
    (hb : s.mem (p + BitVec.ofNat 64 (n - 1)) = b) :
    WP isa (.block [Core.field .x1 fp, Core.field .x9 fl, .subImm .x .x9 .x9 1,
      .add .x .x1 .x1 .x9, .ldrb r .x1 0]) s fun t =>
      t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem ∧ Keep [.x1, .x9, r] s t := by
  have he : BitVec.ofNat 64 n - (1#64) = BitVec.ofNat 64 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  refine WP.mono (WP.keep [.x1, .x9, r] (Q := fun t =>
    t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem) ?_ ?_ ?_ ?_)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  · brun [Core.field, hdi, field_enc fp, field_enc fl, hp, hl, he, hr, hb, read_one,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.zeroExtend]
    have := b.isLt
    omega_using []
  all_goals cases r <;> rfl

end VG.Proof.Dsa.AArch64

end

end

/-! # Public oddness checks on the encoded DSA moduli -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Parity.lean`, which only this module imported.
section

/-! # The shared oddness mask for DSA moduli -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64
open VG.Proof.Bignum

theorem word_low_bit (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 64 by omega)]

theorem word_odd_mask (x : BitVec 64) : 0 - (x &&& 1) = mask (decide (x.toNat % 2 = 1)) := by
  rw [word_low_bit]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- The implementation combines low bits before converting the result to a mask. -/
theorem modulus_odd_mask (p q : Byte) :
    0 - (p.zeroExtend 64 &&& q.zeroExtend 64 &&& 1) =
      mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) := by
  rw [word_odd_mask, BitVec.toNat_and]
  change mask (decide (((p.setWidth 64).toNat &&& (q.setWidth 64).toNat) % 2 = 1)) = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans p.isLt (show 2 ^ 8 < 2 ^ 64 by decide)),
    Nat.mod_eq_of_lt (Nat.lt_trans q.isLt (show 2 ^ 8 < 2 ^ 64 by decide))]
  exact congrArg mask (decide_eq_decide.mpr Nat.and_mod_two_eq_one)

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev oddCombine : List Instr :=
  [.logic .and .x .x3 .x3 .x2, movi .x2 1, .logic .and .x .x3 .x3 .x2,
    movi .x2 0, .sub .x .x3 .x2 .x3]

theorem oddCombine_ok {s : State} {p q : Byte}
    (ha : s.gpr .x3 = p.zeroExtend 64) (hd : s.gpr .x2 = q.zeroExtend 64) :
    WP isa (.block oddCombine) s fun t =>
      t.gpr .x3 = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x2] s t := by
  refine WP.mono (WP.keep [.x3, .x2] (Q := fun t =>
    t.gpr .x3 = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold oddCombine
  brun [ha, hd]
  exact modulus_odd_mask p q

abbrev oddCheck : List Instr :=
  ([Core.field .x1 .p, Core.field .x9 .pLen, .subImm .x .x9 .x9 1,
    .add .x .x1 .x1 .x9, .ldrb .x3 .x1 0] : List Instr) ++
  ([Core.field .x1 .q, Core.field .x9 .qLen, .subImm .x .x9 .x9 1,
    .add .x .x1 .x1 .x9, .ldrb .x2 .x1 0] : List Instr) ++ oddCombine ++ Checks.accumulate

theorem oddCheck_ok {s : State} {B pp qp : Addr} {Z pl ql : Nat} {pLast qLast : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 pl)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 ql)
    (hp1 : 1 ≤ pl) (hp64 : pl < 2 ^ 64) (hq1 : 1 ≤ ql) (hq64 : ql < 2 ^ 64)
    (hpr : InRegions (s.rd ++ s.wr) (pp + BitVec.ofNat 64 (pl - 1)) 1)
    (hqr : InRegions (s.rd ++ s.wr) (qp + BitVec.ofNat 64 (ql - 1)) 1)
    (hpv : s.mem (pp + BitVec.ofNat 64 (pl - 1)) = pLast)
    (hqv : s.mem (qp + BitVec.ofNat 64 (ql - 1)) = qLast)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block oddCheck) s fun t =>
      word t.mem B Field.mask.offset = mask (decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && valid) ∧
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.x3, .x4, .x2, .x1, .x9] s t := by
  unfold oddCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lastByte_ok hs hdi hZ .p .pLen .x3 hpp hpl hp1 hp64 hpr hpv)
    fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  have hudi := (hku.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  refine WP.mono (lastByte_ok (p := qp) (b := qLast) (hs.congr hku.wr) hudi hZ .q .qLen .x2
    (by rw [hum]; exact hqp) (by rw [hum]; exact hql) hq1 hq64
    (by rw [hku.rd, hku.wr]; exact hqr) (by rw [hum]; exact hqv))
    fun v ⟨hvd, hvm, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hva := (hkv.gpr .x3 (show Reg.x3 ∉ _ by decide)).trans hua
  refine WP.mono (oddCombine_ok hva hvd) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hks := (hku.trans hkv).trans hkz
  have hzs := hs.congr hks.wr
  have hzdi := (hks.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  refine WP.mono (accumulate_ok (b := valid) hzs hzdi hZ hza (by rw [hzm, hvm, hum]; exact hm))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨ht, by rw [← hum, ← hvm, ← hzm]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.ShapeSizes`, which the modules that import this one used -/

section

/-! ### `Dsa.AArch64.WidthChoice`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.WidthMask`, which only this module used -/

section

/-! # Equality masks for supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem widthMask_ok {s : State} {n value : Nat}
    (hn : n < 2 ^ 16) (hv : value < 2 ^ 64) (h8 : s.gpr .x8 = BitVec.ofNat 64 value) :
    WP isa (.block (Checks.widthMask n)) s fun t =>
      t.gpr .x3 = mask (decide (value = n)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4] s t := by
  have hn64 : n < 2 ^ 64 := by omega_using [hn]
  have he : (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0 ↔ value = n := by
    change (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0#64 ↔ value = n
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hn64] using h'
    · intro h; rw [h]
  unfold Checks.widthMask
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3] (Q := fun u =>
    u.gpr .x3 = BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n ∧ u.mem = s.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨hu, hm⟩, hk⟩ => ?_
  · have hn' : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega_using [hn]
    brun [h8, hn']
  refine WP.mono (zeroMask_ok .x3 false) fun t ⟨ht, htm, hkt⟩ => ?_
  simp only [Bool.false_eq_true, ite_false, hu, decide_eq_decide.mpr he] at ht
  exact ⟨ht, htm.trans hm, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Public selection of supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem sub_beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == (0#64)) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  constructor
  · intro h
    have hv := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv
  · intro h; rw [h]

theorem widthCompare_ok {s : State} {value n : Nat}
    (hv : value < 2 ^ 64) (hn : n < 4096) (hd : s.gpr .x2 = BitVec.ofNat 64 value) :
    WP isa (.block [.subImm .x .x6 .x2 n]) s fun t =>
      (t.gpr .x6 == (0#64)) = decide (value = n) ∧ t.gpr .x2 = BitVec.ofNat 64 value ∧ t.mem = s.mem ∧ Keep [.x2, .x6] s t := by
  refine WP.mono (WP.keep [.x2, .x6] (Q := fun t =>
    (t.gpr .x6 == (0#64)) = decide (value = n) ∧ t.gpr .x2 = BitVec.ofNat 64 value ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  brun [hd, hn]
  exact sub_beq_ofNat hv (by omega_using [hn])

/-- Recover the saved p width and prepare the first public branch. -/
theorem readWidth_ok {s : State} {B : Addr} {Z p : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .x0 = B) (hZ : 184 ≤ Z) (hp : p < 2 ^ 64)
    (hw : word s.mem B 176 = BitVec.ofNat 64 p) :
    WP isa (.block [ldh .x2 22, .subImm .x .x6 .x2 128]) s fun t =>
      (t.gpr .x6 == (0#64)) = decide (p = 128) ∧ t.gpr .x2 = BitVec.ofNat 64 p ∧ t.mem = s.mem ∧ Keep [.x2, .x6] s t := by
  refine WP.mono (WP.keep [.x2, .x6] (Q := fun t =>
    (t.gpr .x6 == (0#64)) = decide (p = 128) ∧ t.gpr .x2 = BitVec.ofNat 64 p ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  brun [hdi, hdr_enc (show 22 < 32 by decide), hw, hs.ld hZ]
  exact sub_beq_ofNat hp (by decide)

theorem mask_union (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> decide

/-- The 2048-bit modulus supports both 224- and 256-bit subgroups. -/
theorem widthEither_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 q) :
    WP isa (.block (Checks.widthMask 28 ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 32 ++
      ([.logic .orr .x .x3 .x3 .x11] : List Instr))) s fun t =>
      t.gpr .x3 = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = s.mem ∧ Keep [.x3, .x4, .x11] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (widthMask_ok (by decide) hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x11] (Q := fun v => v.gpr .x11 = mask (decide (q = 28)) ∧ v.mem = u.mem)
    (by brun [hua]) rfl rfl rfl) fun v ⟨⟨hv10, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr .x8 (show Reg.x8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hz10 := (hkz.gpr .x11 (show Reg.x11 ∉ [Reg.x3, Reg.x4] by decide)).trans hv10
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.gpr .x3 = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)), (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  brun [hza, hz10, mask_union]
  rw [← Bool.decide_or]
  exact congrArg mask (decide_eq_decide.mpr or_comm)

/-- The legacy 160-bit subgroup extends the two FIPS 2048-bit cases. -/
theorem width2048_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .x8 = BitVec.ofNat 64 q) :
    WP isa (.block Checks.width2048) s fun t =>
      t.gpr .x3 = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x11] s t := by
  unfold Checks.width2048
  rw [show Checks.widthMask 28 ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 32 ++
      ([.logic .orr .x .x3 .x3 .x11] : List Instr) ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 20 ++
      ([.logic .orr .x .x3 .x3 .x11] : List Instr) =
      (Checks.widthMask 28 ++ ([mov .x11 .x3] : List Instr) ++ Checks.widthMask 32 ++
        ([.logic .orr .x .x3 .x3 .x11] : List Instr)) ++
      (([mov .x11 .x3] : List Instr) ++ Checks.widthMask 20 ++ ([.logic .orr .x .x3 .x3 .x11] : List Instr)) by
        simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (widthEither_ok hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.x11] (Q := fun v =>
    v.gpr .x11 = mask (decide (q = 28 ∨ q = 32)) ∧ v.mem = u.mem)
    (by brun [hua]) rfl rfl rfl) fun v ⟨⟨hvs, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr .x8 (show Reg.x8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hzs := (hkz.gpr .x11 (show Reg.x11 ∉ [Reg.x3, Reg.x4] by decide)).trans hvs
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.gpr .x3 = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)),
        (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  brun [hza, hzs, mask_union, ← Bool.decide_or]

abbrev widthChoice : Prog isa :=
  .ite (.zero .x .x6) (.block (Checks.widthMask 20))
    (.seq (.block [.subImm .x .x6 .x2 256])
      (.ite (.zero .x .x6)
        (.block Checks.width2048)
        (.seq (.block [.subImm .x .x6 .x2 384])
          (.ite (.zero .x .x6) (.block (Checks.widthMask 32)) (.block [movi .x3 0])))))

/-- The supported-width switch returns exactly the spec's (L,N) predicate. -/
theorem widthChoice_ok {s : State} {p q : Nat} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : s.gpr .x2 = BitVec.ofNat 64 p) (h8 : s.gpr .x8 = BitVec.ofNat 64 q)
    (hz : (s.gpr .x6 == (0#64)) = decide (p = 128)) :
    WP isa widthChoice s fun t =>
      t.gpr .x3 = mask (decide (Spec.Dsa.supportedSizes (8 * p) (8 * q))) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x2, .x6, .x11] s t := by
  unfold widthChoice
  by_cases h128 : p = 128
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change some (s.gpr .x6 == (0#64)) = some true
      simp only [hz, h128, decide_true]
    · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 := by
        unfold Spec.Dsa.supportedSizes; omega_using [h128]
      rw [decide_eq_decide.mpr he]
      exact WP.mono (widthMask_ok (by decide) hq h8) fun t ⟨ht, hm, hk⟩ => ⟨ht, hm, hk.mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change some (s.gpr .x6 == (0#64)) = some false
      simp only [hz, h128, decide_false]
    · refine WP.seq (WP.mono (widthCompare_ok hp (show 256 < 4096 by decide) hd)
        fun u ⟨huz, hud, hum, hku⟩ => ?_)
      have hu8 := (hku.gpr .x8 (show Reg.x8 ∉ [Reg.x2, Reg.x6] by decide)).trans h8
      by_cases h256 : p = 256
      · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
        · change some (u.gpr .x6 == (0#64)) = some true
          simp only [huz, h256, decide_true]
        · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 ∨ q = 28 ∨ q = 32 := by
            unfold Spec.Dsa.supportedSizes; omega_using [h256]
          rw [decide_eq_decide.mpr he]
          exact WP.mono (width2048_ok hq hu8) fun t ⟨ht, hm, hk⟩ =>
            ⟨ht, hm.trans hum, (hku.trans hk).mono (by decide)⟩
      · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
        · change some (u.gpr .x6 == (0#64)) = some false
          simp only [huz, h256, decide_false]
        · refine WP.seq (WP.mono (widthCompare_ok hp (show 384 < 4096 by decide) hud)
            fun v ⟨hvz, _, hvm, hkv⟩ => ?_)
          have hv8 := (hkv.gpr .x8 (show Reg.x8 ∉ [Reg.x2, Reg.x6] by decide)).trans hu8
          by_cases h384 : p = 384
          · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
            · change some (v.gpr .x6 == (0#64)) = some true
              simp only [hvz, h384, decide_true]
            · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 32 := by
                unfold Spec.Dsa.supportedSizes; omega_using [h384]
              rw [decide_eq_decide.mpr he]
              exact WP.mono (widthMask_ok (by decide) hq hv8) fun t ⟨ht, hm, hk⟩ =>
                ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩
          · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
            · change some (v.gpr .x6 == (0#64)) = some false
              simp only [hvz, h384, decide_false]
            · have he : ¬ Spec.Dsa.supportedSizes (8 * p) (8 * q) := by
                unfold Spec.Dsa.supportedSizes; omega_using [h128, h256, h384]
              rw [decide_eq_false he]
              refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask false ∧ t.mem = v.mem)
                (by brun) rfl rfl rfl) fun t ⟨⟨ht, hm⟩, hk⟩ =>
                  ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # The two public width scans and supported-size selection -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeSizes : Prog isa := seqs [
  .block [Core.field .x1 .p, Core.field .x9 .pLen],
  Checks.significant,
  .block (shapeP ++ ([Core.field .x1 .q, Core.field .x9 .qLen] : List Instr)),
  Checks.significant,
  .block (shapeQ ++ ([ldh .x2 22, .subImm .x .x6 .x2 128] : List Instr)),
  widthChoice]

theorem shapeSizes_ok {s : State} {B pp qp : Addr} {Z : Nat} {p q : List Byte}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64) :
    WP isa shapeSizes s fun t =>
      t.gpr .x3 = mask (decide (Spec.Dsa.supportedSizes
        (8 * (VG.Proof.Dsa.significant p).1) (8 * (VG.Proof.Dsa.significant q).1))) ∧
      word t.mem B Field.mask.offset = mask (decide (128 ≤ (VG.Proof.Dsa.significant q).2.toNat) &&
        decide (128 ≤ (VG.Proof.Dsa.significant p).2.toNat)) ∧
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (VG.Proof.Dsa.significant q).1 ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  have pbound := Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits p) hp64
  have qbound := Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits q) hq64
  unfold shapeSizes seqs
  refine WP.seq (WP.mono (WP.seq_iff.mp (scanField_ok hs hdi hZ .p .pLen hpp hpl hps hp1 hp64))
    fun u hu => WP.seq (WP.mono hu fun v ⟨hv8, hv9, hvm, hkv⟩ => ?_))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hvdi := (hkv.gpr .x0 (show Reg.x0 ∉ [Reg.x3, Reg.x8, Reg.x10, Reg.x1, Reg.x9] by decide)).trans hdi
  refine WP.mono (shapeP_context (hs.congr hkv.wr) hvdi hZ hv8 hv9)
    fun x ⟨hxp, hxm, hfx, hkx⟩ => ?_
  have hksx := hkv.trans hkx
  have hxdi := (hksx.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  have hxqp : word x.mem B Field.q.offset = qp :=
    (shape_field hfx .q (by decide) (by decide)).trans (by rw [hvm]; exact hqp)
  have hxql : word x.mem B Field.qLen.offset = BitVec.ofNat 64 q.length :=
    (shape_field hfx .qLen (by decide) (by decide)).trans (by rw [hvm]; exact hql)
  have hxqs := shape_source hfx hkx (Nat.le_trans (by decide) hZ)
    (hqs.congrK (by rw [hvm]; exact InScr.refl _ _ _) hkv)
  refine WP.mono (WP.seq_iff.mp (scanField_ok (hs.congr hksx.wr) hxdi hZ .q .qLen hxqp hxql hxqs hq1 hq64))
    fun y hy => WP.seq (WP.mono hy fun z ⟨hz8, hz9, hzm, hkz⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hksz := hksx.trans hkz
  have hzdi := (hksz.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  refine WP.mono (shapeQ_context (valid := decide (128 ≤ (VG.Proof.Dsa.significant p).2.toNat))
    (hs.congr hksz.wr) hzdi hZ hz8 hz9 (by rw [hzm]; exact hxm))
    fun a ⟨haq, ham, hap, hfa, hka⟩ => ?_
  have hksa := hksz.trans hka
  have hadi := (hksa.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  have haw : word a.mem B 176 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p).1 :=
    hap.trans (by rw [hzm]; exact hxp)
  refine WP.mono (readWidth_ok (hs.congr hksa.wr) hadi (Nat.le_trans (by decide) hZ) pbound haw)
    fun b ⟨hbz, hbd, hbm, hkb⟩ => ?_
  have hb8 := ((hka.trans hkb).gpr .x8 (show Reg.x8 ∉ _ by decide)).trans hz8
  refine WP.mono (widthChoice_ok pbound qbound hbd hb8 hbz) fun t ⟨ht, htm, hkt⟩ => ?_
  refine ⟨ht, by rw [htm, hbm]; exact ham, by rw [htm, hbm]; exact haq, ?_,
    ((hksa.trans hkb).trans hkt).mono (by decide)⟩
  rw [htm, hbm]
  have hfs : Frm B shapeRanges s.mem z.mem := by rw [hzm, ← hvm]; exact hfx
  exact hfs.trans hfa

end VG.Proof.Dsa.AArch64

end

end

/-! # Composition of domain masks, parity, and digest-prefix selection -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/ShapeFinish.lean`, which only this module imported.
section

/-! # Digest-prefix selection and the public domain-check result -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeFinish : List Instr :=
  [Core.field .x3 .digestLen, Core.field .x2 .digestPrefixLen,
    .subs .x .x4 .x2 .x3, .csel .x .x3 .x3 .x2,
    .str .x .x3 .x0 Field.digestPrefixLen.offset, Core.field .x3 .mask]

theorem shapeFinish_ok {s : State} {B : Addr} {Z n q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hn : n < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hp : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeFinish) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n q) ∧
      word t.mem B Field.mask.offset = mask valid ∧ (t.gpr .x3 == (0#64)) = !valid ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.x3, .x2, .x4] s t := by
  have hr : Field.mask.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hf : Field.digestPrefixLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hdw : Field.digestLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hw (v : BitVec 64) : word (s.mem.writeW (off B Field.digestPrefixLen.offset) v) B Field.mask.offset =
      word s.mem B Field.mask.offset :=
    (writeW_outside _ _ _ (by decide)).word (Or.inr (by decide)) (by decide)
  refine WP.mono (WP.keep [.x3, .x2, .x4] (Q := fun t =>
    t.mem = s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 (min n q)) ∧
    (t.gpr .x3 == (0#64)) = !valid) ?_ rfl rfl rfl) fun t ⟨⟨htm, htz⟩, hk⟩ => ?_
  · unfold shapeFinish
    have hcarry : decide (2 ^ 64 ≤ (BitVec.ofNat 64 q).toNat + (~~~BitVec.ofNat 64 n).toNat + 1) = decide (n ≤ q) := by
      simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hq]
      exact decide_eq_decide.mpr (by omega_using [hn])
    have hsel : (if decide (n ≤ q) then BitVec.ofNat 64 n else BitVec.ofNat 64 q) = BitVec.ofNat 64 (min n q) := by
      by_cases h : n ≤ q <;> simp [h, Nat.min_def]
    brun [Core.field, hdi, field_enc .digestLen, field_enc .digestPrefixLen, field_enc .mask,
      hs.ld hdw, hs.ld hf, hs.st hf, hs.ld hr, hd, hp, hcarry, hsel, hw, hm]
    simp only [Bool.toNat_true, hcarry, hsel]
    exact ⟨True.intro, by cases valid <;> rfl⟩
  · exact ⟨by rw [htm, word_writeW_self], by rw [htm, hw]; exact hm, htz,
      by rw [htm]; exact shape_store _ (Or.inr (Or.inl rfl)), hk⟩

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeTail : List Instr := Checks.accumulate ++ oddCheck ++ shapeFinish

theorem shapeTail_ok {s : State} {B pp qp : Addr} {Z n width : Nat} {p q : List Byte}
    {pLast qLast : Byte} {valid sizes : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64)
    (hplast : p[p.length - 1] = pLast) (hqlast : q[q.length - 1] = qLast)
    (hn : n < 2 ^ 64) (hw : width < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hwidth : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width)
    (ha : s.gpr .x3 = mask sizes) (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeTail) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n width) ∧
      word t.mem B Field.mask.offset = mask (decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && (sizes && valid)) ∧
      (t.gpr .x3 == (0#64)) = !(decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && (sizes && valid)) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  unfold shapeTail
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (accumulate_ok hs hdi hZ ha hm) fun u ⟨hum, hfu, hku⟩ => ?_
  have huf := shape_outside hfu (Or.inr (Or.inr rfl))
  have hups := shape_source huf hku (Nat.le_trans (by decide) hZ) hps
  have huqs := shape_source huf hku (Nat.le_trans (by decide) hZ) hqs
  have hudi := (hku.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  have hpidx : p.length - 1 < p.length := by omega_using [hp1]
  have hqidx : q.length - 1 < q.length := by omega_using [hq1]
  rw [WP.block_append_iff]
  refine WP.mono (oddCheck_ok (hs.congr hku.wr) hudi hZ
    ((shape_field huf .p (by decide) (by decide)).trans hpp)
    ((shape_field huf .q (by decide) (by decide)).trans hqp)
    ((shape_field huf .pLen (by decide) (by decide)).trans hpl)
    ((shape_field huf .qLen (by decide) (by decide)).trans hql)
    hp1 hp64 hq1 hq64 (hups.rd _ hpidx) (huqs.rd _ hqidx)
    ((hups.val _ hpidx).trans hplast) ((huqs.val _ hqidx).trans hqlast) hum)
    fun v ⟨hvm, hfv, hkv⟩ => ?_
  have hvf := shape_outside hfv (Or.inr (Or.inr rfl))
  have hksv := hku.trans hkv
  have hvdi := (hksv.gpr .x0 (show Reg.x0 ∉ _ by decide)).trans hdi
  have hvwidth : word v.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width :=
    (hfv.word (Or.inl (by decide)) (by decide)).trans
      ((hfu.word (Or.inl (by decide)) (by decide)).trans hwidth)
  refine WP.mono (shapeFinish_ok (hs.congr hksv.wr) hvdi hZ hn hw
    ((shape_field (huf.trans hvf) .digestLen (by decide) (by decide)).trans hd)
    hvwidth hvm) fun t ⟨htw, htm, htz, hft, hkt⟩ => ?_
  exact ⟨htw, htm, htz, (huf.trans hvf).trans hft, (hksv.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
