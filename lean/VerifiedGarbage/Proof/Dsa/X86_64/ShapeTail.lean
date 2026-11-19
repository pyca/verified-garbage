module

public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Dsa.X86_64.ScanField
public import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Impl.Dsa.X86_64.Checks
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Bignum.Words
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.TCB.X86_64.State
public import VerifiedGarbage.Impl.Dsa.X86_64.Core
import VerifiedGarbage.Proof.Dsa.Layout

/-! ### `Dsa.X86_64.OddCheck`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.LastByte`, which this module and modules that import it used -/

section

/-! # Reading the final encoded modulus byte for oddness validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem lastByte_ok {s : State} {B p : Addr} {Z n : Nat} {b : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (fp fl : Field) (r : Reg) (hp : word s.mem B fp.offset = p)
    (hl : word s.mem B fl.offset = BitVec.ofNat 64 n) (h1 : 1 ≤ n) (h64 : n < 2 ^ 64)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (n - 1)) 1)
    (hb : s.mem (p + BitVec.ofNat 64 (n - 1)) = b) :
    WP isa (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl)),
      .movzx8 r { base := .rsi, index := some .rcx, disp := -1 }]) s fun t =>
      t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem ∧ Keep [.rsi, .rcx, r] s t := by
  have he : p + BitVec.ofNat 64 n + BitVec.ofInt 64 (-1) = p + BitVec.ofNat 64 (n - 1) := by
    rw [BitVec.add_assoc, show BitVec.ofInt 64 (-1) = -(1#64) from rfl,
      ← BitVec.sub_eq_add_neg]
    exact congrArg (p + ·) (ofNat64_pred h1 h64)
  refine WP.mono (WP.keep [.rsi, .rcx, r] (Q := fun t =>
    t.gpr r = b.zeroExtend 64 ∧ t.mem = s.mem) ?_ ?_)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  · xrun [State.ea, Core.field, hdi, fieldAddress, hp, hl, show ∀ x : Addr, x * 1#64 = x from fun x => BitVec.mul_one x, he, hr, hb,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 hZ)]
  · cases r <;> rfl

end VG.Proof.Dsa.X86_64

end

end

/-! # Public oddness checks on the encoded DSA moduli -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Parity.lean`, which only this module imported.
section

/-! # The shared oddness mask for DSA moduli -/

section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64
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

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev oddCombine : List Instr := [.alu .and .rax (.reg .rdx), .alu .and .rax (.imm 1),
  .mov32 .rdx (.imm 0), .alu .sub .rdx (.reg .rax), .mov .rax (.reg .rdx)]

theorem oddCombine_ok {s : State} {p q : Byte}
    (ha : s.gpr .rax = p.zeroExtend 64) (hd : s.gpr .rdx = q.zeroExtend 64) :
    WP isa (.block oddCombine) s fun t =>
      t.gpr .rax = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rdx] s t := by
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.gpr .rax = mask (decide (p.toNat % 2 = 1 ∧ q.toNat % 2 = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold oddCombine
  xrun [ha, hd, show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from rfl]
  exact modulus_odd_mask p q

abbrev oddCheck : List Instr :=
  ([.mov .rsi (.mem (Core.field .p)), .mov .rcx (.mem (Core.field .pLen)),
    .movzx8 .rax { base := .rsi, index := some .rcx, disp := -1 }] : List Instr) ++
  ([.mov .rsi (.mem (Core.field .q)), .mov .rcx (.mem (Core.field .qLen)),
    .movzx8 .rdx { base := .rsi, index := some .rcx, disp := -1 }] : List Instr) ++
  oddCombine ++ Checks.accumulate

theorem oddCheck_ok {s : State} {B pp qp : Addr} {Z pl ql : Nat} {pLast qLast : Byte} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
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
      Outside B Field.mask.offset 8 s.mem t.mem ∧ Keep [.rax, .rdx, .rsi, .rcx] s t := by
  unfold oddCheck
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (lastByte_ok hs hdi hZ .p .pLen .rax hpp hpl hp1 hp64 hpr hpv)
    fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  have hudi := (hku.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  refine WP.mono (lastByte_ok (p := qp) (b := qLast) (hs.congr hku.2.2) hudi hZ .q .qLen .rdx
    (by rw [hum]; exact hqp) (by rw [hum]; exact hql) hq1 hq64
    (by rw [hku.2.1, hku.2.2]; exact hqr) (by rw [hum]; exact hqv))
    fun v ⟨hvd, hvm, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hva := (hkv.gpr (show Reg.rax ∉ _ by decide)).trans hua
  refine WP.mono (oddCombine_ok hva hvd) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hks := (hku.trans hkv).trans hkz
  have hzs := hs.congr hks.2.2
  have hzdi := (hks.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  refine WP.mono (accumulate_ok (b := valid) hzs hzdi hZ hza (by rw [hzm, hvm, hum]; exact hm))
    fun t ⟨ht, hf, hk⟩ => ?_
  exact ⟨ht, by rw [← hum, ← hvm, ← hzm]; exact hf, (hks.trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.ShapeSizes`, which the modules that import this one used -/

section

/-! ### `Dsa.X86_64.WidthChoice`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.WidthMask`, which only this module used -/

section

/-! # Equality masks for supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem widthMask_ok {s : State} {n value : Nat}
    (hn : n < 2 ^ 31) (hv : value < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 value) :
    WP isa (.block (Checks.widthMask n)) s fun t =>
      t.gpr .rax = mask (decide (value = n)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn64 : n < 2 ^ 64 := by omega_using [hn]
  have he : (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0 ↔ value = n := by
    change (BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n) = 0#64 ↔ value = n
    rw [BitVec.xor_eq_zero_iff]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hn64] using h'
    · intro h; rw [h]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = mask (decide (value = n)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨ht, hm⟩, hk⟩ => ⟨ht, hm, hk⟩
  unfold Checks.widthMask
  xrun [h8, sx_ofNat hn, show BitVec.signExtend 64 (1 : BitVec 32) = 1 from rfl]
  change mask (decide ((BitVec.ofNat 64 value ^^^ BitVec.ofNat 64 n).toNat < 1)) = _
  rw [mask_lt_one, decide_eq_decide.mpr he]

end VG.Proof.Dsa.X86_64

end

end


/-! # Public selection of supported DSA modulus widths -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem widthCompare_ok {s : State} {value n : Nat}
    (hv : value < 2 ^ 64) (hn : n < 2 ^ 31) (hd : s.gpr .rdx = BitVec.ofNat 64 value) :
    WP isa (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 n))]) s fun t =>
      t.zf = some (decide (value = n)) ∧ t.gpr .rdx = BitVec.ofNat 64 value ∧ t.mem = s.mem ∧ Keep [.rdx] s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.zf = some (decide (value = n)) ∧ t.gpr .rdx = BitVec.ofNat 64 value ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  xrun [hd, sx_ofNat hn, ofNat_sub_beq hv (show n < 2 ^ 64 by omega_using [hn])]

/-- Recover the saved p width and prepare the first public branch. -/
theorem readWidth_ok {s : State} {B : Addr} {Z p : Nat} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hZ : 184 ≤ Z) (hp : p < 2 ^ 64)
    (hw : word s.mem B 176 = BitVec.ofNat 64 p) :
    WP isa (.block [.mov .rdx (.mem (hdr 22)), .alu .cmp .rdx (.imm 128)]) s fun t =>
      t.zf = some (decide (p = 128)) ∧ t.gpr .rdx = BitVec.ofNat 64 p ∧ t.mem = s.mem ∧ Keep [.rdx] s t := by
  refine WP.mono (WP.keep [.rdx] (Q := fun t =>
    t.zf = some (decide (p = 128)) ∧ t.gpr .rdx = BitVec.ofNat 64 p ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, ht, hm⟩, hk⟩ => ⟨hz, ht, hm, hk⟩
  xrun [State.ea, hdr, hdi, hdrOff, hw, hs.ld hZ,
    show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 from rfl,
    ofNat_sub_beq hp (show 128 < 2 ^ 64 by decide)]

theorem mask_union (a b : Bool) : mask a ||| mask b = mask (a || b) := by
  cases a <;> cases b <;> decide

/-- The 2048-bit modulus supports both 224- and 256-bit subgroups. -/
theorem widthEither_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 q) :
    WP isa (.block (Checks.widthMask 28 ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 32 ++
      ([.alu .or .rax (.reg .r10)] : List Instr))) s fun t =>
      t.gpr .rax = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = s.mem ∧ Keep [.rax, .r10] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (widthMask_ok (by decide) hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun v => v.gpr .r10 = mask (decide (q = 28)) ∧ v.mem = u.mem)
    (by xrun [hua]) rfl) fun v ⟨⟨hv10, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr (show Reg.r8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hz10 := (hkz.gpr (show Reg.r10 ∉ [Reg.rax] by decide)).trans hv10
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = mask (decide (q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)), (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  xrun [hza, hz10, mask_union]
  rw [← Bool.decide_or]
  exact congrArg mask (decide_eq_decide.mpr or_comm)

/-- The legacy 160-bit subgroup extends the two FIPS 2048-bit cases. -/
theorem width2048_ok {s : State} {q : Nat} (hq : q < 2 ^ 64)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 q) :
    WP isa (.block Checks.width2048) s fun t =>
      t.gpr .rax = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧
      t.mem = s.mem ∧ Keep [.rax, .r10] s t := by
  unfold Checks.width2048
  rw [show Checks.widthMask 28 ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 32 ++
      ([.alu .or .rax (.reg .r10)] : List Instr) ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 20 ++
      ([.alu .or .rax (.reg .r10)] : List Instr) =
      (Checks.widthMask 28 ++ ([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 32 ++
        ([.alu .or .rax (.reg .r10)] : List Instr)) ++
      (([.mov .r10 (.reg .rax)] : List Instr) ++ Checks.widthMask 20 ++ ([.alu .or .rax (.reg .r10)] : List Instr)) by
        simp only [List.append_assoc]]
  rw [WP.block_append_iff]
  refine WP.mono (widthEither_ok hq h8) fun u ⟨hua, hum, hku⟩ => ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun v =>
    v.gpr .r10 = mask (decide (q = 28 ∨ q = 32)) ∧ v.mem = u.mem)
    (by xrun [hua]) rfl) fun v ⟨⟨hvs, hvm⟩, hkv⟩ => ?_
  rw [WP.block_append_iff]
  have hv8 := ((hku.trans hkv).gpr (show Reg.r8 ∉ _ by decide)).trans h8
  refine WP.mono (widthMask_ok (by decide) hq hv8) fun z ⟨hza, hzm, hkz⟩ => ?_
  have hzs := (hkz.gpr (show Reg.r10 ∉ [Reg.rax] by decide)).trans hvs
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.gpr .rax = mask (decide (q = 20 ∨ q = 28 ∨ q = 32)) ∧ t.mem = z.mem) ?_ rfl)
    fun t ⟨⟨ht, htm⟩, hkt⟩ =>
      ⟨ht, htm.trans (hzm.trans (hvm.trans hum)),
        (((hku.trans hkv).trans hkz).trans hkt).mono (by decide)⟩
  xrun [hza, hzs, mask_union, ← Bool.decide_or]

abbrev widthChoice : Prog isa :=
  .ite .e (.block (Checks.widthMask 20))
    (.seq (.block [.alu .cmp .rdx (.imm 256)])
      (.ite .e
        (.block Checks.width2048)
        (.seq (.block [.alu .cmp .rdx (.imm 384)])
          (.ite .e (.block (Checks.widthMask 32)) (.block [.mov32 .rax (.imm 0)])))))

/-- The supported-width switch returns exactly the spec's (L,N) predicate. -/
theorem widthChoice_ok {s : State} {p q : Nat} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : s.gpr .rdx = BitVec.ofNat 64 p) (h8 : s.gpr .r8 = BitVec.ofNat 64 q)
    (hz : s.zf = some (decide (p = 128))) :
    WP isa widthChoice s fun t =>
      t.gpr .rax = mask (decide (Spec.Dsa.supportedSizes (8 * p) (8 * q))) ∧
      t.mem = s.mem ∧ Keep [.rax, .rdx, .r10] s t := by
  unfold widthChoice
  by_cases h128 : p = 128
  · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
    · change VG.X86_64.eval .e s = some true
      simp only [VG.X86_64.eval, hz, h128, decide_true]
    · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 := by
        unfold Spec.Dsa.supportedSizes; omega_using [h128]
      rw [decide_eq_decide.mpr he]
      exact WP.mono (widthMask_ok (by decide) hq h8) fun t ⟨ht, hm, hk⟩ => ⟨ht, hm, hk.mono (by decide)⟩
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change VG.X86_64.eval .e s = some false
      simp only [VG.X86_64.eval, hz, h128, decide_false]
    · refine WP.seq (WP.mono (widthCompare_ok hp (show 256 < 2 ^ 31 by decide) hd)
        fun u ⟨huz, hud, hum, hku⟩ => ?_)
      have hu8 := (hku.gpr (show Reg.r8 ∉ [Reg.rdx] by decide)).trans h8
      by_cases h256 : p = 256
      · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
        · change VG.X86_64.eval .e u = some true
          simp only [VG.X86_64.eval, huz, h256, decide_true]
        · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 20 ∨ q = 28 ∨ q = 32 := by
            unfold Spec.Dsa.supportedSizes; omega_using [h256]
          rw [decide_eq_decide.mpr he]
          exact WP.mono (width2048_ok hq hu8) fun t ⟨ht, hm, hk⟩ =>
            ⟨ht, hm.trans hum, (hku.trans hk).mono (by decide)⟩
      · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
        · change VG.X86_64.eval .e u = some false
          simp only [VG.X86_64.eval, huz, h256, decide_false]
        · refine WP.seq (WP.mono (widthCompare_ok hp (show 384 < 2 ^ 31 by decide) hud)
            fun v ⟨hvz, _, hvm, hkv⟩ => ?_)
          have hv8 := (hkv.gpr (show Reg.r8 ∉ [Reg.rdx] by decide)).trans hu8
          by_cases h384 : p = 384
          · refine WP.ite true ?_ (fun _ => ?_) (fun h => Bool.noConfusion h)
            · change VG.X86_64.eval .e v = some true
              simp only [VG.X86_64.eval, hvz, h384, decide_true]
            · have he : Spec.Dsa.supportedSizes (8 * p) (8 * q) ↔ q = 32 := by
                unfold Spec.Dsa.supportedSizes; omega_using [h384]
              rw [decide_eq_decide.mpr he]
              exact WP.mono (widthMask_ok (by decide) hq hv8) fun t ⟨ht, hm, hk⟩ =>
                ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩
          · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
            · change VG.X86_64.eval .e v = some false
              simp only [VG.X86_64.eval, hvz, h384, decide_false]
            · have he : ¬ Spec.Dsa.supportedSizes (8 * p) (8 * q) := by
                unfold Spec.Dsa.supportedSizes; omega_using [h128, h256, h384]
              rw [decide_eq_false he]
              refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = mask false ∧ t.mem = v.mem)
                (by xrun) rfl) fun t ⟨⟨ht, hm⟩, hk⟩ =>
                  ⟨ht, hm.trans (hvm.trans hum), ((hku.trans hkv).trans hk).mono (by decide)⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # The two public width scans and supported-size selection -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev shapeSizes : Prog isa := seqs [
  .block [.mov .rsi (.mem (Core.field .p)), .mov .rcx (.mem (Core.field .pLen))],
  Checks.significant,
  .block (shapeP ++ ([.mov .rsi (.mem (Core.field .q)), .mov .rcx (.mem (Core.field .qLen))] : List Instr)),
  Checks.significant,
  .block (shapeQ ++ ([.mov .rdx (.mem (hdr 22)), .alu .cmp .rdx (.imm 128)] : List Instr)),
  widthChoice]

theorem shapeSizes_ok {s : State} {B pp qp : Addr} {Z : Nat} {p q : List Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64) :
    WP isa shapeSizes s fun t =>
      t.gpr .rax = mask (decide (Spec.Dsa.supportedSizes
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
  have hvdi := (hkv.gpr (show Reg.rdi ∉ [Reg.rax, Reg.r8, Reg.r9, Reg.rsi, Reg.rcx] by decide)).trans hdi
  refine WP.mono (shapeP_context (hs.congr hkv.2.2) hvdi hZ hv8 hv9)
    fun x ⟨hxp, hxm, hfx, hkx⟩ => ?_
  have hksx := hkv.trans hkx
  have hxdi := (hksx.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have hxqp : word x.mem B Field.q.offset = qp :=
    (shape_field hfx .q (by decide) (by decide)).trans (by rw [hvm]; exact hqp)
  have hxql : word x.mem B Field.qLen.offset = BitVec.ofNat 64 q.length :=
    (shape_field hfx .qLen (by decide) (by decide)).trans (by rw [hvm]; exact hql)
  have hxqs := shape_source hfx hkx (Nat.le_trans (by decide) hZ)
    (hqs.congrK (by rw [hvm]; exact InScr.refl _ _ _) hkv)
  refine WP.mono (WP.seq_iff.mp (scanField_ok (hs.congr hksx.2.2) hxdi hZ .q .qLen hxqp hxql hxqs hq1 hq64))
    fun y hy => WP.seq (WP.mono hy fun z ⟨hz8, hz9, hzm, hkz⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hksz := hksx.trans hkz
  have hzdi := (hksz.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  refine WP.mono (shapeQ_context (valid := decide (128 ≤ (VG.Proof.Dsa.significant p).2.toNat))
    (hs.congr hksz.2.2) hzdi hZ hz8 hz9 (by rw [hzm]; exact hxm))
    fun a ⟨haq, ham, hap, hfa, hka⟩ => ?_
  have hksa := hksz.trans hka
  have hadi := (hksa.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have haw : word a.mem B 176 = BitVec.ofNat 64 (VG.Proof.Dsa.significant p).1 :=
    hap.trans (by rw [hzm]; exact hxp)
  refine WP.mono (readWidth_ok (hs.congr hksa.2.2) hadi (Nat.le_trans (by decide) hZ) pbound haw)
    fun b ⟨hbz, hbd, hbm, hkb⟩ => ?_
  have hb8 := ((hka.trans hkb).gpr (show Reg.r8 ∉ _ by decide)).trans hz8
  refine WP.mono (widthChoice_ok pbound qbound hbd hb8 hbz) fun t ⟨ht, htm, hkt⟩ => ?_
  refine ⟨ht, by rw [htm, hbm]; exact ham, by rw [htm, hbm]; exact haq, ?_,
    ((hksa.trans hkb).trans hkt).mono (by decide)⟩
  rw [htm, hbm]
  have hfs : Frm B shapeRanges s.mem z.mem := by rw [hzm, ← hvm]; exact hfx
  exact hfs.trans hfa

end VG.Proof.Dsa.X86_64

end

end

/-! # Composition of domain masks, parity, and digest-prefix selection -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ShapeFinish.lean`, which only this module imported.
section

/-! # Digest-prefix selection and the public domain-check result -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev shapeFinish : List Instr :=
  [.mov .rax (.mem (Core.field .digestLen)), .mov .rdx (.mem (Core.field .digestPrefixLen)),
    .alu .cmp .rdx (.reg .rax), .cmov .b .rax (.reg .rdx),
    .store (Core.field .digestPrefixLen) .rax,
    .mov .rax (.mem (Core.field .mask)), .alu .test .rax (.reg .rax)]

theorem prefix_select {n q : Nat} (hn : n < 2 ^ 64) (hq : q < 2 ^ 64) :
    (if decide ((BitVec.ofNat 64 q).toNat < (BitVec.ofNat 64 n).toNat) then
      BitVec.ofNat 64 q else BitVec.ofNat 64 n) = BitVec.ofNat 64 (min n q) := by
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hq]
  split <;> rename_i h
  · rw [Nat.min_eq_right (Nat.le_of_lt (of_decide_eq_true h))]
  · rw [Nat.min_eq_left (Nat.le_of_not_gt (by simpa only [decide_eq_true_eq] using h))]

theorem mask_test (valid : Bool) : (mask valid &&& mask valid == 0#64) = !valid := by
  cases valid <;> decide

theorem shapeFinish_ok {s : State} {B : Addr} {Z n q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hn : n < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hp : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeFinish) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n q) ∧
      word t.mem B Field.mask.offset = mask valid ∧ t.zf = some (!valid) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  have hr : Field.mask.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hf : Field.digestPrefixLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hdw : Field.digestLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hw (v : BitVec 64) : word (s.mem.writeW (off B Field.digestPrefixLen.offset) v) B Field.mask.offset =
      word s.mem B Field.mask.offset :=
    (writeW_outside _ _ _ (by decide)).word (Or.inr (by decide)) (by decide)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.mem = s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 (min n q)) ∧
    t.zf = some (!valid)) ?_ rfl) fun t ⟨⟨htm, htz⟩, hk⟩ => ?_
  · unfold shapeFinish
    by_cases hlt : q < n
    all_goals xrun [execCmov, eval, hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hq,
      State.ea, Core.field, hdi, fieldAddress, hs.ld hdw, hs.ld hf, hs.st hf, hs.ld hr,
      hd, hp, prefix_select hn hq, hw, hm, mask_test]
    · rw [Nat.min_eq_right (Nat.le_of_lt hlt)]
      exact ⟨rfl, mask_test valid⟩
    · rw [Nat.min_eq_left (Nat.le_of_not_gt hlt)]
      exact ⟨rfl, mask_test valid⟩
  · exact ⟨by rw [htm, word_writeW_self], by rw [htm, hw]; exact hm, htz,
      by rw [htm]; exact shape_store _ (Or.inr (Or.inl rfl)), hk⟩

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev shapeTail : List Instr := Checks.accumulate ++ oddCheck ++ shapeFinish

theorem shapeTail_ok {s : State} {B pp qp : Addr} {Z n width : Nat} {p q : List Byte}
    {pLast qLast : Byte} {valid sizes : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64)
    (hplast : p[p.length - 1] = pLast) (hqlast : q[q.length - 1] = qLast)
    (hn : n < 2 ^ 64) (hw : width < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hwidth : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width)
    (ha : s.gpr .rax = mask sizes) (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeTail) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n width) ∧
      word t.mem B Field.mask.offset = mask (decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && (sizes && valid)) ∧
      t.zf = some (!(decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && (sizes && valid))) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  unfold shapeTail
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (accumulate_ok hs hdi hZ ha hm) fun u ⟨hum, hfu, hku⟩ => ?_
  have huf := shape_outside hfu (Or.inr (Or.inr rfl))
  have hups := shape_source huf hku (Nat.le_trans (by decide) hZ) hps
  have huqs := shape_source huf hku (Nat.le_trans (by decide) hZ) hqs
  have hudi := (hku.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have hpidx : p.length - 1 < p.length := by omega_using [hp1]
  have hqidx : q.length - 1 < q.length := by omega_using [hq1]
  rw [WP.block_append_iff]
  refine WP.mono (oddCheck_ok (hs.congr hku.2.2) hudi hZ
    ((shape_field huf .p (by decide) (by decide)).trans hpp)
    ((shape_field huf .q (by decide) (by decide)).trans hqp)
    ((shape_field huf .pLen (by decide) (by decide)).trans hpl)
    ((shape_field huf .qLen (by decide) (by decide)).trans hql)
    hp1 hp64 hq1 hq64 (hups.rd _ hpidx) (huqs.rd _ hqidx)
    ((hups.val _ hpidx).trans hplast) ((huqs.val _ hqidx).trans hqlast) hum)
    fun v ⟨hvm, hfv, hkv⟩ => ?_
  have hvf := shape_outside hfv (Or.inr (Or.inr rfl))
  have hksv := hku.trans hkv
  have hvdi := (hksv.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have hvwidth : word v.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width :=
    (hfv.word (Or.inl (by decide)) (by decide)).trans
      ((hfu.word (Or.inl (by decide)) (by decide)).trans hwidth)
  refine WP.mono (shapeFinish_ok (hs.congr hksv.2.2) hvdi hZ hn hw
    ((shape_field (huf.trans hvf) .digestLen (by decide) (by decide)).trans hd)
    hvwidth hvm) fun t ⟨htw, htm, htz, hft, hkt⟩ => ?_
  exact ⟨htw, htm, htz, (huf.trans hvf).trans hft, (hksv.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
