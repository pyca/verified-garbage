module

public import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyLit
meta import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeLoop
public import VerifiedGarbage.Proof.X448.Arm.Save
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyChecks
public import VerifiedGarbage.Proof.Ed25519.SlidingDigits
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
public import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.Arm.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Arm.BitWrite
import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
import VerifiedGarbage.Proof.X448.Arm.Initial
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeLoop
meta import VerifiedGarbage.Proof.X448.Arm.Save
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyChecks
meta import VerifiedGarbage.Proof.Ed25519.SlidingDigits
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
meta import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.X448.Arm.Mem
meta import VerifiedGarbage.Spec.Ed448.Contract
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.X448.Arm.BitWrite
meta import VerifiedGarbage.Proof.X448.Arm.Iter
meta import VerifiedGarbage.Proof.X448.Arm.Carry
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.X448.Arm.Counters
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
meta import VerifiedGarbage.Proof.X448.Arm.Finish
meta import VerifiedGarbage.Proof.Ed448.Arm.BaseStep
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
meta import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
meta import VerifiedGarbage.Proof.X448.Arm.Initial

/-! ### `Ed448.Arm.VerifyMain`, which only this module used -/

section

/-! ### `Ed448.Arm.VerifyLoop`, which only this module used -/

section

/-! ### `Ed448.Arm.VerifyBits`, which only this module used -/

section

/-!
# Ed448 verification's equation on ARMv7: the bits of `S` and `k`

`vbits_ok`: byte `t` at `VBITS` is bit `t` of `S` (the signature's last 57
bytes) plus twice bit `t` of `k` (the challenge), for `t < 456`.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Spec.Ed448 (bytesAt decodeLE)
open VG.Proof.X25519.Arm (wp_mov wp_dp wp_ldrb wp_strb wp_cmp op2_imm op2_reg op2_lsl)

variable {fv : Bool}

/-- Bits `t` of two numbers in one byte. -/
def pair2 (a b t : Nat) : Nat := ((a >>> t) &&& 1) + 2 * ((b >>> t) &&& 1)

theorem shift_eval (s : State) (r : Reg) {j : Nat} (hj : j < 8) :
    Op2.eval s (if j = 0 then .reg r else .shifted r .lsr j) = some (s.gpr r >>> j) := by
  by_cases hz : j = 0
  · subst j; simp only [ite_true, Op2.eval, BitVec.ushiftRight_zero]
  · rw [ite_eq_right hz]
    exact VG.Proof.X25519.Arm.op2_lsr (by omega_using [hj, hz])

theorem pack_bits (a b : BitVec 8) (j : Nat) :
    (((a.setWidth 32 >>> j) &&& 1) + (((b.setWidth 32 >>> j) &&& 1) <<< 1)).setWidth 8 =
      BitVec.ofNat 8 (pair2 a.toNat b.toNat j) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (a.toNat >>> j) &&& 1 ≤ 1 := Nat.and_le_right
  have h2 : (b.toNat >>> j) &&& 1 ≤ 1 := Nat.and_le_right
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, pair2]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega_using []), Nat.mod_eq_of_lt (a := b.toNat) (by omega_using [])]
  change ((a.toNat >>> j &&& 1) + ((b.toNat >>> j &&& 1) * 2 ^ 1) % 2 ^ 32) % 2 ^ 32 % 2 ^ 8 = _
  omega_using []

theorem vbitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {a b : BitVec 8} (ha : s.gpr .r3 = a.setWidth 32) (hb : s.gpr .r9 = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (vbitJ j)) s fun t =>
      t.mem = s.mem.writeW (off base (VBITS + (8 * i + j))) (BitVec.ofNat 8 (pair2 a.toNat b.toNat j)) ∧
        Keeps [.r1, .r4] s t := by
  unfold vbitJ
  refine wp_mov (shift_eval s .r3 hj) fun t1 v1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 v2 => ?_
  refine wp_mov (shift_eval t2 .r9 hj) fun t3 v3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 v4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t5 v5 => ?_
  obtain r7 : t5.gpr .r7 = s.gpr .r7 := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide),
      v1.other _ (by decide)]
  obtain ea : State.addr (t5.gpr .r7 + BitVec.ofNat 32 (VBITS + j)) = off base (VBITS + (8 * i + j)) := by
    rw [r7, hp, BitVec.add_assoc, ← BitVec.ofNat_add, hs.ea (by simp only [VBITS]; omega_using [hi, hj])]
    congr 1; omega_using []
  refine wp_strb (by simp only [VBITS]; omega_using [hj]) ea
    (by rw [v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hs.write (by simp only [VBITS]; omega_using [hi, hj]))
    fun t6 v6 => WP.block_nil ⟨?_, ?_⟩
  · rw [v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem, v5.gpr]
    change s.mem.writeW _ ((t4.gpr .r1 + t4.gpr .r4 <<< 1).setWidth 8) = _
    rw [v4.other _ (by decide), v3.other _ (by decide), v2.gpr, v4.gpr]
    change s.mem.writeW _ (((t1.gpr .r1 &&& 1) + (t3.gpr .r4 &&& 1) <<< 1).setWidth 8) = _
    rw [v3.gpr, v1.gpr, v2.other _ (by decide), v1.other _ (by decide), ha, hb, pack_bits]
  · exact rest_keeps ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest _))))))

theorem vbyteBits_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {a b : BitVec 8} (ha : s.gpr .r3 = a.setWidth 32) (hb : s.gpr .r9 = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap vbitJ)) s fun t =>
      (∀ j < 8, t.mem (off base (VBITS + (8 * i + j))) = BitVec.ofNat 8 (pair2 a.toNat b.toNat j)) ∧
      Outside base (VBITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r1, .r4] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (VBITS + (8 * i + j))) = BitVec.ofNat 8 (pair2 a.toNat b.toNat j)) ∧
    Outside base (VBITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r1, .r4] s t
  obtain step : ∀ n t, n < 8 → inv n t → WP isa (.block (vbitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (vbitJ_ok (hs.of_keeps tk (by decide)) hi
      (by rw [tk.1 .r7 (by decide), tk.1 .r0 (by decide)]; exact hp)
      ((tk.1 _ (by decide)).trans ha) ((tk.1 _ (by decide)).trans hb) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      obtain eq : off base (VBITS + (8 * i + j)) = off base (VBITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [VBITS]; omega_using [hi, hn, hj]) (by simp only [VBITS]; omega_using [hi, hn])]
        omega_using []
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega_using [hj, he])
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [VBITS]; omega_using [hi, hn]) (by omega_using [hn, hx])
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

def vbitHead : List Instr :=
  [.dp .add .r7 .r12 (.reg .r11), .ldrb .r3 .r7 57, .dp .add .r7 .r2 (.reg .r11), .ldrb .r9 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)]

def vbitRegs : List Reg := [.r3, .r1, .r4, .r9, .r11, .r7]

theorem vbitHead_ok {s : State} {sq kq : Addr} (hsq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = sq)
    (hkq : State.addr (s.gpr .r2) = kq)
    (hfs : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32) (hfk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hsr : InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 i) 1)
    (hkr : InRegions (s.rd ++ s.wr) (kq + BitVec.ofNat 64 i) 1) :
    WP isa (.block vbitHead) s fun t =>
      t.gpr .r3 = (s.mem (sq + BitVec.ofNat 64 i)).setWidth 32 ∧
      t.gpr .r9 = (s.mem (kq + BitVec.ofNat 64 i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r9, .r7] s t := by
  unfold vbitHead
  refine wp_dp (op2_reg _ _) fun t1 v1 => ?_
  obtain ea1 : State.addr (t1.gpr .r7 + BitVec.ofNat 32 57) = sq + BitVec.ofNat 64 i := by
    rw [v1.gpr]; change State.addr (s.gpr .r12 + s.gpr .r11 + BitVec.ofNat 32 57) = _
    rw [hb, Offset.add_add, addr_add (by omega_using [hfs, hi]), ← hsq, Offset.add_add, Nat.add_comm]
  refine wp_ldrb (by decide) ea1 (by rw [v1.rd, v1.wr]; exact hsr) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => ?_
  obtain ea3 : State.addr (t3.gpr .r7 + BitVec.ofNat 32 0) = kq + BitVec.ofNat 64 i := by
    rw [v3.gpr]; change State.addr (t2.gpr .r2 + t2.gpr .r11 + BitVec.ofNat 32 0) = _
    rw [v2.other _ (by decide), v1.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide),
      BitVec.add_zero, hb, addr_add (by omega_using [hfk, hi]), hkq]
  refine wp_ldrb (by decide) ea3 (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hkr)
    fun t4 v4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t5 v5 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.gpr, v1.mem]
  · rw [v5.other _ (by decide), v4.gpr, v3.mem, v2.mem, v1.mem]
  · rw [v5.gpr, v5.other .r0 (by decide)]
    change t4.gpr .r0 + t4.gpr .r11 <<< 3 = _
    rw [v4.other .r11 (by decide), v3.other .r11 (by decide), v2.other .r11 (by decide),
      v1.other .r11 (by decide), hb]
    apply congrArg (t4.gpr .r0 + ·)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega_using []
  · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · exact rest_keeps ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide))))))

theorem vbitsBody_ok {s : State} {base sq kq : Addr} (hs : Scr s base)
    (hsq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = sq) (hkq : State.addr (s.gpr .r2) = kq)
    (hfs : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32) (hfk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hsr : InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 i) 1)
    (hkr : InRegions (s.rd ++ s.wr) (kq + BitVec.ofNat 64 i) 1) :
    WP isa (.block vbitsBody) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧ Keeps vbitRegs s t ∧
      (∀ j < 8, t.mem (off base (VBITS + (8 * i + j))) =
        BitVec.ofNat 8 (pair2 (s.mem (sq + BitVec.ofNat 64 i)).toNat (s.mem (kq + BitVec.ofNat 64 i)).toNat j)) ∧
      Outside base (VBITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (vbitHead ++ (List.range 8).flatMap vbitJ ++ baseBitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (vbitHead_ok hsq hkq hfs hfk hi hb hsr hkr) fun t ⟨ta, tb, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (vbyteBits_ok (hs.of_keeps tk (by decide)) hi tp ta tb) fun u ⟨uf, um, uk⟩ => ?_
  obtain ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (baseBitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_)) <;> decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The bits loop's invariant, after `i` bytes. -/
structure VBitsInv (base sq kq : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  esq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = sq
  ekq : State.addr (s.gpr .r2) = kq
  fs : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32
  fk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  gpr : ∀ r, r ∉ vbitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base VBITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (VBITS + t)) =
    BitVec.ofNat 8 (pair2 (s₀.mem (sq + BitVec.ofNat 64 (t / 8))).toNat
      (s₀.mem (kq + BitVec.ofNat 64 (t / 8))).toNat (t % 8))

theorem vbitsLoop_ok {s₀ : State} {base sq kq : Addr}
    (hsr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (sq + BitVec.ofNat 64 q) 1)
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (kq + BitVec.ofNat 64 q) 1)
    (hsd : ∀ q < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 q))
    (hkd : ∀ q < 57, 8192 ≤ ofs base (kq + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → VBitsInv base sq kq s₀ s i →
      WP isa (.loop (.block vbitsBody) .ne) s fun s' => VBitsInv base sq kq s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block vbitsBody) (c := .ne)
    (Q := fun s' => VBitsInv base sq kq s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ VBitsInv base sq kq s₀ s i) ?_ (57 - i) s
    ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (vbitsBody_ok hb.scr hb.esq hb.ekq hb.fs hb.fk hi hb.r11
    (by rw [hb.rd, hb.wr]; exact hsr i hi) (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  obtain hbs : s.mem (sq + BitVec.ofNat 64 i) = s₀.mem (sq + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hsd i hi; simp only [VBITS]; omega_using [this])
  obtain hbk : s.mem (kq + BitVec.ofNat 64 i) = s₀.mem (kq + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [VBITS]; omega_using [this])
  obtain inv : VBitsInv base sq kq s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.esq), (by rw [g' _ (by decide)]; exact hb.ekq),
      (by rw [g' _ (by decide)]; exact hb.fs), (by rw [g' _ (by decide)]; exact hb.fk), b',
      fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega_using []) (by omega_using [hi])),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [VBITS]; omega_using [hi, ht])]; omega_using [h]), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega_using [ht])
      rw [show 8 * i + (t - 8 * i) = t by omega_using [h], hbs, hbk] at e
      rw [e, show t / 8 = i by omega_using [ht, h], show t % 8 = t - 8 * i by omega_using [ht, h]]
  simp only [eval, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega_using [h] : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega_using [hi], i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega_using [hi, h]
    exact .inl ⟨rfl, inv⟩

/-- `vbits`: byte `t` of `VBITS` is bit `t` of `S` plus twice bit `t` of `k`, for `t < 456`. -/
theorem vbits_ok {s : State} {base sq kq : Addr} (hs : Scr s base)
    (hsq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = sq) (hkq : State.addr (s.gpr .r2) = kq)
    (hfs : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32) (hfk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32)
    (hsr : ∀ q < 57, InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 q) 1)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (kq + BitVec.ofNat 64 q) 1)
    (hsd : ∀ q < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 q))
    (hkd : ∀ q < 57, 8192 ≤ ofs base (kq + BitVec.ofNat 64 q)) :
    WP isa vbits s fun s' =>
      (∀ r, r ∉ vbitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base VBITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (VBITS + t)) =
        BitVec.ofNat 8 (pair2 (decodeLE (bytesAt s.mem sq 57)) (decodeLE (bytesAt s.mem kq 57)) t) := by
  unfold vbits
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => VBitsInv base sq kq s s' 0) by
    refine wp_mov (op2_imm (by decide)) fun t ht => WP.block_nil ?_
    obtain keep : Keeps vbitRegs s t := rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r12 (by decide)]; exact hsq,
      by rw [ht.other .r2 (by decide)]; exact hkq, by rw [ht.other .r12 (by decide)]; exact hfs,
      by rw [ht.other .r2 (by decide)]; exact hfk, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.mono (vbitsLoop_ok hsr hkr hsd hkd 0 s₁ (by omega_using []) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega_using [ht])]
  unfold pair2
  rw [scalar_bit _ _ ht, scalar_bit _ _ ht]

end VG.Proof.Ed448.Arm

end

end


/-!
# Ed448 verification's equation on ARMv7: `k`'s digits

`vrecode_ok`: `vrecode` leaves byte `t` at `VBITS` as bit `t` of `S` plus twice digit `t` of `k`
(`pairD`), for the digits of `Proof/Ed25519/SlidingDigits.lean` over 456 bits (`vdigits`). One
bit (`recBit_ok`) keeps `RecAt`: the registers hold that recoding's state after the bits read
(`Slide.run`), the bytes below them are those of its digits, and the bytes from there on are
still those of `vbits`.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (vdigits)
open VG.Proof.X25519.Arm (wp_mov wp_dp wp_ldrb wp_strb wp_cmp op2_imm op2_reg op2_lsl op2_lsr dpVal Rest)

/-- Bit `q` of `k`. -/
def kbit (K q : Nat) : Nat := (K >>> q) &&& 1

/-- The byte of bit `t` of `S` and of the digit `D t`: `pair2 S K t` for the bits of `K`
(`kbit K`). -/
def pairD (S : Nat) (D : Nat → Nat) (t : Nat) : Nat := ((S >>> t) &&& 1) + 2 * D t

theorem kbit_eq (K q : Nat) : kbit K q = Proof.Ed25519.Slide.bit K q := by
  simp only [kbit, Proof.Ed25519.Slide.bit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

/-- The byte of a bit of `S` and a bit of `k`, loaded: the weight of a window it opens, the byte
of the bit of `S` alone, and the bit of `k`. -/
private theorem rec_byte_fact : ∀ a < 2, ∀ b < 2,
    (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 = BitVec.ofNat 32 (a + 2 * b) ∧
    (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 &&& (2 : BitVec 32) = BitVec.ofNat 32 (2 * b) ∧
    ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 &&& (1 : BitVec 32)).setWidth 8 = BitVec.ofNat 8 a ∧
    (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 >>> 1 = BitVec.ofNat 32 b := by decide

/-- A bit of `k` at the weight `m`, twice; the next weight; and the test of no window. -/
private theorem rec_grow_fact : ∀ b < 2, ∀ m < 16,
    (BitVec.ofNat 32 m &&& ~~~(BitVec.ofNat 32 b - 1)) <<< 1 = BitVec.ofNat 32 (2 * (m * b)) ∧
    (BitVec.ofNat 32 m <<< 1) &&& (15 : BitVec 32) = BitVec.ofNat 32 (2 * m % 16) ∧
    (BitVec.ofNat 32 m - (0 : BitVec 32) == 0) = decide (m = 0) := by decide

/-- The count of bits read, moved up, against 456. -/
private theorem rec_next_fact : ∀ n < 456,
    ((BitVec.ofNat 32 n + (1 : BitVec 32) - (456 : BitVec 32)) == 0) = decide (n + 1 = 456) := by
  decide +kernel

theorem ofNat32_setWidth8 (x : Nat) : (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- The registers the recoding changes. -/
abbrev recRegs : List Reg := [.r1, .r2, .r3, .r5, .r7, .r8, .r11]

/-- After bit `i` of `K`: the recoding's state (`Slide.run`) in `r11`, `r8`, `r5` and, with a
window in hand, `r7`; the bytes below `i` those of the digits of the bits read, and the bytes from
`i` on still those of the bits. -/
structure RecAt (base : Addr) (S K i : Nat) (s : State) : Prop where
  scr : Scr s base
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  r8 : s.gpr .r8 = BitVec.ofNat 32 (Proof.Ed25519.Slide.run K i).m
  r5 : s.gpr .r5 = s.gpr .r0 + BitVec.ofNat 32 (Proof.Ed25519.Slide.run K i).p
  r7 : (Proof.Ed25519.Slide.run K i).m ≠ 0 → s.gpr .r7 =
    BitVec.ofNat 32 (pairD S (Proof.Ed25519.Slide.run K i).u (Proof.Ed25519.Slide.run K i).p)
  dig : ∀ q < i, s.mem (off base (VBITS + q)) = BitVec.ofNat 8 (pairD S (Proof.Ed25519.Slide.run K i).u q)
  rest : ∀ q, i ≤ q → q < 456 → s.mem (off base (VBITS + q)) = BitVec.ofNat 8 (pair2 S K q)

/-- The address of a byte at `VBITS`, from its position's. -/
theorem vbyte_ea {s : State} {base : Addr} (hs : Scr s base) {r : Reg} {q : Nat} (hq : q < 456)
    (hr : s.gpr r = s.gpr .r0 + BitVec.ofNat 32 q) :
    State.addr (s.gpr r + BitVec.ofNat 32 VBITS) = off base (VBITS + q) := by
  rw [hr, Offset.add_add, Nat.add_comm q VBITS]
  exact hs.ea (by simp only [VBITS]; omega_using [hq])

theorem recOpen_ok (s : State) {a b : Nat} (ha : a < 2) (hb : b < 2)
    (h1 : s.gpr .r1 = (BitVec.ofNat 8 (a + 2 * b)).setWidth 32) :
    WP isa (.block recOpen) s fun t => Rest [.r5, .r7, .r8] s t ∧ t.mem = s.mem ∧
      t.gpr .r8 = BitVec.ofNat 32 (2 * b) ∧ t.gpr .r7 = BitVec.ofNat 32 (a + 2 * b) ∧
      t.gpr .r5 = s.gpr .r3 := by
  obtain bf := rec_byte_fact a ha b hb
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun t ut => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (ut.rest (by decide)))
  · rw [ut.mem, u₂.mem, u₁.mem]
  · rw [ut.other _ (by decide), u₂.gpr, dpVal, u₁.other _ (by decide), h1]
    exact bf.2.1
  · rw [ut.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h1]
    exact bf.1
  · rw [ut.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]

theorem recGrow_ok {s : State} {base : Addr} (hs : Scr s base) {i p a b m B : Nat} (hi : i < 456)
    (hp : p < 456) (ha : a < 2) (hb : b < 2) (hm : m < 16)
    (h3 : s.gpr .r3 = s.gpr .r0 + BitVec.ofNat 32 i)
    (h1 : s.gpr .r1 = (BitVec.ofNat 8 (a + 2 * b)).setWidth 32)
    (h5 : s.gpr .r5 = s.gpr .r0 + BitVec.ofNat 32 p) (h7 : s.gpr .r7 = BitVec.ofNat 32 B)
    (h8 : s.gpr .r8 = BitVec.ofNat 32 m) :
    WP isa (.block recGrow) s fun t => Rest [.r2, .r7, .r8] s t ∧
      t.mem = (s.mem.writeW (off base (VBITS + i)) (BitVec.ofNat 8 a)).writeW
        (off base (VBITS + p)) (BitVec.ofNat 8 (B + 2 * (m * b))) ∧
      t.gpr .r8 = BitVec.ofNat 32 (2 * m % 16) ∧ t.gpr .r7 = BitVec.ofNat 32 (B + 2 * (m * b)) := by
  obtain bf := rec_byte_fact a ha b hb
  obtain gf := rec_grow_fact b hb m hm
  refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => ?_
  obtain hs₁ := hs.of_upd u₁ (by decide) (by decide)
  refine wp_strb (by decide) (vbyte_ea hs₁ hi (by rw [u₁.other _ (by decide), u₁.other _ (by decide), h3]))
    (hs₁.write (by simp only [VBITS]; omega_using [hi])) fun s₂ u₂ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_dp (op2_imm (by decide)) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => wp_dp (op2_lsl (by decide)) fun s₆ u₆ => ?_
  obtain r6 : Rest [.r2, .r7, .r8] s s₆ :=
    (u₁.rest (by decide)).trans ((u₂.rest _).trans ((u₃.rest (by decide)).trans ((u₄.rest (by decide)).trans
      ((u₅.rest (by decide)).trans (u₆.rest (by decide))))))
  obtain hs₆ : Scr s₆ base := hs.of_keeps (rest_keeps r6) (by decide)
  obtain g7 : s₆.gpr .r7 = BitVec.ofNat 32 (B + 2 * (m * b)) := by
    rw [u₆.gpr, dpVal, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h7, u₅.gpr, dpVal, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h8, u₄.gpr, dpVal, u₃.gpr, u₂.gpr, u₁.other _ (by decide), h1, bf.2.2.2, gf.1,
      ← BitVec.ofNat_add]
  obtain g8 : s₆.gpr .r8 = BitVec.ofNat 32 m := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h8]
  obtain g5 : s₆.gpr .r5 = s₆.gpr .r0 + BitVec.ofNat 32 p := by
    rw [r6.gpr _ (by decide), r6.gpr _ (by decide), h5]
  refine wp_strb (by decide) (vbyte_ea hs₆ hp g5) (hs₆.write (by simp only [VBITS]; omega_using [hp]))
    fun s₇ u₇ => wp_mov (op2_lsl (by decide)) fun s₈ u₈ => wp_dp (op2_imm (by decide)) fun t ut =>
      WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact r6.trans ((u₇.rest _).trans ((u₈.rest (by decide)).trans (ut.rest (by decide))))
  · rw [ut.mem, u₈.mem, u₇.mem, g7, ofNat32_setWidth8, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.gpr, dpVal,
      u₁.mem, h1, bf.2.2.1]
  · rw [ut.gpr, dpVal, u₈.gpr, u₇.gpr, g8]
    exact gf.2.1
  · rw [ut.other _ (by decide), u₈.other _ (by decide), u₇.gpr, g7]

/-- One bit. -/
theorem recBit_ok {base : Addr} {S K i : Nat} {s : State} (h : RecAt base S K i s) (hi : i < 456) :
    WP isa recBit s fun u => Keeps recRegs s u ∧ Outside base VBITS 456 s.mem u.mem ∧
      RecAt base S K (i + 1) u ∧ u.z = decide (i + 1 = 456) := by
  have hB : VBITS = 3104 := rfl
  obtain G := Proof.Ed25519.Slide.run_good K i
  obtain Si := Proof.Ed25519.Slide.run_i K i
  obtain hS := Proof.Ed25519.Slide.run_succ K i
  obtain ⟨hs, h11, h8, h5, h7, hdig, hrest⟩ := h
  generalize Proof.Ed25519.Slide.run K i = T at G Si hS h8 h5 h7 hdig
  obtain hbyte : s.mem (off base (VBITS + i)) = BitVec.ofNat 8 (pairD S (kbit K) i) :=
    hrest i (Nat.le_refl _) hi
  obtain hbit : Proof.Ed25519.Slide.bit K i = kbit K i := (kbit_eq K i).symm
  obtain hb : kbit K i < 2 := bit_lt K i
  obtain ⟨a, ea⟩ : ∃ a, (S >>> i) &&& 1 = a := ⟨_, rfl⟩
  obtain ha : a < 2 := ea ▸ bit_lt S i
  obtain hpd : ∀ D : Nat → Nat, pairD S D i = a + 2 * D i := fun D => by rw [pairD, ea]
  rw [hpd] at hbyte
  generalize kbit K i = b at hbyte hbit hb
  obtain bf := rec_byte_fact a ha b hb
  obtain hm16 : T.m < 16 := by rcases G.m_cases with e | e | e | e <;> rw [e] <;> decide
  rw [recBit]
  -- The byte, and the test of a window in hand.
  refine WP.seq (wp_dp (op2_reg _ _) fun s₁ u₁ => ?_)
  obtain g3₁ : s₁.gpr .r3 = s₁.gpr .r0 + BitVec.ofNat 32 i := by
    rw [u₁.gpr, dpVal, u₁.other _ (by decide), h11]
  obtain hs₁ := hs.of_upd u₁ (by decide) (by decide)
  refine wp_ldrb (by decide) (vbyte_ea hs₁ hi g3₁) (hs₁.read (by omega_arith)) fun s₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_
  obtain r3 : Rest [.r1, .r3] s s₃ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (f₃.rest _))
  obtain m3 : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  obtain hs₃ : Scr s₃ base := hs.of_keeps (rest_keeps r3) (by decide)
  obtain g3 : s₃.gpr .r3 = s₃.gpr .r0 + BitVec.ofNat 32 i := by
    rw [f₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), g3₁]
  obtain g1 : s₃.gpr .r1 = (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 := by
    rw [f₃.gpr, u₂.gpr, u₁.mem, hbyte]
  obtain g5 : s₃.gpr .r5 = s₃.gpr .r0 + BitVec.ofNat 32 T.p := by
    rw [r3.gpr _ (by decide), r3.gpr _ (by decide), h5]
  obtain g8 : s₃.gpr .r8 = BitVec.ofNat 32 T.m := (r3.gpr _ (by decide)).trans h8
  obtain hz : isa.eval .eq s₃ = some (decide (T.m = 0)) := by
    rw [VG.Proof.X25519.Arm.eval_eq, z₃, u₂.other _ (by decide), u₁.other _ (by decide), h8]
    exact congrArg some (rec_grow_fact 0 (by decide) T.m hm16).2.2
  have mid : WP isa (.ite .eq (.block recOpen) (.block recGrow)) s₃ fun x =>
      Rest [.r2, .r5, .r7, .r8] s₃ x ∧ Outside base VBITS 456 s₃.mem x.mem ∧
      x.gpr .r8 = BitVec.ofNat 32 (Proof.Ed25519.Slide.step K T).m ∧
      x.gpr .r5 = x.gpr .r0 + BitVec.ofNat 32 (Proof.Ed25519.Slide.step K T).p ∧
      x.gpr .r7 = BitVec.ofNat 32
        (pairD S (Proof.Ed25519.Slide.step K T).u (Proof.Ed25519.Slide.step K T).p) ∧
      (∀ q < i + 1, x.mem (off base (VBITS + q)) =
        BitVec.ofNat 8 (pairD S (Proof.Ed25519.Slide.step K T).u q)) ∧
      ∀ q, i + 1 ≤ q → q < 456 → x.mem (off base (VBITS + q)) = s₃.mem (off base (VBITS + q)) := by
    apply WP.ite (decide (T.m = 0)) hz
    · intro h0
      obtain h0 : T.m = 0 := of_decide_eq_true h0
      obtain ⟨em, ew, ep, eu⟩ := Proof.Ed25519.Slide.step_idle (K := K) h0
      rw [Si, hbit] at em ew eu
      rw [Si] at ep
      refine WP.mono (recOpen_ok s₃ ha hb g1) fun x ⟨rx, mx, x8, x7, x5⟩ => ?_
      refine ⟨rx.mono (by decide), by rw [mx]; exact Outside.refl _ _ _ _, by rw [x8, em],
        by rw [x5, rx.gpr _ (by decide), g3, ep], ?_, fun q hq => ?_, fun q _ _ => by rw [mx]⟩
      · rw [x7, ep, eu, hpd, Proof.Ed25519.Slide.upd_self]
      · rw [mx, eu]
        by_cases hqi : q = i
        · rw [hqi, m3, hbyte, hpd, Proof.Ed25519.Slide.upd_self]
        · rw [pairD, Proof.Ed25519.Slide.upd_ne _ _ hqi, m3]
          exact hdig q (by omega_using [hq, hqi])
    · intro h0
      obtain h0 : T.m ≠ 0 := of_decide_eq_false h0
      obtain ⟨em, ew, ep, eu⟩ := Proof.Ed25519.Slide.step_grow (K := K) h0
      rw [Si, hbit] at ew eu
      obtain ⟨hp1, -, -, hup, hwm, -⟩ := G.m.resolve_left h0
      rw [Si] at hp1
      obtain g7 : s₃.gpr .r7 = BitVec.ofNat 32 (pairD S T.u T.p) := (r3.gpr _ (by decide)).trans (h7 h0)
      obtain hmb : T.m * b ≤ T.m := by
        rcases (by omega_using [hb] : b = 0 ∨ b = 1) with rfl | rfl <;> omega_arith
      obtain hsp : (S >>> T.p) &&& 1 < 2 := bit_lt S T.p
      refine WP.mono (recGrow_ok hs₃ hi (by omega_using [hp1, hi]) ha hb hm16 g3 g1 g5 g7 g8)
        fun x ⟨rx, mx, x8, x7⟩ => ?_
      obtain eB : pairD S T.u T.p + 2 * (T.m * b) = pairD S (Proof.Ed25519.Slide.step K T).u T.p := by
        rw [eu, pairD, pairD, Proof.Ed25519.Slide.upd_self, hup]
        omega_arith
      rw [eB] at mx x7
      refine ⟨rx.mono (by decide), ?_, by rw [x8, em],
        by rw [rx.gpr _ (by decide), rx.gpr _ (by decide), g5, ep], by rw [x7, ep], fun q hq => ?_,
        fun q hq1 hq2 => ?_⟩
      · intro y hy
        rw [mx, writeW8_outside _ _ _ (by omega_arith) (by omega_using [hy, hp1, hi]),
          writeW8_outside _ _ _ (by omega_arith) (by omega_using [hy, hi])]
      · rw [mx, writeW8_apply]
        by_cases hqp : q = T.p
        · rw [hqp, ite_eq_left rfl]
        · rw [ite_eq_right (fun e => hqp ((off_eq_iff base (by omega_arith) (by omega_arith)).mp e
            |> fun e' => by omega_using [e'])), writeW8_apply]
          by_cases hqi : q = i
          · rw [hqi, ite_eq_left rfl, hpd, eu, Proof.Ed25519.Slide.upd_ne _ _ (by omega_using [hp1]),
              Proof.Ed25519.Slide.upd_self, Nat.mul_zero, Nat.add_zero]
          · rw [ite_eq_right (fun e => hqi ((off_eq_iff base (by omega_arith) (by omega_arith)).mp e
              |> fun e' => by omega_using [e'])), pairD, eu, Proof.Ed25519.Slide.upd_ne _ _ hqp,
              Proof.Ed25519.Slide.upd_ne _ _ hqi, m3]
            exact hdig q (by omega_using [hq, hqi])
      · rw [mx, writeW8_outside _ _ _ (by omega_arith)
            (by rw [ofs_off' base (by omega_arith)]; omega_using [hq1, hp1]),
          writeW8_outside _ _ _ (by omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_using [hq1])]
  refine WP.seq (WP.mono mid fun x ⟨rx, fx, x8, x5, x7, xd, xr⟩ => ?_)
  refine wp_dp (op2_imm (by decide)) fun y uy => wp_cmp (op2_imm (by decide)) fun u fu zu => WP.block_nil ?_
  obtain ru : Rest recRegs s u :=
    (r3.mono (by decide)).trans ((rx.mono (by decide)).trans ((uy.rest (by decide)).trans (fu.rest _)))
  obtain mu : u.mem = x.mem := by rw [fu.mem, uy.mem]
  obtain g11 : y.gpr .r11 = BitVec.ofNat 32 i + 1 := by
    rw [uy.gpr, dpVal, rx.gpr _ (by decide), r3.gpr _ (by decide), h11]
  refine ⟨rest_keeps ru, by rw [mu, ← m3]; exact fx, ⟨hs.of_keeps (rest_keeps ru) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_⟩
  · rw [fu.gpr, g11]
    exact (BitVec.ofNat_add i 1).symm
  · rw [fu.gpr, uy.other _ (by decide), x8, hS]
  · rw [fu.gpr, uy.other _ (by decide), uy.other _ (by decide), x5, hS]
  · intro _
    rw [fu.gpr, uy.other _ (by decide), x7, hS]
  · intro q hq
    rw [mu, hS]
    exact xd q hq
  · intro q hq1 hq2
    rw [mu, xr q hq1 hq2, m3]
    exact hrest q (by omega_using [hq1]) hq2
  · rw [zu, g11]
    exact rec_next_fact i hi

/-- No bit read. -/
theorem recInit_ok {base : Addr} {S K : Nat} {s : State} (hs : Scr s base)
    (hbits : ∀ q < 456, s.mem (off base (VBITS + q)) = BitVec.ofNat 8 (pair2 S K q)) :
    WP isa (.block recInit) s fun t => Keeps recRegs s t ∧ t.mem = s.mem ∧ RecAt base S K 0 t := by
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_reg _ _) fun t ut => WP.block_nil ?_
  obtain rt : Rest recRegs s t := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (ut.rest (by decide)))
  obtain mt : t.mem = s.mem := by rw [ut.mem, u₂.mem, u₁.mem]
  refine ⟨rest_keeps rt, mt, hs.of_keeps (rest_keeps rt) (by decide), ?_, ?_, ?_, fun h => absurd rfl h,
    fun q hq => absurd hq (Nat.not_lt_zero _), fun q _ hq => by rw [mt]; exact hbits q hq⟩
  · rw [ut.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  · rw [ut.other _ (by decide), u₂.gpr]; rfl
  · rw [ut.gpr, ut.other _ (by decide)]
    exact (BitVec.add_zero _).symm

/-- `k`'s digits in place of its bits. -/
theorem vrecode_ok {base : Addr} {S K : Nat} {s : State} (hs : Scr s base)
    (hbits : ∀ q < 456, s.mem (off base (VBITS + q)) = BitVec.ofNat 8 (pair2 S K q)) :
    WP isa vrecode s fun t => Keeps recRegs s t ∧ Outside base VBITS 456 s.mem t.mem ∧
      ∀ q < 456, t.mem (off base (VBITS + q)) = BitVec.ofNat 8 (pairD S (vdigits K) q) := by
  rw [vrecode]
  refine WP.seq (WP.mono (recInit_ok hs hbits) fun s₁ ⟨k₁, m₁, a₁⟩ => ?_)
  refine WP.loop (M := isa) (Inv := fun n t => 0 < n ∧ n ≤ 456 ∧ Keeps recRegs s t ∧
    Outside base VBITS 456 s.mem t.mem ∧ RecAt base S K (456 - n) t) ?_ 456 s₁
    ⟨by decide, Nat.le_refl _, k₁, by rw [m₁]; exact Outside.refl _ _ _ _, by rw [Nat.sub_self]; exact a₁⟩
  intro n x ⟨n0, n456, kx, fx, ax⟩
  refine WP.mono (recBit_ok ax (by omega_using [n0])) fun t ⟨kt, ft, at', zt⟩ => ?_
  by_cases h1 : n = 1
  · subst h1
    exact .inl ⟨by show some (!t.z) = _; rw [zt]; rfl, kx.trans kt, fx.trans ft, fun q hq => at'.dig q hq⟩
  · refine .inr ⟨by show some (!t.z) = _; rw [zt, decide_eq_false (by omega_using [h1, n0])]; rfl, n - 1,
      by omega_using [n0], by omega_using [h1, n0], by omega_using [n456], kx.trans kt, fx.trans ft, ?_⟩
    rw [show 456 - (n - 1) = 456 - n + 1 by omega_using [n0, n456]]
    exact at'

end VG.Proof.Ed448.Arm

end


/-!
# Ed448 verification's equation on ARMv7: the table of `-A`'s odd multiples

`vtable_ok`: `vtable` leaves entry `j < 8` of the table at `VTAB` as `oddMul A j`
(`Proof/Ed448/CombRef.lean`), the multiple `[2j + 1]` of the point `A` in slots 6, 7 and 10, its
coordinates' limbs bounded (`TabOk`), and `Q` the neutral point again. An entry is stored from
`Q` (`ventryStore_ok`), three slots copied to the words at `r12` (`toEntry_ok`), and read back
into slots the same way (`fromEntry_ok`, `ventryLoad_ok`); the field operations write below the
table (`EntryOk.keep`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.Ed448 (double oddMul)
open VG.Impl.X448.Arm (slot ACC ld st)
open VG.Proof.X25519.Arm (wp_dp wp_movw wp_cmp wp_ldr wp_str op2_imm op2_reg op2_lsl dpVal Rest)

variable {fv : Bool}

/-! ## An entry's words -/

/-- The limbs of the slot at `a` to the twenty-eight words at `r12 + o`, which are at byte `q` of
the working space, above the slots. -/
theorem toEntry_ok {s : State} {base : Addr} (hs : Scr s base) {o a q : Nat} (ho : o + 112 ≤ 4096)
    (ha : a + 112 ≤ 4096) (hq1 : 4096 ≤ q) (hq2 : q + 112 ≤ 8192)
    (hea : ∀ i < 28, State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + 4 * i)) = off base (q + 4 * i)) :
    WP isa (.block (toEntry o a)) s fun t =>
      (∀ i < 28, limbs t.mem base q i = limbs s.mem base a i) ∧
      Outside base q 112 s.mem t.mem ∧ Keeps [.r3] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base q i = limbs s.mem base a i) ∧
    Outside base q 112 s.mem t.mem ∧ Keeps [.r3] s t
  obtain step : ∀ n t, n < 28 → inv n t →
      WP isa (.block [ld .r3 (a + 4 * n), .str .r3 .r12 (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain ht := hs.of_keeps tk (by decide)
    refine load_ok ht (by omega_using [ha, hn]) fun u hu => ?_
    refine wp_str (a := off base (q + 4 * n)) (by omega_using [ho, hn])
      (by rw [hu.other _ (by decide), tk.1 _ (by decide)]; exact hea n hn)
      (by rw [hu.wr]; exact ht.write (by omega_using [hq2, hn])) fun v hv => WP.block_nil ?_
    obtain out : Outside base (q + 4 * n) 4 t.mem v.mem := by
      rw [hv.mem, hu.mem]; exact writeW_outside _ _ _ (by omega_using [hq2, hn])
    refine ⟨fun i hi => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans (rest_keeps ((hu.rest (by decide)).trans (hv.rest _)))⟩
    change (word v.mem base (q + 4 * i)).toNat = _
    rw [hv.mem, hu.mem, word_write t.mem base (by omega_using [hq2, hn]) (by omega_using [hq2, hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, hu.gpr]
      exact congrArg BitVec.toNat (tm.word (Or.inl (by omega_using [ha, hq1, hn])) (by omega_using [ha, hn]))
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The twenty-eight words at `r12 + a`, which are at byte `q` of the working space, above the
slots, to the limbs of the slot at `o`. -/
theorem fromEntry_ok {s : State} {base : Addr} (hs : Scr s base) {o a q : Nat} (ho : o + 112 ≤ 4096)
    (ha : a + 112 ≤ 4096) (hq1 : 4096 ≤ q) (hq2 : q + 112 ≤ 8192)
    (hea : ∀ i < 28, State.addr (s.gpr .r12 + BitVec.ofNat 32 (a + 4 * i)) = off base (q + 4 * i)) :
    WP isa (.block (fromEntry o a)) s fun t =>
      (∀ i < 28, limbs t.mem base o i = limbs s.mem base q i) ∧
      Outside base o 112 s.mem t.mem ∧ Keeps [.r3] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = limbs s.mem base q i) ∧
    Outside base o 112 s.mem t.mem ∧ Keeps [.r3] s t
  obtain step : ∀ n t, n < 28 → inv n t →
      WP isa (.block [.ldr .r3 .r12 (a + 4 * n), st .r3 (o + 4 * n)]) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    obtain ht := hs.of_keeps tk (by decide)
    refine wp_ldr (a := off base (q + 4 * n)) (by omega_using [ha, hn])
      (by rw [tk.1 _ (by decide)]; exact hea n hn) (ht.read (by omega_using [hq2, hn])) fun u hu => ?_
    refine store_ok (ht.of_upd hu (by decide) (by decide)) (by omega_using [ho, hn]) fun v hv => WP.block_nil ?_
    obtain out : Outside base (o + 4 * n) 4 t.mem v.mem := by
      rw [hv.mem, hu.mem]; exact writeW_outside _ _ _ (by omega_using [ho, hn])
    refine ⟨fun i hi => ?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])),
      tk.trans (rest_keeps ((hu.rest (by decide)).trans (hv.rest _)))⟩
    change (word v.mem base (o + 4 * i)).toNat = _
    rw [hv.mem, hu.mem, word_write t.mem base (by omega_using [ho, hn]) (by omega_using [ho, hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, hu.gpr]
      exact congrArg BitVec.toNat (tm.word (Or.inr (by omega_using [ho, hq1])) (by omega_using [hq2, hn]))
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The address of a word of the entry `r12` points to. -/
theorem entry_ea {s : State} {base : Addr} (hs : Scr s base) {e : Nat} (hp : Ptr s .r12 e) {c : Nat}
    (he : e + c + 112 ≤ 8192) :
    ∀ i < 28, State.addr (s.gpr .r12 + BitVec.ofNat 32 (c + 4 * i)) = off base (e + c + 4 * i) := fun i hi => by
  rw [hs.eaP hp (by omega_using [he, hi]), Nat.add_assoc]

/-- A slot from the entry's words at `r12 + a`. -/
theorem slotFrom_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (o : Index)
    {a q : Nat} (ha : a + 112 ≤ 4096) (hq1 : 4096 ≤ q) (hq2 : q + 112 ≤ 8192)
    (hea : ∀ i < 28, State.addr (s.gpr .r12 + BitVec.ofNat 32 (a + 4 * i)) = off base (q + 4 * i))
    (hbq : Bounded s.mem base q) :
    WP isa (.block (fromEntry (slot o.val) a)) s fun t =>
      Keep base s t ∧ Keeps [.r3] s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = Function.update (E s.mem base) o (F s.mem base q) := by
  refine WP.mono (fromEntry_ok hs (Nat.le_trans (slot_bound o) (by decide)) ha hq1 hq2 hea)
    fun t ⟨tf, tm, tk⟩ => ?_
  have op : Op base (slot o.val) s t := ⟨tk.mono (by decide), FieldMem.output tm⟩
  refine ⟨op.keep, tk, bounded_update op.mem hb (fun i hi => ?_), ?_⟩
  · rw [tf i hi]; exact hbq i hi
  · rw [E_update op.mem, show F t.mem base (slot o.val) = F s.mem base q from
      congrArg Proof.X448.toFe (valN_congr tf)]

/-! ## The table -/

/-- Entry `j` of the table holds the point `p`, its limbs bounded. -/
structure EntryOk (base : Addr) (m : Mem) (j : Nat) (p : Spec.Ed448.Point) : Prop where
  bx : Bounded m base (VTAB + 384 * j)
  by' : Bounded m base (VTAB + 384 * j + 128)
  bz : Bounded m base (VTAB + 384 * j + 256)
  x : F m base (VTAB + 384 * j) = p.X
  y : F m base (VTAB + 384 * j + 128) = p.Y
  z : F m base (VTAB + 384 * j + 256) = p.Z

/-- An entry whose words are kept. -/
theorem EntryOk.of_words {base : Addr} {m m' : Mem} {j : Nat} {p : Spec.Ed448.Point} (h : EntryOk base m j p)
    (hw : ∀ d, VTAB + 384 * j ≤ d → d + 4 ≤ VTAB + 384 * (j + 1) → word m' base d = word m base d) :
    EntryOk base m' j p := by
  obtain lim : ∀ c, c + 112 ≤ 384 → ∀ i < 28,
      limbs m' base (VTAB + 384 * j + c) i = limbs m base (VTAB + 384 * j + c) i := fun c hc i hi =>
    congrArg BitVec.toNat (hw _ (by omega_arith) (by omega_using [hc, hi]))
  obtain l0 : ∀ i < 28, limbs m' base (VTAB + 384 * j) i = limbs m base (VTAB + 384 * j) i := fun i hi =>
    lim 0 (by decide) i hi
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [l0 i hi]; exact h.bx i hi
  · rw [lim 128 (by decide) i hi]; exact h.by' i hi
  · rw [lim 256 (by decide) i hi]; exact h.bz i hi
  · exact (congrArg Proof.X448.toFe (valN_congr l0)).trans h.x
  · exact (congrArg Proof.X448.toFe (valN_congr (lim 128 (by decide)))).trans h.y
  · exact (congrArg Proof.X448.toFe (valN_congr (lim 256 (by decide)))).trans h.z

/-- The field operations write below the table. -/
theorem EntryOk.keep {base : Addr} {m m' : Mem} {j : Nat} {p : Spec.Ed448.Point} (h : EntryOk base m j p)
    (hj : j < 8) (hm : Outside2 base 64 2816 ACC 512 m m') : EntryOk base m' j p :=
  h.of_words fun d h1 h2 => hm.word (Or.inr (by simp only [VTAB] at h1; omega_using [h1]))
    (Or.inr (by simp only [VTAB, ACC] at h1 ⊢; omega_using [h1])) (by simp only [VTAB] at h2; omega_using [h2, hj])

/-- Another entry's store keeps it. -/
theorem EntryOk.other {base : Addr} {m m' : Mem} {j k : Nat} {p : Spec.Ed448.Point} (h : EntryOk base m j p)
    (hj : j < 8) (hjk : j ≠ k) (hm : Outside base (VTAB + 384 * k) 384 m m') : EntryOk base m' j p :=
  h.of_words fun d h1 h2 => hm.word (by omega_using [h1, h2, hjk])
    (by simp only [VTAB] at h2; omega_using [h2, hj])

/-- The table of the odd multiples of `A`. -/
def TabOk (base : Addr) (A : Spec.Ed448.Point) (m : Mem) : Prop := ∀ j < 8, EntryOk base m j (oddMul A j)

/-- A store of an entry writes within the multiplication's area and the table. -/
theorem outT {base : Addr} {j : Nat} {m m' : Mem} (h : Outside base (VTAB + 384 * j) 384 m m') (hj : j < 8) :
    Outside2 base 64 2816 ACC 3584 m m' := fun p _ hq =>
  h p (by simp only [VTAB, ACC] at hq ⊢; omega_using [hq, hj])

/-- The next entry's place, and the test of the last. -/
private theorem store_next_fact : ∀ j < 8,
    BitVec.ofNat 32 (VTAB + 384 * j) + (384 : BitVec 32) = BitVec.ofNat 32 (VTAB + 384 * (j + 1)) ∧
    (BitVec.ofNat 32 (VTAB + 384 * (j + 1)) - (BitVec.ofNat 16 (VTAB + 8 * 384)).setWidth 32 == 0) =
      decide (j + 1 = 8) := by decide

/-- `Q` stored as entry `j`. -/
theorem ventryStore_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {j : Nat}
    (hj : j < 8) (h11 : s.gpr .r11 = BitVec.ofNat 32 (VTAB + 384 * j)) :
    WP isa (.block ventryStore) s fun t =>
      Keeps [.r3, .r11, .r12] s t ∧ Outside base (VTAB + 384 * j) 384 s.mem t.mem ∧
      EntryOk base t.mem j (pt (E s.mem base) 0 21 2) ∧
      t.gpr .r11 = BitVec.ofNat 32 (VTAB + 384 * (j + 1)) ∧ t.z = decide (j + 1 = 8) := by
  have hT : VTAB = 4096 := rfl
  obtain nf := store_next_fact j hj
  rw [ventryStore, List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append]
  refine wp_dp (op2_reg _ _) fun s₁ u₁ => ?_
  obtain hs₁ := hs.of_upd u₁ (by decide) (by decide)
  obtain hp₁ : Ptr s₁ .r12 (VTAB + 384 * j) := by
    rw [Ptr, u₁.gpr, dpVal, u₁.other _ (by decide), h11]
  obtain sl : ∀ i : Index, slot i.val + 112 ≤ 2880 := fun i => by
    have := i.isLt
    simp only [slot]
    omega_arith
  -- `X`.
  refine VG.Proof.X25519.Arm.WP.append (toEntry_ok hs₁ (o := 0) (a := slot (0 : Index).val)
    (q := VTAB + 384 * j) (by decide) (by have := sl 0; omega_arith) (by omega_arith) (by omega_arith)
    (fun i hi => by have h := entry_ea hs₁ hp₁ (c := 0) (by omega_arith) i hi; rwa [Nat.add_zero] at h))
    fun s₂ ⟨f₂, o₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  obtain hp₂ := hp₁.of_keeps k₂ (by decide) (by decide)
  -- `Y`.
  refine VG.Proof.X25519.Arm.WP.append (toEntry_ok hs₂ (o := 128) (a := slot (21 : Index).val)
    (q := VTAB + 384 * j + 128) (by decide) (by have := sl 21; omega_arith) (by omega_arith) (by omega_arith)
    (entry_ea hs₂ hp₂ (by omega_arith))) fun s₃ ⟨f₃, o₃, k₃⟩ => ?_
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  obtain hp₃ := hp₂.of_keeps k₃ (by decide) (by decide)
  -- `Z`.
  refine VG.Proof.X25519.Arm.WP.append (toEntry_ok hs₃ (o := 256) (a := slot (2 : Index).val)
    (q := VTAB + 384 * j + 256) (by decide) (by have := sl 2; omega_arith) (by omega_arith) (by omega_arith)
    (entry_ea hs₃ hp₃ (by omega_arith))) fun s₄ ⟨f₄, o₄, k₄⟩ => ?_
  -- The next entry.
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => VG.Proof.X25519.Arm.wp_movw fun s₆ u₆ =>
    wp_cmp (op2_reg _ _) fun t ft zt => WP.block_nil ?_
  obtain k14 : Keeps [.r3, .r11, .r12] s₁ s₄ :=
    (k₂.mono (by decide)).trans ((k₃.mono (by decide)).trans (k₄.mono (by decide)))
  obtain g11 : s₅.gpr .r11 = BitVec.ofNat 32 (VTAB + 384 * (j + 1)) := by
    rw [u₅.gpr, dpVal, k₄.1 _ (by decide), k₃.1 _ (by decide), k₂.1 _ (by decide), u₁.other _ (by decide), h11]
    exact nf.1
  -- The limbs stored, from the slots, which the stores keep.
  obtain src : ∀ (i : Index) {m m' : Mem} {q : Nat}, Outside base q 112 m m' → 4096 ≤ q → ∀ k < 28,
      limbs m' base (slot i.val) k = limbs m base (slot i.val) k := fun i _ _ _ ho hq k hk =>
    ho.limbs (Or.inl (by have := sl i; omega_using [hq, this])) (by have := sl i; omega_using [this]) hk
  obtain lx : ∀ k < 28, limbs s₄.mem base (VTAB + 384 * j) k = limbs s.mem base (slot (0 : Index).val) k :=
    fun k hk => by
      rw [o₄.limbs (Or.inl (by omega_arith)) (by omega_arith) hk, o₃.limbs (Or.inl (by omega_arith)) (by omega_arith) hk,
        f₂ k hk, u₁.mem]
  obtain ly : ∀ k < 28, limbs s₄.mem base (VTAB + 384 * j + 128) k = limbs s.mem base (slot (21 : Index).val) k :=
    fun k hk => by
      rw [o₄.limbs (Or.inl (by omega_arith)) (by omega_arith) hk, f₃ k hk, src 21 o₂ (by omega_arith) k hk, u₁.mem]
  obtain lz : ∀ k < 28, limbs s₄.mem base (VTAB + 384 * j + 256) k = limbs s.mem base (slot (2 : Index).val) k :=
    fun k hk => by
      rw [f₄ k hk, src 2 o₃ (by omega_arith) k hk, src 2 o₂ (by omega_arith) k hk, u₁.mem]
  obtain mt : t.mem = s₄.mem := by rw [ft.mem, u₆.mem, u₅.mem]
  refine ⟨?_, ?_, ?_, by rw [ft.gpr, u₆.other _ (by decide), g11], ?_⟩
  · exact (rest_keeps (u₁.rest (ws := [.r3, .r11, .r12]) (by decide))).trans (k14.trans
      (rest_keeps ((u₅.rest (by decide)).trans ((u₆.rest (by decide)).trans (ft.rest _)))))
  · rw [mt, ← u₁.mem]
    exact (o₂.mono (by omega_arith) (by omega_arith)).trans ((o₃.mono (by omega_arith) (by omega_arith)).trans
      (o₄.mono (by omega_arith) (by omega_arith)))
  · rw [mt]
    exact ⟨fun k hk => by rw [lx k hk]; exact hb 0 k hk, fun k hk => by rw [ly k hk]; exact hb 21 k hk,
      fun k hk => by rw [lz k hk]; exact hb 2 k hk, congrArg Proof.X448.toFe (valN_congr lx),
      congrArg Proof.X448.toFe (valN_congr ly), congrArg Proof.X448.toFe (valN_congr lz)⟩
  · rw [zt, u₆.other _ (by decide), g11, u₆.gpr]
    exact nf.2

/-- The address of the entry of an odd digit. -/
private theorem entry_addr_fact : ∀ d < 16, d % 2 = 1 →
    (BitVec.ofNat 16 (VTAB - 192)).setWidth 32 + BitVec.ofNat 32 d <<< 7 + BitVec.ofNat 32 d <<< 6 =
      BitVec.ofNat 32 (VTAB + 384 * ((d - 1) / 2)) := by decide

/-- The entry of the odd digit in `r3` into slots 6, 7 and 1. -/
theorem ventryLoad_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {d : Nat}
    (hd : d < 16) (hodd : d % 2 = 1) (h3 : s.gpr .r3 = BitVec.ofNat 32 d) {p : Spec.Ed448.Point}
    (he : EntryOk base s.mem ((d - 1) / 2) p) :
    WP isa (.block ventryLoad) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = Function.update (Function.update (Function.update (E s.mem base) 6 p.X) 7 p.Y) 1 p.Z := by
  have hT : VTAB = 4096 := rfl
  obtain ⟨j, hj⟩ : ∃ j, (d - 1) / 2 = j := ⟨_, rfl⟩
  obtain hj8 : j < 8 := by omega_using [hd, hj]
  obtain af := entry_addr_fact d hd hodd
  rw [hj] at he af
  rw [ventryLoad, ventryAddr, List.append_assoc, List.append_assoc, List.cons_append, List.cons_append,
    List.cons_append, List.cons_append, List.nil_append]
  refine VG.Proof.X25519.Arm.wp_movw fun s₁ u₁ => wp_dp (op2_lsl (by decide)) fun s₂ u₂ =>
    wp_dp (op2_lsl (by decide)) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ => ?_
  obtain r4 : Rest [.r12] s s₄ := (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans
    ((u₃.rest (by decide)).trans (u₄.rest (by decide))))
  obtain m4 : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain k4 : Keep base s s₄ :=
    ⟨(rest_keeps r4).mono (by decide), by rw [m4]; exact Outside2.refl _ _ _ _ _ _⟩
  obtain hs₄ := k4.scr hs
  obtain g3₁ : s₁.gpr .r3 = BitVec.ofNat 32 d := (u₁.other _ (by decide)).trans h3
  obtain g3₂ : s₂.gpr .r3 = BitVec.ofNat 32 d := (u₂.other _ (by decide)).trans g3₁
  obtain hp₄ : Ptr s₄ .r12 (VTAB + 384 * j) := by
    rw [Ptr, u₄.gpr, dpVal, u₄.other _ (by decide), u₃.other _ (by decide), u₃.gpr, dpVal, u₂.gpr, dpVal, u₁.gpr,
      g3₁, g3₂, af]
  -- `X`.
  refine VG.Proof.X25519.Arm.WP.append (slotFrom_ok hs₄ (m4 ▸ hb) 6 (a := 0) (q := VTAB + 384 * j) (by decide)
    (by omega_arith) (by omega_arith)
    (fun i hi => by have h := entry_ea hs₄ hp₄ (c := 0) (by omega_arith) i hi; rwa [Nat.add_zero] at h)
    (m4 ▸ he.bx)) fun s₅ ⟨k₅, k3₅, b₅, e₅⟩ => ?_
  obtain hs₅ := k₅.scr hs₄
  obtain hp₅ := hp₄.of_keeps k3₅ (by decide) (by decide)
  obtain t₅ : EntryOk base s₅.mem j p := (m4 ▸ he : EntryOk base s₄.mem j p).keep hj8 k₅.mem
  -- `Y`.
  refine VG.Proof.X25519.Arm.WP.append (slotFrom_ok hs₅ b₅ 7 (a := 128) (q := VTAB + 384 * j + 128) (by decide)
    (by omega_arith) (by omega_arith) (entry_ea hs₅ hp₅ (by omega_arith)) t₅.by')
    fun s₆ ⟨k₆, k3₆, b₆, e₆⟩ => ?_
  obtain hs₆ := k₆.scr hs₅
  obtain hp₆ := hp₅.of_keeps k3₆ (by decide) (by decide)
  obtain t₆ : EntryOk base s₆.mem j p := t₅.keep hj8 k₆.mem
  -- `Z`.
  refine WP.mono (slotFrom_ok hs₆ b₆ 1 (a := 256) (q := VTAB + 384 * j + 256) (by decide)
    (by omega_arith) (by omega_arith) (entry_ea hs₆ hp₆ (by omega_arith)) t₆.bz)
    fun t ⟨kt, _, bt, et⟩ => ⟨k4.trans (k₅.trans (k₆.trans kt)), bt, ?_⟩
  rw [et, e₆, e₅, t₆.z, t₅.y, m4, show F s.mem base (VTAB + 384 * j) = p.X from he.x]

/-! ## Its entries -/

/-- `Q` and the copy of `-A` with `Z` in slot 1. -/
def tableQF : List FieldOp := [.copy 0 6, .copy 21 7, .copy 2 10, .copy 1 10]

/-- `Q` the neutral point. -/
def neutralF : List FieldOp := [.sub 0 0 0, .copy 21 10, .copy 2 10]

/-- `T` (slots 3–5) taken into `Q` (slots 0, 21, 2). -/
def takeF : List FieldOp := [.copy 0 3, .copy 21 4, .copy 2 5]

theorem addTake_keep (e : Env) (x y z : Index) (i : Index) (hi : i.val = 1 ∨ (6 ≤ i.val ∧ i.val < 12)) :
    applyOps (addF x y z ++ takeF) e i = e i := by
  refine applyOps_keep _ _ ?_
  rw [List.map_append, addF_dest]
  revert i; decide

theorem addTake_pt6 (e : Env) :
    pt (applyOps (addF 6 7 1 ++ takeF) e) 0 21 2 = addWith (e 11) (pt e 0 21 2) (pt e 6 7 1) := rfl

/-- The table before entry `j`: the entries below it, `Q` the one before, and `[2]A` in slots 6, 7
and 1. -/
structure TabAt (base : Addr) (A : Spec.Ed448.Point) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.r11 :: workRegs) s₀ s
  mem : Outside2 base 64 2816 ACC 3584 s₀.mem s.mem
  r11 : s.gpr .r11 = BitVec.ofNat 32 (VTAB + 384 * j)
  q : pt (E s.mem base) 0 21 2 = oddMul A (j - 1)
  two : pt (E s.mem base) 6 7 1 = double A
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d
  tab : ∀ i < j, EntryOk base s.mem i (oddMul A i)

/-- A field operation's writes are within the slots, the multiplication's area and the table. -/
theorem keep_wide {base : Addr} {s t : State} (h : Keep base s t) :
    Outside2 base 64 2816 ACC 3584 s.mem t.mem := h.mem.mono (Nat.le_refl _) (by decide)

theorem vtableInit_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (vtableInit fv) s fun t => TabAt base (pt (E s.mem base) 6 7 10) s t 1 := by
  rw [vtableInit, show vtableQ = tableQF.map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (ops_ok hs hb tableQF) fun s₁ ⟨k₁, b₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain q₁ : pt (E s₁.mem base) 0 21 2 = pt (E s.mem base) 6 7 10 := by rw [e₁]; rfl
  obtain a₁ : pt (E s₁.mem base) 6 7 1 = pt (E s.mem base) 6 7 10 := by rw [e₁]; rfl
  obtain o₁ : ∀ i : Index, i.val = 10 ∨ i.val = 11 → E s₁.mem base i = E s.mem base i := fun i hi => by
    rw [e₁]
    refine applyOps_keep _ _ ?_
    revert i; decide
  -- The first entry.
  refine WP.seq (VG.Proof.X25519.Arm.wp_movw fun s₂ u₂ => ?_)
  obtain k₂ : Keeps (.r11 :: workRegs) s₁ s₂ := rest_keeps (u₂.rest (by decide))
  refine WP.mono (ventryStore_ok (hs₁.of_keeps k₂ (by decide)) (u₂.mem ▸ b₁) (j := 0) (by decide)
    (by rw [u₂.gpr]; rfl)) fun s₃ ⟨k₃, o₃, t₃, g₃, _⟩ => ?_
  obtain k13 : Keeps (.r11 :: workRegs) s₁ s₃ := k₂.trans (k₃.mono (by decide))
  obtain hs₃ := hs₁.of_keeps k13 (by decide)
  obtain w₃ : ∀ i : Index, ∀ k < 28, limbs s₃.mem base (slot i.val) k = limbs s₁.mem base (slot i.val) k :=
    fun i k hk => by
      have := i.isLt
      rw [o₃.limbs (Or.inl (by simp only [VTAB, slot]; omega_arith)) (by simp only [slot]; omega_arith) hk, u₂.mem]
  obtain e₃ : E s₃.mem base = E s₁.mem base := funext fun i => congrArg Proof.X448.toFe (valN_congr (w₃ i))
  obtain b₃ : BoundedEnv s₃.mem base := fun i k hk => by rw [w₃ i k hk]; exact b₁ i k hk
  rw [u₂.mem, q₁] at t₃
  -- `[2]A`.
  rw [show doubleAt 6 7 1 = (doubleF 6 7 1).map FieldOp.impl from rfl]
  refine WP.mono (ops_ok hs₃ b₃ (doubleF 6 7 1)) fun t ⟨kt, bt, et⟩ => ?_
  obtain kp : ∀ i : Index, i.val = 0 ∨ (2 ≤ i.val ∧ i.val < 6) ∨ (8 ≤ i.val ∧ i.val < 12) ∨ i.val = 20 ∨
      i.val = 21 → E t.mem base i = E s₁.mem base i := fun i hi => by
    rw [et, doubleF_keep6 _ _ hi, e₃]
  refine ⟨kt.scr hs₃, bt, (k₁.regs.mono (by decide)).trans (k13.trans (kt.regs.mono (by decide))), ?_, ?_, ?_, ?_,
    ?_, ?_, fun i hi => ?_⟩
  · refine (keep_wide k₁).trans (Outside2.trans ?_ (keep_wide kt))
    rw [← u₂.mem]
    exact outT o₃ (by decide)
  · rw [kt.regs.1 _ (by decide), g₃]
  · rw [pt_congr' (kp 0 (by decide)) (kp 21 (by decide)) (kp 2 (by decide)), q₁]; rfl
  · rw [et, doubleF_eval6, e₃, a₁]
  · rw [kp 10 (by decide), o₁ 10 (by decide), h10]
  · rw [kp 11 (by decide), o₁ 11 (by decide), h11]
  · obtain rfl : i = 0 := by omega_using [hi]
    exact t₃.keep (by decide) kt.mem

theorem vtableStep_ok {s₀ s : State} {base : Addr} {A : Spec.Ed448.Point} {j : Nat} (h : TabAt base A s₀ s j)
    (h1 : 1 ≤ j) (h8 : j < 8) :
    WP isa (vtableStep fv) s fun t => TabAt base A s₀ t (j + 1) ∧ t.z = decide (j + 1 = 8) := by
  rw [vtableStep, show addAt 6 7 1 ++ vtake = (addF 6 7 1 ++ takeF).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (ops_ok h.scr h.bounded (addF 6 7 1 ++ takeF)) fun s₁ ⟨k₁, b₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr h.scr
  obtain kp : ∀ i : Index, i.val = 1 ∨ (6 ≤ i.val ∧ i.val < 12) → E s₁.mem base i = E s.mem base i := fun i hi => by
    rw [e₁, addTake_keep _ _ _ _ _ hi]
  obtain q₁ : pt (E s₁.mem base) 0 21 2 = oddMul A j := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega_using [h1]⟩
    rw [e₁, addTake_pt6, h.d, h.q, h.two]
    rfl
  refine WP.mono (ventryStore_ok hs₁ b₁ h8 (by rw [k₁.regs.1 _ (by decide), h.r11]))
    fun t ⟨kt, ot, tt, gt, zt⟩ => ?_
  obtain w : ∀ i : Index, ∀ k < 28, limbs t.mem base (slot i.val) k = limbs s₁.mem base (slot i.val) k :=
    fun i k hk => by
      have := i.isLt
      rw [ot.limbs (Or.inl (by simp only [VTAB, slot]; omega_arith)) (by simp only [slot]; omega_arith) hk]
  obtain et : E t.mem base = E s₁.mem base := funext fun i => congrArg Proof.X448.toFe (valN_congr (w i))
  rw [q₁] at tt
  refine ⟨⟨hs₁.of_keeps kt (by decide), fun i k hk => by rw [w i k hk]; exact b₁ i k hk,
    h.regs.trans ((k₁.regs.mono (by decide)).trans (kt.mono (by decide))),
    h.mem.trans ((keep_wide k₁).trans (outT ot h8)), gt, by rw [et, Nat.add_sub_cancel]; exact q₁,
    by rw [et, pt_congr' (kp 6 (by decide)) (kp 7 (by decide)) (kp 1 (by decide))]; exact h.two,
    by rw [et, kp 10 (by decide)]; exact h.one, by rw [et, kp 11 (by decide)]; exact h.d, fun i hi => ?_⟩, zt⟩
  rcases Nat.lt_or_ge i j with hij | hij
  · exact ((h.tab i hij).keep (by omega_using [hij, h8]) k₁.mem).other (by omega_using [hij, h8])
      (by omega_using [hij]) ot
  · obtain rfl : i = j := by omega_using [hi, hij]
    exact tt

/-- What `vtable` leaves, from the state `s` before it: the table of the odd multiples of the
point that was in slots 6, 7 and 10, and `Q` the neutral point again. -/
structure Tabled (base : Addr) (s t : State) : Prop where
  scr : Scr t base
  bounded : BoundedEnv t.mem base
  regs : Keeps (.r11 :: workRegs) s t
  mem : Outside2 base 64 2816 ACC 3584 s.mem t.mem
  tab : TabOk base (pt (E s.mem base) 6 7 10) t.mem
  q : pt (E t.mem base) 0 21 2 = Spec.Ed448.identity
  one : E t.mem base 10 = 1
  d : E t.mem base 11 = Spec.Ed448.d

theorem vtable_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (vtable fv) s (Tabled base s) := by
  rw [vtable]
  refine WP.seq (WP.mono (vtableInit_ok hs hb h10 h11) fun s₁ a₁ => ?_)
  refine WP.seq (WP.mono (WP.loop (M := isa) (Q := fun t => TabAt base (pt (E s.mem base) 6 7 10) s t 8)
    (fun n t => 0 < n ∧ n ≤ 7 ∧ TabAt base (pt (E s.mem base) 6 7 10) s t (8 - n)) ?_ 7 s₁
    ⟨by decide, Nat.le_refl _, (show (8 : Nat) - 7 = 1 from rfl) ▸ a₁⟩) fun s₂ a₂ => ?_)
  · intro n x ⟨n0, n7, ax⟩
    refine WP.mono (vtableStep_ok ax (by omega_using [n7]) (by omega_using [n0])) fun t ⟨at', zt⟩ => ?_
    by_cases hn : n = 1
    · subst hn
      exact .inl ⟨by show some (!t.z) = _; rw [zt]; rfl, at'⟩
    · refine .inr ⟨by show some (!t.z) = _; rw [zt, decide_eq_false (by omega_using [hn, n0])]; rfl, n - 1,
        by omega_using [n0], by omega_using [hn, n0], by omega_using [n7], ?_⟩
      rw [show 8 - (n - 1) = 8 - n + 1 by omega_using [n0, n7]]
      exact at'
  · rw [show vneutral = neutralF.map FieldOp.impl from rfl]
    refine WP.mono (ops_ok a₂.scr a₂.bounded neutralF) fun t ⟨kt, bt, et⟩ => ?_
    obtain kp : ∀ i : Index, i.val = 10 ∨ i.val = 11 → E t.mem base i = E s₂.mem base i := fun i hi => by
      rw [et]
      refine applyOps_keep _ _ ?_
      revert i; decide
    refine ⟨kt.scr a₂.scr, bt, a₂.regs.trans (kt.regs.mono (by decide)), a₂.mem.trans (keep_wide kt),
      fun j hj => (a₂.tab j hj).keep hj kt.mem, ?_, by rw [kp 10 (by decide)]; exact a₂.one,
      by rw [kp 11 (by decide)]; exact a₂.d⟩
    show (⟨E t.mem base 0, E t.mem base 21, E t.mem base 2⟩ : Spec.Ed448.Point) = ⟨0, 1, 1⟩
    rw [et]
    show (⟨E s₂.mem base 0 - E s₂.mem base 0, E s₂.mem base 10, E s₂.mem base 10⟩ : Spec.Ed448.Point) = _
    rw [Fin.sub_self, a₂.one]

end VG.Proof.Ed448.Arm

end


/-!
# Ed448 verification's equation on ARMv7: `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for bit `t` (the bit of `S` is bit 0 of the byte at
`VBITS`, and digit `t` of `k` is above it; byte `t` is loaded into `r8`: `vload_ok`): `Q` (slots
0, 21, 2) doubled; in the comb's rows, `t < 114`, the table's entry of the row's four bits of `S`
(`vcombDigit_ok`, and base-point multiplication's `combSelect_ok`) added (`vcombIf_ok`); and, if
the digit is not zero, its entry of `-A`'s table loaded into slots 6, 7 and 1 (`ventryLoad_ok`)
and added (`vaddIf_ok`, `vdoubleAdd_ok`). The loop's invariant (`VInv`): `Q` is the reference
computation's point after the digits above `n` (`Proof.Ed448.vcomb`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (double vcomb vcombStep vcomb_bit combDigit combDigit_lt oddMul vdigits)
open VG.Impl.X448.Arm (slot ACC)

variable {fv : Bool}

/-! ## The values -/

/-- The slots after the point `p` is put in slots 6, 7 and 1 and added, made if `nz`. -/
def entEnv (p : Spec.Ed448.Point) : Bool → Env → Env
  | true, e => applyOps (addF 6 7 1 ++ takeF)
      (Function.update (Function.update (Function.update e 6 p.X) 7 p.Y) 1 p.Z)
  | false, e => e

/-- The slots after the comb's entry `i` is selected and added, in a row of the comb. -/
def combEnv (i : Nat) : Bool → Env → Env
  | true, e => applyOps (addF 8 9 10 ++ takeF) (selEnv i e)
  | false, e => e

/-- The slots after an iteration: in a row of the comb (`row`), of index `i`, and for the entry
`p` of a digit of `k` that is not zero (`nz`). -/
def vstepEnv (row : Bool) (i : Nat) (nz : Bool) (p : Spec.Ed448.Point) (e : Env) : Env :=
  entEnv p nz (combEnv i row (applyOps (doubleF 0 21 2) e))

/-- The addition of the digit's entry keeps 1 and `d`. -/
theorem entEnv_keep (p : Spec.Ed448.Point) (nz : Bool) (e : Env) (i : Index) (hi : 8 ≤ i.val ∧ i.val < 12) :
    entEnv p nz e i = e i := by
  cases nz
  · rfl
  · rw [entEnv, addTake_keep _ _ _ _ _ (Or.inr (by omega_using [hi])),
      Function.update_of_ne (fun h => by subst h; omega_arith),
      Function.update_of_ne (fun h => by subst h; omega_arith),
      Function.update_of_ne (fun h => by subst h; omega_arith)]

/-- The comb's addition keeps 1 and `d`. -/
theorem combEnv_keep (i : Nat) (row : Bool) (e : Env) (j : Index) (hj : j.val = 10 ∨ j.val = 11) :
    combEnv i row e j = e j := by
  cases row
  · rfl
  · have h8 : j ≠ 8 := fun h => by subst h; omega_arith
    have h9 : j ≠ 9 := fun h => by subst h; omega_arith
    rw [combEnv, addTake_keep _ _ _ _ _ (Or.inr (by omega_using [hj])), selEnv,
      Function.update_of_ne h9, Function.update_of_ne h8]

theorem combEnv_pt (i : Nat) (row : Bool) (e : Env) :
    pt (combEnv i row e) 0 21 2 =
      if row then addWith (e 11) (pt e 0 21 2) ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e 10⟩
      else pt e 0 21 2 := by
  cases row <;> rfl

theorem entEnv_pt (p : Spec.Ed448.Point) (nz : Bool) (e : Env) :
    pt (entEnv p nz e) 0 21 2 = if nz then addWith (e 11) (pt e 0 21 2) p else pt e 0 21 2 := by
  cases nz <;> rfl

theorem vstepEnv_pt (row : Bool) (i : Nat) (nz : Bool) (p : Spec.Ed448.Point) (e : Env) :
    pt (vstepEnv row i nz p e) 0 21 2 =
      let r₁ := double (pt e 0 21 2)
      let r₂ := if row then
        addWith (e 11) r₁ ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e 10⟩ else r₁
      if nz then addWith (e 11) r₂ p else r₂ := by
  unfold vstepEnv
  generalize he0 : applyOps (doubleF 0 21 2) e = e0
  obtain p0 : pt e0 0 21 2 = double (pt e 0 21 2) := by rw [← he0, doubleF_eval0]
  obtain k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, doubleF_keep0 _ _ (Or.inl hi)]
  generalize he1 : combEnv i row e0 = e1
  obtain p1 : pt e1 0 21 2 = if row then
      addWith (e0 11) (pt e0 0 21 2) ⟨(Impl.Ed448.Comb.entry i).1, (Impl.Ed448.Comb.entry i).2, e0 10⟩
      else pt e0 0 21 2 := by
    rw [← he1, combEnv_pt]
  obtain e11 : e1 11 = e 11 := by rw [← he1, combEnv_keep _ _ _ _ (Or.inr rfl), k0 11 (by decide)]
  rw [entEnv_pt, p1, e11, k0 11 (by decide), k0 10 (by decide), p0]

theorem vstepEnv_keep (row : Bool) (i : Nat) (nz : Bool) (p : Spec.Ed448.Point) (e : Env) (j : Index)
    (hj : j.val = 10 ∨ j.val = 11) : vstepEnv row i nz p e j = e j := by
  rw [vstepEnv, entEnv_keep _ _ _ _ (by omega_using [hj]), combEnv_keep _ _ _ _ hj,
    doubleF_keep0 _ _ (Or.inl (by omega_using [hj]))]

/-- One bit: the reference computation's point after the digits above `t`, then after digit
`t`. -/
theorem vcomb_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 21 2 = vcomb S K A (456 - (t + 1))) (h1 : e 10 = 1) (hd : e 11 = Spec.Ed448.d) :
    pt (vstepEnv (decide (t < 114)) (combDigit S t) (!decide (vdigits K t = 0))
      (oddMul A ((vdigits K t - 1) / 2)) e) 0 21 2 = vcomb S K A (456 - t) := by
  rw [vstepEnv_pt, hd, h1, hr, vcomb_bit S K A ht]
  by_cases hz : vdigits K t = 0 <;> by_cases hrow : t < 114 <;>
    simp only [vcombStep, hz, hrow, decide_true, decide_false, Bool.not_true, Bool.not_false, ↓reduceIte,
      Bool.false_eq_true] <;> rfl

/-! ## One iteration -/

/-- The byte of a bit of `S` and a digit of `k`, in `r8`: what the test of `vtest` compares with
zero, the digit, and the bit of `S`. -/
theorem pair_test : ∀ a < 2, ∀ d < 16,
    (((BitVec.ofNat 8 (a + 2 * d)).setWidth 32 >>> 1) - 0 == (0 : BitVec 32)) = decide (d = 0) ∧
    (BitVec.ofNat 8 (a + 2 * d)).setWidth 32 >>> 1 = BitVec.ofNat 32 d ∧
    (BitVec.ofNat 8 (a + 2 * d)).setWidth 32 &&& 1 = (BitVec.ofNat 8 a).setWidth 32 := by
  decide

/-- `k`'s digits are below 16. -/
theorem vdigits_lt (K q : Nat) : vdigits K q < 16 := by
  show Proof.Ed25519.Slide.digits 456 K q < 16
  rcases Proof.Ed25519.Slide.digits_odd 456 K q with h | h <;> omega_using [h]

/-- The loop's invariant, after the bits of `S` and the digits of `k` above `n`, for the table
of the odd multiples of `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.r8 :: .r11 :: workRegs) s₀ s
  r11 : s.gpr .r11 = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  rep : pt (E s.mem base) 0 21 2 = vcomb S K A (456 - n)
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d

/-- An iteration after its byte is loaded: the invariant before bit `n`, with the counter moved
down and the byte of bit `n` of `S` and digit `n` of `k` in `r8`. -/
structure VBit (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.r8 :: .r11 :: workRegs) s₀ s
  r11 : s.gpr .r11 = BitVec.ofNat 32 n
  r8 : s.gpr .r8 = (BitVec.ofNat 8 (pairD S (vdigits K) n)).setWidth 32
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  rep : pt (E s.mem base) 0 21 2 = vcomb S K A (456 - (n + 1))
  one : E s.mem base 10 = 1
  d : E s.mem base 11 = Spec.Ed448.d

theorem vload_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pairD S (vdigits K) t))
    (hi : VInv base S K A s₀ s (n + 1)) :
    WP isa (.block vload) s fun u => VBit base S K A s₀ u n := by
  have hs := hi.scr
  have hB : VBITS = 3104 := rfl
  have hA : ACC = 3584 := rfl
  obtain bitval : s.mem (off base (VBITS + n)) = BitVec.ofNat 8 (pairD S (vdigits K) n) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact hbits n hn
  obtain he : s.gpr .r11 - (1 : BitVec 32) = BitVec.ofNat 32 n := by
    change s.gpr .r11 - BitVec.ofNat 32 1 = _
    rw [hi.r11, BitVec.ofNat_add, BitVec.add_sub_cancel]
  unfold vload
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u1 v1 => ?_
  obtain b1 : u1.gpr .r11 = BitVec.ofNat 32 n := v1.gpr.trans he
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u2 v2 => ?_
  obtain ba : State.addr (u2.gpr .r7 + BitVec.ofNat 32 VBITS) = off base (VBITS + n) := by
    rw [v2.gpr]; change State.addr (u1.gpr .r0 + u1.gpr .r11 + BitVec.ofNat 32 VBITS) = _
    rw [b1, v1.other _ (by decide), Offset.add_add, Nat.add_comm n VBITS]
    exact hs.ea (by omega_arith)
  refine VG.Proof.X25519.Arm.wp_ldrb (by omega_arith) ba
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hs.read (by omega_arith)) fun u3 v3 => WP.block_nil ?_
  obtain k : Keeps (.r8 :: .r11 :: workRegs) s u3 :=
    rest_keeps ((v1.rest (ws := .r8 :: .r11 :: workRegs) (by decide)).trans ((v2.rest (by decide)).trans
      (v3.rest (by decide))))
  obtain m3 : u3.mem = s.mem := by rw [v3.mem, v2.mem, v1.mem]
  refine ⟨hs.of_keeps k (by decide), m3 ▸ hi.bounded, hi.regs.trans k, ?_, ?_, m3 ▸ hi.mem, ?_, ?_, ?_⟩
  · rw [v3.other _ (by decide), v2.other _ (by decide), b1]
  · rw [v3.gpr, v2.mem, v1.mem, bitval]
  · rw [m3]; exact hi.rep
  · rw [m3]; exact hi.one
  · rw [m3]; exact hi.d

theorem vtest_ok (s : State) {a d : Nat} (ha : a < 2) (hd : d < 16)
    (h8 : s.gpr .r8 = (BitVec.ofNat 8 (a + 2 * d)).setWidth 32) :
    WP isa (.block vtest) s fun u => u.z = decide (d = 0) ∧ u.gpr .r3 = BitVec.ofNat 32 d ∧
      Keeps [.r3] s u ∧ u.mem = s.mem := by
  obtain pm := pair_test a ha d hd
  unfold vtest
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsr (by decide)) fun u1 v1 => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u2 v2 hz =>
    WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hz, v1.gpr, h8]; exact pm.1
  · rw [v2.gpr, v1.gpr, h8]; exact pm.2.1
  · exact rest_keeps ((v1.rest (ws := [.r3]) (by decide)).trans (v2.rest _))
  · rw [v2.mem, v1.mem]

/-- The entry of the digit `d` in `r8` (above the bit `a`) added, if the digit is not zero. -/
theorem vaddIf_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {a d : Nat}
    (ha : a < 2) (hd : d = 0 ∨ (d % 2 = 1 ∧ d < 16)) (h8 : s.gpr .r8 = (BitVec.ofNat 8 (a + 2 * d)).setWidth 32)
    {p : Spec.Ed448.Point} (he : EntryOk base s.mem ((d - 1) / 2) p) :
    WP isa (vaddIf fv) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = entEnv p (!decide (d = 0)) (E s.mem base) := by
  obtain hd16 : d < 16 := by rcases hd with h | h <;> omega_using [h]
  unfold vaddIf
  refine WP.seq (WP.mono (vtest_ok s ha hd16 h8) fun u ⟨uz, u3, uk, um⟩ => ?_)
  obtain ku : Keep base s u := ⟨uk.mono (by decide), by rw [um]; exact Outside2.refl _ _ _ _ _ _⟩
  refine WP.ite (!decide (d = 0)) (by rw [VG.Proof.X25519.Arm.eval_ne, uz])
    (fun hset => ?_) (fun hclr => ?_)
  · obtain hodd : d % 2 = 1 := by
      rcases hd with h | h
      · rw [decide_eq_true h] at hset; exact absurd hset (by decide)
      · exact h.1
    refine WP.seq (WP.mono (ventryLoad_ok (ku.scr hs) (um ▸ hbd) hd16 hodd u3 (um ▸ he))
      fun v ⟨kv, bv, ev⟩ => ?_)
    rw [show addAt 6 7 1 ++ vtake = (addF 6 7 1 ++ takeF).map FieldOp.impl from rfl]
    refine WP.mono (ops_ok (kv.scr (ku.scr hs)) bv (addF 6 7 1 ++ takeF)) fun w ⟨kw, bw, ew⟩ =>
      ⟨ku.trans (kv.trans kw), bw, ?_⟩
    rw [ew, ev, um, hset]; rfl
  · refine WP.block_nil ⟨ku, um ▸ hbd, ?_⟩
    rw [um, hclr]; rfl

/-- The test of a row: the top bit of `n - 114`. -/
theorem row_test : ∀ n < 456,
    ((BitVec.ofNat 32 n - 114) >>> 31 - 0 == (0 : BitVec 32)) = !decide (n < 114) := by
  decide +kernel

theorem vrowTest_ok (s : State) {n : Nat} (hn : n < 456) (hb : s.gpr .r11 = BitVec.ofNat 32 n) :
    WP isa (.block vrowTest) s fun u => u.z = !decide (n < 114) ∧ Keeps [.r3] s u ∧ u.mem = s.mem := by
  unfold vrowTest
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u1 v1 => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsr (by decide)) fun u2 v2 => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u3 v3 hz =>
    WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hz, v2.gpr, v1.gpr]; change ((s.gpr .r11 - 114) >>> 31 - 0 == (0 : BitVec 32)) = _
    rw [hb]; exact row_test n hn
  · exact rest_keeps ((v1.rest (ws := [.r3]) (by decide)).trans ((v2.rest (by decide)).trans (v3.rest _)))
  · rw [v3.mem, v2.mem, v1.mem]

theorem vcombDigit_ok {s : State} {base : Addr} (hs : Scr s base) {S : Nat} {D : Nat → Nat} {t : Nat}
    (ht : t < 114) (hD : ∀ i, D i < 16) (hb : s.gpr .r11 = BitVec.ofNat 32 t)
    (hbits : ∀ i < 456, s.mem (off base (VBITS + i)) = BitVec.ofNat 8 (pairD S D i)) :
    WP isa (.block vcombDigit) s fun u =>
      u.gpr .r5 = BitVec.ofNat 32 (combDigit S t) ∧ Keeps [.r7, .r5, .r3] s u ∧ u.mem = s.mem := by
  have hB : VBITS = 3104 := rfl
  obtain low : ∀ i, (BitVec.ofNat 8 (pairD S D i)).setWidth 32 &&& 1 =
      (BitVec.ofNat 8 ((S >>> i) &&& 1)).setWidth 32 := fun i =>
    (pair_test _ (bit_lt S i) _ (hD i)).2.2
  unfold vcombDigit
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u1 v1 => ?_
  obtain e7 : u1.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 t := by
    rw [v1.gpr]; change s.gpr .r0 + s.gpr .r11 = _; rw [hb]
  obtain ea : ∀ c, t + c < 8192 → State.addr (u1.gpr .r7 + BitVec.ofNat 32 c) = off base (c + t) := fun c hc => by
    rw [e7, Offset.add_add]
    exact (hs.ea hc).trans (congrArg (off base) (Nat.add_comm t c))
  obtain rd : ∀ c, t + c < 8192 → InRegions (s.rd ++ s.wr) (off base (c + t)) 1 := fun c hc =>
    hs.read (by omega_using [hc])
  refine VG.Proof.X25519.Arm.wp_ldrb (a := off base (VBITS + 342 + t)) (by omega_arith) (ea _ (by omega_arith))
    (by rw [v1.rd, v1.wr]; exact rd _ (by omega_arith)) fun u2 v2 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u3 v3 => ?_
  obtain r3 := ((v1.rest (ws := [.r7, .r5, .r3]) (by decide)).trans (v2.rest (by decide))).trans
    (v3.rest (by decide))
  obtain m3 : u3.mem = s.mem := by rw [v3.mem, v2.mem, v1.mem]
  obtain x3 : u3.gpr .r5 = (BitVec.ofNat 8 ((S >>> (t + 342)) &&& 1)).setWidth 32 := by
    rw [v3.gpr]; change u2.gpr .r5 &&& 1 = _
    rw [v2.gpr, v1.mem, show VBITS + 342 + t = VBITS + (t + 342) by omega_arith,
      hbits (t + 342) (by omega_using [ht])]
    exact low _
  obtain q3 : u3.gpr .r7 = u1.gpr .r7 := by rw [v3.other .r7 (by decide), v2.other .r7 (by decide)]
  refine VG.Proof.X25519.Arm.wp_ldrb (a := off base (VBITS + 228 + t)) (by omega_arith)
    (by rw [q3]; exact ea _ (by omega_arith))
    (by rw [r3.rd, r3.wr]; exact rd _ (by omega_arith)) fun u4 v4 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u5 v5 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun u6 v6 => ?_
  obtain r6 := ((r3.trans (v4.rest (by decide))).trans (v5.rest (by decide))).trans (v6.rest (by decide))
  obtain m6 : u6.mem = s.mem := by rw [v6.mem, v5.mem, v4.mem, m3]
  obtain q6 : u6.gpr .r7 = u1.gpr .r7 := by
    rw [v6.other .r7 (by decide), v5.other .r7 (by decide), v4.other .r7 (by decide), q3]
  obtain x6 : u6.gpr .r5 = (BitVec.ofNat 8 ((S >>> (t + 228)) &&& 1)).setWidth 32 +
      (BitVec.ofNat 8 ((S >>> (t + 342)) &&& 1)).setWidth 32 <<< 1 := by
    rw [v6.gpr]; change u5.gpr .r3 + u5.gpr .r5 <<< 1 = _
    rw [v5.gpr, v5.other .r5 (by decide), v4.other .r5 (by decide), x3]; change (u4.gpr .r3 &&& 1) + _ = _
    rw [v4.gpr, m3, show VBITS + 228 + t = VBITS + (t + 228) by omega_arith,
      hbits (t + 228) (by omega_using [ht]), low]
  refine VG.Proof.X25519.Arm.wp_ldrb (a := off base (VBITS + 114 + t)) (by omega_arith)
    (by rw [q6]; exact ea _ (by omega_arith))
    (by rw [r6.rd, r6.wr]; exact rd _ (by omega_arith)) fun u7 v7 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u8 v8 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun u9 v9 => ?_
  obtain r9 := ((r6.trans (v7.rest (by decide))).trans (v8.rest (by decide))).trans (v9.rest (by decide))
  obtain m9 : u9.mem = s.mem := by rw [v9.mem, v8.mem, v7.mem, m6]
  obtain q9 : u9.gpr .r7 = u1.gpr .r7 := by
    rw [v9.other .r7 (by decide), v8.other .r7 (by decide), v7.other .r7 (by decide), q6]
  obtain x9 : u9.gpr .r5 = (BitVec.ofNat 8 ((S >>> (t + 114)) &&& 1)).setWidth 32 +
      ((BitVec.ofNat 8 ((S >>> (t + 228)) &&& 1)).setWidth 32 +
        (BitVec.ofNat 8 ((S >>> (t + 342)) &&& 1)).setWidth 32 <<< 1) <<< 1 := by
    rw [v9.gpr]; change u8.gpr .r3 + u8.gpr .r5 <<< 1 = _
    rw [v8.gpr, v8.other .r5 (by decide), v7.other .r5 (by decide), x6]; change (u7.gpr .r3 &&& 1) + _ = _
    rw [v7.gpr, m6, show VBITS + 114 + t = VBITS + (t + 114) by omega_arith,
      hbits (t + 114) (by omega_using [ht]), low]
  refine VG.Proof.X25519.Arm.wp_ldrb (a := off base (VBITS + t)) (by omega_arith)
    (by rw [q9]; exact ea _ (by omega_arith))
    (by rw [r9.rd, r9.wr]; exact rd _ (by omega_arith)) fun u10 v10 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u11 v11 => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun u12 v12 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v12.gpr]; change u11.gpr .r3 + u11.gpr .r5 <<< 1 = _
    rw [v11.gpr, v11.other .r5 (by decide), v10.other .r5 (by decide), x9]; change (u10.gpr .r3 &&& 1) + _ = _
    rw [v10.gpr, m9, hbits t (by omega_using [ht]), low]
    exact digit_val _ (bit_lt S t) _ (bit_lt S (t + 114)) _ (bit_lt S (t + 228)) _ (bit_lt S (t + 342))
  · exact rest_keeps (((r9.trans (v10.rest (by decide))).trans (v11.rest (by decide))).trans
      (v12.rest (by decide)))
  · rw [v12.mem, v11.mem, v10.mem, m9]

theorem vcombIf_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {S : Nat}
    {D : Nat → Nat} {n : Nat} (hn : n < 456) (hD : ∀ i, D i < 16) (hb : s.gpr .r11 = BitVec.ofNat 32 n)
    (hbits : ∀ i < 456, s.mem (off base (VBITS + i)) = BitVec.ofNat 8 (pairD S D i)) :
    WP isa (vcombIf fv) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = combEnv (combDigit S n) (decide (n < 114)) (E s.mem base) := by
  unfold vcombIf
  refine WP.seq (WP.mono (vrowTest_ok s hn hb) fun u ⟨uz, uk, um⟩ => ?_)
  obtain ku : Keep base s u := ⟨uk.mono (by decide), by rw [um]; exact Outside2.refl _ _ _ _ _ _⟩
  obtain hsu := ku.scr hs
  refine WP.ite (decide (n < 114)) (by rw [VG.Proof.X25519.Arm.eval_ne, uz, Bool.not_not])
    (fun hrow => ?_) (fun hno => ?_)
  · obtain hlt : n < 114 := of_decide_eq_true hrow
    refine WP.seq (VG.Proof.X25519.Arm.WP.append (vcombDigit_ok (S := S) (D := D) hsu hlt hD
      (by rw [uk.1 _ (by decide)]; exact hb) (by rw [um]; exact hbits)) fun v ⟨vd, vk, vm⟩ => ?_)
    obtain kv : Keep base u v := ⟨vk.mono (by decide), by rw [vm]; exact Outside2.refl _ _ _ _ _ _⟩
    refine WP.mono (combSelect_ok (kv.scr hsu) (by rw [vm, um]; exact hbd) (combDigit_lt S n) vd)
      fun w ⟨kw, bw, ew⟩ => ?_
    rw [show addAt 8 9 10 ++ vtake = (addF 8 9 10 ++ takeF).map FieldOp.impl from rfl]
    refine WP.mono (ops_ok (kw.scr (kv.scr hsu)) bw (addF 8 9 10 ++ takeF)) fun x ⟨kx, bx, ex⟩ =>
      ⟨ku.trans (kv.trans (kw.trans kx)), bx, ?_⟩
    rw [ex, ew, vm, um, hrow]; rfl
  · refine WP.block_nil ⟨ku, um ▸ hbd, ?_⟩
    rw [um, hno]; rfl

theorem vdoubleAdd_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pairD S (vdigits K) t))
    (htab : TabOk base A s₀.mem) (hi : VBit base S K A s₀ s n) :
    WP isa (vdoubleAdd fv) s fun t => VInv base S K A s₀ t n ∧ t.z = decide (n = 0) := by
  have hs := hi.scr
  have hB : VBITS = 3104 := rfl
  have hA : ACC = 3584 := rfl
  obtain ha2 : (S >>> n) &&& 1 < 2 := bit_lt S n
  obtain hdn := Proof.Ed25519.Slide.digits_odd 456 K n
  obtain hj8 : (vdigits K n - 1) / 2 < 8 := by have := vdigits_lt K n; omega_using [this]
  have h8 : s.gpr .r8 = (BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * vdigits K n)).setWidth 32 := hi.r8
  unfold vdoubleAdd
  rw [show doubleAt 0 21 2 = (doubleF 0 21 2).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (ops_ok hs hi.bounded (doubleF 0 21 2)) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs
  obtain bits₂ : ∀ t < 456, s₂.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pairD S (vdigits K) t) :=
    fun t ht => by
      rw [k₂.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)
          (by rw [ofs_off' base (by omega_arith)]; omega_arith),
        hi.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)
          (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
      exact hbits t ht
  refine WP.seq (WP.mono (vcombIf_ok hs₂ bb₂ hn (vdigits_lt K) (by rw [k₂.regs.1 _ (by decide), hi.r11]) bits₂)
    fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  obtain hs₃ := k₃.scr hs₂
  obtain tab₃ : EntryOk base s₃.mem ((vdigits K n - 1) / 2) (oddMul A ((vdigits K n - 1) / 2)) :=
    (((htab _ hj8).keep hj8 hi.mem).keep hj8 k₂.mem).keep hj8 k₃.mem
  refine WP.seq (WP.mono (vaddIf_ok hs₃ bb₃ ha2 hdn
    (by rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), h8]) tab₃) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_)
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t vt hz =>
    WP.block_nil ?_
  obtain core := k₂.trans (k₃.trans k₄)
  obtain b₄ : s₄.gpr .r11 = BitVec.ofNat 32 n := by rw [core.regs.1 _ (by decide), hi.r11]
  obtain ee : E t.mem base = vstepEnv (decide (n < 114)) (combDigit S n) (!decide (vdigits K n = 0))
      (oddMul A ((vdigits K n - 1) / 2)) (E s.mem base) := by
    rw [vt.mem, e₄, e₃, e₂]; rfl
  obtain kk : ∀ j : Index, j.val = 10 ∨ j.val = 11 → E t.mem base j = E s.mem base j := fun j h => by
    rw [ee, vstepEnv_keep _ _ _ _ _ _ h]
  refine ⟨⟨core.scr hs |> fun h => ?_, vt.mem ▸ bb₄, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h.of_keeps (rest_keeps (vt.rest [])) (by decide)
  · refine hi.regs.trans ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [vt.gpr, core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))]
    · rw [vt.rd, core.regs.2.1]
    · rw [vt.wr, core.regs.2.2]
  · rw [vt.gpr, b₄]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [vt.mem, core.mem p hp hq]
  · rw [ee]; exact vcomb_step hn hi.rep hi.one hi.d
  · rw [kk 10 (by decide)]; exact hi.one
  · rw [kk 11 (by decide)]; exact hi.d
  · rw [hz, b₄]
    change (BitVec.ofNat 32 n - BitVec.ofNat 32 0 == 0) = _
    rw [BitVec.sub_zero]
    exact VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)

theorem vstep_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pairD S (vdigits K) t))
    (htab : TabOk base A s₀.mem) (hi : VInv base S K A s₀ s (n + 1)) :
    WP isa (vstep fv) s fun t => VInv base S K A s₀ t n ∧ t.z = decide (n = 0) :=
  WP.seq (WP.mono (vload_ok hn hbits hi) fun _ hb => vdoubleAdd_ok hn hbits htab hb)

theorem vloop_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbits : ∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pairD S (vdigits K) t))
    (htab : TabOk base A s₀.mem)
    (hi : ∀ s', s'.gpr .r11 = BitVec.ofNat 32 456 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VInv base S K A s₀ s' 456) :
    WP isa (vloop fv) s fun s' => VInv base S K A s₀ s' 0 := by
  unfold vloop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := vstep fv) (c := .ne) (Q := fun s' => VInv base S K A s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VInv base S K A s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (vstep_ok (by omega_arith) hbits htab hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_arith : ¬m = 0), Bool.not_false], m, by omega_arith,
      by omega_arith, by omega_arith, hi'⟩

end VG.Proof.Ed448.Arm

end

end


/-!
# Ed448 verification's equation on ARMv7: the whole function

`vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2, scratch = r3)`
returns `verifyEquation` of its inputs (`verifyEquation_main`), given the
reference computations' agreement with the specification (`RecoverOk`,
`VerifyEqCombOk`): the entry, the bits of `S` and `k`, the check of `S`, `R` and
`A` decoded and `A` negated (`vbefore_ok`, which states what the recoding
starts from, `VMid`, for the constant-time proof too), `k`'s digits and the
table of `-A`'s odd multiples (`vrecode_ok`, `vtable_ok`, which leave what the
loop starts from, `VReady`: `VMid.ready`), `Q = [S]B + [k](-A)` by the
loop, and the comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
inputs are read unchanged; the callee-saved registers are restored from the
working space, and the return address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqCombOk vcomb negPoint double verifyEquation_none)
open VG.Impl.X448.Arm (slot X2 BITS ACC TMP saved ld copy Op)
open VG.Spec.Ed448 (bytesAt decodeLE)

variable {fv : Bool}

/-! ## The bytes of the inputs -/

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [bytesAt]) fun i _ _ => ?_
  simp only [bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt114_len (m : Mem) (p : Addr) : (bytesAt m p 114).length = 57 + 57 := by
  simp [bytesAt]

/-- Bytes far from the working space, after writes only to it. -/
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (by have := hf i (List.mem_range.mp hi); omega_using [this]))

theorem outA {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (h1 : ACC ≤ o)
    (h2 : o + n ≤ ACC + 512) : Outside2 base 64 2816 ACC 512 m m' := fun p _ hq => h p (by omega_using [h1, h2, hq])

/-! ## The entry and the start -/

theorem ventry_eq : ventry = setupHead ++
    ([.mov .r12 (.reg .r1), .str .lr .r0 LR] : List Instr) := rfl

theorem ventry_ok {s : State} {base : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ t.gpr .r8 = s.gpr .r0 ∧ t.gpr .r12 = s.gpr .r1 ∧ t.gpr .r2 = s.gpr .r2 ∧
      Saved base s.gpr t.mem ∧ Outside base 0 (LR + 4) s.mem t.mem ∧ word t.mem base LR = s.gpr .lr ∧
      Keeps [.r10, .r0, .r6, .r8, .r12] s t := by
  rw [ventry_eq]
  refine VG.Proof.X25519.Arm.WP.append (setupHead_ok hc hw hn) fun v ⟨hsv, rv, _, svv, ov, kv⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun w hw' => ?_
  obtain k : Keeps [.r12] v w := rest_keeps (hw'.rest (by decide))
  obtain hsw := hsv.of_keeps k (by decide)
  refine VG.Proof.X25519.Arm.wp_str (a := off base LR) (by decide) (hsw.ea (by decide))
    (hsw.write (by decide)) fun t ht => WP.block_nil ?_
  have wv : w.mem = v.mem := hw'.mem
  obtain ot : Outside base LR 4 v.mem t.mem := by rw [ht.mem, wv]; exact writeW_outside _ _ _ (by decide)
  obtain kt : Keeps [] w t := ⟨fun r _ => by rw [ht.gpr], ht.rd, ht.wr⟩
  refine ⟨hsw.of_keeps kt (by decide), ?_, ?_, ?_, ?_, ?_, ?_,
    (kv.mono (by decide)).trans ((k.mono (by decide)).trans (kt.mono (by decide)))⟩
  · rw [ht.gpr, hw'.other _ (by decide), rv]
  · rw [ht.gpr, hw'.gpr, kv.1 _ (by decide)]
  · rw [ht.gpr, hw'.other _ (by decide), kv.1 _ (by decide)]
  · exact svv.outside ot (by decide)
  · exact (ov.mono (by decide) (by decide)).trans (ot.mono (by decide) (by decide))
  · show t.mem.readW (off base LR) 32 = _
    rw [ht.mem, Mem.readW_writeW_self32, hw'.other _ (by decide), kv.1 _ (by decide)]

theorem vstart_eq : vstart = .mov .r10 (.imm 0) :: (sCheck ++ (initSlots ++
    copy (slot (21 : Index).val) (slot (1 : Index).val))) := by
  simp only [vstart, List.append_assoc]; rfl

/-- `BAD = 0`, the check of `S` (at `sq`), and the slots initialized: `Q` the
neutral point, `B`, `1` in slot 10 and `d`. -/
theorem vstart_ok {s : State} {base sq : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r12) + BitVec.ofNat 64 57 = sq) (hfit : (s.gpr .r12).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 j)) :
    WP isa (.block vstart) s fun t =>
      CKeep base s t ∧ t.gpr .r12 = s.gpr .r12 ∧ BoundedEnv t.mem base ∧
      BadUpd (decodeLE (bytesAt s.mem sq 57) < Spec.Ed448.L) 0 (t.gpr .r10) ∧
      pt (E t.mem base) 0 21 2 = Spec.Ed448.identity ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 10 = 1 ∧ E t.mem base 11 = Spec.Ed448.d := by
  rw [vstart_eq]
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  obtain hsu := hs.of_upd hu (by decide) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (sCheck_ok hsu (by rw [hu.other _ (by decide)]; exact hq)
    (by rw [hu.other _ (by decide)]; exact hfit) (by rw [hu.rd, hu.wr]; exact hr) hd)
    fun v ⟨bv, ov, kv⟩ => ?_
  obtain hsv := hsu.of_keeps kv (by decide)
  refine VG.Proof.X25519.Arm.WP.append (initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  obtain hsw := hsv.of_keeps kw (by decide)
  refine WP.mono (copyE3 hsw (initSlots_bounded lw) 21 1) fun t ⟨kt, k3, bt, et⟩ => ?_
  obtain ev : ∀ i : Index, i ≠ 21 → E t.mem base i = Proof.X448.toFe (initVal i.val) := fun i hi => by
    rw [et, opCopy, Function.update_of_ne hi, initSlots_E lw i]
  obtain e21 : E t.mem base 21 = Proof.X448.toFe (initVal 1) := by
    rw [et, opCopy, Function.update_self, initSlots_E lw 1]; rfl
  refine ⟨⟨?_, ?_⟩, ?_, bt, ?_, ?_, ?_, ?_, ?_⟩
  · refine (rest_keeps (hu.rest (ws := .r10 :: .r11 :: workRegs) (by decide))).trans
      ((kv.mono ?_).trans ((kw.mono ?_).trans (kt.regs.mono ?_))) <;> decide
  · rw [← hu.mem]
    exact ((outA ov (by decide) (by decide)).trans (outC ow (by decide) (by decide))).trans kt.mem
  · rw [k3.1 _ (by decide), kw.1 _ (by decide), kv.1 _ (by decide), hu.other _ (by decide)]
  · rw [hu.gpr] at bv
    rw [kt.regs.1 .r10 (by decide), kw.1 .r10 (by decide), ← hu.mem]
    exact bv
  · show (⟨E t.mem base 0, E t.mem base 21, E t.mem base 2⟩ : Spec.Ed448.Point) = _
    rw [ev 0 (by decide), e21, ev 2 (by decide), show ((0 : Index) : Nat) = 0 from rfl,
      show ((2 : Index) : Nat) = 2 from rfl, show initVal 0 = Spec.Ed448.identity.X.val from rfl,
      show initVal 1 = Spec.Ed448.identity.Y.val from rfl, show initVal 2 = Spec.Ed448.identity.Z.val from rfl,
      Proof.X448.toFe_self, Proof.X448.toFe_self, Proof.X448.toFe_self]
  · show (⟨E t.mem base 8, E t.mem base 9, E t.mem base 10⟩ : Spec.Ed448.Point) = _
    rw [ev 8 (by decide), ev 9 (by decide), ev 10 (by decide), show ((8 : Index) : Nat) = 8 from rfl,
      show ((9 : Index) : Nat) = 9 from rfl, show ((10 : Index) : Nat) = 10 from rfl,
      show initVal 8 = Spec.Ed448.basePoint.X.val from rfl, show initVal 9 = Spec.Ed448.basePoint.Y.val from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self, Proof.X448.toFe_self,
      Proof.X448.toFe_self]
  · rw [ev 10 (by decide), show ((10 : Index) : Nat) = 10 from rfl,
      show initVal 10 = Spec.Ed448.basePoint.Z.val from rfl, Proof.X448.toFe_self]; rfl
  · rw [ev 11 (by decide), show ((11 : Index) : Nat) = 11 from rfl, show initVal 11 = Spec.Ed448.d.val from rfl,
      Proof.X448.toFe_self]

/-! ## The whole function -/

/-- The precondition of `vg_ed448_verify_equation`, by name. -/
structure VerifyPre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r0), 57⟩, ⟨State.addr (s.gpr .r1), 114⟩, ⟨State.addr (s.gpr .r2), 57⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r3), 8192⟩]
  pk_ws : (⟨State.addr (s.gpr .r0), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  sig_ws : (⟨State.addr (s.gpr .r1), 114⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  ch_ws : (⟨State.addr (s.gpr .r2), 57⟩ : Region).Disjoint ⟨State.addr (s.gpr .r3), 8192⟩
  f0 : (s.gpr .r0).toNat + 57 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 114 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32
  f3 : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32

theorem BadUpd.zero {P : Prop} {b : BitVec 32} (h : BadUpd P 0 b) : (b = 0 ↔ P) ∧ b.toNat < 65536 := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  have e : (0 : BitVec 32) ||| c = c := BitVec.zero_or
  rw [e]
  exact ⟨hp, hc⟩

theorem bits_kept {base : Addr} {m m' : Mem} (h : DFrame base m m') :
    ∀ t < 456, m' (off base (VBITS + t)) = m (off base (VBITS + t)) := fun t ht =>
  h _ (by rw [ofs_off' base (by simp only [VBITS]; omega_using [ht])]; simp only [VBITS]; omega_using [])
    (by rw [ofs_off' base (by simp only [VBITS]; omega_using [ht])]; simp only [VBITS, ACC]; omega_using [ht])

/-- The link register's word, above `RY`, is kept by writes below `VBITS` or of the bits. -/
theorem lr_kept {base : Addr} {m m' : Mem} (h : DFrame base m m') : word m' base LR = word m base LR :=
  h.word (by decide) (by decide) (by decide)

/-- The state `t` before `k`'s digits and the table, from the state `s` the function was entered
in: the bits of `S` and `k`, `Q` the neutral point, `B`, `-A` and `d` in their slots, `R` at
`RX` and `RY`, the checks so far in `BAD`, and the saved registers. -/
structure VMid (s : State) (base pk sig : Addr) (S K : Nat) (t : State) : Prop where
  scr : Scr t base
  bounded : BoundedEnv t.mem base
  bits : ∀ i < 456, t.mem (off base (VBITS + i)) = BitVec.ofNat 8 (pair2 S K i)
  q : pt (E t.mem base) 0 21 2 = Spec.Ed448.identity
  b : pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : E t.mem base 11 = Spec.Ed448.d
  bad : BadUpd (S < Spec.Ed448.L ∧ (Spec.Ed448.decodePoint (bytesAt s.mem sig 57)).isSome = true ∧
    (Spec.Ed448.decodePoint (bytesAt s.mem pk 57)).isSome = true) 0 (t.gpr .r10)
  na : ∀ a, Spec.Ed448.decodePoint (bytesAt s.mem pk 57) = some a → pt (E t.mem base) 6 7 10 = negPoint a
  r : ∀ r, Spec.Ed448.decodePoint (bytesAt s.mem sig 57) = some r →
    F t.mem base RX = r.X ∧ F t.mem base RY = r.Y ∧ r.Z = 1
  rx : Bounded t.mem base RX
  ry : Bounded t.mem base RY
  saved : Saved base s.gpr t.mem
  lr : word t.mem base LR = s.gpr .lr

/-- The slots after the recoding, which writes only the bytes at `VBITS`. -/
theorem VMid.coded {s : State} {base pk sig : Addr} {S K : Nat} {t x : State} (hm : VMid s base pk sig S K t)
    (hk : Keeps recRegs t x) (ho : Outside base VBITS 456 t.mem x.mem) :
    Scr x base ∧ BoundedEnv x.mem base ∧ E x.mem base = E t.mem base := by
  obtain sl : ∀ i : Index, slot i.val + 112 ≤ VBITS := fun i => by
    have := i.isLt
    simp only [slot, VBITS]
    omega_arith
  refine ⟨hm.scr.of_keeps hk (by decide), fun i j hj => ?_, funext fun i => ?_⟩
  · rw [ho.limbs (Or.inl (sl i)) (by have := sl i; simp only [VBITS] at this; omega_arith) hj]
    exact hm.bounded i j hj
  · exact congrArg Proof.X448.toFe (ho.fe (Or.inl (sl i)) (by have := sl i; simp only [VBITS] at this; omega_arith))

/-- The state `y` before the loop over the bits, from the state `s` the function was entered in:
the bits of `S` and the digits of `k`, `Q` the neutral point, the table of the odd multiples of
`A`, which is `-A` of the public key, `d`, `R` at `RX` and `RY`, the checks so far in `BAD`, and
the saved registers. -/
structure VReady (s : State) (base pk sig : Addr) (S K : Nat) (A : Spec.Ed448.Point) (y : State) : Prop where
  scr : Scr y base
  bounded : BoundedEnv y.mem base
  bits : ∀ i < 456, y.mem (off base (VBITS + i)) = BitVec.ofNat 8 (pairD S (vdigits K) i)
  tab : TabOk base A y.mem
  q : pt (E y.mem base) 0 21 2 = Spec.Ed448.identity
  one : E y.mem base 10 = 1
  d : E y.mem base 11 = Spec.Ed448.d
  bad : BadUpd (S < Spec.Ed448.L ∧ (Spec.Ed448.decodePoint (bytesAt s.mem sig 57)).isSome = true ∧
    (Spec.Ed448.decodePoint (bytesAt s.mem pk 57)).isSome = true) 0 (y.gpr .r10)
  na : ∀ a, Spec.Ed448.decodePoint (bytesAt s.mem pk 57) = some a → A = negPoint a
  r : ∀ r, Spec.Ed448.decodePoint (bytesAt s.mem sig 57) = some r →
    F y.mem base RX = r.X ∧ F y.mem base RY = r.Y ∧ r.Z = 1
  rx : Bounded y.mem base RX
  ry : Bounded y.mem base RY
  saved : Saved base s.gpr y.mem
  lr : word y.mem base LR = s.gpr .lr

/-- The state before the loop, from the one before the recoding (`t`), the recoding's (`x`) and
the table's. -/
theorem VMid.ready {s : State} {base pk sig : Addr} {S K : Nat} {t x y : State} (hm : VMid s base pk sig S K t)
    (hk : Keeps recRegs t x) (ho : Outside base VBITS 456 t.mem x.mem)
    (hb : ∀ q < 456, x.mem (off base (VBITS + q)) = BitVec.ofNat 8 (pairD S (vdigits K) q))
    (hy : Tabled base x y) : VReady s base pk sig S K (pt (E t.mem base) 6 7 10) y := by
  have hB : VBITS = 3104 := rfl
  have hA : ACC = 3584 := rfl
  obtain ⟨-, -, ex⟩ := hm.coded hk ho
  obtain lim : ∀ d, 2880 ≤ d → d + 112 ≤ VBITS → ∀ i < 28, limbs y.mem base d i = limbs t.mem base d i :=
    fun d h1 h2 i hi => by
      rw [show limbs y.mem base d i = limbs x.mem base d i from congrArg BitVec.toNat
        (hy.mem.word (Or.inr (by omega_using [h1])) (Or.inl (by omega_using [h2, hi, hB, hA]))
          (by omega_using [h2, hi, hB])),
        ho.limbs (Or.inl h2) (by omega_using [h2, hB]) hi]
  refine ⟨hy.scr, hy.bounded, fun i hi => ?_, ?_, hy.q, hy.one, hy.d, ?_, hm.na, fun r hr => ?_, fun i hi => ?_,
    fun i hi => ?_, ?_, ?_⟩
  · rw [hy.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact hb i hi
  · rw [← ex]; exact hy.tab
  · rw [hy.regs.1 .r10 (by decide), hk.1 .r10 (by decide)]; exact hm.bad
  · obtain ⟨rx, ry, rz⟩ := hm.r r hr
    exact ⟨(congrArg Proof.X448.toFe (valN_congr (lim RX (by decide) (by decide)))).trans rx,
      (congrArg Proof.X448.toFe (valN_congr (lim RY (by decide) (by decide)))).trans ry, rz⟩
  · rw [lim RX (by decide) (by decide) i hi]; exact hm.rx i hi
  · rw [lim RY (by decide) (by decide) i hi]; exact hm.ry i hi
  · exact (hm.saved.outside ho (by decide)).outside2 hy.mem (by decide) (by decide)
  · rw [hy.mem.word (Or.inr (by decide)) (Or.inl (by decide)) (by decide),
      ho.word (Or.inr (by decide)) (by decide)]
    exact hm.lr

/-- The loop's invariant holds once the counter is set. -/
theorem VReady.inv {s : State} {base pk sig : Addr} {S K : Nat} {A : Spec.Ed448.Point} {t t' : State}
    (hm : VReady s base pk sig S K A t)
    (h1 : t'.gpr .r11 = BitVec.ofNat 32 456) (h2 : ∀ r, r ≠ .r11 → t'.gpr r = t.gpr r)
    (h3 : t'.mem = t.mem) (h4 : t'.rd = t.rd) (h5 : t'.wr = t.wr) :
    VInv base S K A t t' 456 := by
  have k' : Keeps (.r8 :: .r11 :: workRegs) t t' :=
    ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_of_mem _ List.mem_cons_self)), h4, h5⟩
  refine ⟨hm.scr.of_keeps k' (by decide), h3 ▸ hm.bounded, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_⟩
  · rw [h3, Nat.sub_self, hm.q]; rfl
  · rw [h3]; exact hm.one
  · rw [h3, hm.d]

/-- What comes before `k`'s digits: the entry, the bits of `S` and `k`, the check of `S`, `R` and
`A` decoded, and `A` negated. -/
theorem vbefore_ok (hR : RecoverOk) {s : State} (h : VerifyPre s) {base pk sig ch : Addr}
    (hbase : State.addr (s.gpr .r3) = base) (hpk : State.addr (s.gpr .r0) = pk)
    (hsig : State.addr (s.gpr .r1) = sig) (hch : State.addr (s.gpr .r2) = ch) {S K : Nat}
    (hS : decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) = S) (hK : decodeLE (bytesAt s.mem ch 57) = K) :
    WP isa (vbefore fv) s fun t => VMid s base pk sig S K t := by
  obtain hw₀ : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [h.wr, hbase]; simp
  obtain rpk : ∀ j < 57, InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨pk, 57⟩, by rw [h.rd, hpk]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain rsg : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain rS : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp,
      by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain rch : ∀ j < 57, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨ch, 57⟩, by rw [h.rd, hch]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  obtain fpk : ∀ j < 57, 8192 ≤ ofs base (pk + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hpk ▸ hbase ▸ h.pk_ws) hj (by decide)
  obtain fsg : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega_using [hj]) (by decide)
  obtain fS : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) := fun j hj => by
    rw [Offset.add_add]; exact far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega_using [hj]) (by decide)
  obtain fch : ∀ j < 57, 8192 ≤ ofs base (ch + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hch ▸ hbase ▸ h.ch_ws) hj (by decide)
  unfold vbefore
  -- The entry.
  refine WP.seq (WP.mono (ventry_ok hbase hw₀ h.f3) fun s1 ⟨hs1, r81, r121, r21, sv1, o1, lr1, k1⟩ => ?_)
  obtain rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [k1.2.1, k1.2.2]
  obtain O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `S` and `k`.
  refine WP.seq (WP.mono (vbits_ok hs1 (sq := sig + BitVec.ofNat 64 57) (kq := ch)
    (by rw [r121, hsig]) (by rw [r21, hch]) (by rw [r121]; exact h.f1) (by rw [r21]; exact h.f2)
    (by rw [rr1]; exact rS) (by rw [rr1]; exact rch) fS fch) fun s2 ⟨g2, rd2, wr2, o2, bits2⟩ => ?_)
  rw [far_bytes O1 fS, hS, far_bytes O1 fch, hK] at bits2
  obtain hs2 : Scr s2 base := hs1.of_keeps ⟨g2, rd2, wr2⟩ (by decide)
  obtain rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rr1]
  obtain O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  obtain r122 : s2.gpr .r12 = s.gpr .r1 := by rw [g2 _ (by decide), r121]
  obtain r82 : s2.gpr .r8 = s.gpr .r0 := by rw [g2 _ (by decide), r81]
  -- `BAD = 0`, the check of `S`, and the slots.
  refine WP.seq (WP.mono (vstart_ok hs2 (sq := sig + BitVec.ofNat 64 57) (by rw [r122, hsig])
    (by rw [r122]; exact h.f1) (by rw [rr2]; exact rS) fS) fun s3 ⟨k3, r12s3, b3, c3, q3, p3, h103, h113⟩ => ?_)
  rw [far_bytes O2 fS, hS] at c3
  obtain hs3 := k3.scr hs2
  obtain rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [k3.regs.2.1, k3.regs.2.2, rr2]
  obtain O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (k3.mem.whole (by decide) (by decide))
  obtain r83 : s3.gpr .r8 = s.gpr .r0 := by rw [k3.regs.1 _ (by decide), r82]
  obtain r123 : s3.gpr .r12 = s.gpr .r1 := by rw [r12s3, r122]
  -- `R` and `A`.
  obtain inR : DecIn s3 base sig .r12 :=
    ⟨by rw [r123, hsig], by rw [r123]; have := h.f1; omega_using [this], by rw [rr3]; exact rsg, fsg⟩
  obtain inA : DecIn s3 base pk .r8 := ⟨by rw [r83, hpk], by rw [r83]; exact h.f0, by rw [rr3]; exact rpk, fpk⟩
  refine WP.seq (WP.mono (vdecode_ok hR hs3 b3 inR inA h103 h113)
    fun s4 ⟨k4, f4, b4, c4, v4, w4, bx4, by4, e4⟩ => ?_)
  rw [far_bytes O3 fsg, far_bytes O3 fpk] at c4
  rw [far_bytes O3 fsg] at w4
  rw [far_bytes O3 fpk] at v4
  obtain hs4 := hs3.of_keeps k4 (by decide)
  -- `-A`.
  rw [show ([.sub (slot 6) (slot 0) (slot 6)] : List Op) = ([.sub 6 0 6] : List FieldOp).map FieldOp.impl
    from rfl]
  refine WP.mono (ops_ok hs4 b4 [.sub 6 0 6]) fun s5 ⟨k5, b5, e5⟩ => ?_
  obtain hs5 := k5.scr hs4
  obtain k5' : ∀ i : Index, i ≠ 6 → E s5.mem base i = E s4.mem base i := fun i hi => by
    rw [e5]; exact Function.update_of_ne hi _ _
  obtain k43 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21 →
      E s5.mem base i = E s3.mem base i := fun i hi => by
    rw [k5' i (fun h => by subst h; omega_using [hi]), e4 i (fun h => by subst h; omega_using [hi]) (fun h => by subst h; omega_using [hi])
      (by omega_using [hi])]
  obtain lx5 : ∀ i < 28, limbs s5.mem base RX i = limbs s4.mem base RX i := fun i hi =>
    limbs_mid k5.mem (by decide) (by decide) hi
  obtain ly5 : ∀ i < 28, limbs s5.mem base RY i = limbs s4.mem base RY i := fun i hi =>
    limbs_mid k5.mem (by decide) (by decide) hi
  refine ⟨hs5, b5, fun t ht => ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_, fun i hi => ?_,
    fun i hi => ?_, ?_, ?_⟩
  · rw [bits_kept ((Outside2.widen k5.mem).mono (by decide) (by decide)) t ht, bits_kept f4 t ht,
      bits_kept ((Outside2.widen k3.mem).mono (by decide) (by decide)) t ht]
    exact bits2 t ht
  · rw [pt_congr' (k43 0 (by decide)) (k43 21 (by decide)) (k43 2 (by decide)), q3]
  · rw [pt_congr' (k43 8 (by decide)) (k43 9 (by decide)) (k43 10 (by decide)), p3]
  · rw [k43 11 (by decide), h113]
  · rw [k5.regs.1 .r10 (by decide)]
    exact c3.trans c4
  · obtain ⟨ax, ay, az⟩ := v4 a ha
    obtain e40 : E s4.mem base 0 = 0 := by
      rw [e4 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X q3
    obtain e410 : E s4.mem base 10 = 1 := by
      rw [e4 10 (by decide) (by decide) (by decide)]; exact h103
    show (⟨E s5.mem base 6, E s5.mem base 7, E s5.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
    rw [show E s5.mem base 6 = E s4.mem base 0 - E s4.mem base 6 by rw [e5]; rfl,
      k5' 7 (by decide), k5' 10 (by decide), e40, ax, ay, e410, az]
  · obtain ⟨rx, ry, rz⟩ := w4 r hr
    exact ⟨(congrArg Proof.X448.toFe (valN_congr lx5)).trans rx,
      (congrArg Proof.X448.toFe (valN_congr ly5)).trans ry, rz⟩
  · rw [lx5 i hi]; exact bx4 i hi
  · rw [ly5 i hi]; exact by4 i hi
  · exact (((sv1.outside o2 (by decide)).outside2 k3.mem (by decide) (by decide)).outside2 f4 (by decide)
      (by decide)).outside2 k5.mem (by decide) (by decide)
  · rw [lr_kept ((Outside2.widen k5.mem).mono (by decide) (by decide)), lr_kept f4,
      lr_kept ((Outside2.widen k3.mem).mono (by decide) (by decide)), o2.word (by decide) (by decide), lr1]

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqCombOk) {s : State} (h : VerifyPre s) :
    WP isa (verifyEquation fv) s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.gpr .r0 = if Spec.Ed448.verifyEquation (bytesAt s.mem (State.addr (s.gpr .r0)) 57)
        (bytesAt s.mem (State.addr (s.gpr .r1)) 114) (bytesAt s.mem (State.addr (s.gpr .r2)) 57)
        then 1 else 0 := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s.gpr .r3) = b := ⟨_, rfl⟩
  obtain ⟨pk, hpk⟩ : ∃ p, State.addr (s.gpr .r0) = p := ⟨_, rfl⟩
  obtain ⟨sig, hsig⟩ : ∃ p, State.addr (s.gpr .r1) = p := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ p, State.addr (s.gpr .r2) = p := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) = S := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s.mem ch 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  refine WP.seq (WP.mono (vbefore_ok hR h hbase hpk hsig hch hS hK) fun s3 M₀ => ?_)
  -- `k`'s digits, and the table.
  refine WP.seq (WP.mono (vrecode_ok M₀.scr M₀.bits) fun s4 ⟨k4, o4, d4⟩ => ?_)
  obtain ⟨hs4, b4, e4⟩ := M₀.coded k4 o4
  refine WP.seq (WP.mono (vtable_ok hs4 b4 (by rw [e4]; exact congrArg Spec.Ed448.Point.Z M₀.b)
    (by rw [e4]; exact M₀.d)) fun s5 T5 => ?_)
  obtain M := M₀.ready k4 o4 d4 T5
  -- The loop.
  refine WP.seq (WP.mono (vloop_ok (s₀ := s5) M.bits M.tab
    (fun s' h1 h2 h3 h4 h5 => M.inv h1 h2 h3 h4 h5)) fun s6 I6 => ?_)
  -- `R` into slots 8–9.
  have hs6 := I6.scr
  obtain lx6 : ∀ i < 28, limbs s6.mem base RX i = limbs s5.mem base RX i := fun i hi =>
    limbs_mid I6.mem (by decide) (by decide) hi
  obtain ly6 : ∀ i < 28, limbs s6.mem base RY i = limbs s5.mem base RY i := fun i hi =>
    limbs_mid I6.mem (by decide) (by decide) hi
  obtain h106 : E s6.mem base 10 = 1 := I6.one
  unfold vafter
  refine WP.seq (WP.mono (vR_ok hs6 I6.bounded (fun i hi => by rw [lx6 i hi]; exact M.rx i hi)
    (fun i hi => by rw [ly6 i hi]; exact M.ry i hi)) fun s7 ⟨k7, b7, e78, e79, e7⟩ => ?_)
  obtain hs7 := k7.scr hs6
  -- `BAD`.
  obtain c6 : BadUpd (S < Spec.Ed448.L ∧ (Spec.Ed448.decodePoint (bytesAt s.mem sig 57)).isSome = true ∧
      (Spec.Ed448.decodePoint (bytesAt s.mem pk 57)).isSome = true) 0 (s7.gpr .r10) := by
    rw [k7.regs.1 .r10 (by decide), I6.regs.1 .r10 (by decide)]; exact M.bad
  -- The comparison.
  obtain sv7 : Saved base s.gpr s7.mem :=
    (M.saved.outside2 I6.mem (by decide) (by decide)).outside2 k7.mem (by decide) (by decide)
  obtain lr7 : word s7.mem base LR = s.gpr .lr := by
    rw [lr_kept ((Outside2.widen k7.mem).mono (by decide) (by decide)),
      lr_kept ((Outside2.widen I6.mem).mono (by decide) (by decide)), M.lr]
  have z7 := c6.zero
  refine WP.mono (vfinish_ok hs7 b7 sv7 z7.2) fun t ⟨rt, st, lt, gt⟩ => ⟨fun r hr => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact st 0 (by decide)
    · exact st 1 (by decide)
    · exact st 2 (by decide)
    · exact st 3 (by decide)
    · exact st 4 (by decide)
    · exact st 5 (by decide)
    · exact st 6 (by decide)
    · exact st 7 (by decide)
    · rw [lt, lr7]
  · rw [rt, hpk, hsig, hch]
    refine if_congr ?_ rfl rfl
    rw [z7.1]
    cases ha : Spec.Ed448.decodePoint (bytesAt s.mem pk 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd h.1.2.2 (by simp), fun h => absurd h (by decide)⟩
    | some a =>
      cases hr : Spec.Ed448.decodePoint ((bytesAt s.mem sig 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hr)]
        rw [bytesAt_take57] at hr
        exact ⟨fun h => absurd h.1.2.1 (by rw [hr]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have hr' := hr
        rw [bytesAt_take57] at hr'
        obtain ⟨rx, ry, rz⟩ := M.r r hr'
        obtain hQ : pt (E s7.mem base) 0 21 2 = vcomb S K (negPoint a) 456 := by
          rw [pt_congr' (e7 0 (by decide) (by decide)) (e7 21 (by decide) (by decide))
            (e7 2 (by decide) (by decide)), I6.rep, ← M.na a ha]
        obtain hRR : pt (E s7.mem base) 8 9 10 = r := by
          show (⟨E s7.mem base 8, E s7.mem base 9, E s7.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [e78, e79, show F s6.mem base RX = F s5.mem base RX from
              congrArg Proof.X448.toFe (valN_congr lx6),
            show F s6.mem base RY = F s5.mem base RY from congrArg Proof.X448.toFe (valN_congr ly6), rx, ry,
            e7 10 (by decide) (by decide), h106, ← rz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hr, hQ, hRR,
          bytesAt_drop57, hS, hK, hr']
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.Arm

end

end

/-!
# Ed448 verification's equation on ARMv7: `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqCombOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean` and `CombFacts.lean`), and constant time.

The code branches on the bits of `S` and of the challenge, which the contract
declares public, so its constant time relates two runs (`RelCT`):

* what comes before `k`'s digits (`vbefore`) and after the loop (`vafter`) is
  constant time by taint tracking, from the arguments and from the working
  space's address: their only branches are on loop counters, and every
  address is an argument plus a constant or a counter;
* the two runs enter the recoding with the same bits of `S` and `k` at
  `VBITS`, as correctness says (`vbefore_ok`), and each of its steps leaves
  both in the same state of the recoding (`recBit_ok`), so both branch the
  same way on the window in hand, and the bytes they store are at the count
  of bits and at the window's address, the same in both;
* the table's code is constant time by taint tracking from the working
  space's address: its loop is on the entry's address, a counter;
* the two runs enter the loop with the same bits of `S` and digits of `k` at
  `VBITS`, and each iteration keeps the loop's invariant in both (`vload_ok`,
  `vdoubleAdd_ok`), so both load the same byte into `r8`; from there the
  doubling, the comb's row (in the last 114 bits, a test of the counter; its
  selection scans the whole table), the test of `r8`, the load of the digit's
  entry, whose address is `r8`'s, and the addition are constant time by taint
  tracking, with `r8` and the counter public, which the field functions never
  write.

With `umaal` the taint tracking is `taintU`'s (`ctRegsU`), on the code itself.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (RecoverOk VerifyEqCombOk vdigits)
open VG.Proof.Ed25519.Arm (CT ctRegs ctBoth)
open VG.Spec.Ed448 (bytesAt decodeLE)

variable {fv : Bool}

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqCombOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa (verifyEquation fv) s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verifyEquation_main hR hE (VerifyPre.of hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

/-! ## Constant time -/

/-- The working space's address is the same in two runs with the same working space. -/
theorem scr_agree {base : Addr} {x y : State} (hx : Scr x base) (hy : Scr y base) :
    x.gpr .r0 = y.gpr .r0 := by
  apply BitVec.eq_of_toNat_eq
  rw [← VG.Proof.X25519.Arm.addr_toNat, ← VG.Proof.X25519.Arm.addr_toNat, hx.r0, hy.r0]

/-- A run before `k`'s digits: the state the function was entered in is some state. -/
def Start (base : Addr) (S K : Nat) (x : State) : Prop := ∃ s pk sig, VMid s base pk sig S K x

/-- A run of the recoding after `i` bits, from a run before it. -/
def RecRun (base : Addr) (S K i : Nat) (x : State) : Prop :=
  ∃ t, Start base S K t ∧ Keeps recRegs t x ∧ Outside base VBITS 456 t.mem x.mem ∧ RecAt base S K i x

/-- A run with `k`'s digits, from a run before them. -/
def Coded (base : Addr) (S K : Nat) (x : State) : Prop :=
  ∃ t, Start base S K t ∧ Keeps recRegs t x ∧ Outside base VBITS 456 t.mem x.mem ∧
    ∀ q < 456, x.mem (off base (VBITS + q)) = BitVec.ofNat 8 (pairD S (vdigits K) q)

/-- A run before the loop, with the digits and the table. -/
def Ready (base : Addr) (S K : Nat) (x : State) : Prop := ∃ s pk sig A, VReady s base pk sig S K A x

/-- A run before bit `n - 1`: the loop's invariant, from some state before the loop with the
bits of `S`, the digits of `k` and the table. -/
def Run (base : Addr) (S K n : Nat) (x : State) : Prop :=
  ∃ A s₀, (∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pairD S (vdigits K) t)) ∧
    TabOk base A s₀.mem ∧ VInv base S K A s₀ x n

/-- A run with the byte of bit `n` loaded. -/
def Loaded (base : Addr) (S K n : Nat) (x : State) : Prop :=
  ∃ A s₀, (∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pairD S (vdigits K) t)) ∧
    TabOk base A s₀.mem ∧ VBit base S K A s₀ x n

/-- `ctRegs`, by the analysis of the code without its offsets (`Taint.check_eraseOff`). -/
theorem ctRegsErased {P : State → State → Prop} {c c' : Prog isa} (rs : List Reg)
    (hp : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) (he : Arm.Code.eraseOff c = c')
    {hint : VG.Taint.Hint taint.T} (hc : (taint.check (Taint.ofRegs rs) c' hint).isSome = true) :
    CT P c (fun _ _ => True) :=
  ctRegs rs hp (hint := hint) (Taint.check_eraseOff c hint (Taint.noBase_ofRegs rs) ▸ he ▸ hc)

/-- `ctRegs`, by the analysis of code with `umaal` (`taintU`). -/
theorem ctRegsU {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hp : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r)
    {hint : VG.Taint.Hint taintU.T} (hc : (taintU.check (Taint.ofRegs rs) c hint).isSome = true) :
    CT P c (fun _ _ => True) :=
  RelCT.taint (A := taintU) (Taint.ofRegs rs) (fun x y h => Taint.agree_ofRegs (hp x y h)) hc

theorem vbefore_ct :
    CT (fun x y => verifyEquationLocal.pre x ∧ verifyEquationLocal.pre y ∧ verifyEquationLocal.pub x y)
      (vbefore fv) (fun _ _ => True) := by
  obtain hp : ∀ x y, verifyEquationLocal.pre x ∧ verifyEquationLocal.pre y ∧ verifyEquationLocal.pub x y →
      ∀ r ∈ [Reg.r0, .r1, .r2, .r3], x.gpr r = y.gpr r := by
    intro x y h r hr
    obtain ⟨h0, h1, h2, h3, _⟩ := h.2.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3]
  cases fv
  · exact ctRegsErased [.r0, .r1, .r2, .r3] hp (c' := vbeforeErased) rfl (by native_taint_decide)
  · exact ctRegsU [.r0, .r1, .r2, .r3] hp (by taint_decide)

/-! ### `k`'s digits -/

theorem recInit_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Start base S K x ∧ Start base S K y) (.block recInit)
      (fun x y => RecRun base S K 0 x ∧ RecRun base S K 0 y) := by
  apply ctBoth
  · apply ctRegs [] _ (by native_taint_decide)
    exact fun _ _ _ r hr => (List.not_mem_nil hr).elim
  · rintro x ⟨s, pk, sig, M⟩
    exact WP.mono (recInit_ok M.scr M.bits) fun u ⟨uk, um, ua⟩ =>
      ⟨x, ⟨s, pk, sig, M⟩, uk, um ▸ Outside.refl _ _ _ _, ua⟩

/-- One bit: the branch is on the window in hand, and the stores are at the count of bits and at
the window's address, all the same in both runs, which are in the same state of the recoding. -/
theorem recBit_ct (base : Addr) (S K : Nat) {i : Nat} (hi : i < 456) :
    CT (fun x y => RecRun base S K i x ∧ RecRun base S K i y) recBit
      (fun x y => (RecRun base S K (i + 1) x ∧ x.z = decide (i + 1 = 456)) ∧
        (RecRun base S K (i + 1) y ∧ y.z = decide (i + 1 = 456))) := by
  apply ctBoth
  · apply ctRegs [.r0, .r5, .r8, .r11] _ (by native_taint_decide)
    intro x y h r hr
    obtain ⟨⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := h
    obtain e0 := scr_agree hx.scr hy.scr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact e0
    · rw [hx.r5, hy.r5, e0]
    · exact hx.r8.trans hy.r8.symm
    · exact hx.r11.trans hy.r11.symm
  · rintro x ⟨t, st, tk, to, ta⟩
    exact WP.mono (recBit_ok ta hi) fun u ⟨uk, uo, ua, uz⟩ => ⟨⟨t, st, tk.trans uk, to.trans uo, ua⟩, uz⟩

theorem vrecode_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Start base S K x ∧ Start base S K y) vrecode
      (fun x y => Coded base S K x ∧ Coded base S K y) := by
  have fin : ∀ x, RecRun base S K 456 x → Coded base S K x := fun x ⟨t, st, tk, to, ta⟩ =>
    ⟨t, st, tk, to, fun q hq => ta.dig q hq⟩
  rw [vrecode]
  refine RelCT.seq (recInit_ct base S K) ?_
  refine (RelCT.loop (M := isa) (Q := fun x y => RecRun base S K 456 x ∧ RecRun base S K 456 y)
    (fun n x y => 0 < n ∧ n ≤ 456 ∧ RecRun base S K (456 - n) x ∧ RecRun base S K (456 - n) y)
    (fun n => ?_) 456).mono (fun x y h => ⟨by decide, Nat.le_refl _, by rw [Nat.sub_self]; exact h.1,
      by rw [Nat.sub_self]; exact h.2⟩) fun x y h => ⟨fin x h.1, fin y h.2⟩
  by_cases hn : 0 < n ∧ n ≤ 456
  · refine (recBit_ct base S K (i := 456 - n) (by omega_using [hn])).mono
      (fun x y h => ⟨h.2.2.1, h.2.2.2⟩) fun u v h => ?_
    obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
    refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun hf => ?_, fun ht => ?_⟩
    · have e : some (!u.z) = some false := hf
      rw [zu] at e
      have e456 : 456 - n + 1 = 456 := by simpa using e
      rw [e456] at ru rv
      exact ⟨ru, rv⟩
    · have e : some (!u.z) = some true := ht
      rw [zu] at e
      have e456 : 456 - n + 1 ≠ 456 := by simpa using e
      refine ⟨n - 1, by omega_using [hn], by omega_using [hn, e456], by omega_using [hn], ?_, ?_⟩
      · rw [show 456 - (n - 1) = 456 - n + 1 by omega_using [hn]]; exact ru
      · rw [show 456 - (n - 1) = 456 - n + 1 by omega_using [hn]]; exact rv
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

/-! ### The table -/

theorem vtable_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Coded base S K x ∧ Coded base S K y) (vtable fv)
      (fun x y => Ready base S K x ∧ Ready base S K y) := by
  apply ctBoth
  · obtain hp : ∀ x y, Coded base S K x ∧ Coded base S K y → ∀ r ∈ [Reg.r0], x.gpr r = y.gpr r := by
      intro x y h r hr
      obtain ⟨⟨_, ⟨_, _, _, mx⟩, kx, ox, _⟩, ⟨_, ⟨_, _, _, my⟩, ky, oy, _⟩⟩ := h
      rw [List.mem_singleton] at hr
      subst r
      exact scr_agree (mx.coded kx ox).1 (my.coded ky oy).1
    cases fv
    · exact ctRegs [.r0] hp (by native_taint_decide)
    · exact ctRegsU [.r0] hp (by taint_decide)
  · rintro x ⟨t, ⟨s, pk, sig, M⟩, tk, to, td⟩
    obtain ⟨hs, hb, he⟩ := M.coded tk to
    exact WP.mono (vtable_ok hs hb (by rw [he]; exact congrArg Spec.Ed448.Point.Z M.b) (by rw [he]; exact M.d))
      fun y hy => ⟨s, pk, sig, _, M.ready tk to td hy⟩

/-! ### The loop -/

theorem counter_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Ready base S K x ∧ Ready base S K y) (.block [.movw .r11 456])
      (fun x y => Run base S K 456 x ∧ Run base S K 456 y) := by
  apply ctBoth
  · apply ctRegs [] _ (by native_taint_decide)
    exact fun _ _ _ r hr => (List.not_mem_nil hr).elim
  · rintro x ⟨s, pk, sig, A, M⟩
    exact WP.mono (setCounter_ok x 456 (by decide)) fun x' ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨A, x, M.bits, M.tab, M.inv h1 h2 h3 h4 h5⟩

theorem vload_ct (base : Addr) (S K : Nat) {n : Nat} (hn : n < 456) :
    CT (fun x y => Run base S K (n + 1) x ∧ Run base S K (n + 1) y) (.block vload)
      (fun x y => Loaded base S K n x ∧ Loaded base S K n y) := by
  apply ctBoth
  · apply ctRegs [.r0, .r11] _ (by native_taint_decide)
    intro x y h r hr
    obtain ⟨⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scr_agree hx.scr hy.scr
    · exact hx.r11.trans hy.r11.symm
  · rintro x ⟨A, s₀, hb, ht, hi⟩
    exact WP.mono (vload_ok hn hb hi) fun u hu => ⟨A, s₀, hb, ht, hu⟩

theorem vdoubleAdd_ct (base : Addr) (S K : Nat) {n : Nat} (hn : n < 456) :
    CT (fun x y => Loaded base S K n x ∧ Loaded base S K n y) (vdoubleAdd fv)
      (fun x y => (Run base S K n x ∧ x.z = decide (n = 0)) ∧ (Run base S K n y ∧ y.z = decide (n = 0))) := by
  apply ctBoth
  · obtain hp : ∀ x y, Loaded base S K n x ∧ Loaded base S K n y →
        ∀ r ∈ [Reg.r0, .r8, .r11], x.gpr r = y.gpr r := by
      intro x y h r hr
      obtain ⟨⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact scr_agree hx.scr hy.scr
      · exact hx.r8.trans hy.r8.symm
      · exact hx.r11.trans hy.r11.symm
    cases fv
    · exact ctRegs [.r0, .r8, .r11] hp (by native_taint_decide)
    · exact ctRegsU [.r0, .r8, .r11] hp (by taint_decide)
  · rintro x ⟨A, s₀, hb, ht, hi⟩
    exact WP.mono (vdoubleAdd_ok hn hb ht hi) fun u ⟨hu, hz⟩ => ⟨⟨A, s₀, hb, ht, hu⟩, hz⟩

theorem vloop_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Ready base S K x ∧ Ready base S K y) (vloop fv)
      (fun x y => Run base S K 0 x ∧ Run base S K 0 y) := by
  refine RelCT.seq (counter_ct base S K) ?_
  refine (RelCT.loop (M := isa) (Q := fun x y => Run base S K 0 x ∧ Run base S K 0 y)
    (fun n x y => 0 < n ∧ n ≤ 456 ∧ Run base S K n x ∧ Run base S K n y)
    (fun n => ?_) 456).mono (fun x y h => ⟨by decide, Nat.le_refl _, h.1, h.2⟩) fun _ _ h => h
  by_cases hn : 0 < n ∧ n ≤ 456
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hn]⟩
    have hm : m < 456 := by omega_using [hn]
    refine (RelCT.seq (vload_ct base S K hm) (vdoubleAdd_ct base S K hm)).mono
      (fun x y h => ⟨h.2.2.1, h.2.2.2⟩) fun u v h => ?_
    obtain ⟨⟨ru, zu⟩, ⟨rv, zv⟩⟩ := h
    refine ⟨by show some (!u.z) = some (!v.z); rw [zu, zv], fun hf => ?_, fun ht => ?_⟩
    · have e : some (!u.z) = some false := hf
      rw [zu] at e
      have hm0 : m = 0 := by
        by_contra h0
        rw [decide_eq_false h0] at e
        cases e
      subst hm0
      exact ⟨ru, rv⟩
    · have e : some (!u.z) = some true := ht
      rw [zu] at e
      have hm0 : m ≠ 0 := by
        intro h0
        subst h0
        cases e
      exact ⟨m, by omega_arith, by omega_using [hm0], by omega_using [hn], ru, rv⟩
  · exact RelCT.of_false fun x y h => hn ⟨h.1, h.2.1⟩

theorem vafter_ct (base : Addr) (S K : Nat) :
    CT (fun x y => Run base S K 0 x ∧ Run base S K 0 y) (vafter fv) (fun _ _ => True) := by
  obtain hp : ∀ x y, Run base S K 0 x ∧ Run base S K 0 y → ∀ r ∈ [Reg.r0], x.gpr r = y.gpr r := by
    intro x y h r hr
    obtain ⟨⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := h
    rw [List.mem_singleton] at hr
    subst r
    exact scr_agree hx.scr hy.scr
  cases fv
  · exact ctRegs [.r0] hp (by native_taint_decide)
  · exact ctRegsU [.r0] hp (by taint_decide)

theorem verifyEquation_ct (hR : RecoverOk) :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub (verifyEquation fv) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold verifyEquation
  have hb := (vbefore_ct (fv := fv)).wpDep
    (F := fun (σ t : State) => VMid σ (State.addr (σ.gpr .r3)) (State.addr (σ.gpr .r0)) (State.addr (σ.gpr .r1))
      (decodeLE (bytesAt σ.mem (State.addr (σ.gpr .r1) + BitVec.ofNat 64 57) 57))
      (decodeLE (bytesAt σ.mem (State.addr (σ.gpr .r2)) 57)) t)
    (fun s₁ s₂ h => ⟨vbefore_ok hR (VerifyPre.of h.1) rfl rfl rfl rfl rfl rfl,
      vbefore_ok hR (VerifyPre.of h.2.1) rfl rfl rfl rfl rfl rfl⟩)
  refine RelCT.seq (hb.mono (fun _ _ h => h)
    (Q' := fun x y => ∃ base S K, Start base S K x ∧ Start base S K y) ?_) ?_
  · rintro x y ⟨-, σ₁, σ₂, ⟨-, -, -, -, -, h3, -, hsig, hch⟩, f₁, f₂⟩
    refine ⟨_, _, _, ⟨_, _, _, f₁⟩, ?_⟩
    rw [h3, ← bytesAt_drop57, hsig, bytesAt_drop57, hch]
    exact ⟨_, _, _, f₂⟩
  · refine RelCT.exists_ fun base => RelCT.exists_ fun S => RelCT.exists_ fun K => ?_
    exact RelCT.seq (vrecode_ct base S K) (RelCT.seq (vtable_ct base S K)
      (RelCT.seq (vloop_ct base S K) (vafter_ct base S K)))

end VG.Proof.Ed448.Arm
