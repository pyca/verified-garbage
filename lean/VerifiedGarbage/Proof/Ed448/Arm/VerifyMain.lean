module

public import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeLoop
public import VerifiedGarbage.Proof.X448.Arm.Save
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ed448.Arm.VerifyField
import VerifiedGarbage.Proof.Ed448.Arm.BaseBits
public import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.Arm.Mem
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.Arm.BitWrite
import VerifiedGarbage.Proof.X448.Arm.Iter
import VerifiedGarbage.Proof.X448.Arm.Carry
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.X448.Arm.Counters
import VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish
import VerifiedGarbage.Proof.Ed448.Arm.BaseMain
import VerifiedGarbage.Proof.X448.Arm.Finish
import VerifiedGarbage.Proof.Ed448.Arm.BaseInit
import VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode
import VerifiedGarbage.Proof.Ed448.Arm.VerifyS
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.Arm.Initial

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
  have r7 : t5.gpr .r7 = s.gpr .r7 := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide),
      v1.other _ (by decide)]
  have ea : State.addr (t5.gpr .r7 + BitVec.ofNat 32 (VBITS + j)) = off base (VBITS + (8 * i + j)) := by
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
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (vbitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (vbitJ_ok (hs.of_keeps tk (by decide)) hi
      (by rw [tk.1 .r7 (by decide), tk.1 .r0 (by decide)]; exact hp)
      ((tk.1 _ (by decide)).trans ha) ((tk.1 _ (by decide)).trans hb) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (VBITS + (8 * i + j)) = off base (VBITS + (8 * i + n)) ↔ j = n := by
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
  have ea1 : State.addr (t1.gpr .r7 + BitVec.ofNat 32 57) = sq + BitVec.ofNat 64 i := by
    rw [v1.gpr]; change State.addr (s.gpr .r12 + s.gpr .r11 + BitVec.ofNat 32 57) = _
    rw [hb, Offset.add_add, addr_add (by omega_using [hfs, hi]), ← hsq, Offset.add_add, Nat.add_comm]
  refine wp_ldrb (by decide) ea1 (by rw [v1.rd, v1.wr]; exact hsr) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => ?_
  have ea3 : State.addr (t3.gpr .r7 + BitVec.ofNat 32 0) = kq + BitVec.ofNat 64 i := by
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
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
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
  have hbs : s.mem (sq + BitVec.ofNat 64 i) = s₀.mem (sq + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hsd i hi; simp only [VBITS]; omega_using [this])
  have hbk : s.mem (kq + BitVec.ofNat 64 i) = s₀.mem (kq + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [VBITS]; omega_using [this])
  have inv : VBitsInv base sq kq s₀ s' (i + 1) := by
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
    have keep : Keeps vbitRegs s t := rest_keeps (ht.rest (by decide))
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
# Ed448 verification's equation on ARMv7: `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for bit `t` of `S` and of `k` (bits 0
and 1 of byte `t` at `VBITS`): `Q` (slots 0, 21, 2) doubled, then `B` (slots
8–10) added and swapped in by the first bit, and `-A` (slots 6, 7 and 10) by
the second. The loop's invariant (`VInv`): `Q` is the reference ladder's
point after the bits above `n` (`Proof.Ed448.vladder`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (double vladder vstepRef vladder_bit bitAt)
open VG.Impl.X448.Arm (slot ACC)

/-! ## The values -/

/-- The slots after a swap of `T` into `Q`. -/
def swapEnv (sw : Bool) (e : Env) : Env := opSwap 2 5 sw (opSwap 21 4 sw (opSwap 0 3 sw e))

/-- The slots after an iteration, for the bits `sw₁` (of `S`) and `sw₂` (of `k`). -/
def vstepEnv (sw₁ sw₂ : Bool) (e : Env) : Env :=
  swapEnv sw₂ (applyOps (addF 6 7) (swapEnv sw₁ (applyOps (addF 8 9) (applyOps (doubleF 0 21 2) e))))

theorem swapEnv_keep (sw : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by subst h; omega_arith
  have h2 : i ≠ 2 := fun h => by subst h; omega_arith
  have h3 : i ≠ 3 := fun h => by subst h; omega_arith
  have h4 : i ≠ 4 := fun h => by subst h; omega_arith
  have h5 : i ≠ 5 := fun h => by subst h; omega_arith
  have h21 : i ≠ 21 := fun h => by subst h; omega_arith
  simp only [swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h21]

theorem pt_swap (sw : Bool) (e : Env) :
    pt (swapEnv sw e) 0 21 2 = if sw then pt e 3 4 5 else pt e 0 21 2 := by
  cases sw <;> rfl

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Env) :
    pt (vstepEnv sw₁ sw₂ e) 0 21 2 =
      let r₁ := double (pt e 0 21 2)
      let r₂ := if sw₁ then addWith (e 11) r₁ (pt e 8 9 10) else r₁
      if sw₂ then addWith (e 11) r₂ (pt e 6 7 10) else r₂ := by
  unfold vstepEnv
  generalize he0 : applyOps (doubleF 0 21 2) e = e0
  have p0 : pt e0 0 21 2 = double (pt e 0 21 2) := by rw [← he0, doubleF_eval0]
  have k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, doubleF_keep0 _ _ (Or.inl hi)]
  generalize he1 : applyOps (addF 8 9) e0 = e1
  have p1 : pt e1 3 4 5 = addWith (e0 11) (pt e0 0 21 2) (pt e0 8 9 10) := by rw [← he1, addF_eval8]
  have q1 : pt e1 0 21 2 = pt e0 0 21 2 :=
    pt_congr' (by rw [← he1, addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
      (by rw [← he1, addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inr (Or.inr (by decide)))])
      (by rw [← he1, addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
  have k1 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inr (Or.inl hi))]
  generalize he2 : swapEnv sw₁ e1 = e2
  have p2 : pt e2 0 21 2 = if sw₁ then pt e1 3 4 5 else pt e1 0 21 2 := by rw [← he2, pt_swap]
  have k2 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e2 i = e1 i := fun i hi => by
    rw [← he2, swapEnv_keep _ _ _ hi]
  generalize he3 : applyOps (addF 6 7) e2 = e3
  have p3 : pt e3 3 4 5 = addWith (e2 11) (pt e2 0 21 2) (pt e2 6 7 10) := by rw [← he3, addF_eval6]
  have q3 : pt e3 0 21 2 = pt e2 0 21 2 :=
    pt_congr' (by rw [← he3, addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
      (by rw [← he3, addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inr (Or.inr (by decide)))])
      (by rw [← he3, addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
  have e11 : e2 11 = e 11 := by rw [k2 11 (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  have b8 : pt e0 8 9 10 = pt e 8 9 10 :=
    pt_congr' (k0 8 (by decide)) (k0 9 (by decide)) (k0 10 (by decide))
  have a6 : pt e2 6 7 10 = pt e 6 7 10 :=
    pt_congr' (by rw [k2 6 (by decide), k1 6 (by decide), k0 6 (by decide)])
      (by rw [k2 7 (by decide), k1 7 (by decide), k0 7 (by decide)])
      (by rw [k2 10 (by decide), k1 10 (by decide), k0 10 (by decide)])
  rw [pt_swap, p3, q3, p2, p1, q1, e11, e11', b8, a6, p0]

theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    vstepEnv sw₁ sw₂ e i = e i := by
  rw [vstepEnv, swapEnv_keep _ _ _ hi, addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inr (Or.inl hi)),
    swapEnv_keep _ _ _ hi, addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inr (Or.inl hi)),
    doubleF_keep0 _ _ (Or.inl ⟨by omega_arith, hi.2⟩)]

/-- One bit of both scalars: the reference ladder's point after the bits above
`t`, then after bit `t`. -/
theorem vladder_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : pt e 0 21 2 = vladder S K A (456 - (t + 1)))
    (hq : pt e 8 9 10 = Spec.Ed448.basePoint) (ha : pt e 6 7 10 = A) (hd : e 11 = Spec.Ed448.d) :
    pt (vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 21 2 =
      vladder S K A (456 - t) := by
  rw [vstepEnv_pt, hd, hq, ha, hr, vladder_bit S K A ht]
  rfl

/-! ## One iteration -/

theorem pair_mask : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 &&& 1) = mask (decide (a = 1)) ∧
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 >>> 1) = mask (decide (b = 1)) := by
  decide

theorem vmask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .r11 = BitVec.ofNat 32 t) {a b : Nat} (ha : a < 2) (hb2 : b < 2)
    (hbit : s.mem (off base (VBITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi)) s fun u =>
      u.gpr .r5 = mask (decide ((if hi then b else a) = 1)) ∧ Keeps workRegs s u ∧ u.mem = s.mem := by
  have hB : VBITS = 3104 := rfl
  unfold vmask
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u1 v1 => ?_
  have ba : State.addr (u1.gpr .r7 + BitVec.ofNat 32 VBITS) = off base (VBITS + t) := by
    rw [v1.gpr]; change State.addr (s.gpr .r0 + s.gpr .r11 + BitVec.ofNat 32 VBITS) = _
    rw [hb, Offset.add_add, Nat.add_comm t VBITS]
    exact hs.ea (by omega_arith)
  refine VG.Proof.X25519.Arm.wp_ldrb (by omega_arith) ba
    (by rw [v1.rd, v1.wr]; exact hs.read (by omega_arith)) fun u2 v2 => ?_
  have e2 : u2.gpr .r3 = (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 := by rw [v2.gpr, v1.mem, hbit]
  have pm := pair_mask a ha b hb2
  cases hi
  · refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u3 v3 => ?_
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u4 v4 => ?_
    refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u5 v5 =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [v5.gpr]; change u4.gpr .r5 - u4.gpr .r3 = _
      rw [v4.gpr, v4.other _ (by decide), v3.gpr]
      change (0 : BitVec 32) - (u2.gpr .r3 &&& 1) = _
      rw [e2]; exact pm.1
    · exact rest_keeps ((v1.rest (ws := workRegs) (by decide)).trans ((v2.rest (by decide)).trans
        ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans (v5.rest (by decide))))))
    · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsr (by decide)) fun u3 v3 => ?_
    refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u4 v4 => ?_
    refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u5 v5 =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [v5.gpr]; change u4.gpr .r5 - u4.gpr .r3 = _
      rw [v4.gpr, v4.other _ (by decide), v3.gpr, e2]
      exact pm.2
    · exact rest_keeps ((v1.rest (ws := workRegs) (by decide)).trans ((v2.rest (by decide)).trans
        ((v3.rest (by decide)).trans ((v4.rest (by decide)).trans (v5.rest (by decide))))))
    · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]

theorem vswap_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {sw : Bool}
    (hc : s.gpr .r5 = mask sw) :
    WP isa (.block vswap) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = swapEnv sw (E s.mem base) := by
  unfold vswap
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (cswapE hs hbd 0 3 (by decide) hc) fun u1 ⟨k1, b1, c1, e1⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (cswapE (k1.scr hs) b1 21 4 (by decide) (c1.trans hc))
    fun u2 ⟨k2, b2, c2, e2⟩ => ?_
  refine WP.mono (cswapE (k2.scr (k1.scr hs)) b2 2 5 (by decide) (c2.trans (c1.trans hc)))
    fun u3 ⟨k3, b3, _, e3⟩ => ⟨k1.trans (k2.trans k3), b3, by rw [e3, e2, e1]; rfl⟩

theorem vmaskSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {t : Nat}
    (ht : t < 456) (hb : s.gpr .r11 = BitVec.ofNat 32 t) {a b : Nat} (ha : a < 2) (hb2 : b < 2)
    (hbit : s.mem (off base (VBITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi ++ vswap)) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = swapEnv (decide ((if hi then b else a) = 1)) (E s.mem base) :=
  VG.Proof.X25519.Arm.WP.append (vmask_ok hs ht hb ha hb2 hbit hi) fun u ⟨c, k, m⟩ =>
    WP.mono (vswap_ok (hs.of_keeps k (by decide)) (m ▸ hbd) c) fun v ⟨kv, bv, ev⟩ =>
      ⟨Keep.trans ⟨k, by rw [m]; exact Outside2.refl _ _ _ _ _ _⟩ kv, bv, by rw [ev, m]⟩

/-- The loop's invariant, after the bits above `n` of `S` and `k`, with `-A` the point `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.r11 :: workRegs) s₀ s
  r11 : s.gpr .r11 = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  rep : pt (E s.mem base) 0 21 2 = vladder S K A (456 - n)
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : pt (E s.mem base) 6 7 10 = A
  d : E s.mem base 11 = Spec.Ed448.d

theorem vstep_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pair2 S K t))
    (hi : VInv base S K A s₀ s (n + 1)) :
    WP isa vstep s fun t => VInv base S K A s₀ t n ∧ t.z = decide (n = 0) := by
  have hs := hi.scr
  have hB : VBITS = 3104 := rfl
  have hA : ACC = 3584 := rfl
  have ha2 : (S >>> n) &&& 1 < 2 := bit_lt S n
  have hb2 : (K >>> n) &&& 1 < 2 := bit_lt K n
  have bitval : s.mem (off base (VBITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith) (by rw [ofs_off' base (by omega_arith)]; omega_arith)]
    exact hbits n hn
  unfold vstep
  refine WP.seq (WP.mono (decR11_ok hi.r11) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have K₁ : Keeps [.r11] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  rw [show doubleAt 0 21 2 = (doubleF 0 21 2).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (ops_ok hs₁ (m₁ ▸ hi.bounded) (doubleF 0 21 2)) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  rw [show addAt 8 9 = (addF 8 9).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (ops_ok (k₂.scr hs₁) bb₂ (addF 8 9)) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .r11 = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (VBITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith), m₁, bitval]
  refine WP.seq (WP.mono (vmaskSwap_ok hs₃ bb₃ hn b₃ ha2 hb2 bit₃ false) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  rw [show addAt 6 7 = (addF 6 7).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (ops_ok hs₄ bb₄ (addF 6 7)) fun s₅ ⟨k₅, bb₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr hs₄
  have core4 := k₂.trans (k₃.trans (k₄.trans k₅))
  have b₅ : s₅.gpr .r11 = BitVec.ofNat 32 n := by rw [core4.regs.1 _ (by decide), b₁]
  have bit₅ : s₅.mem (off base (VBITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [core4.mem _ (by rw [ofs_off' base (by omega_arith)]; omega_arith)
      (by rw [ofs_off' base (by omega_arith)]; omega_arith), m₁, bitval]
  refine VG.Proof.X25519.Arm.WP.append (vmaskSwap_ok hs₅ bb₅ hn b₅ ha2 hb2 bit₅ true)
    fun s₆ ⟨k₆, bb₆, e₆⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t vt hz =>
    WP.block_nil ?_
  have core := core4.trans k₆
  have b₆ : s₆.gpr .r11 = BitVec.ofNat 32 n := by rw [core.regs.1 _ (by decide), b₁]
  have ee : E t.mem base = vstepEnv (decide ((S >>> n) &&& 1 = 1)) (decide ((K >>> n) &&& 1 = 1))
      (E s.mem base) := by
    rw [vt.mem, e₆, e₅, e₄, e₃, e₂, m₁]; rfl
  have kk : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → E t.mem base i = E s.mem base i := fun i h => by
    rw [ee, vstepEnv_keep _ _ _ _ h]
  refine ⟨⟨core.scr hs₁ |> fun h => ?_, vt.mem ▸ bb₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h.of_keeps (rest_keeps (vt.rest [])) (by decide)
  · refine hi.regs.trans ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [vt.gpr, core.regs.1 r (fun h => hr (List.mem_cons_of_mem _ h)), g₁ r (fun h => hr (by simp [h]))]
    · rw [vt.rd, core.regs.2.1, rd₁]
    · rw [vt.wr, core.regs.2.2, wr₁]
  · rw [vt.gpr, b₆]
  · refine hi.mem.trans ?_
    intro p hp hq
    rw [vt.mem, core.mem p hp hq, m₁]
  · rw [ee]; exact vladder_step hn hi.rep hi.q hi.na hi.d
  · rw [pt_congr' (kk 8 (by decide)) (kk 9 (by decide)) (kk 10 (by decide))]; exact hi.q
  · rw [pt_congr' (kk 6 (by decide)) (kk 7 (by decide)) (kk 10 (by decide))]; exact hi.na
  · rw [kk 11 (by decide)]; exact hi.d
  · rw [hz, b₆]
    change (BitVec.ofNat 32 n - BitVec.ofNat 32 0 == 0) = _
    rw [BitVec.sub_zero]
    exact VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)

theorem vloop_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbits : ∀ t < 456, s₀.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pair2 S K t))
    (hi : ∀ s', s'.gpr .r11 = BitVec.ofNat 32 456 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VInv base S K A s₀ s' 456) :
    WP isa vloop s fun s' => VInv base S K A s₀ s' 0 := by
  unfold vloop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := vstep) (c := .ne) (Q := fun s' => VInv base S K A s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VInv base S K A s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_arith⟩
  refine WP.mono (vstep_ok (by omega_arith) hbits hi) fun s' ⟨hi', hz⟩ => ?_
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
`VerifyEqOk`): the entry, the bits of `S` and `k`, the check of `S`, `A`
decoded and negated, `Q = [S]B + [k](-A)` by the loop, `R` decoded, and the
comparison of `[4]Q` and `[4]R`. Every write is in the working space, so the
inputs are read unchanged; the callee-saved registers are restored from the
working space, and the return address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Proof.Ed448 (RecoverOk VerifyEqOk vladder negPoint double verifyEquation_none)
open VG.Impl.X448.Arm (slot X2 BITS ACC TMP saved ld copy Op)
open VG.Spec.Ed448 (bytesAt decodeLE)

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
  have k : Keeps [.r12] v w := rest_keeps (hw'.rest (by decide))
  have hsw := hsv.of_keeps k (by decide)
  refine VG.Proof.X25519.Arm.wp_str (a := off base LR) (by decide) (hsw.ea (by decide))
    (hsw.write (by decide)) fun t ht => WP.block_nil ?_
  have wv : w.mem = v.mem := hw'.mem
  have ot : Outside base LR 4 v.mem t.mem := by rw [ht.mem, wv]; exact writeW_outside _ _ _ (by decide)
  have kt : Keeps [] w t := ⟨fun r _ => by rw [ht.gpr], ht.rd, ht.wr⟩
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
  have hsu := hs.of_upd hu (by decide) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (sCheck_ok hsu (by rw [hu.other _ (by decide)]; exact hq)
    (by rw [hu.other _ (by decide)]; exact hfit) (by rw [hu.rd, hu.wr]; exact hr) hd)
    fun v ⟨bv, ov, kv⟩ => ?_
  have hsv := hsu.of_keeps kv (by decide)
  refine VG.Proof.X25519.Arm.WP.append (initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  have hsw := hsv.of_keeps kw (by decide)
  refine WP.mono (copyE3 hsw (initSlots_bounded lw) 21 1) fun t ⟨kt, k3, bt, et⟩ => ?_
  have ev : ∀ i : Index, i ≠ 21 → E t.mem base i = Proof.X448.toFe (initVal i.val) := fun i hi => by
    rw [et, opCopy, Function.update_of_ne hi, initSlots_E lw i]
  have e21 : E t.mem base 21 = Proof.X448.toFe (initVal 1) := by
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

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqOk) {s : State} (h : VerifyPre s) :
    WP isa verifyEquation s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.gpr .r0 = if Spec.Ed448.verifyEquation (bytesAt s.mem (State.addr (s.gpr .r0)) 57)
        (bytesAt s.mem (State.addr (s.gpr .r1)) 114) (bytesAt s.mem (State.addr (s.gpr .r2)) 57)
        then 1 else 0 := by
  obtain ⟨base, hbase⟩ : ∃ b, State.addr (s.gpr .r3) = b := ⟨_, rfl⟩
  obtain ⟨pk, hpk⟩ : ∃ p, State.addr (s.gpr .r0) = p := ⟨_, rfl⟩
  obtain ⟨sig, hsig⟩ : ∃ p, State.addr (s.gpr .r1) = p := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ p, State.addr (s.gpr .r2) = p := ⟨_, rfl⟩
  have hw₀ : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [h.wr, hbase]; simp
  have rpk : ∀ j < 57, InRegions (s.rd ++ s.wr) (pk + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨pk, 57⟩, by rw [h.rd, hpk]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have rsg : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have rS : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp,
      by rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have rch : ∀ j < 57, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨ch, 57⟩, by rw [h.rd, hch]; simp, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have fpk : ∀ j < 57, 8192 ≤ ofs base (pk + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hpk ▸ hbase ▸ h.pk_ws) hj (by decide)
  have fsg : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega_using [hj]) (by decide)
  have fS : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) := fun j hj => by
    rw [Offset.add_add]; exact far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega_using [hj]) (by decide)
  have fch : ∀ j < 57, 8192 ≤ ofs base (ch + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hch ▸ hbase ▸ h.ch_ws) hj (by decide)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) = S := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s.mem ch 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  -- The entry.
  refine WP.seq (WP.mono (ventry_ok hbase hw₀ h.f3) fun s1 ⟨hs1, r81, r121, r21, sv1, o1, lr1, k1⟩ => ?_)
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [k1.2.1, k1.2.2]
  have O1 : Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `S` and `k`.
  refine WP.seq (WP.mono (vbits_ok hs1 (sq := sig + BitVec.ofNat 64 57) (kq := ch)
    (by rw [r121, hsig]) (by rw [r21, hch]) (by rw [r121]; exact h.f1) (by rw [r21]; exact h.f2)
    (by rw [rr1]; exact rS) (by rw [rr1]; exact rch) fS fch) fun s2 ⟨g2, rd2, wr2, o2, bits2⟩ => ?_)
  rw [far_bytes O1 fS, hS, far_bytes O1 fch, hK] at bits2
  have hs2 : Scr s2 base := hs1.of_keeps ⟨g2, rd2, wr2⟩ (by decide)
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rr1]
  have O2 : Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  have r122 : s2.gpr .r12 = s.gpr .r1 := by rw [g2 _ (by decide), r121]
  have r82 : s2.gpr .r8 = s.gpr .r0 := by rw [g2 _ (by decide), r81]
  -- `BAD = 0`, the check of `S`, and the slots.
  refine WP.seq (WP.mono (vstart_ok hs2 (sq := sig + BitVec.ofNat 64 57) (by rw [r122, hsig])
    (by rw [r122]; exact h.f1) (by rw [rr2]; exact rS) fS) fun s3 ⟨k3, r12s3, b3, c3, q3, p3, h103, h113⟩ => ?_)
  rw [far_bytes O2 fS, hS] at c3
  have hs3 := k3.scr hs2
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [k3.regs.2.1, k3.regs.2.2, rr2]
  have O3 : Outside base 0 8192 s.mem s3.mem := O2.trans (k3.mem.whole (by decide) (by decide))
  have r83 : s3.gpr .r8 = s.gpr .r0 := by rw [k3.regs.1 _ (by decide), r82]
  have r123 : s3.gpr .r12 = s.gpr .r1 := by rw [r12s3, r122]
  -- `R` and `A`.
  have inR : DecIn s3 base sig .r12 :=
    ⟨by rw [r123, hsig], by rw [r123]; have := h.f1; omega_using [this], by rw [rr3]; exact rsg, fsg⟩
  have inA : DecIn s3 base pk .r8 := ⟨by rw [r83, hpk], by rw [r83]; exact h.f0, by rw [rr3]; exact rpk, fpk⟩
  refine WP.seq (WP.mono (vdecode_ok hR hs3 b3 inR inA h103 h113)
    fun s4 ⟨k4, f4, b4, c4, v4, w4, bx4, by4, e4⟩ => ?_)
  rw [far_bytes O3 fsg, far_bytes O3 fpk] at c4
  rw [far_bytes O3 fsg] at w4
  rw [far_bytes O3 fpk] at v4
  have hs4 := hs3.of_keeps k4 (by decide)
  have O4 : Outside base 0 8192 s.mem s4.mem :=
    O3.trans fun p hp => f4 p (by omega_using [hp]) (by simp only [ACC]; omega_using [hp])
  -- `-A`.
  rw [show ([.sub (slot 6) (slot 0) (slot 6)] : List Op) = ([.sub 6 0 6] : List FieldOp).map FieldOp.impl
    from rfl]
  refine WP.seq (WP.mono (ops_ok hs4 b4 [.sub 6 0 6]) fun s5 ⟨k5, b5, e5⟩ => ?_)
  have hs5 := k5.scr hs4
  have O5 : Outside base 0 8192 s.mem s5.mem := O4.trans (k5.mem.whole (by decide) (by decide))
  have k5' : ∀ i : Index, i ≠ 6 → E s5.mem base i = E s4.mem base i := fun i hi => by
    rw [e5]; exact Function.update_of_ne hi _ _
  have k43 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21 →
      E s5.mem base i = E s3.mem base i := fun i hi => by
    rw [k5' i (fun h => by subst h; omega_using [hi]), e4 i (fun h => by subst h; omega_using [hi]) (fun h => by subst h; omega_using [hi])
      (by omega_using [hi])]
  -- The loop.
  have bits5 : ∀ t < 456, s5.mem (off base (VBITS + t)) = BitVec.ofNat 8 (pair2 S K t) := fun t ht => by
    rw [bits_kept ((Outside2.widen k5.mem).mono (by decide) (by decide)) t ht, bits_kept f4 t ht,
      bits_kept ((Outside2.widen k3.mem).mono (by decide) (by decide)) t ht]
    exact bits2 t ht
  refine WP.seq (WP.mono (vloop_ok (s₀ := s5) (A := pt (E s5.mem base) 6 7 10) bits5
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s6 I6 => ?_)
  · have k' : Keeps (.r11 :: workRegs) s5 s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hs5.of_keeps k' (by decide), h3 ▸ b5, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [h3, Nat.sub_self, pt_congr' (k43 0 (by decide)) (k43 21 (by decide)) (k43 2 (by decide)), q3]
      rfl
    · rw [h3, pt_congr' (k43 8 (by decide)) (k43 9 (by decide)) (k43 10 (by decide)), p3]
    · rw [h3]
    · rw [h3, k43 11 (by decide), h113]
  -- `R` into slots 8–9.
  have hs6 := I6.scr
  have O6 : Outside base 0 8192 s.mem s6.mem := O5.trans (I6.mem.whole (by decide) (by decide))
  have lx6 : ∀ i < 28, limbs s6.mem base RX i = limbs s4.mem base RX i := fun i hi => by
    rw [limbs_mid I6.mem (by decide) (by decide) hi, limbs_mid k5.mem (by decide) (by decide) hi]
  have ly6 : ∀ i < 28, limbs s6.mem base RY i = limbs s4.mem base RY i := fun i hi => by
    rw [limbs_mid I6.mem (by decide) (by decide) hi, limbs_mid k5.mem (by decide) (by decide) hi]
  have h106 : E s6.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z I6.q
  refine WP.seq (WP.mono (vR_ok hs6 I6.bounded (fun i hi => by rw [lx6 i hi]; exact bx4 i hi)
    (fun i hi => by rw [ly6 i hi]; exact by4 i hi)) fun s7 ⟨k7, b7, e78, e79, e7⟩ => ?_)
  have hs7 := k7.scr hs6
  -- `BAD`.
  have c4' : BadUpd ((Spec.Ed448.decodePoint (bytesAt s.mem sig 57)).isSome = true ∧
      (Spec.Ed448.decodePoint (bytesAt s.mem pk 57)).isSome = true) (s3.gpr .r10) (s7.gpr .r10) := by
    rw [k7.regs.1 .r10 (by decide), I6.regs.1 .r10 (by decide), k5.regs.1 .r10 (by decide)]; exact c4
  have c6 := c3.trans c4'
  -- The comparison.
  have sv7 : Saved base s.gpr s7.mem :=
    (((((sv1.outside o2 (by decide)).outside2 k3.mem (by decide) (by decide)).outside2 f4 (by decide)
      (by decide)).outside2 k5.mem (by decide) (by decide)).outside2 I6.mem (by decide) (by decide)).outside2
      k7.mem (by decide) (by decide)
  have lr7 : word s7.mem base LR = s.gpr .lr := by
    rw [lr_kept ((Outside2.widen k7.mem).mono (by decide) (by decide)),
      lr_kept ((Outside2.widen I6.mem).mono (by decide) (by decide)),
      lr_kept ((Outside2.widen k5.mem).mono (by decide) (by decide)), lr_kept f4,
      lr_kept ((Outside2.widen k3.mem).mono (by decide) (by decide)), o2.word (by decide) (by decide), lr1]
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
        obtain ⟨ax, ay, az⟩ := v4 a ha
        obtain ⟨rx, ry, rz⟩ := w4 r hr'
        have e40 : E s4.mem base 0 = 0 := by
          rw [e4 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X q3
        have e410 : E s4.mem base 10 = 1 := by
          rw [e4 10 (by decide) (by decide) (by decide)]; exact h103
        have hA : pt (E s5.mem base) 6 7 10 = negPoint a := by
          show (⟨E s5.mem base 6, E s5.mem base 7, E s5.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [show E s5.mem base 6 = E s4.mem base 0 - E s4.mem base 6 by rw [e5]; rfl,
            k5' 7 (by decide), k5' 10 (by decide), e40, ax, ay, e410, az]
        have hQ : pt (E s7.mem base) 0 21 2 = vladder S K (negPoint a) 456 := by
          rw [pt_congr' (e7 0 (by decide) (by decide)) (e7 21 (by decide) (by decide))
            (e7 2 (by decide) (by decide)), I6.rep, hA]
        have hRR : pt (E s7.mem base) 8 9 10 = r := by
          show (⟨E s7.mem base 8, E s7.mem base 9, E s7.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [e78, e79, show F s6.mem base RX = F s4.mem base RX from
              congrArg Proof.X448.toFe (valN_congr lx6),
            show F s6.mem base RY = F s4.mem base RY from congrArg Proof.X448.toFe (valN_congr ly6), rx, ry,
            e7 10 (by decide) (by decide), h106, ← rz]
        rw [hE _ _ _ _ _ (bytesAt57_len _ _) (bytesAt114_len _ _) (bytesAt57_len _ _) ha hr, hQ, hRR,
          bytesAt_drop57, hS, hK, hr']
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.Arm
