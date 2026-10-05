import VerifiedGarbage.Proof.Ed448.Arm.BaseVerified
import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation
import VerifiedGarbage.Proof.X448.Arm.Verified
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.X448.Encoding
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Taint

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyBits`. -/
section

/-!
# Ed448 verification's equation on ARMv7: the bits of `S` and `k`

`vbits_ok`: byte `t` at `BITS` is bit `t` of `S` (the signature's last 57
bytes) plus twice bit `t` of `k` (the challenge), for `t < 456`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Impl.X448.Arm (BITS)
open VG.Spec.Ed448 (bytesAt decodeLE)
open VG.Proof.X25519.Arm (wp_mov wp_dp wp_ldrb wp_strb wp_cmp op2_imm op2_reg op2_lsl)

/-- Bits `t` of two numbers in one byte. -/
def pair2 (a b t : Nat) : Nat := ((a >>> t) &&& 1) + 2 * ((b >>> t) &&& 1)

theorem shift_eval (s : State) (r : Reg) {j : Nat} (hj : j < 8) :
    Op2.eval s (if j = 0 then .reg r else .shifted r .lsr j) = some (s.gpr r >>> j) := by
  by_cases hz : j = 0
  · subst j; simp only [ite_true, Op2.eval, BitVec.ushiftRight_zero]
  · rw [ite_eq_right hz]
    exact VG.Proof.X25519.Arm.op2_lsr (by omega)

theorem pack_bits (a b : BitVec 8) (j : Nat) :
    (((a.setWidth 32 >>> j) &&& 1) + (((b.setWidth 32 >>> j) &&& 1) <<< 1)).setWidth 8 =
      BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 a.toNat b.toNat j) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (a.toNat >>> j) &&& 1 ≤ 1 := Nat.and_le_right
  have h2 : (b.toNat >>> j) &&& 1 ≤ 1 := Nat.and_le_right
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, VG.Proof.Ed448.Arm.pair2]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
  change ((a.toNat >>> j &&& 1) + ((b.toNat >>> j &&& 1) * 2 ^ 1) % 2 ^ 32) % 2 ^ 32 % 2 ^ 8 = _
  omega

theorem vbitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {a b : BitVec 8} (ha : s.gpr .r3 = a.setWidth 32) (hb : s.gpr .r9 = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (vbitJ j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j))) (BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 a.toNat b.toNat j)) ∧
        Keeps [.r1, .r4] s t := by
  unfold vbitJ
  refine wp_mov (VG.Proof.Ed448.Arm.shift_eval s .r3 hj) fun t1 v1 => ?_
  refine wp_dp (op2_imm (by decide)) fun t2 v2 => ?_
  refine wp_mov (VG.Proof.Ed448.Arm.shift_eval t2 .r9 hj) fun t3 v3 => ?_
  refine wp_dp (op2_imm (by decide)) fun t4 v4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t5 v5 => ?_
  have r7 : t5.gpr .r7 = s.gpr .r7 := by
    rw [v5.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide),
      v1.other _ (by decide)]
  have ea : State.addr (t5.gpr .r7 + BitVec.ofNat 32 (BITS + j)) = off base (BITS + (8 * i + j)) := by
    rw [r7, hp, BitVec.add_assoc, ← BitVec.ofNat_add, hs.ea (by simp only [BITS]; omega)]
    congr 1; omega
  refine wp_strb (by simp only [BITS]; omega) ea
    (by rw [v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hs.write (by simp only [BITS]; omega))
    fun t6 v6 => WP.block_nil ⟨?_, ?_⟩
  · rw [v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem, v5.gpr]
    change s.mem.writeW _ ((t4.gpr .r1 + t4.gpr .r4 <<< 1).setWidth 8) = _
    rw [v4.other _ (by decide), v3.other _ (by decide), v2.gpr, v4.gpr]
    change s.mem.writeW _ (((t1.gpr .r1 &&& 1) + (t3.gpr .r4 &&& 1) <<< 1).setWidth 8) = _
    rw [v3.gpr, v1.gpr, v2.other _ (by decide), v1.other _ (by decide), ha, hb, VG.Proof.Ed448.Arm.pack_bits]
  · exact rest_keeps ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans (v6.rest _))))))

theorem vbyteBits_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    (hp : s.gpr .r7 = s.gpr .r0 + BitVec.ofNat 32 (8 * i))
    {a b : BitVec 8} (ha : s.gpr .r3 = a.setWidth 32) (hb : s.gpr .r9 = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap vbitJ)) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 a.toNat b.toNat j)) ∧
      VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r1, .r4] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 a.toNat b.toNat j)) ∧
    VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.r1, .r4] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (vbitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.Ed448.Arm.vbitJ_ok (hs.of_keeps tk (by decide)) hi
      (by rw [tk.1 .r7 (by decide), tk.1 .r0 (by decide)]; exact hp)
      ((tk.1 _ (by decide)).trans ha) ((tk.1 _ (by decide)).trans hb) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, VG.Proof.X448.Arm.writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

def vbitHead : List Instr :=
  [.dp .add .r7 .r10 (.reg .r11), .ldrb .r3 .r7 57, .dp .add .r7 .r2 (.reg .r11), .ldrb .r9 .r7 0,
    .dp .add .r7 .r0 (.shifted .r11 .lsl 3)]

def vbitRegs : List Reg := [.r3, .r1, .r4, .r9, .r11, .r7]

theorem vbitHead_ok {s : State} {sq kq : Addr} (hsq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = sq)
    (hkq : State.addr (s.gpr .r2) = kq)
    (hfs : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32) (hfk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hsr : InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 i) 1)
    (hkr : InRegions (s.rd ++ s.wr) (kq + BitVec.ofNat 64 i) 1) :
    WP isa (.block VG.Proof.Ed448.Arm.vbitHead) s fun t =>
      t.gpr .r3 = (s.mem (sq + BitVec.ofNat 64 i)).setWidth 32 ∧
      t.gpr .r9 = (s.mem (kq + BitVec.ofNat 64 i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r9, .r7] s t := by
  unfold VG.Proof.Ed448.Arm.vbitHead
  refine wp_dp (op2_reg _ _) fun t1 v1 => ?_
  have ea1 : State.addr (t1.gpr .r7 + BitVec.ofNat 32 57) = sq + BitVec.ofNat 64 i := by
    rw [v1.gpr]; change State.addr (s.gpr .r10 + s.gpr .r11 + BitVec.ofNat 32 57) = _
    rw [hb, Offset.add_add, addr_add (by omega), ← hsq, Offset.add_add, Nat.add_comm]
  refine wp_ldrb (by decide) ea1 (by rw [v1.rd, v1.wr]; exact hsr) fun t2 v2 => ?_
  refine wp_dp (op2_reg _ _) fun t3 v3 => ?_
  have ea3 : State.addr (t3.gpr .r7 + BitVec.ofNat 32 0) = kq + BitVec.ofNat 64 i := by
    rw [v3.gpr]; change State.addr (t2.gpr .r2 + t2.gpr .r11 + BitVec.ofNat 32 0) = _
    rw [v2.other _ (by decide), v1.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide),
      BitVec.add_zero, hb, addr_add (by omega), hkq]
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
    omega
  · rw [v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · exact rest_keeps ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (v5.rest (by decide))))))

theorem vbitsBody_ok {s : State} {base sq kq : Addr} (hs : Scr s base)
    (hsq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = sq) (hkq : State.addr (s.gpr .r2) = kq)
    (hfs : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32) (hfk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32) {i : Nat} (hi : i < 57)
    (hb : s.gpr .r11 = BitVec.ofNat 32 i) (hsr : InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 i) 1)
    (hkr : InRegions (s.rd ++ s.wr) (kq + BitVec.ofNat 64 i) 1) :
    WP isa (.block vbitsBody) s fun t =>
      t.gpr .r11 = BitVec.ofNat 32 (i + 1) ∧ t.z = decide (i + 1 = 57) ∧ Keeps VG.Proof.Ed448.Arm.vbitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 (s.mem (sq + BitVec.ofNat 64 i)).toNat (s.mem (kq + BitVec.ofNat 64 i)).toNat j)) ∧
      VG.Proof.X448.Arm.Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (VG.Proof.Ed448.Arm.vbitHead ++ (List.range 8).flatMap vbitJ ++ baseBitTail)) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.Arm.vbitHead_ok hsq hkq hfs hfk hi hb hsr hkr) fun t ⟨ta, tb, tp, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.Arm.vbyteBits_ok (hs.of_keeps tk (by decide)) hi tp ta tb) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .r11 = BitVec.ofNat 32 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (baseBitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_)) <;> decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The bits loop's invariant, after `i` bytes. -/
structure VBitsInv (base sq kq : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  esq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = sq
  ekq : State.addr (s.gpr .r2) = kq
  fs : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32
  fk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  gpr : ∀ r, r ∉ VG.Proof.Ed448.Arm.vbitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VG.Proof.X448.Arm.Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 (s₀.mem (sq + BitVec.ofNat 64 (t / 8))).toNat
      (s₀.mem (kq + BitVec.ofNat 64 (t / 8))).toNat (t % 8))

theorem vbitsLoop_ok {s₀ : State} {base sq kq : Addr}
    (hsr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (sq + BitVec.ofNat 64 q) 1)
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (kq + BitVec.ofNat 64 q) 1)
    (hsd : ∀ q < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 q))
    (hkd : ∀ q < 57, 8192 ≤ ofs base (kq + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → VG.Proof.Ed448.Arm.VBitsInv base sq kq s₀ s i →
      WP isa (.loop (.block vbitsBody) .ne) s fun s' => VG.Proof.Ed448.Arm.VBitsInv base sq kq s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block vbitsBody) (c := .ne)
    (Q := fun s' => VG.Proof.Ed448.Arm.VBitsInv base sq kq s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ VG.Proof.Ed448.Arm.VBitsInv base sq kq s₀ s i) ?_ (57 - i) s
    ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.Ed448.Arm.vbitsBody_ok hb.scr hb.esq hb.ekq hb.fs hb.fk hi hb.r11
    (by rw [hb.rd, hb.wr]; exact hsr i hi) (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbs : s.mem (sq + BitVec.ofNat 64 i) = s₀.mem (sq + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hsd i hi; simp only [BITS]; omega)
  have hbk : s.mem (kq + BitVec.ofNat 64 i) = s₀.mem (kq + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : VG.Proof.Ed448.Arm.VBitsInv base sq kq s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.esq), (by rw [g' _ (by decide)]; exact hb.ekq),
      (by rw [g' _ (by decide)]; exact hb.fs), (by rw [g' _ (by decide)]; exact hb.fk), b',
      fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbs, hbk] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega
    exact .inl ⟨rfl, inv⟩

/-- `vbits`: byte `t` of `BITS` is bit `t` of `S` plus twice bit `t` of `k`, for `t < 456`. -/
theorem vbits_ok {s : State} {base sq kq : Addr} (hs : Scr s base)
    (hsq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = sq) (hkq : State.addr (s.gpr .r2) = kq)
    (hfs : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32) (hfk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32)
    (hsr : ∀ q < 57, InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 q) 1)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (kq + BitVec.ofNat 64 q) 1)
    (hsd : ∀ q < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 q))
    (hkd : ∀ q < 57, 8192 ≤ ofs base (kq + BitVec.ofNat 64 q)) :
    WP isa vbits s fun s' =>
      (∀ r, r ∉ VG.Proof.Ed448.Arm.vbitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      VG.Proof.X448.Arm.Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 (decodeLE (bytesAt s.mem sq 57)) (decodeLE (bytesAt s.mem kq 57)) t) := by
  unfold vbits
  refine WP.seq (WP.mono (show WP isa (.block [.mov .r11 (.imm 0)]) s
      (fun s' => VG.Proof.Ed448.Arm.VBitsInv base sq kq s s' 0) by
    refine wp_mov (op2_imm (by decide)) fun t ht => WP.block_nil ?_
    have keep : Keeps VG.Proof.Ed448.Arm.vbitRegs s t := rest_keeps (ht.rest (by decide))
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r10 (by decide)]; exact hsq,
      by rw [ht.other .r2 (by decide)]; exact hkq, by rw [ht.other .r10 (by decide)]; exact hfs,
      by rw [ht.other .r2 (by decide)]; exact hfk, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.mono (VG.Proof.Ed448.Arm.vbitsLoop_ok hsr hkr hsd hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega)]
  unfold VG.Proof.Ed448.Arm.pair2
  rw [scalar_bit _ _ ht, scalar_bit _ _ ht]

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyField`. -/
section

/-!
# Ed448 verification's equation on ARMv7: field programs

The field programs of `vg_ed448_verify_equation` (`Impl/Ed448/Arm/
VerifyEquation.lean`) as X448's slot operations (`FieldOp`), evaluated on the
slots: the doubling and the addition at the slots they are used with (RFC 8032
§5.2.4's formulas, as for base-point multiplication), and the steps of
decoding. `VKeep` is what the checks and decoding may change: the field
operations' registers, the counter `r11` and `BAD` (`r12`), and the working
space from `SIGN` to the slots' end and from X448's `ACC`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Impl.X448.Arm (slot X2 ACC)

/-! ## The frame -/

structure VKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.r12 :: .r11 :: workRegs) s t
  mem : Outside2 base 32 2848 ACC 512 s.mem t.mem

theorem VKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed448.Arm.VKeep base s t) (h' : VG.Proof.Ed448.Arm.VKeep base t u) :
    VG.Proof.Ed448.Arm.VKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem VKeep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed448.Arm.VKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem Outside2.widen {base : Addr} {m m' : Mem} (h : Outside2 base 64 2816 ACC 512 m m') :
    Outside2 base 32 2848 ACC 512 m m' :=
  fun p h1 h2 => h p (by rcases h1 with h1 | h1 <;> [exact Or.inl (by omega); exact Or.inr (by omega)]) h2

theorem IKeep.toV {base : Addr} {s t : State} (h : IKeep base s t) : VG.Proof.Ed448.Arm.VKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), Outside2.widen h.mem⟩

theorem Keep.toV {base : Addr} {s t : State} (h : Keep base s t) : VG.Proof.Ed448.Arm.VKeep base s t := IKeep.toV h.ikeep

/-- What the comparisons may change: `VKeep`'s registers, and the slots and `ACC`. -/
structure CKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.r12 :: .r11 :: workRegs) s t
  mem : Outside2 base 64 2816 ACC 512 s.mem t.mem

theorem CKeep.toV {base : Addr} {s t : State} (h : VG.Proof.Ed448.Arm.CKeep base s t) : VG.Proof.Ed448.Arm.VKeep base s t :=
  ⟨h.regs, Outside2.widen h.mem⟩

theorem CKeep.scr {base : Addr} {s t : State} (h : VG.Proof.Ed448.Arm.CKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem CKeep.trans {base : Addr} {s t u : State} (h : VG.Proof.Ed448.Arm.CKeep base s t) (h' : VG.Proof.Ed448.Arm.CKeep base t u) :
    VG.Proof.Ed448.Arm.CKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.toC {base : Addr} {s t : State} (h : IKeep base s t) : VG.Proof.Ed448.Arm.CKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem Keep.toC {base : Addr} {s t : State} (h : Keep base s t) : VG.Proof.Ed448.Arm.CKeep base s t := IKeep.toC h.ikeep

/-! ## Operations and where they write -/

def fdest : FieldOp → Index
  | .mul o _ _ | .add o _ _ | .sub o _ _ | .mulSmall o _ | .copy o _ => o

theorem fop_apply_keep (op : FieldOp) (e : Env) {i : Index} (h : VG.Proof.Ed448.Arm.fdest op ≠ i) :
    op.apply e i = e i := by
  cases op <;> exact Function.update_of_ne (Ne.symm h) _ _

theorem applyOps_keep (xs : List FieldOp) (e : Env) {i : Index} (h : i ∉ xs.map VG.Proof.Ed448.Arm.fdest) :
    applyOps xs e i = e i := by
  induction xs generalizing e with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [applyOps, ih _ h.2, VG.Proof.Ed448.Arm.fop_apply_keep _ _ (Ne.symm h.1)]

theorem applyOps_append (a b : List FieldOp) (e : Env) :
    applyOps (a ++ b) e = applyOps b (applyOps a e) := by
  induction a generalizing e with
  | nil => rfl
  | cons op rest ih => exact ih _

/-! ## The programs -/

def doubleF (x y z : Index) : List FieldOp := [
  .add 12 x y, .mul 12 12 12, .mul 13 x x, .mul 14 y y, .add 15 13 14, .mul 16 z z,
  .add 17 16 16, .sub 17 15 17, .sub 18 12 15, .mul x 18 17, .sub 19 13 14, .mul y 15 19,
  .mul z 15 17]

def addF (x y : Index) : List FieldOp := [
  .mul 12 2 10, .mul 13 12 12, .mul 14 0 x, .mul 15 21 y, .mul 16 11 14, .mul 16 16 15,
  .sub 17 13 16, .add 18 13 16, .add 19 0 21, .add 20 x y, .mul 19 19 20, .mul 20 12 17,
  .sub 19 19 14, .sub 19 19 15, .mul 3 20 19, .mul 20 12 18, .sub 19 15 14, .mul 4 20 19,
  .mul 5 17 18]

def decodeUVF (yo xo : Index) : List FieldOp :=
  [.mul 12 yo yo, .sub 13 12 10, .mul 3 11 12, .sub 3 3 10, .mul 4 13 3, .mul 4 4 4,
    .mul 5 13 13, .mul 5 5 13, .mul xo 5 3, .mul 12 xo 4]

def decodeXF (xo : Index) : List FieldOp := [.mul xo xo 1, .mul 12 xo xo, .mul 12 3 12]

def negXF (xo : Index) : List FieldOp := [.sub 12 xo xo, .sub 12 12 xo]

theorem doubleF_impl (x y z : Index) :
    (VG.Proof.Ed448.Arm.doubleF x y z).map FieldOp.impl = VG.Impl.Ed448.Arm.doubleAt x.val y.val z.val := rfl
theorem addF_impl (x y : Index) : (VG.Proof.Ed448.Arm.addF x y).map FieldOp.impl = VG.Impl.Ed448.Arm.addAt x.val y.val := rfl
theorem decodeUVF_impl (yo xo : Index) :
    (VG.Proof.Ed448.Arm.decodeUVF yo xo).map FieldOp.impl = VG.Impl.Ed448.Arm.decodeUV yo.val xo.val := rfl
theorem decodeXF_impl (xo : Index) : (VG.Proof.Ed448.Arm.decodeXF xo).map FieldOp.impl = decodeX xo.val := rfl
theorem negXF_impl (xo : Index) : (VG.Proof.Ed448.Arm.negXF xo).map FieldOp.impl = negX xo.val := rfl

/-! ## Their values -/

theorem pt_congr' {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    VG.Proof.Ed448.Arm.pt e' a b c = VG.Proof.Ed448.Arm.pt e a b c := by
  simp only [VG.Proof.Ed448.Arm.pt, ha, hb, hc]


theorem doubleF_eval0 (e : Env) :
    VG.Proof.Ed448.Arm.pt (applyOps (VG.Proof.Ed448.Arm.doubleF 0 21 2) e) 0 21 2 = Proof.Ed448.double (VG.Proof.Ed448.Arm.pt e 0 21 2) := rfl

theorem doubleF_eval8 (e : Env) :
    VG.Proof.Ed448.Arm.pt (applyOps (VG.Proof.Ed448.Arm.doubleF 8 9 10) e) 8 9 10 = Proof.Ed448.double (VG.Proof.Ed448.Arm.pt e 8 9 10) := rfl

theorem addF_eval8 (e : Env) :
    VG.Proof.Ed448.Arm.pt (applyOps (VG.Proof.Ed448.Arm.addF 8 9) e) 3 4 5 = VG.Proof.Ed448.Arm.addWith (e 11) (VG.Proof.Ed448.Arm.pt e 0 21 2) (VG.Proof.Ed448.Arm.pt e 8 9 10) := rfl

theorem addF_eval6 (e : Env) :
    VG.Proof.Ed448.Arm.pt (applyOps (VG.Proof.Ed448.Arm.addF 6 7) e) 3 4 5 = VG.Proof.Ed448.Arm.addWith (e 11) (VG.Proof.Ed448.Arm.pt e 0 21 2) (VG.Proof.Ed448.Arm.pt e 6 7 10) := rfl

theorem doubleF_keep0 (e : Env) (i : Index)
    (hi : 3 ≤ i.val ∧ i.val < 12 ∨ i.val = 1 ∨ i.val = 20) :
    applyOps (VG.Proof.Ed448.Arm.doubleF 0 21 2) e i = e i := by
  refine VG.Proof.Ed448.Arm.applyOps_keep _ _ ?_
  revert i; decide

theorem doubleF_keep8 (e : Env) (i : Index)
    (hi : i.val < 8 ∨ i.val = 11 ∨ i.val = 20 ∨ i.val = 21) :
    applyOps (VG.Proof.Ed448.Arm.doubleF 8 9 10) e i = e i := by
  refine VG.Proof.Ed448.Arm.applyOps_keep _ _ ?_
  revert i; decide

theorem addF_keep (e : Env) (x y : Index) (hx : x.val = 6 ∧ y.val = 7 ∨ x.val = 8 ∧ y.val = 9) (i : Index)
    (hi : i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 12) ∨ i.val = 21) :
    applyOps (VG.Proof.Ed448.Arm.addF x y) e i = e i := by
  refine VG.Proof.Ed448.Arm.applyOps_keep _ _ ?_
  have hx' : (x = 6 ∧ y = 7) ∨ (x = 8 ∧ y = 9) := by
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨Fin.ext h1, Fin.ext h2⟩
    · exact Or.inr ⟨Fin.ext h1, Fin.ext h2⟩
  rcases hx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert i <;> decide

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyChecks`. -/
section

/-!
# Ed448 verification's equation on ARMv7: accumulating checks

`BAD` (`r12`) accumulates checks: a check of `P` ORs into it a word below
`2^16` that is 0 exactly when `P` holds (`BadUpd`). Comparing the limbs of
slot 1 with those of another slot (`diffSlot_ok`), and two slots' field
elements, fully reduced (`eqSlots_ok`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC TMP ld copy freeze)

/-! ## The accumulated word -/

/-- `b'` is `b` ORed with a word below `2^16` that is 0 exactly when `P` holds. -/
def BadUpd (P : Prop) (b b' : BitVec 32) : Prop :=
  ∃ c : BitVec 32, c.toNat < 65536 ∧ (c = 0 ↔ P) ∧ b' = b ||| c

theorem BadUpd.trans {P Q : Prop} {b b' b'' : BitVec 32} (h : VG.Proof.Ed448.Arm.BadUpd P b b') (h' : VG.Proof.Ed448.Arm.BadUpd Q b' b'') :
    VG.Proof.Ed448.Arm.BadUpd (P ∧ Q) b b'' := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  obtain ⟨c', hc', hq, rfl⟩ := h'
  refine ⟨c ||| c', ?_, ?_, BitVec.or_assoc _ _ _⟩
  · rw [BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) hc hc'
  · rw [← hp, ← hq]; exact BitVec.or_eq_zero_iff

theorem BadUpd.congr {P Q : Prop} {b b' : BitVec 32} (h : VG.Proof.Ed448.Arm.BadUpd P b b') (e : P ↔ Q) : VG.Proof.Ed448.Arm.BadUpd Q b b' := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  exact ⟨c, hc, hp.trans e, rfl⟩

theorem BadUpd.rfl' {b : BitVec 32} : VG.Proof.Ed448.Arm.BadUpd True b b :=
  ⟨0, by decide, ⟨fun _ => trivial, fun _ => rfl⟩, (BitVec.or_zero).symm⟩

theorem orBad_ok {s : State} {P : Prop} (hc : (s.gpr .r3).toNat < 65536) (hp : s.gpr .r3 = 0 ↔ P) :
    WP isa (.block orBad) s fun t =>
      VG.Proof.Ed448.Arm.BadUpd P (s.gpr .r12) (t.gpr .r12) ∧ t.mem = s.mem ∧ Keeps [.r12] s t := by
  unfold orBad
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht =>
    WP.block_nil ⟨⟨s.gpr .r3, hc, hp, ht.gpr⟩, ht.mem, rest_keeps (ht.rest (by decide))⟩

/-! ## Comparing limbs -/

theorem xor_limb {x y : BitVec 32} (hx : x.toNat < VG.Proof.X448.Radix16.radix) (hy : y.toNat < VG.Proof.X448.Radix16.radix) :
    (x ^^^ y).toNat < 65536 ∧ (x ^^^ y = 0 ↔ x.toNat = y.toNat) := by
  refine ⟨?_, BitVec.xor_eq_zero_iff.trans ⟨fun h => h ▸ rfl, BitVec.eq_of_toNat_eq⟩⟩
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 16) hx hy

theorem diffLimb_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat} (ha : a + 112 ≤ 4096)
    (hi : i < 28) (h1 : limbs s.mem base X2 i < VG.Proof.X448.Radix16.radix) (h2 : limbs s.mem base a i < VG.Proof.X448.Radix16.radix) :
    WP isa (.block (diffLimb a i)) s fun t =>
      VG.Proof.Ed448.Arm.BadUpd (limbs s.mem base X2 i = limbs s.mem base a i) (s.gpr .r12) (t.gpr .r12) ∧
        t.mem = s.mem ∧ Keeps [.r3, .r2, .r12] s t := by
  unfold diffLimb
  refine load_ok hs (by simp only [X2, slot]; omega) fun u hu => ?_
  refine load_ok (hs.of_upd hu (by decide) (by decide)) (by omega) fun v hv => ?_
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun w hw => ?_
  have x := VG.Proof.Ed448.Arm.xor_limb (x := word s.mem base (X2 + 4 * i)) (y := word s.mem base (a + 4 * i)) h1 h2
  refine WP.mono (VG.Proof.Ed448.Arm.orBad_ok (P := limbs s.mem base X2 i = limbs s.mem base a i)
    (by rw [hw.gpr, hv.other _ (by decide), hu.gpr, hv.gpr, hu.mem]; exact x.1)
    (by rw [hw.gpr, hv.other _ (by decide), hu.gpr, hv.gpr, hu.mem]; exact x.2))
    fun t ⟨tb, tm, tk⟩ => ⟨?_, ?_, ?_⟩
  · rw [hw.other _ (by decide), hv.other _ (by decide), hu.other _ (by decide)] at tb; exact tb
  · rw [tm, hw.mem, hv.mem, hu.mem]
  · exact (rest_keeps (ws := [.r3, .r2, .r12]) ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans
      (hw.rest (by decide))))).trans (tk.mono (by decide))

theorem diffSlot_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : a + 112 ≤ 4096)
    (h1 : Bounded s.mem base X2) (h2 : Bounded s.mem base a) :
    WP isa (.block (diffSlot a)) s fun t =>
      VG.Proof.Ed448.Arm.BadUpd (∀ i < 28, limbs s.mem base X2 i = limbs s.mem base a i) (s.gpr .r12) (t.gpr .r12) ∧
        t.mem = s.mem ∧ Keeps [.r3, .r2, .r12] s t := by
  let inv := fun n (t : State) =>
    VG.Proof.Ed448.Arm.BadUpd (∀ i < n, limbs s.mem base X2 i = limbs s.mem base a i) (s.gpr .r12) (t.gpr .r12) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r2, .r12] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tb, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨BadUpd.rfl'.congr ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => trivial⟩, rfl,
      Keeps.refl _ _⟩
  refine WP.mono (VG.Proof.Ed448.Arm.diffLimb_ok (hs.of_keeps tk (by decide)) ha hn (tm ▸ h1 n hn) (tm ▸ h2 n hn))
    fun u ⟨ub, um, uk⟩ => ⟨?_, um.trans tm, tk.trans uk⟩
  rw [tm] at ub
  refine (tb.trans ub).congr ⟨fun ⟨h, h'⟩ i hi => ?_, fun h => ⟨fun i hi => h i (by omega), h n (by omega)⟩⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact h i hi
  · exact h'

/-! ## Comparing field elements -/

theorem slot_range (i : Index) : 64 ≤ slot i.val ∧ slot i.val + 112 ≤ 2880 := by
  have := i.isLt
  simp only [slot]
  omega

theorem outC {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m') (h1 : 64 ≤ o)
    (h2 : o + n ≤ 2880) : Outside2 base 64 2816 ACC 512 m m' := fun p hp _ => h p (by omega)

theorem fmC {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 64 ≤ o)
    (h2 : o + 112 ≤ 2880) : Outside2 base 64 2816 ACC 512 m m' := fun p hp hq => h p (by omega) hq

theorem outV {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m') (h1 : 32 ≤ o)
    (h2 : o + n ≤ 2880) : Outside2 base 32 2848 ACC 512 m m' := fun p hp _ => h p (by omega)

theorem fmV {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m') (h1 : 32 ≤ o)
    (h2 : o + 112 ≤ 2880) : Outside2 base 32 2848 ACC 512 m m' := fun p hp hq => h p (by omega) hq

theorem valN_inj {f g : Nat → Nat} :
    ∀ {n}, (∀ i < n, f i < VG.Proof.X448.Radix16.radix) → (∀ i < n, g i < VG.Proof.X448.Radix16.radix) → VG.Proof.X448.Radix16.valN f n = VG.Proof.X448.Radix16.valN g n → ∀ i < n, f i = g i
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, hf, hg, h, i, hi => by
    rw [VG.Proof.X448.Radix16.valN_succ, VG.Proof.X448.Radix16.valN_succ] at h
    have lf := VG.Proof.X448.Radix16.valN_lt (n := n) (fun j hj => hf j (by omega))
    have lg := VG.Proof.X448.Radix16.valN_lt (n := n) (fun j hj => hg j (by omega))
    have hp : 0 < VG.Proof.X448.Radix16.radix ^ n := Nat.pow_pos (by decide)
    have e1 : f n = g n := by
      have := congrArg (· / VG.Proof.X448.Radix16.radix ^ n) h
      simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lf, Nat.div_eq_of_lt lg, Nat.zero_add] at this
      exact this
    rw [e1] at h
    have e0 : VG.Proof.X448.Radix16.valN f n = VG.Proof.X448.Radix16.valN g n := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact VG.Proof.Ed448.Arm.valN_inj (fun j hj => hf j (by omega)) (fun j hj => hg j (by omega)) e0 i hi
    · exact e1

theorem limbs_eq_iff {m : Mem} {base : Addr} {a b : Nat} (ha : Bounded m base a) (hb : Bounded m base b) :
    (∀ i < 28, limbs m base a i = limbs m base b i) ↔ fe m base a = fe m base b :=
  ⟨fun h => VG.Proof.X448.Radix16.valN_congr h, fun h => VG.Proof.Ed448.Arm.valN_inj ha hb h⟩

/-- Slots `a` and `b` compared: `BAD |= 0` exactly when they hold the same field
element; slot `a` holds the same element, fully reduced, and slot 1 is
overwritten. -/
theorem eqSlots_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (a b : Index)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    WP isa (.block (eqSlots (slot a.val) (slot b.val))) s fun t =>
      VG.Proof.Ed448.Arm.CKeep base s t ∧ BoundedEnv t.mem base ∧ (∀ i : Index, i ≠ 1 → E t.mem base i = E s.mem base i) ∧
        VG.Proof.Ed448.Arm.BadUpd (E s.mem base a = E s.mem base b) (s.gpr .r12) (t.gpr .r12) := by
  have sa := VG.Proof.Ed448.Arm.slot_range a
  have sb := VG.Proof.Ed448.Arm.slot_range b
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  have s1a : slot a.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot a.val := by rw [hX2]; exact slot_sep ha1
  have s1b : slot b.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot b.val := by rw [hX2]; exact slot_sep hb1
  have sab := slot_sep hab
  unfold eqSlots
  simp only [List.append_assoc]
  -- slot 1 = slot a
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs (o := X2) (a := slot a.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base X2 := fun i hi => by rw [f1 i hi]; exact hb a i hi
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.X448.Arm.freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  -- slot a = slot 1
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs2 (o := slot a.val) (a := X2) (by omega) (by decide)
    (Or.inr (by omega))) fun s3 ⟨f3, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  -- slot 1 = slot b
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs3 (o := X2) (a := slot b.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s4 ⟨f4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  -- what each stage leaves
  have lb3 : ∀ i < 28, limbs s3.mem base (slot b.val) i = limbs s.mem base (slot b.val) i := by
    intro i hi
    rw [m3.limbs (by omega) (by omega) hi, m2.limbs s1b (by omega) hi,
      m1.limbs (by omega) (by omega) hi]
  have bd4 : Bounded s4.mem base X2 := fun i hi => by rw [f4 i hi, lb3 i hi]; exact hb b i hi
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.X448.Arm.freeze_ok hs4 bd4) fun s5 ⟨b5, v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have la5 : ∀ i < 28, limbs s5.mem base (slot a.val) i = limbs s2.mem base X2 i := by
    intro i hi
    rw [m5.limbs s1a (by omega) hi, m4.limbs (by omega) (by omega) hi, f3 i hi]
  have ba5 : Bounded s5.mem base (slot a.val) := fun i hi => by rw [la5 i hi]; exact b2 i hi
  refine WP.mono (VG.Proof.Ed448.Arm.diffSlot_ok hs5 (by omega) b5 ba5) fun t ⟨tb, tm, tk⟩ => ?_
  -- the values
  have fa : fe s5.mem base (slot a.val) = fe s.mem base (slot a.val) % Spec.X448.P := by
    rw [show fe s5.mem base (slot a.val) = fe s2.mem base X2 from VG.Proof.X448.Radix16.valN_congr la5, v2]
    exact congrArg (· % Spec.X448.P) (VG.Proof.X448.Radix16.valN_congr f1)
  have fb : fe s5.mem base X2 = fe s.mem base (slot b.val) % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((VG.Proof.X448.Radix16.valN_congr f4).trans (VG.Proof.X448.Radix16.valN_congr lb3))
  -- the other slots
  have other : ∀ i : Index, i ≠ 1 → i ≠ a → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hia j hj
    have si := VG.Proof.Ed448.Arm.slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    have sai := slot_sep hia
    rw [tm, m5.limbs s1i (by omega) hj, m4.limbs (by omega) (by omega) hj,
      m3.limbs (by omega) (by omega) hj, m2.limbs s1i (by omega) hj,
      m1.limbs (by omega) (by omega) hj]
  refine ⟨⟨?_, ?_⟩, fun i j hj => ?_, fun i hi => ?_, ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans
      (k5.mono ?_))))).trans (tk.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · rw [tm]
    exact ((((VG.Proof.Ed448.Arm.outC m1 (by decide) (by decide)).trans (VG.Proof.Ed448.Arm.fmC m2 (by decide) (by decide))).trans
      (VG.Proof.Ed448.Arm.outC m3 (by omega) (by omega))).trans (VG.Proof.Ed448.Arm.outC m4 (by decide) (by decide))).trans
      (VG.Proof.Ed448.Arm.fmC m5 (by decide) (by decide))
  · by_cases h1 : i = 1
    · subst i; rw [tm]; exact b5 j hj
    · by_cases ha' : i = a
      · subst i; rw [tm]; exact ba5 j hj
      · rw [other i h1 ha' j hj]; exact hb i j hj
  · by_cases ha' : i = a
    · subst i
      simp only [E, F]
      rw [tm, fa, Proof.X448.toFe_mod]
    · simp only [E, F]
      exact congrArg Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr (other i hi ha'))
  · have r12 : s5.gpr .r12 = s.gpr .r12 := by
      rw [k5.1 _ (by decide), k4.1 _ (by decide), k3.1 _ (by decide), k2.1 _ (by decide),
        k1.1 _ (by decide)]
    rw [r12] at tb
    refine tb.congr ?_
    rw [VG.Proof.Ed448.Arm.limbs_eq_iff b5 ba5, fb, fa]
    simp only [E, F, Proof.X448.toFe_eq_iff]
    exact eq_comm
end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyS`. -/
section

/-!
# Ed448 verification's equation on ARMv7: limbs from bytes, and `S < L`

`byteLimb_ok`: a limb of 56 bytes from two byte loads. `sCheck_ok`: the
twenty-eight limbs of `S`'s low 448 bits plus those of `2^448 - L` (scalar
reduction's `kLimb`), carried by X448's `pass`, carry out of 448 bits exactly
when they are at least `L`; with byte 56, `BAD |= 0` exactly when `S < L`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC TMP ld st pass)
open VG.Proof.X25519.Arm (wp_ldrb wp_dp wp_movw op2_lsl op2_reg)

/-- The number of 57 bytes: the limbs of the first 56 and the last byte. -/
theorem decodeLE_bytes57 (m : Mem) (q : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m q 57) =
      VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded m q) 28 + 256 ^ 56 * (m (q + BitVec.ofNat 64 56)).toNat := by
  rw [VG.Proof.Ed448.Arm.bytesAt_57 m q, Proof.Ed448.decodeLE_append, Proof.Ed448.decodeLE_eq, Proof.Ed448.decodeLE_eq,
    show (56 : Nat) = 2 * 28 from rfl, VG.Proof.X448.Radix16.decoded_val m q 28, Proof.X448.length_bytesAt]
  simp only [Proof.X25519.leNum, Nat.mul_zero, Nat.add_zero]

theorem byteLimb_ok {s : State} {p : Reg} {src : Nat} {q : Addr}
    (hq : State.addr (s.gpr p) + BitVec.ofNat 64 src = q) (hsrc : src + 56 ≤ 4096)
    (hfit : (s.gpr p).toNat + src + 56 ≤ 2 ^ 32) (hp3 : p ≠ .r3) {i : Nat} (hi : i < 28)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (byteLimb p src i)) s fun t =>
      t.gpr .r3 = BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem q i) ∧ t.mem = s.mem ∧ Keeps [.r3, .r4] s t := by
  have ea0 : State.addr (s.gpr p + BitVec.ofNat 32 (src + 2 * i)) = q + BitVec.ofNat 64 (2 * i) := by
    rw [addr_add (by omega), ← hq, Offset.add_add]
  have ea1 : State.addr (s.gpr p + BitVec.ofNat 32 (src + 2 * i + 1)) =
      q + BitVec.ofNat 64 (2 * i + 1) := by
    rw [addr_add (by omega), ← hq, Offset.add_add, Nat.add_assoc]
  unfold byteLimb
  refine wp_ldrb (off := src + 2 * i) (by omega) ea0 (hr _ (by omega)) fun s1 h1 => ?_
  refine wp_ldrb (off := src + 2 * i + 1) (a := q + BitVec.ofNat 64 (2 * i + 1)) (by omega) (by rw [h1.other p hp3]; exact ea1)
    (by rw [h1.rd, h1.wr]; exact hr _ (by omega)) fun s2 h2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 h3 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .r3 + s2.gpr .r4 <<< 8 = _
    rw [h2.other .r3 (by decide), h1.gpr, h2.gpr, h1.mem]
    apply BitVec.eq_of_toNat_eq
    have b0 := (s.mem (q + BitVec.ofNat 64 (2 * i))).isLt
    have b1 := (s.mem (q + BitVec.ofNat 64 (2 * i + 1))).isLt
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat, VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN]
    omega
  · rw [h3.mem, h2.mem, h1.mem]
  · exact rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide))))

theorem sLimb_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32)
    {i : Nat} (hi : i < 28) (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1) :
    WP isa (.block (sLimb i)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * i)) (BitVec.ofNat 32 (VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i)) ∧
        Keeps [.r3, .r4, .r2] s t := by
  unfold sLimb
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.byteLimb_ok (src := 57) hq (by decide) (by omega) (by decide) hi hr)
    fun t ⟨t3, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  refine wp_movw fun u hu => ?_
  refine wp_dp (op2_reg _ _) fun v hv => ?_
  refine store_ok ((ht.of_upd hu (by decide) (by decide)).of_upd hv (by decide) (by decide))
    (by simp only [TMP]; omega) fun w hw => WP.block_nil ⟨?_, ?_⟩
  · rw [hw.mem, hv.mem, hu.mem, tm, hv.gpr]
    change s.mem.writeW _ (u.gpr .r3 + u.gpr .r2) = _
    rw [hu.other _ (by decide), t3, hu.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := decoded_lt s.mem q i
    have := kLimb_lt i
    simp only [VG.Proof.X448.Radix16.radix] at *
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · exact (tk.mono (by decide)).trans (rest_keeps (ws := [.r3, .r4, .r2])
      ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest _))))

theorem sLimbs_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block ((List.range 28).flatMap sLimb)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) ∧
        VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r4, .r2] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) ∧
      VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r4, .r2] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have byte : ∀ j < 56, t.mem (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) :=
    fun j hj => tm _ (Or.inr (by have := hd j hj; simp only [TMP]; omega))
  have eq : VG.Proof.X448.Radix16.decoded t.mem q n = VG.Proof.X448.Radix16.decoded s.mem q n := by
    simp only [VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN]; rw [byte _ (by omega), byte _ (by omega)]
  refine WP.mono (VG.Proof.Ed448.Arm.sLimb_ok (q := q) (hs.of_keeps tk (by decide)) (by rw [tk.1 _ (by decide)]; exact hq)
    (by rw [tk.1 _ (by decide)]; exact hfit) hn (by rw [tk.2.1, tk.2.2]; exact hr))
    fun u ⟨um, uk⟩ => ⟨fun i hi => ?_, tm.trans ?_, tk.trans uk⟩
  · rw [eq] at um
    change (word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega) (by simp only [TMP]; omega)]
    by_cases h : i = n
    · have := decoded_lt s.mem q n
      have := kLimb_lt n
      simp only [VG.Proof.X448.Radix16.radix] at *
      rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right h]; exact tf i (by omega)
  · rw [um]; exact (writeW_outside _ _ _ (by simp only [TMP]; omega)).mono (by omega) (by omega)

theorem valN_kLimb : VG.Proof.X448.Radix16.valN kLimb 28 = 2 ^ 448 - Spec.Ed448.L := by decide +kernel

theorem radix_28 : VG.Proof.X448.Radix16.radix ^ 28 = 2 ^ 448 := by decide +kernel

theorem sCheck_ok {s : State} {base q : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = q) (hfit : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) :
    WP isa (.block sCheck) s fun t =>
      VG.Proof.Ed448.Arm.BadUpd (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L) (s.gpr .r12) (t.gpr .r12) ∧
        VG.Proof.X448.Arm.Outside base TMP 112 s.mem t.mem ∧ Keeps [.r3, .r4, .r2, .r5, .r12] s t := by
  unfold sCheck
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.sLimbs_ok hs hq hfit (fun j hj => hr j (by omega))
    (fun j hj => hd j (by omega))) fun t ⟨tf, tm, tk⟩ => ?_
  have ht := hs.of_keeps tk (by decide)
  have hf : ∀ i < 28, VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i ≤ 2 ^ 32 - VG.Proof.X448.Radix16.radix := fun i _ => by
    have := decoded_lt s.mem q i; have := kLimb_lt i; simp only [VG.Proof.X448.Radix16.radix] at *; omega
  refine VG.Proof.X25519.Arm.WP.append (pass_ok ht (o := TMP) (a := TMP) (by decide) (by decide)
    (Or.inl rfl) tf hf) fun u ⟨_, uc, um, uk⟩ => ?_
  have hu := ht.of_keeps uk (by decide)
  have r10 : u.gpr .r10 = s.gpr .r10 := by rw [uk.1 _ (by decide), tk.1 _ (by decide)]
  have b56 : u.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) := by
    have := hd 56 (by decide)
    rw [um _ (Or.inr (by simp only [TMP]; omega)), tm _ (Or.inr (by simp only [TMP]; omega))]
  refine wp_ldrb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [r10, addr_add (by omega), ← hq, Offset.add_add])
    (by rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr 56 (by decide)) fun v hv => ?_
  refine wp_dp (op2_reg _ _) fun w hw => ?_
  -- the carry and the check
  have cy := VG.Proof.X448.Radix16.pass_eq (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28
  rw [VG.Proof.X448.Radix16.valN_add, VG.Proof.Ed448.Arm.valN_kLimb, VG.Proof.Ed448.Arm.radix_28] at cy
  have dl : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.digit fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28 < 2 ^ 448 := by
    rw [← VG.Proof.Ed448.Arm.radix_28]; exact VG.Proof.X448.Radix16.valN_lt (fun i _ => VG.Proof.X448.Radix16.digit_lt _ i)
  have yl : VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 < 2 ^ 448 := by
    rw [← VG.Proof.Ed448.Arm.radix_28]; exact VG.Proof.X448.Radix16.valN_lt (fun i _ => decoded_lt _ _ i)
  have hL : Spec.Ed448.L ≤ 2 ^ 448 := by decide +kernel
  have c1 : VG.Proof.X448.Radix16.carry (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28 ≤ 1 := by
    generalize (2 : Nat) ^ 448 = M at *
    generalize VG.Proof.X448.Radix16.carry (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28 = c at *
    rcases Nat.lt_or_ge c 2 with h | h
    · omega
    · have : M * 2 ≤ M * c := Nat.mul_le_mul_left M h
      omega
  have hchk := Proof.Ed448.sCheck_nat (b := (s.mem (q + BitVec.ofNat 64 56)).toNat) yl dl c1 cy
  rw [← VG.Proof.Ed448.Arm.decodeLE_bytes57] at hchk
  have e3 : w.gpr .r3 = (s.mem (q + BitVec.ofNat 64 56)).setWidth 32 |||
      BitVec.ofNat 32 (VG.Proof.X448.Radix16.carry (fun i => VG.Proof.X448.Radix16.decoded s.mem q i + kLimb i) 28) := by
    rw [hw.gpr]; change v.gpr .r3 ||| v.gpr .r5 = _
    rw [hv.gpr, hv.other _ (by decide), b56]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [uc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have bt := (s.mem (q + BitVec.ofNat 64 56)).isLt
  refine WP.mono (VG.Proof.Ed448.Arm.orBad_ok (s := w) (P := Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem q 57) < Spec.Ed448.L)
    ?_ ?_) fun x ⟨xb, xm, xk⟩ => ⟨?_, ?_, ?_⟩
  · rw [e3, BitVec.toNat_or, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.or_lt_two_pow (n := 16) (by omega) (by omega)
  · rw [e3, ← hchk]
    refine BitVec.or_eq_zero_iff.trans ?_
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := congrArg BitVec.toNat h2
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact this
      · have := congrArg BitVec.toNat h1
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] at this
        exact this
    · rintro ⟨h1, h2⟩
      refine ⟨BitVec.eq_of_toNat_eq ?_, ?_⟩
      · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; exact h2
      · rw [h1]
  · have r12w : w.gpr .r12 = s.gpr .r12 := by
      rw [hw.other .r12 (by decide), hv.other .r12 (by decide), uk.1 .r12 (by decide),
        tk.1 .r12 (by decide)]
    rw [r12w] at xb
    exact xb
  · rw [xm, hw.mem, hv.mem]; exact tm.trans um
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans ((rest_keeps ((hv.rest (ws := [.r3, .r4, .r2, .r5, .r12])
      (by decide)).trans (hw.rest (by decide)))).trans (xk.mono ?_))) <;> decide

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyDecodeY`. -/
section

/-!
# Ed448 verification's equation on ARMv7: the `y` of a point

`decodeY_ok`: the 57 bytes of an encoded point at `q`: the twenty-eight limbs
of the first 56 (`y₀`) into slot `yo`, the sign bit (bit 7 of the last byte
`b`) to `SIGN`, and `BAD |= 0` exactly when bits 0–6 of `b` are 0 and
`y₀ < p` (`y₀` is equal to its full reduction, in slot 1).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC TMP ld st copy freeze)
open VG.Proof.X25519.Arm (wp_ldrb wp_dp wp_mov op2_lsr op2_imm op2_reg)

theorem loadLimbs_ok {s : State} {base q : Addr} (hs : Scr s base) {p : Reg} (hp3 : p ≠ .r3)
    (hp4 : p ≠ .r4)
    (hq : State.addr (s.gpr p) = q) (hfit : (s.gpr p).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) {o : Nat} (ho : 32 ≤ o ∧ o + 112 ≤ 4096) :
    WP isa (.block (loadLimbs p o)) s fun t =>
      (∀ i < 28, limbs t.mem base o i = VG.Proof.X448.Radix16.decoded s.mem q i) ∧
        VG.Proof.X448.Arm.Outside base o 112 s.mem t.mem ∧ Keeps [.r3, .r4] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base o i = VG.Proof.X448.Radix16.decoded s.mem q i) ∧
      VG.Proof.X448.Arm.Outside base o 112 s.mem t.mem ∧ Keeps [.r3, .r4] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  have byte : ∀ j < 56, t.mem (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) :=
    fun j hj => tm _ (Or.inr (by have := hd j hj; omega))
  have eq : VG.Proof.X448.Radix16.decoded t.mem q n = VG.Proof.X448.Radix16.decoded s.mem q n := by
    simp only [VG.Proof.X448.Radix16.decoded, VG.Proof.X448.Radix16.byteN]; rw [byte _ (by omega), byte _ (by omega)]
  have hpk : p ∉ [Reg.r3, .r4] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hp3, hp4⟩
  have tp : s.gpr p = t.gpr p := (tk.1 p hpk).symm
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.byteLimb_ok (src := 0) (q := q)
    (by rw [← tp, hq, BitVec.add_zero]) (by decide) (by rw [← tp]; omega) hp3 hn
    (by rw [tk.2.1, tk.2.2]; exact hr)) fun u ⟨u3, um, uk⟩ => ?_
  refine store_ok ((hs.of_keeps tk (by decide)).of_keeps uk (by decide)) (by omega) fun v hv =>
    WP.block_nil ⟨fun i hi => ?_, tm.trans ?_, tk.trans (uk.trans (rest_keeps (hv.rest _)))⟩
  · change (word v.mem base (o + 4 * i)).toNat = _
    rw [hv.mem, um, word_write t.mem base (by omega) (by omega)]
    by_cases h : i = n
    · rw [ite_eq_left h, h, u3, eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem q n) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega)
  · rw [hv.mem, um]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

/-- The last byte: `SIGN = b / 128` and `r3 = b mod 128`. -/
theorem signByte_ok {s : State} {base q : Addr} (hs : Scr s base) {p : Reg}
    (hq : State.addr (s.gpr p) = q) (hfit : (s.gpr p).toNat + 57 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 56) 1) :
    WP isa (.block [.ldrb .r3 p 56, .mov .r2 (.shifted .r3 .lsr 7), st .r2 SIGN,
      .dp .and .r3 .r3 (.imm 0x7f)]) s fun t =>
      (t.gpr .r3).toNat = (s.mem (q + BitVec.ofNat 64 56)).toNat % 128 ∧
      t.mem = s.mem.writeW (off base SIGN) (BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128)) ∧
      Keeps [.r3, .r2] s t := by
  refine wp_ldrb (a := q + BitVec.ofNat 64 56) (by decide) (by rw [addr_add (by omega), hq]) hr fun u hu => ?_
  refine wp_mov (op2_lsr (by decide)) fun v hv => ?_
  refine store_ok ((hs.of_upd hu (by decide) (by decide)).of_upd hv (by decide) (by decide))
    (by decide) fun w hw => ?_
  refine wp_dp (op2_imm (by decide)) fun x hx => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [hx.gpr]; change (w.gpr .r3 &&& 0x7f#32).toNat = _
    rw [hw.gpr, hv.other _ (by decide), hu.gpr, BitVec.toNat_and, BitVec.toNat_setWidth,
      show (0x7f#32).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    omega
  · rw [hx.mem, hw.mem, hv.mem, hu.mem, hv.gpr, hu.gpr]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · exact rest_keeps ((hu.rest (by decide)).trans ((hv.rest (by decide)).trans
      ((hw.rest _).trans (hx.rest (by decide)))))

/-- `decodeY p yo`. -/
theorem decodeY_ok {s : State} {base q : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {p : Reg} (hp : p = .r8 ∨ p = .r10) (hq : State.addr (s.gpr p) = q) (hfit : (s.gpr p).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j)) (yo : Index) (hyo : yo ≠ 1) :
    WP isa (.block (decodeY p yo.val)) s fun t =>
      VG.Proof.Ed448.Arm.VKeep base s t ∧ BoundedEnv t.mem base ∧
      word t.mem base SIGN = BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128) ∧
      VG.Proof.Ed448.Arm.BadUpd ((s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧ VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 < Spec.X448.P)
        (s.gpr .r12) (t.gpr .r12) ∧
      E t.mem base yo = Proof.X448.toFe (VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28) ∧
      (∀ i : Index, i ≠ 1 → i ≠ yo → E t.mem base i = E s.mem base i) := by
  have sy := VG.Proof.Ed448.Arm.slot_range yo
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  have s1y : slot yo.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot yo.val := by rw [hX2]; exact slot_sep hyo
  have hp3 : p ≠ .r3 := by rcases hp with rfl | rfl <;> decide
  have hpk : p ∉ [Reg.r3, .r4] := by rcases hp with rfl | rfl <;> decide
  unfold decodeY
  simp only [List.append_assoc]
  have hp4 : p ≠ .r4 := by rcases hp with rfl | rfl <;> decide
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.loadLimbs_ok hs hp3 hp4 hq hfit (fun j hj => hr j (by omega))
    (fun j hj => hd j (by omega)) (o := slot yo.val) ⟨by omega, by omega⟩) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have b56 : s1.mem (q + BitVec.ofNat 64 56) = s.mem (q + BitVec.ofNat 64 56) :=
    m1 _ (Or.inr (by have := hd 56 (by decide); omega))
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.signByte_ok hs1 (p := p) (q := q) (by rw [k1.1 p hpk]; exact hq)
    (by rw [k1.1 p hpk]; exact hfit) (by rw [k1.2.1, k1.2.2]; exact hr 56 (by decide)))
    fun s2 ⟨r2, m2, k2⟩ => ?_
  rw [b56] at r2 m2
  have hs2 := hs1.of_keeps k2 (by decide)
  have bnd : ∀ i < 28, limbs s1.mem base (slot yo.val) i < VG.Proof.X448.Radix16.radix := fun i hi => by
    rw [f1 i hi]; exact decoded_lt _ _ _
  have o2 : VG.Proof.X448.Arm.Outside base SIGN 4 s1.mem s2.mem := by rw [m2]; exact writeW_outside _ _ _ (by decide)
  have l2 : ∀ i < 28, limbs s2.mem base (slot yo.val) i = VG.Proof.X448.Radix16.decoded s.mem q i := fun i hi => by
    rw [o2.limbs (Or.inr (by simp only [SIGN]; omega)) (by omega) hi, f1 i hi]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.orBad_ok (s := s2)
    (P := (s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0)
    (by rw [r2]; omega) (by rw [← r2]; exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩))
    fun s3 ⟨b3, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs3 (o := X2) (a := slot yo.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s4 ⟨f4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have bd4 : Bounded s4.mem base X2 := fun i hi => by
    rw [f4 i hi, m3, l2 i hi]; exact decoded_lt _ _ _
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.X448.Arm.freeze_ok hs4 bd4) fun s5 ⟨b5, v5, m5, k5⟩ => ?_
  have hs5 := hs4.of_keeps k5 (by decide)
  have l5 : ∀ i < 28, limbs s5.mem base (slot yo.val) i = VG.Proof.X448.Radix16.decoded s.mem q i := fun i hi => by
    rw [m5.limbs s1y (by omega) hi, m4.limbs (by omega) (by omega) hi, m3, l2 i hi]
  have by5 : Bounded s5.mem base (slot yo.val) := fun i hi => by rw [l5 i hi]; exact decoded_lt _ _ _
  refine WP.mono (VG.Proof.Ed448.Arm.diffSlot_ok hs5 (by omega) b5 by5) fun t ⟨tb, tm, tk⟩ => ?_
  have fe5 : fe s5.mem base X2 = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 % Spec.X448.P := by
    rw [v5]; exact congrArg (· % Spec.X448.P) ((VG.Proof.X448.Radix16.valN_congr f4).trans (by rw [m3]; exact VG.Proof.X448.Radix16.valN_congr l2))
  have fy5 : fe s5.mem base (slot yo.val) = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 := VG.Proof.X448.Radix16.valN_congr l5
  have other : ∀ i : Index, i ≠ 1 → i ≠ yo → ∀ j < 28,
      limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j := by
    intro i hi1 hiy j hj
    have si := VG.Proof.Ed448.Arm.slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep hi1
    have syi := slot_sep hiy
    rw [tm, m5.limbs s1i (by omega) hj, m4.limbs (by omega) (by omega) hj, m3,
      o2.limbs (Or.inr (by simp only [SIGN]; omega)) (by omega) hj, m1.limbs (by omega) (by omega) hj]
  have r12 : s5.gpr .r12 = s3.gpr .r12 := by rw [k5.1 _ (by decide), k4.1 _ (by decide)]
  have r12' : s2.gpr .r12 = s.gpr .r12 := by rw [k2.1 _ (by decide), k1.1 _ (by decide)]
  refine ⟨⟨?_, ?_⟩, fun i j hj => ?_, ?_, ?_, ?_, fun i h1 hy => ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans ((k4.mono ?_).trans
      (k5.mono ?_))))).trans (tk.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · rw [tm]
    exact ((((VG.Proof.Ed448.Arm.outV m1 (by omega) (by omega)).trans (VG.Proof.Ed448.Arm.outV o2 (by decide) (by decide))).trans
      (by rw [m3]; exact Outside2.refl _ _ _ _ _ _)).trans (VG.Proof.Ed448.Arm.outV m4 (by decide) (by decide))).trans
      (VG.Proof.Ed448.Arm.fmV m5 (by decide) (by decide))
  · by_cases h1 : i = 1
    · subst i; rw [tm]; exact b5 j hj
    · by_cases hy : i = yo
      · subst i; rw [tm]; exact by5 j hj
      · rw [other i h1 hy j hj]; exact hb i j hj
  · rw [tm, m5.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m4.word (Or.inl (by simp only [SIGN]; omega)) (by decide), m3, m2]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [r12] at tb
    have h := b3.trans tb
    rw [r12'] at h
    refine h.congr (and_congr_right fun _ => ?_)
    rw [VG.Proof.Ed448.Arm.limbs_eq_iff b5 by5, fe5, fy5]
    exact Nat.mod_eq_iff_lt (NeZero.ne Spec.X448.P)
  · simp only [E, F]
    rw [tm, fy5]
  · simp only [E, F]
    exact congrArg Proof.X448.toFe (VG.Proof.X448.Radix16.valN_congr (other i h1 hy))

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifySign`. -/
section

/-!
# Ed448 verification's equation on ARMv7: the sign of a decoded point

`decodeSign_ok`: with the candidate `x` in slot `xo` and `-x` in slot 12,
`x` fully reduced in slot 1; `BAD |= 0` exactly when `x ≠ 0` or the sign bit
(`SIGN`) is 0; and `x` swapped with `-x` under the mask of its low bit
differing from the sign bit (RFC 8032 §5.2.3, step 4).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC TMP ld st copy freeze cswap)
open VG.Proof.X25519.Arm (wp_dp wp_mov op2_lsr op2_imm op2_reg)

/-- `r2 = ⋁` the limbs of slot 1: 0 exactly when they all are. -/
theorem orLimbs_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2) :
    WP isa (.block orLimbs) s fun t =>
      (t.gpr .r2).toNat < 65536 ∧ (t.gpr .r2 = 0 ↔ ∀ i < 28, limbs s.mem base X2 i = 0) ∧
        t.mem = s.mem ∧ Keeps [.r2, .r3] s t := by
  unfold orLimbs
  refine load_ok hs (by decide) fun u hu => ?_
  let inv := fun n (t : State) =>
    (t.gpr .r2).toNat < 65536 ∧ (t.gpr .r2 = 0 ↔ ∀ i < n + 1, limbs s.mem base X2 i = 0) ∧
      t.mem = s.mem ∧ Keeps [.r2, .r3] s t
  have h0 : inv 0 u := by
    refine ⟨?_, ?_, hu.mem, rest_keeps (hu.rest (by decide))⟩
    · rw [hu.gpr]; exact hb 0 (by decide)
    · rw [hu.gpr]
      exact ⟨fun h i hi => by rw [show i = 0 by omega]; exact congrArg BitVec.toNat h,
        fun h => BitVec.eq_of_toNat_eq (h 0 (by decide))⟩
  refine wp_range_flatMap (M := isa) (N := 27) inv (fun n t hn ⟨tb, tz, tm, tk⟩ => ?_) 27 (by decide) u h0
  refine load_ok (hs.of_keeps tk (by decide)) (by simp only [X2, slot]; omega) fun v hv => ?_
  refine wp_dp (op2_reg _ _) fun w hw => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [hw.gpr]; change (v.gpr .r2 ||| v.gpr .r3).toNat < _
    rw [hv.other _ (by decide), hv.gpr, BitVec.toNat_or, tm]
    exact Nat.or_lt_two_pow (n := 16) tb (hb (n + 1) (by omega))
  · rw [hw.gpr]; change v.gpr .r2 ||| v.gpr .r3 = 0 ↔ _
    rw [hv.other _ (by decide), hv.gpr, tm]
    refine BitVec.or_eq_zero_iff.trans ((and_congr_left fun _ => tz).trans ?_)
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact congrArg BitVec.toNat h2
    · intro h
      exact ⟨fun i hi => h i (by omega), BitVec.eq_of_toNat_eq (h (n + 1) (by omega))⟩
  · rw [hw.mem, hv.mem, tm]
  · exact tk.trans (rest_keeps ((hv.rest (by decide)).trans (hw.rest (by decide))))

theorem isZero16 (x : BitVec 32) (h : x.toNat < 65536) :
    (x - 1) >>> 31 = if x = 0 then 1 else 0 := by
  by_cases hx : x = 0
  · subst hx; decide
  · rw [ite_eq_right hx]
    have hx' : x.toNat ≠ 0 := fun e => hx (BitVec.eq_of_toNat_eq e)
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    change (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 2 ^ 31 = 0
    omega

theorem zeroSign : ∀ z : Bool, ∀ sb < 2,
    (((if z then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb) = 0 ↔ ¬(z = true ∧ sb = 1)) ∧
      ((if z then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb).toNat < 65536 := by decide

theorem negMask : ∀ a < 2, ∀ sb < 2,
    (0 : BitVec 32) - (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 sb) = mask (decide (a ≠ sb)) := by decide

theorem and1 (w : BitVec 32) : w &&& 1 = BitVec.ofNat 32 (w.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w.toNat % 2) (by omega)]

/-- After the `x = 0` check (`r2`, 0 exactly when `Z`): `BAD |= 0` exactly when
not both `Z` and the sign bit, and `r5` the mask of the low bit `l₀` differing
from it. -/
theorem signTail_ok {s : State} {base : Addr} (hs : Scr s base) {Z : Prop} (h2 : (s.gpr .r2).toNat < 65536)
    (hz : s.gpr .r2 = 0 ↔ Z) {sb : Nat} (hsb : sb < 2) (hsign : word s.mem base SIGN = BitVec.ofNat 32 sb) :
    WP isa (.block [.dp .sub .r2 .r2 (.imm 1), .mov .r2 (.shifted .r2 .lsr 31), ld .r3 SIGN,
      .dp .and .r2 .r2 (.reg .r3), .dp .orr .r12 .r12 (.reg .r2),
      ld .r2 X2, .dp .and .r2 .r2 (.imm 1), .dp .eor .r2 .r2 (.reg .r3), .mov .r5 (.imm 0),
      .dp .sub .r5 .r5 (.reg .r2)]) s fun t =>
      VG.Proof.Ed448.Arm.BadUpd (¬(Z ∧ sb = 1)) (s.gpr .r12) (t.gpr .r12) ∧
        t.gpr .r5 = mask (decide (limbs s.mem base X2 0 % 2 ≠ sb)) ∧ t.mem = s.mem ∧
        Keeps [.r2, .r3, .r5, .r12] s t := by
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun u2 v2 => ?_
  have s2 := (hs.of_upd v1 (by decide) (by decide)).of_upd v2 (by decide) (by decide)
  refine load_ok s2 (by decide) fun u3 v3 => ?_
  refine wp_dp (op2_reg _ _) fun u4 v4 => ?_
  refine wp_dp (op2_reg _ _) fun u5 v5 => ?_
  have s5 := ((s2.of_upd v3 (by decide) (by decide)).of_upd v4 (by decide) (by decide)).of_upd v5
    (by decide) (by decide)
  refine load_ok s5 (by decide) fun u6 v6 => ?_
  refine wp_dp (op2_imm (by decide)) fun u7 v7 => ?_
  refine wp_dp (op2_reg _ _) fun u8 v8 => ?_
  refine wp_mov (op2_imm (by decide)) fun u9 v9 => ?_
  refine wp_dp (op2_reg _ _) fun t vt => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · have e2 : u2.gpr .r2 = if s.gpr .r2 = 0 then 1 else 0 := by
      rw [v2.gpr, v1.gpr]; exact VG.Proof.Ed448.Arm.isZero16 _ h2
    have e4 : u4.gpr .r2 = (if s.gpr .r2 = 0 then 1 else 0 : BitVec 32) &&& BitVec.ofNat 32 sb := by
      rw [v4.gpr]; change u3.gpr .r2 &&& u3.gpr .r3 = _
      rw [v3.other _ (by decide), e2, v3.gpr, v2.mem, v1.mem, hsign]
    have z := VG.Proof.Ed448.Arm.zeroSign (decide (s.gpr .r2 = 0)) sb hsb
    simp only [decide_eq_true_eq] at z
    have e12 : t.gpr .r12 = s.gpr .r12 ||| u4.gpr .r2 := by
      rw [vt.other _ (by decide), v9.other _ (by decide), v8.other _ (by decide), v7.other _ (by decide),
        v6.other _ (by decide), v5.gpr]
      change u4.gpr .r12 ||| u4.gpr .r2 = _
      rw [v4.other _ (by decide), v3.other _ (by decide), v2.other _ (by decide), v1.other _ (by decide)]
    refine ⟨u4.gpr .r2, ?_, ?_, e12⟩
    · rw [e4]; exact z.2
    · rw [e4, z.1, hz]
  · rw [vt.gpr]; change u9.gpr .r5 - u9.gpr .r2 = _
    rw [v9.gpr, v9.other _ (by decide), v8.gpr]
    change (0 : BitVec 32) - (u7.gpr .r2 ^^^ u7.gpr .r3) = _
    rw [v7.gpr, v7.other _ (by decide)]
    change (0 : BitVec 32) - ((u6.gpr .r2 &&& 1) ^^^ u6.gpr .r3) = _
    rw [v6.gpr, v6.other _ (by decide), v5.other _ (by decide), v4.other _ (by decide), v3.gpr,
      v5.mem, v4.mem, v3.mem, v2.mem, v1.mem, hsign, VG.Proof.Ed448.Arm.and1]
    exact VG.Proof.Ed448.Arm.negMask _ (Nat.mod_lt _ (by decide)) sb hsb
  · rw [vt.mem, v9.mem, v8.mem, v7.mem, v6.mem, v5.mem, v4.mem, v3.mem, v2.mem, v1.mem]
  · exact rest_keeps ((v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans ((v5.rest (by decide)).trans ((v6.rest (by decide)).trans
      ((v7.rest (by decide)).trans ((v8.rest (by decide)).trans ((v9.rest (by decide)).trans
      (vt.rest (by decide)))))))))))

theorem sel_sign : ∀ a < 2, ∀ sb < 2, decide (a ≠ sb) = !((a == 1) == (sb == 1)) := by decide

theorem fe_zero_iff {m : Mem} {base : Addr} {o : Nat} (hb : Bounded m base o) :
    (∀ i < 28, limbs m base o i = 0) ↔ fe m base o = 0 := by
  have z : VG.Proof.X448.Radix16.valN (fun _ => 0) 28 = 0 := valN_zero 28
  constructor
  · intro h; exact (VG.Proof.X448.Radix16.valN_congr h).trans z
  · intro h; exact VG.Proof.Ed448.Arm.valN_inj hb (fun _ _ => by decide) (h.trans z.symm)

/-- `decodeSign xo`, with `-x` in slot 12 and the sign bit `sb` at `SIGN`. -/
theorem decodeSign_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (xo : Index) (hxo : xo = 6 ∨ xo = 8) {sb : Nat} (hsb : sb < 2)
    (hsign : word s.mem base SIGN = BitVec.ofNat 32 sb)
    (hneg : E s.mem base 12 = (E s.mem base xo - E s.mem base xo) - E s.mem base xo) :
    WP isa (.block (decodeSign xo.val)) s fun t =>
      VG.Proof.Ed448.Arm.CKeep base s t ∧ BoundedEnv t.mem base ∧
      VG.Proof.Ed448.Arm.BadUpd (¬(E s.mem base xo = 0 ∧ sb = 1)) (s.gpr .r12) (t.gpr .r12) ∧
      E t.mem base xo = (if ((E s.mem base xo).val % 2 == 1) == (sb == 1) then E s.mem base xo
        else (E s.mem base xo - E s.mem base xo) - E s.mem base xo) ∧
      (∀ i : Index, i ≠ 1 → i ≠ 12 → i ≠ xo → E t.mem base i = E s.mem base i) := by
  have hx1 : xo ≠ 1 := by rcases hxo with rfl | rfl <;> decide
  have hx12 : xo ≠ 12 := by rcases hxo with rfl | rfl <;> decide
  have sx := VG.Proof.Ed448.Arm.slot_range xo
  have hX2v : X2 = 192 := rfl
  have hA : ACC = 3584 := rfl
  have hX2 : X2 = slot (1 : Index).val := rfl
  have s1x : slot xo.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot xo.val := by rw [hX2]; exact slot_sep hx1
  unfold decodeSign
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (copy_ok hs (o := X2) (a := slot xo.val) (by decide) (by omega)
    (Or.inr (by omega))) fun s1 ⟨f1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  have bd1 : Bounded s1.mem base X2 := fun i hi => by rw [f1 i hi]; exact hb xo i hi
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.X448.Arm.freeze_ok hs1 bd1) fun s2 ⟨b2, v2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.orLimbs_ok hs2 b2) fun s3 ⟨r3b, r3z, m3, k3⟩ => ?_
  have hs3 := hs2.of_keeps k3 (by decide)
  -- `x` and its value in slot 1
  have fx : fe s2.mem base X2 = (E s.mem base xo).val := by
    rw [v2, show fe s1.mem base X2 = fe s.mem base (slot xo.val) from VG.Proof.X448.Radix16.valN_congr f1]; rfl
  have zero : (∀ i < 28, limbs s2.mem base X2 i = 0) ↔ E s.mem base xo = 0 := by
    rw [VG.Proof.Ed448.Arm.fe_zero_iff b2, fx]; exact Fin.val_eq_zero_iff
  have sign3 : word s3.mem base SIGN = BitVec.ofNat 32 sb := by
    rw [m3, m2.word (Or.inl (by simp only [SIGN]; omega)) (by decide),
      m1.word (Or.inl (by simp only [SIGN]; omega)) (by decide), hsign]
  rw [zero] at r3z
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.signTail_ok hs3 r3b r3z hsb sign3) fun s4 ⟨b4, c4, m4, k4⟩ => ?_
  have hs4 := hs3.of_keeps k4 (by decide)
  have bd4 : BoundedEnv s4.mem base := by
    intro i j hj
    by_cases h1 : i = 1
    · subst i; rw [m4, m3]; exact b2 j hj
    · have si := VG.Proof.Ed448.Arm.slot_range i
      have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep h1
      rw [m4, m3, m2.limbs s1i (by omega) hj, m1.limbs (by omega) (by omega) hj]; exact hb i j hj
  refine WP.mono (cswapE hs4 bd4 xo 12 hx12 c4) fun t ⟨kt, bt, _, et⟩ => ?_
  have e4 : ∀ i : Index, i ≠ 1 → E s4.mem base i = E s.mem base i := by
    intro i h1
    have si := VG.Proof.Ed448.Arm.slot_range i
    have s1i : slot i.val + 112 ≤ X2 ∨ X2 + 112 ≤ slot i.val := by rw [hX2]; exact slot_sep h1
    simp only [E, F]
    rw [m4, m3, m2.fe s1i (by omega), m1.fe (by omega) (by omega)]
  have l0 : limbs s3.mem base X2 0 % 2 = (E s.mem base xo).val % 2 := by
    rw [m3, ← fe_mod2, fx]
  refine ⟨⟨?_, ?_⟩, bt, ?_, ?_, fun i h1 h12 hx => ?_⟩
  · refine (((k1.mono ?_).trans ((k2.mono ?_).trans ((k3.mono ?_).trans (k4.mono ?_)))).trans
      (kt.regs.mono ?_)) <;> intro r hr <;> revert r <;> decide
  · have e : s4.mem = s2.mem := by rw [m4, m3]
    exact ((VG.Proof.Ed448.Arm.outC m1 (by decide) (by decide)).trans (VG.Proof.Ed448.Arm.fmC m2 (by decide) (by decide))).trans
      (by rw [← e]; exact kt.mem)
  · have r12 : s3.gpr .r12 = s.gpr .r12 := by
      rw [k3.1 _ (by decide), k2.1 _ (by decide), k1.1 _ (by decide)]
    rw [kt.regs.1 _ (by decide), ← r12]
    exact b4
  · rw [et]
    simp only [opSwap, Function.update_of_ne hx12, Function.update_self]
    rw [e4 xo hx1, e4 12 (by decide), hneg, l0, VG.Proof.Ed448.Arm.sel_sign _ (Nat.mod_lt _ (by decide)) sb hsb]
    cases ((E s.mem base xo).val % 2 == 1) == (sb == 1) <;> rfl
  · rw [et]
    simp only [opSwap, Function.update_of_ne h12, Function.update_of_ne hx]
    exact e4 i h1

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyRoot`. -/
section

/-!
# Ed448 verification's equation on ARMv7: the square root's power

`root`: X448's addition chain for the inversion as far as `z^(2^223 - 1)`,
then 223 squarings and a multiplication, for `z` in slot 12, into slot 1 with
the temporaries 14–20: `Proof.Ed448.rootPow`, `z^((p-3)/4)`.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Impl.X448.Arm (slot X2)

/-- The field slots after `root`. -/
def rootEnv (e : Env) : Env :=
  let e := applyOps [.copy 14 12] e
  let e := opSqn 14 1 e
  let e := applyOps [.mul 14 14 12, .copy 15 14] e
  let e := opSqn 15 2 e
  let e := applyOps [.mul 15 15 14, .copy 16 15] e
  let e := opSqn 16 4 e
  let e := applyOps [.mul 16 16 15, .copy 17 16] e
  let e := opSqn 17 8 e
  let e := applyOps [.mul 17 17 16, .copy 18 17] e
  let e := opSqn 18 16 e
  let e := applyOps [.mul 18 18 17, .copy 19 18] e
  let e := opSqn 19 32 e
  let e := applyOps [.mul 19 19 18, .copy 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 64 e
  let e := applyOps [.mul 20 20 19] e
  let e := opSqn 20 16 e
  let e := applyOps [.mul 20 20 17] e
  let e := opSqn 20 8 e
  let e := applyOps [.mul 20 20 16] e
  let e := opSqn 20 4 e
  let e := applyOps [.mul 20 20 15] e
  let e := opSqn 20 2 e
  let e := applyOps [.mul 20 20 14, .copy 1 20] e
  let e := opSqn 1 1 e
  let e := applyOps [.mul 1 1 12] e
  let e := opSqn 1 223 e
  applyOps [.mul 1 1 20] e

theorem root_spec (base : Addr) : ISpec base root VG.Proof.Ed448.Arm.rootEnv := by
  have h : ISpec base _ _ :=
    (opsI base [.copy 14 12]).seq <|
    (sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 14 14 12, .copy 15 14]).seq <|
    (sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 19]).seq <|
    (sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 17]).seq <|
    (sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 16]).seq <|
    (sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 15]).seq <|
    (sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (opsI base [.mul 20 20 14, .copy 1 20]).seq <|
    (sqnI base 1 (n := 1) (by decide) (by decide)).seq <|
    (opsI base [.mul 1 1 12]).seq <|
    (sqnI base 1 (n := 223) (by decide) (by decide)).seq <|
    (opsI base [.mul 1 1 20])
  exact h

theorem rootEnv_eval (e : Env) : VG.Proof.Ed448.Arm.rootEnv e 1 = Proof.Ed448.rootPow (e 12) := by
  simp only [↓reduceIte, VG.Proof.Ed448.Arm.rootEnv, applyOps, FieldOp.apply, VG.Proof.X448.Arm.opMul, opCopy, opSqn,
    Function.update_apply]
  rfl

theorem rootEnv_keep (e : Env) (i : Index) (hi : i ≠ 1 ∧ (i.val < 14 ∨ 20 < i.val)) :
    VG.Proof.Ed448.Arm.rootEnv e i = e i := by
  have h14 : i ≠ 14 := fun h => by subst h; omega
  have h15 : i ≠ 15 := fun h => by subst h; omega
  have h16 : i ≠ 16 := fun h => by subst h; omega
  have h17 : i ≠ 17 := fun h => by subst h; omega
  have h18 : i ≠ 18 := fun h => by subst h; omega
  have h19 : i ≠ 19 := fun h => by subst h; omega
  have h20 : i ≠ 20 := fun h => by subst h; omega
  simp only [VG.Proof.Ed448.Arm.rootEnv, applyOps, FieldOp.apply, VG.Proof.X448.Arm.opMul, opCopy, opSqn,
    Function.update_of_ne hi.1, Function.update_of_ne h14, Function.update_of_ne h15,
    Function.update_of_ne h16, Function.update_of_ne h17, Function.update_of_ne h18,
    Function.update_of_ne h19, Function.update_of_ne h20]

theorem root_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) :
    WP isa root s fun t =>
      IKeep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = VG.Proof.Ed448.Arm.rootEnv (E s.mem base) :=
  VG.Proof.Ed448.Arm.root_spec base s hs hb

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyDecode`. -/
section

/-!
# Ed448 verification's equation on ARMv7: decoding a point

`decode_ok`: `decode p xo yo` on the 57 bytes at `q` (RFC 8032 §5.2.3):
`BAD |= 0` exactly when they decode, and then the point is `(x : y : 1)` with
`x` in slot `xo` and `y` in slot `yo` (by `Proof.Ed448.decodePoint_impl`,
given `RecoverOk`). The steps' field values: `u = y² - 1`, `v = d y² - 1`,
`t = u³v`, `x = t (t (uv)²)^((p-3)/4)`, the check `v x² = u`, and the sign.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm VG.Proof.X448.Radix16
open VG.Impl.X448.Arm (slot X2 ACC)
open VG.Proof.Ed448 (RecoverOk rootPow)

/-! ## The field steps -/

theorem decodeUV_eval (e : Env) (xo yo : Index) (h : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9) :
    applyOps (VG.Proof.Ed448.Arm.decodeUVF yo xo) e 13 = e yo * e yo - e 10 ∧
    applyOps (VG.Proof.Ed448.Arm.decodeUVF yo xo) e 3 = e 11 * (e yo * e yo) - e 10 ∧
    applyOps (VG.Proof.Ed448.Arm.decodeUVF yo xo) e xo = (e yo * e yo - e 10) * (e yo * e yo - e 10) *
      (e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10) ∧
    applyOps (VG.Proof.Ed448.Arm.decodeUVF yo xo) e 12 = (e yo * e yo - e 10) * (e yo * e yo - e 10) *
      (e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10) *
      (((e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10)) *
        ((e yo * e yo - e 10) * (e 11 * (e yo * e yo) - e 10))) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem decodeUV_keep (e : Env) (xo yo : Index) (h : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9) (i : Index)
    (hi : i ≠ 3 ∧ i ≠ 4 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 13 ∧ i ≠ xo) :
    applyOps (VG.Proof.Ed448.Arm.decodeUVF yo xo) e i = e i := by
  refine VG.Proof.Ed448.Arm.applyOps_keep _ _ ?_
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> revert i <;> decide

theorem decodeX_eval (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) :
    applyOps (VG.Proof.Ed448.Arm.decodeXF xo) e xo = e xo * e 1 ∧
    applyOps (VG.Proof.Ed448.Arm.decodeXF xo) e 12 = e 3 * ((e xo * e 1) * (e xo * e 1)) := by
  rcases h with rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem decodeX_keep (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) (i : Index) (hi : i ≠ 12 ∧ i ≠ xo) :
    applyOps (VG.Proof.Ed448.Arm.decodeXF xo) e i = e i := by
  refine VG.Proof.Ed448.Arm.applyOps_keep _ _ ?_
  rcases h with rfl | rfl <;> revert i <;> decide

theorem negX_eval (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) :
    applyOps (VG.Proof.Ed448.Arm.negXF xo) e 12 = (e xo - e xo) - e xo := by
  rcases h with rfl | rfl <;> rfl

theorem negX_keep (e : Env) (xo : Index) (h : xo = 6 ∨ xo = 8) (i : Index) (hi : i ≠ 12) :
    applyOps (VG.Proof.Ed448.Arm.negXF xo) e i = e i := by
  refine VG.Proof.Ed448.Arm.applyOps_keep _ _ ?_
  rcases h with rfl | rfl <;> revert i <;> decide

/-! ## The bytes -/

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

theorem decodeLE_56 (m : Mem) (p : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 56) = VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded m p) 28 := by
  rw [Proof.Ed448.decodeLE_eq, show (56 : Nat) = 2 * 28 from rfl]
  exact VG.Proof.X448.Radix16.decoded_val m p 28

/-! ## Decoding -/

theorem decode_ok (hR : RecoverOk) {s : State} {base q : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {p : Reg} (hp : p = .r8 ∨ p = .r10) (hq : State.addr (s.gpr p) = q) (hfit : (s.gpr p).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (q + BitVec.ofNat 64 j))
    (xo yo : Index) (hxy : xo = 6 ∧ yo = 7 ∨ xo = 8 ∧ yo = 9)
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d) :
    WP isa (decode p xo.val yo.val) s fun t =>
      VG.Proof.Ed448.Arm.VKeep base s t ∧ BoundedEnv t.mem base ∧
      VG.Proof.Ed448.Arm.BadUpd ((Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem q 57)).isSome) (s.gpr .r12) (t.gpr .r12) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem q 57) = some a →
        E t.mem base xo = a.X ∧ E t.mem base yo = a.Y ∧ a.Z = 1) ∧
      (∀ i : Index, i ≠ xo → i ≠ yo → (i.val = 0 ∨ i.val = 2 ∨ (6 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21) →
        E t.mem base i = E s.mem base i) := by
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hx1 : xo ≠ 1 := by rcases hxo with rfl | rfl <;> decide
  unfold decode
  -- `y`, the sign bit, and the first checks
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.decodeY_ok hs hb hp hq hfit hr hd yo hy1)
    fun s1 ⟨k1, b1, sg1, c1, y1, e1⟩ => ?_)
  have hs1 := k1.scr hs
  -- `u`, `v`, `t` and `t (uv)²`
  rw [← VG.Proof.Ed448.Arm.decodeUVF_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs1 b1 (VG.Proof.Ed448.Arm.decodeUVF yo xo)) fun s2 ⟨k2, b2, e2⟩ => ?_)
  have hs2 := k2.scr hs1
  -- the root
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.root_ok hs2 b2) fun s3 ⟨k3, b3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  -- `x` and `v x²`
  rw [← VG.Proof.Ed448.Arm.decodeXF_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs3 b3 (VG.Proof.Ed448.Arm.decodeXF xo)) fun s4 ⟨k4, b4, e4⟩ => ?_)
  have hs4 := k4.scr hs3
  -- `v x² = u`
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.eqSlots_ok hs4 b4 12 13 (by decide) (by decide) (by decide))
    fun s5 ⟨k5, b5, e5, c5⟩ => ?_)
  have hs5 := k5.scr hs4
  -- `-x`
  rw [← VG.Proof.Ed448.Arm.negXF_impl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs5 b5 (VG.Proof.Ed448.Arm.negXF xo)) fun s6 ⟨k6, b6, e6⟩ => ?_)
  have hs6 := k6.scr hs5
  -- the sign
  have hb128 : (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (q + BitVec.ofNat 64 56)).isLt; omega
  have K16 : VG.Proof.Ed448.Arm.CKeep base s1 s6 :=
    (Keep.toC k2).trans ((IKeep.toC k3).trans ((Keep.toC k4).trans (k5.trans (Keep.toC k6))))
  have sg : word s6.mem base SIGN = BitVec.ofNat 32 ((s.mem (q + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [K16.mem.word (Or.inl (by simp only [SIGN]; omega)) (Or.inl (by simp only [SIGN, ACC]; omega))
      (by decide), sg1]
  -- the values
  have h10' : E s1.mem base 10 = 1 := by
    rw [e1 10 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1 11 (by decide) (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, v2, t2, w2⟩ := VG.Proof.Ed448.Arm.decodeUV_eval (E s1.mem base) xo yo hxy
  simp only [h10', h11', y1, ← e2] at u2 v2 t2 w2
  generalize hY : Proof.X448.toFe (VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28) = Y at *
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  have r31 : E s3.mem base 1 = rootPow (E s2.mem base 12) := by rw [e3, VG.Proof.Ed448.Arm.rootEnv_eval]
  have r3k : ∀ i : Index, i ≠ 1 → (i.val < 14 ∨ 20 < i.val) → E s3.mem base i = E s2.mem base i :=
    fun i h1 h2 => by rw [e3, VG.Proof.Ed448.Arm.rootEnv_keep _ _ ⟨h1, h2⟩]
  have hxlt : xo.val < 14 := by rcases hxo with rfl | rfl <;> decide
  obtain ⟨x4, w4⟩ := VG.Proof.Ed448.Arm.decodeX_eval (E s3.mem base) xo hxo
  rw [← e4, r3k xo hx1 (Or.inl hxlt), t2, r31, w2] at x4
  rw [← e4, r3k xo hx1 (Or.inl hxlt), t2, r31, w2, r3k 3 (by decide) (Or.inl (by decide)), v2] at w4
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  have x5 : E s5.mem base xo = x := by rw [e5 xo hx1, x4]
  have w5 : E s5.mem base 12 = v * (x * x) := by rw [e5 12 (by decide), w4]
  have u4 : E s4.mem base 13 = u := by
    rw [e4, VG.Proof.Ed448.Arm.decodeX_keep _ xo hxo 13 ⟨by decide, by rcases hxo with rfl | rfl <;> decide⟩,
      r3k 13 (by decide) (Or.inl (by decide)), u2]
  have n6 : E s6.mem base 12 = (E s6.mem base xo - E s6.mem base xo) - E s6.mem base xo := by
    rw [e6, VG.Proof.Ed448.Arm.negX_eval _ xo hxo, VG.Proof.Ed448.Arm.negX_keep _ xo hxo xo (by rcases hxo with rfl | rfl <;> decide)]
  refine WP.mono (VG.Proof.Ed448.Arm.decodeSign_ok hs6 b6 xo hxo hb128 sg n6) fun t ⟨kt, bt, ct, xt, et⟩ => ?_
  have x6 : E s6.mem base xo = x := by
    rw [e6, VG.Proof.Ed448.Arm.negX_keep _ xo hxo xo (by rcases hxo with rfl | rfl <;> decide), x5]
  rw [x6] at ct xt
  rw [w4, u4] at c5
  -- `decodePoint`
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem q 57) (VG.Proof.Ed448.Arm.bytesAt57_len _ _)
    (VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28) ((s.mem (q + BitVec.ofNat 64 56)).toNat)
    (by rw [VG.Proof.Ed448.Arm.bytesAt57_take, VG.Proof.Ed448.Arm.decodeLE_56]) (by rw [VG.Proof.Ed448.Arm.bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  -- what is kept
  have r12 : ∀ {a b : State}, Keep base a b → b.gpr .r12 = a.gpr .r12 := fun h => h.regs.1 _ (by decide)
  have r12i : s3.gpr .r12 = s2.gpr .r12 := k3.regs.1 _ (by decide)
  have kY : E t.mem base yo = Y := by
    rw [et yo hy1 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide) hyx,
      e6, VG.Proof.Ed448.Arm.negX_keep _ xo hxo yo (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), e5 yo hy1, e4,
      VG.Proof.Ed448.Arm.decodeX_keep _ xo hxo yo ⟨by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide, hyx⟩,
      r3k yo hy1 (Or.inl (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide)), e2,
      VG.Proof.Ed448.Arm.decodeUV_keep _ xo yo hxy yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide), y1]
  refine ⟨k1.trans ((Keep.toV k2).trans ((IKeep.toV k3).trans ((Keep.toV k4).trans
    ((CKeep.toV k5).trans ((Keep.toV k6).trans (CKeep.toV kt)))))), bt, ?_, fun a ha => ?_,
    fun i hix hiy hi => ?_⟩
  · have c5' : VG.Proof.Ed448.Arm.BadUpd (v * (x * x) = u) (s1.gpr .r12) (s5.gpr .r12) := by
      rw [← r12 k2, ← r12i, ← r12 k4]; exact c5
    have ct' : VG.Proof.Ed448.Arm.BadUpd (¬(x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)) (s5.gpr .r12)
        (t.gpr .r12) := by
      rw [← r12 k6]; exact ct
    refine ((c1.trans c5').trans ct').congr ?_
    rw [hD]
    by_cases hall : ((s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [hD] at ha
    by_cases hall : ((s.mem (q + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        VG.Proof.X448.Radix16.valN (VG.Proof.X448.Radix16.decoded s.mem q) 28 < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (q + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at ha
      cases ha
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at ha
      cases ha
  · have h1 : i ≠ 1 := fun h => by subst h; omega
    have h12 : i ≠ 12 := fun h => by subst h; omega
    rw [et i h1 h12 hix, e6, VG.Proof.Ed448.Arm.negX_keep _ xo hxo i h12, e5 i h1, e4, VG.Proof.Ed448.Arm.decodeX_keep _ xo hxo i ⟨h12, hix⟩,
      r3k i h1 (by omega), e2, VG.Proof.Ed448.Arm.decodeUV_keep _ xo yo hxy i ⟨fun h => by subst h; omega,
        fun h => by subst h; omega, fun h => by subst h; omega, h12, fun h => by subst h; omega, hix⟩,
      e1 i h1 hiy]

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyFinish`. -/
section

/-!
# Ed448 verification's equation on ARMv7: the comparison and the result

`vfinish_ok`: `Q` (slots 0, 21, 2) and `R` (slots 8–10) doubled twice and
compared projectively, `BAD |= 0` exactly when they represent the same point;
`r0 = 1` exactly when `BAD` is then 0, and the callee-saved registers
restored.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (double)
open VG.Impl.X448.Arm (slot ACC saved ld ops Op)

/-- `[4]Q` and `[4]R`, doubling `Q` twice and then `R` twice. -/
def vcompare : List FieldOp := VG.Proof.Ed448.Arm.doubleF 0 21 2 ++ VG.Proof.Ed448.Arm.doubleF 0 21 2 ++ VG.Proof.Ed448.Arm.doubleF 8 9 10 ++ VG.Proof.Ed448.Arm.doubleF 8 9 10

theorem compare_eval (e : Env) :
    VG.Proof.Ed448.Arm.pt (applyOps VG.Proof.Ed448.Arm.vcompare e) 0 21 2 = double (double (VG.Proof.Ed448.Arm.pt e 0 21 2)) ∧
    VG.Proof.Ed448.Arm.pt (applyOps VG.Proof.Ed448.Arm.vcompare e) 8 9 10 = double (double (VG.Proof.Ed448.Arm.pt e 8 9 10)) := by
  simp only [VG.Proof.Ed448.Arm.vcompare, VG.Proof.Ed448.Arm.applyOps_append]
  generalize h1 : applyOps (VG.Proof.Ed448.Arm.doubleF 0 21 2) e = e1
  generalize h2 : applyOps (VG.Proof.Ed448.Arm.doubleF 0 21 2) e1 = e2
  generalize h3 : applyOps (VG.Proof.Ed448.Arm.doubleF 8 9 10) e2 = e3
  generalize h4 : applyOps (VG.Proof.Ed448.Arm.doubleF 8 9 10) e3 = e4
  refine ⟨?_, ?_⟩
  · rw [VG.Proof.Ed448.Arm.pt_congr' (by rw [← h4, VG.Proof.Ed448.Arm.doubleF_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h4, VG.Proof.Ed448.Arm.doubleF_keep8 _ _ (Or.inr (Or.inr (Or.inr (by decide))))])
      (by rw [← h4, VG.Proof.Ed448.Arm.doubleF_keep8 _ _ (Or.inl (by decide))]),
      VG.Proof.Ed448.Arm.pt_congr' (by rw [← h3, VG.Proof.Ed448.Arm.doubleF_keep8 _ _ (Or.inl (by decide))])
      (by rw [← h3, VG.Proof.Ed448.Arm.doubleF_keep8 _ _ (Or.inr (Or.inr (Or.inr (by decide))))])
      (by rw [← h3, VG.Proof.Ed448.Arm.doubleF_keep8 _ _ (Or.inl (by decide))]),
      ← h2, VG.Proof.Ed448.Arm.doubleF_eval0, ← h1, VG.Proof.Ed448.Arm.doubleF_eval0]
  · rw [← h4, VG.Proof.Ed448.Arm.doubleF_eval8, ← h3, VG.Proof.Ed448.Arm.doubleF_eval8,
      VG.Proof.Ed448.Arm.pt_congr' (by rw [← h2, VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h2, VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl (by decide))]) (by rw [← h2, VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl (by decide))]),
      VG.Proof.Ed448.Arm.pt_congr' (by rw [← h1, VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl (by decide))])
      (by rw [← h1, VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl (by decide))]) (by rw [← h1, VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl (by decide))])]

/-- `r1 = (r12 == 0)`. -/
theorem isZeroR1_ok {s : State} (h12 : (s.gpr .r12).toNat < 65536) :
    WP isa (.block [.dp .sub .r1 .r12 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31)]) s fun t =>
      t.gpr .r1 = (if s.gpr .r12 = 0 then 1 else 0) ∧ t.mem = s.mem ∧ Keeps [.r1] s t := by
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsr (by decide)) fun t ht =>
    WP.block_nil ⟨?_, by rw [ht.mem, hu.mem], rest_keeps ((hu.rest (by decide)).trans (ht.rest (by decide)))⟩
  rw [ht.gpr, hu.gpr]
  exact VG.Proof.Ed448.Arm.isZero16 _ h12

theorem ops_seq {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (xs : List FieldOp)
    {c : Prog isa} {Q : State → Prop}
    (k : ∀ t, Keep base s t → BoundedEnv t.mem base → E t.mem base = applyOps xs (E s.mem base) → WP isa c t Q) :
    WP isa (.seq (ops (xs.map FieldOp.impl)) c) s Q :=
  WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs hb xs) fun t ⟨kt, bt, et⟩ => k t kt bt et)

theorem vtail_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : VG.Proof.X448.Arm.Saved base g s.mem) (h12 : (s.gpr .r12).toNat < 65536) :
    WP isa (.block (eqSlots (slot 12) (slot 13) ++
      ([.dp .sub .r1 .r12 (.imm 1), .mov .r1 (.shifted .r1 .lsr 31)] : List Instr) ++
      (List.range 8).map (fun i => ld (saved[i]!) (4 * i)) ++ ([.mov .r0 (.reg .r1)] : List Instr))) s fun t =>
      t.gpr .r0 = (if s.gpr .r12 = 0 ∧ E s.mem base 12 = E s.mem base 13 then 1 else 0) ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧
      (∀ r, r ∉ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved → t.gpr r = s.gpr r) := by
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.eqSlots_ok hs hb 12 13 (by decide) (by decide) (by decide))
    fun s1 ⟨k1, _, _, ⟨c, hc, hcz, he⟩⟩ => ?_
  have hs1 := k1.scr hs
  have h12' : (s1.gpr .r12).toNat < 65536 := by
    rw [he, BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) h12 hc
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.isZeroR1_ok h12') fun s2 ⟨r2, m2, k2⟩ => ?_
  have hs2 := hs1.of_keeps k2 (by decide)
  have sv2 : VG.Proof.X448.Arm.Saved base g s2.mem := by
    rw [m2]; exact hsv.outside2 k1.mem (by decide) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.X448.Arm.restore_ok hs2 sv2) fun s3 ⟨r3, m3, k3⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [ht.gpr, k3.1 _ (by decide), r2, he]
    refine if_congr ?_ rfl rfl
    exact BitVec.or_eq_zero_iff.trans (and_congr_right fun _ => hcz)
  · intro i hi
    rw [ht.other _ (by revert i; decide), r3 i hi]
  · intro r hr
    have a1 : ∀ x ∈ [Reg.r0], x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a2 : ∀ x ∈ saved, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a3 : ∀ x ∈ [Reg.r1], x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a4 : ∀ x ∈ Reg.r12 :: .r11 :: workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by
      decide
    rw [ht.other r (fun h => hr (a1 r (h ▸ List.mem_singleton_self _))), k3.1 r (fun h => hr (a2 r h)),
      k2.1 r (fun h => hr (a3 r h)), k1.regs.1 r (fun h => hr (a4 r h))]

theorem vfinish_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {g : Reg → BitVec 32} (hsv : VG.Proof.X448.Arm.Saved base g s.mem) (h12 : (s.gpr .r12).toNat < 65536) :
    WP isa vfinish s fun t =>
      t.gpr .r0 = (if s.gpr .r12 = 0 ∧ Spec.Ed448.pointEqual (double (double (VG.Proof.Ed448.Arm.pt (E s.mem base) 0 21 2)))
        (double (double (VG.Proof.Ed448.Arm.pt (E s.mem base) 8 9 10))) = true then 1 else 0) ∧
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧
      (∀ r, r ∉ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved → t.gpr r = s.gpr r) := by
  unfold vfinish
  rw [show VG.Impl.Ed448.Arm.doubleAt 0 21 2 = (VG.Proof.Ed448.Arm.doubleF 0 21 2).map FieldOp.impl from rfl,
    show VG.Impl.Ed448.Arm.doubleAt 8 9 10 = (VG.Proof.Ed448.Arm.doubleF 8 9 10).map FieldOp.impl from rfl]
  refine VG.Proof.Ed448.Arm.ops_seq hs hb _ fun sa ka ba ea => ?_
  refine VG.Proof.Ed448.Arm.ops_seq (ka.scr hs) ba _ fun sb kb bb eb => ?_
  refine VG.Proof.Ed448.Arm.ops_seq (kb.scr (ka.scr hs)) bb _ fun sc kc bc ec => ?_
  refine VG.Proof.Ed448.Arm.ops_seq (kc.scr (kb.scr (ka.scr hs))) bc _ fun sd kd bd ed => ?_
  have hsd := kd.scr (kc.scr (kb.scr (ka.scr hs)))
  rw [show ([.mul (slot 12) (slot 0) (slot 10), .mul (slot 13) (slot 8) (slot 2)] : List Op) =
    ([.mul 12 0 10, .mul 13 8 2] : List FieldOp).map FieldOp.impl from rfl]
  refine VG.Proof.Ed448.Arm.ops_seq hsd bd _ fun s1 k1 b1 e1 => ?_
  have hs1 := k1.scr hsd
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.eqSlots_ok hs1 b1 12 13 (by decide) (by decide) (by decide))
    fun s2 ⟨k2, b2, e2, c2⟩ => ?_)
  have hs2 := k2.scr hs1
  rw [show ([.mul (slot 12) (slot 21) (slot 10), .mul (slot 13) (slot 9) (slot 2)] : List Op) =
    ([.mul 12 21 10, .mul 13 9 2] : List FieldOp).map FieldOp.impl from rfl]
  refine VG.Proof.Ed448.Arm.ops_seq hs2 b2 _ fun s3 k3 b3 e3 => ?_
  have hs3 := k3.scr hs2
  have sv3 : VG.Proof.X448.Arm.Saved base g s3.mem :=
    ((((((hsv.outside2 ka.mem (by decide) (by decide)).outside2 kb.mem (by decide) (by decide)).outside2
      kc.mem (by decide) (by decide)).outside2 kd.mem (by decide) (by decide)).outside2 k1.mem (by decide)
      (by decide)).outside2 k2.mem (by decide) (by decide)).outside2 k3.mem (by decide) (by decide)
  obtain ⟨c, hc, hcz, he⟩ := c2
  have r12 : s3.gpr .r12 = s1.gpr .r12 ||| c := by
    rw [k3.regs.1 _ (by decide)]; exact he
  have r12' : s1.gpr .r12 = s.gpr .r12 := by
    rw [k1.regs.1 _ (by decide), kd.regs.1 _ (by decide), kc.regs.1 _ (by decide), kb.regs.1 _ (by decide),
      ka.regs.1 _ (by decide)]
  rw [r12'] at r12
  have h12' : (s3.gpr .r12).toNat < 65536 := by
    rw [r12, BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 16) h12 hc
  refine WP.mono (VG.Proof.Ed448.Arm.vtail_ok hs3 b3 sv3 h12') fun t ⟨rt, st, gt⟩ => ⟨?_, st, fun r hr => ?_⟩
  · rw [rt]
    refine if_congr ?_ rfl rfl
    -- the values
    have ed' : E sd.mem base = applyOps VG.Proof.Ed448.Arm.vcompare (E s.mem base) := by
      rw [ed, ec, eb, ea]; simp only [VG.Proof.Ed448.Arm.vcompare, VG.Proof.Ed448.Arm.applyOps_append]
    obtain ⟨q4, r4⟩ := VG.Proof.Ed448.Arm.compare_eval (E s.mem base)
    rw [← ed'] at q4 r4
    have x12 : E s3.mem base 12 = E sd.mem base 21 * E sd.mem base 10 := by
      rw [e3, show ∀ e : Env, applyOps [.mul 12 21 10, .mul 13 9 2] e 12 = e 21 * e 10 from fun _ => rfl,
        e2 21 (by decide), e2 10 (by decide), e1]; rfl
    have x13 : E s3.mem base 13 = E sd.mem base 9 * E sd.mem base 2 := by
      rw [e3, show ∀ e : Env, applyOps [.mul 12 21 10, .mul 13 9 2] e 13 = e 9 * e 2 from fun _ => rfl,
        e2 9 (by decide), e2 2 (by decide), e1]; rfl
    have y12 : E s1.mem base 12 = E sd.mem base 0 * E sd.mem base 10 := by rw [e1]; rfl
    have y13 : E s1.mem base 13 = E sd.mem base 8 * E sd.mem base 2 := by rw [e1]; rfl
    rw [r12]
    refine (and_congr_left fun _ => BitVec.or_eq_zero_iff).trans ?_
    change (s.gpr .r12 = 0 ∧ c = 0) ∧ E s3.mem base 12 = E s3.mem base 13 ↔ _
    rw [hcz, x12, x13, y12, y13, ← q4, ← r4]
    simp only [Spec.Ed448.pointEqual, VG.Proof.Ed448.Arm.pt, Bool.and_eq_true, beq_iff_eq, and_assoc]
  · have a1 : ∀ x ∈ workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by decide
    have a2 : ∀ x ∈ Reg.r12 :: .r11 :: workRegs, x ∈ .r0 :: .r1 :: .r12 :: .r11 :: workRegs ++ saved := by
      decide
    rw [gt r hr, k3.regs.1 r (fun h => hr (a1 r h)), k2.regs.1 r (fun h => hr (a2 r h)),
      k1.regs.1 r (fun h => hr (a1 r h)), kd.regs.1 r (fun h => hr (a1 r h)),
      kc.regs.1 r (fun h => hr (a1 r h)), kb.regs.1 r (fun h => hr (a1 r h)),
      ka.regs.1 r (fun h => hr (a1 r h))]

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyLit`. -/
section

/-!
# Ed448 verification's equation on ARMv7: the code as a literal

The kernel checks the literal once.

The constant-time analysis, from the arguments alone, reads neither the
offsets of loads and stores nor the immediates of `movw`
(`Proof/Framework/Arm/TaintErase.lean`), so it checks the code without them,
`verifyEquationErased`: there the field operations on the working space's
slots (some 150 multiplications) are the same code, which its literal
shares, and the kernel analyses each once from the same taint rather than
every copy.
-/

namespace VG

materialize_code Impl.Ed448.Arm.verifyEquation

/-- `verifyEquation` without its offsets. -/
def Proof.Ed448.Arm.verifyEquationErased : Prog Arm.isa :=
  Arm.Code.eraseOff Impl.Ed448.Arm.verifyEquation

materialize_code Proof.Ed448.Arm.verifyEquationErased

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyLocal`. -/
section

/-!
# Ed448 verification's equation on ARMv7: the contract the proof is written against

The facts of `Spec.Ed448.verifyEquationContract` the proof uses, stated for
ARMv7, in a module of their own: callers proven for any code meeting them
need not import the proof.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm

/-- `vg_ed448_verify_equation(pk = r0, signature = r1, challenge = r2, scratch = r3) -> r0`. -/
def verifyEquationLocal : Contract Arm.isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let sig : Region := ⟨State.addr (s.gpr .r1), 114⟩
    let ch : Region := ⟨State.addr (s.gpr .r2), 57⟩
    let ws : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [pk, sig, ch] ∧ s.wr = [ws] ∧ pk.Disjoint ws ∧ sig.Disjoint ws ∧ ch.Disjoint ws ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 114 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s t := t.gpr .r0 = if Spec.Ed448.verifyEquation
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r0)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 114)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57) then 1 else 0
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.sp = t.sp

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyLoop`. -/
section

/-!
# Ed448 verification's equation on ARMv7: `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for bit `t` of `S` and of `k` (bits 0
and 1 of byte `t` at `BITS`): `Q` (slots 0, 21, 2) doubled, then `B` (slots
8–10) added and swapped in by the first bit, and `-A` (slots 6, 7 and 10) by
the second. The loop's invariant (`VInv`): `Q` is the reference ladder's
point after the bits above `n` (`Proof.Ed448.vladder`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X448.Arm
open VG.Proof.Ed448 (double vladder vstepRef vladder_bit bitAt)
open VG.Impl.X448.Arm (BITS slot ACC)

/-! ## The values -/

/-- The slots after a swap of `T` into `Q`. -/
def swapEnv (sw : Bool) (e : Env) : Env := opSwap 2 5 sw (opSwap 21 4 sw (opSwap 0 3 sw e))

/-- The slots after an iteration, for the bits `sw₁` (of `S`) and `sw₂` (of `k`). -/
def vstepEnv (sw₁ sw₂ : Bool) (e : Env) : Env :=
  VG.Proof.Ed448.Arm.swapEnv sw₂ (applyOps (VG.Proof.Ed448.Arm.addF 6 7) (VG.Proof.Ed448.Arm.swapEnv sw₁ (applyOps (VG.Proof.Ed448.Arm.addF 8 9) (applyOps (VG.Proof.Ed448.Arm.doubleF 0 21 2) e))))

theorem swapEnv_keep (sw : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    VG.Proof.Ed448.Arm.swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by subst h; omega
  have h2 : i ≠ 2 := fun h => by subst h; omega
  have h3 : i ≠ 3 := fun h => by subst h; omega
  have h4 : i ≠ 4 := fun h => by subst h; omega
  have h5 : i ≠ 5 := fun h => by subst h; omega
  have h21 : i ≠ 21 := fun h => by subst h; omega
  simp only [VG.Proof.Ed448.Arm.swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h2, Function.update_of_ne h3,
    Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h21]

theorem pt_swap (sw : Bool) (e : Env) :
    VG.Proof.Ed448.Arm.pt (VG.Proof.Ed448.Arm.swapEnv sw e) 0 21 2 = if sw then VG.Proof.Ed448.Arm.pt e 3 4 5 else VG.Proof.Ed448.Arm.pt e 0 21 2 := by
  cases sw <;> rfl

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Env) :
    VG.Proof.Ed448.Arm.pt (VG.Proof.Ed448.Arm.vstepEnv sw₁ sw₂ e) 0 21 2 =
      let r₁ := double (VG.Proof.Ed448.Arm.pt e 0 21 2)
      let r₂ := if sw₁ then VG.Proof.Ed448.Arm.addWith (e 11) r₁ (VG.Proof.Ed448.Arm.pt e 8 9 10) else r₁
      if sw₂ then VG.Proof.Ed448.Arm.addWith (e 11) r₂ (VG.Proof.Ed448.Arm.pt e 6 7 10) else r₂ := by
  unfold VG.Proof.Ed448.Arm.vstepEnv
  generalize he0 : applyOps (VG.Proof.Ed448.Arm.doubleF 0 21 2) e = e0
  have p0 : VG.Proof.Ed448.Arm.pt e0 0 21 2 = double (VG.Proof.Ed448.Arm.pt e 0 21 2) := by rw [← he0, VG.Proof.Ed448.Arm.doubleF_eval0]
  have k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl hi)]
  generalize he1 : applyOps (VG.Proof.Ed448.Arm.addF 8 9) e0 = e1
  have p1 : VG.Proof.Ed448.Arm.pt e1 3 4 5 = VG.Proof.Ed448.Arm.addWith (e0 11) (VG.Proof.Ed448.Arm.pt e0 0 21 2) (VG.Proof.Ed448.Arm.pt e0 8 9 10) := by rw [← he1, VG.Proof.Ed448.Arm.addF_eval8]
  have q1 : VG.Proof.Ed448.Arm.pt e1 0 21 2 = VG.Proof.Ed448.Arm.pt e0 0 21 2 :=
    VG.Proof.Ed448.Arm.pt_congr' (by rw [← he1, VG.Proof.Ed448.Arm.addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
      (by rw [← he1, VG.Proof.Ed448.Arm.addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inr (Or.inr (by decide)))])
      (by rw [← he1, VG.Proof.Ed448.Arm.addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
  have k1 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, VG.Proof.Ed448.Arm.addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inr (Or.inl hi))]
  generalize he2 : VG.Proof.Ed448.Arm.swapEnv sw₁ e1 = e2
  have p2 : VG.Proof.Ed448.Arm.pt e2 0 21 2 = if sw₁ then VG.Proof.Ed448.Arm.pt e1 3 4 5 else VG.Proof.Ed448.Arm.pt e1 0 21 2 := by rw [← he2, VG.Proof.Ed448.Arm.pt_swap]
  have k2 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e2 i = e1 i := fun i hi => by
    rw [← he2, VG.Proof.Ed448.Arm.swapEnv_keep _ _ _ hi]
  generalize he3 : applyOps (VG.Proof.Ed448.Arm.addF 6 7) e2 = e3
  have p3 : VG.Proof.Ed448.Arm.pt e3 3 4 5 = VG.Proof.Ed448.Arm.addWith (e2 11) (VG.Proof.Ed448.Arm.pt e2 0 21 2) (VG.Proof.Ed448.Arm.pt e2 6 7 10) := by rw [← he3, VG.Proof.Ed448.Arm.addF_eval6]
  have q3 : VG.Proof.Ed448.Arm.pt e3 0 21 2 = VG.Proof.Ed448.Arm.pt e2 0 21 2 :=
    VG.Proof.Ed448.Arm.pt_congr' (by rw [← he3, VG.Proof.Ed448.Arm.addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
      (by rw [← he3, VG.Proof.Ed448.Arm.addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inr (Or.inr (by decide)))])
      (by rw [← he3, VG.Proof.Ed448.Arm.addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inl (by decide))])
  have e11 : e2 11 = e 11 := by rw [k2 11 (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  have b8 : VG.Proof.Ed448.Arm.pt e0 8 9 10 = VG.Proof.Ed448.Arm.pt e 8 9 10 :=
    VG.Proof.Ed448.Arm.pt_congr' (k0 8 (by decide)) (k0 9 (by decide)) (k0 10 (by decide))
  have a6 : VG.Proof.Ed448.Arm.pt e2 6 7 10 = VG.Proof.Ed448.Arm.pt e 6 7 10 :=
    VG.Proof.Ed448.Arm.pt_congr' (by rw [k2 6 (by decide), k1 6 (by decide), k0 6 (by decide)])
      (by rw [k2 7 (by decide), k1 7 (by decide), k0 7 (by decide)])
      (by rw [k2 10 (by decide), k1 10 (by decide), k0 10 (by decide)])
  rw [VG.Proof.Ed448.Arm.pt_swap, p3, q3, p2, p1, q1, e11, e11', b8, a6, p0]

theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    VG.Proof.Ed448.Arm.vstepEnv sw₁ sw₂ e i = e i := by
  rw [VG.Proof.Ed448.Arm.vstepEnv, VG.Proof.Ed448.Arm.swapEnv_keep _ _ _ hi, VG.Proof.Ed448.Arm.addF_keep _ 6 7 (Or.inl ⟨rfl, rfl⟩) _ (Or.inr (Or.inl hi)),
    VG.Proof.Ed448.Arm.swapEnv_keep _ _ _ hi, VG.Proof.Ed448.Arm.addF_keep _ 8 9 (Or.inr ⟨rfl, rfl⟩) _ (Or.inr (Or.inl hi)),
    VG.Proof.Ed448.Arm.doubleF_keep0 _ _ (Or.inl ⟨by omega, hi.2⟩)]

/-- One bit of both scalars: the reference ladder's point after the bits above
`t`, then after bit `t`. -/
theorem vladder_step {e : Env} {S K t : Nat} {A : Spec.Ed448.Point} (ht : t < 456)
    (hr : VG.Proof.Ed448.Arm.pt e 0 21 2 = vladder S K A (456 - (t + 1)))
    (hq : VG.Proof.Ed448.Arm.pt e 8 9 10 = Spec.Ed448.basePoint) (ha : VG.Proof.Ed448.Arm.pt e 6 7 10 = A) (hd : e 11 = Spec.Ed448.d) :
    VG.Proof.Ed448.Arm.pt (VG.Proof.Ed448.Arm.vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 21 2 =
      vladder S K A (456 - t) := by
  rw [VG.Proof.Ed448.Arm.vstepEnv_pt, hd, hq, ha, hr, vladder_bit S K A ht]
  rfl

/-! ## One iteration -/

theorem pair_mask : ∀ a < 2, ∀ b < 2,
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 &&& 1) = mask (decide (a = 1)) ∧
    (0 : BitVec 32) - ((BitVec.ofNat 8 (a + 2 * b)).setWidth 32 >>> 1) = mask (decide (b = 1)) := by
  decide

theorem vmask_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .r11 = BitVec.ofNat 32 t) {a b : Nat} (ha : a < 2) (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi)) s fun u =>
      u.gpr .r5 = mask (decide ((if hi then b else a) = 1)) ∧ Keeps workRegs s u ∧ u.mem = s.mem := by
  have hB : BITS = 3072 := rfl
  unfold vmask
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun u1 v1 => ?_
  have ba : State.addr (u1.gpr .r7 + BitVec.ofNat 32 BITS) = off base (BITS + t) := by
    rw [v1.gpr]; change State.addr (s.gpr .r0 + s.gpr .r11 + BitVec.ofNat 32 BITS) = _
    rw [hb, Offset.add_add, Nat.add_comm t BITS]
    exact hs.ea (by omega)
  refine VG.Proof.X25519.Arm.wp_ldrb (by omega) ba
    (by rw [v1.rd, v1.wr]; exact hs.read (by omega)) fun u2 v2 => ?_
  have e2 : u2.gpr .r3 = (BitVec.ofNat 8 (a + 2 * b)).setWidth 32 := by rw [v2.gpr, v1.mem, hbit]
  have pm := VG.Proof.Ed448.Arm.pair_mask a ha b hb2
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
      E u.mem base = VG.Proof.Ed448.Arm.swapEnv sw (E s.mem base) := by
  unfold vswap
  simp only [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (cswapE hs hbd 0 3 (by decide) hc) fun u1 ⟨k1, b1, c1, e1⟩ => ?_
  refine VG.Proof.X25519.Arm.WP.append (cswapE (k1.scr hs) b1 21 4 (by decide) (c1.trans hc))
    fun u2 ⟨k2, b2, c2, e2⟩ => ?_
  refine WP.mono (cswapE (k2.scr (k1.scr hs)) b2 2 5 (by decide) (c2.trans (c1.trans hc)))
    fun u3 ⟨k3, b3, _, e3⟩ => ⟨k1.trans (k2.trans k3), b3, by rw [e3, e2, e1]; rfl⟩

theorem vmaskSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hbd : BoundedEnv s.mem base) {t : Nat}
    (ht : t < 456) (hb : s.gpr .r11 = BitVec.ofNat 32 t) {a b : Nat} (ha : a < 2) (hb2 : b < 2)
    (hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 (a + 2 * b)) (hi : Bool) :
    WP isa (.block (vmask hi ++ vswap)) s fun u => Keep base s u ∧ BoundedEnv u.mem base ∧
      E u.mem base = VG.Proof.Ed448.Arm.swapEnv (decide ((if hi then b else a) = 1)) (E s.mem base) :=
  VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.vmask_ok hs ht hb ha hb2 hbit hi) fun u ⟨c, k, m⟩ =>
    WP.mono (VG.Proof.Ed448.Arm.vswap_ok (hs.of_keeps k (by decide)) (m ▸ hbd) c) fun v ⟨kv, bv, ev⟩ =>
      ⟨Keep.trans ⟨k, by rw [m]; exact Outside2.refl _ _ _ _ _ _⟩ kv, bv, by rw [ev, m]⟩

/-- The loop's invariant, after the bits above `n` of `S` and `k`, with `-A` the point `A`. -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  bounded : BoundedEnv s.mem base
  regs : Keeps (.r11 :: workRegs) s₀ s
  r11 : s.gpr .r11 = BitVec.ofNat 32 n
  mem : Outside2 base 64 2816 ACC 512 s₀.mem s.mem
  rep : VG.Proof.Ed448.Arm.pt (E s.mem base) 0 21 2 = vladder S K A (456 - n)
  q : VG.Proof.Ed448.Arm.pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : VG.Proof.Ed448.Arm.pt (E s.mem base) 6 7 10 = A
  d : E s.mem base 11 = Spec.Ed448.d

theorem vstep_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point} {n : Nat} (hn : n < 456)
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 S K t))
    (hi : VG.Proof.Ed448.Arm.VInv base S K A s₀ s (n + 1)) :
    WP isa vstep s fun t => VG.Proof.Ed448.Arm.VInv base S K A s₀ t n ∧ t.z = decide (n = 0) := by
  have hs := hi.scr
  have hB : BITS = 3072 := rfl
  have hA : ACC = 3584 := rfl
  have ha2 : (S >>> n) &&& 1 < 2 := bit_lt S n
  have hb2 : (K >>> n) &&& 1 < 2 := bit_lt K n
  have bitval : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [hi.mem _ (by rw [ofs_off' base (by omega)]; omega) (by rw [ofs_off' base (by omega)]; omega)]
    exact hbits n hn
  unfold vstep
  refine WP.seq (WP.mono (decR11_ok hi.r11) fun s₁ ⟨b₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have K₁ : Keeps [.r11] s s₁ := ⟨fun r hr => g₁ r (fun h => hr (by simp [h])), rd₁, wr₁⟩
  have hs₁ := hs.of_keeps K₁ (by decide)
  rw [show VG.Impl.Ed448.Arm.doubleAt 0 21 2 = (VG.Proof.Ed448.Arm.doubleF 0 21 2).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs₁ (m₁ ▸ hi.bounded) (VG.Proof.Ed448.Arm.doubleF 0 21 2)) fun s₂ ⟨k₂, bb₂, e₂⟩ => ?_)
  rw [show VG.Impl.Ed448.Arm.addAt 8 9 = (VG.Proof.Ed448.Arm.addF 8 9).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok (k₂.scr hs₁) bb₂ (VG.Proof.Ed448.Arm.addF 8 9)) fun s₃ ⟨k₃, bb₃, e₃⟩ => ?_)
  have hs₃ := k₃.scr (k₂.scr hs₁)
  have b₃ : s₃.gpr .r11 = BitVec.ofNat 32 n := by
    rw [k₃.regs.1 _ (by decide), k₂.regs.1 _ (by decide), b₁]
  have bit₃ : s₃.mem (off base (BITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [(k₂.trans k₃).mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.vmaskSwap_ok hs₃ bb₃ hn b₃ ha2 hb2 bit₃ false) fun s₄ ⟨k₄, bb₄, e₄⟩ => ?_)
  have hs₄ := k₄.scr hs₃
  rw [show VG.Impl.Ed448.Arm.addAt 6 7 = (VG.Proof.Ed448.Arm.addF 6 7).map FieldOp.impl from rfl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs₄ bb₄ (VG.Proof.Ed448.Arm.addF 6 7)) fun s₅ ⟨k₅, bb₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr hs₄
  have core4 := k₂.trans (k₃.trans (k₄.trans k₅))
  have b₅ : s₅.gpr .r11 = BitVec.ofNat 32 n := by rw [core4.regs.1 _ (by decide), b₁]
  have bit₅ : s₅.mem (off base (BITS + n)) = BitVec.ofNat 8 (((S >>> n) &&& 1) + 2 * ((K >>> n) &&& 1)) := by
    rw [core4.mem _ (by rw [ofs_off' base (by omega)]; omega)
      (by rw [ofs_off' base (by omega)]; omega), m₁, bitval]
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.vmaskSwap_ok hs₅ bb₅ hn b₅ ha2 hb2 bit₅ true)
    fun s₆ ⟨k₆, bb₆, e₆⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_cmp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t vt hz =>
    WP.block_nil ?_
  have core := core4.trans k₆
  have b₆ : s₆.gpr .r11 = BitVec.ofNat 32 n := by rw [core.regs.1 _ (by decide), b₁]
  have ee : E t.mem base = VG.Proof.Ed448.Arm.vstepEnv (decide ((S >>> n) &&& 1 = 1)) (decide ((K >>> n) &&& 1 = 1))
      (E s.mem base) := by
    rw [vt.mem, e₆, e₅, e₄, e₃, e₂, m₁]; rfl
  have kk : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → E t.mem base i = E s.mem base i := fun i h => by
    rw [ee, VG.Proof.Ed448.Arm.vstepEnv_keep _ _ _ _ h]
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
  · rw [ee]; exact VG.Proof.Ed448.Arm.vladder_step hn hi.rep hi.q hi.na hi.d
  · rw [VG.Proof.Ed448.Arm.pt_congr' (kk 8 (by decide)) (kk 9 (by decide)) (kk 10 (by decide))]; exact hi.q
  · rw [VG.Proof.Ed448.Arm.pt_congr' (kk 6 (by decide)) (kk 7 (by decide)) (kk 10 (by decide))]; exact hi.na
  · rw [kk 11 (by decide)]; exact hi.d
  · rw [hz, b₆]
    change (BitVec.ofNat 32 n - BitVec.ofNat 32 0 == 0) = _
    rw [BitVec.sub_zero]
    exact VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)

theorem vloop_ok {s₀ s : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 S K t))
    (hi : ∀ s', s'.gpr .r11 = BitVec.ofNat 32 456 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → VG.Proof.Ed448.Arm.VInv base S K A s₀ s' 456) :
    WP isa vloop s fun s' => VG.Proof.Ed448.Arm.VInv base S K A s₀ s' 0 := by
  unfold vloop
  refine WP.seq (WP.mono (setCounter_ok s 456 (by decide)) fun s' ⟨h1, h2, h3, h4, h5⟩ => ?_)
  refine WP.loop (M := isa) (body := vstep) (c := .ne) (Q := fun s' => VG.Proof.Ed448.Arm.VInv base S K A s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VG.Proof.Ed448.Arm.VInv base S K A s₀ s m) ?_ 456 s'
    ⟨by decide, by decide, hi s' h1 h2 h3 h4 h5⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (VG.Proof.Ed448.Arm.vstep_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyMain`. -/
section

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
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (by have := hf i (List.mem_range.mp hi); omega))

theorem far_bytes' {base p : Addr} {n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) : ∀ i < n,
      m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  fun i hi => h _ (Or.inr (by have := hf i hi; omega))

theorem outA {base : Addr} {o n : Nat} {m m' : Mem} (h : VG.Proof.X448.Arm.Outside base o n m m') (h1 : ACC ≤ o)
    (h2 : o + n ≤ ACC + 512) : Outside2 base 64 2816 ACC 512 m m' := fun p _ hq => h p (by omega)

/-! ## The entry and the start -/

theorem ventry_eq : ventry = setupHead ++ ([.mov .r8 (.reg .r12), .mov .r10 (.reg .r1)] : List Instr) := rfl

theorem ventry_ok {s : State} {base : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ t.gpr .r8 = s.gpr .r0 ∧ t.gpr .r10 = s.gpr .r1 ∧ t.gpr .r2 = s.gpr .r2 ∧
      VG.Proof.X448.Arm.Saved base s.gpr t.mem ∧ VG.Proof.X448.Arm.Outside base 0 32 s.mem t.mem ∧
      Keeps [.r12, .r0, .r6, .r8, .r10] s t := by
  rw [VG.Proof.Ed448.Arm.ventry_eq]
  refine VG.Proof.X25519.Arm.WP.append (setupHead_ok hc hw hn) fun v ⟨hsv, rv, svv, ov, kv⟩ => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun u hu => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_reg _ _) fun t ht => WP.block_nil ?_
  have k : Keeps [.r8, .r10] v t := rest_keeps ((hu.rest (by decide)).trans (ht.rest (by decide)))
  refine ⟨hsv.of_keeps k (by decide), ?_, ?_, ?_, by rw [ht.mem, hu.mem]; exact svv,
    by rw [ht.mem, hu.mem]; exact ov, (kv.mono (by decide)).trans (k.mono (by decide))⟩
  · rw [ht.other _ (by decide), hu.gpr, rv]
  · rw [ht.gpr, hu.other _ (by decide), kv.1 _ (by decide)]
  · rw [ht.other _ (by decide), hu.other _ (by decide), kv.1 _ (by decide)]

theorem vstart_eq : vstart = .mov .r12 (.imm 0) :: (sCheck ++ (initSlots ++
    copy (slot (21 : Index).val) (slot (1 : Index).val))) := by
  simp only [vstart, List.append_assoc]; rfl

/-- `BAD = 0`, the check of `S` (at `sq`), and the slots initialized: `Q` the
neutral point, `B`, `1` in slot 10 and `d`. -/
theorem vstart_ok {s : State} {base sq : Addr} (hs : Scr s base)
    (hq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = sq) (hfit : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (sq + BitVec.ofNat 64 j) 1)
    (hd : ∀ j < 57, 8192 ≤ ofs base (sq + BitVec.ofNat 64 j)) :
    WP isa (.block vstart) s fun t =>
      VG.Proof.Ed448.Arm.CKeep base s t ∧ BoundedEnv t.mem base ∧
      VG.Proof.Ed448.Arm.BadUpd (decodeLE (bytesAt s.mem sq 57) < Spec.Ed448.L) 0 (t.gpr .r12) ∧
      VG.Proof.Ed448.Arm.pt (E t.mem base) 0 21 2 = Spec.Ed448.identity ∧ VG.Proof.Ed448.Arm.pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 10 = 1 ∧ E t.mem base 11 = Spec.Ed448.d := by
  rw [VG.Proof.Ed448.Arm.vstart_eq]
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u hu => ?_
  have hsu := hs.of_upd hu (by decide) (by decide)
  refine VG.Proof.X25519.Arm.WP.append (VG.Proof.Ed448.Arm.sCheck_ok hsu (by rw [hu.other _ (by decide)]; exact hq)
    (by rw [hu.other _ (by decide)]; exact hfit) (by rw [hu.rd, hu.wr]; exact hr) hd)
    fun v ⟨bv, ov, kv⟩ => ?_
  have hsv := hsu.of_keeps kv (by decide)
  refine VG.Proof.X25519.Arm.WP.append (initSlots_ok hsv) fun w ⟨lw, ow, kw⟩ => ?_
  have hsw := hsv.of_keeps kw (by decide)
  refine WP.mono (copyE hsw (initSlots_bounded lw) 21 1) fun t ⟨kt, bt, et⟩ => ?_
  have ev : ∀ i : Index, i ≠ 21 → E t.mem base i = Proof.X448.toFe (initVal i.val) := fun i hi => by
    rw [et, opCopy, Function.update_of_ne hi, initSlots_E lw i]
  have e21 : E t.mem base 21 = Proof.X448.toFe (initVal 1) := by
    rw [et, opCopy, Function.update_self, initSlots_E lw 1]; rfl
  refine ⟨⟨?_, ?_⟩, bt, ?_, ?_, ?_, ?_, ?_⟩
  · refine (rest_keeps (hu.rest (ws := .r12 :: .r11 :: workRegs) (by decide))).trans
      ((kv.mono ?_).trans ((kw.mono ?_).trans (kt.regs.mono ?_))) <;> decide
  · rw [← hu.mem]
    exact ((VG.Proof.Ed448.Arm.outA ov (by decide) (by decide)).trans (VG.Proof.Ed448.Arm.outC ow (by decide) (by decide))).trans kt.mem
  · rw [hu.gpr] at bv
    rw [kt.regs.1 .r12 (by decide), kw.1 .r12 (by decide), ← hu.mem]
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

theorem BadUpd.zero {P : Prop} {b : BitVec 32} (h : VG.Proof.Ed448.Arm.BadUpd P 0 b) : (b = 0 ↔ P) ∧ b.toNat < 65536 := by
  obtain ⟨c, hc, hp, rfl⟩ := h
  have e : (0 : BitVec 32) ||| c = c := BitVec.zero_or
  rw [e]
  exact ⟨hp, hc⟩

theorem bits_kept {base : Addr} {m m' : Mem} (h : Outside2 base 32 2848 ACC 512 m m') :
    ∀ t < 456, m' (off base (BITS + t)) = m (off base (BITS + t)) := fun t ht =>
  h _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)
    (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, ACC]; omega)

theorem verifyEquation_main (hR : RecoverOk) (hE : VerifyEqOk) {s : State} (h : VG.Proof.Ed448.Arm.VerifyPre s) :
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
    ⟨⟨pk, 57⟩, by rw [h.rd, hpk]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have rsg : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have rS : ∀ j < 57, InRegions (s.rd ++ s.wr) (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨⟨sig, 114⟩, by rw [h.rd, hsig]; simp,
      by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have rch : ∀ j < 57, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 j) 1 := fun j hj =>
    ⟨⟨ch, 57⟩, by rw [h.rd, hch]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have fpk : ∀ j < 57, 8192 ≤ ofs base (pk + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hpk ▸ hbase ▸ h.pk_ws) hj (by decide)
  have fsg : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega) (by decide)
  have fS : ∀ j < 57, 8192 ≤ ofs base (sig + BitVec.ofNat 64 57 + BitVec.ofNat 64 j) := fun j hj => by
    rw [Offset.add_add]; exact far_ws (hsig ▸ hbase ▸ h.sig_ws) (by omega) (by decide)
  have fch : ∀ j < 57, 8192 ≤ ofs base (ch + BitVec.ofNat 64 j) := fun j hj =>
    far_ws (hch ▸ hbase ▸ h.ch_ws) hj (by decide)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 57) 57) = S := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, decodeLE (bytesAt s.mem ch 57) = K := ⟨_, rfl⟩
  unfold verifyEquation
  -- The entry.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.ventry_ok hbase hw₀ h.f3) fun s1 ⟨hs1, r81, r101, r21, sv1, o1, k1⟩ => ?_)
  have rr1 : s1.rd ++ s1.wr = s.rd ++ s.wr := by rw [k1.2.1, k1.2.2]
  have O1 : VG.Proof.X448.Arm.Outside base 0 8192 s.mem s1.mem := o1.mono (by decide) (by decide)
  -- The bits of `S` and `k`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.vbits_ok hs1 (sq := sig + BitVec.ofNat 64 57) (kq := ch)
    (by rw [r101, hsig]) (by rw [r21, hch]) (by rw [r101]; exact h.f1) (by rw [r21]; exact h.f2)
    (by rw [rr1]; exact rS) (by rw [rr1]; exact rch) fS fch) fun s2 ⟨g2, rd2, wr2, o2, bits2⟩ => ?_)
  rw [VG.Proof.Ed448.Arm.far_bytes O1 fS, hS, VG.Proof.Ed448.Arm.far_bytes O1 fch, hK] at bits2
  have hs2 : Scr s2 base := hs1.of_keeps ⟨g2, rd2, wr2⟩ (by decide)
  have rr2 : s2.rd ++ s2.wr = s.rd ++ s.wr := by rw [rd2, wr2, rr1]
  have O2 : VG.Proof.X448.Arm.Outside base 0 8192 s.mem s2.mem := O1.trans (o2.mono (by decide) (by decide))
  have r102 : s2.gpr .r10 = s.gpr .r1 := by rw [g2 _ (by decide), r101]
  have r82 : s2.gpr .r8 = s.gpr .r0 := by rw [g2 _ (by decide), r81]
  -- `BAD = 0`, the check of `S`, and the slots.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.vstart_ok hs2 (sq := sig + BitVec.ofNat 64 57) (by rw [r102, hsig])
    (by rw [r102]; exact h.f1) (by rw [rr2]; exact rS) fS) fun s3 ⟨k3, b3, c3, q3, p3, h103, h113⟩ => ?_)
  rw [VG.Proof.Ed448.Arm.far_bytes O2 fS, hS] at c3
  have hs3 := k3.scr hs2
  have rr3 : s3.rd ++ s3.wr = s.rd ++ s.wr := by rw [k3.regs.2.1, k3.regs.2.2, rr2]
  have O3 : VG.Proof.X448.Arm.Outside base 0 8192 s.mem s3.mem := O2.trans (k3.mem.whole (by decide) (by decide))
  have r83 : s3.gpr .r8 = s.gpr .r0 := by rw [k3.regs.1 _ (by decide), r82]
  have r103 : s3.gpr .r10 = s.gpr .r1 := by rw [k3.regs.1 _ (by decide), r102]
  -- `A`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.decode_ok hR hs3 b3 (p := .r8) (Or.inl rfl) (by rw [r83, hpk])
    (by rw [r83]; exact h.f0) (by rw [rr3]; exact rpk) fpk 6 7 (Or.inl ⟨rfl, rfl⟩) h103 h113)
    fun s4 ⟨k4, b4, c4, v4, e4⟩ => ?_)
  rw [VG.Proof.Ed448.Arm.far_bytes O3 fpk] at c4 v4
  have hs4 := k4.scr hs3
  have O4 : VG.Proof.X448.Arm.Outside base 0 8192 s.mem s4.mem := O3.trans (k4.mem.whole (by decide) (by decide))
  -- `-A`.
  rw [show ([.sub (slot 6) (slot 0) (slot 6)] : List Op) = ([.sub 6 0 6] : List FieldOp).map FieldOp.impl
    from rfl]
  refine WP.seq (WP.mono (VG.Proof.X448.Arm.ops_ok hs4 b4 [.sub 6 0 6]) fun s5 ⟨k5, b5, e5⟩ => ?_)
  have hs5 := k5.scr hs4
  have O5 : VG.Proof.X448.Arm.Outside base 0 8192 s.mem s5.mem := O4.trans (k5.mem.whole (by decide) (by decide))
  have k5' : ∀ i : Index, i ≠ 6 → E s5.mem base i = E s4.mem base i := fun i hi => by
    rw [e5]; exact Function.update_of_ne hi _ _
  have k43 : ∀ i : Index, i.val = 0 ∨ i.val = 2 ∨ (8 ≤ i.val ∧ i.val ≤ 11) ∨ i.val = 21 →
      E s5.mem base i = E s3.mem base i := fun i hi => by
    rw [k5' i (fun h => by subst h; omega), e4 i (fun h => by subst h; omega) (fun h => by subst h; omega)
      (by omega)]
  -- The loop.
  have bits5 : ∀ t < 456, s5.mem (off base (BITS + t)) = BitVec.ofNat 8 (VG.Proof.Ed448.Arm.pair2 S K t) := fun t ht => by
    rw [VG.Proof.Ed448.Arm.bits_kept (Outside2.widen k5.mem) t ht, VG.Proof.Ed448.Arm.bits_kept k4.mem t ht, VG.Proof.Ed448.Arm.bits_kept (Outside2.widen k3.mem) t ht]
    exact bits2 t ht
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.vloop_ok (s₀ := s5) (A := VG.Proof.Ed448.Arm.pt (E s5.mem base) 6 7 10) bits5
    (fun s' h1 h2 h3 h4 h5 => ?_)) fun s6 I6 => ?_)
  · have k' : Keeps (.r11 :: workRegs) s5 s' :=
      ⟨fun r hr => h2 r (fun e => hr (by subst r; exact List.mem_cons_self)), h4, h5⟩
    refine ⟨hs5.of_keeps k' (by decide), h3 ▸ b5, k', h1, h3 ▸ Outside2.refl _ _ _ _ _ _, ?_, ?_, ?_, ?_⟩
    · rw [h3, Nat.sub_self, VG.Proof.Ed448.Arm.pt_congr' (k43 0 (by decide)) (k43 21 (by decide)) (k43 2 (by decide)), q3]
      rfl
    · rw [h3, VG.Proof.Ed448.Arm.pt_congr' (k43 8 (by decide)) (k43 9 (by decide)) (k43 10 (by decide)), p3]
    · rw [h3]
    · rw [h3, k43 11 (by decide), h113]
  -- `R`.
  have hs6 := I6.scr
  have O6 : VG.Proof.X448.Arm.Outside base 0 8192 s.mem s6.mem := O5.trans (I6.mem.whole (by decide) (by decide))
  have r106 : s6.gpr .r10 = s.gpr .r1 := by
    rw [I6.regs.1 _ (by decide), k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), r103]
  have h106 : E s6.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z I6.q
  have rr6 : s6.rd ++ s6.wr = s.rd ++ s.wr := by
    rw [I6.regs.2.1, I6.regs.2.2, k5.regs.2.1, k5.regs.2.2, k4.regs.2.1, k4.regs.2.2, rr3]
  have f6 : (s6.gpr .r10).toNat + 57 ≤ 2 ^ 32 := by rw [r106]; have := h.f1; omega
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.decode_ok hR hs6 I6.bounded (p := .r10) (Or.inr rfl) (by rw [r106, hsig])
    f6 (by rw [rr6]; exact rsg) fsg 8 9 (Or.inr ⟨rfl, rfl⟩) h106 I6.d)
    fun s7 ⟨k7, b7, c7, v7, e7⟩ => ?_)
  rw [VG.Proof.Ed448.Arm.far_bytes O6 fsg] at c7 v7
  have hs7 := k7.scr hs6
  -- `BAD`.
  have c7' : VG.Proof.Ed448.Arm.BadUpd ((Spec.Ed448.decodePoint (bytesAt s.mem sig 57)).isSome = true) (s4.gpr .r12)
      (s7.gpr .r12) := by
    rw [← k5.regs.1 .r12 (by decide), ← I6.regs.1 .r12 (by decide)]; exact c7
  have c6 := (c3.trans c4).trans c7'
  -- The comparison.
  have sv7 : VG.Proof.X448.Arm.Saved base s.gpr s7.mem :=
    (((((sv1.outside o2 (by decide)).outside2 k3.mem (by decide) (by decide)).outside2 k4.mem (by decide)
      (by decide)).outside2 k5.mem (by decide) (by decide)).outside2 I6.mem (by decide) (by decide)).outside2
      k7.mem (by decide) (by decide)
  have z7 := c6.zero
  refine WP.mono (VG.Proof.Ed448.Arm.vfinish_ok hs7 b7 sv7 z7.2) fun t ⟨rt, st, gt⟩ => ⟨fun r hr => ?_, ?_⟩
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
    · rw [gt _ (by decide), k7.regs.1 _ (by decide), I6.regs.1 _ (by decide), k5.regs.1 _ (by decide),
        k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), g2 _ (by decide), k1.1 _ (by decide)]
  · rw [rt, hpk, hsig, hch]
    refine if_congr ?_ rfl rfl
    rw [z7.1]
    cases ha : Spec.Ed448.decodePoint (bytesAt s.mem pk 57) with
    | none =>
      rw [verifyEquation_none (Or.inl ha)]
      exact ⟨fun h => absurd h.1.1.2 (by simp), fun h => absurd h (by decide)⟩
    | some a =>
      cases hr : Spec.Ed448.decodePoint ((bytesAt s.mem sig 114).take 57) with
      | none =>
        rw [verifyEquation_none (Or.inr hr)]
        rw [VG.Proof.Ed448.Arm.bytesAt_take57] at hr
        exact ⟨fun h => absurd h.1.2 (by rw [hr]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have hr' := hr
        rw [VG.Proof.Ed448.Arm.bytesAt_take57] at hr'
        obtain ⟨ax, ay, az⟩ := v4 a ha
        obtain ⟨rx, ry, rz⟩ := v7 r hr'
        have e40 : E s4.mem base 0 = 0 := by
          rw [e4 0 (by decide) (by decide) (Or.inl rfl)]; exact congrArg Spec.Ed448.Point.X q3
        have e410 : E s4.mem base 10 = 1 := by
          rw [e4 10 (by decide) (by decide) (by decide)]; exact h103
        have hA : VG.Proof.Ed448.Arm.pt (E s5.mem base) 6 7 10 = negPoint a := by
          show (⟨E s5.mem base 6, E s5.mem base 7, E s5.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
          rw [show E s5.mem base 6 = E s4.mem base 0 - E s4.mem base 6 by rw [e5]; rfl,
            k5' 7 (by decide), k5' 10 (by decide), e40, ax, ay, e410, az]
        have hQ : VG.Proof.Ed448.Arm.pt (E s7.mem base) 0 21 2 = vladder S K (negPoint a) 456 := by
          rw [VG.Proof.Ed448.Arm.pt_congr' (e7 0 (by decide) (by decide) (Or.inl rfl)) (e7 21 (by decide) (by decide)
            (Or.inr (Or.inr (Or.inr rfl)))) (e7 2 (by decide) (by decide) (Or.inr (Or.inl rfl))), I6.rep,
            hA]
        have hRR : VG.Proof.Ed448.Arm.pt (E s7.mem base) 8 9 10 = r := by
          show (⟨E s7.mem base 8, E s7.mem base 9, E s7.mem base 10⟩ : Spec.Ed448.Point) = r
          rw [rx, ry, e7 10 (by decide) (by decide) (by decide), h106, ← rz]
        rw [hE _ _ _ _ _ (VG.Proof.Ed448.Arm.bytesAt57_len _ _) (VG.Proof.Ed448.Arm.bytesAt114_len _ _) (VG.Proof.Ed448.Arm.bytesAt57_len _ _) ha hr, hQ, hRR,
          VG.Proof.Ed448.Arm.bytesAt_drop57, hS, hK, hr']
        simp only [Option.isSome_some, and_true, Bool.and_eq_true, decide_eq_true_eq]

end VG.Proof.Ed448.Arm

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified`. -/
section

/-!
# Ed448 verification's equation on ARMv7: `Verified`

Correctness including the ABI, given the reference computations' agreement
with the specification (`RecoverOk`, `VerifyEqOk`, which the registration
file passes in, from `Proof/Ed448/Facts.lean`), constant time (by taint
tracking: the only branches are on the loop counters, and every address is
an argument plus a constant or a counter), and a concrete state satisfying
the signature's contract. The contract lets timing depend on the inputs; the
code's depends on the pointers alone.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm
open VG.Proof.Ed448 (RecoverOk VerifyEqOk)

theorem VerifyPre.of {s : State} (h : verifyEquationLocal.pre s) : VG.Proof.Ed448.Arm.VerifyPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2⟩

def verifyEquationSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 114⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verifyEquation_ok (hR : RecoverOk) (hE : VerifyEqOk) (s : State) (hs : verifyEquationLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Ed448.Arm.verifyEquation_main hR hE (VerifyPre.of hs)
  exact ⟨t, s', he, ⟨h.1, Exec.sp he⟩, h.2⟩

theorem verifyEquation_ct :
    ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub verifyEquation := by
  refine Taint.constantTime_eraseOff_of_eq (Taint.ofRegs [.r0, .r1, .r2, .r3]) (Taint.noBase_ofRegs _) ?_
    (c' := VG.Proof.Ed448.Arm.verifyEquationErased) rfl (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1, h2, h3, _⟩
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [h0, h1, h2, h3]

theorem verifyEquation_implies :
    verifyEquationLocal.Implies (Spec.Ed448.verifyEquationContract Arm.abi) where
  pre := by
    sig_implies_pre [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.verifyEquationLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  post := by
    intro s t _ h
    sig_post [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    exact (e _ _).trans h
  pub := by
    sig_implies_pub [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.verifyEquationLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
  sat := by
    sig_implies_sat [Spec.Ed448.verifyEquationContract, Spec.Ed448.verifyEquationSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.verifyEquationLocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [verifyEquationSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Ed448.Arm.verifyEquationSat

theorem verifyEquation_verified (hR : RecoverOk) (hE : VerifyEqOk) :
    Verified Arm.target verifyEquation (Spec.Ed448.verifyEquationContract Arm.abi) :=
  Verified.of_correct (VG.Proof.Ed448.Arm.verifyEquation_ok hR hE) VG.Proof.Ed448.Arm.verifyEquation_ct VG.Proof.Ed448.Arm.verifyEquation_implies

end VG.Proof.Ed448.Arm

end
