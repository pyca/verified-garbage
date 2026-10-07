import VerifiedGarbage.Proof.Ed448.Arm.BaseBits
import VerifiedGarbage.Impl.Ed448.Arm.VerifyEquation

/-!
# Ed448 verification's equation on ARMv7: the bits of `S` and `k`

`vbits_ok`: byte `t` at `VBITS` is bit `t` of `S` (the signature's last 57
bytes) plus twice bit `t` of `k` (the challenge), for `t < 456`.
-/

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
    exact VG.Proof.X25519.Arm.op2_lsr (by omega)

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
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
  change ((a.toNat >>> j &&& 1) + ((b.toNat >>> j &&& 1) * 2 ^ 1) % 2 ^ 32) % 2 ^ 32 % 2 ^ 8 = _
  omega

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
    rw [r7, hp, BitVec.add_assoc, ← BitVec.ofNat_add, hs.ea (by simp only [VBITS]; omega)]
    congr 1; omega
  refine wp_strb (by simp only [VBITS]; omega) ea
    (by rw [v5.wr, v4.wr, v3.wr, v2.wr, v1.wr]; exact hs.write (by simp only [VBITS]; omega))
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
        rw [off_eq_iff base (by simp only [VBITS]; omega) (by simp only [VBITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [VBITS]; omega) (by omega)
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
    WP isa (.block vbitHead) s fun t =>
      t.gpr .r3 = (s.mem (sq + BitVec.ofNat 64 i)).setWidth 32 ∧
      t.gpr .r9 = (s.mem (kq + BitVec.ofNat 64 i)).setWidth 32 ∧
      t.gpr .r7 = t.gpr .r0 + BitVec.ofNat 32 (8 * i) ∧
      t.mem = s.mem ∧ Keeps [.r3, .r9, .r7] s t := by
  unfold vbitHead
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
  esq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = sq
  ekq : State.addr (s.gpr .r2) = kq
  fs : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32
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
    hb.mem _ (by have := hsd i hi; simp only [VBITS]; omega)
  have hbk : s.mem (kq + BitVec.ofNat 64 i) = s₀.mem (kq + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [VBITS]; omega)
  have inv : VBitsInv base sq kq s₀ s' (i + 1) := by
    refine ⟨hb.scr.of_keeps ⟨g', rd', wr'⟩ (by decide),
      (by rw [g' _ (by decide)]; exact hb.esq), (by rw [g' _ (by decide)]; exact hb.ekq),
      (by rw [g' _ (by decide)]; exact hb.fs), (by rw [g' _ (by decide)]; exact hb.fk), b',
      fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · rw [o' _ (by rw [ofs_off' base (by simp only [VBITS]; omega)]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbs, hbk] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega
    exact .inl ⟨rfl, inv⟩

/-- `vbits`: byte `t` of `VBITS` is bit `t` of `S` plus twice bit `t` of `k`, for `t < 456`. -/
theorem vbits_ok {s : State} {base sq kq : Addr} (hs : Scr s base)
    (hsq : State.addr (s.gpr .r10) + BitVec.ofNat 64 57 = sq) (hkq : State.addr (s.gpr .r2) = kq)
    (hfs : (s.gpr .r10).toNat + 114 ≤ 2 ^ 32) (hfk : (s.gpr .r2).toNat + 57 ≤ 2 ^ 32)
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
    exact ⟨hs.of_keeps keep (by decide), by rw [ht.other .r10 (by decide)]; exact hsq,
      by rw [ht.other .r2 (by decide)]; exact hkq, by rw [ht.other .r10 (by decide)]; exact hfs,
      by rw [ht.other .r2 (by decide)]; exact hfk, ht.gpr, keep.1, keep.2.1, keep.2.2,
      ht.mem ▸ Outside.refl _ _ _ _, fun _ hi => by omega⟩) fun s₁ h₁ => ?_)
  refine WP.mono (vbitsLoop_ok hsr hkr hsd hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega)]
  unfold pair2
  rw [scalar_bit _ _ ht, scalar_bit _ _ ht]

end VG.Proof.Ed448.Arm
