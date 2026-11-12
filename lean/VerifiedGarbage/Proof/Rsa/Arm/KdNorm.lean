module
-- separate module: the proof of the division by words is split in a chain of modules (`KdNorm`, `KdTop`, `KdEst`, `KdStep`, `KdDiv`), so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Rsa.Arm.KdRun
public import VerifiedGarbage.Proof.Framework.Arm.Keep
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Bignum.Arm.WideMul
public import VerifiedGarbage.Proof.Bignum.NormMask32
import VerifiedGarbage.Proof.Bignum.WordStep32

/-! # The normalization of the key checks' divisor on ARMv7 (`KeyDiv.norm`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_dp op2_lsr op2_lsl op2_reg op2_imm dpVal)
open VG.Proof.Bignum.NormMask32

theorem top_val (B : BitVec 32) {X w i : Nat} (hi : i ≤ w / 2) (hw : w < 2 ^ 31) (hX : X + 4 * (w / 2) < 2 ^ 32) :
    B + BitVec.ofNat 32 X + (BitVec.ofNat 32 w >>> 1 - BitVec.ofNat 32 i) <<< 2 =
      B + BitVec.ofNat 32 (X + 4 * (w / 2 - i)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have e1 : (BitVec.ofNat 32 w >>> 1).toNat = w / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]; omega
  have e2 : (BitVec.ofNat 32 w >>> 1 - BitVec.ofNat 32 i).toNat = w / 2 - i := by
    rw [BitVec.toNat_sub, e1, BitVec.toNat_ofNat]; omega
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, e2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `topPtr r j i t`: `r` at word `w / 2 - i` of array `j`. -/
theorem topPtr_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) {r t : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) (ht : t ∉ [.r7, .r8, .r9]) (hrt : r ≠ t) {j i : Nat} (hj : j < 256)
    (hi : i ≤ w / 2) (hi2 : i < 256) (hfit : arr w j + 4 * (w / 2) + 4 ≤ Z) {rest : List Instr} {Q : State → Prop}
    (k : ∀ u, u.gpr r = B + BitVec.ofNat 32 (arr w j + 4 * (w / 2 - i)) → Rest [r, t] s u → u.mem = s.mem →
      Ws u B Z w N → WP isa (.block rest) u Q) :
    WP isa (.block (topPtr r j i t ++ rest)) s Q := by
  have := h.wle
  have nw := h.nowrap
  simp only [topPtr, List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h hr hj fun u1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun u2 U2 => ?_
  refine wp_dp (op2_imm (encodable_lt hi2)) fun u3 U3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun u4 U4 => k u4 ?_ ?_ ?_ ?_
  · have t9 : t ≠ .r9 := fun e => ht (by simp [e])
    rw [U4.gpr, dpVal, U3.other _ hrt, U2.other _ hrt, p1, U3.gpr, dpVal, U2.gpr, h1.r9]
    exact top_val B hi (by omega) (by have := h.arr_fit (j := j); omega)
  · exact (r1.mono (by simp)).trans ((U2.rest (by simp)).trans ((U3.rest (by simp)).trans (U4.rest (by simp))))
  · rw [U4.mem, U3.mem, U2.mem, m1]
  · have r7 : r ≠ .r7 := fun e => hr (by simp [e])
    have r8 : r ≠ .r8 := fun e => hr (by simp [e])
    have r9 : r ≠ .r9 := fun e => hr (by simp [e])
    have t7 : t ≠ .r7 := fun e => ht (by simp [e])
    have t8 : t ≠ .r8 := fun e => ht (by simp [e])
    have t9 : t ≠ .r9 := fun e => ht (by simp [e])
    exact ((h1.of_upd U2 t7 t8 t9).of_upd U3 t7 t8 t9).of_upd U4 r7 r8 r9

theorem normBit_ok {s : State} :
    WP isa (.block normBit) s fun t =>
      t.gpr .r1 = s.gpr .r1 + (s.gpr .r1 &&& clearMask (s.gpr .r1)) ∧
      t.gpr .r2 = s.gpr .r2 + (s.gpr .r2 &&& clearMask (s.gpr .r1)) ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧ t.mem = s.mem := by
  krun [normBit, clearMask]
  done

/-- The 31 doublings: from `r1 = T ≠ 0`, `r2 = 1` and `lr = 31`, `r1 = T 2^z`
and `r2 = 2^z` for `z = lz T`. -/
theorem normLoop_ok {s : State} {T : Nat} (hT : 0 < T) (hT' : T < 2 ^ 32) (h1 : s.gpr .r1 = BitVec.ofNat 32 T)
    (h2 : s.gpr .r2 = 1) (hl : s.gpr .lr = 31) :
    WP isa (.loop (.block normBit) .ne) s fun t =>
      t.gpr .r1 = BitVec.ofNat 32 (T * 2 ^ lz T) ∧ t.gpr .r2 = BitVec.ofNat 32 (2 ^ lz T) ∧ t.mem = s.mem ∧
      Rest [.r1, .r2, .r3, .r4, .lr] s t := by
  refine WP.loop (M := isa) (fun n t => ∃ j, n = 31 - j ∧ j < 31 ∧
      t.gpr .r1 = BitVec.ofNat 32 (T * 2 ^ min j (lz T)) ∧ t.gpr .r2 = BitVec.ofNat 32 (2 ^ min j (lz T)) ∧
      t.gpr .lr = BitVec.ofNat 32 (31 - j) ∧ t.mem = s.mem ∧ Rest [.r1, .r2, .r3, .r4, .lr] s t) ?_ _ s
    ⟨0, rfl, by decide, by rw [h1]; simp, by rw [h2]; simp, by rw [hl]; rfl, rfl,
      VG.Proof.X25519.Arm.Rest.refl _ _⟩
  rintro n t ⟨j, rfl, hj, h1', h2', hl', hm, k⟩
  refine WP.mono (WP.keep [.r1, .r2, .r3, .r4, .lr] normBit_ok (by decide))
    fun t' ⟨⟨e1, e2, el, ez, hm'⟩, k'⟩ => ?_
  obtain ⟨c1, c2⟩ := normStep_val hT hT' (i := min j (lz T)) (Nat.min_le_right _ _)
  have hmin : min (min j (lz T) + 1) (lz T) = min (j + 1) (lz T) := by omega
  rw [hmin] at c1 c2
  have hd : t'.gpr .lr = BitVec.ofNat 32 (31 - (j + 1)) := by
    rw [el, hl']; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; simp; omega
  have hz : (t.gpr .lr - 1 == 0) = (31 - (j + 1) == 0) := by
    rw [← el, hd]
    by_cases e : 31 - (j + 1) = 0
    · rw [e]; rfl
    · have : (BitVec.ofNat 32 (31 - (j + 1)) == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro e'
        have := congrArg BitVec.toNat e'; simp at this; omega
      rw [this]; simp only [Bool.false_eq, beq_eq_false_iff_ne, ne_eq]; omega
  have K := k.trans k'
  by_cases e : j + 1 = 31
  · refine .inl ⟨by simp only [eval, ez, hz, e]; rfl, ?_, ?_, hm'.trans hm, K⟩
    · rw [e1, h1', c1, Nat.min_eq_right (by unfold lz; omega)]
    · rw [e2, h2', h1', c2, Nat.min_eq_right (by unfold lz; omega)]
  · refine .inr ⟨by simp only [eval, ez, hz]; simp; omega, 31 - (j + 1), by omega, j + 1, rfl, by omega, ?_, ?_,
      hd, hm'.trans hm, K⟩
    · rw [e1, h1', c1]
    · rw [e2, h2', h1', c2]

theorem Preserves.toRest {rs : List Reg} {s t : State} (h : VG.Proof.Bignum.Arm.Preserves rs s t) :
    Rest rs s t := ⟨h.regs, h.rd, h.wr, h.sp⟩

/-- `wideMul` then `rest`. -/
theorem wp_wide {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, (t.gpr .r3).toNat + (t.gpr .r4).toNat * 2 ^ 32 = (s.gpr .r1).toNat * (s.gpr .r2).toNat →
      VG.Proof.Bignum.Arm.Preserves VG.Proof.Bignum.Arm.clobbers s t → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.Bignum.Arm.wideMul ++ rest)) s Q :=
  WP.block_append_iff.mpr (WP.mono (VG.Proof.Bignum.Arm.wideMul_ok s) fun t ⟨h1, h2⟩ => k t h1 h2)

/-- The low and high words of a product. -/
theorem wide_lo_hi {a b x y : Nat} (ha : a < 2 ^ 32) (h : a + b * 2 ^ 32 = x * y) :
    a = x * y % 2 ^ 32 ∧ b = x * y / 2 ^ 32 := by
  constructor <;> omega

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem add_ofNat_assoc (B : BitVec 32) (X k : Nat) :
    B + BitVec.ofNat 32 X + BitVec.ofNat 32 k = B + BitVec.ofNat 32 (X + k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem stride_val {w : Nat} (_hw : w ≤ 1024) :
    (BitVec.ofNat 32 w + 2) <<< 2 = BitVec.ofNat 32 (4 * (w + 2)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    show (2 : BitVec 32).toNat = 2 from rfl]
  omega

/-- The registers `norm` changes. -/
abbrev normRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr]

/-- `norm m`: `P = 2^z` (136), `d = T 2^z + ⌊U 2^z / 2^32⌋` (140) and `d₁ = U 2^z
mod 2^32 + ⌊V 2^z / 2^32⌋` (148), for `[m]`'s word `T ≠ 0` at `w / 2 - 1`
and the two below it, `U` and `V`. -/
theorem norm_ok {s : State} {B : BitVec 32} {Z w N m : Nat} (h : Ws s B Z w N) (hm : m < N) (hN : N ≤ 256)
    (hw6 : 6 ≤ w) {T U V : Nat} (hT : w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 1)) = T)
    (hU : w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 2)) = U)
    (hV : w32 s.mem (State.addr B) (arr w m + 4 * (w / 2 - 3)) = V) (hT0 : 0 < T) :
    WP isa (norm m) s fun t => slot t.mem B sP = 2 ^ lz T ∧
      slot t.mem B sD = T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32 ∧
      slot t.mem B sD1 = U * 2 ^ lz T % 2 ^ 32 + V * 2 ^ lz T / 2 ^ 32 ∧
      Keep B w [] [sP, sD, sD1] s.mem t.mem ∧ Ws t B Z w N ∧ Rest normRegs s t := by
  have := h.wle
  have nw := h.nowrap
  have fm := h.arr_fit hm
  have hz := h.hdr_le
  simp only [S] at fm
  have hT' : T < 2 ^ 32 := hT ▸ BitVec.isLt _
  have hU' : U < 2 ^ 32 := hU ▸ BitVec.isLt _
  have hV' : V < 2 ^ 32 := hV ▸ BitVec.isLt _
  rw [norm]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  rw [WP.seq_iff]
  -- The three words.
  refine topPtr_ok h (r := .r0) (t := .r1) (j := m) (i := 3) (by decide) (by decide) (by decide) (by omega)
    (by omega) (by decide) (by omega) fun u p0 ru mu hu => ?_
  generalize hX : arr w m + 4 * (w / 2 - 3) = X at p0
  have a0 : State.addr (B + BitVec.ofNat 32 X) = off (State.addr B) X := h.addr (by omega)
  have a4 : State.addr (B + BitVec.ofNat 32 X + BitVec.ofNat 32 4) = off (State.addr B) (X + 4) := by
    rw [add_ofNat_assoc]; exact h.addr (by omega)
  have a8 : State.addr (B + BitVec.ofNat 32 X + BitVec.ofNat 32 8) = off (State.addr B) (X + 8) := by
    rw [add_ofNat_assoc]; exact h.addr (by omega)
  have r0 : InRegions (u.rd ++ u.wr) (off (State.addr B) X) 4 := hu.read (by omega)
  have r4 : InRegions (u.rd ++ u.wr) (off (State.addr B) (X + 4)) 4 := hu.read (by omega)
  have r8 : InRegions (u.rd ++ u.wr) (off (State.addr B) (X + 8)) 4 := hu.read (by omega)
  have v0 : u.mem.readW (off (State.addr B) X) 32 = BitVec.ofNat 32 V := by
    rw [mu, ← hV, ← hX]; exact (ofNat_toNat32 _).symm
  have v4 : u.mem.readW (off (State.addr B) (X + 4)) 32 = BitVec.ofNat 32 U := by
    rw [mu, ← hU, show X + 4 = arr w m + 4 * (w / 2 - 2) by omega]; exact (ofNat_toNat32 _).symm
  have v8 : u.mem.readW (off (State.addr B) (X + 8)) 32 = BitVec.ofNat 32 T := by
    rw [mu, ← hT, show X + 8 = arr w m + 4 * (w / 2 - 1) by omega]; exact (ofNat_toNat32 _).symm
  refine WP.mono (WP.keep [.r1, .r2, .r10, .r11, .lr] (Q := fun v => v.gpr .r11 = BitVec.ofNat 32 V ∧
      v.gpr .r10 = BitVec.ofNat 32 U ∧ v.gpr .r1 = BitVec.ofNat 32 T ∧ v.gpr .r2 = 1 ∧ v.gpr .lr = 31 ∧
      v.mem = u.mem) (by
    krun [p0, a0, a4, a8, r0, r4, r8, v0, v4, v8]) (by decide)) fun v ⟨⟨v11, v10, v1, v2, vl, vm⟩, kv⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (normLoop_ok hT0 hT' v1 v2 vl) fun t ⟨t1, t2, tm, kt⟩ => ?_
  -- `P`, `d` and `d₁`.
  have ht : Ws t B Z w N := (hu.rest kv).rest kt
  have k3 : Rest normRegs s t := ((ru.mono (by decide)).trans (kv.mono (by decide))).trans (kt.mono (by decide))
  have t10 : t.gpr .r10 = BitVec.ofNat 32 U := by rw [kt.gpr _ (by decide), v10]
  have t11 : t.gpr .r11 = BitVec.ofNat 32 V := by rw [kt.gpr _ (by decide), v11]
  have aP := h.addr (d := sP) (by simp only [sP, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have wP : InRegions t.wr (off (State.addr B) sP) 4 := ht.write (by simp only [sP, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have aD := h.addr (d := sD) (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have wD : InRegions t.wr (off (State.addr B) sD) 4 := ht.write (by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have aD1 := h.addr (d := sD1) (by simp only [sD1, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  have wD1 : InRegions t.wr (off (State.addr B) sD1) 4 := ht.write (by simp only [sD1, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega)
  simp only [List.append_assoc]
  have hp32 : 2 ^ lz T < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by unfold lz; omega)
  have hTz := (shifted_bounds hT0 hT' (Nat.le_refl (lz T))).1
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r12, .lr, .r0, .r1] (Q := fun v =>
      v.mem = t.mem.writeW (off (State.addr B) sP) (BitVec.ofNat 32 (2 ^ lz T)) ∧ v.gpr .r12 = B ∧
      v.gpr .lr = BitVec.ofNat 32 w ∧ v.gpr .r0 = BitVec.ofNat 32 (T * 2 ^ lz T) ∧ v.gpr .r1 = BitVec.ofNat 32 U ∧
      v.gpr .r2 = BitVec.ofNat 32 (2 ^ lz T) ∧ v.gpr .r11 = BitVec.ofNat 32 V) (by
    krun [ht.r8, ht.r9, t1, t2, t10, t11, aP, wP]) (by decide)) fun v1 ⟨⟨m1, b1, l1, x1, y1, p1, z1⟩, k1⟩ => ?_)
  refine wp_wide fun v2 e2 P2 => ?_
  rw [y1, p1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hU', Nat.mod_eq_of_lt hp32] at e2
  obtain ⟨lo2, hi2⟩ := wide_lo_hi (BitVec.isLt _) e2
  have q0 : v2.gpr .r0 = BitVec.ofNat 32 (T * 2 ^ lz T) := (P2.regs _ (by decide)).trans x1
  have q12 : v2.gpr .r12 = B := (P2.regs _ (by decide)).trans b1
  have ql : v2.gpr .lr = BitVec.ofNat 32 w := (P2.regs _ (by decide)).trans l1
  have q11 : v2.gpr .r11 = BitVec.ofNat 32 V := (P2.regs _ (by decide)).trans z1
  have q2 : v2.gpr .r2 = BitVec.ofNat 32 (2 ^ lz T) := (P2.regs _ (by decide)).trans p1
  have wD2 : InRegions v2.wr (off (State.addr B) sD) 4 := by rw [P2.wr, k1.wr]; exact wD
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r1] (Q := fun v =>
      v.mem = v2.mem.writeW (off (State.addr B) sD) (v2.gpr .r0 + v2.gpr .r4) ∧ v.gpr .r0 = v2.gpr .r3 ∧
      v.gpr .r1 = BitVec.ofNat 32 V ∧ v.gpr .r12 = B ∧ v.gpr .lr = BitVec.ofNat 32 w ∧
      v.gpr .r2 = BitVec.ofNat 32 (2 ^ lz T)) (by
    krun [q0, q12, ql, q11, q2, aD, wD2]) (by decide)) fun v3 ⟨⟨m3, x3, y3, b3, l3, p3⟩, k3'⟩ => ?_)
  refine wp_wide fun v4 e4 P4 => ?_
  rw [y3, p3, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV', Nat.mod_eq_of_lt hp32] at e4
  obtain ⟨lo4, hi4⟩ := wide_lo_hi (BitVec.isLt _) e4
  have s0 : v4.gpr .r0 = v2.gpr .r3 := (P4.regs _ (by decide)).trans x3
  have s12 : v4.gpr .r12 = B := (P4.regs _ (by decide)).trans b3
  have sl : v4.gpr .lr = BitVec.ofNat 32 w := (P4.regs _ (by decide)).trans l3
  have wD14 : InRegions v4.wr (off (State.addr B) sD1) 4 := by rw [P4.wr, k3'.wr, P2.wr, k1.wr]; exact wD1
  refine WP.mono (WP.keep [.r0, .r7, .r8, .r9] (Q := fun v =>
      v.mem = v4.mem.writeW (off (State.addr B) sD1) (v4.gpr .r0 + v4.gpr .r4) ∧ v.gpr .r8 = B ∧
      v.gpr .r9 = BitVec.ofNat 32 w ∧ v.gpr .r7 = (BitVec.ofNat 32 w + 2) <<< 2) (by
    krun [s0, s12, sl, aD1, wD14, VG.Impl.Rsa.Arm.Keys.stride]) (by decide)) fun u5 ⟨⟨m5, b5, n5, s5⟩, k5⟩ => ?_
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  have sPZ : sP + 4 ≤ Z := by simp only [sP, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega
  have sDZ : sD + 4 ≤ Z := by simp only [sD, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega
  have sD1Z : sD1 + 4 ≤ Z := by simp only [sD1, VG.Impl.Rsa.Arm.Keys.hdr] at hz ⊢; omega
  have mt : t.mem = s.mem := by rw [tm, vm, mu]
  have e5 : u5.mem = ((s.mem.writeW (off (State.addr B) sP) (BitVec.ofNat 32 (2 ^ lz T))).writeW
      (off (State.addr B) sD) (v2.gpr .r0 + v2.gpr .r4)).writeW (off (State.addr B) sD1) (v4.gpr .r0 + v4.gpr .r4) := by
    rw [m5, P4.mem, m3, P2.mem, m1, mt]
  have hdz : U * 2 ^ lz T / 2 ^ 32 < 2 ^ lz T := by
    rw [Nat.div_lt_iff_lt_mul (by decide), Nat.mul_comm (2 ^ lz T)]
    exact Nat.mul_lt_mul_of_pos_right hU' (Nat.two_pow_pos _)
  have hTz2 : T * 2 ^ lz T + 2 ^ lz T ≤ 2 ^ 32 := by
    have hzl : lz T ≤ 31 := by unfold lz; omega
    have e : 2 ^ 32 = 2 ^ (32 - lz T) * 2 ^ lz T := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hlt : T < 2 ^ (32 - lz T) := by rw [e] at hTz; exact Nat.lt_of_mul_lt_mul_right hTz
    calc T * 2 ^ lz T + 2 ^ lz T = (T + 1) * 2 ^ lz T := by rw [Nat.succ_mul]
      _ ≤ 2 ^ (32 - lz T) * 2 ^ lz T := Nat.mul_le_mul_right _ hlt
      _ = 2 ^ 32 := e.symm
  have dv : (v2.gpr .r0 + v2.gpr .r4).toNat = T * 2 ^ lz T + U * 2 ^ lz T / 2 ^ 32 := by
    rw [BitVec.toNat_add, q0, hi2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hTz]; omega
  have hz32 : lz T ≤ 32 := by unfold lz; omega
  have d1v : (v4.gpr .r0 + v4.gpr .r4).toNat = U * 2 ^ lz T % 2 ^ 32 + V * 2 ^ lz T / 2 ^ 32 := by
    rw [BitVec.toNat_add, s0, lo2, hi4]
    exact Nat.mod_eq_of_lt (VG.Proof.Bignum.WordStep32.lohi_lt hz32 hV')
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [slot]
    rw [e5, w32_write_ne hA sD1Z sPZ (by simp only [sP, sD1]; omega),
      w32_write_ne hA sDZ sPZ (by simp only [sP, sD]; omega), w32_write_self, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hp32]
  · simp only [slot]
    rw [e5, w32_write_ne hA sD1Z sDZ (by simp only [sD, sD1]; omega), w32_write_self, dv]
  · simp only [slot]
    rw [e5, w32_write_self, d1v]
  · rw [e5]
    exact ((keep_write _ _ (by simp) (by simp only [sP]; omega)).trans
      (keep_write _ _ (by simp) (by simp only [sD]; omega))).trans (keep_write _ _ (by simp) (by simp only [sD1]; omega))
  · have e7 : u5.gpr .r7 = BitVec.ofNat 32 (S w) := by
      rw [s5, stride_val (by omega)]
    exact ht.of (e7.trans ht.r7.symm) (b5.trans ht.r8.symm) (n5.trans ht.r9.symm)
      (by rw [k5.wr, P4.wr, k3'.wr, P2.wr, k1.wr])
  · have K : Rest (normRegs ++ [.r7, .r8, .r9]) s u5 :=
      ((((k3.mono (by decide)).trans (k1.mono (by decide))).trans ((Preserves.toRest P2).mono (by decide))).trans
        (((k3'.mono (by decide)).trans ((Preserves.toRest P4).mono (by decide))).trans (k5.mono (by decide))))
    refine ⟨fun r hr => ?_, K.rd, K.wr, K.sp⟩
    by_cases e : r ∈ [Reg.r7, .r8, .r9]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at e
      rcases e with rfl | rfl | rfl
      · rw [h.r7, s5, stride_val (by omega)]
      · rw [b5, h.r8]
      · rw [n5, h.r9]
    · exact K.gpr r fun hm => (List.mem_append.mp hm).elim hr e

end VG.Proof.Rsa.Arm.KeyDiv
