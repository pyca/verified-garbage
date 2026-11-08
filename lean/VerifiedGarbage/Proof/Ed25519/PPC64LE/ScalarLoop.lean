module

import VerifiedGarbage.Proof.Ed25519.Scalar
public import VerifiedGarbage.Proof.X25519.PPC64LE.Product
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
import VerifiedGarbage.Proof.Framework.PPC64LE.MovImm
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Proof.Ed25519.ScalarWord
public import VerifiedGarbage.Spec.Ed25519.Contract

/-!
# Ed25519 on PPC64LE: a 64-byte integer modulo `L`

`scalarReduceEngine` reads the 64 bytes at `r14` a word at a time, from the
top, each folded into the remainder in `r8`–`r11` (`scalarWord_ok`), and
stores the integer modulo `L` at `SR` (`engine_ok`). It writes no memory
before that store, so the input may be anywhere readable.

`wordFold` turns the remainder `r < L` and the next word `w` in `r12` into
`v mod L`, for `v = 2^64 r + w = h 2^252 + l`: `l - t` for `t = h c`, plus
`L` if that borrows (`fold_nat`). Each of its four blocks is checked against
the numbers it computes (`wordFold_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE VG.Proof.Ed25519
open VG.Spec.Ed25519 (L decodeLE bytesAt)

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- A write that keeps CA. -/
theorem wp_w {i : Instr} {d : Reg} {v : BitVec 64} (he : exec i s = some (s.write d v))
    (k : ∀ s', Upd s s' d v → s'.ca = s.ca → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons he (k _ (Upd.write _ _ _) rfl)

theorem wp_subc {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + 1) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subc d n m :: is)) s Q := by
  have := (s.gpr n).isLt; have := (s.gpr m).isLt
  exact WP.cons exec_subc (k _ (UpdC.writeCarry _ _ (by omega)))

theorem wp_sube {d n m : Reg}
    (k : ∀ s', UpdC s s' d ((s.gpr n).toNat + (2 ^ 64 - 1 - (s.gpr m).toNat) + s.ca.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.sube d n m :: is)) s Q := by
  have := (s.gpr n).isLt; have := (s.gpr m).isLt; have : s.ca.toNat ≤ 1 := Bool.toNat_le _
  exact WP.cons exec_sube (k _ (UpdC.writeCarry _ _ (by omega)))

/-- `lis`, `ori`, `sldi`, `oris`, `ori`: a 64-bit constant. -/
theorem movImm64_ok {d : Reg} {v : BitVec 64} (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (movImm64 d v ++ is)) s Q := by
  unfold movImm64
  simp only [List.cons_append, List.nil_append]
  refine wp_lis fun s1 u1 => wp_ori fun s2 u2 => wp_lsl (by decide) fun s3 u3 =>
    wp_w (v := s3.gpr d ||| (v.extractLsb' 16 16).setWidth 64 <<< 16) exec_oris fun s4 u4 _ =>
    wp_ori fun s5 u5 => k _ ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
    exact movImm64_eq v
  · rw [u5.other r hr, u4.other r hr, u3.other r hr, u2.other r hr, u1.other r hr]
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  · rw [u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · rw [u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

end

/-! ## Numbers -/

theorem c_limbs : orderLo.toNat + 2 ^ 64 * orderHi.toNat = cL := by decide

theorem orderHi_lt : orderHi.toNat < 2 ^ 61 := by decide

theorem mulhu_toNat (a b : BitVec 64) :
    (BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have hp : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
  rw [BitVec.toNat_ofNat]
  omega_arith

/-- A word times a bit, `h ≤ 1`, does not wrap. -/
theorem mul_bit (h v : BitVec 64) (hh : h.toNat ≤ 1) : (h * v).toNat = h.toNat * v.toNat := by
  rw [BitVec.toNat_mul]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hh with e | e <;> rw [e]
  · simp
  · rw [Nat.one_mul, Nat.mod_eq_of_lt v.isLt]

theorem mul_expand (X H C0 C1 : Nat) :
    (X + 2 ^ 64 * H) * (C0 + 2 ^ 64 * C1) =
      X * C0 + 2 ^ 64 * (X * C1) + 2 ^ 64 * (H * C0) + 2 ^ 128 * (H * C1) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm X (2 ^ 64),
    Nat.mul_assoc (2 ^ 64) H C0, Nat.mul_mul_mul_comm (2 ^ 64) H (2 ^ 64) C1]
  omega_arith

/-- The mask of a borrow `B`, and what `foldAdd` makes of it. -/
theorem mask_and (c : BitVec 64) {B : Nat} (hB : B ≤ 1) :
    (c &&& (0#64 - BitVec.ofNat 64 B)).toNat = B * c.toNat := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with rfl | rfl
  · simp
  · rw [show 0#64 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes, Nat.one_mul]

theorem mask_top {B : Nat} (hB : B ≤ 1) :
    ((0#64 - BitVec.ofNat 64 B) >>> 63 <<< 60).toNat = 2 ^ 60 * B := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with rfl | rfl <;> decide

/-- The remainder in `r8`–`r11`. -/
abbrev R4 (s : State) : Nat :=
  (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat + 2 ^ 128 * (s.gpr .r10).toNat +
    2 ^ 192 * (s.gpr .r11).toNat

theorem R4_lt (s : State) : R4 s < 2 ^ 256 := by
  have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
  have := (s.gpr .r11).isLt
  simp only [R4]
  omega_arith

/-! ## The blocks -/

section
variable {s : State}

theorem foldPrep_ok :
    WP isa (.block foldPrep) s fun t =>
      (t.gpr .r3).toNat = (s.gpr .r10).toNat / 2 ^ 60 + 16 * ((s.gpr .r11).toNat % 2 ^ 60) ∧
      (t.gpr .r4).toNat = (s.gpr .r11).toNat / 2 ^ 60 ∧
      t.gpr .r8 = s.gpr .r12 ∧ t.gpr .r9 = s.gpr .r8 ∧ t.gpr .r10 = s.gpr .r9 ∧
      (t.gpr .r11).toNat = (s.gpr .r10).toNat % 2 ^ 60 ∧
      Rest [.r3, .r4, .r8, .r9, .r10, .r11] s t ∧ t.mem = s.mem := by
  unfold foldPrep
  refine wp_lsr (by decide) fun s1 u1 => wp_lsl (by decide) fun s2 u2 =>
    wp_w (v := s2.gpr .r3 ||| s2.gpr .r4) exec_logic fun s3 u3 _ => wp_lsr (by decide) fun s4 u4 =>
    wp_lsl (by decide) fun s5 u5 => wp_lsr (by decide) fun s6 u6 =>
    wp_addi (by decide) (by decide) fun s7 u7 => wp_addi (by decide) (by decide) fun s8 u8 =>
    wp_addi (by decide) (by decide) fun s9 u9 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp (disch := decide) only [u9.gpr, u9.other, u8.gpr, u8.other, u7.gpr, u7.other,
    u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other,
    u1.gpr, u1.other, BitVec.add_zero]
  · exact shr_or_shl _ _
  · exact shr60 _
  · exact shl_shr _
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans (u9.rest (by decide)))))))))
  · rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

/-- `foldMul`: `t = (h₀ + 2^64 h₁) c` into `r5`, `r7`, `r3`, for `h₁ ≤ 1` in `r4`. -/
theorem foldMul_ok (h16 : s.gpr .r16 = orderLo) (h19 : s.gpr .r19 = orderHi)
    (hh : (s.gpr .r4).toNat ≤ 1) :
    WP isa (.block foldMul) s fun t =>
      (t.gpr .r5).toNat + 2 ^ 64 * (t.gpr .r7).toNat + 2 ^ 128 * (t.gpr .r3).toNat =
        ((s.gpr .r3).toNat + 2 ^ 64 * (s.gpr .r4).toNat) * cL ∧
      Rest [.r3, .r5, .r7, .r12] s t ∧ t.mem = s.mem := by
  unfold foldMul
  refine wp_mul fun s1 u1 => wp_mulhu fun s2 u2 => wp_mul fun s3 u3 => wp_mulhu fun s4 u4 =>
    wp_addc fun s5 u5 => wp_addze fun s6 u6 => wp_mul fun s7 u7 => wp_addc fun s8 u8 =>
    wp_addze fun s9 u9 => wp_mul fun s10 u10 => wp_add fun s11 u11 => WP.block_nil ⟨?_, ?_, ?_⟩
  · have e5 := u5.val; have e6 := u6.val; have e8 := u8.val; have e9 := u9.val
    have c5 := u5.ca; have c6 := u6.ca; have c8 := u8.ca; have c9 := u9.ca
    have g2 : (s2.gpr .r7).toNat = (s1.gpr .r3).toNat * (s1.gpr .r16).toNat / 2 ^ 64 := by
      rw [u2.gpr, mulhu_toNat]
    have g4 : (s4.gpr .r3).toNat = (s3.gpr .r3).toNat * (s3.gpr .r19).toNat / 2 ^ 64 := by
      rw [u4.gpr, mulhu_toNat]
    simp (disch := decide) only [u11.gpr, u11.other, u10.gpr, u10.other, u9.other, u8.other,
      u7.gpr, u7.other, u6.other, u5.other, u4.other, u3.gpr, u3.other, u2.other,
      u1.gpr, u1.other, h16, h19] at e5 e6 e8 e9 g2 g4 ⊢
    rw [g2] at e5; rw [g4] at e6
    rw [mul_bit _ _ hh] at e8
    rw [BitVec.toNat_add, mul_bit _ _ hh, BitVec.toNat_mul, ← c_limbs, mul_expand]
    have hx := (s.gpr .r3).isLt
    have hc0 := orderLo.isLt
    have hc1 := orderHi_lt
    have hq : (s.gpr .r3).toNat * orderHi.toNat < 2 ^ 64 * 2 ^ 61 := Nat.mul_lt_mul'' hx hc1
    have hq0 : (s.gpr .r4).toNat * orderLo.toNat ≤ orderLo.toNat := by
      have := Nat.mul_le_mul_right orderLo.toNat hh; omega_arith
    have hq1 : (s.gpr .r4).toNat * orderHi.toNat ≤ orderHi.toNat := by
      have := Nat.mul_le_mul_right orderHi.toNat hh; omega_arith
    have hl5 := (s5.gpr .r7).isLt; have hl6 := (s6.gpr .r3).isLt
    have hl8 := (s8.gpr .r7).isLt; have hl9 := (s9.gpr .r3).isLt
    rw [BitVec.toNat_mul] at e5
    generalize (s.gpr .r3).toNat * orderLo.toNat = P0 at *
    generalize (s.gpr .r3).toNat * orderHi.toNat = P1 at *
    generalize (s.gpr .r4).toNat * orderLo.toNat = Q0 at *
    generalize (s.gpr .r4).toNat * orderHi.toNat = Q1 at *
    omega_arith
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
      ((u10.rest (by decide)).trans (u11.rest (by decide)))))))))))
  · rw [u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

/-- `foldSub`: `l - t` into `r8`–`r11`, for `t` in `r5`, `r7`, `r3`, and the mask of its
borrow `B` into `r12`. -/
theorem foldSub_ok :
    WP isa (.block foldSub) s fun t => ∃ B, B ≤ 1 ∧
      R4 t + ((s.gpr .r5).toNat + 2 ^ 64 * (s.gpr .r7).toNat + 2 ^ 128 * (s.gpr .r3).toNat) =
        R4 s + 2 ^ 256 * B ∧ t.gpr .r12 = 0#64 - BitVec.ofNat 64 B ∧
      Rest [.r8, .r9, .r10, .r11, .r12] s t ∧ t.mem = s.mem := by
  unfold foldSub
  refine wp_subc fun s1 u1 => wp_sube fun s2 u2 => wp_sube fun s3 u3 =>
    wp_w (exec_li (imm := 0) (by decide)) fun s4 u4 c4 => wp_sube fun s5 u5 =>
    wp_addze fun s6 u6 => wp_subi (by decide) (by decide) fun s7 u7 =>
    WP.block_nil ⟨1 - s5.ca.toNat, by omega, ?_, ?_, ?_, ?_⟩
  · have e1 := u1.val; have e2 := u2.val; have e3 := u3.val; have e5 := u5.val
    have c5 := u5.ca
    rw [c4] at e5
    simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u4.other, u3.other,
      u2.other, u1.other, R4] at e1 e2 e3 e5 ⊢
    have := (s.gpr .r5).isLt; have := (s.gpr .r7).isLt; have := (s.gpr .r3).isLt
    have z : (BitVec.ofNat 64 0).toNat = 0 := rfl
    rw [z] at e5
    omega_arith
  · have e6 := u6.val
    simp only [u7.gpr]
    have c5 := u5.ca
    have := (s6.gpr .r12).isLt
    have h12 : (s6.gpr .r12).toNat = s5.ca.toNat := by
      simp (disch := decide) only [u5.other, u4.gpr] at e6
      rw [show (BitVec.ofNat 64 0).toNat = 0 from rfl] at e6
      omega_arith
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c5 with e | e <;> rw [e] at h12 ⊢
    · rw [show s6.gpr .r12 = 0#64 from BitVec.eq_of_toNat_eq h12]
    · rw [show s6.gpr .r12 = 1#64 from BitVec.eq_of_toNat_eq h12]; decide
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      (u7.rest (by decide)))))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

/-- `foldAdd`: `B L` added to `r8`–`r11`, for the mask of `B` in `r12`. -/
theorem foldAdd_ok (h16 : s.gpr .r16 = orderLo) (h19 : s.gpr .r19 = orderHi) {B : Nat}
    (hB : B ≤ 1) (h12 : s.gpr .r12 = 0#64 - BitVec.ofNat 64 B) :
    WP isa (.block foldAdd) s fun t => ∃ c, c ≤ 1 ∧ R4 t + 2 ^ 256 * c = R4 s + B * L ∧
      Rest [.r3, .r8, .r9, .r10, .r11] s t ∧ t.mem = s.mem := by
  unfold foldAdd
  refine wp_and fun s1 u1 => wp_addc fun s2 u2 =>
    wp_w (v := s2.gpr .r19 &&& s2.gpr .r12) exec_logic fun s3 u3 c3 => wp_adde fun s4 u4 =>
    wp_addze fun s5 u5 => wp_w (exec_lsr_d (by decide)) fun s6 u6 c6 =>
    wp_w (exec_lsl (by decide)) fun s7 u7 c7 => wp_adde fun s8 u8 =>
    WP.block_nil ⟨s8.ca.toNat, u8.ca, ?_, ?_, ?_⟩
  · have e2 := u2.val; have e4 := u4.val; have e5 := u5.val; have e8 := u8.val
    have c2 := u2.ca; have c4 := u4.ca; have c5 := u5.ca
    rw [c3] at e4; rw [c7, c6] at e8
    simp (disch := decide) only [u8.other, u7.gpr, u7.other, u6.gpr, u6.other, u5.other, u4.other,
      u3.gpr, u3.other, u2.other, u1.gpr, u1.other, h16, h19, h12, R4] at e2 e4 e5 e8 ⊢
    rw [mask_and _ hB] at e2 e4
    rw [mask_top hB] at e8
    have hL : L = orderLo.toNat + 2 ^ 64 * orderHi.toNat + 2 ^ 252 := by
      rw [c_limbs, L_eq]; omega_arith
    rw [hL, Nat.mul_add, Nat.mul_add, Nat.mul_left_comm B (2 ^ 64)]
    have := orderLo.isLt; have := orderHi_lt
    generalize B * orderLo.toNat = Q0 at *
    generalize B * orderHi.toNat = Q1 at *
    omega_arith
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide))))))))
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

/-- The registers `wordFold` writes. -/
abbrev foldClob : List Reg := [.r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

/-- **One word**: the remainder `r < L` in `r8`–`r11` and the next word `w` in
`r12` become `(w + 2^64 r) mod L`. -/
theorem wordFold_ok (h16 : s.gpr .r16 = orderLo) (h19 : s.gpr .r19 = orderHi) (hr : R4 s < L) :
    WP isa (.block wordFold) s fun t =>
      R4 t = ((s.gpr .r12).toNat + 2 ^ 64 * R4 s) % L ∧ Rest foldClob s t ∧ t.mem = s.mem := by
  unfold wordFold
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono foldPrep_ok fun s1 ⟨e3, e4, e8, e9, e10, e11, k1, m1⟩ => ?_
  have h16' : s1.gpr .r16 = orderLo := by rw [k1.gpr _ (by decide), h16]
  have h19' : s1.gpr .r19 = orderHi := by rw [k1.gpr _ (by decide), h19]
  have h11 : (s.gpr .r11).toNat < 2 ^ 61 := by
    have : L < 2 ^ 253 := by decide
    simp only [R4] at hr
    omega_arith
  have hh : (s1.gpr .r4).toNat ≤ 1 := by rw [e4]; omega_arith
  refine WP.mono (foldMul_ok h16' h19' hh) fun s2 ⟨m, k2, m2⟩ => ?_
  refine WP.mono foldSub_ok fun s3 ⟨B, hB, d, h12, k3, m3⟩ => ?_
  have h16'' : s3.gpr .r16 = orderLo := by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), h16']
  have h19'' : s3.gpr .r19 = orderHi := by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), h19']
  refine WP.mono (foldAdd_ok h16'' h19'' hB h12) fun s4 ⟨c, hc, a, k4, m4⟩ => ⟨?_, ?_, ?_⟩
  · have r2 : R4 s2 = R4 s1 := by
      simp only [R4, k2.gpr .r8 (by decide), k2.gpr .r9 (by decide), k2.gpr .r10 (by decide),
        k2.gpr .r11 (by decide)]
    have hw := (s.gpr .r12).isLt
    have t2 : (s2.gpr .r5).toNat + 2 ^ 64 * (s2.gpr .r7).toNat + 2 ^ 128 * (s2.gpr .r3).toNat =
        ((s.gpr .r12).toNat + 2 ^ 64 * R4 s) / 2 ^ 252 * cL := by
      rw [m, show (s1.gpr .r3).toNat + 2 ^ 64 * (s1.gpr .r4).toNat =
        ((s.gpr .r12).toNat + 2 ^ 64 * R4 s) / 2 ^ 252 by rw [e3, e4]; simp only [R4]; omega_arith]
    have l1 : R4 s1 = ((s.gpr .r12).toNat + 2 ^ 64 * R4 s) % 2 ^ 252 := by
      simp only [R4]
      rw [e8, e9, e10, e11]
      omega_arith
    obtain ⟨f1, f2, f3⟩ := fold_nat (R4 s) (s.gpr .r12).toNat hr hw
    rw [show R4 s * 2 ^ 64 + (s.gpr .r12).toNat = (s.gpr .r12).toNat + 2 ^ 64 * R4 s by
      rw [Nat.mul_comm, Nat.add_comm]] at f1 f2 f3
    rw [← f3]
    rw [r2, t2, l1] at d
    have hd := R4_lt s3
    have he := R4_lt s4
    have hl := Nat.mod_lt ((s.gpr .r12).toNat + 2 ^ 64 * R4 s) (show 0 < 2 ^ 252 by decide)
    generalize ((s.gpr .r12).toNat + 2 ^ 64 * R4 s) / 2 ^ 252 * cL = T at *
    generalize ((s.gpr .r12).toNat + 2 ^ 64 * R4 s) % 2 ^ 252 = l at *
    generalize R4 s3 = D at *
    generalize R4 s4 = E at *
    have hLv : L = 2 ^ 252 + 27742317777372353535851937790883648493 := by decide
    rw [hLv] at f1 f2 a ⊢
    clear f3 e3 e4 e8 e9 e10 e11 m t2 l1 r2 hh h11 hr
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB with rfl | rfl <;> omega_arith
  · exact (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans
      (k4.mono (by decide))))
  · rw [m4, m3, m2, m1]

end

/-- What the scalar code writes: the remainder (and the candidate of the check
that a scalar is below `L`, `SD`, after it). -/
abbrev RD (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SR, 64⟩

/-- The registers one word's fold writes. -/
abbrev wordClob : List Reg := [.r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r15]

/-- The registers the engine writes. -/
abbrev engClob : List Reg := [.r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r15, .r16, .r19]

section
variable {s : State}

theorem init_ok :
    WP isa (.block scalarInit) s fun t =>
      R4 t = 0 ∧ t.gpr .r15 = BitVec.ofNat 64 64 ∧ t.gpr .r16 = orderLo ∧ t.gpr .r19 = orderHi ∧
      Rest engClob s t ∧ t.mem = s.mem := by
  unfold scalarInit
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => wp_li (by decide) fun s3 u3 =>
    wp_li (by decide) fun s4 u4 => wp_li (by decide) fun s5 u5 => movImm64_ok fun s6 u6 => ?_
  rw [← List.append_nil (movImm64 .r19 orderHi)]
  refine movImm64_ok fun s7 u7 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp (disch := decide) only [R4, u7.gpr, u7.other, u6.gpr, u6.other, u5.gpr, u5.other,
    u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other, u1.gpr, BitVec.toNat_ofNat,
    Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      (u7.rest (by decide)))))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

/-- One word: `r15` counted down by 8, the word at `r14 + r15` folded into the remainder. -/
theorem scalarWord_ok {p : Addr} (h14 : s.gpr .r14 = p) {k : Nat}
    (h15 : s.gpr .r15 = BitVec.ofNat 64 (8 * (k + 1))) (h16 : s.gpr .r16 = orderLo)
    (h19 : s.gpr .r19 = orderHi) (hin : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8)
    (hr : R4 s < L) :
    WP isa (.block scalarWord) s fun t =>
      R4 t = ((s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat + 2 ^ 64 * R4 s) % L ∧
      t.gpr .r15 = BitVec.ofNat 64 (8 * k) ∧ Rest wordClob s t ∧ t.mem = s.mem := by
  unfold scalarWord scalarLoad
  simp only [List.cons_append, List.nil_append]
  refine wp_subi (by decide) (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e15 : s1.gpr .r15 = BitVec.ofNat 64 (8 * k) := by
    rw [u1.gpr, h15, show 8 * (k + 1) = 8 * k + 8 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e7 : s2.gpr .r7 + BitVec.ofNat 64 0 = p + BitVec.ofNat 64 (8 * k) := by
    rw [BitVec.add_zero, u2.gpr, u1.other _ (by decide), h14, e15]
  refine wp_w (exec_load_d (by decide) ⟨by decide, by decide⟩
    (by rw [e7, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin)) fun s3 u3 _ => ?_
  have k3 : Rest [.r7, .r12, .r15] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have r3 : R4 s3 = R4 s := by
    simp only [R4, k3.gpr .r8 (by decide), k3.gpr .r9 (by decide), k3.gpr .r10 (by decide),
      k3.gpr .r11 (by decide)]
  refine WP.mono (wordFold_ok (by rw [k3.gpr _ (by decide), h16]) (by rw [k3.gpr _ (by decide), h19])
    (by rw [r3]; exact hr)) fun t ⟨vt, kt, mt⟩ =>
      ⟨?_, ?_, (k3.mono (by decide)).trans (kt.mono (by decide)), by rw [mt, m3]⟩
  · rw [vt, r3, u3.gpr, e7, u2.mem, u1.mem]
  · rw [kt.gpr _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e15]

/-- The remainder, stored at `SR`. -/
theorem store_ok {b : Addr} (hc : Ctx b s) :
    WP isa (.block scalarStore) s fun t =>
      V t.mem b SR = R4 s ∧ Rest [] s t ∧ Frame [⟨b + BitVec.ofNat 64 SR, 32⟩] s.mem t.mem := by
  unfold scalarStore
  have hS : SR = 160 := rfl
  refine sd0_ok hc (by omega) (by omega) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest []) (by decide)
  refine sd0_ok hc1 (by omega) (by omega) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest []) (by decide)
  refine sd0_ok hc2 (by omega) (by omega) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest []) (by decide)
  refine sd0_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [V_eq4]
    simp only [val4, ew, R4, u4.mem, u3.mem, u2.mem, u1.mem, u3.gpr, u2.gpr, u1.gpr, hS,
      Nat.reduceMul, Nat.reduceAdd]
    simp (disch := omega) only [dw_write_self, dw_write_other]
    omega_arith
  · exact ⟨fun r _ => by rw [u4.gpr, u3.gpr, u2.gpr, u1.gpr], by rw [u4.rd, u3.rd, u2.rd, u1.rd],
      by rw [u4.wr, u3.wr, u2.wr, u1.wr], by rw [u4.sp, u3.sp, u2.sp, u1.sp]⟩
  · rw [u4.mem, u3.mem, u2.mem, u1.mem]
    simp only [hS, Nat.reduceAdd]
    have hw : ∀ d, 160 ≤ d → d + 8 ≤ 192 → ∀ {m m' : Mem}, Frame [⟨b + BitVec.ofNat 64 160, 32⟩] m m' →
        ∀ v : BitVec 64, Frame [⟨b + BitVec.ofNat 64 160, 32⟩] m (m'.writeW (b + BitVec.ofNat 64 d) v) :=
      fun d h1 h2 _ _ f v => f.writeW (List.mem_singleton_self _) _
        (Offset.contains b h1 (by omega) (by omega))
    exact hw 184 (by omega) (by omega) (hw 176 (by omega) (by omega) (hw 168 (by omega) (by omega)
      (hw 160 (by omega) (by omega) (Frame.refl _ _) _) _) _) _

end

theorem mod_inner (w a : Nat) : (w + 2 ^ 64 * (a % L)) % L = (w + 2 ^ 64 * a) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- After the words from `n` up: the remainder of the integer they make. -/
structure EngInv (p : Addr) (s0 : State) (n : Nat) (t : State) : Prop where
  le : n ≤ 8
  rest : Rest engClob s0 t
  mem : t.mem = s0.mem
  r15 : t.gpr .r15 = BitVec.ofNat 64 (8 * n)
  r16 : t.gpr .r16 = orderLo
  r19 : t.gpr .r19 = orderHi
  val : R4 t = decodeLE (bytesAt s0.mem (p + BitVec.ofNat 64 (8 * n)) (64 - 8 * n)) % L

/-- **The 64 bytes at `r14`**, modulo `L`, into `SR`. -/
theorem engine_ok {b : Addr} {s : State} (hc : Ctx b s) {p : Addr} (h14 : s.gpr .r14 = p)
    (hin : ∀ k < 8, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa scalarReduceEngine s fun t =>
      Rest engClob s t ∧ Frame [RD b] s.mem t.mem ∧
      V t.mem b SR = decodeLE (bytesAt s.mem p 64) % L := by
  unfold scalarReduceEngine
  have hS : SR = 160 := rfl
  refine WP.seq (WP.mono init_ok fun s1 ⟨r1, t15, t16, t19, k1, m1⟩ => ?_)
  have i1 : EngInv p s 8 s1 := ⟨Nat.le_refl _, k1, m1, t15, t16, t19, by
      rw [r1, show 64 - 8 * 8 = 0 from rfl]; rfl⟩
  refine WP.seq (WP.mono (WP.loop (M := isa) (fun n t => 1 ≤ n ∧ EngInv p s n t)
    (Q := fun t => EngInv p s 0 t) ?_ 8 s1 ⟨by decide, i1⟩) fun t ht => ?_)
  · intro n t ⟨hn, h⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k < 8 := by have := h.le; omega
    have hr : R4 t < L := by rw [h.val]; exact Nat.mod_lt _ order_pos
    refine WP.mono (scalarWord_ok (p := p) (k := k) (by rw [h.rest.gpr _ (by decide), h14]) h.r15
      h.r16 h.r19 (by rw [h.rest.rd, h.rest.wr]; exact hin k hk) hr) fun t' ⟨vt, r15, kt, mt⟩ => ?_
    have hv : R4 t' = decodeLE (bytesAt s.mem (p + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) % L := by
      rw [vt, h.val, h.mem, words_step _ _ _ hk, mod_inner]
    have i' : EngInv p s k t' := ⟨by omega, h.rest.trans (kt.mono (by decide)), by rw [mt, h.mem],
      r15, by rw [kt.gpr _ (by decide), h.r16], by rw [kt.gpr _ (by decide), h.r19], hv⟩
    rw [eval_nonzero, r15]
    by_cases hk0 : k = 0
    · subst hk0
      exact .inl ⟨by decide, i'⟩
    · have h8 : 8 * k ≠ 0 := by omega
      exact .inr ⟨by rw [ofNat_ne_zero (by omega)]; simp [h8], k, by omega, ⟨by omega, i'⟩⟩
  · refine WP.mono (store_ok (hc.of_rest ht.rest (by decide))) fun u ⟨vu, ru, fu⟩ =>
      ⟨ht.rest.trans (ru.mono (by decide)), ?_, ?_⟩
    · rw [← ht.mem]
      exact fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)⟩
    · rw [vu, ht.val, Nat.mul_zero, Nat.sub_zero, show BitVec.ofNat 64 0 = 0#64 from rfl,
        BitVec.add_zero]

end VG.Proof.Ed25519.PPC64LE
