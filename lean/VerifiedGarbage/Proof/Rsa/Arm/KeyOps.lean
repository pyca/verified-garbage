module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Bignum.Arm.SubState
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Framework.Block

/-! # The operations on the arrays of the working space: subtraction and selection -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The registers the operations may change: all but `r6`–`r9`. -/
abbrev opRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r10, .r11, .r12, .lr]

/-- The pointers of three arrays into `r0`, `r10` and `r12`. -/
theorem ptr3_ok {s : State} {B : BitVec 32} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < 256) (ha : a < 256) (hb : b < 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, t.gpr .r0 = B + BitVec.ofNat 32 (arr w o) → t.gpr .r10 = B + BitVec.ofNat 32 (arr w a) →
      t.gpr .r12 = B + BitVec.ofNat 32 (arr w b) → Rest [.r0, .r10, .r12] s t → t.mem = s.mem →
      Ws t B Z w N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ rest)) s Q := by
  refine ptr_ok h (by decide) ho fun s1 p1 r1 m1 h1 => ?_
  refine ptr_ok h1 (by decide) ha fun s2 p2 r2 m2 h2 => ?_
  refine ptr_ok h2 (by decide) hb fun t p3 r3 m3 h3 => ?_
  refine k t ?_ ?_ p3 ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (r3.mono (by simp))))
    (m3.trans (m2.trans m1)) h3
  · rw [r3.gpr _ (by decide), r2.gpr _ (by decide), p1]
  · rw [r3.gpr _ (by decide), p2]

theorem Ws.subCtx {s : State} {B : BitVec 32} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hoa : o ≠ a) (hob : o ≠ b) :
    SubCtx s B Z (arr w o) (arr w a) (arr w b) w := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have da := arr_disj (w := w) hoa
  have db := arr_disj (w := w) hob
  have hS : S w = 4 * (w + 2) := rfl
  refine ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, h.writable⟩

/-- `sub3 o a b`: `[o] = [a] - [b]` with the borrow in `r11`. -/
theorem sub3_ok {s : State} {B : BitVec 32} {Z w N o a b : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b) :
    WP isa (sub3 o a b) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o + num s.mem B w b = num s.mem B w a + 2 ^ (32 * w) * (t.gpr .r11).toNat ∧
      (t.gpr .r11).toNat ≤ 1 ∧ Rest opRegs s t := by
  rw [sub3, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := (h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  refine WP.mono (subRow_ok u (hu.subCtx ho ha hb hoa hob) h.wpos
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr, h3.r9])
    (by rw [u5.gpr]; decide)) ?_
  intro t inv
  have v := inv.value
  rw [u5.gpr, mu] at v
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
      (by simp only [S]; omega) (by simp), ?_, inv.borrow, restU.trans (inv.rest.mono (by simp))⟩
  simpa using v

/-- `sel o a b sl`: `[o] = [b]` if the slot `sl` is 1, `[a]` if it is 0. -/
theorem sel_ok {s : State} {B : BitVec 32} {Z w N o a b sl : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (hoa : o ≠ a) (hob : o ≠ b)
    (hsl : sl + 4 ≤ hdr) (bit : slot s.mem B sl ≤ 1) :
    WP isa (sel o a b sl) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = (if slot s.mem B sl = 0 then num s.mem B w a else num s.mem B w b) ∧
      Rest opRegs s t := by
  rw [sel, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h4 hsl fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  have bitU : (u.gpr .r11).toNat = slot s.mem B sl := by
    rw [u5.gpr, u4.mem, m3]
  refine WP.mono (selectRow_ok u (hu.subCtx ho ha hb hoa hob) h.wpos
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr, h3.r9])
    (by rw [bitU]; exact bit)) ?_
  intro t inv
  have v := inv.value
  rw [bitU, mu] at v
  exact ⟨hu.rest inv.rest, Keep.of_arr (d := 0)
    (by simpa only [Nat.add_zero, mu] using inv.outside) (by simp only [S]; omega) (by simp), v,
    restU.trans (inv.rest.mono (by simp))⟩

/-- `copy o a`: `[o] = [a]`. -/
theorem copy_ok {s : State} {B : BitVec 32} {Z w N o a : Nat} (h : Ws s B Z w N)
    (ho : o < N) (ha : a < N) (hN : N ≤ 256) (hoa : o ≠ a) :
    WP isa (copy o a) s fun t => Ws t B Z w N ∧ Keep B w [o] [] s.mem t.mem ∧
      num t.mem B w o = num s.mem B w a ∧ Rest opRegs s t ∧
      w32 t.mem (State.addr B) (arr w o + 4 * w) = w32 s.mem (State.addr B) (arr w o + 4 * w) := by
  rw [copy, WP.seq_iff]
  refine ptr3_ok h (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine wp_mov (op2_reg _ _) fun s4 u4 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := (h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans m3)
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans (u5.rest (by simp)))
  refine WP.mono (selectRow_ok u (hu.subCtx ho ha ha hoa hoa) h.wpos
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u5.other _ (by decide), u4.gpr, h3.r9])
    (by rw [u5.gpr]; decide)) ?_
  intro t inv
  have v := inv.value
  rw [mu] at v
  have fo := h.fit64 ho
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0)
    (by simpa only [Nat.add_zero, mu] using inv.outside) (by simp only [S]; omega) (by simp), ?_,
    restU.trans (inv.rest.mono (by simp)), ?_⟩
  · change val32 _ _ _ _ = _; rw [v]; split <;> rfl
  · rw [← mu]; exact inv.outside.w32 (by omega) (by simp only [S] at fo; omega)

end VG.Proof.Rsa.Arm.Keys
