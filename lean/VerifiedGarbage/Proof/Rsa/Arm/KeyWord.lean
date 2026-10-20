module
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps

import VerifiedGarbage.Proof.Rsa.Arm.KeyBits
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The operations on the arrays of the working space: low words and equality -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

/-- The store of `r1` to the low word of array `j` (pointer in `r0`). -/
theorem storeLow_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (p : s.gpr .r0 = B + BitVec.ofNat 32 (arr w j)) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = (s.gpr .r1).toNat + 2 ^ 32 * (num s.mem B w j / 2 ^ 32) →
      Rest [] s t → w32 t.mem (State.addr B) (arr w j + 4 * w) = w32 s.mem (State.addr B) (arr w j + 4 * w) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.str .r1 .r0 0 :: rest)) s Q := by
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  have nw := h.nowrap
  refine wp_str (by decide) (arr_addr0 h hj p) (h.write (by omega)) fun t u => ?_
  have wp := h.wpos
  refine k t (h.of_mupd u) ?_ ?_ (u.rest _) ?_
  · have o := writeW32_outside s.mem (State.addr B) (d := arr w j) (s.gpr .r1) (by omega)
    rw [u.mem]; exact Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using o) (by omega) (by simp)
  · rw [u.mem]; exact num_write0 _ _ h.wpos (by omega) _
  · rw [u.mem]
    exact (writeW32_outside s.mem (State.addr B) (d := arr w j) (s.gpr .r1) (by omega)).w32 (by omega) (by omega)

/-- `setOne j`: the low word of `[j]` := 1. -/
theorem setOne_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = 1 + 2 ^ 32 * (num s.mem B w j / 2 ^ 32) →
      Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (setOne j ++ rest)) s Q := by
  unfold setOne
  rw [List.append_assoc]
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  refine storeLow_ok (h1.of_upd u2 (by decide) (by decide) (by decide)) hj
    (by rw [u2.other _ (by decide), p1]) fun t ht kt vt rt _ => k t ht ?_ ?_ ?_
  · rw [u2.mem, m1] at kt; exact kt
  · rw [vt, u2.gpr, u2.mem, m1]; rfl
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans (rt.mono (by simp)))

/-- The low word of `[j]` into `r1` and back, through `f`. -/
theorem lowOp_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) {ops rest : List Instr} {Q : State → Prop} {f : BitVec 32 → BitVec 32}
    (hops : ∀ u : State, ∀ R : State → Prop, (∀ u', Upd u u' .r1 (f (u.gpr .r1)) → R u') →
      WP isa (.block ops) u R)
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = (f (BitVec.ofNat 32 (num s.mem B w j % 2 ^ 32))).toNat +
        2 ^ 32 * (num s.mem B w j / 2 ^ 32) →
      Rest opRegs s t → w32 t.mem (State.addr B) (arr w j + 4 * w) = w32 s.mem (State.addr B) (arr w j + 4 * w) →
      WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r0 j ++ .ldr .r1 .r0 0 :: (ops ++ .str .r1 .r0 0 :: rest))) s Q := by
  refine ptr_ok h (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  have fit := h.arr_fit hj
  have hS : S w = 4 * (w + 2) := rfl
  refine wp_ldr (by decide) (arr_addr0 h1 hj p1) (h1.read (by omega)) fun s2 u2 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hops s2 _ fun u' x => x) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := (h1.of_upd u2 (by decide) (by decide) (by decide)).of_upd u3 (by decide)
    (by decide) (by decide)
  refine storeLow_ok h3 hj (by rw [u3.other _ (by decide), u2.other _ (by decide), p1])
    fun t ht kt vt rt tt => k t ht ?_ ?_ ?_ ?_
  · rw [u3.mem, u2.mem, m1] at kt; exact kt
  · rw [vt, u3.gpr, u3.mem, u2.mem, m1, u2.gpr, m1, num_mod32 _ _ h.wpos]; simp
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (rt.mono (by simp))))
  · rw [tt, u3.mem, u2.mem, m1]

/-- `orOne j`: the low bit of `[j]` set. -/
theorem orOne_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = 2 * (num s.mem B w j / 2) + 1 → Rest opRegs s t → WP isa (.block rest) t Q) :
    WP isa (.block (orOne j ++ rest)) s Q := by
  unfold orOne
  rw [List.append_assoc]
  refine lowOp_ok (ops := [.dp .orr .r1 .r1 (.imm 1)]) (f := fun x => x ||| 1) h hj hN
    (fun u R k' => wp_dp (op2_imm (by decide)) fun u' up => WP.block_nil (k' u' up))
    fun t ht kt vt rt _ => k t ht kt ?_ rt
  rw [vt, bv_or_one, BitVec.toNat_ofNat, Nat.mod_mod]
  omega

/-- `clrLow j`: the low bit of `[j]` cleared. -/
theorem clrLow_ok {s : State} {B : BitVec 32} {Z w N j : Nat} (h : Ws s B Z w N)
    (hj : j < N) (hN : N ≤ 256) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Keep B w [j] [] s.mem t.mem →
      num t.mem B w j = 2 * (num s.mem B w j / 2) → Rest opRegs s t →
      w32 t.mem (State.addr B) (arr w j + 4 * w) = w32 s.mem (State.addr B) (arr w j + 4 * w) →
      WP isa (.block rest) t Q) :
    WP isa (.block (clrLow j ++ rest)) s Q := by
  unfold clrLow
  rw [List.append_assoc]
  refine lowOp_ok (ops := [.dp .orr .r1 .r1 (.imm 1), .dp .eor .r1 .r1 (.imm 1)])
    (f := fun x => (x ||| 1) ^^^ 1) h hj hN
    (fun u R k' => wp_dp (op2_imm (by decide)) fun u' up => wp_dp (op2_imm (by decide)) fun u'' up' =>
      WP.block_nil (k' u'' ⟨by rw [up'.gpr, dpVal, up.gpr]; rfl, fun r hr => by
        rw [up'.other r hr, up.other r hr], up'.mem.trans up.mem, up'.rd.trans up.rd,
        up'.wr.trans up.wr, up'.sp.trans up.sp⟩))
    fun t ht kt vt rt tt => k t ht kt ?_ rt tt
  rw [vt, bv_clr_one, BitVec.toNat_ofNat, Nat.mod_mod]
  omega

end VG.Proof.Rsa.Arm.Keys
