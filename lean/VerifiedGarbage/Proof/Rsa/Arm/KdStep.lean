module

public import VerifiedGarbage.Proof.Rsa.Arm.KdEst
public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Bignum.Arm.CopyWords
import VerifiedGarbage.Proof.Bignum.Arm.SubRow
import VerifiedGarbage.Proof.Bignum.Arm.SelectRow
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.Omega

/-! # A step's subtraction of the key checks' division on ARMv7 (`KeyDiv.step`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont VG.Impl.Bignum.Arm
  VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_dp wp_str op2_reg op2_imm op2_lsr dpVal)
open VG.Impl.Rsa.Arm.Keys (sC)

/-- `lr := w / 2 + 1` from `r9 = w`. -/
theorem dwLr_val {w : Nat} (hw : w ≤ 1024) :
    BitVec.ofNat 32 w >>> 1 + 1 = BitVec.ofNat 32 (w / 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-- `clearT t`: `[t]`'s `w / 2 + 1` words zero, copied from `[0]`'s. -/
theorem clearT_ok {s : State} {B : BitVec 32} {Z w N t : Nat} (h : Ws s B Z w N) (ht : t < N) (ht0 : t ≠ 0)
    (hN : N ≤ 256) (hz : val32 s.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0) :
    WP isa (clearT t) s fun v => Ws v B Z w N ∧ Keep B w [t] [] s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w t) (w / 2 + 1) = 0 ∧ Rest opRegs s v := by
  have := h.wle
  rw [clearT, WP.seq_iff]
  refine ptr3_ok h (o := t) (a := 0) (b := 0) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun u u6 => WP.block_nil ?_
  have hu : Ws u B Z w N :=
    ((h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)).of_upd u6
      (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans m3))
  have restU : Rest opRegs s u :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))
  have ft := h.arr_fit ht
  have f0 := h.arr_fit (j := 0) (by omega)
  have dt := arr_disj (w := w) ht0
  simp only [S] at ft f0 dt
  have ctx : SubCtx u B Z (arr w t) (arr w 0) (arr w 0) (w / 2 + 1) :=
    ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, by rw [restU.wr]; exact h.writable⟩
  refine WP.mono (copyWords_ok u ctx (by omega)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u6.other _ (by decide), u5.gpr, dpVal, u4.gpr, h3.r9, dwLr_val (by omega)])) ?_
  intro v inv
  have vv := inv.value
  rw [mu] at vv
  refine ⟨hu.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mu] using inv.outside)
    (by simp only [S]; omega) (by simp), ?_, restU.trans (inv.rest.mono (by simp))⟩
  rw [vv]; split <;> exact hz

theorem dw_val {w : Nat} (hw : w ≤ 1024) : BitVec.ofNat 32 w >>> 1 = BitVec.ofNat 32 (w / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- The registers of a step's parts but `r7`–`r9`, which they put back. -/
abbrev divRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr]

/-- Put back `r7`–`r9` in a `Rest` over every register. -/
theorem rest_back {s t : State} {B : BitVec 32} {Z w N : Nat} {ws : List Reg} (h : Ws s B Z w N)
    (ht : Ws t B Z w N) (r : Rest ws s t) (hws : ∀ x ∈ ws, x ∈ divRegs ++ [.r7, .r8, .r9] := by decide) :
    Rest divRegs s t := by
  have K := r.mono hws
  refine ⟨fun x hx => ?_, K.rd, K.wr, K.sp⟩
  by_cases e : x ∈ [Reg.r7, .r8, .r9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at e
    rcases e with rfl | rfl | rfl
    · rw [ht.r7, h.r7]
    · rw [ht.r8, h.r8]
    · rw [ht.r9, h.r9]
  · exact K.gpr x fun hm => (List.mem_append.mp hm).elim hx e

/-- `prodT m t`: `[t] := q̂ [m]` over `w / 2` words and its carry, for `[t]` zero. -/
theorem prodT_ok {s : State} {B : BitVec 32} {Z w N m t : Nat} (h : Ws s B Z w N) (hm : m < N) (ht : t < N)
    (hmt : m ≠ t) (hN : N ≤ 256) (h16 : slot s.mem B 16 = w) (hdw : 1 ≤ w / 2)
    (hz : val32 s.mem (State.addr B) (arr w t) (w / 2) = 0) {q : Nat} (hq : slot s.mem B sQ = q) :
    WP isa (prodT m t) s fun v => Ws v B Z w N ∧ Keep B w [t] [] s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w t) (w / 2 + 1) = q * val32 s.mem (State.addr B) (arr w m) (w / 2) ∧
      Rest divRegs s v := by
  have := h.wle
  have nw := h.nowrap
  have fm := h.arr_fit hm
  have ft := h.arr_fit ht
  have dt := arr_disj (w := w) hmt
  have hz' := h.hdr_le
  simp only [S] at fm ft dt
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  rw [prodT, WP.seq_iff, List.append_assoc]
  refine ptr_ok h (r := .r0) (by decide) (j := t) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine ptr_ok h1 (r := .r12) (by decide) (j := m) (by omega) fun s2 p2 r2 m2 h2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  have h3 : Ws s3 B Z w N := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h3 (d := sQ) (by decide) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun u u5 => WP.block_nil ?_
  have hu : Ws u B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  have mu : u.mem = s.mem := u5.mem.trans (u4.mem.trans (u3.mem.trans (m2.trans m1)))
  have restU : Rest [.r0, .r12, .lr, .r1, .r11] s u :=
    ((r1.mono (by simp)).trans (r2.mono (by simp))).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      (u5.rest (by simp))))
  have rc : RowCtx u B Z (arr w t) (arr w m) (w / 2) :=
    ⟨h.nowrap, by omega, by omega, by omega, by rw [restU.wr]; exact h.writable⟩
  have x1 : (u.gpr .r1).toNat = q := by
    rw [u5.other _ (by decide), u4.gpr, u3.mem, m2, m1, ← hq]
  have x11 : (u.gpr .r11).toNat = 0 := by rw [u5.gpr]; rfl
  rw [WP.seq_iff]
  refine WP.mono (WP.keep [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .r10, .r11, .r12, .lr]
    (row_ok u rc (by omega) (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      r2.gpr _ (by decide), p1]) (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), p2])
      (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, h2.r9, dw_val (by omega)]))
    (by decide)) fun v ⟨inv, kv⟩ => ?_
  have h8 : v.gpr .r8 = B := by rw [kv.gpr _ (by decide), hu.r8]
  have aW : State.addr (v.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr B) (arr w t + 4 * (w / 2)) := by
    rw [inv.outPtr, BitVec.add_zero]; exact h.addr (by omega)
  rw [← List.append_nil ([Instr.str .r11 .r0 0] ++ VG.Impl.Rsa.Arm.KeyDiv.ctx), List.append_assoc, List.singleton_append]
  refine wp_str (by decide) aW (by rw [kv.wr, restU.wr]; exact h.write (by omega)) fun v1 u1 => ?_
  have mv1 : v1.mem = v.mem.writeW (off (State.addr B) (arr w t + 4 * (w / 2))) (v.gpr .r11) := u1.mem
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  have h16' : slot v1.mem B 16 = w := by
    simp only [slot]
    have ht0 : 160 ≤ arr w t := Nat.le_add_right _ _
    rw [mv1, w32_write_ne hA (by omega) (by omega) (by omega), inv.outside.w32 (by omega) (by omega), mu]
    exact h16
  refine kctx_ok (h.m.of (by rw [u1.wr, kv.wr, restU.wr])) (by rw [u1.gpr]; exact h8) h16' h.wpos this
    fun v2 h2' R2 m2' => WP.block_nil ⟨h2', ?_, ?_, ?_⟩
  · rw [m2', mv1, ← mu]
    exact (Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using inv.outside) (by simp only [S]; omega)
      (by simp)).trans (Keep.of_arr (d := 4 * (w / 2)) (writeW32_outside _ _ _ (by omega)) (by simp only [S]; omega)
      (by simp))
  · have vv := inv.value
    rw [x1, x11, mu, hz] at vv
    rw [m2', mv1, val32_succ, w32_write_self, Outside.val32 (writeW32_outside _ _ _ (by omega)) (by omega)
      (by omega)]
    omega
  · exact rest_back h h2' (ws := divRegs ++ [.r7, .r8, .r9]) (((restU.mono (by decide)).trans (kv.mono (by decide))).trans
      ((u1.rest _).trans (R2.mono (by decide)))) (by decide)

/-- `winPtr r rr t`: `r` at the window, word `j` (72, `4 j`) of `[rr]`. -/
theorem winPtr_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : Ws s B Z w N) {r t : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) (ht : t ∉ [.r7, .r8, .r9]) (hrt : r ≠ t) {rr j : Nat} (hrr : rr < 256)
    (hJ : slot s.mem B sJ = 4 * j) {rest : List Instr} {Q : State → Prop}
    (k : ∀ u, u.gpr r = B + BitVec.ofNat 32 (arr w rr + 4 * j) → Rest [r, t] s u → u.mem = s.mem →
      Ws u B Z w N → WP isa (.block rest) u Q) :
    WP isa (.block (winPtr r rr t ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  have r9 : r ≠ .r9 := fun e => hr (by simp [e])
  have t7 : t ≠ .r7 := fun e => ht (by simp [e])
  have t8 : t ≠ .r8 := fun e => ht (by simp [e])
  have t9 : t ≠ .r9 := fun e => ht (by simp [e])
  simp only [winPtr, List.append_assoc, List.cons_append, List.nil_append]
  refine ptr_ok h hr hrr fun u1 p1 r1 m1 h1 => ?_
  refine wp_ldrSlot h1 (d := sJ) (by decide) fun u2 U2 => ?_
  refine wp_dp (op2_reg _ _) fun u3 U3 => k u3 ?_ ?_ ?_ ?_
  · rw [U3.gpr, dpVal, U2.other _ hrt, p1, U2.gpr, m1,
      show s.mem.readW (off (State.addr B) sJ) 32 = BitVec.ofNat 32 (4 * j) by
        rw [← hJ]; exact (ofNat_toNat32 _).symm, add_ofNat_assoc]
  · exact (r1.mono (by simp)).trans ((U2.rest (by simp)).trans (U3.rest (by simp)))
  · rw [U3.mem, U2.mem, m1]
  · exact (h1.of_upd U2 t7 t8 t9).of_upd U3 r7 r8 r9

/-- `subT r t u`: `[u] := Y - [t]` over `w / 2 + 1` words, `Y` the window at word `j`
of `[r]`, the borrow into `sC`. -/
theorem subT_ok {s : State} {B : BitVec 32} {Z w N r t u j : Nat} (h : Ws s B Z w N) (hr : r < N) (ht : t < N)
    (hu : u < N) (hN : N ≤ 256) (hru : r ≠ u) (htu : t ≠ u) (hJ : slot s.mem B sJ = 4 * j) (hj : j + w / 2 ≤ w) :
    WP isa (subT r t u) s fun v => Ws v B Z w N ∧ Keep B w [u] [sC] s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w u) (w / 2 + 1) + val32 s.mem (State.addr B) (arr w t) (w / 2 + 1) =
        val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) + 2 ^ (32 * (w / 2 + 1)) * slot v.mem B sC ∧
      slot v.mem B sC ≤ 1 ∧ Rest opRegs s v := by
  have := h.wle
  have nw := h.nowrap
  have fr := h.arr_fit hr
  have ft := h.arr_fit ht
  have fu := h.arr_fit hu
  have dr := arr_disj (w := w) hru
  have dt := arr_disj (w := w) htu
  have hz' := h.hdr_le
  have r0 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr ft fu dr dt
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  rw [subT, WP.seq_iff, List.append_assoc, List.append_assoc]
  refine ptr_ok h (r := .r0) (by decide) (j := u) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine winPtr_ok h1 (r := .r10) (t := .r1) (by decide) (by decide) (by decide) (rr := r) (j := j) (by omega)
    (by rw [m1]; exact hJ) fun s2 p2 r2 m2 h2 => ?_
  refine ptr_ok h2 (r := .r12) (by decide) (j := t) (by omega) fun s3 p3 r3 m3 h3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun x u6 => WP.block_nil ?_
  have hx : Ws x B Z w N :=
    ((h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)).of_upd u6
      (by decide) (by decide) (by decide)
  have mx : x.mem = s.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans (m3.trans (m2.trans m1))))
  have restX : Rest opRegs s x :=
    ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (r3.mono (by simp)))).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))
  have sc : SubCtx x B Z (arr w u) (arr w r + 4 * j) (arr w t) (w / 2 + 1) :=
    ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, by rw [restX.wr]; exact h.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (subRow_ok x sc (by omega)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), p1])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide), p2])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p3])
    (by rw [u6.other _ (by decide), u5.gpr, dpVal, u4.gpr, h3.r9, dwLr_val (by omega)])
    (by rw [u6.gpr]; decide)) fun v inv => ?_
  have hv : Ws v B Z w N := hx.rest inv.rest
  have aC : State.addr (v.gpr .r8 + BitVec.ofNat 32 sC) = off (State.addr B) sC :=
    (congrArg (fun x => State.addr (x + BitVec.ofNat 32 sC)) hv.r8).trans (h.addr (d := sC) (by simp only [sC]; omega))
  have wC : InRegions v.wr (off (State.addr B) sC) 4 :=
    (inv.rest.wr.trans restX.wr) ▸ h.write (d := sC) (by simp only [sC]; omega)
  refine wp_str (by decide) aC wC fun v1 u1 => WP.block_nil ?_
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  have sCv : slot v1.mem B sC = (v.gpr .r11).toNat := by simp only [slot]; rw [u1.mem, w32_write_self]
  have vv := inv.value
  rw [u6.gpr, mx] at vv
  refine ⟨hv.of_mupd u1, ?_, ?_, by rw [sCv]; exact inv.borrow,
    restX.trans ((inv.rest.mono (by simp)).trans (u1.rest _))⟩
  · rw [u1.mem, ← mx]
    exact (Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using inv.outside) (by simp only [S]; omega)
      (by simp)).trans (keep_write _ _ (by simp) (by simp only [sC]; omega))
  · have u0 : 160 ≤ arr w u := Nat.le_add_right _ _
    rw [sCv, u1.mem, Outside.val32 (d := arr w u) (k := w / 2 + 1) (writeW32_outside _ _ _ (by simp only [sC]; omega))
      (Or.inr (by simp only [sC]; omega)) (by omega)]
    simpa using vv

/-- `selT t nm`: `[t] := [nm]` if the borrow `sC` is set, else `[0]`, over `w / 2 + 1` words. -/
theorem selT_ok {s : State} {B : BitVec 32} {Z w N t nm : Nat} (h : Ws s B Z w N) (ht : t < N) (hnm : nm < N)
    (hN : N ≤ 256) (ht0 : t ≠ 0) (htn : t ≠ nm) (hc : slot s.mem B sC ≤ 1) :
    WP isa (selT t nm) s fun v => Ws v B Z w N ∧ Keep B w [t] [] s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w t) (w / 2 + 1) = (if slot s.mem B sC = 0 then
        val32 s.mem (State.addr B) (arr w 0) (w / 2 + 1) else val32 s.mem (State.addr B) (arr w nm) (w / 2 + 1)) ∧
      Rest opRegs s v := by
  have := h.wle
  have ft := h.arr_fit ht
  have f0 := h.arr_fit (j := 0) (by omega)
  have fn := h.arr_fit hnm
  have d0 := arr_disj (w := w) ht0
  have dn := arr_disj (w := w) htn
  simp only [S] at ft f0 fn d0 dn
  rw [selT, WP.seq_iff]
  refine ptr3_ok h (o := t) (a := 0) (b := nm) (by omega) (by omega) (by omega) fun s3 p0 p10 p12 r3 m3 h3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  have h4 : Ws s4 B Z w N := h3.of_upd u4 (by decide) (by decide) (by decide)
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  have h5 : Ws s5 B Z w N := h4.of_upd u5 (by decide) (by decide) (by decide)
  refine wp_ldrSlot h5 (d := sC) (by simp only [sC, VG.Impl.Rsa.Arm.Keys.hdr]; omega) fun x u6 => WP.block_nil ?_
  have hx : Ws x B Z w N := h5.of_upd u6 (by decide) (by decide) (by decide)
  have mx : x.mem = s.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans m3))
  have restX : Rest opRegs s x :=
    (r3.mono (by simp)).trans ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))
  have bitX : (x.gpr .r11).toNat = slot s.mem B sC := by rw [u6.gpr, u5.mem, u4.mem, m3]
  have sc : SubCtx x B Z (arr w t) (arr w 0) (arr w nm) (w / 2 + 1) :=
    ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, by rw [restX.wr]; exact h.writable⟩
  refine WP.mono (selectRow_ok x sc (by omega)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p0])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p10])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p12])
    (by rw [u6.other _ (by decide), u5.gpr, dpVal, u4.gpr, h3.r9, dwLr_val (by omega)])
    (by rw [bitX]; exact hc)) fun v inv => ?_
  have vv := inv.value
  rw [bitX, mx] at vv
  exact ⟨hx.rest inv.rest, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero, mx] using inv.outside)
    (by simp only [S]; omega) (by simp), vv, restX.trans (inv.rest.mono (by simp))⟩

/-- `subBack r t u`: the window at word `j` of `[r]` `:= [u] - [t]` over `w / 2 + 1` words,
the borrow in `r11`. -/
theorem subBack_ok {s : State} {B : BitVec 32} {Z w N r t u j : Nat} (h : Ws s B Z w N) (hr : r < N)
    (ht : t < N) (hu : u < N) (hN : N ≤ 256) (hru : r ≠ u) (hrt : r ≠ t) (hJ : slot s.mem B sJ = 4 * j)
    (hj : j + w / 2 ≤ w) :
    WP isa (subBack r t u) s fun v => Ws v B Z w N ∧
      Outside (State.addr B) (arr w r + 4 * j) (4 * (w / 2 + 1)) s.mem v.mem ∧
      val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) + val32 s.mem (State.addr B) (arr w t) (w / 2 + 1) =
        val32 s.mem (State.addr B) (arr w u) (w / 2 + 1) + 2 ^ (32 * (w / 2 + 1)) * (v.gpr .r11).toNat ∧
      Rest opRegs s v := by
  have := h.wle
  have fr := h.arr_fit hr
  have ft := h.arr_fit ht
  have fu := h.arr_fit hu
  have du := arr_disj (w := w) hru
  have dt := arr_disj (w := w) hrt
  simp only [S] at fr ft fu du dt
  rw [subBack, WP.seq_iff, List.append_assoc, List.append_assoc]
  refine winPtr_ok h (r := .r0) (t := .r1) (by decide) (by decide) (by decide) (rr := r) (j := j) (by omega)
    hJ fun s1 p1 r1 m1 h1 => ?_
  refine ptr_ok h1 (r := .r10) (by decide) (j := u) (by omega) fun s2 p2 r2 m2 h2 => ?_
  refine ptr_ok h2 (r := .r12) (by decide) (j := t) (by omega) fun s3 p3 r3 m3 h3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun x u6 => WP.block_nil ?_
  have hx : Ws x B Z w N :=
    ((h3.of_upd u4 (by decide) (by decide) (by decide)).of_upd u5 (by decide) (by decide) (by decide)).of_upd u6
      (by decide) (by decide) (by decide)
  have mx : x.mem = s.mem := u6.mem.trans (u5.mem.trans (u4.mem.trans (m3.trans (m2.trans m1))))
  have restX : Rest opRegs s x :=
    ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (r3.mono (by simp)))).trans
      ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans (u6.rest (by simp))))
  have sc : SubCtx x B Z (arr w r + 4 * j) (arr w u) (arr w t) (w / 2 + 1) :=
    ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, by rw [restX.wr]; exact h.writable⟩
  refine WP.mono (subRow_ok x sc (by omega)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), p1])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide), p2])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), p3])
    (by rw [u6.other _ (by decide), u5.gpr, dpVal, u4.gpr, h3.r9, dwLr_val (by omega)])
    (by rw [u6.gpr]; decide)) fun v inv => ?_
  have vv := inv.value
  rw [u6.gpr, mx] at vv
  refine ⟨hx.rest inv.rest, by simpa only [mx] using inv.outside, by simpa using vv,
    restX.trans (inv.rest.mono (by simp))⟩

/-- A step's arithmetic: `U = Y - q̂ M` modulo `W` with its borrow `b`, then `W - M`
subtracted (`M` added) for the borrow, is `Y mod M`, for `⌊Y / M⌋ ≤ q̂ ≤ ⌊Y / M⌋ + 1`. -/
theorem step_math {W Y M qh U V b c : Nat} (hM0 : 0 < M) (hMW : M ≤ W) (hge : Y / M ≤ qh)
    (hle : qh ≤ Y / M + 1) (hU : U < W) (hb : b ≤ 1) (h1 : U + qh * M = Y + W * b) (hV : V < W)
    (h2 : V + (if b = 0 then 0 else W - M) = U + W * c) : V = Y % M := by
  have hy := Nat.div_add_mod Y M
  have hr := Nat.mod_lt Y hM0
  generalize Y / M = Q at hge hle hy
  generalize Y % M = R at hy hr ⊢
  have e : qh * M = Q * M + (qh - Q) * M := by rw [← Nat.add_mul]; congr 1; omega
  rw [Nat.mul_comm M Q] at hy
  have hc : qh - Q = 0 ∨ qh - Q = 1 := by omega
  rw [e] at h1
  generalize Q * M = P at h1 hy
  rcases hc with hc | hc <;> rw [hc] at h1 <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    simp only [↓reduceIte, Nat.zero_mul, Nat.one_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero,
      show (1 : Nat) = 0 ↔ False by decide] at h1 h2 <;>
    rcases (show c = 0 ∨ 1 ≤ c by omega) with rfl | hc1 <;> (try simp only [Nat.mul_zero, Nat.add_zero] at h2) <;>
    (try have := Nat.mul_le_mul_left W hc1) <;> omega

/-- Words within an array outside the frame. -/
theorem keep_val {B : BitVec 32} {w : Nat} {js ds : List Nat} {m m' : Mem} (K : Keep B w js ds m m')
    {a o k : Nat} (hlo : arr w a ≤ o) (hhi : o + 4 * k ≤ arr w a + S w) (ha : ∀ x ∈ js, x ≠ a)
    (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr := by decide) (fit : arr w a + S w ≤ 2 ^ 64) :
    val32 m' (State.addr B) o k = val32 m (State.addr B) o k := by
  refine Outs.val32 K (fun x hx => ?_) (by omega)
  simp only [ranges, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := w) (ha y hy); simp only [S] at this hhi ⊢; omega
  · have := hd d hd'; have : VG.Impl.Rsa.Arm.Keys.hdr ≤ arr w a := Nat.le_add_right _ _; dsimp only; omega

/-- A step's first half: the estimate `q̂`, then `[t] := q̂ M`. -/
theorem stepA_ok {s : State} {B : BitVec 32} {Z w N r m t j z : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hm : m < N) (ht : t < N) (hN : N ≤ 256) (hmt : m ≠ t) (ht0 : t ≠ 0)
    (h16 : slot s.mem B 16 = w) (hdw : 3 ≤ w / 2) (hJ : slot s.mem B sJ = 4 * j) (hj : j + w / 2 ≤ w)
    {Y M : Nat} (hY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y)
    (hM : val32 s.mem (State.addr B) (arr w m) (w / 2) = M) (hYM : Y < M * 2 ^ 32)
    (hz : z ≤ 31) (hP : slot s.mem B sP = 2 ^ z) (hMP : M * 2 ^ z < 2 ^ (32 * (w / 2)))
    (hD : slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2)))
    (hDn : 2 ^ 31 ≤ slot s.mem B sD) (hV : slot s.mem B sV = (2 ^ 64 - 1) / slot s.mem B sD - 2 ^ 32)
    (hz0 : val32 s.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ v q, Y / M ≤ q → q ≤ Y / M + 1 → val32 v.mem (State.addr B) (arr w t) (w / 2 + 1) = q * M →
      Keep B w [t] [sMk, sQ, sU0, sU2] s.mem v.mem → Ws v B Z w N → Rest divRegs s v → WP isa rest v Q) :
    WP isa (.seq (.block (estimate r)) (.seq (clearT t) (.seq (prodT m t) rest))) s Q := by
  have := h.wle
  have fm := h.arr_fit hm
  have ft := h.arr_fit ht
  have g0 := h.fit64 (j := 0) (by omega)
  have gm := h.fit64 hm
  simp only [S] at fm ft
  rw [WP.seq_iff, ← List.append_nil (estimate r)]
  refine estimate_ok h hr hN h16 hdw hJ hj hY hYM hz hP hMP hD hDn hV
    fun t1 q hq1 Elo Ehi _ K1 W1 R1 => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (clearT_ok W1 ht ht0 hN (by
    rw [keep_val K1 (a := 0) (Nat.le_refl _) (by simp only [S]; omega) (by simp) (fit := g0)]; exact hz0))
    fun t2 ⟨W2, K2, Z2, R2⟩ => ?_
  rw [WP.seq_iff]
  have M2 : val32 t2.mem (State.addr B) (arr w m) (w / 2) = M := by
    rw [keep_val K2 (a := m) (Nat.le_refl _) (by simp only [S]; omega) (by simpa using hmt.symm) (fit := gm),
      keep_val K1 (a := m) (Nat.le_refl _) (by simp only [S]; omega) (by simp) (fit := gm)]
    exact hM
  have Zt : val32 t2.mem (State.addr B) (arr w t) (w / 2) = 0 := by
    have := Z2; rw [val32_succ] at this; omega
  have s16 : slot t2.mem B 16 = w := by
    rw [K2.slot (by decide) (by simp), K1.slot (by decide) (by decide)]; exact h16
  have sQ2 : slot t2.mem B sQ = q := by rw [K2.slot (by decide) (by simp)]; exact hq1
  refine WP.mono (prodT_ok W2 hm ht hmt hN s16 (by omega) Zt sQ2) fun t3 ⟨W3, K3, T3, R3⟩ => ?_
  refine k t3 q Elo Ehi (by rw [T3, M2]) ((K1.mono).trans ((K2.mono).trans K3.mono)) W3 ?_
  exact rest_back h W3 (ws := divRegs ++ [.r7, .r8, .r9])
    ((R1.mono (by decide)).trans ((R2.mono (by decide)).trans (R3.mono (by decide))))

/-- The bytes a step's second half may change. -/
abbrev stepBRanges (w r t u j : Nat) : List (Nat × Nat) :=
  ranges w [t, u] [sC, sJ] ++ [(arr w r + 4 * j, 4 * (w / 2 + 1))]

/-- A step's second half: `[u] := Y - [t]` with its borrow, `[t] := -M` or zero by it,
the window `:= [u] - [t]`, `Y mod M` for `[t] = q̂ M`, and the window's offset a word down. -/
theorem stepB_ok {s : State} {B : BitVec 32} {Z w N r t nm u j : Nat} (h : Ws s B Z w N) (hr : r < N)
    (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u) (htu : t ≠ u)
    (htn : t ≠ nm) (hnu : nm ≠ u) (ht0 : t ≠ 0) (hu0 : u ≠ 0) (hJ : slot s.mem B sJ = 4 * j) (hj : j + w / 2 ≤ w)
    {Y M q : Nat} (hY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y) (hM0 : 0 < M)
    (hMW : M ≤ 2 ^ (32 * (w / 2 + 1))) (hge : Y / M ≤ q) (hle : q ≤ Y / M + 1)
    (hT : val32 s.mem (State.addr B) (arr w t) (w / 2 + 1) = q * M)
    (hz0 : val32 s.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0)
    (hnm' : val32 s.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M) :
    WP isa (.seq (subT r t u) (.seq (selT t nm) (.seq (subBack r t u)
        (.block [.ldr .r0 .r8 sJ, .subs .r0 .r0 (.imm 4), .str .r0 .r8 sJ])))) s fun v =>
      Ws v B Z w N ∧ val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y % M ∧
      slot v.mem B sJ = (BitVec.ofNat 32 (4 * j) - 4).toNat ∧
      Outs (State.addr B) (stepBRanges w r t u j) s.mem v.mem ∧ Rest divRegs s v := by
  have := h.wle
  have nw := h.nowrap
  have fr := h.arr_fit hr
  have hz' := h.hdr_le
  have g0 := h.fit64 (j := 0) (by omega)
  have gn := h.fit64 hnm
  have gu := h.fit64 hu
  have r0 : 160 ≤ arr w r := Nat.le_add_right _ _
  simp only [S] at fr
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  rw [WP.seq_iff]
  refine WP.mono (subT_ok h hr ht hu hN hru htu hJ hj) fun t4 ⟨W4, K4, E4, c4, R4⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (selT_ok W4 ht hnm hN ht0 htn c4) fun t5 ⟨W5, K5, E5, R5⟩ => ?_
  have J5 : slot t5.mem B sJ = 4 * j := by
    rw [K5.slot (by decide) (by simp), K4.slot (by decide) (by decide)]; exact hJ
  rw [WP.seq_iff]
  refine WP.mono (subBack_ok W5 hr ht hu hN hru hrt J5 hj) fun t6 ⟨W6, O6, E6, R6⟩ => ?_
  have J6 : slot t6.mem B sJ = 4 * j := by
    simp only [slot]; rw [O6.w32 (Or.inl (by simp only [sJ]; omega)) (by simp only [sJ]; omega)]; exact J5
  have aJ : State.addr (B + BitVec.ofNat 32 sJ) = off (State.addr B) sJ := h.addr (by simp only [sJ]; omega)
  have rJ : InRegions (t6.rd ++ t6.wr) (off (State.addr B) sJ) 4 := W6.read (by simp only [sJ]; omega)
  have wJ : InRegions t6.wr (off (State.addr B) sJ) 4 := W6.write (by simp only [sJ]; omega)
  have vJ : t6.mem.readW (off (State.addr B) sJ) 32 = BitVec.ofNat 32 (4 * j) := by
    rw [← J6]; exact (ofNat_toNat32 _).symm
  refine WP.mono (WP.keep [.r0] (Q := fun v =>
      v.mem = t6.mem.writeW (off (State.addr B) sJ) (BitVec.ofNat 32 (4 * j) - 4)) (by
    krun [W6.r8, aJ, rJ, wJ, vJ]) (by decide)) fun t7 ⟨m7, R7⟩ => ?_
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  -- The values.
  have z4 : val32 t4.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0 := by
    rw [keep_val K4 (a := 0) (Nat.le_refl _) (by simp only [S]; omega) (by simpa using hu0) (fit := g0)]
    exact hz0
  have n4 : val32 t4.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M := by
    rw [keep_val K4 (a := nm) (Nat.le_refl _) (by simp only [S]; omega) (by simpa using hnu.symm) (fit := gn)]
    exact hnm'
  have T5 : val32 t5.mem (State.addr B) (arr w t) (w / 2 + 1) =
      if slot t4.mem B sC = 0 then 0 else 2 ^ (32 * (w / 2 + 1)) - M := by rw [E5, z4, n4]
  have U5 : val32 t5.mem (State.addr B) (arr w u) (w / 2 + 1) = val32 t4.mem (State.addr B) (arr w u) (w / 2 + 1) :=
    keep_val K5 (a := u) (Nat.le_refl _) (by simp only [S]; omega) (by simpa using htu) (fit := gu)
  rw [hT, hY] at E4
  rw [T5, U5] at E6
  have V := step_math hM0 hMW hge hle (val32_lt _ _ _ _) c4 E4 (val32_lt _ _ _ _) E6
  have win7 : val32 t7.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) =
      val32 t6.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) := by
    rw [m7]; exact Outside.val32 (writeW32_outside _ _ _ (by simp only [sJ]; omega)) (Or.inr (by simp only [sJ]; omega))
      (by omega)
  refine ⟨W6.of (by rw [R7.gpr _ (by decide)]) (by rw [R7.gpr _ (by decide)]) (by rw [R7.gpr _ (by decide)]) R7.wr,
    by rw [win7, V], by simp only [slot]; rw [m7, w32_write_self], ?_, ?_⟩
  · have F4 : Outs (State.addr B) (stepBRanges w r t u j) s.mem t4.mem :=
      Outs.mono (K4.mono (js' := [t, u]) (ds' := [sC, sJ])) fun x hx => List.mem_append_left _ hx
    have F5 : Outs (State.addr B) (stepBRanges w r t u j) t4.mem t5.mem :=
      Outs.mono (K5.mono (js' := [t, u]) (ds' := [sC, sJ])) fun x hx => List.mem_append_left _ hx
    have F6 : Outs (State.addr B) (stepBRanges w r t u j) t5.mem t6.mem := Outs.of_outside O6 (by simp)
    have F7 : Outs (State.addr B) (stepBRanges w r t u j) t6.mem t7.mem := by
      rw [m7]
      exact Outs.mono ((keep_write (B := B) (w := w) (js := [t, u]) (ds := [sC, sJ]) t6.mem _ (by simp)
        (by simp only [sJ]; omega))) fun x hx => List.mem_append_left _ hx
    exact ((F4.trans F5).trans F6).trans F7
  · exact (R4.mono (by decide)).trans ((R5.mono (by decide)).trans ((R6.mono (by decide)).trans (R7.mono (by decide))))

/-- The bytes a step may change: `[t]`, `[u]`, its header words and the window. -/
abbrev stepRanges (w r t u j : Nat) : List (Nat × Nat) :=
  ranges w [t, u] [sMk, sQ, sU0, sU2, sC, sJ] ++ [(arr w r + 4 * j, 4 * (w / 2 + 1))]

/-- `step r m t nm u`: the window `Y < 2^32 M` at word `j` of `[r]` `:= Y mod M`, for
`M = [m]` of `w / 2` words normalized by `P = 2^z` (`d`, `d₁`, `v` its top words and
reciprocal), `[0]` zero and `[nm] = -M`; the window's offset a word down. -/
theorem step_ok {s : State} {B : BitVec 32} {Z w N r m t nm u j z : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hm : m < N) (ht : t < N) (hnm : nm < N) (hu : u < N) (hN : N ≤ 256) (hrt : r ≠ t) (hru : r ≠ u)
    (htu : t ≠ u) (hmt : m ≠ t) (htn : t ≠ nm) (hnu : nm ≠ u) (ht0 : t ≠ 0) (hu0 : u ≠ 0)
    (h16 : slot s.mem B 16 = w) (hdw : 3 ≤ w / 2) (hJ : slot s.mem B sJ = 4 * j) (hj : j + w / 2 ≤ w)
    {Y M : Nat} (hY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y)
    (hM : val32 s.mem (State.addr B) (arr w m) (w / 2) = M) (hYM : Y < M * 2 ^ 32)
    (hz : z ≤ 31) (hP : slot s.mem B sP = 2 ^ z) (hMP : M * 2 ^ z < 2 ^ (32 * (w / 2)))
    (hD : slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2)))
    (hDn : 2 ^ 31 ≤ slot s.mem B sD) (hV : slot s.mem B sV = (2 ^ 64 - 1) / slot s.mem B sD - 2 ^ 32)
    (hz0 : val32 s.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0)
    (hnm' : val32 s.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M) :
    WP isa (step r m t nm u) s fun v =>
      Ws v B Z w N ∧ val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y % M ∧
      slot v.mem B sJ = (BitVec.ofNat 32 (4 * j) - 4).toNat ∧
      Outs (State.addr B) (stepRanges w r t u j) s.mem v.mem ∧ Rest divRegs s v := by
  have := h.wle
  have fr := h.arr_fit hr
  have gr := h.fit64 hr
  have g0 := h.fit64 (j := 0) (by omega)
  have gn := h.fit64 hnm
  simp only [S] at fr
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun e => by
    rw [e, Nat.zero_mul, Nat.zero_div] at hD
    have := Nat.mul_le_mul_right (2 ^ 32) hDn; omega
  have hMW : M ≤ 2 ^ (32 * (w / 2 + 1)) := by
    have h1 : M ≤ M * 2 ^ z := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (32 * (w / 2)) ≤ 2 ^ (32 * (w / 2 + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  rw [step]
  simp only [VG.Impl.Rsa.Arm.Keys.seqs]
  refine stepA_ok h hr hm ht hN hmt ht0 h16 hdw hJ hj hY hM hYM hz hP hMP hD hDn hV hz0
    fun v q hge hle hT K W R => ?_
  have Jv : slot v.mem B sJ = 4 * j := by rw [K.slot (by decide) (by decide)]; exact hJ
  have Yv : val32 v.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y := by
    rw [keep_val K (a := r) (by omega) (by simp only [S]; omega) (by simpa using hrt.symm) (fit := gr)]; exact hY
  have Zv : val32 v.mem (State.addr B) (arr w 0) (w / 2 + 1) = 0 := by
    rw [keep_val K (a := 0) (Nat.le_refl _) (by simp only [S]; omega) (by simpa using ht0) (fit := g0)]; exact hz0
  have Nv : val32 v.mem (State.addr B) (arr w nm) (w / 2 + 1) = 2 ^ (32 * (w / 2 + 1)) - M := by
    rw [keep_val K (a := nm) (Nat.le_refl _) (by simp only [S]; omega) (by simpa using htn) (fit := gn)]; exact hnm'
  refine WP.mono (stepB_ok W hr ht hnm hu hN hrt hru htu htn hnu ht0 hu0 Jv hj Yv hM0 hMW hge hle hT Zv Nv)
    fun x ⟨Wx, Vx, Jx, Fx, Rx⟩ => ⟨Wx, Vx, Jx, ?_, R.trans Rx⟩
  have F : Outs (State.addr B) (stepRanges w r t u j) s.mem v.mem :=
    Outs.mono (K.mono (js' := [t, u]) (ds' := [sMk, sQ, sU0, sU2, sC, sJ])) fun x hx => List.mem_append_left _ hx
  refine F.trans (Outs.mono Fx fun x hx => ?_)
  simp only [stepBRanges, stepRanges, ranges, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  rcases hx with (⟨y, hy, rfl⟩ | ⟨d, hd, rfl⟩) | hx
  · exact .inl (.inl ⟨y, hy, rfl⟩)
  · exact .inl (.inr ⟨d, by rcases hd with rfl | rfl <;> simp, rfl⟩)
  · exact .inr hx

end VG.Proof.Rsa.Arm.KeyDiv
