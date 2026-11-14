module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.Divstep.Word32Def
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Ops
public import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Divstep.Word32Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Divstep.Red30
-- separate module: the divsteps' word kernel, which edits of the batches' and the end's proofs in `InvLoop` do not rebuild

/-! # The divsteps of a batch of `inverse` on ARMv7

`divsteps_ok`: the window of `δ`, `f` and `g` loaded, 30 divsteps (`wstepI` is `wstep`), and the batch's
matrix `(u, v, q, r)` stored (`Mat`), for the passes over `(f, g)` and `(d, e)` (`Inv/Pass.lean`).
-/

@[expose] public section

/-! ## The divsteps of `inverse` on ARMv7: `wstepI` is `wstep` -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rsa.Arm.Keys VG.Proof.Divstep.W32
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem sub_shl1 (x : BitVec 32) : x - (x <<< 1) = 0 - x := by
  rw [shl1]; bv_omega

/-- The window's words in a state. -/
def win (s : State) : WSt :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, s.gpr .r4, s.gpr .r5, s.gpr .r10⟩

/-- The registers the divsteps write. -/
abbrev wRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr]

theorem wbody_run (s : State) : ∃ t, runBlock isa wbody s = some t ∧ win t = wstep (win s) ∧
    t.gpr .r6 = s.gpr .r6 - 1 ∧ t.z = ((s.gpr .r6 - 1) &&& 31 == 0) ∧ Rest wRegs s t ∧ t.mem = s.mem := by
  have e1 : encodable 1 = true := by decide
  have e2 : encodable 2 = true := by decide
  have e31 : encodable 31 = true := by decide
  have e0 : encodable 0 = true := by decide
  have s1 : (1 ≤ 1 ∧ 1 ≤ 31) = True := by decide
  have s31 : (1 ≤ 31 ∧ 31 ≤ 31) = True := by decide
  obtain ⟨t, run⟩ : ∃ t, runBlock isa wbody s = some t := ⟨_, by
    simp only [wbody, wstepI, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      reduceExec, Op2.eval, Option.map_some, e0, e1, e2, e31, s1, s31, ↓reduceIte]
    exact rfl⟩
  have ht := run
  simp only [wbody, wstepI, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    reduceExec, Op2.eval, Option.map_some, e0, e1, e2, e31, s1, s31, ↓reduceIte, Option.some.injEq] at ht
  subst ht
  refine ⟨_, run, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl⟩
  · simp only [win, wstep, subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte, sub_shl1]
  · simp only [subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
  · simp only [subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte]
    have z0 : ∀ x : BitVec 32, x - (0 : BitVec 32) = x := fun x => by simp
    rw [z0]
  · simp only [wRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h10, h11, h12, hl⟩ := hr
    simp only [subFlags, gpr_setReg, h0, h1, h2, h3, h4, h5, h6, h10, h11, h12, hl, ↓reduceIte]

theorem ofNat_sub_one_and31 {b j : Nat} (hj : j < 30) (hb : 32 * b + 30 < 2 ^ 32) :
    (BitVec.ofNat 32 (32 * b + 30 - j) - 1) = BitVec.ofNat 32 (32 * b + 30 - (j + 1)) ∧
    ((BitVec.ofNat 32 (32 * b + 30 - (j + 1)) &&& 31 == 0) = decide (j + 1 = 30)) := by
  constructor
  · rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hj]), Nat.sub_sub]
  · have e : BitVec.ofNat 32 (32 * b + 30 - (j + 1)) &&& 31 = BitVec.ofNat 32 (29 - j) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb]),
        Nat.mod_eq_of_lt (by omega_using []), show (31 : BitVec 32).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega_using [hj]
    rw [e, ofNat_beq_zero (by omega_using [])]
    simp only [decide_eq_decide]; omega_using [hj]

/-- The 30 divsteps of a batch, from `32 b + 30` in `r6` to `32 b`. -/
theorem wloop_ok (s : State) {b : Nat} (hb : 32 * b + 30 < 2 ^ 32)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 (32 * b + 30)) :
    WP isa (.loop (.block wbody) .ne) s fun t => win t = wsteps 30 (win s) ∧
      t.gpr .r6 = BitVec.ofNat 32 (32 * b) ∧ Rest wRegs s t ∧ t.mem = s.mem := by
  refine WP.loop (M := isa) (fun n t => ∃ j, j + n = 30 ∧ 0 < n ∧ win t = wsteps j (win s) ∧
      t.gpr .r6 = BitVec.ofNat 32 (32 * b + 30 - j) ∧ Rest wRegs s t ∧ t.mem = s.mem) ?_ 30 s
    ⟨0, rfl, by decide, rfl, by simpa using h6, Rest.refl _ _, rfl⟩
  rintro n t ⟨j, hjn, hn, hw, hr6, hr, hm⟩
  obtain ⟨u, run, w', r6', z', ru, mu⟩ := wbody_run t
  refine WP.of_runBlock ⟨u, run, ?_⟩
  have e := ofNat_sub_one_and31 (j := j) (by omega_using [hjn, hn]) hb
  rw [hr6, e.1] at r6'
  rw [hr6, e.1, e.2] at z'
  have wu : win u = wsteps (j + 1) (win s) := by rw [w', hw, wsteps_succ]
  by_cases hd : j + 1 = 30
  · left
    refine ⟨by change some (!u.z) = some false; simp [z', hd], ?_, ?_, hr.trans ru, by rw [mu, hm]⟩
    · rw [wu, hd]
    · rw [r6']; congr 1; omega_using [hd]
  · right
    refine ⟨by change some (!u.z) = some true; simp [z', hd], n - 1, by omega_using [hn], j + 1, by omega_using [hjn, hn], by omega_using [hjn, hn, hd],
      wu, r6', hr.trans ru, by rw [mu, hm]⟩

end VG.Proof.Rsa.Arm.Inv

/-! ## The divsteps of a batch of `inverse` on ARMv7: the window loaded, 30 steps, and stored -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.Divstep.W32
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm

/-- The word at byte `d` of the working space. -/
abbrev bw (m : Mem) (B : BitVec 32) (d : Nat) : BitVec 32 := m.readW (off (State.addr B) d) 32

/-- The window a batch starts from. -/
def win0 (m : Mem) (B : BitVec 32) (W : Nat) : WSt :=
  ⟨bw m B sOdd, bw m B (arr W bF), bw m B (arr W bG), 1, 0, 0, 1⟩

theorem Gk.slotAddr {s : State} {B : BitVec 32} {Z W k N d : Nat} (h : Gk s B Z W k N) (hd : d < Z) :
    State.addr (s.gpr .r8 + BitVec.ofNat 32 d) = off (State.addr B) d := by
  rw [h.r8]; exact h.addr hd

theorem Gk.hdr_le {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) : hdr ≤ Z :=
  Nat.le_trans (Nat.le_add_right _ _) h.fits

theorem wload_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (hN : 8 ≤ N)
    {b : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 (32 * b)) :
    WP isa (.block wload) s fun t => win t = win0 s.mem B W ∧ t.gpr .r6 = BitVec.ofNat 32 (32 * b + 30) ∧
      t.mem = s.mem ∧ Rest wRegs s t ∧ Gk t B Z W k N := by
  have hz := h.hdr_le
  have fF := h.arr_fit (j := bF) (Nat.lt_of_lt_of_le (by decide) hN)
  have fG := h.arr_fit (j := bG) (Nat.lt_of_lt_of_le (by decide) hN)
  have hS : S W = 4 * (W + 2) := rfl
  simp only [wload, List.append_assoc, List.cons_append, List.nil_append]
  refine h.ptr_ok (r := .r12) (j := bF) (by decide) (by decide) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldr (by decide) (h1.arrAddr (j := bF) (Nat.lt_of_lt_of_le (by decide) hN) (d := 0)
    (by simpa using p1) (by omega_using [hS])) (h1.read (by omega_using [fF, hS])) fun s2 u2 => ?_
  have h2 : Gk s2 B Z W k N := h1.rest (u2.rest (ws := [.r1]) (by simp))
  refine h2.ptr_ok (r := .r12) (j := bG) (by decide) (by decide) fun s3 p3 r3 m3 h3 => ?_
  refine wp_ldr (by decide) (h3.arrAddr (j := bG) (Nat.lt_of_lt_of_le (by decide) hN) (d := 0)
    (by simpa using p3) (by omega_using [hS])) (h3.read (by omega_using [fG, hS])) fun s4 u4 => ?_
  have h4 : Gk s4 B Z W k N := h3.rest (u4.rest (ws := [.r2]) (by simp))
  have hsl : sOdd + 4 ≤ hdr := by decide
  refine wp_ldr (a := off (State.addr B) sOdd) (by decide) (h4.slotAddr (by omega_using [hz, hsl])) (h4.read (by omega_using [hz, hsl]))
    fun s5 u5 => ?_
  refine wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_mov (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_mov (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_mov (op2_imm (by decide)) fun s9 u9 => ?_
  refine wp_dp (op2_imm (by decide)) fun t u10 => WP.block_nil ?_
  have mt : t.mem = s.mem := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, m3, u2.mem, m1]
  have rt : Rest wRegs s t := (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((r3.mono (by simp)).trans
    ((u4.rest (by simp)).trans ((u5.rest (by simp)).trans ((u6.rest (by simp)).trans ((u7.rest (by simp)).trans
      ((u8.rest (by simp)).trans ((u9.rest (by simp)).trans (u10.rest (by simp))))))))))
  refine ⟨?_, ?_, mt, rt, h.rest rt⟩
  · simp only [win, win0, bw, Nat.add_zero] at u2 u4 ⊢
    rw [u10.other .r0 (by decide), u9.other .r0 (by decide), u8.other .r0 (by decide), u7.other .r0 (by decide),
      u6.other .r0 (by decide), u5.gpr, u4.mem, m3, u2.mem, m1,
      u10.other .r1 (by decide), u9.other .r1 (by decide), u8.other .r1 (by decide), u7.other .r1 (by decide),
      u6.other .r1 (by decide), u5.other .r1 (by decide), u4.other .r1 (by decide), r3.gpr .r1 (by decide), u2.gpr,
      m1,
      u10.other .r2 (by decide), u9.other .r2 (by decide), u8.other .r2 (by decide), u7.other .r2 (by decide),
      u6.other .r2 (by decide), u5.other .r2 (by decide), u4.gpr, m3, u2.mem, m1,
      u10.other .r3 (by decide), u9.other .r3 (by decide), u8.other .r3 (by decide), u7.other .r3 (by decide),
      u6.gpr, u10.other .r4 (by decide), u9.other .r4 (by decide), u8.other .r4 (by decide), u7.gpr,
      u10.other .r5 (by decide), u9.other .r5 (by decide), u8.gpr, u10.other .r10 (by decide), u9.gpr]
  · rw [u10.gpr, dpVal, u9.other .r6 (by decide), u8.other .r6 (by decide), u7.other .r6 (by decide),
      u6.other .r6 (by decide), u5.other .r6 (by decide), u4.other .r6 (by decide), r3.gpr .r6 (by decide),
      u2.other .r6 (by decide), r1.gpr .r6 (by decide), h6, BitVec.ofNat_add]; rfl

theorem bw_write_other (m : Mem) (B : BitVec 32) {d e : Nat} (v : BitVec 32) (h : e + 4 ≤ d ∨ d + 4 ≤ e)
    (fit : d + 4 ≤ 2 ^ 64) (fit' : e + 4 ≤ 2 ^ 64) :
    bw (m.writeW (off (State.addr B) d) v) B e = bw m B e := by
  have := (writeW32_outside m (State.addr B) (d := d) v fit).w32 (d := e) h fit'
  exact BitVec.eq_of_toNat_eq this

theorem bw_write_self (m : Mem) (B : BitVec 32) (d : Nat) (v : BitVec 32) :
    bw (m.writeW (off (State.addr B) d) v) B d = v := BitVec.eq_of_toNat_eq (w32_write_self m _ d v)

theorem wstore_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (hN : 8 ≤ N) :
    WP isa (.block wstore) s fun t => Keep B W [1, 3] [sOdd] s.mem t.mem ∧
      bw t.mem B sOdd = s.gpr .r0 ∧ bw t.mem B (arr W 1) = s.gpr .r3 ∧ bw t.mem B (arr W 1 + 4) = s.gpr .r4 ∧
      bw t.mem B (arr W 1 + 8) = s.gpr .r5 ∧ bw t.mem B (arr W 3) = s.gpr .r10 ∧ Rest [.r12] s t ∧
      Gk t B Z W k N := by
  have hz := h.hdr_le
  have f1 := h.arr_fit (j := 1) (by omega_using [hN])
  have f3 := h.arr_fit (j := 3) (by omega_using [hN])
  have a13 := arr_end (w := W) (show 1 < 3 by decide)
  have h0 : hdr ≤ arr W 1 := Nat.le_add_right _ _
  have hN64 := h.nowrap
  have hS : S W = 4 * (W + 2) := rfl
  have hW : 1 ≤ W := Nat.le_trans h.kpos h.kle
  simp only [wstore, cU, cV, cQ, cR, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_str (a := off (State.addr B) sOdd) (by decide) (h.slotAddr (by simp only [sOdd, hdr] at *; omega_using [hz]))
    (h.write (by simp only [sOdd, hdr] at *; omega_using [hz])) fun s1 u1 => ?_
  have h1 : Gk s1 B Z W k N := h.rest (u1.rest [])
  refine h1.ptr_ok (r := .r12) (j := 1) (by decide) (by decide) fun s2 p2 r2 m2 h2 => ?_
  refine wp_str (by decide) (h2.arrAddr (r := .r12) (o := 0) (j := 1) (by omega_using [hN]) (d := 0) (by simpa using p2)
    (by omega_using [hS])) (h2.write (by omega_using [f1, hS])) fun s3 u3 => ?_
  have h3 : Gk s3 B Z W k N := h2.rest (u3.rest [])
  have p3 : s3.gpr .r12 = B + BitVec.ofNat 32 (arr W 1 + 0) := by rw [u3.gpr]; simpa using p2
  refine wp_str (by decide) (h3.arrAddr (r := .r12) (o := 4) (j := 1) (by omega_using [hN]) (d := 0) p3 (by omega_using [hS]))
    (h3.write (by omega_using [f1, hS])) fun s4 u4 => ?_
  have h4 : Gk s4 B Z W k N := h3.rest (u4.rest [])
  have p4 : s4.gpr .r12 = B + BitVec.ofNat 32 (arr W 1 + 0) := by rw [u4.gpr]; exact p3
  refine wp_str (by decide) (h4.arrAddr (r := .r12) (o := 8) (j := 1) (by omega_using [hN]) (d := 0) p4 (by omega_using [hS, hW]))
    (h4.write (by omega_using [f3, a13, hS])) fun s5 u5 => ?_
  have h5 : Gk s5 B Z W k N := h4.rest (u5.rest [])
  refine h5.ptr_ok (r := .r12) (j := 3) (by decide) (by decide) fun s6 p6 r6 m6 h6 => ?_
  refine wp_str (by decide) (h6.arrAddr (r := .r12) (o := 0) (j := 3) (by omega_using [hN]) (d := 0) (by simpa using p6)
    (by omega_using [hS])) (h6.write (by omega_using [f3, hS])) fun t u7 => WP.block_nil ?_
  simp only [Nat.add_zero] at u3 u4 u5 u7
  have g : ∀ r, r ≠ .r12 → s6.gpr r = s.gpr r := fun r hr => by
    rw [r6.gpr r (by simpa using hr), u5.gpr, u4.gpr, u3.gpr, r2.gpr r (by simpa using hr), u1.gpr]
  have g4 : ∀ r, r ≠ .r12 → s4.gpr r = s.gpr r := fun r hr => by
    rw [u4.gpr, u3.gpr, r2.gpr r (by simpa using hr), u1.gpr]
  have g3 : ∀ r, r ≠ .r12 → s3.gpr r = s.gpr r := fun r hr => by
    rw [u3.gpr, r2.gpr r (by simpa using hr), u1.gpr]
  have g2 : ∀ r, r ≠ .r12 → s2.gpr r = s.gpr r := fun r hr => by rw [r2.gpr r (by simpa using hr), u1.gpr]
  have ht : t.mem = ((((s.mem.writeW (off (State.addr B) sOdd) (s.gpr .r0)).writeW (off (State.addr B) (arr W 1))
      (s.gpr .r3)).writeW (off (State.addr B) (arr W 1 + 4)) (s.gpr .r4)).writeW
      (off (State.addr B) (arr W 1 + 8)) (s.gpr .r5)).writeW (off (State.addr B) (arr W 3)) (s.gpr .r10) := by
    rw [u7.mem, m6, u5.mem, u4.mem, u3.mem, m2, u1.mem, g .r10 (by decide), g4 .r5 (by decide),
      g3 .r4 (by decide), g2 .r3 (by decide)]
  have hsO : sOdd + 4 ≤ hdr := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, h.rest (ws := [.r12]) ?_⟩
  · rw [ht]
    generalize s.gpr .r0 = v0
    generalize s.gpr .r3 = v3
    generalize s.gpr .r4 = v4
    generalize s.gpr .r5 = v5
    generalize s.gpr .r10 = v10
    have o1 : ∀ (m : Mem) (v : BitVec 32) (d : Nat) (j : Nat), d + 4 ≤ S W → j ∈ [1, 3] →
        arr W j + d + 4 ≤ 2 ^ 64 →
        Keep B W [1, 3] [sOdd] m (m.writeW (off (State.addr B) (arr W j + d)) v) :=
      fun m v d j hd hj fit => Keep.of_arr (o := j) (d := d) (writeW32_outside m _ v fit) hd hj
    have o1' : ∀ (m : Mem) (v : BitVec 32) (j : Nat), j ∈ [1, 3] → arr W j + 4 ≤ 2 ^ 64 →
        Keep B W [1, 3] [sOdd] m (m.writeW (off (State.addr B) (arr W j)) v) :=
      fun m v j hj fit => o1 m v 0 j (by omega_using [hS]) hj fit
    exact ((((keep_write _ _ (by simp) (by omega_using [hz, hN64, hsO])).trans (o1' _ _ 1 (by simp) (by omega_using [f1, hN64]))).trans
      (o1 _ _ 4 1 (by omega_using [hS]) (by simp) (by omega_using [f1, hN64]))).trans (o1 _ _ 8 1 (by omega_using [hS, hW]) (by simp) (by omega_using [f1, hN64]))).trans
      (o1' _ _ 3 (by simp) (by omega_using [f3, hN64]))
  · rw [ht, bw_write_other _ _ _ (by omega_using [a13, h0, hsO]) (by omega_using [f3, hN64]) (by omega_using [hz, hN64, hsO]), bw_write_other _ _ _ (by omega_using [h0, hsO]) (by omega_using [f1, hN64]) (by omega_using [hz, hN64, hsO]),
      bw_write_other _ _ _ (by omega_using [h0, hsO]) (by omega_using [f1, hN64]) (by omega_using [hz, hN64, hsO]), bw_write_other _ _ _ (by omega_using [h0, hsO]) (by omega_using [f1, hN64]) (by omega_using [hz, hN64, hsO]),
      bw_write_self]
  · rw [ht, bw_write_other _ _ _ (by omega_using [a13, hS]) (by omega_using [f3, hN64]) (by omega_using [f1, hN64]), bw_write_other _ _ _ (by omega_using []) (by omega_using [f1, hN64]) (by omega_using [f1, hN64]),
      bw_write_other _ _ _ (by omega_using []) (by omega_using [f1, hN64]) (by omega_using [f1, hN64]), bw_write_self]
  · rw [ht, bw_write_other _ _ _ (by omega_using [a13, hS]) (by omega_using [f3, hN64]) (by omega_using [f1, hN64]), bw_write_other _ _ _ (by omega_using []) (by omega_using [f1, hN64]) (by omega_using [f1, hN64]),
      bw_write_self]
  · rw [ht, bw_write_other _ _ _ (by omega_using [a13, hS, hW]) (by omega_using [f3, hN64]) (by omega_using [f1, hN64]), bw_write_self]
  · rw [ht, bw_write_self]
  · exact (u1.rest _).trans ((r2.mono (by simp)).trans ((u3.rest _).trans ((u4.rest _).trans ((u5.rest _).trans
      ((r6.mono (by simp)).trans (u7.rest _))))))
  · exact (u1.rest _).trans ((r2.mono (by simp)).trans ((u3.rest _).trans ((u4.rest _).trans ((u5.rest _).trans
      ((r6.mono (by simp)).trans (u7.rest _))))))

/-- A batch's divsteps: the window stored is `wsteps 30` of the one loaded. -/
theorem divsteps_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (hN : 8 ≤ N)
    {b : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 (32 * b)) (hb : 32 * b + 30 < 2 ^ 32) :
    WP isa divsteps s fun t => Gk t B Z W k N ∧ Keep B W [1, 3] [sOdd] s.mem t.mem ∧
      t.gpr .r6 = BitVec.ofNat 32 (32 * b) ∧
      bw t.mem B sOdd = (wsteps 30 (win0 s.mem B W)).D ∧ bw t.mem B (arr W 1) = (wsteps 30 (win0 s.mem B W)).U ∧
      bw t.mem B (arr W 1 + 4) = (wsteps 30 (win0 s.mem B W)).V ∧
      bw t.mem B (arr W 1 + 8) = (wsteps 30 (win0 s.mem B W)).Q ∧
      bw t.mem B (arr W 3) = (wsteps 30 (win0 s.mem B W)).R ∧ Rest wRegs s t := by
  simp only [divsteps, seqs]
  rw [WP.seq_iff]
  refine WP.mono (wload_ok h hN h6) fun s1 ⟨w1, r61, m1, rr1, g1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (wloop_ok s1 hb r61) fun s2 ⟨w2, r62, rr2, m2⟩ => ?_
  have g2 : Gk s2 B Z W k N := g1.rest rr2
  refine WP.mono (wstore_ok g2 hN) fun t ⟨kt, d, u, v, q, r, rt, gt⟩ => ?_
  rw [w1] at w2
  rw [m2, m1] at kt
  refine ⟨gt, kt, by rw [rt.gpr _ (by decide), r62], ?_, ?_, ?_, ?_, ?_,
    (rr1.trans rr2).trans (rt.mono (by simp))⟩
  · rw [d]; exact congrArg WSt.D w2
  · rw [u]; exact congrArg WSt.U w2
  · rw [v]; exact congrArg WSt.V w2
  · rw [q]; exact congrArg WSt.Q w2
  · rw [r]; exact congrArg WSt.R w2

end VG.Proof.Rsa.Arm.Inv

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.Divstep.W32
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm

/-- The words of the matrix in a state. -/
structure Mat (m : Mem) (B : BitVec 32) (W : Nat) (u v q r : Int) : Prop where
  u : bw m B (arr W cU.arr + cU.off) = BitVec.ofInt 32 u
  v : bw m B (arr W cV.arr + cV.off) = BitVec.ofInt 32 v
  q : bw m B (arr W cQ.arr + cQ.off) = BitVec.ofInt 32 q
  r : bw m B (arr W cR.arr + cR.off) = BitVec.ofInt 32 r

theorem Mat.keep {m m' : Mem} {B : BitVec 32} {W : Nat} {u v q r : Int} {js : List Nat} (h : Mat m B W u v q r)
    (k : Keep B W js [] m m') (hj : ∀ j ∈ js, j ≠ 1 ∧ j ≠ 3) (hW : 1 ≤ W) (f1 : arr W 1 + S W ≤ 2 ^ 64)
    (f3 : arr W 3 + S W ≤ 2 ^ 64) : Mat m' B W u v q r := by
  have hS : S W = 4 * (W + 2) := rfl
  have e : ∀ (c : Coef), (c.arr = 1 ∨ c.arr = 3) → c.off + 4 ≤ S W →
      bw m' B (arr W c.arr + c.off) = bw m B (arr W c.arr + c.off) := fun c hc ho => by
    apply BitVec.eq_of_toNat_eq
    have := Keep.aw k (j := c.arr) ho (fun x hx => by rcases hc with h | h <;> rw [h] <;> simp [hj x hx])
      (by rcases hc with h | h <;> rw [h] <;> with_reducible assumption)
    exact this
  exact ⟨by rw [e cU (.inl rfl) (by simp only [cU]; omega_using [hS])]; exact h.u, by rw [e cV (.inl rfl) (by simp only [cV]; omega_using [hS])]; exact h.v,
    by rw [e cQ (.inl rfl) (by simp only [cQ]; omega_using [hW, hS])]; exact h.q, by rw [e cR (.inr rfl) (by simp only [cR]; omega_using [hS])]; exact h.r⟩

/-- Index bounds. -/
macro "ix" : tactic => `(tactic| (simp only [bZ, bA1, bA2, bF, bG, bD, bE, bP, bT1, bT2, cU, cV, cQ, cR]; omega))

theorem word0 (m : Mem) (B : BitVec 32) (W j k : Nat) : aw m B W j 0 = nk m B W j (k + 1) % 2 ^ 32 := by
  simp only [nk, val32]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
  simp only [aw, w32, Nat.add_zero]

end VG.Proof.Rsa.Arm.Inv
