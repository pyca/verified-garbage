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
-- separate module: the divsteps' word kernel and the update's array proofs, which edits of the batches' and the end's proofs in `InvLoop` do not rebuild

/-! # The update of a batch of `inverse` on ARMv7

`update_ok`: from the matrix `(u, v, q, r)` of a batch's divsteps in its words, `f` and `g`
(two's complement in `k + 1` words) become `(u f + v g) / 2^30` and `(q f + r g) / 2^30`, and `d`
and `e` (below `m`) become `d', e' < m` with `2^30 d' ≡ u d + v e` and `2^30 e' ≡ q d + r e`
modulo `m`.
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

theorem wstepI_run (s : State) : ∃ t, runBlock isa wstepI s = some t ∧ win t = wstep (win s) ∧
    (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r10 → r ≠ .r11 →
      r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have e1 : encodable 1 = true := by decide
  have e2 : encodable 2 = true := by decide
  have s1 : (1 ≤ 1 ∧ 1 ≤ 31) = True := by decide
  have s31 : (1 ≤ 31 ∧ 31 ≤ 31) = True := by decide
  obtain ⟨t, run⟩ : ∃ t, runBlock isa wstepI s = some t := ⟨_, by
    simp only [wstepI, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval,
      Option.map_some, e1, e2, s1, s31, ↓reduceIte]
    exact rfl⟩
  have ht := run
  simp only [wstepI, runBlock_cons, runStep_some, runBlock_nil, reduceExec, Op2.eval,
    Option.map_some, e1, e2, s1, s31, ↓reduceIte, Option.some.injEq] at ht
  subst ht
  refine ⟨_, run, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [win, wstep, gpr_setReg, reduceCtorEq, ↓reduceIte, sub_shl1]
  · intro r h0 h1 h2 h3 h4 h5 h10 h11 h12 hl
    simp only [gpr_setReg, h0, h1, h2, h3, h4, h5, h10, h11, h12, hl, ↓reduceIte]

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
      BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), Nat.sub_sub]
  · have e : BitVec.ofNat 32 (32 * b + 30 - (j + 1)) &&& 31 = BitVec.ofNat 32 (29 - j) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega), show (31 : BitVec 32).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [e, ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]; omega

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
  have e := ofNat_sub_one_and31 (j := j) (by omega) hb
  rw [hr6, e.1] at r6'
  rw [hr6, e.1, e.2] at z'
  have wu : win u = wsteps (j + 1) (win s) := by rw [w', hw, wsteps_succ]
  by_cases hd : j + 1 = 30
  · left
    refine ⟨by change some (!u.z) = some false; simp [z', hd], ?_, ?_, hr.trans ru, by rw [mu, hm]⟩
    · rw [wu, hd]
    · rw [r6']; congr 1; omega
  · right
    refine ⟨by change some (!u.z) = some true; simp [z', hd], n - 1, by omega, j + 1, by omega, by omega,
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
    (by simpa using p1) (by omega)) (h1.read (by omega)) fun s2 u2 => ?_
  have h2 : Gk s2 B Z W k N := h1.rest (u2.rest (ws := [.r1]) (by simp))
  refine h2.ptr_ok (r := .r12) (j := bG) (by decide) (by decide) fun s3 p3 r3 m3 h3 => ?_
  refine wp_ldr (by decide) (h3.arrAddr (j := bG) (Nat.lt_of_lt_of_le (by decide) hN) (d := 0)
    (by simpa using p3) (by omega)) (h3.read (by omega)) fun s4 u4 => ?_
  have h4 : Gk s4 B Z W k N := h3.rest (u4.rest (ws := [.r2]) (by simp))
  have hsl : sOdd + 4 ≤ hdr := by decide
  refine wp_ldr (a := off (State.addr B) sOdd) (by decide) (h4.slotAddr (by omega)) (h4.read (by omega))
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
  have f1 := h.arr_fit (j := 1) (by omega)
  have f3 := h.arr_fit (j := 3) (by omega)
  have a13 := arr_end (w := W) (show 1 < 3 by decide)
  have h0 : hdr ≤ arr W 1 := Nat.le_add_right _ _
  have hN64 := h.nowrap
  have hS : S W = 4 * (W + 2) := rfl
  have hW : 1 ≤ W := Nat.le_trans h.kpos h.kle
  simp only [wstore, cU, cV, cQ, cR, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_str (a := off (State.addr B) sOdd) (by decide) (h.slotAddr (by simp only [sOdd, hdr] at *; omega))
    (h.write (by simp only [sOdd, hdr] at *; omega)) fun s1 u1 => ?_
  have h1 : Gk s1 B Z W k N := h.rest (u1.rest [])
  refine h1.ptr_ok (r := .r12) (j := 1) (by decide) (by decide) fun s2 p2 r2 m2 h2 => ?_
  refine wp_str (by decide) (h2.arrAddr (r := .r12) (o := 0) (j := 1) (by omega) (d := 0) (by simpa using p2)
    (by omega)) (h2.write (by omega)) fun s3 u3 => ?_
  have h3 : Gk s3 B Z W k N := h2.rest (u3.rest [])
  have p3 : s3.gpr .r12 = B + BitVec.ofNat 32 (arr W 1 + 0) := by rw [u3.gpr]; simpa using p2
  refine wp_str (by decide) (h3.arrAddr (r := .r12) (o := 4) (j := 1) (by omega) (d := 0) p3 (by omega))
    (h3.write (by omega)) fun s4 u4 => ?_
  have h4 : Gk s4 B Z W k N := h3.rest (u4.rest [])
  have p4 : s4.gpr .r12 = B + BitVec.ofNat 32 (arr W 1 + 0) := by rw [u4.gpr]; exact p3
  refine wp_str (by decide) (h4.arrAddr (r := .r12) (o := 8) (j := 1) (by omega) (d := 0) p4 (by omega))
    (h4.write (by omega)) fun s5 u5 => ?_
  have h5 : Gk s5 B Z W k N := h4.rest (u5.rest [])
  refine h5.ptr_ok (r := .r12) (j := 3) (by decide) (by decide) fun s6 p6 r6 m6 h6 => ?_
  refine wp_str (by decide) (h6.arrAddr (r := .r12) (o := 0) (j := 3) (by omega) (d := 0) (by simpa using p6)
    (by omega)) (h6.write (by omega)) fun t u7 => WP.block_nil ?_
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
      fun m v j hj fit => o1 m v 0 j (by omega) hj fit
    exact ((((keep_write _ _ (by simp) (by omega)).trans (o1' _ _ 1 (by simp) (by omega))).trans
      (o1 _ _ 4 1 (by omega) (by simp) (by omega))).trans (o1 _ _ 8 1 (by omega) (by simp) (by omega))).trans
      (o1' _ _ 3 (by simp) (by omega))
  · rw [ht, bw_write_other _ _ _ (by omega) (by omega) (by omega), bw_write_other _ _ _ (by omega) (by omega) (by omega),
      bw_write_other _ _ _ (by omega) (by omega) (by omega), bw_write_other _ _ _ (by omega) (by omega) (by omega),
      bw_write_self]
  · rw [ht, bw_write_other _ _ _ (by omega) (by omega) (by omega), bw_write_other _ _ _ (by omega) (by omega) (by omega),
      bw_write_other _ _ _ (by omega) (by omega) (by omega), bw_write_self]
  · rw [ht, bw_write_other _ _ _ (by omega) (by omega) (by omega), bw_write_other _ _ _ (by omega) (by omega) (by omega),
      bw_write_self]
  · rw [ht, bw_write_other _ _ _ (by omega) (by omega) (by omega), bw_write_self]
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

/-- The arrays a batch writes. -/
abbrev updArrs : List Nat := [bF, bG, bD, bE, bT1, bT2, bA1, bA2]
abbrev deArrs : List Nat := [bD, bE, bT1, bT2, bA1, bA2]
abbrev fgArrs : List Nat := [bF, bG, bT1, bT2, bA1, bA2]

theorem top_bit (m : Mem) (B : BitVec 32) (W j k : Nat) :
    (2 ^ 31 * 2 ^ (32 * k) ≤ nk m B W j (k + 1) ↔ 2 ^ 31 ≤ aw m B W j (4 * k)) := by
  have e := val32_succ m (State.addr B) (arr W j) k
  have l := val32_lt m (State.addr B) (arr W j) k
  have t := (m.readW (off (State.addr B) (arr W j + 4 * k)) 32).isLt
  change nk m B W j (k + 1) = nk m B W j k + 2 ^ (32 * k) * aw m B W j (4 * k) at e
  change nk m B W j k < 2 ^ (32 * k) at l
  rw [e]
  generalize 2 ^ (32 * k) = P at *
  generalize aw m B W j (4 * k) = x at *
  constructor
  · intro h
    by_contra hx
    have : P * x ≤ P * (2 ^ 31 - 1) := Nat.mul_le_mul_left _ (by omega)
    have : P * (2 ^ 31 - 1) + P = 2 ^ 31 * P := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm P]; have : P ≤ 2 ^ 31 * P := Nat.le_mul_of_pos_left _ (by decide)
      omega
    omega
  · intro h
    have : 2 ^ 31 * P ≤ P * x := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ h
    omega

theorem sgn_of {m : Mem} {B : BitVec 32} {W : Nat} {c : Coef} {x : Int}
    (hw : bw m B (arr W c.arr + c.off) = BitVec.ofInt 32 x) (hx : |x| ≤ 2 ^ 30) : (sgnC m B W c ↔ x < 0) := by
  simp only [sgnC, aw, w32]
  change 2 ^ 31 ≤ (bw m B (arr W c.arr + c.off)).toNat ↔ _
  rw [hw]; exact small_sign hx

theorem abs_of {m : Mem} {B : BitVec 32} {W : Nat} {c : Coef} {x : Int}
    (hw : bw m B (arr W c.arr + c.off) = BitVec.ofInt 32 x) (hx : |x| ≤ 2 ^ 30) : absC m B W c = x.natAbs := by
  simp only [absC]
  change (bw m B (arr W c.arr + c.off)).toInt.natAbs = _
  rw [hw]; exact small_abs hx

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
  exact ⟨by rw [e cU (.inl rfl) (by simp only [cU]; omega)]; exact h.u, by rw [e cV (.inl rfl) (by simp only [cV]; omega)]; exact h.v,
    by rw [e cQ (.inl rfl) (by simp only [cQ]; omega)]; exact h.q, by rw [e cR (.inr rfl) (by simp only [cR]; omega)]; exact h.r⟩

/-- Index bounds. -/
macro "ix" : tactic => `(tactic| (simp only [bZ, bA1, bA2, bF, bG, bD, bE, bP, bT1, bT2, cU, cV, cQ, cR]; omega))

theorem two_H (k : Nat) : 2 * (2 ^ 31 * 2 ^ (32 * k)) = 2 ^ (32 * (k + 1)) := by
  rw [pow32_succ, ← Nat.mul_assoc]; rfl

theorem Mat.abs {m : Mem} {B : BitVec 32} {W : Nat} {u v q r : Int} (hm : Mat m B W u v q r)
    (huv : |u| + |v| ≤ 2 ^ 30) (hqr : |q| + |r| ≤ 2 ^ 30) :
    absC m B W cU = u.natAbs ∧ absC m B W cV = v.natAbs ∧ absC m B W cQ = q.natAbs ∧ absC m B W cR = r.natAbs :=
  ⟨abs_of hm.u (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
   abs_of hm.v (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
   abs_of hm.q (le_trans (le_add_of_nonneg_right (abs_nonneg _)) hqr),
   abs_of hm.r (le_trans (le_add_of_nonneg_left (abs_nonneg _)) hqr)⟩

theorem Mat.sgn {m : Mem} {B : BitVec 32} {W : Nat} {u v q r : Int} (hm : Mat m B W u v q r)
    (huv : |u| + |v| ≤ 2 ^ 30) (hqr : |q| + |r| ≤ 2 ^ 30) :
    (sgnC m B W cU ↔ u < 0) ∧ (sgnC m B W cV ↔ v < 0) ∧ (sgnC m B W cQ ↔ q < 0) ∧ (sgnC m B W cR ↔ r < 0) :=
  ⟨sgn_of hm.u (le_trans (le_add_of_nonneg_right (abs_nonneg _)) huv),
   sgn_of hm.v (le_trans (le_add_of_nonneg_left (abs_nonneg _)) huv),
   sgn_of hm.q (le_trans (le_add_of_nonneg_right (abs_nonneg _)) hqr),
   sgn_of hm.r (le_trans (le_add_of_nonneg_left (abs_nonneg _)) hqr)⟩

/-- The `f, g` half of a batch's update. -/
def fgList : List (Prog isa) := [lin bZ bA1 bF bG cU cV, lin bZ bA2 bF bG cQ cR, shr1 bF bA1, shr1 bG bA2]

/-- The value of one row, from `lin`'s and `shr1`'s results. -/
theorem fg_value {k cap : Nat} {u v f g z : Int} {F G T₁ T₂ A e R Zv : Nat}
    (hF : (F : Int) % ((2 ^ (32 * (k + 1)) : Nat) : Int) = f % ((2 ^ (32 * (k + 1)) : Nat) : Int))
    (hG : (G : Int) % ((2 ^ (32 * (k + 1)) : Nat) : Int) = g % ((2 ^ (32 * (k + 1)) : Nat) : Int))
    (hZ : Zv = 0) (c₁ : CN (u < 0) T₁ F Zv (k + 1)) (c₂ : CN (v < 0) T₂ G Zv (k + 1))
    (hA : A + 2 ^ (32 * (k + 1)) * e = u.natAbs * T₁ + v.natAbs * T₂) (hA' : A < 2 ^ (32 * (k + 1)))
    (huv : |u| + |v| ≤ 2 ^ 30) (hf : |f| ≤ cap) (hg : |g| ≤ cap) (hcap : 2 ^ 30 * cap < 2 ^ 31 * 2 ^ (32 * k))
    (hz : u * f + v * g = 2 ^ 30 * z)
    (hR : R = (A + 2 ^ (32 * (k + 1)) * (if 2 ^ 31 * 2 ^ (32 * k) ≤ A then 2 ^ 32 - 1 else 0)) / 2 ^ 30 %
      2 ^ (32 * (k + 1))) :
    (R : Int) % ((2 ^ (32 * (k + 1)) : Nat) : Int) = z % ((2 ^ (32 * (k + 1)) : Nat) : Int) := by
  subst hZ
  have e2 := two_H k
  rw [← e2] at hF hG hA hA' hR ⊢
  obtain ⟨n₁, p₁⟩ := c₁
  obtain ⟨n₂, p₂⟩ := c₂
  rw [← e2] at n₁ n₂
  exact fg_word (H := 2 ^ 31 * 2 ^ (32 * k)) (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) hF hG n₁ p₁ n₂ p₂
    hA hA' huv hf hg hcap rfl hz hR

theorem fg_ok {s : State} {B : BitVec 32} {Z W k N cap : Nat} {u v q r f g f' g' : Int} {P : Prop}
    (h : Gk s B Z W k N) (hN : 15 ≤ N) (hN' : N ≤ 256) (hm : P → Mat s.mem B W u v q r)
    (huv : P → |u| + |v| ≤ 2 ^ 30) (hqr : P → |q| + |r| ≤ 2 ^ 30)
    (hF : P → (nk s.mem B W bF (k + 1) : Int) % ((2 ^ (32 * (k + 1)) : Nat) : Int) = f % ((2 ^ (32 * (k + 1)) : Nat) : Int))
    (hG : P → (nk s.mem B W bG (k + 1) : Int) % ((2 ^ (32 * (k + 1)) : Nat) : Int) = g % ((2 ^ (32 * (k + 1)) : Nat) : Int))
    (hf : P → |f| ≤ cap) (hg : P → |g| ≤ cap) (hcap : P → 2 ^ 30 * cap < 2 ^ 31 * 2 ^ (32 * k))
    (z1 : P → u * f + v * g = 2 ^ 30 * f') (z2 : P → q * f + r * g = 2 ^ 30 * g') (hZ : nk s.mem B W bZ (k + 1) = 0) :
    WP isa (seqs fgList) s fun t => Gk t B Z W k N ∧ Keep B W fgArrs [] s.mem t.mem ∧
      (P → (nk t.mem B W bF (k + 1) : Int) % ((2 ^ (32 * (k + 1)) : Nat) : Int) = f' % ((2 ^ (32 * (k + 1)) : Nat) : Int)) ∧
      (P → (nk t.mem B W bG (k + 1) : Int) % ((2 ^ (32 * (k + 1)) : Nat) : Int) = g' % ((2 ^ (32 * (k + 1)) : Nat) : Int)) ∧
      Rest opRegs s t := by
  have hW : 1 ≤ W := Nat.le_trans h.kpos h.kle
  have hL : k + 1 ≤ W + 2 := by have := h.kle; omega
  have fit := fun j (hj : j < N) => h.fit64 hj
  have hS : S W = 4 * (W + 2) := rfl
  simp only [fgList, seqs]
  rw [WP.seq_iff]
  refine WP.mono (lin_ok (base := bZ) (acc := bA1) (x := bF) (y := bG) cU cV h hN hN' (by ix) (by ix) (by ix) (by ix) (by ix) (by ix)
    (by decide) (by decide) (by simp only [cU]; omega) (by simp only [cV]; omega) (by decide) (by decide))
    fun s1 ⟨g1, k1, T₁, T₂, e₁, c₁, c₂, t₁, t₂, v1, r1⟩ => ?_
  have hm1 := fun hP => (hm hP).keep k1 (by decide) hW (fit 1 (by omega)) (fit 3 (by omega))
  have nF1 := Keep.nk k1 hL (j := bF) (by decide) (by simp) (fit _ (by simp only [bF]; omega))
  have nG1 := Keep.nk k1 hL (j := bG) (by decide) (by simp) (fit _ (by simp only [bG]; omega))
  have nZ1 := Keep.nk k1 hL (j := bZ) (by decide) (by simp) (fit _ (by simp only [bZ]; omega))
  rw [WP.seq_iff]
  refine WP.mono (lin_ok (base := bZ) (acc := bA2) (x := bF) (y := bG) cQ cR g1 hN hN' (by ix) (by ix) (by ix) (by ix) (by ix) (by ix)
    (by decide) (by decide) (by simp only [cQ]; omega) (by simp only [cR]; omega) (by decide) (by decide))
    fun s2 ⟨g2, k2, T₃, T₄, e₂, c₃, c₄, t₃, t₄, v2, r2⟩ => ?_
  have nA1 := Keep.nk k2 hL (j := bA1) (by decide) (by simp) (fit _ (by simp only [bA1]; omega))
  have aw1 : aw s2.mem B W bA1 (4 * k) = aw s1.mem B W bA1 (4 * k) :=
    Keep.aw k2 (by omega) (by decide) (fit _ (by simp only [bA1]; omega))
  rw [WP.seq_iff]
  refine WP.mono (shr1_ok g2 (o := bF) (a := bA1) (by simp only [bF]; omega) (by simp only [bA1]; omega) hN'
    (by decide)) fun s3 ⟨g3, k3, v3, r3⟩ => ?_
  have nA2 := Keep.nk k3 hL (j := bA2) (by decide) (by simp) (fit _ (by simp only [bA2]; omega))
  have aw2 : aw s3.mem B W bA2 (4 * k) = aw s2.mem B W bA2 (4 * k) :=
    Keep.aw k3 (by omega) (by decide) (fit _ (by simp only [bA2]; omega))
  refine WP.mono (shr1_ok g3 (o := bG) (a := bA2) (by simp only [bG]; omega) (by simp only [bA2]; omega) hN'
    (by decide)) fun t ⟨gt, kt, vt, rt⟩ => ?_
  have nF4 := Keep.nk kt hL (j := bF) (by decide) (by simp) (fit _ (by simp only [bF]; omega))
  refine ⟨gt, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans ((k3.mono (by decide)).trans
    (kt.mono (by decide))), ?_, ?_, r1.trans (r2.trans (r3.trans rt))⟩
  · intro hP
    obtain ⟨au, av, -, -⟩ := (hm hP).abs (huv hP) (hqr hP)
    obtain ⟨su, sv, -, -⟩ := (hm hP).sgn (huv hP) (hqr hP)
    rw [nF4, v3, nA1, aw1]
    simp only [← top_bit]
    rw [au, av] at v1
    have c₁' : CN (u < 0) T₁ (nk s.mem B W bF (k + 1)) (nk s.mem B W bZ (k + 1)) (k + 1) := by
      simpa only [CN, su] using c₁
    have c₂' : CN (v < 0) T₂ (nk s.mem B W bG (k + 1)) (nk s.mem B W bZ (k + 1)) (k + 1) := by
      simpa only [CN, sv] using c₂
    exact fg_value (hF hP) (hG hP) hZ c₁' c₂' v1 (val32_lt _ _ _ _) (huv hP) (hf hP) (hg hP) (hcap hP) (z1 hP) rfl
  · intro hP
    obtain ⟨-, -, aq, ar⟩ := (hm1 hP).abs (huv hP) (hqr hP)
    obtain ⟨-, -, sq, sr⟩ := (hm1 hP).sgn (huv hP) (hqr hP)
    rw [vt, nA2, aw2]
    simp only [← top_bit]
    rw [aq, ar] at v2
    have c₃' : CN (q < 0) T₃ (nk s.mem B W bF (k + 1)) (nk s.mem B W bZ (k + 1)) (k + 1) := by
      simpa only [CN, sq, nF1, nZ1] using c₃
    have c₄' : CN (r < 0) T₄ (nk s.mem B W bG (k + 1)) (nk s.mem B W bZ (k + 1)) (k + 1) := by
      simpa only [CN, sr, nG1, nZ1] using c₄
    exact fg_value (hF hP) (hG hP) hZ c₃' c₄' v2 (val32_lt _ _ _ _) (hqr hP) (hf hP) (hg hP) (hcap hP) (z2 hP) rfl

theorem word0 (m : Mem) (B : BitVec 32) (W j k : Nat) : aw m B W j 0 = nk m B W j (k + 1) % 2 ^ 32 := by
  simp only [nk, val32]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (BitVec.isLt _)]
  simp only [aw, w32, Nat.add_zero]

/-- The `d, e` half of a batch's update. -/
def deList : List (Prog isa) := [lin bP bA1 bD bE cU cV, lin bP bA2 bD bE cQ cR, redc bA1, redc bA2,
  shr1 bT2 bA1, csub1 bD bT2, shr1 bT2 bA2, csub1 bE bT2]

/-- One row of `d, e`, from the results of `lin`, `redc`, `shr1` and `csub1`. -/
theorem de_value {k p iv : Nat} {u v : Int} {D E T₁ T₂ A e A' c R D' : Nat}
    (hp : p % 2 = 1) (hpk : p ≤ 2 ^ (32 * k)) (hiv : (p * iv + 1) % 2 ^ 32 = 0) (hD : D < p) (hE : E < p)
    (c₁ : CN (u < 0) T₁ D p (k + 1)) (c₂ : CN (v < 0) T₂ E p (k + 1))
    (t₁ : T₁ < 2 ^ (32 * (k + 1))) (t₂ : T₂ < 2 ^ (32 * (k + 1))) (huv : |u| + |v| ≤ 2 ^ 30)
    (hA : A + 2 ^ (32 * (k + 1)) * e = u.natAbs * T₁ + v.natAbs * T₂) (hA' : A < 2 ^ (32 * (k + 1)))
    (hred : A' + 2 ^ (32 * (k + 1)) * c = A + digit (A % 2 ^ 32) iv * p) (hA'' : A' < 2 ^ (32 * (k + 1)))
    (hR : R = (A' + 2 ^ (32 * (k + 1)) * (if 2 ^ 31 * 2 ^ (32 * k) ≤ A' then 2 ^ 32 - 1 else 0)) / 2 ^ 30 %
      2 ^ (32 * (k + 1)))
    (hD' : D' = (if R < p then R else R - p) % 2 ^ (32 * (k + 1))) :
    D' < p ∧ (2 ^ 30 * D' : Int) ≡ u * D + v * E [ZMOD p] := by
  have e2 := two_H k
  rw [← e2] at t₁ t₂ hA hA' hred hA'' hR hD'
  obtain ⟨n₁, p₁⟩ := c₁
  obtain ⟨n₂, p₂⟩ := c₂
  rw [← e2] at n₁ n₂
  exact de_word hp (Nat.mul_le_mul_left _ hpk) hiv hD hE t₁ t₂ n₁ p₁ n₂ p₂ huv hA hA' rfl hred hA'' hR hD'

theorem de_ok {s : State} {B : BitVec 32} {Z W k N p iv : Nat} {u v q r : Int} {P : Prop}
    (h : Gk s B Z W k N) (hN : 15 ≤ N) (hN' : N ≤ 256) (hm : P → Mat s.mem B W u v q r)
    (huv : P → |u| + |v| ≤ 2 ^ 30) (hqr : P → |q| + |r| ≤ 2 ^ 30) (hP : nk s.mem B W bP (k + 1) = p)
    (hp : P → p % 2 = 1) (hpk : p ≤ 2 ^ (32 * k)) (hiv : P → (p * iv + 1) % 2 ^ 32 = 0) (hsB : slot s.mem B sB = iv)
    (hD : P → nk s.mem B W bD (k + 1) < p) (hE : P → nk s.mem B W bE (k + 1) < p) :
    WP isa (seqs deList) s fun t => Gk t B Z W k N ∧ Keep B W deArrs [] s.mem t.mem ∧
      (P → nk t.mem B W bD (k + 1) < p ∧ (2 ^ 30 * nk t.mem B W bD (k + 1) : Int) ≡
        u * nk s.mem B W bD (k + 1) + v * nk s.mem B W bE (k + 1) [ZMOD p]) ∧
      (P → nk t.mem B W bE (k + 1) < p ∧ (2 ^ 30 * nk t.mem B W bE (k + 1) : Int) ≡
        q * nk s.mem B W bD (k + 1) + r * nk s.mem B W bE (k + 1) [ZMOD p]) ∧
      Rest opRegs s t := by
  have hW : 1 ≤ W := Nat.le_trans h.kpos h.kle
  have hL : k + 1 ≤ W + 2 := by have := h.kle; omega
  have fit := fun j (hj : j < N) => h.fit64 hj
  have hS : S W = 4 * (W + 2) := rfl
  have pk : nk s.mem B W bP (k + 1) ≤ 2 ^ (32 * k) := hP ▸ hpk
  simp only [deList, seqs]
  rw [WP.seq_iff]
  refine WP.mono (lin_ok (base := bP) (acc := bA1) (x := bD) (y := bE) cU cV h hN hN' (by ix) (by ix) (by ix)
    (by ix) (by ix) (by ix) (by decide) (by decide) (by simp only [cU]; omega) (by simp only [cV]; omega)
    (by decide) (by decide)) fun s1 ⟨g1, k1, T₁, T₂, e₁, c₁, c₂, t₁, t₂, v1, r1⟩ => ?_
  have hm1 := fun hP => (hm hP).keep k1 (by decide) hW (fit 1 (by omega)) (fit 3 (by omega))
  have nD1 := Keep.nk k1 hL (j := bD) (by decide) (by simp) (fit _ (by ix))
  have nE1 := Keep.nk k1 hL (j := bE) (by decide) (by simp) (fit _ (by ix))
  have nP1 := Keep.nk k1 hL (j := bP) (by decide) (by simp) (fit _ (by ix))
  rw [WP.seq_iff]
  refine WP.mono (lin_ok (base := bP) (acc := bA2) (x := bD) (y := bE) cQ cR g1 hN hN' (by ix) (by ix) (by ix)
    (by ix) (by ix) (by ix) (by decide) (by decide) (by simp only [cQ]; omega) (by simp only [cR]; omega)
    (by decide) (by decide)) fun s2 ⟨g2, k2, T₃, T₄, e₂, c₃, c₄, t₃, t₄, v2, r2⟩ => ?_
  have nA1 := Keep.nk k2 hL (j := bA1) (by decide) (by simp) (fit _ (by ix))
  have nP2 := Keep.nk k2 hL (j := bP) (by decide) (by simp) (fit _ (by ix))
  have sl2 : slot s2.mem B sB = iv := by
    rw [Keep.slot k2 (by decide) (by simp), Keep.slot k1 (by decide) (by simp), hsB]
  rw [WP.seq_iff]
  refine WP.mono (redc_ok g2 (acc := bA1) (by ix) (by ix) (by decide) hN') fun s3 ⟨g3, k3, v3, r3⟩ => ?_
  have nA2 := Keep.nk k3 hL (j := bA2) (by decide) (by simp) (fit _ (by ix))
  have nP3 := Keep.nk k3 hL (j := bP) (by decide) (by simp) (fit _ (by ix))
  have sl3 : slot s3.mem B sB = iv := by rw [Keep.slot k3 (by decide) (by simp), sl2]
  rw [WP.seq_iff]
  refine WP.mono (redc_ok g3 (acc := bA2) (by ix) (by ix) (by decide) hN') fun s4 ⟨g4, k4, v4, r4⟩ => ?_
  have nA1' := Keep.nk k4 hL (j := bA1) (by decide) (by simp) (fit _ (by ix))
  have aw1 : aw s4.mem B W bA1 (4 * k) = aw s3.mem B W bA1 (4 * k) :=
    Keep.aw k4 (by omega) (by decide) (fit _ (by ix))
  have nP4 := Keep.nk k4 hL (j := bP) (by decide) (by simp) (fit _ (by ix))
  rw [WP.seq_iff]
  refine WP.mono (shr1_ok g4 (o := bT2) (a := bA1) (by ix) (by ix) hN' (by decide)) fun s5 ⟨g5, k5, v5, r5⟩ => ?_
  have nP5 := Keep.nk k5 hL (j := bP) (by decide) (by simp) (fit _ (by ix))
  have nA2' := Keep.nk k5 hL (j := bA2) (by decide) (by simp) (fit _ (by ix))
  have aw2 : aw s5.mem B W bA2 (4 * k) = aw s4.mem B W bA2 (4 * k) :=
    Keep.aw k5 (by omega) (by decide) (fit _ (by ix))
  rw [WP.seq_iff]
  refine WP.mono (csub1_ok false g5 (o := bD) (a := bT2) hN hN' (by ix) (by ix) (by decide))
    fun s6 ⟨g6, k6, v6, r6, _⟩ => ?_
  have nP6 := Keep.nk k6 hL (j := bP) (by decide) (by simp) (fit _ (by ix))
  have nA2'' := Keep.nk k6 hL (j := bA2) (by decide) (by simp) (fit _ (by ix))
  have aw2' : aw s6.mem B W bA2 (4 * k) = aw s5.mem B W bA2 (4 * k) :=
    Keep.aw k6 (by omega) (by decide) (fit _ (by ix))
  rw [WP.seq_iff]
  refine WP.mono (shr1_ok g6 (o := bT2) (a := bA2) (by ix) (by ix) hN' (by decide)) fun s7 ⟨g7, k7, v7, r7⟩ => ?_
  have nP7 := Keep.nk k7 hL (j := bP) (by decide) (by simp) (fit _ (by ix))
  have nD7 := Keep.nk k7 hL (j := bD) (by decide) (by simp) (fit _ (by ix))
  refine WP.mono (csub1_ok false g7 (o := bE) (a := bT2) hN hN' (by ix) (by ix) (by decide))
    fun t ⟨gt, kt, vt, rt, _⟩ => ?_
  have nDt := Keep.nk kt hL (j := bD) (by decide) (by simp) (fit _ (by ix))
  refine ⟨gt, ((k1.mono (by decide)).trans (k2.mono (by decide))).trans (((k3.mono (by decide)).trans
    (k4.mono (by decide))).trans (((k5.mono (by decide)).trans (k6.mono (by decide))).trans
    ((k7.mono (by decide)).trans (kt.mono (by decide))))), ?_, ?_,
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans (r6.trans (r7.trans rt))))))⟩
  · intro hQ
    obtain ⟨au, av, -, -⟩ := (hm hQ).abs (huv hQ) (hqr hQ)
    obtain ⟨su, sv, -, -⟩ := (hm hQ).sgn (huv hQ) (hqr hQ)
    rw [nDt, nD7]
    simp only [len1, Bool.false_eq_true, ↓reduceIte] at v6 vt
    have pP : ∀ m, m = s5.mem ∨ m = s7.mem → nk m B W bP (k + 1) = p := by
      rintro m (rfl | rfl)
      · rw [nP5, nP4, nP3, nP2, nP1, hP]
      · rw [nP7, nP6, nP5, nP4, nP3, nP2, nP1, hP]
    rw [pP _ (.inl rfl)] at v6
    rw [nA1', aw1] at v5
    simp only [← top_bit] at v5
    rw [word0 s2.mem B W bA1 k, nA1, sl2, nP2, nP1, hP] at v3
    have c₁' : CN (u < 0) T₁ (nk s.mem B W bD (k + 1)) p (k + 1) := by simpa only [CN, su, hP] using c₁
    have c₂' : CN (v < 0) T₂ (nk s.mem B W bE (k + 1)) p (k + 1) := by simpa only [CN, sv, hP] using c₂
    rw [au, av] at v1
    exact de_value (hp hQ) hpk (hiv hQ) (hD hQ) (hE hQ) c₁' c₂' t₁ t₂ (huv hQ) v1 (val32_lt _ _ _ _) v3 (val32_lt _ _ _ _) v5 v6
  · intro hQ
    obtain ⟨-, -, aq, ar⟩ := (hm1 hQ).abs (huv hQ) (hqr hQ)
    obtain ⟨-, -, sq, sr⟩ := (hm1 hQ).sgn (huv hQ) (hqr hQ)
    simp only [len1, Bool.false_eq_true, ↓reduceIte] at vt
    rw [nP7, nP6, nP5, nP4, nP3, nP2, nP1, hP] at vt
    rw [nA2'', aw2', nA2', aw2] at v7
    simp only [← top_bit] at v7
    rw [word0 s3.mem B W bA2 k, nA2, sl3, nP3, nP2, nP1, hP] at v4
    have nA2s : nk s3.mem B W bA2 (k + 1) = nk s2.mem B W bA2 (k + 1) := nA2
    have c₃' : CN (q < 0) T₃ (nk s.mem B W bD (k + 1)) p (k + 1) := by
      simpa only [CN, sq, hP, nD1, nP1] using c₃
    have c₄' : CN (r < 0) T₄ (nk s.mem B W bE (k + 1)) p (k + 1) := by
      simpa only [CN, sr, hP, nE1, nP1] using c₄
    rw [aq, ar] at v2
    exact de_value (hp hQ) hpk (hiv hQ) (hD hQ) (hE hQ) c₃' c₄' t₃ t₄ (hqr hQ) v2 (val32_lt _ _ _ _) v4 (val32_lt _ _ _ _) v7 vt

end VG.Proof.Rsa.Arm.Inv
