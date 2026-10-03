import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Lanes

/-!
# A reverse mix on four blocks at once

`rmixCode_ok`: on registers given as variables, the eight instructions of a
reverse mix leave in each lane of the word's register the lane's word
rotated right, less the key word and the two composite terms
(`Spec.Rc2.reverseMix`). `rmix_ok` instantiates it for word `i` of set `h`.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64.Vec

/-- `0xffff` in every lane. -/
def mask16 : BitVec 128 := ofVWords 65535 65535 65535 65535

theorem vword_mask16 {b : Nat} (hb : b < 4) : vword mask16 b = 65535 := by
  rw [mask16, vword_ofVWords _ _ _ _ hb]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- A reverse mix, on registers given as variables: the word `w`, the words
before it `a3`, `a2`, `a1`, the temporaries `t`, `u`, `v`. -/
def rmixCode (w a1 a2 a3 t u v : VReg) (s : Nat) : List Instr :=
  [.vop (.logic .and w w m16),
   .vop (.shift .ushr .s4 t w s),
   .vop (.shift .sli .s4 t w (16 - s)),
   .vop (.logic .and u a3 a2),
   .vop (.logic .bic v a1 a3),
   .vop (.sub .s4 t t kb),
   .vop (.sub .s4 t t u),
   .vop (.sub .s4 w t v)]

theorem rmix_eq (h i : Nat) : rmix h i =
    rmixCode (wreg h i) (wreg h (i + 1)) (wreg h (i + 2)) (wreg h (i + 3)) (tmp h 0) (tmp h 1)
      (tmp h 2) (Spec.Rc2.rotation i) := rfl

theorem exec_shift (s : State) (op : VShiftOp) (a : VArr) (d n : VReg) (sh : Nat)
    (h : op.ok a.esize sh = true) :
    exec (.vop (.shift op a d n sh)) s =
      some (s.setV d (a.map2 (fun w x y => op.eval sh w x y) (s.v d) (s.v n))) := by
  simp [exec, VOp.eval, h]

theorem exec_sub4 (s : State) (d n m : VReg) :
    exec (.vop (.sub .s4 d n m)) s = some (s.setV d (VArr.s4.map2 (fun _ x y => x - y) (s.v n) (s.v m))) :=
  rfl

theorem exec_and (s : State) (d n m : VReg) :
    exec (.vop (.logic .and d n m)) s = some (s.setV d (s.v n &&& s.v m)) := rfl

theorem exec_bic (s : State) (d n m : VReg) :
    exec (.vop (.logic .bic d n m)) s = some (s.setV d (s.v n &&& ~~~(s.v m))) := rfl

/-- The registers of a reverse mix: all different where it matters. -/
structure MixRegs (w a1 a2 a3 t u v : VReg) : Prop where
  tw : t ≠ w
  uw : u ≠ w
  vw : v ≠ w
  ut : u ≠ t
  vt : v ≠ t
  vu : v ≠ u
  a1w : a1 ≠ w
  a1t : a1 ≠ t
  a1u : a1 ≠ u
  a2w : a2 ≠ w
  a2t : a2 ≠ t
  a3w : a3 ≠ w
  a3t : a3 ≠ t
  a3u : a3 ≠ u
  kw : kb ≠ w
  kt : kb ≠ t
  ku : kb ≠ u
  kv : kb ≠ v
  mw : m16 ≠ w

/-- The lane value of a reverse mix. -/
theorem rmixLane (x a b c k : BitVec 32) {s : Nat} (h1 : 1 ≤ s) (h2 : s < 16) :
    ((((((x &&& 65535) >>> s) &&& ~~~(BitVec.allOnes 32 <<< (16 - s))) |||
      ((x &&& 65535) <<< (16 - s))) - k - (a &&& b) - (c &&& ~~~a)).setWidth 16) =
      (x.setWidth 16).rotateRight s - k.setWidth 16 - (a.setWidth 16 &&& b.setWidth 16) -
        (~~~(a.setWidth 16) &&& c.setWidth 16) := by
  rw [setWidth16_sub, setWidth16_sub, setWidth16_sub, ror_lane x h1 h2, setWidth16_and,
    setWidth16_and, setWidth16_not, BitVec.and_comm (c.setWidth 16)]

theorem rmixCode_ok {s : State} {w a1 a2 a3 t u v : VReg} (hr : MixRegs w a1 a2 a3 t u v)
    {sh : Nat} (h1 : 1 ≤ sh) (h2 : sh < 16) (hm : s.v m16 = mask16) :
    ∃ s', runBlock isa (rmixCode w a1 a2 a3 t u v sh) s = some s' ∧
      (∀ b < 4, lw (s'.v w) b =
        (lw (s.v w) b).rotateRight sh - lw (s.v kb) b - (lw (s.v a3) b &&& lw (s.v a2) b) -
          (~~~(lw (s.v a3) b) &&& lw (s.v a1) b)) ∧
      (∀ r, r ≠ w → r ≠ t → r ≠ u → r ≠ v → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setV w (s.v w &&& s.v m16)
  let s₂ := s₁.setV t (VArr.s4.map2 (fun ww x y => VShiftOp.ushr.eval sh ww x y) (s₁.v t) (s₁.v w))
  let s₃ := s₂.setV t (VArr.s4.map2 (fun ww x y => VShiftOp.sli.eval (16 - sh) ww x y) (s₂.v t) (s₂.v w))
  let s₄ := s₃.setV u (s₃.v a3 &&& s₃.v a2)
  let s₅ := s₄.setV v (s₄.v a1 &&& ~~~(s₄.v a3))
  let s₆ := s₅.setV t (VArr.s4.map2 (fun _ x y => x - y) (s₅.v t) (s₅.v kb))
  let s₇ := s₆.setV t (VArr.s4.map2 (fun _ x y => x - y) (s₆.v t) (s₆.v u))
  let s₈ := s₇.setV w (VArr.s4.map2 (fun _ x y => x - y) (s₇.v t) (s₇.v v))
  have ok1 : VShiftOp.ushr.ok VArr.s4.esize sh = true := by
    simp [VShiftOp.ok, VArr.esize]; omega
  have ok2 : VShiftOp.sli.ok VArr.s4.esize (16 - sh) = true := by
    simp [VShiftOp.ok, VArr.esize]; omega
  refine ⟨s₈, ?_, fun b hb => ?_, fun r h1 h2 h3 h4 => ?_,
    by simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_setV],
    by simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, mem_setV],
    by simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, rd_setV],
    by simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, wr_setV],
    by simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, sp_setV]⟩
  · rw [rmixCode, runBlock_cons, exec_and, runStep_some, runBlock_cons, exec_shift _ _ _ _ _ _ ok1,
      runStep_some, runBlock_cons, exec_shift _ _ _ _ _ _ ok2, runStep_some, runBlock_cons, exec_and,
      runStep_some, runBlock_cons, exec_bic, runStep_some, runBlock_cons, exec_sub4, runStep_some,
      runBlock_cons, exec_sub4, runStep_some, runBlock_cons, exec_sub4, runStep_some, runBlock_nil]
  · -- The values of the registers along the way.
    have w1 : s₁.v w = s.v w &&& mask16 := by simp only [s₁, v_setV_self, hm]
    have w2 : s₂.v w = s₁.v w := v_setV_of_ne _ _ hr.tw.symm
    have t3 : s₃.v t = VArr.s4.map2 (fun ww x y => VShiftOp.sli.eval (16 - sh) ww x y)
        (VArr.s4.map2 (fun ww x y => VShiftOp.ushr.eval sh ww x y) (s₁.v t) (s₁.v w)) (s₁.v w) := by
      simp only [s₃, v_setV_self, w2]; rw [show s₂.v t = _ from v_setV_self _ _ _]
    have a3s : s₃.v a3 = s.v a3 := by
      simp only [s₃, s₂, s₁, v_setV_of_ne _ _ hr.a3t, v_setV_of_ne _ _ hr.a3w]
    have a2s : s₃.v a2 = s.v a2 := by
      simp only [s₃, s₂, s₁, v_setV_of_ne _ _ hr.a2t, v_setV_of_ne _ _ hr.a2w]
    have u4 : s₄.v u = s.v a3 &&& s.v a2 := by simp only [s₄, v_setV_self, a3s, a2s]
    have a1s : s₄.v a1 = s.v a1 := by
      simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ hr.a1u, v_setV_of_ne _ _ hr.a1t,
        v_setV_of_ne _ _ hr.a1w]
    have a3s4 : s₄.v a3 = s.v a3 := by
      simp only [s₄, v_setV_of_ne _ _ hr.a3u, a3s]
    have v5 : s₅.v v = s.v a1 &&& ~~~(s.v a3) := by simp only [s₅, v_setV_self, a1s, a3s4]
    have t5 : s₅.v t = s₃.v t := by
      simp only [s₅, s₄, v_setV_of_ne _ _ hr.vt.symm, v_setV_of_ne _ _ hr.ut.symm]
    have k5 : s₅.v kb = s.v kb := by
      simp only [s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ hr.kv, v_setV_of_ne _ _ hr.ku,
        v_setV_of_ne _ _ hr.kt, v_setV_of_ne _ _ hr.kw]
    have u6 : s₆.v u = s₄.v u := by
      simp only [s₆, s₅, v_setV_of_ne _ _ hr.ut, v_setV_of_ne _ _ hr.vu.symm]
    have v7 : s₇.v v = s₅.v v := by
      simp only [s₇, s₆, v_setV_of_ne _ _ hr.vt]
    have t7 : s₇.v t = VArr.s4.map2 (fun _ x y => x - y)
        (VArr.s4.map2 (fun _ x y => x - y) (s₅.v t) (s₅.v kb)) (s₆.v u) := by
      simp only [s₇, v_setV_self]; rw [show s₆.v t = _ from v_setV_self _ _ _]
    have w8 : s₈.v w = VArr.s4.map2 (fun _ x y => x - y) (s₇.v t) (s₇.v v) := v_setV_self _ _ _
    have lane : vword (s₈.v w) b =
        (((((vword (s.v w) b &&& 65535) >>> sh) &&& ~~~(BitVec.allOnes 32 <<< (16 - sh))) |||
          ((vword (s.v w) b &&& 65535) <<< (16 - sh))) - vword (s.v kb) b -
          (vword (s.v a3) b &&& vword (s.v a2) b) - (vword (s.v a1) b &&& ~~~vword (s.v a3) b)) := by
      rw [w8, t7, v7, v5, u6, u4, k5, t5, t3, w1]
      simp only [vword_map2 _ _ _ hb, vword_and, vword_not _ hb, vword_mask16 hb, VShiftOp.eval]
    rw [lw, lane]
    exact rmixLane _ _ _ _ _ h1 h2
  · simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2,
      v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h4]

end VG.Proof.Rc2.AArch64.Vec
