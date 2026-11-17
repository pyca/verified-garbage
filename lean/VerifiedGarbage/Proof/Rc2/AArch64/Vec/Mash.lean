module

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Rc2.AArch64.CbcVec
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
public import VerifiedGarbage.Proof.Rc2.AArch64.Lookup
import VerifiedGarbage.Proof.Rc2.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Rc2.AArch64.Vec.Round`, which this module and modules that import it used -/

section

/-! ### `Rc2.AArch64.Vec.Mix`, which only this module used -/

section

/-! ### `Rc2.AArch64.Vec.Lanes`, which only this module used -/

section

/-!
# RC2 words in 32-bit lanes

The vector decryption keeps word `i` of block `b` of set `h` in the low 16
bits of lane `b` of `wreg h i` (`lw`, `VWords`); the high 16 bits are not
kept. These are the lane facts about the operations it uses: the bitwise
ones and subtraction act on each lane's low 16 bits alone, and masking,
shifting right by `s` and inserting the word shifted left by `16 - s`
rotates it right by `s` (`ror_lane`).
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64.Vec

/-- The low 16 bits of lane `b`. -/
abbrev lw (x : BitVec 128) (b : Nat) : BitVec 16 := (vword x b).setWidth 16

/-- The words of set `h`: word `i` of block `b` is `vs b`'s. -/
def VWords (s : State) (h : Nat) (vs : Nat → Spec.Rc2.State) : Prop :=
  ∀ i < 4, ∀ b < 4, lw (s.v (wreg h i)) b = (vs b).getD i 0

theorem vword_and (x y : BitVec 128) (c : Nat) : vword (x &&& y) c = vword x c &&& vword y c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_and]

theorem vword_not (x : BitVec 128) {c : Nat} (hc : c < 4) : vword (~~~x) c = ~~~vword x c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_not, show 32 * c + i < 128 by omega_using [hc, hi]]

theorem setWidth16_sub (x y : BitVec 32) : (x - y).setWidth 16 = x.setWidth 16 - y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  omega_using []

theorem setWidth16_and (x y : BitVec 32) : (x &&& y).setWidth 16 = x.setWidth 16 &&& y.setWidth 16 := by
  ext i hi; simp

theorem setWidth16_not (x : BitVec 32) : (~~~x).setWidth 16 = ~~~(x.setWidth 16) := by
  ext i hi; simp [show i < 32 by omega_using [hi]]

theorem bit65535 (k : Nat) : (65535 : BitVec 32).getLsbD k = decide (k < 16) := by
  rw [show (65535 : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : k < 16
  · simp [h, show k < 32 by omega_using [h]]
  · simp [h]

/-- Masking, shifting right by `s` and inserting the masked word shifted left
by `16 - s`: the low 16 bits rotated right by `s`. -/
theorem ror_lane (x : BitVec 32) {s : Nat} (h1 : 1 ≤ s) (h2 : s < 16) :
    ((((x &&& 65535) >>> s) &&& ~~~(BitVec.allOnes 32 <<< (16 - s))) |||
      ((x &&& 65535) <<< (16 - s))).setWidth 16 = (x.setWidth 16).rotateRight s := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_rotateRight, hj, decide_true, Bool.true_and, Nat.mod_eq_of_lt h2, bit65535]
  by_cases hs : j < 16 - s
  · simp (disch := omega) [hs, show j < 32 by omega_using [hj], show s + j < 16 by omega_using [hs]]
  · simp (disch := omega) [hs, show j < 32 by omega_using [hj], show ¬ s + j < 16 by omega_using [hs],
      show j - (16 - s) < 16 by omega_using [hj]]

end VG.Proof.Rc2.AArch64.Vec

end

end


/-!
# A reverse mix on four blocks at once

`rmixCode_ok`: on registers given as variables, the eight instructions of a
reverse mix leave in each lane of the word's register the lane's word
rotated right, less the key word and the two composite terms
(`Spec.Rc2.reverseMix`). `rmix_ok` instantiates it for word `i` of set `h`.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64.Vec

/-- `0xffff` in every lane. -/
def mask16 : BitVec 128 := ofVWords 65535 65535 65535 65535

theorem vword_mask16 {b : Nat} (hb : b < 4) : vword mask16 b = 65535 := by
  rw [mask16, vword_ofVWords _ _ _ _ hb]
  rcases (by omega_using [hb] : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

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
    simp [VShiftOp.ok, VArr.esize]; omega_using [h1, h2]
  have ok2 : VShiftOp.sli.ok VArr.s4.esize (16 - sh) = true := by
    simp [VShiftOp.ok, VArr.esize]; omega_using []
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

end

end


/-!
# Reverse mixing rounds on eight blocks

The schedule is in `v16`–`v23` (`SchedV`); `keyBcast_ok` broadcasts a key
word from it, `rmix_ok` is a reverse mix on a set (`VWords`), and
`rmixRound_ok` a reverse mixing round on both sets.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- The schedule at `p` in `v16`–`v23`. -/
def SchedV (s : State) (m : Mem) (p : Addr) : Prop :=
  ∀ r < 8, s.v (treg r) = m.read (p + BitVec.ofNat 64 (16 * r)) 16

/-- A lane's low 16 bits are its first two bytes. -/
theorem lw_bytes (x : BitVec 128) (b : Nat) :
    lw x b = (vbyte x (4 * b)).setWidth 16 ||| (vbyte x (4 * b + 1)).setWidth 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [lw, vword, vbyte, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and]
  by_cases h8 : t < 8
  · simp [h8, show t < 32 by omega_arith, show 8 * (4 * b) + t = 32 * b + t by omega_arith]
  · simp [h8, show t < 32 by omega_arith, show t - 8 < 8 by omega_arith, show t - 8 < 16 by omega_arith,
      show 8 * (4 * b + 1) + (t - 8) = 32 * b + t by omega_arith]

theorem exec_dupE (s : State) (d n : VReg) {i : Nat} (hi : i < 4) :
    exec (.vop (.dupE .s4 d n i)) s =
      some (s.setV d (VArr.s4.map2 (fun w _ _ => (s.v n).extractLsb' (w * i) w) 0 0)) := by
  simp [exec, VOp.eval, VArr.esize, show i < 4 from hi]

theorem exec_rev (s : State) (op : VRevOp) (d n : VReg) :
    exec (.vop (.rev op d n)) s = some (s.setV d (op.eval (s.v n))) := rfl

theorem vbyte_read (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    vbyte (m.read a 16) e = m (a + BitVec.ofNat 64 e) := Mem.extractLsb'_read m a he

/-- Key word `k` broadcast. -/
theorem keyBcast_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p) {k : Nat} (hk : k < 64) :
    ∃ s', runBlock isa (keyBcast k) s = some s' ∧
      (∀ b < 4, lw (s'.v kb) b = (Spec.Rc2.scheduleAt m p).getD k 0) ∧
      (∀ r, r ≠ kb → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let S := s.v (treg (k / 8))
  let D : BitVec 128 := VArr.s4.map2 (fun w _ _ => S.extractLsb' (w * (k % 8 / 2)) w) 0 0
  let s₁ := s.setV kb D
  have hS : S = m.read (p + BitVec.ofNat 64 (16 * (k / 8))) 16 := hs _ (by omega_arith)
  -- Byte `e` of lane `b` of the broadcast.
  have dB : ∀ b < 4, ∀ e < 4, vbyte D (4 * b + e) = m (p + BitVec.ofNat 64 (2 * (k / 2 * 2) + e)) := by
    intro b hb e he
    have hv : vword D b = vword S (k % 8 / 2) := by
      simp only [D, vword_map2 _ _ _ hb]; rfl
    have : vbyte D (4 * b + e) = (vword D b).extractLsb' (8 * e) 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro t ht
      simp [vbyte, vword, ht, show 8 * e + t < 32 by omega_arith, show 8 * (4 * b + e) + t = 32 * b + (8 * e + t) by omega_arith]
    rw [this, hv]
    have : (vword S (k % 8 / 2)).extractLsb' (8 * e) 8 = vbyte S (4 * (k % 8 / 2) + e) := by
      apply BitVec.eq_of_getLsbD_eq; intro t ht
      simp [vbyte, vword, ht, show 8 * e + t < 32 by omega_arith,
        show 8 * (4 * (k % 8 / 2) + e) + t = 32 * (k % 8 / 2) + (8 * e + t) by omega_arith]
    rw [this, hS, vbyte_read _ _ (by omega_arith), Offset.add_add,
      show 16 * (k / 8) + (4 * (k % 8 / 2) + e) = 2 * (k / 2 * 2) + e by omega_arith]
  have key : ∀ b < 4, lw (s₁.v kb) b = (m (p + BitVec.ofNat 64 (2 * (k / 2 * 2)))).setWidth 16 |||
      (m (p + BitVec.ofNat 64 (2 * (k / 2 * 2) + 1))).setWidth 16 <<< 8 := by
    intro b hb
    rw [show s₁.v kb = D from v_setV_self _ _ _, lw_bytes _ b,
      show 4 * b = 4 * b + 0 by omega_arith, dB b hb 0 (by decide), dB b hb 1 (by decide)]
    rfl
  by_cases hp : k % 2 = 1
  · let s₂ := s₁.setV kb (VRevOp.rev32h.eval (s₁.v kb))
    refine ⟨s₂, ?_, fun b hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [keyBcast, ite_eq_left hp, List.singleton_append, runBlock_cons, exec_dupE _ _ _ (by omega_arith),
        runStep_some, runBlock_cons, exec_rev, runStep_some, runBlock_nil]
    · rw [show s₂.v kb = VRevOp.rev32h.eval (s₁.v kb) from v_setV_self _ _ _, lw_bytes _ b,
        VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hk]
      simp only [VRevOp.eval, vbyte_ofVBytes _ (show 4 * b < 16 by omega_arith),
        vbyte_ofVBytes _ (show 4 * b + 1 < 16 by omega_arith),
        show 4 * (4 * b / 4) + (4 * b % 4 + 2) % 4 = 4 * b + 2 by omega_arith,
        show 4 * ((4 * b + 1) / 4) + ((4 * b + 1) % 4 + 2) % 4 = 4 * b + 3 by omega_arith]
      rw [show s₁.v kb = D from v_setV_self _ _ _, dB b hb 2 (by decide), dB b hb 3 (by decide),
        show 2 * (k / 2 * 2) + 2 = 2 * k by omega_arith, show 2 * (k / 2 * 2) + 3 = 2 * k + 1 by omega_arith]
    · simp only [s₂, s₁, v_setV_of_ne _ _ hr]
  · refine ⟨s₁, ?_, fun b hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [keyBcast, ite_eq_right hp, List.append_nil, runBlock_cons, exec_dupE _ _ _ (by omega_arith),
        runStep_some, runBlock_nil]
    · rw [key b hb, VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hk, show k / 2 * 2 = k by omega_arith]
    · simp only [s₁, v_setV_of_ne _ _ hr]

/-! ## A reverse mix on a set -/

theorem wreg_mod (h i : Nat) : wreg h i = wreg h (i % 4) := by simp [wreg]

theorem mixRegs (h i : Nat) (hh : h < 2) (hi : i < 4) :
    MixRegs (wreg h i) (wreg h (i + 1)) (wreg h (i + 2)) (wreg h (i + 3)) (tmp h 0) (tmp h 1)
      (tmp h 2) := by
  constructor <;> (revert hi; revert i; revert hh; revert h; decide)

/-- The registers a set's reverse mix writes, and the set's other words. -/
theorem regs_other (h i i' : Nat) (hh : h < 2) (hi : i < 4) (hi' : i' < 4) (he : i' ≠ i) :
    wreg h i' ≠ wreg h i ∧ wreg h i' ≠ tmp h 0 ∧ wreg h i' ≠ tmp h 1 ∧ wreg h i' ≠ tmp h 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (revert he; revert hi'; revert i'; revert hi; revert i; revert hh; revert h; decide)

/-- The registers a set's reverse mix writes, and the other set's words. -/
theorem regs_cross (h i i' : Nat) (hh : h < 2) (hi : i < 4) (hi' : i' < 4) :
    wreg (1 - h) i' ≠ wreg h i ∧ wreg (1 - h) i' ≠ tmp h 0 ∧ wreg (1 - h) i' ≠ tmp h 1 ∧
      wreg (1 - h) i' ≠ tmp h 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (revert hi'; revert i'; revert hi; revert i; revert hh; revert h; decide)

/-- The registers a set's reverse mix writes, and the key, mask and schedule. -/
theorem regs_fixed (h i : Nat) (hh : h < 2) (hi : i < 4) :
    kb ≠ wreg h i ∧ m16 ≠ wreg h i ∧ m16 ≠ tmp h 0 ∧ m16 ≠ tmp h 1 ∧ m16 ≠ tmp h 2 ∧
      kb ≠ tmp h 0 ∧ kb ≠ tmp h 1 ∧ kb ≠ tmp h 2 ∧
      (∀ r < 8, treg r ≠ wreg h i ∧ treg r ≠ tmp h 0 ∧ treg r ≠ tmp h 1 ∧ treg r ≠ tmp h 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    first
    | (revert hr; revert r; revert hi; revert i; revert hh; revert h; decide)
    | (revert hi; revert i; revert hh; revert h; decide)

theorem getD_set (v : Spec.Rc2.State) {i i' : Nat} (hi' : i' < 4) (x : BitVec 16) :
    (v.set! i x).getD i' 0 = if i' = i then x else v.getD i' 0 := by
  rw [vector_getD _ i' hi', vector_getD _ i' hi', Vector.getElem_set! hi']
  by_cases h : i' = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem rmix_ok {s : State} {h i : Nat} (hh : h < 2) (hi : i < 4) {vs : Nat → Spec.Rc2.State}
    (hv : VWords s h vs) {K : BitVec 16} (hk : ∀ b < 4, lw (s.v kb) b = K)
    (hm : s.v m16 = mask16) (k : Spec.Rc2.Schedule) {j : Nat} (hK : k.getD j 0 = K) :
    ∃ s', runBlock isa (rmix h i) s = some s' ∧
      VWords s' h (fun b => Spec.Rc2.reverseMix k j i (vs b)) ∧
      (∀ r, r ≠ wreg h i → r ≠ tmp h 0 → r ≠ tmp h 1 → r ≠ tmp h 2 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hn := VG.Proof.Rc2.AArch64.rotation_bounds i
  obtain ⟨s', run, lane, other, g, me, rd, wr, sp⟩ :=
    rmixCode_ok (s := s) (mixRegs h i hh hi) hn.1 hn.2 hm
  refine ⟨s', by rw [rmix_eq]; exact run, fun i' hi' b hb => ?_, other, g, me, rd, wr, sp⟩
  simp only [Spec.Rc2.reverseMix]
  rw [getD_set _ hi']
  by_cases he : i' = i
  · subst he
    rw [ite_eq_left rfl, lane b hb, hk b hb, hv i' hi' b hb, wreg_mod h (i' + 3), wreg_mod h (i' + 2),
      wreg_mod h (i' + 1), hv _ (Nat.mod_lt _ (by decide)) b hb, hv _ (Nat.mod_lt _ (by decide)) b hb,
      hv _ (Nat.mod_lt _ (by decide)) b hb, hK]
  · obtain ⟨o1, o2, o3, o4⟩ := regs_other h i i' hh hi hi' he
    rw [ite_eq_right he, other _ o1 o2 o3 o4, hv i' hi' b hb]

/-! ## A reverse mixing round on both sets -/

/-- The words of both sets: block `b` of the eight is `vs b`. -/
def Sets (s : State) (vs : Nat → Spec.Rc2.State) : Prop :=
  ∀ h < 2, VWords s h (fun b => vs (4 * h + b))

/-- What the rounds keep: the general registers but `x9` and `x6`, memory,
the regions, the stack pointer, the schedule and the mask. -/
structure VKeep (s s' : State) : Prop where
  keep : Keep [.x9, .x6] s s'
  sp : s'.sp = s.sp
  sched : ∀ r < 8, s'.v (treg r) = s.v (treg r)
  mask : s'.v m16 = s.v m16

theorem VKeep.trans {s s' s'' : State} (h : VKeep s s') (h' : VKeep s' s'') : VKeep s s'' :=
  ⟨h.keep.trans h'.keep, h'.sp.trans h.sp, fun r hr => (h'.sched r hr).trans (h.sched r hr),
    h'.mask.trans h.mask⟩

theorem SchedV.keep {s s' : State} {m : Mem} {p : Addr} (hs : SchedV s m p) (h : VKeep s s') :
    SchedV s' m p := fun r hr => (h.sched r hr).trans (hs r hr)

theorem VWords.keep {s s' : State} {h : Nat} {vs : Nat → Spec.Rc2.State} (hv : VWords s h vs)
    (hk : ∀ i < 4, s'.v (wreg h i) = s.v (wreg h i)) : VWords s' h vs :=
  fun i hi b hb => by rw [hk i hi]; exact hv i hi b hb

theorem treg_ne_kb : ∀ r < 8, treg r ≠ kb ∧ treg r ≠ m16 := by decide

/-- Key word `4 j + i` broadcast, and word `i` of both sets reverse mixed. -/
theorem mixStep_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p) (hm : s.v m16 = mask16)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) {j i : Nat} (hi : i < 4) (hj : j < 16) :
    ∃ s', runBlock isa (keyBcast (4 * j + i) ++ rmix 0 i ++ rmix 1 i) s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i (vs b)) ∧
      VKeep s s' := by
  obtain ⟨s₁, r₁, k₁, o₁, g₁, me₁, rd₁, wr₁, sp₁⟩ := keyBcast_ok hs (k := 4 * j + i) (by omega_arith)
  have v₁ : Sets s₁ vs := fun h hh =>
    (hv h hh).keep fun i' hi' => o₁ _ (regs_fixed h i' hh hi').1.symm
  have m₁ : s₁.v m16 = mask16 := (o₁ m16 (by decide)).trans hm
  obtain ⟨s₂, r₂, w₂, o₂, g₂, me₂, rd₂, wr₂, sp₂⟩ :=
    rmix_ok (h := 0) (by decide) hi (v₁ 0 (by decide)) k₁ m₁ (Spec.Rc2.scheduleAt m p) rfl
  have f₀ := regs_fixed 0 i (by decide) hi
  have k₂ : ∀ b < 4, lw (s₂.v kb) b = (Spec.Rc2.scheduleAt m p).getD (4 * j + i) 0 := by
    intro b hb; rw [o₂ kb f₀.1 f₀.2.2.2.2.2.1 f₀.2.2.2.2.2.2.1 f₀.2.2.2.2.2.2.2.1]; exact k₁ b hb
  have m₂ : s₂.v m16 = mask16 := by
    rw [o₂ m16 f₀.2.1 f₀.2.2.1 f₀.2.2.2.1 f₀.2.2.2.2.1]; exact m₁
  have v₂ : VWords s₂ 1 (fun b => vs (4 * 1 + b)) := (v₁ 1 (by decide)).keep fun i' hi' => by
    obtain ⟨a, b, c, d⟩ := regs_cross 0 i i' (by decide) hi hi'
    exact o₂ _ a b c d
  obtain ⟨s₃, r₃, w₃, o₃, g₃, me₃, rd₃, wr₃, sp₃⟩ :=
    rmix_ok (h := 1) (by decide) hi v₂ k₂ m₂ (Spec.Rc2.scheduleAt m p) rfl
  have f₁ := regs_fixed 1 i (by decide) hi
  have w₃' : VWords s₃ 0 (fun b => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i
      (vs (4 * 0 + b))) := w₂.keep fun i' hi' => by
    obtain ⟨a, b, c, d⟩ := regs_cross 1 i i' (by decide) hi hi'
    exact o₃ _ a b c d
  refine ⟨s₃, runBlock_cat_some (runBlock_cat_some r₁ r₂) r₃, fun h hh => ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · match h, hh with
    | 0, _ => exact w₃'
    | 1, _ => exact w₃
  · exact ⟨fun r _ => by rw [g₃, g₂, g₁], by rw [me₃, me₂, me₁], by rw [rd₃, rd₂, rd₁],
      by rw [wr₃, wr₂, wr₁]⟩
  · rw [sp₃, sp₂, sp₁]
  · intro r hr
    have f₀ := f₀.2.2.2.2.2.2.2.2 r hr
    have f₁ := f₁.2.2.2.2.2.2.2.2 r hr
    rw [o₃ _ f₁.1 f₁.2.1 f₁.2.2.1 f₁.2.2.2, o₂ _ f₀.1 f₀.2.1 f₀.2.2.1 f₀.2.2.2,
      o₁ _ (treg_ne_kb r hr).1]
  · rw [o₃ m16 f₁.2.1 f₁.2.2.1 f₁.2.2.2.1 f₁.2.2.2.2.1, o₂ m16 f₀.2.1 f₀.2.2.1 f₀.2.2.2.1
      f₀.2.2.2.2.1, o₁ m16 (by decide)]

theorem mixSteps_ok {m : Mem} {p : Addr} {j : Nat} (hj : j < 16) (is : List Nat)
    (his : ∀ i ∈ is, i < 4) {s : State} (hs : SchedV s m p) (hm : s.v m16 = mask16)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (is.flatMap fun i => keyBcast (4 * j + i) ++ rmix 0 i ++ rmix 1 i) s =
        some s' ∧
      Sets s' (fun b => is.foldl (fun r i =>
        Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i r) (vs b)) ∧
      VKeep s s' := by
  induction is generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons i is ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := mixStep_ok hs hm hv (his i (by simp)) hj
    obtain ⟨s₂, r₂, v₂, k₂⟩ := ih (fun i hi => his i (by simp [hi])) (hs.keep k₁)
      (k₁.mask.trans hm) v₁
    exact ⟨s₂, by rw [List.flatMap_cons]; exact runBlock_cat_some r₁ r₂, v₂, k₁.trans k₂⟩

theorem rmixRound_ok {m : Mem} {p : Addr} {j : Nat} (hj : j < 16) {s : State}
    (hs : SchedV s m p) (hm : s.v m16 = mask16) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (rmixRound j) s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt m p) j (vs b)) ∧
      VKeep s s' :=
  mixSteps_ok hj [3, 2, 1, 0] (by decide) hs hm hv

end VG.Proof.Rc2.AArch64.Vec

end

end

/-!
# Reverse mashing on eight blocks

`rmash_ok`: the reverse mash of word `i` of a set. Each lane's index is the
low six bits of the word before it, made into the bytes `2 j`, `2 j + 1`
(`514 j + 256`), which `select false` looks up in the schedule; the lane's
low 16 bits are then the schedule word `j`.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

theorem exec_mul4 (s : State) (d n m : VReg) :
    exec (.vop (.mul d n m)) s = some (s.setV d (VArr.s4.map2 (fun _ x y => x * y) (s.v n) (s.v m))) :=
  rfl

theorem exec_add4 (s : State) (d n m : VReg) :
    exec (.vop (.add .s4 d n m)) s = some (s.setV d (VArr.s4.map2 (fun _ x y => x + y) (s.v n) (s.v m))) :=
  rfl

/-- Byte `c` of lane `b`. -/
theorem vbyte_lane (x : BitVec 128) {b c : Nat} (hc : c < 4) :
    vbyte x (4 * b + c) = (vword x b).extractLsb' (8 * c) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp [vbyte, vword, ht, show 8 * c + t < 32 by omega_arith,
    show 8 * (4 * b + c) + t = 32 * b + (8 * c + t) by omega_arith]

/-- A lane's index: `514 j + 256`, `j` the low six bits of its word. -/
theorem index_lane (x : BitVec 32) :
    (x &&& (BitVec.ofNat 64 63).setWidth 32) * (BitVec.ofNat 64 514).setWidth 32 +
        (BitVec.ofNat 64 256).setWidth 32 =
      BitVec.ofNat 32 (256 + 514 * (x.setWidth 16 &&& 63).toNat) := by
  have a : ∀ n : Nat, n &&& 63 = n % 64 := fun n => Nat.and_two_pow_sub_one_eq_mod n 6
  rw [show (BitVec.ofNat 64 63).setWidth 32 = (63 : BitVec 32) from rfl,
    show (BitVec.ofNat 64 514).setWidth 32 = (514 : BitVec 32) from rfl,
    show (BitVec.ofNat 64 256).setWidth 32 = (256 : BitVec 32) from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, show (63 : BitVec 32).toNat = 63 from rfl,
    show (63 : BitVec 16).toNat = 63 from rfl, show (514 : BitVec 32).toNat = 514 from rfl,
    show (256 : BitVec 32).toNat = 256 from rfl, a, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 16)]
  have : x.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  generalize x.toNat % 64 = y at *
  omega_arith

theorem index_lt (x : BitVec 16) : (x &&& 63).toNat < 64 := by
  rw [BitVec.toNat_and, show (63 : BitVec 16).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem vword_dup4 (w : BitVec 32) {b : Nat} (hb : b < 4) : vword (ofVWords w w w w) b = w := by
  rw [vword_ofVWords _ _ _ _ hb]
  rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- A block keeps the stack pointer. -/
theorem runBlock_sp {is : List Instr} {s s' : State} (hr : runBlock isa is s = some s') :
    s'.sp = s.sp := by
  induction is generalizing s with
  | nil => cases hr; rfl
  | cons i is ih =>
    cases he : exec i s with
    | none => rw [runBlock_cons, he] at hr; cases hr
    | some u => rw [runBlock_cons, he, runStep_some] at hr; rw [ih hr]; exact exec_sp he

theorem wreg_ne (h i : Nat) (hh : h < 2) : wreg h i ≠ .v0 ∧ wreg h i ≠ .v1 ∧ wreg h i ≠ .v2 ∧
    wreg h i ≠ .v3 ∧ wreg h i ≠ .v4 ∧ wreg h i ≠ .v5 ∧ wreg h i ≠ .v6 ∧ wreg h i ≠ .v7 :=
  treg_ne8 (8 + 4 * h + i % 4) (by omega_arith)

theorem rmash_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p) {h i : Nat} (hh : h < 2)
    (hi : i < 4) {vs : Nat → Spec.Rc2.State} (hv : VWords s h vs) :
    ∃ s', runBlock isa (rmash h i) s = some s' ∧
      VWords s' h (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i (vs b)) ∧
      (∀ r, r ≠ wreg h i → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 →
        s'.v r = s.v r) ∧
      Keep [.x9, .x6] s s' ∧ s'.sp = s.sp := by
  have wn := wreg_ne h (i + 3) hh
  let W := s.v (wreg h (i + 3))
  let s₁ := s.write .x .x9 (BitVec.ofNat 64 63)
  let s₂ := s₁.setV .v1 (ofVWords ((s₁.gpr .x9).setWidth 32) ((s₁.gpr .x9).setWidth 32)
    ((s₁.gpr .x9).setWidth 32) ((s₁.gpr .x9).setWidth 32))
  let s₃ := s₂.setV .v0 (s₂.v (wreg h (i + 3)) &&& s₂.v .v1)
  let s₄ := s₃.write .x .x9 (BitVec.ofNat 64 514)
  let s₅ := s₄.setV .v4 (ofVWords ((s₄.gpr .x9).setWidth 32) ((s₄.gpr .x9).setWidth 32)
    ((s₄.gpr .x9).setWidth 32) ((s₄.gpr .x9).setWidth 32))
  let s₆ := s₅.setV .v0 (VArr.s4.map2 (fun _ x y => x * y) (s₅.v .v0) (s₅.v .v4))
  let s₇ := s₆.write .x .x9 (BitVec.ofNat 64 256)
  let s₈ := s₇.setV .v1 (ofVWords ((s₇.gpr .x9).setWidth 32) ((s₇.gpr .x9).setWidth 32)
    ((s₇.gpr .x9).setWidth 32) ((s₇.gpr .x9).setWidth 32))
  let s₉ := s₈.setV .v0 (VArr.s4.map2 (fun _ x y => x + y) (s₈.v .v0) (s₈.v .v1))
  have run₉ : runBlock isa ([imm .x9 63, .vop (.dup .s4 .v1 .x9),
      .vop (.logic .and .v0 (wreg h (i + 3)) .v1), imm .x9 514, .vop (.dup .s4 .v4 .x9),
      .vop (.mul .v0 .v0 .v4), imm .x9 256, .vop (.dup .s4 .v1 .x9),
      .vop (.add .s4 .v0 .v0 .v1)] : List Instr) s = some s₉ := by
    rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups,
      runStep_some, runBlock_cons, exec_and, runStep_some, runBlock_cons,
      exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups, runStep_some,
      runBlock_cons, exec_mul4, runStep_some, runBlock_cons, exec_imm _ _ _ (by decide),
      runStep_some, runBlock_cons, exec_dups, runStep_some, runBlock_cons, exec_add4,
      runStep_some, runBlock_nil]
  -- The index of each lane.
  let J (b : Nat) : Nat := (lw W b &&& 63).toNat
  have l₉ : ∀ b < 4, vword (s₉.v .v0) b = BitVec.ofNat 32 (256 + 514 * J b) := by
    intro b hb
    have : vword (s₉.v .v0) b = (vword W b &&& (BitVec.ofNat 64 63).setWidth 32) *
        (BitVec.ofNat 64 514).setWidth 32 + (BitVec.ofNat 64 256).setWidth 32 := by
      simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_self, v_write,
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v4),
        v_setV_of_ne _ _ wn.2.1, gpr_write_self, BitVec.setWidth_eq,
        vword_map2 _ _ _ hb, vword_and, vword_dup4 _ hb]
      rfl
    rw [this, index_lane]
  let I : Nat → BitVec 8 := fun e => vbyte (s₉.v .v0) e
  have hI : ∀ e < 16, (I e).toNat =
      if e % 4 = 0 then 2 * J (e / 4) else if e % 4 = 1 then 2 * J (e / 4) + 1 else 0 := by
    intro e he
    simp only [I]
    rw [show e = 4 * (e / 4) + e % 4 by omega_arith, vbyte_lane _ (by omega_arith), l₉ _ (by omega_arith),
      show (4 * (e / 4) + e % 4) / 4 = e / 4 by omega_arith, show (4 * (e / 4) + e % 4) % 4 = e % 4 by omega_arith]
    exact index_bytes _ (index_lt _) e
  obtain ⟨d, rund, d1, _, dv, dk⟩ := quarters_run false s₉
  have d0 : d.v .v0 = s₉.v .v0 := dv _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨f, runf, f0, fv⟩ := select_half_run (s := d) I
    (fun e he => by
      have : J (e / 4) < 64 := index_lt _
      rw [hI e he]; split <;> (try split) <;> omega_arith)
    (fun e he => by rw [d0])
    (fun e he => by rw [d1 e he])
  let s' := f.setV (wreg h i) (VArr.s4.map2 (fun _ x y => x - y) (f.v (wreg h i)) (f.v .v0))
  -- Everything but `v0`–`v5` is kept up to the subtraction.
  have keepV : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 →
      f.v r = s.v r := by
    intro r a0 a1 a2 a3 a4 a5
    rw [fv.2 r (by simp [a0, a1, a2, a3]), dv r a1 a2 a3 a4 a5]
    simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ a0, v_setV_of_ne _ _ a1,
      v_setV_of_ne _ _ a4, v_write]
  have tab : ∀ k < 128, tbyte d.v k = m (p + BitVec.ofNat 64 k) := by
    intro k hk
    have : ∀ a < 16, d.v (treg a) = s.v (treg a) := by
      intro a ha
      obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 a ha
      rw [dv _ a1 a2 a3 a4 a5]
      simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ a0, v_setV_of_ne _ _ a1,
        v_setV_of_ne _ _ a4, v_write]
    rw [tbyte_congr' this _ (by omega_arith)]
    exact tbyte_loaded m p hs k hk
  have run : runBlock isa (rmash h i) s = some s' :=
    runBlock_cat_some (runBlock_cat_some (runBlock_cat_some run₉ rund) runf)
      (by rw [runBlock_cons, exec_sub4, runStep_some, runBlock_nil])
  refine ⟨s', run, fun i' hi' b hb => ?_, fun r h0 a0 a1 a2 a3 a4 a5 => ?_, ?_, runBlock_sp run⟩
  · have wi := wreg_ne h i hh
    simp only [Spec.Rc2.reverseMash]
    rw [getD_set _ hi']
    by_cases he : i' = i
    · subst he
      rw [ite_eq_left rfl]
      have hw : lw (f.v .v0) b = (Spec.Rc2.scheduleAt m p).getD (J b) 0 := by
        have hj : J b < 64 := index_lt _
        have e0 : (I (4 * b)).toNat = 2 * J b := by
          rw [hI _ (by omega_arith), show 4 * b % 4 = 0 by omega_arith, show 4 * b / 4 = b by omega_arith]; rfl
        have e1 : (I (4 * b + 1)).toNat = 2 * J b + 1 := by
          rw [hI _ (by omega_arith), show (4 * b + 1) % 4 = 1 by omega_arith,
            show (4 * b + 1) / 4 = b by omega_arith]; rfl
        rw [lw_bytes, f0 _ (by omega_arith), f0 _ (by omega_arith), e0, e1, tab _ (by omega_arith),
          tab _ (by omega_arith), scheduleAt_getD _ _ _ hj]
      have : lw (s'.v (wreg h i')) b = lw (s.v (wreg h i')) b - lw (f.v .v0) b := by
        simp only [s', lw, v_setV_self, vword_map2 _ _ _ hb]
        rw [setWidth16_sub, keepV _ wi.1 wi.2.1 wi.2.2.1 wi.2.2.2.1 wi.2.2.2.2.1 wi.2.2.2.2.2.1]
      have hJ : J b = ((vs b).getD ((i' + 3) % 4) 0 &&& 63).toNat := by
        simp only [J, W]; rw [wreg_mod h (i' + 3), hv _ (Nat.mod_lt _ (by decide)) b hb]
      rw [this, hw, hv i' hi' b hb, hJ]
    · obtain ⟨o1, -, -, -⟩ := regs_other h i i' hh hi hi' he
      have wi' := wreg_ne h i' hh
      rw [ite_eq_right he, ← hv i' hi' b hb]
      simp only [s', v_setV_of_ne _ _ o1]
      rw [keepV _ wi'.1 wi'.2.1 wi'.2.2.1 wi'.2.2.2.1 wi'.2.2.2.2.1 wi'.2.2.2.2.2.1]
  · simp only [s', v_setV_of_ne _ _ h0]
    exact keepV r a0 a1 a2 a3 a4 a5
  · have k₉ : Keep [.x9, .x6] s s₉ :=
      ⟨fun r hr => by
        have h9 : ¬r = .x9 := fun e => hr (by simp [e])
        simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, gpr_setV, gpr_write_of_ne _ _ _ h9],
        rfl, rfl, rfl⟩
    exact k₉.trans ((dk.weaken (by simp)).trans
      ⟨fun r _ => by simp only [s', gpr_setV, fv.gpr], by simp only [s', mem_setV, fv.mem],
        by simp only [s', rd_setV, fv.rd], by simp only [s', wr_setV, fv.wr]⟩)

end VG.Proof.Rc2.AArch64.Vec
