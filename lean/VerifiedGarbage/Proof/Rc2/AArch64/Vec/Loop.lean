import VerifiedGarbage.Impl.Rc2.AArch64.CbcVec
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Rc2.AArch64.Block
import VerifiedGarbage.Proof.Rc2.Stream

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Lanes`. -/
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

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64.Vec

/-- The low 16 bits of lane `b`. -/
abbrev lw (x : BitVec 128) (b : Nat) : BitVec 16 := (vword x b).setWidth 16

/-- The words of set `h`: word `i` of block `b` is `vs b`'s. -/
def VWords (s : State) (h : Nat) (vs : Nat → Spec.Rc2.State) : Prop :=
  ∀ i < 4, ∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (s.v (wreg h i)) b = (vs b).getD i 0

theorem vword_and (x y : BitVec 128) (c : Nat) : vword (x &&& y) c = vword x c &&& vword y c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_and]

theorem vword_bic (x y : BitVec 128) (c : Nat) :
    vword (x &&& ~~~y) c = vword x c &&& ~~~vword y c := by
  ext i hi
  simp only [vword, BitVec.getElem_extractLsb', BitVec.getElem_and, BitVec.getElem_not,
    BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h : 32 * c + i < 128
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x (32 * c + i) (by omega)]

theorem vword_not (x : BitVec 128) {c : Nat} (hc : c < 4) : vword (~~~x) c = ~~~vword x c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_not, show 32 * c + i < 128 by omega]

theorem vword_xor (x y : BitVec 128) (c : Nat) : vword (x ^^^ y) c = vword x c ^^^ vword y c := by
  simp only [vword, BitVec.extractLsb'_xor]

theorem vword_or (x y : BitVec 128) (c : Nat) : vword (x ||| y) c = vword x c ||| vword y c := by
  ext i hi
  simp [vword, BitVec.getElem_extractLsb', BitVec.getElem_or]

theorem setWidth16_sub (x y : BitVec 32) : (x - y).setWidth 16 = x.setWidth 16 - y.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub]
  omega

theorem setWidth16_and (x y : BitVec 32) : (x &&& y).setWidth 16 = x.setWidth 16 &&& y.setWidth 16 := by
  ext i hi; simp

theorem setWidth16_not (x : BitVec 32) : (~~~x).setWidth 16 = ~~~(x.setWidth 16) := by
  ext i hi; simp [show i < 32 by omega]

theorem bit65535 (k : Nat) : (65535 : BitVec 32).getLsbD k = decide (k < 16) := by
  rw [show (65535 : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases h : k < 16
  · simp [h, show k < 32 by omega]
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
    BitVec.getLsbD_rotateRight, hj, decide_true, Bool.true_and, Nat.mod_eq_of_lt h2, VG.Proof.Rc2.AArch64.Vec.bit65535]
  by_cases hs : j < 16 - s
  · simp (disch := omega) [hs, show j < 32 by omega, show s + j < 16 by omega]
  · simp (disch := omega) [hs, show j < 32 by omega, show ¬ s + j < 16 by omega,
      show j - (16 - s) < 16 by omega]

end VG.Proof.Rc2.AArch64.Vec

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Mix`. -/
section

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

theorem vword_mask16 {b : Nat} (hb : b < 4) : vword VG.Proof.Rc2.AArch64.Vec.mask16 b = 65535 := by
  rw [VG.Proof.Rc2.AArch64.Vec.mask16, vword_ofVWords _ _ _ _ hb]
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
    VG.Proof.Rc2.AArch64.Vec.rmixCode (wreg h i) (wreg h (i + 1)) (wreg h (i + 2)) (wreg h (i + 3)) (tmp h 0) (tmp h 1)
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
  rw [VG.Proof.Rc2.AArch64.Vec.setWidth16_sub, VG.Proof.Rc2.AArch64.Vec.setWidth16_sub, VG.Proof.Rc2.AArch64.Vec.setWidth16_sub, VG.Proof.Rc2.AArch64.Vec.ror_lane x h1 h2, VG.Proof.Rc2.AArch64.Vec.setWidth16_and,
    VG.Proof.Rc2.AArch64.Vec.setWidth16_and, VG.Proof.Rc2.AArch64.Vec.setWidth16_not, BitVec.and_comm (c.setWidth 16)]

theorem rmixCode_ok {s : State} {w a1 a2 a3 t u v : VReg} (hr : VG.Proof.Rc2.AArch64.Vec.MixRegs w a1 a2 a3 t u v)
    {sh : Nat} (h1 : 1 ≤ sh) (h2 : sh < 16) (hm : s.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16) :
    ∃ s', runBlock isa (VG.Proof.Rc2.AArch64.Vec.rmixCode w a1 a2 a3 t u v sh) s = some s' ∧
      (∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (s'.v w) b =
        (VG.Proof.Rc2.AArch64.Vec.lw (s.v w) b).rotateRight sh - VG.Proof.Rc2.AArch64.Vec.lw (s.v kb) b - (VG.Proof.Rc2.AArch64.Vec.lw (s.v a3) b &&& VG.Proof.Rc2.AArch64.Vec.lw (s.v a2) b) -
          (~~~(VG.Proof.Rc2.AArch64.Vec.lw (s.v a3) b) &&& VG.Proof.Rc2.AArch64.Vec.lw (s.v a1) b)) ∧
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
  · rw [VG.Proof.Rc2.AArch64.Vec.rmixCode, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_and, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_shift _ _ _ _ _ _ ok1,
      runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_shift _ _ _ _ _ _ ok2, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_and,
      runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_bic, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_sub4, runStep_some,
      runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_sub4, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_sub4, runStep_some, runBlock_nil]
  · -- The values of the registers along the way.
    have w1 : s₁.v w = s.v w &&& VG.Proof.Rc2.AArch64.Vec.mask16 := by simp only [s₁, v_setV_self, hm]
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
      simp only [vword_map2 _ _ _ hb, VG.Proof.Rc2.AArch64.Vec.vword_and, VG.Proof.Rc2.AArch64.Vec.vword_not _ hb, VG.Proof.Rc2.AArch64.Vec.vword_mask16 hb, VShiftOp.eval]
    rw [VG.Proof.Rc2.AArch64.Vec.lw, lane]
    exact VG.Proof.Rc2.AArch64.Vec.rmixLane _ _ _ _ _ h1 h2
  · simp only [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2,
      v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h4]

end VG.Proof.Rc2.AArch64.Vec

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Round`. -/
section

/-!
# Reverse mixing rounds on eight blocks

The schedule is in `v16`–`v23` (`SchedV`); `keyBcast_ok` broadcasts a key
word from it, `rmix_ok` is a reverse mix on a set (`VWords`), and
`rmixRound_ok` a reverse mixing round on both sets.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- The schedule at `p` in `v16`–`v23`. -/
def SchedV (s : State) (m : Mem) (p : Addr) : Prop :=
  ∀ r < 8, s.v (treg r) = m.read (p + BitVec.ofNat 64 (16 * r)) 16

/-- A lane's low 16 bits are its first two bytes. -/
theorem lw_bytes (x : BitVec 128) (b : Nat) :
    VG.Proof.Rc2.AArch64.Vec.lw x b = (vbyte x (4 * b)).setWidth 16 ||| (vbyte x (4 * b + 1)).setWidth 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  simp only [VG.Proof.Rc2.AArch64.Vec.lw, vword, vbyte, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and]
  by_cases h8 : t < 8
  · simp [h8, show t < 32 by omega, show 8 * (4 * b) + t = 32 * b + t by omega]
  · simp [h8, show t < 32 by omega, show t - 8 < 8 by omega, show t - 8 < 16 by omega,
      show 8 * (4 * b + 1) + (t - 8) = 32 * b + t by omega]

theorem exec_dupE (s : State) (d n : VReg) {i : Nat} (hi : i < 4) :
    exec (.vop (.dupE .s4 d n i)) s =
      some (s.setV d (VArr.s4.map2 (fun w _ _ => (s.v n).extractLsb' (w * i) w) 0 0)) := by
  simp [exec, VOp.eval, VArr.esize, show i < 4 from hi]

theorem exec_rev (s : State) (op : VRevOp) (d n : VReg) :
    exec (.vop (.rev op d n)) s = some (s.setV d (op.eval (s.v n))) := rfl

theorem vbyte_read (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    vbyte (m.read a 16) e = m (a + BitVec.ofNat 64 e) := Mem.extractLsb'_read m a he

/-- Key word `k` broadcast. -/
theorem keyBcast_ok {s : State} {m : Mem} {p : Addr} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p) {k : Nat} (hk : k < 64) :
    ∃ s', runBlock isa (keyBcast k) s = some s' ∧
      (∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (s'.v kb) b = (Spec.Rc2.scheduleAt m p).getD k 0) ∧
      (∀ r, r ≠ kb → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let S := s.v (treg (k / 8))
  let D : BitVec 128 := VArr.s4.map2 (fun w _ _ => S.extractLsb' (w * (k % 8 / 2)) w) 0 0
  let s₁ := s.setV kb D
  have hS : S = m.read (p + BitVec.ofNat 64 (16 * (k / 8))) 16 := hs _ (by omega)
  -- Byte `e` of lane `b` of the broadcast.
  have dB : ∀ b < 4, ∀ e < 4, vbyte D (4 * b + e) = m (p + BitVec.ofNat 64 (2 * (k / 2 * 2) + e)) := by
    intro b hb e he
    have hv : vword D b = vword S (k % 8 / 2) := by
      simp only [D, vword_map2 _ _ _ hb]; rfl
    have : vbyte D (4 * b + e) = (vword D b).extractLsb' (8 * e) 8 := by
      apply BitVec.eq_of_getLsbD_eq; intro t ht
      simp [vbyte, vword, ht, show 8 * e + t < 32 by omega, show 8 * (4 * b + e) + t = 32 * b + (8 * e + t) by omega]
    rw [this, hv]
    have : (vword S (k % 8 / 2)).extractLsb' (8 * e) 8 = vbyte S (4 * (k % 8 / 2) + e) := by
      apply BitVec.eq_of_getLsbD_eq; intro t ht
      simp [vbyte, vword, ht, show 8 * e + t < 32 by omega,
        show 8 * (4 * (k % 8 / 2) + e) + t = 32 * (k % 8 / 2) + (8 * e + t) by omega]
    rw [this, hS, VG.Proof.Rc2.AArch64.Vec.vbyte_read _ _ (by omega), Offset.add_add,
      show 16 * (k / 8) + (4 * (k % 8 / 2) + e) = 2 * (k / 2 * 2) + e by omega]
  have key : ∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (s₁.v kb) b = (m (p + BitVec.ofNat 64 (2 * (k / 2 * 2)))).setWidth 16 |||
      (m (p + BitVec.ofNat 64 (2 * (k / 2 * 2) + 1))).setWidth 16 <<< 8 := by
    intro b hb
    rw [show s₁.v kb = D from v_setV_self _ _ _, VG.Proof.Rc2.AArch64.Vec.lw_bytes _ b,
      show 4 * b = 4 * b + 0 by omega, dB b hb 0 (by decide), dB b hb 1 (by decide)]
    rfl
  by_cases hp : k % 2 = 1
  · let s₂ := s₁.setV kb (VRevOp.rev32h.eval (s₁.v kb))
    refine ⟨s₂, ?_, fun b hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [keyBcast, ite_eq_left hp, List.singleton_append, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_dupE _ _ _ (by omega),
        runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_rev, runStep_some, runBlock_nil]
    · rw [show s₂.v kb = VRevOp.rev32h.eval (s₁.v kb) from v_setV_self _ _ _, VG.Proof.Rc2.AArch64.Vec.lw_bytes _ b,
        VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hk]
      simp only [VRevOp.eval, vbyte_ofVBytes _ (show 4 * b < 16 by omega),
        vbyte_ofVBytes _ (show 4 * b + 1 < 16 by omega),
        show 4 * (4 * b / 4) + (4 * b % 4 + 2) % 4 = 4 * b + 2 by omega,
        show 4 * ((4 * b + 1) / 4) + ((4 * b + 1) % 4 + 2) % 4 = 4 * b + 3 by omega]
      rw [show s₁.v kb = D from v_setV_self _ _ _, dB b hb 2 (by decide), dB b hb 3 (by decide),
        show 2 * (k / 2 * 2) + 2 = 2 * k by omega, show 2 * (k / 2 * 2) + 3 = 2 * k + 1 by omega]
    · simp only [s₂, s₁, v_setV_of_ne _ _ hr]
  · refine ⟨s₁, ?_, fun b hb => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [keyBcast, ite_eq_right hp, List.append_nil, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_dupE _ _ _ (by omega),
        runStep_some, runBlock_nil]
    · rw [key b hb, VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hk, show k / 2 * 2 = k by omega]
    · simp only [s₁, v_setV_of_ne _ _ hr]

/-! ## A reverse mix on a set -/

theorem wreg_mod (h i : Nat) : wreg h i = wreg h (i % 4) := by simp [wreg]

theorem mixRegs (h i : Nat) (hh : h < 2) (hi : i < 4) :
    VG.Proof.Rc2.AArch64.Vec.MixRegs (wreg h i) (wreg h (i + 1)) (wreg h (i + 2)) (wreg h (i + 3)) (tmp h 0) (tmp h 1)
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
    (hv : VG.Proof.Rc2.AArch64.Vec.VWords s h vs) {K : BitVec 16} (hk : ∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (s.v kb) b = K)
    (hm : s.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16) (k : Spec.Rc2.Schedule) {j : Nat} (hK : k.getD j 0 = K) :
    ∃ s', runBlock isa (rmix h i) s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.VWords s' h (fun b => Spec.Rc2.reverseMix k j i (vs b)) ∧
      (∀ r, r ≠ wreg h i → r ≠ tmp h 0 → r ≠ tmp h 1 → r ≠ tmp h 2 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hn := VG.Proof.Rc2.AArch64.rotation_bounds i
  obtain ⟨s', run, lane, other, g, me, rd, wr, sp⟩ :=
    VG.Proof.Rc2.AArch64.Vec.rmixCode_ok (s := s) (VG.Proof.Rc2.AArch64.Vec.mixRegs h i hh hi) hn.1 hn.2 hm
  refine ⟨s', by rw [VG.Proof.Rc2.AArch64.Vec.rmix_eq]; exact run, fun i' hi' b hb => ?_, other, g, me, rd, wr, sp⟩
  simp only [Spec.Rc2.reverseMix]
  rw [VG.Proof.Rc2.AArch64.Vec.getD_set _ hi']
  by_cases he : i' = i
  · subst he
    rw [ite_eq_left rfl, lane b hb, hk b hb, hv i' hi' b hb, VG.Proof.Rc2.AArch64.Vec.wreg_mod h (i' + 3), VG.Proof.Rc2.AArch64.Vec.wreg_mod h (i' + 2),
      VG.Proof.Rc2.AArch64.Vec.wreg_mod h (i' + 1), hv _ (Nat.mod_lt _ (by decide)) b hb, hv _ (Nat.mod_lt _ (by decide)) b hb,
      hv _ (Nat.mod_lt _ (by decide)) b hb, hK]
  · obtain ⟨o1, o2, o3, o4⟩ := VG.Proof.Rc2.AArch64.Vec.regs_other h i i' hh hi hi' he
    rw [ite_eq_right he, other _ o1 o2 o3 o4, hv i' hi' b hb]

/-! ## A reverse mixing round on both sets -/

/-- The words of both sets: block `b` of the eight is `vs b`. -/
def Sets (s : State) (vs : Nat → Spec.Rc2.State) : Prop :=
  ∀ h < 2, VG.Proof.Rc2.AArch64.Vec.VWords s h (fun b => vs (4 * h + b))

/-- What the rounds keep: the general registers but `x9` and `x6`, memory,
the regions, the stack pointer, the schedule and the mask. -/
structure VKeep (s s' : State) : Prop where
  keep : Keep [.x9, .x6] s s'
  sp : s'.sp = s.sp
  sched : ∀ r < 8, s'.v (treg r) = s.v (treg r)
  mask : s'.v m16 = s.v m16

theorem VKeep.trans {s s' s'' : State} (h : VG.Proof.Rc2.AArch64.Vec.VKeep s s') (h' : VG.Proof.Rc2.AArch64.Vec.VKeep s' s'') : VG.Proof.Rc2.AArch64.Vec.VKeep s s'' :=
  ⟨h.keep.trans h'.keep, h'.sp.trans h.sp, fun r hr => (h'.sched r hr).trans (h.sched r hr),
    h'.mask.trans h.mask⟩

theorem SchedV.keep {s s' : State} {m : Mem} {p : Addr} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p) (h : VG.Proof.Rc2.AArch64.Vec.VKeep s s') :
    VG.Proof.Rc2.AArch64.Vec.SchedV s' m p := fun r hr => (h.sched r hr).trans (hs r hr)

theorem VWords.keep {s s' : State} {h : Nat} {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.VWords s h vs)
    (hk : ∀ i < 4, s'.v (wreg h i) = s.v (wreg h i)) : VG.Proof.Rc2.AArch64.Vec.VWords s' h vs :=
  fun i hi b hb => by rw [hk i hi]; exact hv i hi b hb

theorem treg_ne_kb : ∀ r < 8, treg r ≠ kb ∧ treg r ≠ m16 := by decide

/-- Key word `4 j + i` broadcast, and word `i` of both sets reverse mixed. -/
theorem mixStep_ok {s : State} {m : Mem} {p : Addr} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p) (hm : s.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16)
    {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) {j i : Nat} (hi : i < 4) (hj : j < 16) :
    ∃ s', runBlock isa (keyBcast (4 * j + i) ++ rmix 0 i ++ rmix 1 i) s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' := by
  obtain ⟨s₁, r₁, k₁, o₁, g₁, me₁, rd₁, wr₁, sp₁⟩ := VG.Proof.Rc2.AArch64.Vec.keyBcast_ok hs (k := 4 * j + i) (by omega)
  have v₁ : VG.Proof.Rc2.AArch64.Vec.Sets s₁ vs := fun h hh =>
    (hv h hh).keep fun i' hi' => o₁ _ (VG.Proof.Rc2.AArch64.Vec.regs_fixed h i' hh hi').1.symm
  have m₁ : s₁.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16 := (o₁ m16 (by decide)).trans hm
  obtain ⟨s₂, r₂, w₂, o₂, g₂, me₂, rd₂, wr₂, sp₂⟩ :=
    VG.Proof.Rc2.AArch64.Vec.rmix_ok (h := 0) (by decide) hi (v₁ 0 (by decide)) k₁ m₁ (Spec.Rc2.scheduleAt m p) rfl
  have f₀ := VG.Proof.Rc2.AArch64.Vec.regs_fixed 0 i (by decide) hi
  have k₂ : ∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (s₂.v kb) b = (Spec.Rc2.scheduleAt m p).getD (4 * j + i) 0 := by
    intro b hb; rw [o₂ kb f₀.1 f₀.2.2.2.2.2.1 f₀.2.2.2.2.2.2.1 f₀.2.2.2.2.2.2.2.1]; exact k₁ b hb
  have m₂ : s₂.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16 := by
    rw [o₂ m16 f₀.2.1 f₀.2.2.1 f₀.2.2.2.1 f₀.2.2.2.2.1]; exact m₁
  have v₂ : VG.Proof.Rc2.AArch64.Vec.VWords s₂ 1 (fun b => vs (4 * 1 + b)) := (v₁ 1 (by decide)).keep fun i' hi' => by
    obtain ⟨a, b, c, d⟩ := VG.Proof.Rc2.AArch64.Vec.regs_cross 0 i i' (by decide) hi hi'
    exact o₂ _ a b c d
  obtain ⟨s₃, r₃, w₃, o₃, g₃, me₃, rd₃, wr₃, sp₃⟩ :=
    VG.Proof.Rc2.AArch64.Vec.rmix_ok (h := 1) (by decide) hi v₂ k₂ m₂ (Spec.Rc2.scheduleAt m p) rfl
  have f₁ := VG.Proof.Rc2.AArch64.Vec.regs_fixed 1 i (by decide) hi
  have w₃' : VG.Proof.Rc2.AArch64.Vec.VWords s₃ 0 (fun b => Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i
      (vs (4 * 0 + b))) := w₂.keep fun i' hi' => by
    obtain ⟨a, b, c, d⟩ := VG.Proof.Rc2.AArch64.Vec.regs_cross 1 i i' (by decide) hi hi'
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
      o₁ _ (VG.Proof.Rc2.AArch64.Vec.treg_ne_kb r hr).1]
  · rw [o₃ m16 f₁.2.1 f₁.2.2.1 f₁.2.2.2.1 f₁.2.2.2.2.1, o₂ m16 f₀.2.1 f₀.2.2.1 f₀.2.2.2.1
      f₀.2.2.2.2.1, o₁ m16 (by decide)]

theorem mixSteps_ok {m : Mem} {p : Addr} {j : Nat} (hj : j < 16) (is : List Nat)
    (his : ∀ i ∈ is, i < 4) {s : State} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p) (hm : s.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16)
    {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) :
    ∃ s', runBlock isa (is.flatMap fun i => keyBcast (4 * j + i) ++ rmix 0 i ++ rmix 1 i) s =
        some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => is.foldl (fun r i =>
        Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt m p) (4 * j + i) i r) (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' := by
  induction is generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons i is ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := VG.Proof.Rc2.AArch64.Vec.mixStep_ok hs hm hv (his i (by simp)) hj
    obtain ⟨s₂, r₂, v₂, k₂⟩ := ih (fun i hi => his i (by simp [hi])) (hs.keep k₁)
      (k₁.mask.trans hm) v₁
    exact ⟨s₂, by rw [List.flatMap_cons]; exact runBlock_cat_some r₁ r₂, v₂, k₁.trans k₂⟩

theorem rmixRound_ok {m : Mem} {p : Addr} {j : Nat} (hj : j < 16) {s : State}
    (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p) (hm : s.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16) {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) :
    ∃ s', runBlock isa (rmixRound j) s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt m p) j (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' :=
  VG.Proof.Rc2.AArch64.Vec.mixSteps_ok hj [3, 2, 1, 0] (by decide) hs hm hv

end VG.Proof.Rc2.AArch64.Vec

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Mash`. -/
section

/-!
# Reverse mashing on eight blocks

`rmash_ok`: the reverse mash of word `i` of a set. Each lane's index is the
low six bits of the word before it, made into the bytes `2 j`, `2 j + 1`
(`514 j + 256`), which `select false` looks up in the schedule; the lane's
low 16 bits are then the schedule word `j`.
-/

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
  simp [vbyte, vword, ht, show 8 * c + t < 32 by omega,
    show 8 * (4 * b + c) + t = 32 * b + (8 * c + t) by omega]

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
  omega

theorem index_lt (x : BitVec 16) : (x &&& 63).toNat < 64 := by
  rw [BitVec.toNat_and, show (63 : BitVec 16).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem vword_dup4 (w : BitVec 32) {b : Nat} (hb : b < 4) : vword (ofVWords w w w w) b = w := by
  rw [vword_ofVWords _ _ _ _ hb]
  rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl <;> rfl

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
  treg_ne8 (8 + 4 * h + i % 4) (by omega)

theorem rmash_ok {s : State} {m : Mem} {p : Addr} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p) {h i : Nat} (hh : h < 2)
    (hi : i < 4) {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.VWords s h vs) :
    ∃ s', runBlock isa (rmash h i) s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.VWords s' h (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i (vs b)) ∧
      (∀ r, r ≠ wreg h i → r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 →
        s'.v r = s.v r) ∧
      Keep [.x9, .x6] s s' ∧ s'.sp = s.sp := by
  have wn := VG.Proof.Rc2.AArch64.Vec.wreg_ne h (i + 3) hh
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
      runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_and, runStep_some, runBlock_cons,
      exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dups, runStep_some,
      runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_mul4, runStep_some, runBlock_cons, exec_imm _ _ _ (by decide),
      runStep_some, runBlock_cons, exec_dups, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_add4,
      runStep_some, runBlock_nil]
  -- The index of each lane.
  let J (b : Nat) : Nat := (VG.Proof.Rc2.AArch64.Vec.lw W b &&& 63).toNat
  have l₉ : ∀ b < 4, vword (s₉.v .v0) b = BitVec.ofNat 32 (256 + 514 * J b) := by
    intro b hb
    have : vword (s₉.v .v0) b = (vword W b &&& (BitVec.ofNat 64 63).setWidth 32) *
        (BitVec.ofNat 64 514).setWidth 32 + (BitVec.ofNat 64 256).setWidth 32 := by
      simp only [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, v_setV_self, v_write,
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v4),
        v_setV_of_ne _ _ wn.2.1, gpr_write_self, BitVec.setWidth_eq,
        vword_map2 _ _ _ hb, VG.Proof.Rc2.AArch64.Vec.vword_and, VG.Proof.Rc2.AArch64.Vec.vword_dup4 _ hb]
      rfl
    rw [this, VG.Proof.Rc2.AArch64.Vec.index_lane]
  let I : Nat → BitVec 8 := fun e => vbyte (s₉.v .v0) e
  have hI : ∀ e < 16, (I e).toNat =
      if e % 4 = 0 then 2 * J (e / 4) else if e % 4 = 1 then 2 * J (e / 4) + 1 else 0 := by
    intro e he
    simp only [I]
    rw [show e = 4 * (e / 4) + e % 4 by omega, VG.Proof.Rc2.AArch64.Vec.vbyte_lane _ (by omega), l₉ _ (by omega),
      show (4 * (e / 4) + e % 4) / 4 = e / 4 by omega, show (4 * (e / 4) + e % 4) % 4 = e % 4 by omega]
    exact index_bytes _ (VG.Proof.Rc2.AArch64.Vec.index_lt _) e
  obtain ⟨d, rund, d1, _, dv, dk⟩ := quarters_run false s₉
  have d0 : d.v .v0 = s₉.v .v0 := dv _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨f, runf, f0, fv⟩ := select_half_run (s := d) I
    (fun e he => by
      have : J (e / 4) < 64 := VG.Proof.Rc2.AArch64.Vec.index_lt _
      rw [hI e he]; split <;> (try split) <;> omega)
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
    rw [tbyte_congr' this _ (by omega)]
    exact tbyte_loaded m p hs k hk
  have run : runBlock isa (rmash h i) s = some s' :=
    runBlock_cat_some (runBlock_cat_some (runBlock_cat_some run₉ rund) runf)
      (by rw [runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_sub4, runStep_some, runBlock_nil])
  refine ⟨s', run, fun i' hi' b hb => ?_, fun r h0 a0 a1 a2 a3 a4 a5 => ?_, ?_, VG.Proof.Rc2.AArch64.Vec.runBlock_sp run⟩
  · have wi := VG.Proof.Rc2.AArch64.Vec.wreg_ne h i hh
    simp only [Spec.Rc2.reverseMash]
    rw [VG.Proof.Rc2.AArch64.Vec.getD_set _ hi']
    by_cases he : i' = i
    · subst he
      rw [ite_eq_left rfl]
      have hw : VG.Proof.Rc2.AArch64.Vec.lw (f.v .v0) b = (Spec.Rc2.scheduleAt m p).getD (J b) 0 := by
        have hj : J b < 64 := VG.Proof.Rc2.AArch64.Vec.index_lt _
        have e0 : (I (4 * b)).toNat = 2 * J b := by
          rw [hI _ (by omega), show 4 * b % 4 = 0 by omega, show 4 * b / 4 = b by omega]; rfl
        have e1 : (I (4 * b + 1)).toNat = 2 * J b + 1 := by
          rw [hI _ (by omega), show (4 * b + 1) % 4 = 1 by omega,
            show (4 * b + 1) / 4 = b by omega]; rfl
        rw [VG.Proof.Rc2.AArch64.Vec.lw_bytes, f0 _ (by omega), f0 _ (by omega), e0, e1, tab _ (by omega),
          tab _ (by omega), scheduleAt_getD _ _ _ hj]
      have : VG.Proof.Rc2.AArch64.Vec.lw (s'.v (wreg h i')) b = VG.Proof.Rc2.AArch64.Vec.lw (s.v (wreg h i')) b - VG.Proof.Rc2.AArch64.Vec.lw (f.v .v0) b := by
        simp only [s', VG.Proof.Rc2.AArch64.Vec.lw, v_setV_self, vword_map2 _ _ _ hb]
        rw [VG.Proof.Rc2.AArch64.Vec.setWidth16_sub, keepV _ wi.1 wi.2.1 wi.2.2.1 wi.2.2.2.1 wi.2.2.2.2.1 wi.2.2.2.2.2.1]
      have hJ : J b = ((vs b).getD ((i' + 3) % 4) 0 &&& 63).toNat := by
        simp only [J, W]; rw [VG.Proof.Rc2.AArch64.Vec.wreg_mod h (i' + 3), hv _ (Nat.mod_lt _ (by decide)) b hb]
      rw [this, hw, hv i' hi' b hb, hJ]
    · obtain ⟨o1, -, -, -⟩ := VG.Proof.Rc2.AArch64.Vec.regs_other h i i' hh hi hi' he
      have wi' := VG.Proof.Rc2.AArch64.Vec.wreg_ne h i' hh
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

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Rounds`. -/
section

/-!
# The sixteen reverse rounds on eight blocks

`rounds_ok`: on both sets, the reverse rounds of `Spec.Rc2.decryptBlock`.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- Word `i` of both sets reverse mashed. -/
theorem mashStep_ok {s : State} {m : Mem} {p : Addr} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p)
    {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) {i : Nat} (hi : i < 4) :
    ∃ s', runBlock isa (rmash 0 i ++ rmash 1 i) s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' := by
  obtain ⟨s₁, r₁, w₁, o₁, k₁, sp₁⟩ := VG.Proof.Rc2.AArch64.Vec.rmash_ok hs (h := 0) (by decide) hi (hv 0 (by decide))
  have f₀ := VG.Proof.Rc2.AArch64.Vec.regs_fixed 0 i (by decide) hi
  have sch₁ : ∀ r < 8, s₁.v (treg r) = s.v (treg r) := by
    intro r hr
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    exact o₁ _ (f₀.2.2.2.2.2.2.2.2 r hr).1 a0 a1 a2 a3 a4 a5
  have v₁ : VG.Proof.Rc2.AArch64.Vec.VWords s₁ 1 (fun b => vs (4 * 1 + b)) := (hv 1 (by decide)).keep fun i' hi' => by
    have wn := VG.Proof.Rc2.AArch64.Vec.wreg_ne 1 i' (by decide)
    exact o₁ _ (VG.Proof.Rc2.AArch64.Vec.regs_cross 0 i i' (by decide) hi hi').1 wn.1 wn.2.1 wn.2.2.1 wn.2.2.2.1
      wn.2.2.2.2.1 wn.2.2.2.2.2.1
  obtain ⟨s₂, r₂, w₂, o₂, k₂, sp₂⟩ :=
    VG.Proof.Rc2.AArch64.Vec.rmash_ok (fun r hr => (sch₁ r hr).trans (hs r hr)) (h := 1) (by decide) hi v₁
  have f₁ := VG.Proof.Rc2.AArch64.Vec.regs_fixed 1 i (by decide) hi
  have w₂' : VG.Proof.Rc2.AArch64.Vec.VWords s₂ 0 (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i
      (vs (4 * 0 + b))) := w₁.keep fun i' hi' => by
    have wn := VG.Proof.Rc2.AArch64.Vec.wreg_ne 0 i' (by decide)
    exact o₂ _ (VG.Proof.Rc2.AArch64.Vec.regs_cross 1 i i' (by decide) hi hi').1 wn.1 wn.2.1 wn.2.2.1 wn.2.2.2.1
      wn.2.2.2.2.1 wn.2.2.2.2.2.1
  refine ⟨s₂, runBlock_cat_some r₁ r₂, fun h hh => ?_, ⟨k₁.trans k₂, by rw [sp₂, sp₁], ?_, ?_⟩⟩
  · match h, hh with
    | 0, _ => exact w₂'
    | 1, _ => exact w₂
  · intro r hr
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    rw [o₂ _ (f₁.2.2.2.2.2.2.2.2 r hr).1 a0 a1 a2 a3 a4 a5]
    exact sch₁ r hr
  · rw [o₂ _ f₁.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      o₁ _ f₀.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem mashSteps_ok {m : Mem} {p : Addr} (is : List Nat) (his : ∀ i ∈ is, i < 4) {s : State}
    (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p) {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) :
    ∃ s', runBlock isa (is.flatMap fun i => rmash 0 i ++ rmash 1 i) s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => is.foldl (fun r i =>
        Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i r) (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' := by
  induction is generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons i is ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := VG.Proof.Rc2.AArch64.Vec.mashStep_ok hs hv (his i (by simp))
    obtain ⟨s₂, r₂, v₂, k₂⟩ := ih (fun i hi => his i (by simp [hi])) (hs.keep k₁) v₁
    exact ⟨s₂, by rw [List.flatMap_cons]; exact runBlock_cat_some r₁ r₂, v₂, k₁.trans k₂⟩

theorem rmashRound_ok {m : Mem} {p : Addr} {s : State} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p)
    {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) :
    ∃ s', runBlock isa rmashRound s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => Spec.Rc2.reverseMashRound (Spec.Rc2.scheduleAt m p) (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' :=
  VG.Proof.Rc2.AArch64.Vec.mashSteps_ok [3, 2, 1, 0] (by decide) hs hv

/-- A reverse round of `Spec.Rc2.decryptBlock`: the mixing round `15 - j`,
then the mashing round after the fifth and the eleventh. -/
def revRound (k : Spec.Rc2.Schedule) (r : Spec.Rc2.State) (j : Nat) : Spec.Rc2.State :=
  if j = 4 ∨ j = 10 then Spec.Rc2.reverseMashRound k (Spec.Rc2.reverseMixRound k (15 - j) r)
  else Spec.Rc2.reverseMixRound k (15 - j) r

theorem roundsList_ok {m : Mem} {p : Addr} (js : List Nat) {s : State} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p)
    (hm : s.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16) {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) :
    ∃ s', runBlock isa (js.flatMap fun j =>
        rmixRound (15 - j) ++ (if j = 4 ∨ j = 10 then rmashRound else [])) s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => js.foldl (VG.Proof.Rc2.AArch64.Vec.revRound (Spec.Rc2.scheduleAt m p)) (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' := by
  induction js generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons j js ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := VG.Proof.Rc2.AArch64.Vec.rmixRound_ok (j := 15 - j) (by omega) hs hm hv
    have step : ∃ s', runBlock isa
        (rmixRound (15 - j) ++ (if j = 4 ∨ j = 10 then rmashRound else [])) s = some s' ∧
        VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => VG.Proof.Rc2.AArch64.Vec.revRound (Spec.Rc2.scheduleAt m p) (vs b) j) ∧ VG.Proof.Rc2.AArch64.Vec.VKeep s s' := by
      by_cases hc : j = 4 ∨ j = 10
      · obtain ⟨s₂, r₂, v₂, k₂⟩ := VG.Proof.Rc2.AArch64.Vec.rmashRound_ok (hs.keep k₁) v₁
        refine ⟨s₂, ?_, fun h hh i hi b hb => ?_, k₁.trans k₂⟩
        · simp only [hc, ↓reduceIte]; exact runBlock_cat_some r₁ r₂
        · simp only [VG.Proof.Rc2.AArch64.Vec.revRound, hc, ↓reduceIte]; exact v₂ h hh i hi b hb
      · refine ⟨s₁, ?_, fun h hh i hi b hb => ?_, k₁⟩
        · simp only [hc, ↓reduceIte, List.append_nil]; exact r₁
        · simp only [VG.Proof.Rc2.AArch64.Vec.revRound, hc, ↓reduceIte]; exact v₁ h hh i hi b hb
    obtain ⟨s₂, r₂, v₂, k₂⟩ := step
    obtain ⟨s₃, r₃, v₃, k₃⟩ := ih (hs.keep k₂) (k₂.mask.trans hm) v₂
    exact ⟨s₃, by rw [List.flatMap_cons]; exact runBlock_cat_some r₂ r₃, v₃, k₂.trans k₃⟩

theorem revRounds_eq (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    Spec.Rc2.decryptBlock k b =
      Spec.Rc2.encodeBlock ((List.range 16).foldl (VG.Proof.Rc2.AArch64.Vec.revRound k) (Spec.Rc2.decodeBlock b)) := by
  simp only [Spec.Rc2.decryptBlock]
  rfl

theorem rounds_ok {m : Mem} {p : Addr} {s : State} (hs : VG.Proof.Rc2.AArch64.Vec.SchedV s m p)
    (hm : s.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16) {vs : Nat → Spec.Rc2.State} (hv : VG.Proof.Rc2.AArch64.Vec.Sets s vs) :
    ∃ s', runBlock isa rounds s = some s' ∧
      VG.Proof.Rc2.AArch64.Vec.Sets s' (fun b => (List.range 16).foldl (VG.Proof.Rc2.AArch64.Vec.revRound (Spec.Rc2.scheduleAt m p)) (vs b)) ∧
      VG.Proof.Rc2.AArch64.Vec.VKeep s s' :=
  VG.Proof.Rc2.AArch64.Vec.roundsList_ok _ hs hm hv

end VG.Proof.Rc2.AArch64.Vec

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Load`. -/
section

/-!
# Loading a group of eight blocks

`loadGroup_ok`: the eight blocks at `x1`, loaded into `v0`–`v3` and their
words gathered into the sets by `tbl` (`inIndex`): block `b` of the eight is
`Spec.Rc2.decodeBlock` of the block at `x1 + 8 b`.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

theorem exec_tbl2 (s : State) (d n m : VReg) :
    exec (.vop (.tblN false 2 d n m)) s = some (s.setV d (ofVBytes fun e =>
      if (vbyte (s.v m) e).toNat < 16 * 2 then tableByte s.v n (vbyte (s.v m) e).toNat else 0)) :=
  rfl

/-- A byte of a two-register table loaded from consecutive memory. -/
theorem tableByte_pair {v : VReg → BitVec 128} {n : VReg} {m : Mem} {a : Addr}
    (h0 : v n = m.read a 16) (h1 : v (VReg.succ n) = m.read (a + BitVec.ofNat 64 16) 16)
    {idx : Nat} (hi : idx < 32) : tableByte v n idx = m (a + BitVec.ofNat 64 idx) := by
  rw [tableByte]
  by_cases hl : idx < 16
  · rw [show idx / 16 = 0 by omega, show Nat.repeat VReg.succ 0 n = n from rfl, h0,
      VG.Proof.Rc2.AArch64.Vec.vbyte_read _ _ (by omega), Nat.mod_eq_of_lt hl]
  · rw [show idx / 16 = 1 by omega, show Nat.repeat VReg.succ 1 n = VReg.succ n from rfl, h1,
      VG.Proof.Rc2.AArch64.Vec.vbyte_read _ _ (by omega), Offset.add_add, show 16 + idx % 16 = idx by omega]

theorem inIndex_byte (i : Nat) (hi : i < 4) {e : Nat} (he : e < 16) :
    (vbyte (inIndex i) e).toNat = if e % 4 < 2 then 8 * (e / 4) + 2 * i + e % 4 else 255 := by
  rw [inIndex, vbyte_ofVBytes _ he]
  split
  · rw [BitVec.toNat_ofNat]; omega
  · rfl

/-- The block's word `i`, from its bytes. -/
theorem decode_getD (m : Mem) (a : Addr) {i : Nat} (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m a)).getD i 0 =
      (m (a + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (a + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.decodeBlock, Spec.Rc2.blockAt, Vector.getD, hi, show 2 * i < 8 by omega,
    show 2 * i + 1 < 8 by omega]

/-- Word `i` of set `h`, gathered from the table at `n` (`v0` or `v2`). -/
theorem gather_lane {v : VReg → BitVec 128} {n : VReg} {m : Mem} {a : Addr}
    (h0 : v n = m.read a 16) (h1 : v (VReg.succ n) = m.read (a + BitVec.ofNat 64 16) 16)
    {i : Nat} (hix : v .v4 = inIndex i) (hi : i < 4) {b : Nat} (hb : b < 4) :
    VG.Proof.Rc2.AArch64.Vec.lw (ofVBytes fun e =>
      if (vbyte (v .v4) e).toNat < 16 * 2 then tableByte v n (vbyte (v .v4) e).toNat else 0) b =
      (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m (a + BitVec.ofNat 64 (8 * b)))).getD i 0 := by
  rw [VG.Proof.Rc2.AArch64.Vec.lw_bytes, vbyte_ofVBytes _ (by omega), vbyte_ofVBytes _ (by omega), hix,
    VG.Proof.Rc2.AArch64.Vec.inIndex_byte i hi (by omega), VG.Proof.Rc2.AArch64.Vec.inIndex_byte i hi (by omega), VG.Proof.Rc2.AArch64.Vec.decode_getD _ _ hi,
    Offset.add_add, Offset.add_add]
  simp only [show 4 * b % 4 = 0 by omega, show (4 * b + 1) % 4 = 1 by omega,
    show 4 * b / 4 = b by omega, show (4 * b + 1) / 4 = b by omega, show 0 < 2 by decide,
    show 1 < 2 by decide, ite_true, Nat.add_zero, show 8 * b + 2 * i + 1 = 8 * b + (2 * i + 1) by omega,
    eq_true (show 8 * b + 2 * i < 16 * 2 by omega), eq_true (show 8 * b + (2 * i + 1) < 16 * 2 by omega)]
  rw [VG.Proof.Rc2.AArch64.Vec.tableByte_pair h0 h1 (by omega), VG.Proof.Rc2.AArch64.Vec.tableByte_pair h0 h1 (by omega)]

theorem wreg_inj {h i h' i' : Nat} (hh : h < 2) (hi : i < 4) (hh' : h' < 2) (hi' : i' < 4)
    (e : wreg h i = wreg h' i') : h = h' ∧ i = i' := by
  have := treg_inj (8 + 4 * h + i % 4) (by omega) (8 + 4 * h' + i' % 4) (by omega) e
  omega

/-- The words the gathers of `is` leave: block `b` of the eight at `q`. -/
def Gathered (t : State) (m : Mem) (q : Addr) (i : Nat) : Prop :=
  ∀ h < 2, ∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (t.v (wreg h i)) b =
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m (q + BitVec.ofNat 64 (8 * (4 * h + b))))).getD i 0

theorem gathers_ok {m : Mem} {q : Addr} (is : List Nat) (his : ∀ i ∈ is, i < 4) (t : State)
    (r0 : t.v .v0 = m.read q 16) (r1 : t.v .v1 = m.read (q + BitVec.ofNat 64 16) 16)
    (r2 : t.v .v2 = m.read (q + BitVec.ofNat 64 32) 16)
    (r3 : t.v .v3 = m.read (q + BitVec.ofNat 64 48) 16) :
    WP isa (.block (is.flatMap fun i => const128 .v4 (inIndex i) ++
        ([.vop (.tblN false 2 (wreg 0 i) .v0 .v4), .vop (.tblN false 2 (wreg 1 i) .v2 .v4)] :
          List Instr))) t
      fun t' => (∀ i ∈ is, VG.Proof.Rc2.AArch64.Vec.Gathered t' m q i) ∧
        (∀ w, w ≠ .v4 → (∀ i ∈ is, ∀ h < 2, w ≠ wreg h i) → t'.v w = t.v w) ∧
        (∀ g, g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧
        t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  induction is generalizing t with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h (by simp), fun _ _ _ => rfl, fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | cons i is ih =>
    have hi := his i (by simp)
    rw [List.flatMap_cons, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (const128_ok t .v4 (inIndex i)) fun a ⟨a4, av, ag, am, ard, awr, asp⟩ => ?_
    have w0 := VG.Proof.Rc2.AArch64.Vec.wreg_ne 0 i (by decide)
    have w1 := VG.Proof.Rc2.AArch64.Vec.wreg_ne 1 i (by decide)
    have n01 : wreg 1 i ≠ wreg 0 i := fun e => absurd (VG.Proof.Rc2.AArch64.Vec.wreg_inj (by decide) hi (by decide) hi e).1 (by decide)
    let c₁ := a.setV (wreg 0 i) (ofVBytes fun e => if (vbyte (a.v .v4) e).toNat < 16 * 2 then
      tableByte a.v .v0 (vbyte (a.v .v4) e).toNat else 0)
    let c₂ := c₁.setV (wreg 1 i) (ofVBytes fun e => if (vbyte (c₁.v .v4) e).toNat < 16 * 2 then
      tableByte c₁.v .v2 (vbyte (c₁.v .v4) e).toNat else 0)
    refine WP.of_runBlock ⟨c₂, by
      rw [runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_tbl2, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_tbl2, runStep_some,
        runBlock_nil], ?_⟩
    have cv : ∀ w, w ≠ wreg 0 i → w ≠ wreg 1 i → c₂.v w = a.v w := fun w h0 h1 => by
      simp only [c₂, c₁, v_setV_of_ne _ _ h0, v_setV_of_ne _ _ h1]
    have keepT : ∀ w, w ≠ .v4 → w ≠ wreg 0 i → w ≠ wreg 1 i → c₂.v w = t.v w := fun w h4 h0 h1 => by
      rw [cv w h0 h1, av w h4]
    have g : VG.Proof.Rc2.AArch64.Vec.Gathered c₂ m q i := by
      intro h hh b hb
      match h, hh with
      | 0, _ =>
        rw [show c₂.v (wreg 0 i) = c₁.v (wreg 0 i) from v_setV_of_ne _ _ n01.symm,
          show c₁.v (wreg 0 i) = _ from v_setV_self _ _ _,
          VG.Proof.Rc2.AArch64.Vec.gather_lane (a := q) (by rw [av _ (by decide), r0])
            (by rw [show VReg.succ .v0 = .v1 from rfl, av _ (by decide), r1]) a4 hi hb,
          show 4 * 0 + b = b by omega]
      | 1, _ =>
        rw [show c₂.v (wreg 1 i) = _ from v_setV_self _ _ _]
        have e4 : c₁.v .v4 = a.v .v4 := v_setV_of_ne _ _ w0.2.2.2.2.1.symm
        rw [VG.Proof.Rc2.AArch64.Vec.gather_lane (a := q + BitVec.ofNat 64 32)
          (by rw [v_setV_of_ne _ _ w0.2.2.1.symm, av _ (by decide), r2])
          (by rw [show VReg.succ .v2 = .v3 from rfl, v_setV_of_ne _ _ w0.2.2.2.1.symm,
            av _ (by decide), r3, Offset.add_add]) (e4.trans a4) hi hb, Offset.add_add,
          show 32 + 8 * b = 8 * (4 * 1 + b) by omega]
    have hr : ∀ r < 4, c₂.v (VReg.v0) = t.v .v0 ∧ c₂.v .v1 = t.v .v1 ∧ c₂.v .v2 = t.v .v2 ∧
        c₂.v .v3 = t.v .v3 := fun _ _ =>
      ⟨keepT _ (by decide) w0.1.symm w1.1.symm, keepT _ (by decide) w0.2.1.symm w1.2.1.symm,
        keepT _ (by decide) w0.2.2.1.symm w1.2.2.1.symm,
        keepT _ (by decide) w0.2.2.2.1.symm w1.2.2.2.1.symm⟩
    obtain ⟨e0, e1, e2, e3⟩ := hr 0 (by decide)
    refine WP.mono (ih (fun i hi => his i (by simp [hi])) c₂ (e0.trans r0) (e1.trans r1)
      (e2.trans r2) (e3.trans r3)) fun t' ⟨tg, tv, tgp, tm, trd, twr, tsp⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' hi'
      by_cases hin : i' ∈ is
      · exact tg i' hin
      · have he : i' = i := by simpa [hin] using hi'
        subst he
        intro h hh b hb
        rw [tv _ (by have := VG.Proof.Rc2.AArch64.Vec.wreg_ne h i' hh; exact this.2.2.2.2.1)
          (fun i'' hi'' h' hh' e => by
            have := VG.Proof.Rc2.AArch64.Vec.wreg_inj hh hi hh' (his i'' (by simp [hi''])) e
            exact hin (this.2 ▸ hi''))]
        exact g h hh b hb
    · intro w h4 hw
      rw [tv w h4 (fun i' hi' => hw i' (by simp [hi'])),
        keepT w h4 (hw i (by simp) 0 (by decide)) (hw i (by simp) 1 (by decide))]
    · intro r h6 h7
      rw [tgp r h6 h7]
      simp only [c₂, c₁, gpr_setV]
      exact ag r h6 h7
    · rw [tm]; simp only [c₂, c₁, mem_setV]; exact am
    · rw [trd]; simp only [c₂, c₁, rd_setV]; exact ard
    · rw [twr]; simp only [c₂, c₁, wr_setV]; exact awr
    · rw [tsp]; simp only [c₂, c₁, sp_setV]; exact asp

theorem loadGroup_ok (t : State)
    (hr : ∀ c < 4, InRegions (t.rd ++ t.wr) (t.gpr .x1 + BitVec.ofNat 64 (16 * c)) 16) :
    WP isa (.block loadGroup) t fun t' =>
      VG.Proof.Rc2.AArch64.Vec.Sets t' (fun b => Spec.Rc2.decodeBlock
        (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b)))) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → (∀ i < 4, ∀ h < 2, w ≠ wreg h i) →
        t'.v w = t.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  let q := t.gpr .x1
  let s₁ := t.setV .v0 (t.mem.read (q + BitVec.ofNat 64 0) 16)
  let s₂ := s₁.setV .v1 (t.mem.read (q + BitVec.ofNat 64 16) 16)
  let s₃ := s₂.setV .v2 (t.mem.read (q + BitVec.ofNat 64 32) 16)
  let s₄ := s₃.setV .v3 (t.mem.read (q + BitVec.ofNat 64 48) 16)
  rw [loadGroup, WP.block_append_iff]
  have e₁ : exec (.ldrq .v0 .x1 0) t = some s₁ :=
    exec_ldrq' t _ _ 0 ⟨by decide, by decide⟩ (hr 0 (by decide))
  have e₂ : exec (.ldrq .v1 .x1 16) s₁ = some s₂ :=
    exec_ldrq' s₁ _ _ 16 ⟨by decide, by decide⟩ (hr 1 (by decide))
  have e₃ : exec (.ldrq .v2 .x1 32) s₂ = some s₃ :=
    exec_ldrq' s₂ _ _ 32 ⟨by decide, by decide⟩ (hr 2 (by decide))
  have e₄ : exec (.ldrq .v3 .x1 48) s₃ = some s₄ :=
    exec_ldrq' s₃ _ _ 48 ⟨by decide, by decide⟩ (hr 3 (by decide))
  refine WP.of_runBlock ⟨s₄, by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil], ?_⟩
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  refine WP.mono (VG.Proof.Rc2.AArch64.Vec.gathers_ok (m := t.mem) (q := q) (List.range 4) (fun i hi => List.mem_range.mp hi) s₄
    (by simp only [s₄, s₃, s₂, s₁, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1),
      v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3), z])
    (by simp only [s₄, s₃, s₂, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2),
      v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v3)])
    (by simp only [s₄, s₃, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3)])
    (by simp only [s₄, v_setV_self])) fun t' ⟨tg, tv, tgp, tm, trd, twr, tsp⟩ =>
      ⟨fun h hh i hi b hb => tg i (List.mem_range.mpr hi) h hh b hb, fun w a0 a1 a2 a3 a4 hw => ?_,
        fun g h6 h7 => (tgp g h6 h7).trans rfl, tm, trd, twr, tsp⟩
  rw [tv w a4 (fun i hi h hh => hw i (List.mem_range.mp hi) h hh)]
  simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ a0, v_setV_of_ne _ _ a1, v_setV_of_ne _ _ a2,
    v_setV_of_ne _ _ a3]

end VG.Proof.Rc2.AArch64.Vec

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Store`. -/
section

/-!
# Storing a group of eight blocks

`scatter_ok`: `tbl` scatters the sets' words back into blocks, blocks `4 h +
2 k` and `4 h + 2 k + 1` into `v(2 h + k)` (`outIndex`). `xorStore_ok`: each
XORed with the ciphertext block before it and stored in place.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- Byte `j` of a block with words `r` (`Spec.Rc2.encodeBlock`). -/
def encByte (r : Spec.Rc2.State) (j : Nat) : BitVec 8 :=
  ((r.getD (j / 2) 0) >>> (8 * (j % 2))).setWidth 8

theorem encodeBlock_getElem (r : Spec.Rc2.State) {j : Nat} (hj : j < 8) :
    (Spec.Rc2.encodeBlock r)[j] = VG.Proof.Rc2.AArch64.Vec.encByte r j := by
  simp [Spec.Rc2.encodeBlock, VG.Proof.Rc2.AArch64.Vec.encByte]

theorem exec_tbl4 (s : State) (d n m : VReg) :
    exec (.vop (.tblN false 4 d n m)) s = some (s.setV d (ofVBytes fun e =>
      if (vbyte (s.v m) e).toNat < 16 * 4 then tableByte s.v n (vbyte (s.v m) e).toNat else 0)) :=
  rfl

/-- The low two bytes of a lane, from its low 16 bits. -/
theorem vbyte_lw (x : BitVec 128) (b : Nat) {c : Nat} (hc : c < 2) :
    vbyte x (4 * b + c) = ((VG.Proof.Rc2.AArch64.Vec.lw x b) >>> (8 * c)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, VG.Proof.Rc2.AArch64.Vec.lw, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and]
  simp [show 8 * c + t < 16 by omega, show 8 * c + t < 32 by omega,
    show 8 * (4 * b + c) + t = 32 * b + (8 * c + t) by omega]

theorem outIndex_byte (k : Nat) (hk : k < 2) {e : Nat} (he : e < 16) :
    (vbyte (outIndex k) e).toNat = 16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2 := by
  rw [outIndex, vbyte_ofVBytes _ he, BitVec.toNat_ofNat]
  omega

theorem repeat_wreg : ∀ h < 2, ∀ w < 4, Nat.repeat VReg.succ w (wreg h 0) = wreg h w := by
  decide

/-- Byte `e` of `tbl` of set `h` at `outIndex k`: byte `e % 8` of block `4 h + 2 k + e / 8`. -/
theorem scatter_byte {v : VReg → BitVec 128} {h k : Nat} (hh : h < 2) (hk : k < 2)
    (hix : v .v4 = outIndex k) {R : Nat → Spec.Rc2.State}
    (hw : ∀ i < 4, ∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (v (wreg h i)) b = (R (4 * h + b)).getD i 0) {e : Nat} (he : e < 16) :
    vbyte (ofVBytes fun e =>
      if (vbyte (v .v4) e).toNat < 16 * 4 then tableByte v (wreg h 0) (vbyte (v .v4) e).toNat else 0) e =
      VG.Proof.Rc2.AArch64.Vec.encByte (R (4 * h + 2 * k + e / 8)) (e % 8) := by
  rw [vbyte_ofVBytes _ he, hix, VG.Proof.Rc2.AArch64.Vec.outIndex_byte k hk he,
    ite_eq_left (show 16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2 < 16 * 4 by omega), tableByte,
    show (16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2) / 16 = e % 8 / 2 by omega,
    show (16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2) % 16 = 4 * (2 * k + e / 8) + e % 2 by omega,
    VG.Proof.Rc2.AArch64.Vec.repeat_wreg h hh _ (by omega), VG.Proof.Rc2.AArch64.Vec.vbyte_lw _ _ (by omega), hw _ (by omega) _ (by omega), VG.Proof.Rc2.AArch64.Vec.encByte,
    show 4 * h + (2 * k + e / 8) = 4 * h + 2 * k + e / 8 by omega,
    show e % 8 % 2 = e % 2 by omega]

/-- The scattering: the blocks into `v0`–`v3`. -/
def scatterCode : List Instr :=
  const128 .v4 (outIndex 0) ++
  [.vop (.tblN false 4 .v0 (wreg 0 0) .v4), .vop (.tblN false 4 .v2 (wreg 1 0) .v4)] ++
  const128 .v4 (outIndex 1) ++
  [.vop (.tblN false 4 .v1 (wreg 0 0) .v4), .vop (.tblN false 4 .v3 (wreg 1 0) .v4)]

/-- The XOR with the ciphertext blocks, and the stores. -/
def xorCode : List Instr :=
  [.ldr .x .x9 .x1 0, .vop (.ins .d2 .v4 0 .x11), .vop (.ins .d2 .v4 1 .x9),
   .addImm .x .x12 .x1 8, .ldrq .v5 .x12 0,
   .vop (.logic .eor .v0 .v0 .v4), .vop (.logic .eor .v1 .v1 .v5),
   .ldrq .v4 .x12 16, .ldrq .v5 .x12 32,
   .vop (.logic .eor .v2 .v2 .v4), .vop (.logic .eor .v3 .v3 .v5),
   .ldr .x .x11 .x1 56,
   .strq .v0 .x1 0, .strq .v1 .x1 16, .strq .v2 .x1 32, .strq .v3 .x1 48]

theorem storeGroup_eq : storeGroup = VG.Proof.Rc2.AArch64.Vec.scatterCode ++ VG.Proof.Rc2.AArch64.Vec.xorCode := by
  simp only [storeGroup, VG.Proof.Rc2.AArch64.Vec.scatterCode, VG.Proof.Rc2.AArch64.Vec.xorCode, List.append_assoc, List.cons_append, List.nil_append]

/-- Byte `e` of `v0`–`v3` after the scattering: byte `16 c + e` of the eight blocks. -/
def Scattered (v : VReg → BitVec 128) (R : Nat → Spec.Rc2.State) : Prop :=
  ∀ e < 16, vbyte (v .v0) e = VG.Proof.Rc2.AArch64.Vec.encByte (R (e / 8)) (e % 8) ∧
    vbyte (v .v1) e = VG.Proof.Rc2.AArch64.Vec.encByte (R (2 + e / 8)) (e % 8) ∧
    vbyte (v .v2) e = VG.Proof.Rc2.AArch64.Vec.encByte (R (4 + e / 8)) (e % 8) ∧
    vbyte (v .v3) e = VG.Proof.Rc2.AArch64.Vec.encByte (R (6 + e / 8)) (e % 8)

theorem scatter_ok (t : State) {R : Nat → Spec.Rc2.State} (hS : VG.Proof.Rc2.AArch64.Vec.Sets t R) :
    WP isa (.block VG.Proof.Rc2.AArch64.Vec.scatterCode) t fun t' => VG.Proof.Rc2.AArch64.Vec.Scattered t'.v R ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → t'.v w = t.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  rw [VG.Proof.Rc2.AArch64.Vec.scatterCode, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const128_ok t .v4 (outIndex 0)) fun a ⟨a4, av, ag, am, ard, awr, asp⟩ => ?_
  let c₁ := a.setV .v0 (ofVBytes fun e => if (vbyte (a.v .v4) e).toNat < 16 * 4 then
    tableByte a.v (wreg 0 0) (vbyte (a.v .v4) e).toNat else 0)
  let c₂ := c₁.setV .v2 (ofVBytes fun e => if (vbyte (c₁.v .v4) e).toNat < 16 * 4 then
    tableByte c₁.v (wreg 1 0) (vbyte (c₁.v .v4) e).toNat else 0)
  refine WP.of_runBlock ⟨c₂, by
    rw [runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_tbl4, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_tbl4, runStep_some,
      runBlock_nil], ?_⟩
  refine WP.mono (const128_ok c₂ .v4 (outIndex 1)) fun b ⟨b4, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  let d₁ := b.setV .v1 (ofVBytes fun e => if (vbyte (b.v .v4) e).toNat < 16 * 4 then
    tableByte b.v (wreg 0 0) (vbyte (b.v .v4) e).toNat else 0)
  let d₂ := d₁.setV .v3 (ofVBytes fun e => if (vbyte (d₁.v .v4) e).toNat < 16 * 4 then
    tableByte d₁.v (wreg 1 0) (vbyte (d₁.v .v4) e).toNat else 0)
  refine WP.of_runBlock ⟨d₂, by
    rw [runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_tbl4, runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_tbl4, runStep_some,
      runBlock_nil], ?_⟩
  -- The sets, kept until the end.
  have ws : ∀ h < 2, ∀ i < 4, a.v (wreg h i) = t.v (wreg h i) ∧ c₁.v (wreg h i) = t.v (wreg h i) ∧
      b.v (wreg h i) = t.v (wreg h i) ∧ d₁.v (wreg h i) = t.v (wreg h i) := by
    intro h hh i hi
    have wn := VG.Proof.Rc2.AArch64.Vec.wreg_ne h i hh
    have e₁ : a.v (wreg h i) = t.v (wreg h i) := av _ wn.2.2.2.2.1
    have e₂ : c₁.v (wreg h i) = t.v (wreg h i) := by
      simp only [c₁, v_setV_of_ne _ _ wn.1]; exact e₁
    have e₃ : b.v (wreg h i) = t.v (wreg h i) := by
      rw [bv _ wn.2.2.2.2.1]; simp only [c₂, v_setV_of_ne _ _ wn.2.2.1]; exact e₂
    refine ⟨e₁, e₂, e₃, ?_⟩
    simp only [d₁, v_setV_of_ne _ _ wn.2.1]; exact e₃
  have hw : ∀ (f : VReg → BitVec 128), (∀ h < 2, ∀ i < 4, f (wreg h i) = t.v (wreg h i)) →
      ∀ h < 2, ∀ i < 4, ∀ b < 4, VG.Proof.Rc2.AArch64.Vec.lw (f (wreg h i)) b = (R (4 * h + b)).getD i 0 :=
    fun f hf h hh i hi b hb => by rw [hf h hh i hi]; exact hS h hh i hi b hb
  have c4 : c₁.v .v4 = outIndex 0 := by simp only [c₁, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v0)]; exact a4
  have d4 : d₁.v .v4 = outIndex 1 := by simp only [d₁, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1)]; exact b4
  refine ⟨fun e he => ⟨?_, ?_, ?_, ?_⟩, fun w h0 h1 h2 h3 h4 => ?_, fun g h6 h7 => ?_, ?_, ?_, ?_, ?_⟩
  · have : d₂.v .v0 = c₁.v .v0 := by
      simp only [d₂, d₁, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]
      rw [bv _ (by decide)]; simp only [c₂, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2)]
    rw [this, show c₁.v .v0 = _ from v_setV_self _ _ _,
      VG.Proof.Rc2.AArch64.Vec.scatter_byte (h := 0) (k := 0) (by decide) (by decide) a4
        (hw a.v (fun h hh i hi => (ws h hh i hi).1) 0 (by decide)) he,
      show 4 * 0 + 2 * 0 + e / 8 = e / 8 by omega]
  · rw [show d₂.v .v1 = d₁.v .v1 from v_setV_of_ne _ _ (by decide),
      show d₁.v .v1 = _ from v_setV_self _ _ _,
      VG.Proof.Rc2.AArch64.Vec.scatter_byte (h := 0) (k := 1) (by decide) (by decide) b4
        (hw b.v (fun h hh i hi => (ws h hh i hi).2.2.1) 0 (by decide)) he]
  · have : d₂.v .v2 = c₂.v .v2 := by
      simp only [d₂, d₁, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v1)]
      exact bv _ (by decide)
    rw [this, show c₂.v .v2 = _ from v_setV_self _ _ _,
      VG.Proof.Rc2.AArch64.Vec.scatter_byte (h := 1) (k := 0) (by decide) (by decide) c4
        (hw c₁.v (fun h hh i hi => (ws h hh i hi).2.1) 1 (by decide)) he]
  · rw [show d₂.v .v3 = _ from v_setV_self _ _ _,
      VG.Proof.Rc2.AArch64.Vec.scatter_byte (h := 1) (k := 1) (by decide) (by decide) d4
        (hw d₁.v (fun h hh i hi => (ws h hh i hi).2.2.2) 1 (by decide)) he]
  · simp only [d₂, d₁, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h1]
    rw [bv _ h4]
    simp only [c₂, c₁, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h0]
    exact av _ h4
  · simp only [d₂, d₁, gpr_setV]; rw [bg g h6 h7]; simp only [c₂, c₁, gpr_setV]; exact ag g h6 h7
  · simp only [d₂, d₁, mem_setV]; rw [bm]; simp only [c₂, c₁, mem_setV]; exact am
  · simp only [d₂, d₁, rd_setV]; rw [brd]; simp only [c₂, c₁, rd_setV]; exact ard
  · simp only [d₂, d₁, wr_setV]; rw [bwr]; simp only [c₂, c₁, wr_setV]; exact awr
  · simp only [d₂, d₁, sp_setV]; rw [bsp]; simp only [c₂, c₁, sp_setV]; exact asp

theorem exec_addImmx (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp [exec, State.read, h]

theorem exec_strq (s : State) (t : VReg) (n : Reg) (off : Nat) (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.store, h,
    Option.bind_some]

/-- A 16-byte write at offset `d`, read at offset `j`. -/
theorem write16_at (m : Mem) (q : Addr) {d j : Nat} (hd : d + 16 ≤ 64) (hj : j < 64)
    (v : BitVec (8 * 16)) :
    (m.write (q + BitVec.ofNat 64 d) 16 v) (q + BitVec.ofNat 64 j) =
      if d ≤ j ∧ j < d + 16 then vbyte v (j - d) else m (q + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.add_sub_add_left]
  by_cases h : d ≤ j ∧ j < d + 16
  · rw [Offset.ofNat_sub_ofNat h.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [show j - d < 16 by omega, h, and_self, ite_true]
    rfl
  · have : ¬ (BitVec.ofNat 64 j - BitVec.ofNat 64 d).toNat < 16 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    simp only [this, h, ite_false]

theorem write4_at (m : Mem) (q : Addr) (V0 V1 V2 V3 : BitVec (8 * 16)) {o : Nat} (ho : o < 64) :
    ((((m.write (q + BitVec.ofNat 64 0) 16 V0).write (q + BitVec.ofNat 64 16) 16 V1).write
      (q + BitVec.ofNat 64 32) 16 V2).write (q + BitVec.ofNat 64 48) 16 V3) (q + BitVec.ofNat 64 o) =
      vbyte (if o < 16 then V0 else if o < 32 then V1 else if o < 48 then V2 else V3) (o % 16) := by
  rw [VG.Proof.Rc2.AArch64.Vec.write16_at _ _ (by decide) ho, VG.Proof.Rc2.AArch64.Vec.write16_at _ _ (by decide) ho, VG.Proof.Rc2.AArch64.Vec.write16_at _ _ (by decide) ho,
    VG.Proof.Rc2.AArch64.Vec.write16_at _ _ (by decide) ho]
  rcases (by omega : o < 16 ∨ (16 ≤ o ∧ o < 32) ∨ (32 ≤ o ∧ o < 48) ∨ 48 ≤ o) with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem vbyte_ofVDwords (a b : BitVec 64) {e : Nat} (he : e < 16) :
    vbyte (ofVDwords a b) e =
      if e < 8 then a.extractLsb' (8 * e) 8 else b.extractLsb' (8 * (e - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, ofVDwords, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : e < 8
  · simp only [h, ite_true, show 8 * e + t < 64 by omega, BitVec.getLsbD_extractLsb', ht,
      decide_true, Bool.true_and]
  · simp only [h, ite_false, show ¬ 8 * e + t < 64 by omega, BitVec.getLsbD_extractLsb', ht,
      decide_true, Bool.true_and, show 8 * e + t - 64 = 8 * (e - 8) + t by omega]

/-- The ciphertext byte before byte `o` of the group: the chaining value's
in the first block. -/
def prevByte (X : BitVec 64) (m : Mem) (q : Addr) (o : Nat) : BitVec 8 :=
  if o < 8 then X.extractLsb' (8 * o) 8 else m (q + BitVec.ofNat 64 (o - 8))

theorem xorStore_ok (t : State) {R : Nat → Spec.Rc2.State} (hsc : VG.Proof.Rc2.AArch64.Vec.Scattered t.v R)
    (hrd : InRegions (t.rd ++ t.wr) (t.gpr .x1) 64) (hwr : InRegions t.wr (t.gpr .x1) 64) :
    ∃ t', runBlock isa VG.Proof.Rc2.AArch64.Vec.xorCode t = some t' ∧
      (∀ o < 64, t'.mem (t.gpr .x1 + BitVec.ofNat 64 o) =
        VG.Proof.Rc2.AArch64.Vec.encByte (R (o / 8)) (o % 8) ^^^ VG.Proof.Rc2.AArch64.Vec.prevByte (t.gpr .x11) t.mem (t.gpr .x1) o) ∧
      Frame [⟨t.gpr .x1, 64⟩] t.mem t'.mem ∧
      t'.gpr .x11 = t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 56) 64 ∧
      (∀ g, g ≠ .x9 → g ≠ .x11 → g ≠ .x12 → t'.gpr g = t.gpr g) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 → t'.v w = t.v w) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  let q := t.gpr .x1
  let M := t.mem
  let X := t.gpr .x11
  have rd : ∀ off, off + 16 ≤ 64 → InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 off) 16 :=
    fun off h => CallLay.inRegions_sub hrd h (by decide)
  let d₁ := t.write .x .x9 (t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 0) 64)
  let d₂ := d₁.setV .v4 (setLane (d₁.v .v4) 64 0 (d₁.gpr .x11))
  let d₃ := d₂.setV .v4 (setLane (d₂.v .v4) 64 1 (d₂.gpr .x9))
  let d₄ := d₃.write .x .x12 (d₃.gpr .x1 + BitVec.ofNat 64 8)
  let d₅ := d₄.setV .v5 (d₄.mem.read (d₄.gpr .x12 + BitVec.ofNat 64 0) 16)
  let d₆ := d₅.setV .v0 (d₅.v .v0 ^^^ d₅.v .v4)
  let d₇ := d₆.setV .v1 (d₆.v .v1 ^^^ d₆.v .v5)
  let d₈ := d₇.setV .v4 (d₇.mem.read (d₇.gpr .x12 + BitVec.ofNat 64 16) 16)
  let d₉ := d₈.setV .v5 (d₈.mem.read (d₈.gpr .x12 + BitVec.ofNat 64 32) 16)
  let d₁₀ := d₉.setV .v2 (d₉.v .v2 ^^^ d₉.v .v4)
  let d₁₁ := d₁₀.setV .v3 (d₁₀.v .v3 ^^^ d₁₀.v .v5)
  let d₁₂ := d₁₁.write .x .x11 (d₁₁.mem.readW (d₁₁.gpr .x1 + BitVec.ofNat 64 56) 64)
  let d₁₃ : State := { d₁₂ with mem := d₁₂.mem.write (d₁₂.gpr .x1 + BitVec.ofNat 64 0) 16 (d₁₂.v .v0) }
  let d₁₄ : State := { d₁₃ with mem := d₁₃.mem.write (d₁₃.gpr .x1 + BitVec.ofNat 64 16) 16 (d₁₃.v .v1) }
  let d₁₅ : State := { d₁₄ with mem := d₁₄.mem.write (d₁₄.gpr .x1 + BitVec.ofNat 64 32) 16 (d₁₄.v .v2) }
  let d₁₆ : State := { d₁₅ with mem := d₁₅.mem.write (d₁₅.gpr .x1 + BitVec.ofNat 64 48) 16 (d₁₅.v .v3) }
  -- The general registers along the way.
  have x1₄ : d₄.gpr .x1 = q := by
    simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x12), gpr_setV,
      gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x9)]; rfl
  have x12₄ : d₄.gpr .x12 = q + BitVec.ofNat 64 8 := by
    simp only [d₄, gpr_write_self, BitVec.setWidth_eq]
    rw [show d₃.gpr .x1 = d₄.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₄]
  have x1₁₂ : d₁₂.gpr .x1 = q := by
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x11),
      gpr_setV]; exact x1₄
  have x12₇ : d₇.gpr .x12 = q + BitVec.ofNat 64 8 := by
    simp only [d₇, d₆, d₅, gpr_setV]; exact x12₄
  have e₁ : exec (.ldr .x .x9 .x1 0) t = some d₁ :=
    VG.AArch64.exec_ldr_x ⟨by decide, by decide⟩ (CallLay.inRegions_sub hrd (by decide : 0 + 8 ≤ 64) (by decide))
  have e₄ : exec (.addImm .x .x12 .x1 8) d₃ = some d₄ := VG.Proof.Rc2.AArch64.Vec.exec_addImmx _ _ _ (by decide)
  have e₅ : exec (.ldrq .v5 .x12 0) d₄ = some d₅ := exec_ldrq' d₄ _ _ 0 ⟨by decide, by decide⟩
    (by rw [x12₄, Offset.add_add]; exact rd _ (by decide))
  have e₈ : exec (.ldrq .v4 .x12 16) d₇ = some d₈ := exec_ldrq' d₇ _ _ 16 ⟨by decide, by decide⟩
    (by rw [x12₇, Offset.add_add]; exact rd _ (by decide))
  have e₉ : exec (.ldrq .v5 .x12 32) d₈ = some d₉ := exec_ldrq' d₈ _ _ 32 ⟨by decide, by decide⟩
    (by rw [show d₈.gpr .x12 = d₇.gpr .x12 from rfl, x12₇, Offset.add_add]; exact rd _ (by decide))
  have e₁₂ : exec (.ldr .x .x11 .x1 56) d₁₁ = some d₁₂ := VG.AArch64.exec_ldr_x ⟨by decide, by decide⟩
    (by
      rw [show d₁₁.gpr .x1 = d₁₂.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₁₂]
      exact CallLay.inRegions_sub hrd (by decide : 56 + 8 ≤ 64) (by decide))
  have wr : ∀ off, off + 16 ≤ 64 → InRegions d₁₂.wr (d₁₂.gpr .x1 + BitVec.ofNat 64 off) 16 :=
    fun off h => by rw [x1₁₂]; exact CallLay.inRegions_sub hwr h (by decide)
  have e₁₃ : exec (.strq .v0 .x1 0) d₁₂ = some d₁₃ := VG.Proof.Rc2.AArch64.Vec.exec_strq _ _ _ 0 ⟨by decide, by decide⟩ (wr 0 (by decide))
  have e₁₄ : exec (.strq .v1 .x1 16) d₁₃ = some d₁₄ := VG.Proof.Rc2.AArch64.Vec.exec_strq _ _ _ 16 ⟨by decide, by decide⟩ (wr 16 (by decide))
  have e₁₅ : exec (.strq .v2 .x1 32) d₁₄ = some d₁₅ := VG.Proof.Rc2.AArch64.Vec.exec_strq _ _ _ 32 ⟨by decide, by decide⟩ (wr 32 (by decide))
  have e₁₆ : exec (.strq .v3 .x1 48) d₁₅ = some d₁₆ := VG.Proof.Rc2.AArch64.Vec.exec_strq _ _ _ 48 ⟨by decide, by decide⟩ (wr 48 (by decide))
  have run : runBlock isa VG.Proof.Rc2.AArch64.Vec.xorCode t = some d₁₆ := by
    rw [VG.Proof.Rc2.AArch64.Vec.xorCode, runBlock_cons, e₁, runStep_some, runBlock_cons, exec_insd _ _ _ (by decide),
      runStep_some, runBlock_cons, exec_insd _ _ _ (by decide), runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, exec_eorv, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_cons, e₉,
      runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, e₁₂, runStep_some, runBlock_cons, e₁₃, runStep_some, runBlock_cons, e₁₄,
      runStep_some, runBlock_cons, e₁₅, runStep_some, runBlock_cons, e₁₆, runStep_some, runBlock_nil]
  -- The values stored.
  have V0 : d₁₂.v .v0 = t.v .v0 ^^^ ofVDwords X (M.readW (q + BitVec.ofNat 64 0) 64) := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq,
      setLane_two] <;> rfl
  have V1 : d₁₂.v .v1 = t.v .v1 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 0) 16 := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  have V2 : d₁₂.v .v2 = t.v .v2 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 16) 16 := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  have V3 : d₁₂.v .v3 = t.v .v3 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 32) 16 := by
    simp (disch := decide) only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  have mem : d₁₆.mem = (((M.write (q + BitVec.ofNat 64 0) 16 (d₁₂.v .v0)).write
      (q + BitVec.ofNat 64 16) 16 (d₁₂.v .v1)).write (q + BitVec.ofNat 64 32) 16 (d₁₂.v .v2)).write
      (q + BitVec.ofNat 64 48) 16 (d₁₂.v .v3) := by
    simp only [d₁₆, d₁₅, d₁₄, d₁₃, x1₁₂]
    rfl
  refine ⟨d₁₆, run, fun o ho => ?_, ?_, ?_, fun g h9 h11 h12 => ?_, fun w h0 h1 h2 h3 h4 h5 => ?_,
    rfl, rfl, rfl⟩
  · rw [mem, VG.Proof.Rc2.AArch64.Vec.write4_at _ _ _ _ _ _ ho, VG.Proof.Rc2.AArch64.Vec.prevByte]
    rcases (by omega : o < 16 ∨ (16 ≤ o ∧ o < 32) ∨ (32 ≤ o ∧ o < 48) ∨ 48 ≤ o) with h | h | h | h <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right]
    · rw [V0, vbyte_xor, (hsc _ (by omega)).1, VG.Proof.Rc2.AArch64.Vec.vbyte_ofVDwords _ _ (by omega),
        show o % 16 = o by omega]
      by_cases h8 : o < 8
      · simp only [h8, ite_true] <;> rfl
      · simp only [h8, ite_false]
        rw [read64_byte _ _ _ (by omega), Offset.add_add, show 0 + (o - 8) = o - 8 by omega]
    · rw [V1, vbyte_xor, (hsc _ (by omega)).2.1, VG.Proof.Rc2.AArch64.Vec.vbyte_read _ _ (by omega), Offset.add_add,
        Offset.add_add, show o / 8 = 2 + o % 16 / 8 by omega, show o % 8 = o % 16 % 8 by omega,
        show 8 + (0 + o % 16) = o - 8 by omega]
    · rw [V2, vbyte_xor, (hsc _ (by omega)).2.2.1, VG.Proof.Rc2.AArch64.Vec.vbyte_read _ _ (by omega), Offset.add_add,
        Offset.add_add, show o / 8 = 4 + o % 16 / 8 by omega, show o % 8 = o % 16 % 8 by omega,
        show 8 + (16 + o % 16) = o - 8 by omega]
    · rw [V3, vbyte_xor, (hsc _ (by omega)).2.2.2, VG.Proof.Rc2.AArch64.Vec.vbyte_read _ _ (by omega), Offset.add_add,
        Offset.add_add, show o / 8 = 6 + o % 16 / 8 by omega, show o % 8 = o % 16 % 8 by omega,
        show 8 + (32 + o % 16) = o - 8 by omega]
  · rw [mem]
    have c : ∀ d, d + 16 ≤ 64 → (⟨q, 64⟩ : Region).Contains (q + BitVec.ofNat 64 d) 16 :=
      fun d h => Offset.contains_base q h (by omega)
    exact (((((Frame.refl _ M).write (List.mem_singleton_self _) _ (c 0 (by decide))).write
      (List.mem_singleton_self _) _ (c 16 (by decide))).write (List.mem_singleton_self _) _
      (c 32 (by decide))).write (List.mem_singleton_self _) _ (c 48 (by decide)))
  · show d₁₂.gpr .x11 = _
    simp only [d₁₂, gpr_write_self, BitVec.setWidth_eq]
    rw [show d₁₁.gpr .x1 = d₁₂.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₁₂]
    rfl
  · show d₁₂.gpr g = t.gpr g
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ h11, gpr_setV,
      gpr_write_of_ne _ _ _ h12, gpr_write_of_ne _ _ _ h9]
  · show d₁₂.v w = t.v w
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_of_ne _ _ h0,
      v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h4,
      v_setV_of_ne _ _ h5]

end VG.Proof.Rc2.AArch64.Vec

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Group`. -/
section

/-!
# One group of eight blocks

`group_ok`: the eight blocks at `x1` decrypted, each XORed with the
ciphertext block before it (the chaining value in `x11` before the first),
in place; the last ciphertext block into `x11`, and `x1` and `x10` advanced.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec VG.Proof.Rc2

/-- The block before block `b` of the group at `q`: the chaining value `X` before the first. -/
def prevBlock (X : BitVec 64) (m : Mem) (q : Addr) (b : Nat) : Spec.Rc2.Block :=
  if b = 0 then wordBlock X else Spec.Rc2.blockAt m (q + BitVec.ofNat 64 (8 * (b - 1)))

structure GroupPost (m : Mem) (p : Addr) (t t' : State) : Prop where
  data : ∀ b < 8, Spec.Rc2.blockAt t'.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b)) =
    Spec.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m p)
        (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b))))
      (VG.Proof.Rc2.AArch64.Vec.prevBlock (t.gpr .x11) t.mem (t.gpr .x1) b)
  frame : Frame [⟨t.gpr .x1, 64⟩] t.mem t'.mem
  chain : t'.gpr .x11 = t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 56) 64
  ptr : t'.gpr .x1 = t.gpr .x1 + BitVec.ofNat 64 64
  count : t'.gpr .x10 = t.gpr .x10 - BitVec.ofNat 64 1
  reg : ∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
    t'.gpr g = t.gpr g
  sched : VG.Proof.Rc2.AArch64.Vec.SchedV t' m p
  mask : t'.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp

theorem exec_subImmx (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp [exec, State.read, h]

/-- The output byte, as a block. -/
theorem out_block {m m' : Mem} {q : Addr} {X : BitVec 64} {R : Nat → Spec.Rc2.State}
    (h : ∀ o < 64, m' (q + BitVec.ofNat 64 o) = VG.Proof.Rc2.AArch64.Vec.encByte (R (o / 8)) (o % 8) ^^^ VG.Proof.Rc2.AArch64.Vec.prevByte X m q o)
    {b : Nat} (hb : b < 8) :
    Spec.Rc2.blockAt m' (q + BitVec.ofNat 64 (8 * b)) =
      Spec.Rc2.xorBlock (Spec.Rc2.encodeBlock (R b)) (VG.Proof.Rc2.AArch64.Vec.prevBlock X m q b) := by
  apply Vector.ext
  intro j hj
  simp only [Spec.Rc2.blockAt, Spec.Rc2.xorBlock, Vector.getElem_ofFn, Offset.add_add, Fin.getElem_fin]
  rw [h _ (by omega), VG.Proof.Rc2.AArch64.Vec.encodeBlock_getElem _ hj, show (8 * b + j) / 8 = b by omega,
    show (8 * b + j) % 8 = j by omega, VG.Proof.Rc2.AArch64.Vec.prevByte, VG.Proof.Rc2.AArch64.Vec.prevBlock]
  by_cases h0 : b = 0
  · subst h0
    simp only [ite_true, wordBlock, Vector.getElem_ofFn, show 8 * 0 + j = j by omega, hj]
  · simp only [show ¬ 8 * b + j < 8 by omega, h0, ite_false, Spec.Rc2.blockAt, Vector.getElem_ofFn,
      Offset.add_add, show 8 * (b - 1) + j = 8 * b + j - 8 by omega]

theorem group_ok {m : Mem} {p : Addr} (t : State) (hs : VG.Proof.Rc2.AArch64.Vec.SchedV t m p) (hm : t.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16)
    (hrd : InRegions (t.rd ++ t.wr) (t.gpr .x1) 64) (hwr : InRegions t.wr (t.gpr .x1) 64) :
    WP isa (.block group) t (VG.Proof.Rc2.AArch64.Vec.GroupPost m p t) := by
  rw [group, VG.Proof.Rc2.AArch64.Vec.storeGroup_eq]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc2.AArch64.Vec.loadGroup_ok t fun c hc => CallLay.inRegions_sub hrd (by omega) (by decide))
    fun a ⟨aS, av, ag, am, ard, awr, asp⟩ => ?_
  have aw : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 →
      (∀ i < 4, ∀ h < 2, w ≠ wreg h i) → a.v w = t.v w := fun w a0 a1 a2 a3 a4 _ hw =>
    av w a0 a1 a2 a3 a4 hw
  have hsA : VG.Proof.Rc2.AArch64.Vec.SchedV a m p := fun r hr => by
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    rw [aw _ a0 a1 a2 a3 a4 a5 fun i hi h hh => ((VG.Proof.Rc2.AArch64.Vec.regs_fixed h i hh hi).2.2.2.2.2.2.2.2 r hr).1]
    exact hs r hr
  have hmA : a.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16 := by
    rw [aw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun i hi h hh => (VG.Proof.Rc2.AArch64.Vec.regs_fixed h i hh hi).2.1]
    exact hm
  let R : Nat → Spec.Rc2.State := fun b => (List.range 16).foldl (VG.Proof.Rc2.AArch64.Vec.revRound (Spec.Rc2.scheduleAt m p))
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b))))
  obtain ⟨b, runb, bS, bk⟩ := VG.Proof.Rc2.AArch64.Vec.rounds_ok hsA hmA aS
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b, runb, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rc2.AArch64.Vec.scatter_ok b (R := R) bS) fun c ⟨cS, cv, cg, cm, crd, cwr, csp⟩ => ?_
  have cx : ∀ g, g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → c.gpr g = t.gpr g := fun g h6 h7 h9 => by
    rw [cg g h6 h7, bk.keep.reg g (by simp [h6, h9]), ag g h6 h7]
  have q₁ : c.gpr .x1 = t.gpr .x1 := cx _ (by decide) (by decide) (by decide)
  have mc : c.mem = t.mem := by rw [cm, bk.keep.mem, am]
  have rdc : c.rd = t.rd := by rw [crd, bk.keep.rd, ard]
  have wrc : c.wr = t.wr := by rw [cwr, bk.keep.wr, awr]
  obtain ⟨d, rund, dmem, dframe, d11, dg, dv, drd, dwr, dsp⟩ := VG.Proof.Rc2.AArch64.Vec.xorStore_ok c (R := R) cS
    (by rw [rdc, wrc, q₁]; exact hrd) (by rw [wrc, q₁]; exact hwr)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨d, rund, ?_⟩
  let e := d.write .x .x1 (d.gpr .x1 + BitVec.ofNat 64 64)
  let f := e.write .x .x10 (e.gpr .x10 - BitVec.ofNat 64 1)
  refine WP.of_runBlock ⟨f, by
    rw [runBlock_cons, VG.Proof.Rc2.AArch64.Vec.exec_addImmx _ _ _ (by decide), runStep_some, runBlock_cons,
      VG.Proof.Rc2.AArch64.Vec.exec_subImmx _ _ _ (by decide), runStep_some, runBlock_nil], ?_⟩
  have fg : ∀ g, g ≠ .x1 → g ≠ .x10 → f.gpr g = d.gpr g := fun g h1 h10 => by
    simp only [f, e, gpr_write_of_ne _ _ _ h10, gpr_write_of_ne _ _ _ h1]
  have x11 : c.gpr .x11 = t.gpr .x11 := cx _ (by decide) (by decide) (by decide)
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, ?_, fun g h1 h6 h7 h9 h10 h11 h12 => ?_, fun r hr => ?_, ?_,
    by simp only [f, e, rd_write]; rw [drd, rdc], by simp only [f, e, wr_write]; rw [dwr, wrc],
    by simp only [f, e, sp_write]; rw [dsp, csp, bk.sp, asp]⟩
  · have := VG.Proof.Rc2.AArch64.Vec.out_block (R := R) dmem hb
    rw [q₁, x11, mc] at this
    simp only [f, e, mem_write]
    rw [this, VG.Proof.Rc2.AArch64.Vec.revRounds_eq]
  · simp only [f, e, mem_write]; rw [← mc, ← q₁]; exact dframe
  · rw [fg _ (by decide) (by decide), d11, mc, q₁]
  · simp only [f, e, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x10), gpr_write_self,
      BitVec.setWidth_eq]
    rw [dg _ (by decide) (by decide) (by decide), q₁]
  · simp only [f, gpr_write_self, BitVec.setWidth_eq, e, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x10 = .x1)]
    rw [dg _ (by decide) (by decide) (by decide), cx _ (by decide) (by decide) (by decide)]
  · rw [fg g h1 h10, dg g h9 h11 h12, cx g h6 h7 h9]
  · simp only [f, e, v_write]
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega)
    rw [dv _ a0 a1 a2 a3 a4 a5, cv _ a0 a1 a2 a3 a4, bk.sched r hr]
    exact hsA r hr
  · simp only [f, e, v_write]
    rw [dv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      cv _ (by decide) (by decide) (by decide) (by decide) (by decide), bk.mask]
    exact hmA

end VG.Proof.Rc2.AArch64.Vec

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Vec.Loop`. -/
section

/-!
# The loop over groups

`loopV_ok`: `j` groups of eight blocks at `x1`, decrypted in CBC mode from the
chaining value in `x11`, which is left the last ciphertext block.
-/

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec VG.Proof.Rc2

/-- A group, as CBC on its eight blocks. -/
theorem GroupPost.cbc {m : Mem} {p : Addr} {t t' : State} (h : VG.Proof.Rc2.AArch64.Vec.GroupPost m p t t') :
    Spec.Rc2.blocksAt t'.mem (t.gpr .x1) 8 = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p) .decrypt
      (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) 8)).1 ∧
    wordBlock (t'.gpr .x11) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p) .decrypt
      (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) 8)).2 := by
  rw [cbc_decrypt]
  constructor
  · apply List.ext_getElem (by simp [blocksAt_length])
    intro i h₁ h₂
    have hi : i < 8 := by simpa [blocksAt_length] using h₁
    rw [List.getElem_zipWith, blocksAt_getElem, blocksAt_getElem, h.data i hi, VG.Proof.Rc2.AArch64.Vec.prevBlock]
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.getElem_cons_succ, blocksAt_getElem, Nat.add_sub_cancel, Nat.add_one_ne_zero,
        ite_false]
  · rw [h.chain, ← blockAt_read64, List.getLast_eq_getElem]
    simp only [List.length_cons, blocksAt_length, Nat.add_sub_cancel, List.getElem_cons_succ,
      blocksAt_getElem]

structure LoopVPost (m : Mem) (p : Addr) (t : State) (j : Nat) (t' : State) : Prop where
  ptr : t'.gpr .x1 = t.gpr .x1 + BitVec.ofNat 64 (64 * j)
  count : t'.gpr .x10 = 0
  reg : ∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
    t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  frame : Frame [⟨t.gpr .x1, 64 * j⟩] t.mem t'.mem
  data : Spec.Rc2.blocksAt t'.mem (t.gpr .x1) (8 * j) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p)
    .decrypt (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) (8 * j))).1
  chain : wordBlock (t'.gpr .x11) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt m p)
    .decrypt (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) (8 * j))).2

theorem ofNat_ne_zero {a : Nat} (h : 0 < a) (h' : a < 2 ^ 64) : BitVec.ofNat 64 a ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h', show (0 : BitVec 64).toNat = 0 from rfl] at this
  omega

theorem loopV_ok (m : Mem) (p : Addr) (j : Nat) :
    ∀ t : State, 1 ≤ j → 64 * j < 2 ^ 64 → VG.Proof.Rc2.AArch64.Vec.SchedV t m p → t.v m16 = VG.Proof.Rc2.AArch64.Vec.mask16 →
      t.gpr .x10 = BitVec.ofNat 64 j →
      InRegions (t.rd ++ t.wr) (t.gpr .x1) (64 * j) → InRegions t.wr (t.gpr .x1) (64 * j) →
      WP isa (.loop (.block group) (.nonzero .x .x10)) t (VG.Proof.Rc2.AArch64.Vec.LoopVPost m p t j) := by
  induction j with
  | zero => intro t h; omega
  | succ j ih =>
    intro t _ bound hs hm count hrd hwr
    have z : t.gpr .x1 + BitVec.ofNat 64 0 = t.gpr .x1 := BitVec.add_zero _
    obtain ⟨t₀, s₁, exec₁, h₁⟩ := VG.Proof.Rc2.AArch64.Vec.group_ok (m := m) (p := p) t hs hm
      (by have := CallLay.inRegions_sub hrd (by omega : 0 + 64 ≤ 64 * (j + 1)) (by omega)
          rwa [z] at this)
      (by have := CallLay.inRegions_sub hwr (by omega : 0 + 64 ≤ 64 * (j + 1)) (by omega)
          rwa [z] at this)
    have c₁ : s₁.gpr .x10 = BitVec.ofNat 64 j := by
      rw [h₁.count, count, Offset.ofNat_sub_ofNat (by omega)]; rfl
    have g8 := h₁.cbc
    by_cases hz : j = 0
    · subst hz
      refine ⟨_, s₁, Exec.loopExit exec₁ (by simp [eval, State.read, c₁]), ?_⟩
      refine ⟨by rw [h₁.ptr], c₁, fun g a b c d e f i => h₁.reg g a b c d e f i, h₁.rd, h₁.wr,
        h₁.sp, h₁.frame, g8.1, g8.2⟩
    · obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega) (by omega) h₁.sched h₁.mask c₁
        (by rw [h₁.rd, h₁.wr, h₁.ptr]; exact CallLay.inRegions_sub hrd (by omega) (by omega))
        (by rw [h₁.wr, h₁.ptr]; exact CallLay.inRegions_sub hwr (by omega) (by omega))
      refine ⟨_, s₂, Exec.loopNext exec₁ (by
        simp [eval, State.read, c₁]; exact VG.Proof.Rc2.AArch64.Vec.ofNat_ne_zero (by omega) (by omega)) exec₂, ?_⟩
      let q := t.gpr .x1
      have q₁ : s₁.gpr .x1 = q + BitVec.ofNat 64 64 := h₁.ptr
      -- The first group's blocks, left by the rest; the rest's, by the first.
      have keepFirst : Spec.Rc2.blocksAt s₂.mem q 8 = Spec.Rc2.blocksAt s₁.mem q 8 :=
        blocksAt_frame h₂.frame q 8 (by
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          rw [q₁]
          exact Offset.base_disjoint q (by omega) (by omega))
      have keepRest : Spec.Rc2.blocksAt s₁.mem (q + BitVec.ofNat 64 64) (8 * j) =
          Spec.Rc2.blocksAt t.mem (q + BitVec.ofNat 64 64) (8 * j) :=
        blocksAt_frame h₁.frame _ _ (by
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact Offset.disjoint_base q (by omega) (by omega))
      have split : ∀ mm : Mem, Spec.Rc2.blocksAt mm q (8 * (j + 1)) =
          Spec.Rc2.blocksAt mm q 8 ++ Spec.Rc2.blocksAt mm (q + BitVec.ofNat 64 64) (8 * j) :=
        fun mm => by rw [show 8 * (j + 1) = 8 + 8 * j by omega, blocksAt_add]
      have data₂ := h₂.data
      have chain₂ := h₂.chain
      rw [q₁, keepRest, g8.2] at data₂ chain₂
      refine ⟨?_, h₂.count, fun g a b c d e f i => (h₂.reg g a b c d e f i).trans
        (h₁.reg g a b c d e f i), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, ?_, ?_, ?_⟩
      · rw [h₂.ptr, q₁, Offset.add_add, show 64 + 64 * j = 64 * (j + 1) by omega]
      · refine (h₁.frame.sub ?_).trans (h₂.frame.sub ?_)
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          rw [q₁]
          exact ⟨_, List.mem_singleton_self _, Offset.sub_base q (by omega)⟩
      · rw [split, split, keepFirst, g8.1, cbc_append, data₂]
      · rw [chain₂, split, cbc_append]

end VG.Proof.Rc2.AArch64.Vec

end
