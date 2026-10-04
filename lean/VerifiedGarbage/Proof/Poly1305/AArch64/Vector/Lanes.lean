import VerifiedGarbage.Proof.Curve448.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Poly1305.AArch64.Vector

/-!
# Poly1305 on AArch64 in AdvSIMD: the lanes of the operations

Untrusted: everything here is checked by Lean. Executing the AdvSIMD
instructions of `Vector`, and the 64-bit lanes (`ln`) and 32-bit words (`wd`)
of their results, as numbers.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Curve448.AArch64.Neon (map2_0 map2_1 vdword_and uzp1_0 uzp1_1 uzp1_2 uzp1_3 vword_lo)

/-- Lane `e` (64 bits) and word `c` (32 bits) of a vector, as numbers. -/
abbrev ln (x : BitVec 128) (e : Nat) : Nat := (vdword x e).toNat
abbrev wd (x : BitVec 128) (c : Nat) : Nat := (vword x c).toNat

/-! ## Execution -/

theorem exec_vo {op : VOp} {s : State} {d : VReg} {x : BitVec 128} (h : op.eval s = some (d, x)) :
    isa.exec (vo op) s = some (s.setV d x) := by
  show (op.eval s).map (fun p => s.setV p.1 p.2) = _
  rw [h]; rfl

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    isa.exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, and_self, ite_true, Option.bind_some, State.load, hr]
  rfl

theorem exec_umov (s : State) (d : Reg) (n : VReg) {i : Nat} (hi : i < 2) :
    isa.exec (.umov .x d n i) s = some (s.write .x d (vdword (s.v n) i)) := by
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl

theorem exec_str {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (hw : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    isa.exec (.str .x t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 8 (s.gpr t) } := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some, State.store, hw, State.read]
  rfl

theorem exec_ldr {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    isa.exec (.ldr .x t n off) s =
      some (s.write .x t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 8)) := by
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, Option.bind_some, State.load, hr]
  rfl

/-! ## 64-bit lanes -/

theorem ln_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VArr.d2.map2 f x y) e = f 64 (vdword x e) (vdword y e) := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact map2_0 f x y
  · exact map2_1 f x y

theorem ln_ushr (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    ln (VArr.d2.map2 (fun w a b => VShiftOp.ushr.eval sh w a b) y x) e = ln x e / 2 ^ sh := by
  simp only [ln, ln_map2 _ _ _ he, VShiftOp.eval, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem ln_shl (y x : BitVec 128) (sh : Nat) {e : Nat} (he : e < 2) :
    ln (VArr.d2.map2 (fun w a b => VShiftOp.shl.eval sh w a b) y x) e = ln x e * 2 ^ sh % 2 ^ 64 := by
  simp only [ln, ln_map2 _ _ _ he, VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem ln_add (x y : BitVec 128) {e : Nat} (he : e < 2) :
    ln (VArr.d2.map2 (fun _ a b => a + b) x y) e = (ln x e + ln y e) % 2 ^ 64 := by
  simp only [ln, ln_map2 _ _ _ he, BitVec.toNat_add]

theorem ln_and_mask (x m : BitVec 128) {e : Nat} (hm : ln m e = 2 ^ 26 - 1) :
    ln (x &&& m) e = ln x e % 2 ^ 26 := by
  have hm' : (vdword m e).toNat = 2 ^ 26 - 1 := hm
  rw [ln, vdword_and, BitVec.toNat_and, hm', Nat.and_two_pow_sub_one_eq_mod]

theorem ln_or (x y : BitVec 128) (e : Nat) : ln (x ||| y) e = ln x e ||| ln y e := by
  have : vdword (x ||| y) e = vdword x e ||| vdword y e := by
    ext i hi
    simp [vdword, BitVec.getElem_extractLsb', BitVec.getElem_or]
  rw [ln, this, BitVec.toNat_or]

theorem ln_or_pad (x p : BitVec 128) {e : Nat} (hp : ln p e = 2 ^ 24) (hx : ln x e < 2 ^ 24) :
    ln (x ||| p) e = ln x e + 2 ^ 24 := by
  have h := Nat.two_pow_add_eq_or_of_lt hx 1
  rw [Nat.mul_one] at h
  rw [ln_or, hp, Nat.or_comm, ← h, Nat.add_comm]

/-- `sli d, n, #12` of a lane of `d` below `2¹²`. -/
theorem ln_sli (y x : BitVec 128) {e : Nat} (he : e < 2) (hy : ln y e < 2 ^ 12) :
    ln (VArr.d2.map2 (fun w a b => VShiftOp.sli.eval 12 w a b) y x) e = ln x e * 2 ^ 12 % 2 ^ 64 + ln y e := by
  have hb : (vdword y e &&& ~~~(BitVec.allOnes 64 <<< 12)) = vdword y e := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_shiftLeft, BitVec.toNat_allOnes]
    rw [show (2 ^ 64 - 1) <<< 12 % 2 ^ 64 = 2 ^ 64 - 2 ^ 12 by decide,
      show 2 ^ 64 - 1 - (2 ^ 64 - 2 ^ 12) = 2 ^ 12 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hy]
  simp only [ln, ln_map2 _ _ _ he, VShiftOp.eval, hb]
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.or_comm]
  have hm : (vdword x e).toNat * 2 ^ 12 % 2 ^ 64 = 2 ^ 12 * ((vdword x e).toNat % 2 ^ 52) := by omega
  rw [hm, ← Nat.two_pow_add_eq_or_of_lt hy, hm.symm, Nat.add_comm]

theorem zip1_0 (x y : BitVec 128) : vdword (VPermOp.eval .zip1 .d2 x y) 0 = vdword x 0 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_0]

theorem zip1_1 (x y : BitVec 128) : vdword (VPermOp.eval .zip1 .d2 x y) 1 = vdword y 0 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_1]

theorem zip2_0 (x y : BitVec 128) : vdword (VPermOp.eval .zip2 .d2 x y) 0 = vdword x 1 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_0]

theorem zip2_1 (x y : BitVec 128) : vdword (VPermOp.eval .zip2 .d2 x y) 1 = vdword y 1 := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, vdword_ofVDwords_1]

/-- Lane `e` of `zip1`/`zip2` of two loaded blocks: word 0 or 1 of block `e`. -/
theorem zip1_ln (x y : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VPermOp.eval .zip1 .d2 x y) e = vdword (if e = 0 then x else y) 0 := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact zip1_0 x y
  · exact zip1_1 x y

theorem zip2_ln (x y : BitVec 128) {e : Nat} (he : e < 2) :
    vdword (VPermOp.eval .zip2 .d2 x y) e = vdword (if e = 0 then x else y) 1 := by
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
  · exact zip2_0 x y
  · exact zip2_1 x y

/-! ## 32-bit words -/

/-- `uzp1 v.4s, x.4s, x.4s`: the low halves of the 64-bit lanes, twice. -/
theorem wd_uzp_self (x : BitVec 128) {c : Nat} (hc : c < 4) :
    wd (VPermOp.eval .uzp1 .s4 x x) c = ln x (c % 2) % 2 ^ 32 := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [wd, uzp1_0, show (vword x 0).toNat = _ from vword_lo x 0]
  · rw [wd, uzp1_1, show (vword x 2).toNat = _ from vword_lo x 1]
  · rw [wd, uzp1_2, show (vword x 0).toNat = _ from vword_lo x 0]
  · rw [wd, uzp1_3, show (vword x 2).toNat = _ from vword_lo x 1]

theorem wd_map2 (f : (w : Nat) → BitVec w → BitVec w → BitVec w) (x y : BitVec 128) {c : Nat}
    (hc : c < 4) : wd (VArr.s4.map2 f x y) c = (f 32 (vword x c) (vword y c)).toNat := by
  rw [wd, vword_map2 f x y hc]

/-- `5 x` of a word below `2³⁰ / 5`, by `shl #2` and `add`. -/
theorem wd_times5 (x y : BitVec 128) {c : Nat} (hc : c < 4) (hx : wd x c < 2 ^ 29) :
    wd (VArr.s4.map2 (fun _ a b => a + b)
      (VArr.s4.map2 (fun w a b => VShiftOp.shl.eval 2 w a b) y x) x) c = 5 * wd x c := by
  rw [wd_map2 _ _ _ hc, BitVec.toNat_add, vword_map2 _ _ _ hc]
  simp only [VShiftOp.eval, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [wd] at hx ⊢
  omega

/-! ## Inserting lanes -/

theorem vword_setLane (v : BitVec 128) {j c : Nat} (hj : j < 4) (hc : c < 4) (x : BitVec 32) :
    vword (setLane v 32 j x) c = if c = j then x else vword v c := by
  by_cases h : c = j
  · subst h
    simp only [ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have e1 : ¬ 32 * c + b < 32 * c := by omega
    have e2 : 32 * c + b - 32 * c = b := by omega
    have e3 : b < 128 := by omega
    have h1 : 32 * c + b < 128 := by omega
    simp only [vword, setLane, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, h1, e1, e2, e3, decide_false, Bool.not_false,
      Bool.not_true, Bool.and_false, Bool.false_or]
  · simp only [h, ite_false]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have h1 : 32 * c + b < 128 := by omega
    have hm : (32 * c + b < 32 * j) ∨ ¬ 32 * c + b - 32 * j < 32 := by omega
    simp only [vword, setLane, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, h1]
    rcases hm with hm | hm
    · simp only [hm, decide_true, Bool.not_true, Bool.false_and, Bool.or_false, Bool.not_false, Bool.and_true]
    · have hn : ¬ 32 * c + b < 32 * j := by omega
      have hx' : x.getLsbD (32 * c + b - 32 * j) = false := x.getLsbD_of_ge _ (by omega)
      simp only [hn, hm, hx', decide_false, Bool.not_false, Bool.and_false, Bool.and_true, Bool.or_false]

theorem vdword_setLane (v : BitVec 128) {j e : Nat} (hj : j < 2) (he : e < 2) (x : BitVec 64) :
    vdword (setLane v 64 j x) e = if e = j then x else vdword v e := by
  by_cases h : e = j
  · subst h
    simp only [ite_true]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have e1 : ¬ 64 * e + b < 64 * e := by omega
    have e2 : 64 * e + b - 64 * e = b := by omega
    have e3 : b < 128 := by omega
    have h1 : 64 * e + b < 128 := by omega
    simp only [vdword, setLane, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, h1, e1, e2, e3, decide_false, Bool.not_false,
      Bool.not_true, Bool.and_false, Bool.false_or]
  · simp only [h, ite_false]
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    have h1 : 64 * e + b < 128 := by omega
    have hm : (64 * e + b < 64 * j) ∨ ¬ 64 * e + b - 64 * j < 64 := by omega
    simp only [vdword, setLane, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
      BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, h1]
    rcases hm with hm | hm
    · simp only [hm, decide_true, Bool.not_true, Bool.false_and, Bool.or_false, Bool.not_false, Bool.and_true]
    · have hn : ¬ 64 * e + b < 64 * j := by omega
      have hx' : x.getLsbD (64 * e + b - 64 * j) = false := x.getLsbD_of_ge _ (by omega)
      simp only [hn, hm, hx', decide_false, Bool.not_false, Bool.and_false, Bool.and_true, Bool.or_false]

end VG.Proof.Poly1305.AArch64.Vector
