module

public import VerifiedGarbage.Proof.MlKem.Blocks
public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Impl.MlKem.X86_64.NttAvx2
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: AVX2 registers, the pieces

Words of a 256-bit store (`wordAt_write256`), and what `vpermq`, the
broadcast of a 128-bit load and `vpblendd` do to the lanes of a register
(`ypermq_ok`, `ybcast_ok`, `yblend_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## Words in both lanes -/

/-- Word `e` of a 256-bit register, as stored. -/
theorem word_ymm (s : State) (r : XReg) {e : Nat} (he : e < 16) :
    (s.ymm r).extractLsb' (8 * (2 * e)) (8 * 2) = word (s.lane r (e / 8)) (e % 8) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  by_cases h : e < 8
  · simp only [show 8 * (2 * e) + j < 128 by bdd_omega, ite_true, show e / 8 = 0 by bdd_omega]
    exact congrArg _ (by bdd_omega)
  · simp only [show ¬ 8 * (2 * e) + j < 128 by bdd_omega, ite_false, show e / 8 = 1 by bdd_omega, Nat.one_ne_zero]
    exact congrArg _ (by bdd_omega)

/-- Word `i` after storing `x` (256 bits) at word `j`. -/
theorem wordAt_write256 (m : Mem) (p : Addr) {j : Nat} (hj : j + 16 ≤ 256) (x : BitVec 256) {i : Nat}
    (hi : i < 256) :
    wordAt (m.writeW (wAddr p j) x) p i =
      if j ≤ i ∧ i < j + 16 then x.extractLsb' (8 * (2 * (i - j))) (8 * 2) else wordAt m p i := by
  split
  · rename_i h
    rw [wordAt, show wAddr p i = wAddr p j + BitVec.ofNat 64 (2 * (i - j)) by
      rw [wAddr_add, show j + (i - j) = i by bdd_omega]]
    exact readW_writeW_inside (k := 2 * (i - j)) (n := 2) _ _ _ (by bdd_omega) (by decide)
  · exact Mem.readW_writeW_sep (Offset.sep p (by bdd_omega) (by bdd_omega) (by bdd_omega)) (by decide)

/-! ## Across lanes -/

/-- `vperm2i128`. -/
theorem yperm_ok {d a b : XReg} {n : BitVec 8} (s : State) :
    WP isa (.block [.vop (.vperm2i128 d a b n)]) s fun s' =>
      (∀ l < 2, s'.lane d l = perm2Lanes (s.lane a) (s.lane b) n l) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem perm20 (a b : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    perm2Lanes a b 0x20 l = if l = 0 then a 0 else b 0 := by
  rcases lane01 hl with rfl | rfl <;> rfl

theorem perm31 (a b : Nat → BitVec 128) {l : Nat} (hl : l < 2) :
    perm2Lanes a b 0x31 l = if l = 0 then a 1 else b 1 := by
  rcases lane01 hl with rfl | rfl <;> rfl

theorem q256lo (a b : BitVec 128) {i : Nat} (hi : i < 2) : qword256 (b ++ a) i = qword a i :=
  BitVec.extractLsb'_append_eq_of_add_le (by bdd_omega)

theorem q256hi (a b : BitVec 128) (i : Nat) : qword256 (b ++ a) (2 + i) = qword b i := by
  rw [qword256, BitVec.extractLsb'_append_eq_of_le (by bdd_omega), show 64 * (2 + i) - 128 = 64 * i by bdd_omega]; rfl

theorem lo4 (w x y z : BitVec 64) : (w ++ x ++ y ++ z).extractLsb' 0 128 = y ++ z := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and, Nat.zero_add]
  by_cases h : i < 64
  · simp only [h, ite_true]
  · simp only [h, ite_false, show i - 64 < 64 by bdd_omega, ite_true]

theorem hi4 (w x y z : BitVec 64) : (w ++ x ++ y ++ z).extractLsb' 128 128 = w ++ x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    show ¬ 128 + i < 64 by bdd_omega, ite_false, show ¬ 128 + i - 64 < 64 by bdd_omega]
  by_cases h : i < 64
  · simp only [h, ite_true, show 128 + i - 64 - 64 < 64 by bdd_omega]; exact congrArg _ (by bdd_omega)
  · simp only [h, ite_false, show ¬ 128 + i - 64 - 64 < 64 by bdd_omega]; exact congrArg _ (by bdd_omega)

theorem permD8 (a b : BitVec 128) :
    permQwords (b ++ a) 0xD8 = qword256 (b ++ a) (2 + 1) ++ qword256 (b ++ a) 1 ++
      qword256 (b ++ a) (2 + 0) ++ qword256 (b ++ a) 0 := rfl

/-- `vpermq` with `0xD8`: lane 0 is `punpcklqdq` of the two lanes. -/
theorem permD8_lo (a b : BitVec 128) :
    (permQwords (b ++ a) 0xD8).extractLsb' 0 128 = XBinOp.eval .punpcklqdq a b := by
  rw [permD8, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), lo4]; rfl

/-- `vpermq` with `0xD8`: lane 1 is `punpckhqdq` of the two lanes. -/
theorem permD8_hi (a b : BitVec 128) :
    (permQwords (b ++ a) 0xD8).extractLsb' 128 128 = XBinOp.eval .punpckhqdq a b := by
  rw [permD8, q256hi, q256hi, q256lo _ _ (by decide), q256lo _ _ (by decide), hi4]; rfl

/-- `vpermq d, r, 0xD8`. -/
theorem ypermq_ok {d r : XReg} (s : State) :
    WP isa (.block [.vop (.vpermq d r 0xD8)]) s fun s' =>
      s'.lane d 0 = XBinOp.eval .punpcklqdq (s.lane r 0) (s.lane r 1) ∧
      s'.lane d 1 = XBinOp.eval .punpckhqdq (s.lane r 0) (s.lane r 1) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r' hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, State.ymm_eq, permD8_lo]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), State.ymm_eq, permD8_hi]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-! ## The zetas -/

theorem wp_cons_iff {i : Instr} {l : List Instr} {s : State} {Q : State → Prop} :
    WP isa (.block (i :: l)) s Q ↔ WP isa (.block [i]) s fun s1 => WP isa (.block l) s1 Q := by
  rw [← WP.block_append_iff]; rfl

/-- A 128-bit load into both lanes. -/
theorem ybcast_ok {s : State} {p : Reg} {off : Nat} {d : XReg}
    (h : InRegions (s.rd ++ s.wr) (s.gpr p + BitVec.ofNat 64 off) 16) :
    WP isa (.block [.vbroadcasti128 d (at_ p off)]) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW (s.gpr p + BitVec.ofNat 64 off) 128) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, ea_at, h, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem blend0 (a b : BitVec 128) : blendDwords a b (BitVec.extractLsb' 0 4 (0xF0 : BitVec 8)) = a :=
  ext_dword (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords])

theorem blendF (a b : BitVec 128) : blendDwords a b (BitVec.extractLsb' 4 4 (0xF0 : BitVec 8)) = b :=
  ext_dword (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords]) (by simp [blendDwords])

/-- `vpblendd d, a, b, 0xF0`: lane 0 of `a` and lane 1 of `b`. -/
theorem yblend_ok {d a b : XReg} (s : State) :
    WP isa (.block [.vop (.vpblendd .l256 d a b 0xF0)]) s fun s' =>
      s'.lane d 0 = s.lane a 0 ∧ s'.lane d 1 = s.lane b 1 ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, ifp rfl, blend0]
  · rw [State.lane_setV256, ifp rfl, ifn (by decide), blendF]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

end VG.Proof.MlKem.X86_64
