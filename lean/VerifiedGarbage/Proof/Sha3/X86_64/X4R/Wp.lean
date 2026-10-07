import VerifiedGarbage.Proof.Sha3.X86_64.X4.Wp
import VerifiedGarbage.Impl.Sha3.X86_64.X4Reg

/-!
# Keccak-f[1600] four times at once, in registers: one instruction at a time

Weakest-precondition rules for the EVEX-encoded instructions of `permute4R`
(`Impl/Sha3/X86_64/X4Reg.lean`) on the thirty-two `ymm` registers, in terms
of the four 64-bit elements of each (`qy`), one per state.
-/

namespace VG.Proof.Sha3.X86_64.X4R

open VG VG.X86_64 VG.Impl.Sha3.X86_64.X4R

/-- Element `k` (`k < 4`) of `ymm r`. -/
def qy (s : State) (r : VReg) (k : Nat) : BitVec 64 := qword256 (s.vy r) k

/-! ## Values -/

theorem extract_xor (a b : BitVec 256) (i n : Nat) :
    (a ^^^ b).extractLsb' i n = a.extractLsb' i n ^^^ b.extractLsb' i n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

theorem extract_or (a b : BitVec 256) (i n : Nat) :
    (a ||| b).extractLsb' i n = a.extractLsb' i n ||| b.extractLsb' i n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [hj]

/-- The two lanes of a value, put back together. -/
theorem lanes_cat (v : BitVec 256) : lane256 v 1 ++ lane256 v 0 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < 128
  · simp [lane256, h]
  · simp [lane256, h, show j - 128 < 128 by omega, show 128 + (j - 128) = j by omega]

theorem qword256_xor (a b : BitVec 256) (k : Nat) : qword256 (a ^^^ b) k = qword256 a k ^^^ qword256 b k :=
  extract_xor _ _ _ _

theorem qword256_or (a b : BitVec 256) (k : Nat) : qword256 (a ||| b) k = qword256 a k ||| qword256 b k :=
  extract_or _ _ _ _

/-- Quadword `k` (`k < 4`) of a 256-bit value. -/
theorem qword256_eq (x : BitVec 256) (k : Nat) :
    qword256 x k = qword (x.extractLsb' (128 * (k / 2)) 128) (k % 2) := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword256, qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and,
    decide_eq_true (show 64 * (k % 2) + j < 128 by omega)]
  congr 1; omega

theorem lane_app0 (x y : BitVec 128) : (x ++ y).extractLsb' 0 128 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, Nat.zero_add]
  rw [BitVec.getLsbD_append]; simp [hj]

theorem lane_app1 (x y : BitVec 128) : (x ++ y).extractLsb' 128 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_append]; simp [hj]

/-- Element `k` of a value made of two lanes. -/
theorem qword256_lanes (x y : BitVec 128) {k : Nat} (hk : k < 4) :
    qword256 (x ++ y) k = qword (if k / 2 = 0 then y else x) (k % 2) := by
  rw [qword256_eq]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceDiv, Nat.reduceMul, Nat.reduceMod, lane_app0, lane_app1, ite_true, ite_false,
      Nat.one_ne_zero]

/-- Element `k` of a value made of the two lanes of a three-operand operation. -/
theorem qword256_lanes3 (f : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) (a b c : BitVec 256)
    {k : Nat} (hk : k < 4) :
    qword256 (f (lane256 a 1) (lane256 b 1) (lane256 c 1) ++ f (lane256 a 0) (lane256 b 0) (lane256 c 0)) k =
      qword (f (lane256 a (k / 2)) (lane256 b (k / 2)) (lane256 c (k / 2))) (k % 2) := by
  rw [qword256_lanes _ _ hk]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-- Element `k` of each lane-wise result: of the lanes `k / 2`. -/
theorem qword256_lanes256 (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 256) {k : Nat} (hk : k < 4) :
    qword256 (lanes256 f a b) k = qword (f (lane256 a (k / 2)) (lane256 b (k / 2))) (k % 2) := by
  rw [lanes256, qword256_lanes _ _ hk]
  rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

/-- Element `j` of a lane, as an element of the whole. -/
theorem qword_lane (v : BitVec 256) {k : Nat} (_hk : k < 4) : qword (lane256 v (k / 2)) (k % 2) = qword256 v k := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [qword256, qword, lane256, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  have : 64 * (k % 2) + j < 128 := by omega
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

theorem qword_xor (x y : BitVec 128) (i : Nat) : qword (x ^^^ y) i = qword x i ^^^ qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword, hj]

theorem qword_or (x y : BitVec 128) (i : Nat) : qword (x ||| y) i = qword x i ||| qword y i := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; simp [qword, hj]

theorem ternlog96 (a b c : BitVec 128) : ternlog a b c 0x96 = a ^^^ b ^^^ c := by
  simp only [ternlog, List.range, List.range.loop, List.foldl, show (0x96 : BitVec 8).getLsbD 0 = false from rfl, show (0x96 : BitVec 8).getLsbD 1 = true from rfl, show (0x96 : BitVec 8).getLsbD 2 = true from rfl, show (0x96 : BitVec 8).getLsbD 3 = false from rfl, show (0x96 : BitVec 8).getLsbD 4 = true from rfl, show (0x96 : BitVec 8).getLsbD 5 = false from rfl, show (0x96 : BitVec 8).getLsbD 6 = false from rfl, show (0x96 : BitVec 8).getLsbD 7 = true from rfl, Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj,
    decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem ternlogD2 (a b c : BitVec 128) : ternlog a b c 0xD2 = (~~~b &&& c) ^^^ a := by
  simp only [ternlog, List.range, List.range.loop, List.foldl, show (0xD2 : BitVec 8).getLsbD 0 = false from rfl, show (0xD2 : BitVec 8).getLsbD 1 = true from rfl, show (0xD2 : BitVec 8).getLsbD 2 = false from rfl, show (0xD2 : BitVec 8).getLsbD 3 = false from rfl, show (0xD2 : BitVec 8).getLsbD 4 = true from rfl, show (0xD2 : BitVec 8).getLsbD 5 = false from rfl, show (0xD2 : BitVec 8).getLsbD 6 = true from rfl, show (0xD2 : BitVec 8).getLsbD 7 = true from rfl, Nat.testBit, Nat.reduceShiftRight, Nat.reduceAnd, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, show (0 : BitVec 128).getLsbD j = false from BitVec.getLsbD_zero, hj,
    decide_true, Bool.true_and]
  generalize a.getLsbD j = x; generalize b.getLsbD j = y; generalize c.getLsbD j = z
  revert x y z; decide

theorem qword_tern96 (a b c : BitVec 128) (i : Nat) :
    qword (ternlog a b c 0x96) i = qword a i ^^^ qword b i ^^^ qword c i := by
  rw [ternlog96, qword_xor, qword_xor]

theorem qword_ternD2 (a b c : BitVec 128) {i : Nat} (hi : i < 2) :
    qword (ternlog a b c 0xD2) i = (qword b i ^^^ 0xffffffffffffffff) &&& qword c i ^^^ qword a i := by
  rw [ternlogD2]
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have e : (0xffffffffffffffff : BitVec 64).getLsbD j = true := by
    rw [show (0xffffffffffffffff : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.getLsbD_allOnes]; simp [hj]
  simp only [qword, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_and, BitVec.getLsbD_not, e, show 64 * i + j < 128 by omega]
  cases b.getLsbD (64 * i + j) <;> rfl

theorem qword_ror (x : BitVec 128) (n : BitVec 8) {i : Nat} (hi : i < 2) :
    qword (rorQwords x n) i = (qword x i).rotateRight (n.toNat % 64) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [rorQwords, VG.Proof.Sha3.X86_64.X4.qword_app0,
    VG.Proof.Sha3.X86_64.X4.qword_app1]

/-! ## The machine -/

theorem qy_setVy (s : State) (d r : VReg) (v : BitVec 256) (k : Nat) :
    qy (s.setVy d v) r k = if r = d then qword256 v k else qy s r k := by
  cases d with
  | lo d =>
    cases r with
    | lo r =>
      simp only [qy, State.vy, State.setVy, VReg.lo.injEq]
      by_cases h : r = d
      · subst h
        simp only [ite_true, State.ymm, State.setV]
        congr 1
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        rw [BitVec.getLsbD_append]
        by_cases h' : j < 128
        · simp [h']
        · simp [h', show j - 128 < 128 by omega, show 128 + (j - 128) = j by omega]
      · simp only [h, ite_false, State.ymm, State.setV]
    | hi r => simp only [qy, State.vy, State.setVy, reduceCtorEq, ite_false]; rfl
  | hi d =>
    cases r with
    | lo r => simp only [qy, State.vy, State.setVy, reduceCtorEq, ite_false]; rfl
    | hi r =>
      simp only [qy, State.vy, State.setVy, VReg.hi.injEq]
      split <;> rfl

/-- `s'` is `s` with `ymm d` set to the four elements `v`. -/
structure YUpd (s s' : State) (d : VReg) (v : Nat → BitVec 64) : Prop where
  val : ∀ k < 4, qy s' d k = v k
  other : ∀ r, r ≠ d → ∀ k < 4, qy s' r k = qy s r k
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  zf : s'.zf = s.zf

theorem YUpd.setVy (s : State) (d : VReg) (w : BitVec 256) {v : Nat → BitVec 64}
    (hv : ∀ k < 4, qword256 w k = v k) : YUpd s (s.setVy d w) d v :=
  ⟨fun k hk => by rw [qy_setVy, ite_eq_left rfl]; exact hv k hk,
    fun r hr k _ => by rw [qy_setVy, ite_eq_right hr], by cases d <;> rfl, by cases d <;> rfl,
    by cases d <;> rfl, by cases d <;> rfl, by cases d <;> rfl⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_exor {d a b : VReg} (k : ∀ s', YUpd s s' d (fun i => qy s a i ^^^ qy s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (eb .vpxorq d a b :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes256 _ _ _ hi]
    simp only [EBinOp.sse, XBinOp.eval, qword_xor, qword_lane _ hi]; rfl))

theorem wp_ecopy {d a : VReg} (k : ∀ s', YUpd s s' d (fun i => qy s a i) → WP isa (.block is) s' Q) :
    WP isa (.block (copy d a :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes256 _ _ _ hi]
    simp only [EBinOp.sse, XBinOp.eval, qword_lane _ hi, BitVec.or_self]; rfl))

theorem wp_tern96 {d a b : VReg}
    (k : ∀ s', YUpd s s' d (fun i => qy s d i ^^^ qy s a i ^^^ qy s b i) → WP isa (.block is) s' Q) :
    WP isa (.block (tern d a b 0x96 :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes3 (fun x y z => ternlog x y z 0x96) _ _ _ hi, qword_tern96, qword_lane _ hi, qword_lane _ hi,
      qword_lane _ hi]; rfl))

theorem wp_ternD2 {d a b : VReg}
    (k : ∀ s', YUpd s s' d (fun i => (qy s a i ^^^ 0xffffffffffffffff) &&& qy s b i ^^^ qy s d i) →
      WP isa (.block is) s' Q) :
    WP isa (.block (tern d a b 0xD2 :: is)) s Q :=
  WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes3 (fun x y z => ternlog x y z 0xD2) _ _ _ hi, qword_ternD2 _ _ _ (by omega), qword_lane _ hi,
      qword_lane _ hi, qword_lane _ hi]; rfl))

theorem wp_eror {d a : VReg} {n : Nat} (hn : n < 64)
    (k : ∀ s', YUpd s s' d (fun i => (qy s a i).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (ror d a n :: is)) s Q := by
  have en : (BitVec.ofNat 8 n).toNat % 64 = n := by rw [BitVec.toNat_ofNat]; omega
  exact WP.cons rfl (k _ (YUpd.setVy _ _ _ fun i hi => by
    rw [qword256_lanes256 _ _ _ hi, qword_ror _ _ (by omega), en, qword_lane _ hi]; rfl))

theorem wp_evld {d : VReg} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 32)
    (k : ∀ s', YUpd s s' d (fun i => s.mem.readW (a + BitVec.ofNat 64 (8 * i)) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.evLoad d m :: is)) s Q :=
  WP.cons (s' := s.setVy d (s.mem.readW a 256))
    (by simp only [exec, ha, State.load256, hin, ite_true, Option.map_some])
    (k _ (YUpd.setVy _ _ _ fun i hi => by
      rw [qword256, show 64 * i = 8 * (8 * i) by omega]
      exact readW_extract _ _ (k := 8 * i) (n := 8) (by omega)))

theorem wp_evst {m : MemOp} {r : VReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 32)
    (k : WP isa (.block is) { s with mem := s.mem.writeW a (s.vy r) } Q) :
    WP isa (.block (.evStore m r :: is)) s Q :=
  WP.cons (by simp [exec, State.store256, ha, hout]) k

end

/-- Element `k` of a stored register, read back. -/
theorem readW_evst (m : Mem) (a : Addr) (s : State) (r : VReg) {k : Nat} (hk : k < 4) :
    (m.writeW a (s.vy r)).readW (a + BitVec.ofNat 64 (8 * k)) 64 = qy s r k := by
  have e := readW_writeW_inside m a (s.vy r) (k := 8 * k) (n := 8) (by omega) (by decide)
  rw [show 8 * (8 * k) = 64 * k by omega] at e
  exact e

end VG.Proof.Sha3.X86_64.X4R
