module

public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleCountMemory
import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Complete R-squared computation from a valid RSA workspace

`65 w` doublings leave `2^(64 w + w)` in array 4, and each of the six
Montgomery squarings takes `2^(64 w + k)` to `2^(64 w + 2 k)` (modulo the odd
modulus `m`, cancelling `R = 2^(64 w)`), so that the last leaves
`2^(128 w) mod m = R² mod m`. -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

/-- A modulus with an inverse modulo `2^64` is odd. -/
theorem numAt_odd_of_inverse (mem : Mem) (base : Addr) {w : Nat} (hw : 0 < w) {y : Nat}
    (h : ((VG.Proof.Mont.word mem base (arrAt w 0)).toNat * y + 1) % 2 ^ 64 = 0) :
    numAt mem base w 0 % 2 = 1 := by
  have split : numAt mem base w 0 = (VG.Proof.Mont.word mem base (arrAt w 0)).toNat +
      2 ^ 64 * VG.Proof.Mont.wordsVal mem base (arrAt w 0 + 8) (w - 1) := by
    unfold numAt
    rw [read_eq_wordsVal]
    exact congrArg (fun n => VG.Proof.Mont.wordsVal mem base (arrAt w 0) n)
      (show w = (w - 1) + 1 by omega_using [hw])
  generalize (VG.Proof.Mont.word mem base (arrAt w 0)).toNat = x at h split
  have two : 2 ∣ x * y + 1 := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (by decide : 2 ^ 64 % 2 = 0))
    (Nat.dvd_of_mod_eq_zero h)
  have odd : x % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · have : (x * y + 1) % 2 = 1 := by rw [Nat.add_mod, Nat.mul_mod, hx]; simp
      omega_using [h, this]
    · exact hx
  omega_using [split, odd]

/-- A Montgomery square of `2^(64 w + k)` is `2^(64 w + 2 k)`. -/
theorem r2_square_value {o v m w k : Nat} (hm : m % 2 = 1) (hv : v % m = 2 ^ (64 * w + k) % m)
    (h : o * 2 ^ (64 * w) % m = v * v % m) : o % m = 2 ^ (64 * w + 2 * k) % m := by
  apply VG.Proof.Bignum.mont_cancel (coprime_pow2 hm (64 * w))
  rw [h, Nat.mul_mod, hv, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add]
  congr 2
  omega_using []

/-- What the squarings keep and need. -/
structure R2Sq (base : BitVec 32) (len w m k : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = m
  operand : numAt s.mem (State.addr base) w 4 < m
  value : numAt s.mem (State.addr base) w 4 % m = 2 ^ (64 * w + k) % m
  two : w32 s.mem (State.addr base) (arrAt w 7) = 2
  counter : s.mem.readW (off (State.addr base) 208) 32 = BitVec.ofNat 32 0

/-- One squaring of array 4 in place doubles the exponent above `64 w`. -/
theorem r2Square_ok (s : State) {base : BitVec 32} {len w m k : Nat} (h : R2Sq base len w m k s) :
    WP isa (squareOp 4 4) s fun t => R2Sq base len w m (2 * k) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have odd : m % 2 = 1 := h.modulus ▸ numAt_odd_of_inverse s.mem _ (by omega_using [hw]) h.ready.inverse
  refine WP.mono (squareOp_ok s h.ready op4 op4 (by decide) (by rw [h.modulus]; exact h.operand)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at modulus bound value
  refine ⟨⟨ready, modulus, bound, r2_square_value odd h.value value, ?_, ?_⟩, frame, rest⟩
  · have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega_using [])
    simp only [Nat.add_zero] at this
    change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter

/-! ## The squarings' loop

`r2Squares` counts its six squarings in header byte 208, which the
doublings leave zero. Its state is `SqC`: `R2Sq` with the count `c` there,
and its value only under `P`, so that the fold of `PrimeR2From`, whose value
holds only for a factor of `n`, shares the loop. -/

/-- The squarings' state, the count `c` at header byte 208 and the value
only under `P`. -/
structure SqC (base : BitVec 32) (len w m : Nat) (P : Prop) (k c : Nat) (s : State) : Prop where
  ready : ArithmeticReady base len w s
  modulus : numAt s.mem (State.addr base) w 0 = m
  operand : numAt s.mem (State.addr base) w 4 < m
  value : P → numAt s.mem (State.addr base) w 4 % m = 2 ^ (64 * w + k) % m
  two : w32 s.mem (State.addr base) (arrAt w 7) = 2
  counter : s.mem.readW (off (State.addr base) 208) 32 = BitVec.ofNat 32 c

theorem R2Sq.toC {s : State} {base : BitVec 32} {len w m k : Nat} (h : R2Sq base len w m k s) :
    SqC base len w m True k 0 s :=
  ⟨h.ready, h.modulus, h.operand, fun _ => h.value, h.two, h.counter⟩

theorem SqC.toR2Sq {s : State} {base : BitVec 32} {len w m k : Nat} (h : SqC base len w m True k 0 s) :
    R2Sq base len w m k s :=
  ⟨h.ready, h.modulus, h.operand, h.value trivial, h.two, h.counter⟩

theorem SqC.toDouble {s : State} {base : BitVec 32} {len w m k c : Nat} {P : Prop}
    (h : SqC base len w m P k c s) : DoubleLoopReady base len w c s :=
  ⟨h.ready.workspace, h.ready.layout, h.ready.width, h.ready.ptr, h.ready.inverse,
    by rw [h.modulus]; exact h.operand, h.two, h.counter, h.ready.stackRead, h.ready.stackSep, h.ready.saved⟩

/-- A write of the count leaves the rest of the state. -/
theorem SqC.after_count {s t : State} {base : BitVec 32} {len w m k c c' : Nat} {P : Prop}
    (h : SqC base len w m P k c s)
    (mem : t.mem = s.mem.writeW (off (State.addr base) 208) (BitVec.ofNat 32 c'))
    (rest : Rest [.r1] s t) :
    SqC base len w m P k c' t ∧ Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by
  obtain ⟨d, frame, n4, n0⟩ := h.toDouble.after_count mem rest
  refine ⟨⟨⟨d.workspace, d.layout, d.width, d.ptr, d.inverse, by rw [n0]; exact h.ready.modulus,
      d.stackRead, d.stackSep, d.saved⟩, n0.trans h.modulus, by rw [n4]; exact h.operand,
    fun p => by rw [n4]; exact h.value p, d.two, d.counter⟩, frame⟩

/-- One squaring keeps the count and doubles the exponent above `64 w`. -/
theorem sqC_square_ok (s : State) {base : BitVec 32} {len w m k c : Nat} {P : Prop}
    (h : SqC base len w m P k c s) :
    WP isa (squareOp 4 4) s fun t => SqC base len w m P (2 * k) c t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain hw : 2 ≤ w := h.ready.width ▸ h.ready.layout.1
  obtain fits : arrAt w 8 ≤ 8 * len := h.ready.width ▸ h.ready.layout.2.2.1
  obtain size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  obtain op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  obtain odd : m % 2 = 1 := h.modulus ▸ numAt_odd_of_inverse s.mem _ (by omega_using [hw]) h.ready.inverse
  refine WP.mono (squareOp_ok s h.ready op4 op4 (by decide) (by rw [h.modulus]; exact h.operand)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at modulus bound value
  refine ⟨⟨ready, modulus, bound, fun p => r2_square_value odd (h.value p) value, ?_, ?_⟩, frame, rest⟩
  · have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega_using [])
    simp only [Nat.add_zero] at this
    change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter

/-- A squaring, then the count down. -/
theorem sqC_step_ok (s : State) {base : BitVec 32} {len w m k c : Nat} {P : Prop}
    (h : SqC base len w m P k c s) (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa r2SquareStep s fun t => SqC base len w m P (2 * k) (c - 1) t ∧ t.z = decide (c = 1) ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2SquareStep, WP.seq_iff]
  refine WP.mono (sqC_square_ok s h) ?_
  rintro u ⟨hu, frameU, restU⟩
  obtain fits := hu.ready.layout.2.2.1
  obtain size : 212 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  refine WP.mono (doubleCount_ok u hu.ready.workspace size hu.ready.ptr hc hc' hu.counter) ?_
  rintro t ⟨mem, zero, keep⟩
  obtain ⟨ht, frameT⟩ := hu.after_count mem keep
  exact ⟨ht, zero, frameU.trans frameT, restU.trans (keep.mono (by decide))⟩

/-- The count, six. -/
theorem r2SquareCount_ok (s : State) {base : BitVec 32} {len w m k : Nat} {P : Prop}
    (h : SqC base len w m P k 0 s) :
    WP isa (.block r2SquareCount) s fun t => SqC base len w m P k 6 t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  obtain ws := h.ready.workspace
  obtain fits := h.ready.layout.2.2.1
  obtain size : 212 ≤ 8 * len := by
    rw [h.ready.width] at fits; simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega_using [fits]
  obtain nowrap := ws.nowrap
  obtain addr : State.addr (s.gpr .r0 + BitVec.ofNat 32 208) = off (State.addr base) 208 := by
    rw [h.ready.ptr]; exact addr_add (by omega_using [size, nowrap])
  unfold r2SquareCount
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun s1 u1 => ?_
  refine wp_str_z (a := off (State.addr base) 208) (by decide)
    (by rw [u1.other .r0 (by decide)]; exact addr)
    (by rw [u1.wr]; exact ws.write (by omega_using [size])) fun t u2 _ => WP.block_nil ?_
  obtain rest : Rest [.r1] s t := (u1.rest (by simp)).trans (u2.rest _)
  obtain ⟨ht, frame⟩ := h.after_count (c' := 6) (by rw [u2.mem, u1.mem, u1.gpr]; rfl) rest
  exact ⟨ht, frame, rest⟩

/-- The squarings' loop, from the count `c`: `c` squarings. -/
theorem sqC_loop_ok (s : State) {base : BitVec 32} {len w m k c : Nat} {P : Prop}
    (h : SqC base len w m P k c s) (hc : 0 < c) (hc' : c < 2 ^ 32) :
    WP isa (.loop r2SquareStep .ne) s fun t => SqC base len w m P (2 ^ c * k) 0 t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let inv := fun j t => ∃ i, i + j = c ∧ 0 < j ∧ SqC base len w m P (2 ^ i * k) j t ∧
    Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t
  refine WP.loop (M := isa) inv ?_ c s ⟨0, by omega_using [], hc, by rw [Nat.pow_zero, Nat.one_mul]; exact h,
    Frame.refl _ _, Rest.refl _ _⟩
  intro j t hi
  obtain ⟨i, hij, hj, ht, frame, rest⟩ := hi
  refine WP.mono (sqC_step_ok t ht hj (by omega_using [hc', hij])) ?_
  rintro u ⟨hu, zero, frameU, restU⟩
  rw [show 2 * (2 ^ i * k) = 2 ^ (i + 1) * k by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]] at hu
  by_cases exit : j = 1
  · left
    refine ⟨?_, ?_, frame.trans frameU, rest.trans restU⟩
    · change some (!u.z) = some false
      simp only [zero, exit, decide_true, Bool.not_true]
    · rw [show c = i + 1 by omega_using [hij, exit]]
      simpa only [exit, Nat.sub_self] using hu
  · right
    refine ⟨?_, j - 1, by omega_using [hj], i + 1, by omega_using [hij, hj], by omega_using [hj, exit], hu,
      frame.trans frameU, rest.trans restU⟩
    change some (!u.z) = some true
    simp only [zero, exit, decide_false, Bool.not_false]

/-- The six squarings, as a `SqC` from the count zero. -/
theorem sqC_squares_ok (s : State) {base : BitVec 32} {len w m k : Nat} {P : Prop}
    (h : SqC base len w m P k 0 s) :
    WP isa r2Squares s fun t => SqC base len w m P (64 * k) 0 t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [r2Squares, WP.seq_iff]
  refine WP.mono (r2SquareCount_ok s h) ?_
  rintro u ⟨hu, frameU, restU⟩
  refine WP.mono (sqC_loop_ok u hu (by decide) (by decide)) ?_
  rintro t ⟨ht, frameT, restT⟩
  rw [show (2 : Nat) ^ 6 = 64 from rfl] at ht
  exact ⟨ht, frameU.trans frameT, (restU.mono (by decide)).trans restT⟩

/-- The six squarings. -/
theorem r2Squares_ok (s : State) {base : BitVec 32} {len w m : Nat} (h : R2Sq base len w m w s) :
    WP isa r2Squares s fun t => R2Sq base len w m (64 * w) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t :=
  WP.mono (sqC_squares_ok s h.toC) fun _ ⟨ht, frame, rest⟩ => ⟨ht.toR2Sq, frame, rest⟩

/-- The doublings, from one: `2^(65 w)`. -/
theorem r2Loop_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : DoubleLoopReady base len w (65 * w) s) (one : numAt s.mem (State.addr base) w 4 = 1)
    (large : 1 < numAt s.mem (State.addr base) w 0) (countFits : 128 * w < 2 ^ 32) :
    WP isa doubleLoop s fun v => R2Sq base len w (numAt s.mem (State.addr base) w 0) w v ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem v.mem ∧ Rest roundClobbers s v := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  refine WP.mono (doubleLoop_ok s h (by omega_using [hw]) (by omega_using [countFits])) ?_
  rintro v ⟨done, value, modV, frameV, restV⟩
  rw [one, Nat.mul_one] at value
  exact ⟨⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse, by rw [modV]; exact large,
      done.stackRead, done.stackSep, done.saved⟩, modV, modV ▸ done.operand,
      by rw [value, Nat.mod_mod, show 65 * w = 64 * w + w by omega_using []], done.two, done.counter⟩,
    frameV, restV⟩

theorem r2_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) (countFits : 128 * w < 2 ^ 32) :
    WP isa r2 s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  rw [r2, WP.seq_iff]
  refine WP.mono (r2Init_ok s h) ?_
  rintro u ⟨ready, one, modulus, frame, rest⟩
  rw [WP.seq_iff]
  refine WP.mono (r2Loop_ok u ready one (by rw [modulus]; exact h.modulus) countFits) ?_
  rintro v ⟨sq, frameV, restV⟩
  rw [modulus] at sq
  refine WP.mono (r2Squares_ok v sq) ?_
  rintro t ⟨fin, frameT, restT⟩
  have exact : numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 := by
    rw [← Nat.mod_eq_of_lt fin.operand, fin.value, show 64 * w + 64 * w = 128 * w by omega_using []]
  refine ⟨⟨fin.ready.workspace, fin.ready.layout, fin.ready.width, fin.ready.ptr, fin.ready.inverse,
      by rw [fin.modulus]; exact fin.operand, fin.two, fin.counter, fin.ready.stackRead,
      fin.ready.stackSep, fin.ready.saved⟩, exact, fin.modulus,
    frame.trans (frameV.trans frameT), rest.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
