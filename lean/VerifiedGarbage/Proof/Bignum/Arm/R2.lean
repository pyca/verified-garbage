module
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState

import VerifiedGarbage.Proof.Bignum.Arm.R2Init
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Bignum.Arm.SquareOp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.Block

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
      (show w = (w - 1) + 1 by omega)
  generalize (VG.Proof.Mont.word mem base (arrAt w 0)).toNat = x at h split
  have two : 2 ∣ x * y + 1 := Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (by decide : 2 ^ 64 % 2 = 0))
    (Nat.dvd_of_mod_eq_zero h)
  have odd : x % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · have : (x * y + 1) % 2 = 1 := by rw [Nat.add_mod, Nat.mul_mod, hx]; simp
      omega
    · exact hx
  omega

/-- A Montgomery square of `2^(64 w + k)` is `2^(64 w + 2 k)`. -/
theorem r2_square_value {o v m w k : Nat} (hm : m % 2 = 1) (hv : v % m = 2 ^ (64 * w + k) % m)
    (h : o * 2 ^ (64 * w) % m = v * v % m) : o % m = 2 ^ (64 * w + 2 * k) % m := by
  apply VG.Proof.Bignum.mont_cancel (coprime_pow2 hm (64 * w))
  rw [h, Nat.mul_mod, hv, ← Nat.mul_mod, ← Nat.pow_add, ← Nat.pow_add]
  congr 2
  omega

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
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have odd : m % 2 = 1 := h.modulus ▸ numAt_odd_of_inverse s.mem _ (by omega) h.ready.inverse
  refine WP.mono (squareOp_ok s h.ready op4 op4 (by decide) (by rw [h.modulus]; exact h.operand)) ?_
  rintro t ⟨ready, modulus, bound, value, keeps, frame, rest⟩
  rw [h.modulus] at modulus bound value
  refine ⟨⟨ready, modulus, bound, r2_square_value odd h.value value, ?_, ?_⟩, frame, rest⟩
  · have := keeps_array_word (d := 0) (bits := 32) keeps fits op7 (by decide) (by omega)
    simp only [Nat.add_zero] at this
    change (t.mem.readW (off (State.addr base) (arrAt w 7)) 32).toNat = 2
    rw [this]; exact h.two
  · rw [keeps_header_readW keeps size (d := 208) (bits := 32) (by decide)]; exact h.counter

/-- The six squarings. -/
theorem r2Squares_ok (s : State) {base : BitVec 32} {len w m : Nat} (h : R2Sq base len w m w s) :
    WP isa r2Squares s fun t => R2Sq base len w m (64 * w) t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold r2Squares
  refine WP.seq (WP.mono (r2Square_ok s h) fun s1 ⟨h1, f1, r1⟩ => ?_)
  refine WP.seq (WP.mono (r2Square_ok s1 h1) fun s2 ⟨h2, f2, r2⟩ => ?_)
  refine WP.seq (WP.mono (r2Square_ok s2 h2) fun s3 ⟨h3, f3, r3⟩ => ?_)
  refine WP.seq (WP.mono (r2Square_ok s3 h3) fun s4 ⟨h4, f4, r4⟩ => ?_)
  refine WP.seq (WP.mono (r2Square_ok s4 h4) fun s5 ⟨h5, f5, r5⟩ => ?_)
  refine WP.mono (r2Square_ok s5 h5) fun t ⟨h6, f6, r6⟩ => ?_
  refine ⟨?_, f1.trans (f2.trans (f3.trans (f4.trans (f5.trans f6)))),
    r1.trans (r2.trans (r3.trans (r4.trans (r5.trans r6))))⟩
  have e : 2 * (2 * (2 * (2 * (2 * (2 * w))))) = 64 * w := by omega
  rw [e] at h6
  exact h6

/-- The doublings, from one: `2^(65 w)`. -/
theorem r2Loop_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : DoubleLoopReady base len w (65 * w) s) (one : numAt s.mem (State.addr base) w 4 = 1)
    (large : 1 < numAt s.mem (State.addr base) w 0) (countFits : 128 * w < 2 ^ 32) :
    WP isa doubleLoop s fun v => R2Sq base len w (numAt s.mem (State.addr base) w 0) w v ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem v.mem ∧ Rest roundClobbers s v := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  refine WP.mono (doubleLoop_ok s h (by omega) (by omega)) ?_
  rintro v ⟨done, value, modV, frameV, restV⟩
  rw [one, Nat.mul_one] at value
  exact ⟨⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse, by rw [modV]; exact large,
      done.stackRead, done.stackSep, done.saved⟩, modV, modV ▸ done.operand,
      by rw [value, Nat.mod_mod, show 65 * w = 64 * w + w by omega], done.two, done.counter⟩,
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
    rw [← Nat.mod_eq_of_lt fin.operand, fin.value, show 64 * w + 64 * w = 128 * w by omega]
  refine ⟨⟨fin.ready.workspace, fin.ready.layout, fin.ready.width, fin.ready.ptr, fin.ready.inverse,
      by rw [fin.modulus]; exact fin.operand, fin.two, fin.counter, fin.ready.stackRead,
      fin.ready.stackSep, fin.ready.saved⟩, exact, fin.modulus,
    frame.trans (frameV.trans frameT), rest.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
