module

public import VerifiedGarbage.Impl.Bignum.Arm.NormalizedR2
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.NormalizedR2Init
import VerifiedGarbage.Proof.Bignum.Arm.SharedR2
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Framework.Block

/-! Normalized R-squared setup reaches the existing six shared squarings. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- Starting at the highest radix word saves `64 * (w - 1)` doublings. -/
theorem normalizedR2Loop_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : DoubleLoopReady base len w (w + 64) s)
    (seed : numAt s.mem (State.addr base) w 4 = 2 ^ (64 * (w - 1)))
    (large : 1 < numAt s.mem (State.addr base) w 0) (countFits : 128 * w < 2 ^ 32) :
    WP isa doubleLoop s fun v => R2Sq base len w (numAt s.mem (State.addr base) w 0) w v ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem v.mem ∧ Rest roundClobbers s v := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  refine WP.mono (doubleLoop_ok s h (by omega) (by omega)) ?_
  rintro v ⟨done, value, modV, frameV, restV⟩
  rw [seed, ← Nat.pow_add, show w + 64 + 64 * (w - 1) = 64 * w + w by omega] at value
  exact ⟨⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse, by rw [modV]; exact large,
      done.stackRead, done.stackSep, done.saved⟩, modV, modV ▸ done.operand,
      by rw [value, Nat.mod_mod], done.two, done.counter⟩, frameV, restV⟩

theorem normalizedR2_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State)
    (h : ArithmeticReady base len w s) (hp : P s) (countFits : 128 * w < 2 ^ 32)
    (normalized : 2 ^ (64 * (w - 1)) ≤ numAt s.mem (State.addr base) w 0) :
    WP isa (NormalizedR2.r2 K.op) s fun t => DoubleLoopReady base len w 0 t ∧
      numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  rw [NormalizedR2.r2, WP.seq_iff]
  refine WP.mono (normalizedR2Init_ok s h normalized) ?_
  rintro u ⟨ready, one, modulus, frame, rest⟩
  have pU := K.stable frame rest hp
  rw [WP.seq_iff]
  refine WP.mono (normalizedR2Loop_ok u ready one (by rw [modulus]; exact h.modulus) countFits) ?_
  rintro v ⟨sq, frameV, restV⟩
  rw [modulus] at sq
  have pV := K.stable frameV restV pU
  refine WP.mono (sharedR2Squares_ok K v sq pV) ?_
  rintro t ⟨fin, pT, frameT, restT⟩
  have exact : numAt t.mem (State.addr base) w 4 = 2 ^ (128 * w) % numAt s.mem (State.addr base) w 0 := by
    rw [← Nat.mod_eq_of_lt fin.operand, fin.value, show 64 * w + 64 * w = 128 * w by omega]
  refine ⟨⟨fin.ready.workspace, fin.ready.layout, fin.ready.width, fin.ready.ptr, fin.ready.inverse,
      by rw [fin.modulus]; exact fin.operand, fin.two, fin.counter, fin.ready.stackRead,
      fin.ready.stackSep, fin.ready.saved⟩, exact, fin.modulus,
    pT, (Frame.mono (frame.trans frameV) (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace)).trans frameT, rest.trans (restV.trans restT)⟩

end VG.Proof.Bignum.Arm
