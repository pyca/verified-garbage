module

public import VerifiedGarbage.Proof.Bignum.Arm.R2
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoop
import VerifiedGarbage.Proof.Framework.Block

/-! A normalized modulus lets R-squared setup begin at the top radix bit.
The existing modular doubling loop and six squarings are shared unchanged. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

/-- Starting at `R/2` needs only `w+1` doublings to reach `2^(65*w)`. -/
theorem r2NormalizedLoop_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : DoubleLoopReady base len w (w + 1) s)
    (top : numAt s.mem (State.addr base) w 4 = 2 ^ (64 * w - 1))
    (large : 1 < numAt s.mem (State.addr base) w 0)
    (countFits : 128 * w < 2 ^ 32) :
    WP isa doubleLoop s fun v => R2Sq base len w (numAt s.mem (State.addr base) w 0) w v ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem v.mem ∧ Rest roundClobbers s v := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  refine WP.mono (doubleLoop_ok s h (by omega) (by omega)) ?_
  rintro v ⟨done, value, modV, frameV, restV⟩
  have powers : 2 ^ (w + 1) * 2 ^ (64 * w - 1) = 2 ^ (64 * w + w) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [top, powers] at value
  exact ⟨⟨⟨done.workspace, done.layout, done.width, done.ptr, done.inverse,
      by rw [modV]; exact large, done.stackRead, done.stackSep, done.saved⟩,
    modV, modV ▸ done.operand, by rw [value, Nat.mod_mod], done.two, done.counter⟩,
    frameV, restV⟩

end VG.Proof.Bignum.Arm
