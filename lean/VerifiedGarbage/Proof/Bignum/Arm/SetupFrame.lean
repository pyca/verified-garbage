module

import VerifiedGarbage.Proof.Bignum.Arm.Setup
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Impl.Bignum.Arm.Setup
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Workspace setup changes only bytes within the caller's scratch buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf Layout)
open VG.Proof.X25519.Arm (Rest)

theorem outs_workspace {m m' : Mem} {base : Addr} {size : Nat} {ranges : List (Nat × Nat)}
    (outside : VG.Proof.Mont.Outs base ranges m m')
    (fit : ∀ r ∈ ranges, r.1 + r.2 ≤ size) : Frame [⟨base, size⟩] m m' := by
  intro a ha
  have h := ha ⟨base, size⟩ (by simp)
  change ¬ ((a - base).toNat + 1 ≤ size) at h
  apply outside
  intro r hr
  right
  have bound := fit r hr
  change r.1 + r.2 ≤ (a - base).toNat
  omega

theorem setup_frame_ok (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (fits : arrAt w 8 ≤ 8 * len) (ptr : s.gpr .r0 = base)
    (count : s.gpr .r7 = BitVec.ofNat 32 w) (zero : s.gpr .r3 = 0) :
    WP isa setup s fun t => Layout t.mem (State.addr base) len ∧
      wOf t.mem (State.addr base) = w ∧ t.gpr .r0 = base ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  refine WP.mono (setup_ok s ws hw hw' fits ptr count zero) ?_
  rintro t ⟨layout, width, ptr, outside, rest⟩
  refine ⟨layout, width, ptr, outs_workspace outside ?_, rest.mono (by decide)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> omega

end VG.Proof.Bignum.Arm
