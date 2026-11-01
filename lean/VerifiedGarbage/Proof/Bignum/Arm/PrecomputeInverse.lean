module
public import VerifiedGarbage.Impl.Bignum.Arm.Precompute
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady

import VerifiedGarbage.Proof.Bignum.Arm.InverseArgs
import VerifiedGarbage.Proof.Bignum.Arm.ModulusReady
import VerifiedGarbage.Proof.Bignum.Arm.InverseReady
import VerifiedGarbage.Proof.Framework.Block

/-! # Establish arithmetic readiness from an imported odd RSA modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest)

theorem precomputeInverse_r2_ok (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ptr : s.gpr .r0 = base)
    (odd : numAt s.mem (State.addr base) w 0 % 2 = 1)
    (large : 1 < numAt s.mem (State.addr base) w 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa precomputeInverse s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧
      numAt t.mem (State.addr base) w 4 = numAt s.mem (State.addr base) w 4 := by
  have hw : 2 ≤ w := width ▸ layout.1
  rw [precomputeInverse, WP.seq_iff]
  refine WP.mono (inverseArgs_ok s ws layout width ptr) ?_
  rintro u ⟨modptr, baseReg, mem, rest⟩
  refine WP.mono (initInverse_ready_r2 u (ws.congr rest.wr) (by rw [mem]; exact layout)
    (by rw [mem]; exact width) modptr baseReg
    (by rw [mem]; exact numAt_low_odd s.mem _ (by omega) odd)
    (by rw [mem]; exact large)
    (by rw [rest.rd, rest.wr, rest.sp]; exact stackRead)
    (by rw [rest.sp]; exact stackSep) (by rw [mem, rest.sp]; exact saved)) ?_
  rintro t ⟨ready, number, frame, keep, r2⟩
  rw [mem] at number frame r2
  exact ⟨ready, number, frame, (rest.mono (by decide)).trans keep, r2⟩

theorem precomputeInverse_ok (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ptr : s.gpr .r0 = base)
    (odd : numAt s.mem (State.addr base) w 0 % 2 = 1)
    (large : 1 < numAt s.mem (State.addr base) w 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa precomputeInverse s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  exact WP.mono (precomputeInverse_r2_ok s ws layout width ptr odd large stackRead stackSep saved)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)

end VG.Proof.Bignum.Arm
