module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Bignum.Arm.CrtAdvanceLink

/-! # Named offsets for each CRT pointer advancement -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_linkStep_ok (s : State) {base : BitVec 32} {size d x step y w : Nat}
    (ws : Workspace s base size) (fit : d + 4 ≤ size) (hd : d < 4096)
    (ptr : s.gpr .r0 = base) (current : s.gpr .r2 = base + BitVec.ofNat 32 x)
    (increment : s.gpr .r1 = BitVec.ofNat 32 step) (width : s.gpr .r7 = BitVec.ofNat 32 w)
    (next : y = x + step) :
    WP isa (.block (advanceLink d)) s fun t =>
      t.gpr .r0 = base ∧ t.gpr .r2 = base + BitVec.ofNat 32 y ∧
      t.gpr .r1 = BitVec.ofNat 32 step ∧ t.gpr .r7 = BitVec.ofNat 32 w ∧
      t.mem = s.mem.writeW (off (State.addr base) d) (base + BitVec.ofNat 32 y) ∧ Rest [.r2] s t := by
  refine WP.mono (crt_advanceLink_ok s ws fit hd ptr) ?_
  rintro t ⟨value, mem, rest⟩
  have result : s.gpr .r2 + s.gpr .r1 = base + BitVec.ofNat 32 y := by
    rw [current, increment, BitVec.add_assoc, ← BitVec.ofNat_add, ← next]
  exact ⟨(rest.gpr .r0 (by simp)).trans ptr, value.trans result,
    (rest.gpr .r1 (by simp)).trans increment, (rest.gpr .r7 (by simp)).trans width,
    by rw [mem, result], rest⟩

end VG.Proof.Bignum.Arm
