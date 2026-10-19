module
public import VerifiedGarbage.Impl.Bignum.Arm.ExportArray
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import Batteries.Logic
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Mont

import VerifiedGarbage.Proof.Bignum.Arm.ExportArray
import VerifiedGarbage.Proof.Bignum.Arm.ArrayFrame
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Export a modulus into a zero-padded full-product buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt wOf Layout numAt)
open VG.Proof.X25519.Arm (Rest)

theorem exportPadded_ok (s : State) {base : BitVec 32} {len w o d k : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ho : o < 8)
    (fit : base.toNat + d + 4 * (2 * w + k) ≤ 2 ^ 32)
    (write : InRegions s.wr (off (State.addr base) d) (8 * w))
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨off (State.addr base) d, 8 * w⟩)
    (zero : val32 s.mem (State.addr base) (d + 8 * w) k = 0)
    (ptr : s.gpr .r0 = base) (index : s.gpr .r2 = BitVec.ofNat 32 o)
    (output : s.gpr .r4 = base + BitVec.ofNat 32 d) :
    WP isa exportArray s fun t =>
      val32 t.mem (State.addr base) d (2 * w + k) = numAt s.mem (State.addr base) w o ∧
      Outside (State.addr base) d (8 * w) s.mem t.mem ∧
      t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := width ▸ layout.1
  have dstAddr : State.addr (base + BitVec.ofNat 32 d) = off (State.addr base) d := addr_add (by omega)
  have dstNat : (base + BitVec.ofNat 32 d).toNat = base.toNat + d := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : d < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : base.toNat + d < 2 ^ 32)]
  refine WP.mono (exportArray_ok s ws layout width ho (by rw [dstNat]; omega)
    (by rw [dstAddr]; exact write) (by rw [dstAddr]; exact sep) ptr index output) ?_
  rintro t ⟨value, frame, ptrT, _, rest⟩
  rw [dstAddr] at value frame
  have outside := frame_array_outside (by omega : d + 8 * w < 2 ^ 64) frame
  have high := outside.val32 (d := d + 8 * w) (k := k) (by omega) (by omega)
  have low : val32 t.mem (State.addr base) d (2 * w) = numAt s.mem (State.addr base) w o := by
    rw [← read_eq_val32, show 4 * (2 * w) = 8 * w by omega, value]
    rfl
  refine ⟨?_, outside, ptrT, rest⟩
  rw [val32_append, show d + 4 * (2 * w) = d + 8 * w by omega, high, zero,
    Nat.mul_zero, Nat.add_zero, low]

end VG.Proof.Bignum.Arm
