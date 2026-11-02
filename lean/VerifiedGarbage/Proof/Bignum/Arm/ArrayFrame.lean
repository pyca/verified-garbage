module
public import VerifiedGarbage.Proof.Rsa.MontContract
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.Arm.Isa

import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Translate native-array byte frames to the shared RSA workspace -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt)

theorem frame_array_outside {m m' : Mem} {base : Addr} {d n : Nat}
    (fit : d + n < 2 ^ 64) (frame : Frame [⟨off base d, n⟩] m m') :
    Outside base d n m m' := by
  intro a ha
  apply frame a
  intro r hr hc
  simp only [List.mem_singleton] at hr
  subst r
  change (a - off base d).toNat + 1 ≤ n at hc
  have inside : (a - off base d).toNat < n := by omega
  rw [Offset.lt_iff a base (by omega)] at inside
  simp only [ofs] at ha
  omega

theorem native_array_num (mem : Mem) {base : BitVec 32} {w o : Nat}
    (fit : base.toNat + arrAt w o < 2 ^ 32) :
    val32 mem (State.addr (base + BitVec.ofNat 32 (arrAt w o))) 0 (2 * w) =
      numAt mem (State.addr base) w o := by
  rw [← read_eq_val32, addr_add fit]
  simp only [off, BitVec.add_zero, numAt]
  rw [show 4 * (2 * w) = 8 * w by omega]

end VG.Proof.Bignum.Arm
