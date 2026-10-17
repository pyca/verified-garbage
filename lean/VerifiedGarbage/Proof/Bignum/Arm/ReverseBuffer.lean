module

public import VerifiedGarbage.Proof.Bignum.Arm.StoreBE
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Serialize a nonempty native integer buffer as exact big-endian octets -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem reverseBuffer_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (hn : 0 < n) (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (countFits : n < 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr src) n)
    (write : InRegions s.wr (State.addr dst) n)
    (sep : Region.Disjoint ⟨State.addr src, n⟩ ⟨State.addr dst, n⟩)
    (p0 : s.gpr .r0 = dst) (p1 : s.gpr .r1 = src + BitVec.ofNat 32 (n - 1))
    (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa reverseBytes s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n = Spec.Rsa.i2osp (s.mem.read (State.addr src) n).toNat n ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧
      t.gpr .r0 = dst + BitVec.ofNat 32 n ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  refine WP.mono (reverseBytes_ok s (reverseCtx_of_regions s src dst countFits srcFit dstFit read write sep)
    hn p1 p0 count) ?_
  intro t inv
  exact ⟨inv.i2osp srcFit dstFit, inv.frame dstFit, inv.dest, inv.rest⟩

end VG.Proof.Bignum.Arm
