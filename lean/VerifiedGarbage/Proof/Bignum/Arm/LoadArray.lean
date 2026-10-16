module

public import VerifiedGarbage.Impl.Bignum.Arm.MontFn
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Load an array pointer using a public RSA array index -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_dp wp_ldr op2_lsl dpVal)

theorem loadArray_ok (s : State) (d i : Reg) {base : BitVec 32} {size j a : Nat}
    (ws : Workspace s base size) (fit : 64 + 8 * j + 4 ≤ size)
    (ptr : s.gpr .r0 = base) (index : s.gpr i = BitVec.ofNat 32 j)
    (header : s.mem.readW (off (State.addr base) (64 + 8 * j)) 32 = base + BitVec.ofNat 32 a) :
    WP isa (.block (MontFn.loadArray d i)) s fun t =>
      t.gpr d = base + BitVec.ofNat 32 a ∧ t.mem = s.mem ∧ Rest [i, d] s t := by
  have nowrap := ws.nowrap
  have shift : BitVec.ofNat 32 j <<< 3 = BitVec.ofNat 32 (8 * j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 32)]
    congr 1
    omega
  unfold MontFn.loadArray
  refine wp_dp (op2_lsl (by decide)) fun u hu => ?_
  have pu : u.gpr i = base + BitVec.ofNat 32 (8 * j) := by
    rw [hu.gpr, dpVal, ptr, index, shift]
  have wu := ws.congr hu.wr
  refine wp_ldr (by decide) (wu.ea pu (by omega)) (wu.read (by omega)) fun t ht => WP.block_nil ?_
  refine ⟨?_, ht.mem.trans hu.mem, (hu.rest (by simp)).trans (ht.rest (by simp))⟩
  rw [ht.gpr, hu.mem, show 8 * j + 64 = 64 + 8 * j by omega, header]

end VG.Proof.Bignum.Arm
