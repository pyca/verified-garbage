module

public import VerifiedGarbage.Impl.Bignum.Arm.SetSmall
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The initialized array is exactly the chosen native-word integer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem setSmall_ok (s : State) {base : BitVec 32} {size o n : Nat}
    (ctx : ZeroCtx s base size o n) (hn : 0 < n)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 o) (p4 : s.gpr .r4 = base + BitVec.ofNat 32 o)
    (count : s.gpr .lr = BitVec.ofNat 32 n) (zero : s.gpr .r3 = 0) :
    WP isa setSmall s fun t =>
      val32 t.mem (State.addr base) o n = (s.gpr .r5).toNat ∧
      w32 t.mem (State.addr base) o = (s.gpr .r5).toNat ∧
      Outside (State.addr base) o (4 * n) s.mem t.mem ∧ Rest [.r0, .lr] s t := by
  have nowrap := ctx.nowrap
  have fits := ctx.fits
  rw [setSmall, WP.seq_iff]
  refine WP.mono (zero_ok s ctx hn p0 count zero) ?_
  intro u inv
  have addr : State.addr (u.gpr .r4 + BitVec.ofNat 32 0) = off (State.addr base) o := by
    rw [inv.rest.gpr .r4 (by simp), p4, Offset.add_add, Nat.add_zero]
    exact addr_add (by omega)
  have wr : InRegions u.wr (off (State.addr base) o) 4 := by
    rw [inv.rest.wr]
    exact CallLay.inRegions_sub ctx.writable (by omega) (by omega)
  refine wp_str (a := off (State.addr base) o) (by decide) addr wr fun t h => WP.block_nil ?_
  have mem : t.mem = u.mem.writeW (off (State.addr base) o) (s.gpr .r5) := by
    rw [h.mem, inv.rest.gpr .r5 (by simp)]
  have outside := writeW32_outside u.mem (State.addr base) (d := o) (s.gpr .r5) (by omega)
  rw [← mem] at outside
  have low : w32 t.mem (State.addr base) o = (s.gpr .r5).toNat := by
    rw [mem, w32_write_self]
  have tail : val32 u.mem (State.addr base) (o + 4) (n - 1) = 0 := by
    have z := inv.value
    rw [show n = (n - 1) + 1 by omega, val32] at z
    omega
  refine ⟨?_, low, inv.outside.trans (outside.mono (Nat.le_refl _) (by omega)), inv.rest.trans (h.rest _)⟩
  rw [show n = (n - 1) + 1 by omega, val32, low,
    outside.val32 (d := o + 4) (k := n - 1) (by omega) (by omega), tail, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Bignum.Arm
