module
public import VerifiedGarbage.Impl.Bignum.Arm.WideProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The scalar source address comes from a public product control -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem wideProductHead_ok (s : State) {base ap : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fit : 148 ≤ size) (ptr : s.gpr .r0 = base)
    (aPtr : s.mem.readW (off (State.addr base) 128) 32 = ap) :
    WP isa (.block wideProductArgsHead) s fun t => t.gpr .r0 = base ∧ t.gpr .r1 = ap := by
  have addr (d : Nat) (hd : d + 4 ≤ size) : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = off (State.addr base) d := by
    rw [ptr]; exact addr_add (by have := ws.nowrap; omega)
  unfold wideProductArgsHead
  refine wp_ldr (a := off (State.addr base) 132) (by decide) (addr 132 (by omega))
    (ws.read (by omega)) fun u h => ?_
  refine wp_ldr (a := off (State.addr base) 144) (by decide)
    (by rw [h.other .r0 (by decide)]; exact addr 144 (by omega))
    (by rw [h.rd, h.wr]; exact ws.read (by omega)) fun v j => ?_
  refine wp_ldr (a := off (State.addr base) 128) (by decide)
    (by rw [j.other .r0 (by decide), h.other .r0 (by decide)]; exact addr 128 (by omega))
    (by rw [j.rd, j.wr, h.rd, h.wr]; exact ws.read (by omega)) fun t l => WP.block_nil ?_
  exact ⟨by rw [l.other .r0 (by decide), j.other .r0 (by decide), h.other .r0 (by decide)]; exact ptr,
    by rw [l.gpr, j.mem, h.mem]; exact aPtr⟩

end VG.Proof.Bignum.Arm
