module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Copy a factor's modulus pointer into the multiplication header -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem crt_copyChildPointer_ok (s : State) {base value : BitVec 32} {size src dst child slot : Nat}
    (ws : Workspace s base size) (srcFit : src + 4 ≤ size) (dstFit : dst + 4 ≤ size)
    (hs : src < 4096) (hd : dst < 4096) (hslot : slot < 4096) (childFit : child + slot + 4 ≤ size) (ptr : s.gpr .r0 = base)
    (childPtr : s.mem.readW (off (State.addr base) src) 32 = base + BitVec.ofNat 32 child)
    (arrayPtr : s.mem.readW (off (State.addr base) (child + slot)) 32 = value) :
    WP isa (.block (copyChildPointer src dst slot)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) dst) value ∧ Rest [.r1] s t := by
  unfold copyChildPointer
  refine wp_ldr (a := off (State.addr base) src) hs
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read srcFit) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) (child + slot)) hslot
    (by rw [a.gpr, childPtr, Offset.add_add]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [a.rd, a.wr]; exact ws.read childFit) fun v b => ?_
  refine wp_str (a := off (State.addr base) dst) hd
    (by rw [b.other .r0 (by decide), a.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [b.wr, a.wr]; exact ws.write dstFit) fun t c => WP.block_nil ?_
  refine ⟨?_, (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest _))⟩
  rw [c.mem, b.mem, a.mem, b.gpr, a.mem, arrayPtr]

end VG.Proof.Bignum.Arm
