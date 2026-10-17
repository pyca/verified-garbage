module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtProduct
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Copy a public buffer pointer between header slots -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

theorem crt_copyHeaderPointer_ok (s : State) {base value : BitVec 32} {size src dst : Nat}
    (ws : Workspace s base size) (srcFit : src + 4 ≤ size) (dstFit : dst + 4 ≤ size)
    (hs : src < 4096) (hd : dst < 4096) (ptr : s.gpr .r0 = base)
    (source : s.mem.readW (off (State.addr base) src) 32 = value) :
    WP isa (.block (copyHeaderPointer src dst)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) dst) value ∧ Rest [.r1] s t := by
  unfold copyHeaderPointer
  refine wp_ldr (a := off (State.addr base) src) hs
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read srcFit) fun u a => ?_
  refine wp_str (a := off (State.addr base) dst) hd
    (by rw [a.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [a.wr]; exact ws.write dstFit) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.mem, a.mem, a.gpr, source], (a.rest (by simp)).trans (b.rest _)⟩

end VG.Proof.Bignum.Arm
