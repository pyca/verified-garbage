module

public import VerifiedGarbage.Impl.Bignum.Arm.SanitizeModulus
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Load the secret CRT validation bit -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem sanitizeBit_ok (s : State) {base : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fit : 216 ≤ size) (ptr : s.gpr .r0 = base) :
    WP isa (.block sanitizeBit) s fun t =>
      t.gpr .r11 = s.mem.readW (off (State.addr base) 212) 32 ∧
      t.mem = s.mem ∧ Rest [.r11] s t := by
  unfold sanitizeBit
  refine wp_ldr (by decide) (a := off (State.addr base) 212)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read (by omega)) fun t h =>
    WP.block_nil ⟨h.gpr, h.mem, h.rest (by simp)⟩

end VG.Proof.Bignum.Arm
