module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Read a factor workspace pointer and its public arithmetic width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem crt_primeArgs_ok (s : State) {base child : BitVec 32} {size slot w : Nat}
    (ws : Workspace s base size) (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096)
    (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (link : s.mem.readW (off (State.addr base) slot) 32 = child) :
    WP isa (.block (primeArgs slot)) s fun t =>
      t.gpr .r7 = BitVec.ofNat 32 w ∧ t.gpr .r2 = child ∧ t.mem = s.mem ∧ Rest [.r7, .r2] s t := by
  unfold primeArgs
  refine wp_ldr (a := off (State.addr base) 48) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun u a => ?_
  refine wp_ldr (a := off (State.addr base) slot) hs
    (by rw [a.other .r0 (by decide), ptr]; exact addr_add (by have := ws.nowrap; omega))
    (by rw [a.rd, a.wr]; exact ws.read slotFit) fun t b => WP.block_nil ?_
  exact ⟨(b.other .r7 (by decide)).trans (a.gpr.trans count),
    by rw [b.gpr, a.mem]; exact link, b.mem.trans a.mem, (a.rest (by simp)).trans (b.rest (by simp))⟩

end VG.Proof.Bignum.Arm
