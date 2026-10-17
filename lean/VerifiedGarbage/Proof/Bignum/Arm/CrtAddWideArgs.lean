module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtAddWideScalars
public import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideArgs
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Load the public pointers and width for final CRT addition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr)

theorem crt_addWideArgs_ok (s : State) {base dst src : BitVec 32} {size w : Nat}
    (ws : Workspace s base size) (fit : 244 ≤ size) (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (output : s.mem.readW (off (State.addr base) 232) 32 = dst)
    (input : s.mem.readW (off (State.addr base) 240) 32 = src) :
    WP isa addWideArgs s fun t => t.gpr .r0 = dst ∧ t.gpr .r12 = src ∧
      t.gpr .lr = BitVec.ofNat 32 (4 * w) ∧ t.gpr .r1 = 1 ∧ t.gpr .r11 = 0 ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r3, .r11, .r12, .lr] s t := by
  rw [addWideArgs, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) 240) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega)) (ws.read fit) fun u a => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (crt_clearWideArgs_ok u (dst := dst) (w := w) (ws.congr a.wr) (by omega) (by omega) (by decide)
    ((a.other .r0 (by decide)).trans ptr) (by rw [a.mem]; exact count) (by rw [a.mem]; exact output)) ?_
  rintro v ⟨out, width, _, memV, restV⟩
  refine WP.mono (crt_addWideScalars_ok v width) ?_
  rintro t ⟨countT, one, zero, memT, restT⟩
  exact ⟨(restT.gpr .r0 (by simp)).trans out,
    (restT.gpr .r12 (by simp)).trans ((restV.gpr .r12 (by simp)).trans (a.gpr.trans input)),
    countT, one, zero, memT.trans (memV.trans a.mem),
    (a.rest (by simp)).trans ((restV.mono (by simp)).trans (restT.mono (by simp)))⟩

end VG.Proof.Bignum.Arm
