module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtAddWide
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWideArgs
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.X25519.Arm.Instr
/-! # Load the public pointers and width for final CRT addition -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CrtAddWideScalars.lean`, which only this module imported.
section

/-! # Set an extended addition's scalar and carry to one and zero -/

section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest wp_dp wp_mov op2_imm dpVal)

theorem crt_addWideScalars_ok (s : State) {w : Nat} (count : s.gpr .lr = BitVec.ofNat 32 (4 * w + 2)) :
    WP isa (.block addWideScalars) s fun t => t.gpr .lr = BitVec.ofNat 32 (4 * w) ∧
      t.gpr .r1 = 1 ∧ t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest [.r1, .r11, .lr] s t := by
  unfold addWideScalars
  refine wp_dp (op2_imm (by decide)) fun u a => ?_
  refine wp_mov (op2_imm (by decide)) fun v b => ?_
  refine wp_mov (op2_imm (by decide)) fun t c => WP.block_nil ?_
  refine ⟨?_, (c.other .r1 (by decide)).trans b.gpr, c.gpr, c.mem.trans (b.mem.trans a.mem),
    (a.rest (by simp)).trans ((b.rest (by simp)).trans (c.rest (by simp)))⟩
  rw [c.other .lr (by decide), b.other .lr (by decide), a.gpr, dpVal, count, BitVec.ofNat_add]
  change (BitVec.ofNat 32 (4 * w) + 2#32) - 2#32 = _
  exact BitVec.add_sub_cancel _ _

end VG.Proof.Bignum.Arm
end

end

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
  exact ⟨(restT.gpr .r0 (by decide)).trans out,
    (restT.gpr .r12 (by decide)).trans ((restV.gpr .r12 (by decide)).trans (a.gpr.trans input)),
    countT, one, zero, memT.trans (memV.trans a.mem),
    (a.rest (by decide)).trans ((restV.mono (by decide)).trans (restT.mono (by decide)))⟩

end VG.Proof.Bignum.Arm
