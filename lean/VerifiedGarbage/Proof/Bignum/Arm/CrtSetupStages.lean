module
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupContext
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup

import VerifiedGarbage.Proof.Bignum.Arm.CrtLeavePrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupPrime
import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupMain
import VerifiedGarbage.Impl.Bignum.Arm.Zero

/-! # Per-execution invariants for the complete setup timing proof -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.Rsa.Mont (arrAt)

structure CrtSetupInput (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  context : CrtSetupContext base len w s
  ptr : s.gpr .r0 = base
  count : s.gpr .r7 = BitVec.ofNat 32 w
  zero : s.gpr .r3 = 0

structure CrtAtMain (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  context : CrtSetupContext base len w s
  main : CrtMainState base len w s.mem
  ptr : s.gpr .r0 = base

structure CrtAtPrime (base child : BitVec 32) (len w : Nat) (s : State) : Prop where
  context : CrtSetupContext base len w s
  main : CrtMainState base len w s.mem
  childWorkspace : Workspace s child (8 * len)
  ptr : s.gpr .r0 = child
  link : s.mem.readW (VG.Proof.Mont.off (State.addr child) 216) 32 = base

theorem crt_setupMain_ready (s : State) {base : BitVec 32} {len w : Nat} (h : CrtSetupInput base len w s) :
    WP isa setupMain s (CrtAtMain base len w) := by
  refine WP.mono (crt_setupMain_ok s h.context.main h.context.width h.context.widthFit h.context.arraysFit h.ptr h.count h.zero) ?_
  rintro t ⟨main, ptr, _, rest⟩
  exact ⟨h.context.congr rest.wr, main, ptr⟩

theorem crt_setupPrime_ready (s : State) {base child : BitVec 32} {len slot w : Nat}
    (h : CrtAtMain base len w s) (ws : Workspace s child (8 * len))
    (slotFit : slot + 4 ≤ 8 * len) (hs : slot < 4096)
    (sep : Region.Disjoint ⟨State.addr base, 8 * len⟩ ⟨State.addr child, 8 * len⟩)
    (link : s.mem.readW (VG.Proof.Mont.off (State.addr base) slot) 32 = child) :
    WP isa (setupPrime slot) s (CrtAtPrime base child len w) := by
  have size := h.context.size
  refine WP.mono (crt_setupPrime_ok s h.context.main ws (by omega) slotFit hs
    h.context.width h.context.widthFit h.context.arraysFit h.ptr
    (h.main.toCrtLayoutState.nativeCount h.context.main) link) ?_
  rintro t ⟨_, _, ptr, linkT, frame, rest⟩
  exact ⟨h.context.congr rest.wr, h.main.congr (h.context.main.eq_of_frame sep frame), ws.congr rest.wr, ptr, linkT⟩

theorem crt_leavePrime_ready (s : State) {base child : BitVec 32} {len w : Nat}
    (h : CrtAtPrime base child len w s) : WP isa (.block leavePrime) s (CrtAtMain base len w) := by
  have size := h.context.size
  refine WP.mono (crt_leavePrime_ok s h.childWorkspace (by omega) h.ptr h.link) ?_
  rintro t ⟨ptr, mem, rest⟩
  exact ⟨h.context.congr rest.wr, mem ▸ h.main, ptr⟩

end VG.Proof.Bignum.Arm
