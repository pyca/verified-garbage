module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeArgs
import VerifiedGarbage.Proof.Bignum.Arm.CrtPrimeEnter
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Entering a CRT factor changes only its parent-link word -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem crt_enterPrime_ok (s : State) {base child : BitVec 32} {size childSize slot w : Nat}
    (ws : Workspace s base size) (childWs : Workspace s child childSize)
    (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096) (childFit : 220 ≤ childSize)
    (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (link : s.mem.readW (off (State.addr base) slot) 32 = child) :
    WP isa (enterPrime slot) s fun t =>
      t.gpr .r0 = child ∧ t.gpr .r7 = BitVec.ofNat 32 w ∧ t.gpr .r3 = 0 ∧
      t.mem.readW (off (State.addr child) 216) 32 = base ∧
      Outside (State.addr child) 216 4 s.mem t.mem ∧
      Frame [⟨State.addr child, childSize⟩] s.mem t.mem ∧ Rest [.r0, .r2, .r3, .r7] s t := by
  rw [enterPrime, WP.seq_iff]
  refine WP.mono (crt_primeArgs_ok s ws fit slotFit hs ptr count link) ?_
  rintro u ⟨width, childPtr, memU, restU⟩
  refine WP.mono (crt_primeEnter_ok u (childWs.congr restU.wr) childFit childPtr) ?_
  rintro t ⟨ptrT, zero, memT, restT⟩
  rw [memU, restU.gpr .r0 (by simp), ptr] at memT
  have outside := writeW32_outside s.mem (State.addr child) (d := 216) base (by decide)
  rw [← memT] at outside
  exact ⟨ptrT, (restT.gpr .r7 (by simp)).trans width, zero,
    by rw [memT, Mem.readW_writeW_self32], outside, outside_workspace outside childFit,
    (restU.mono (by simp)).trans (restT.mono (by simp))⟩

end VG.Proof.Bignum.Arm
