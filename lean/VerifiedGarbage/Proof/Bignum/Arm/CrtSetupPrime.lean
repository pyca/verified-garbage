module
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.CrtEnterPrime
import VerifiedGarbage.Proof.Bignum.Arm.SetupFrame
import VerifiedGarbage.Proof.Bignum.Arm.Setup
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Initialize one factor workspace while retaining its parent link -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.Rsa.Mont (Layout wOf arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_setupPrime_ok (s : State) {base child : BitVec 32} {size len slot w : Nat}
    (ws : Workspace s base size) (childWs : Workspace s child (8 * len))
    (fit : 52 ≤ size) (slotFit : slot + 4 ≤ size) (hs : slot < 4096)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (arraysFit : arrAt w 8 ≤ 8 * len)
    (ptr : s.gpr .r0 = base)
    (count : s.mem.readW (off (State.addr base) 48) 32 = BitVec.ofNat 32 w)
    (link : s.mem.readW (off (State.addr base) slot) 32 = child) :
    WP isa (.seq (enterPrime slot) setup) s fun t =>
      Layout t.mem (State.addr child) len ∧ wOf t.mem (State.addr child) = w ∧ t.gpr .r0 = child ∧
      t.mem.readW (off (State.addr child) 216) 32 = base ∧
      Frame [⟨State.addr child, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have childFit : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at arraysFit; omega
  rw [WP.seq_iff]
  refine WP.mono (crt_enterPrime_ok s ws childWs fit slotFit hs (by omega) ptr count link) ?_
  rintro u ⟨ptrU, widthU, zeroU, linkU, _, frameU, restU⟩
  refine WP.mono (setup_ok u (childWs.congr restU.wr) hw hw' arraysFit ptrU widthU zeroU) ?_
  rintro t ⟨layoutT, widthT, ptrT, outsideT, restT⟩
  have word := outs_word32 outsideT (d := 216) (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> omega)
    (by decide)
  have linkT : t.mem.readW (off (State.addr child) 216) 32 = base := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem (State.addr child) 216 = base.toNat
    rw [word]
    exact congrArg BitVec.toNat linkU
  have frameT := outs_workspace outsideT (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl <;> omega :
    ∀ r ∈ [(48, 8), (64, 64)], r.1 + r.2 ≤ 8 * len)
  exact ⟨layoutT, widthT, ptrT, linkT, frameU.trans frameT,
    (restU.mono (by decide)).trans (restT.mono (by decide))⟩

end VG.Proof.Bignum.Arm
