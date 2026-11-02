module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Ffdh.Arm.LowBit
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Impl.Ffdh.Arm.Checks
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The p-1 comparison changes only array 7's low word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps)
open VG.Proof.X25519.Arm (Rest)

theorem setLowBit_store (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.setLowBit) s fun t =>
      t.mem = s.mem.writeW (off (State.addr base) (arrAt w 7))
        (s.mem.readW (off (State.addr base) (arrAt w 7)) 32 ||| 1) ∧ Rest [.r3, .r4] s t := by
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := array_end_le (w := w) (by decide : 7 < 8)
  have size : 128 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have header := nativeHeader_of_layout s.mem base h.workspace.nowrap (Nat.le_refl _) h.layout
  rw [h.width] at header
  have pointer := header.array 7 (by decide)
  have a120 : State.addr (base + BitVec.ofNat 32 120) = off (State.addr base) 120 :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega)
  have arrAddr : State.addr (base + BitVec.ofNat 32 (arrAt w 7)) = off (State.addr base) (arrAt w 7) :=
    VG.Arm.addr_add (by have := h.workspace.nowrap; omega)
  have rh := h.workspace.read (off := 120) (by omega)
  have ra := h.workspace.read (off := arrAt w 7) (by omega)
  have wa := h.workspace.write (off := arrAt w 7) (by omega)
  refine withRest_all [.r3, .r4] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.setLowBit
  ffrun [h.ptr, a120, arrAddr, rh, ra, wa, pointer, off, BitVec.add_zero]

theorem setLowBit_ok (s : State) {base : BitVec 32} {len w : Nat}
    (h : ArithmeticReady base len w s) :
    WP isa (.block VG.Impl.Ffdh.Arm.setLowBit) s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 7 = numAt s.mem (State.addr base) w 7 +
        (1 - numAt s.mem (State.addr base) w 7 % 2) ∧
      Keeps (State.addr base) len w 7 s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have bound := array_end_le (w := w) (by decide : 7 < 8)
  have nowrap := h.workspace.nowrap
  refine WP.mono (setLowBit_store s h) ?_
  rintro t ⟨mem, restT⟩
  have outside := writeW32_outside s.mem (State.addr base)
    (s.mem.readW (off (State.addr base) (arrAt w 7)) 32 ||| 1) (d := arrAt w 7) (by omega)
  rw [← mem] at outside
  have wide := outside.mono (o' := arrAt w 7) (n' := 8 * w) (by omega) (by omega)
  have keeps := outside_array_keeps wide (len := len) (by omega)
  have frame := outside_workspace wide (size := 8 * len) (by omega)
  have rest : Rest roundClobbers s t := restT.mono (by simp [roundClobbers])
  refine ⟨(h.after_array (by decide : 7 ≠ 0) keeps frame rest
    ((restT.gpr .r0 (by simp)).trans h.ptr)).1, ?_, keeps, frame, rest⟩
  rw [numAt_native, numAt_native, mem]
  exact val32_setLowBit _ _ _ _ (by omega) (by omega)

end VG.Proof.Ffdh.Arm
