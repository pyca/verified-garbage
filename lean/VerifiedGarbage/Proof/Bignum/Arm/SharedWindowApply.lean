module
import VerifiedGarbage.Proof.Bignum.Arm.SharedWindowArithmetic
import VerifiedGarbage.Proof.Bignum.Arm.WindowBit
import VerifiedGarbage.Proof.Bignum.Arm.WindowScan
import VerifiedGarbage.Proof.Bignum.Arm.WindowState
import VerifiedGarbage.Proof.Bignum.Arm.WindowCtl
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Bignum.Arm.SharedWindow
public import VerifiedGarbage.Proof.Bignum.Arm.ExpState
public import VerifiedGarbage.Proof.Bignum.Arm.TwoExpMontgomery
public import VerifiedGarbage.Proof.Bignum.Arm.WindowBuild

/-! The window table is selected once, then multiplied through a shared call. -/
@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Keeps Operand)
open VG.Proof.X25519.Arm (Rest)
theorem sharedWindowApply_ok {base : BitVec 32} {len w : Nat} {P : State → Prop} {regions : List Region}
    (K : TwoExp.Montgomery base len w P regions) (s : State) {M x A d : Nat}
    (h : ExpState base len w M x A s) (hp : P s) (table : TableHolds s.mem base w M x 8) (fits : arrAt w 16 ≤ 8 * len)
    (hd : d < 8) (digit : s.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 d) :
    WP isa (SharedWindow.apply K.op) s fun t => ExpState base len w M x (A + d) t ∧ TableHolds t.mem base w M x 8 ∧
      t.mem.readW (off (State.addr base) 196) 32 = BitVec.ofNat 32 0 ∧
      t.mem.readW (off (State.addr base) 204) 32 = BitVec.ofNat 32 0 ∧
      KeepsExp base s.mem t.mem ∧ P t ∧ Frame regions s.mem t.mem ∧ Rest roundClobbers s t := by
  have nowrap := h.ready.workspace.nowrap
  have size : 256 ≤ 8 * len := Nat.le_trans (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) fits
  rw [SharedWindow.apply, WP.seq_iff]
  refine WP.mono (scan_ok s h table fits hd digit) ?_
  rintro u ⟨powerU, tableU, selected, _, keepsU, frameU, restU⟩
  have entry := tableU d hd
  rw [← selected] at entry
  have pU := K.stable frameU restU hp
  rw [WP.seq_iff]
  refine WP.mono (K.op_ok u 6 6 1 powerU.ready pU
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp])
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]) (by decide)
    (by rw [powerU.modulus]; exact entry.1)) ?_
  rintro v ⟨ready, modulus, bound, value, keeps, pV, frameV, restV⟩
  rw [powerU.modulus] at modulus bound value
  have powerV := powerU.after_y ready modulus keeps bound
    (mont_mulpow powerU.coprime powerU.powerValue entry.2 value)
  have tableV := tableU.of_keeps keeps fits (by decide) (by decide)
  refine WP.mono (windowReset_ok v ready) ?_
  rintro t ⟨memT, restT⟩
  have ctl : CtlOnly base v.mem t.mem := by
    rw [memT]; exact ctl_write2 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨powerT, frameT⟩ := powerV.after_ctl ctl restT ((restT.gpr .r0 (by simp)).trans ready.ptr)
  have outside := writeW32_outside (v.mem.writeW (off (State.addr base) 196) (BitVec.ofNat 32 0))
    (State.addr base) (d := 204) (BitVec.ofNat 32 0) (by decide)
  refine ⟨powerT, tableV.after_ctl ctl fits nowrap (by decide), ?_, by rw [memT]; exact Mem.readW_writeW_self32 _ _ _,
    keepsU.trans ((KeepsExp.of_keeps keeps size).trans ?_), K.stable frameT (rest_round restT) pV,
    (Frame.mono frameU (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace)).trans
      (frameV.trans (Frame.mono frameT (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact K.workspace))),
    restU.trans (restV.trans (rest_round restT))⟩
  · rw [memT, outside_read32 outside (d := 196) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [memT]
    exact KeepsExp.of_writes _ _ _ _ (Or.inr rfl) (by decide) (Or.inl (by decide)) (by decide)

end VG.Proof.Bignum.Arm
