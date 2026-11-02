module
public import VerifiedGarbage.Impl.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Stable workspace assumptions for RSA precomputation and exponentiation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout Operand Keeps)
open VG.Proof.X25519.Arm (Rest)

structure ArithmeticReady (base : BitVec 32) (len w : Nat) (s : State) : Prop where
  workspace : Workspace s base (8 * len)
  layout : Layout s.mem (State.addr base) len
  width : wOf s.mem (State.addr base) = w
  ptr : s.gpr .r0 = base
  inverse : ((word s.mem (State.addr base) (arrAt w 0)).toNat *
    (wordAt s.mem (State.addr base) Proof.Rsa.Mont.minvWord).toNat + 1) % 2 ^ 64 = 0
  modulus : 1 < numAt s.mem (State.addr base) w 0
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem ArithmeticReady.after_array {s t : State} {base : BitVec 32} {len w o : Nat}
    (h : ArithmeticReady base len w s) (ho : o ≠ 0)
    (keeps : Keeps (State.addr base) len w o s.mem t.mem)
    (frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem)
    (rest : Rest roundClobbers s t) (ptr : t.gpr .r0 = base) :
    ArithmeticReady base len w t ∧ numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  have hw : 2 ≤ w := h.width ▸ h.layout.1
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have op0 : Operand 0 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have kl := keeps_layout h.layout (by rw [h.width]; exact keeps)
  have oldM := keeps_array_num keeps fits op0 (Ne.symm ho)
  have oldLow := keeps_array_word (d := 0) (bits := 64) keeps fits op0 (Ne.symm ho) (by omega)
  simp only [Nat.add_zero] at oldLow
  refine ⟨⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_⟩, oldM⟩
  · change ((t.mem.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
      (t.mem.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [oldLow, keeps_header_readW keeps size (d := 56) (bits := 64) (by decide)]
    exact h.inverse
  · rw [oldM]; exact h.modulus
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

theorem ArithmeticReady.setSmall (s : State) {base : BitVec 32} {len w o : Nat}
    (h : ArithmeticReady base len w s) (ho : o < 8) (ho0 : o ≠ 0)
    (index : s.gpr .r2 = BitVec.ofNat 32 o) :
    WP isa VG.Impl.Bignum.Arm.setSmallFn s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w o = (s.gpr .r5).toNat ∧
      w32 t.mem (State.addr base) (arrAt w o) = (s.gpr .r5).toNat ∧
      Keeps (State.addr base) len w o s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have body := setSmallFn_ok s h.workspace h.layout ho h.ptr index h.stackRead h.stackSep h.saved
  simp only [h.width] at body
  refine WP.mono body ?_
  rintro t ⟨value, low, outside, frame, rest, ptr⟩
  have nowrap := h.workspace.nowrap
  have keeps := outside_array_keeps outside (len := len) (by omega)
  exact ⟨(h.after_array ho0 keeps frame rest ptr).1, value, low, keeps, frame, rest⟩

end VG.Proof.Bignum.Arm
