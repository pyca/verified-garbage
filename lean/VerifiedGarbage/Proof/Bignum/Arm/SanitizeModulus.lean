module
public import VerifiedGarbage.Impl.Bignum.Arm.SanitizeModulus
public import Batteries.Logic
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Rsa.MontContract

import VerifiedGarbage.Proof.Bignum.Arm.SanitizeBit
import VerifiedGarbage.Proof.Bignum.Arm.SmallConstLayout
import VerifiedGarbage.Proof.Bignum.Arm.SelectArray
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.SetSmallFn
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Block

/-! # A rejected factor is replaced by three before Montgomery arithmetic -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt wOf Layout Operand)
open VG.Proof.X25519.Arm (Rest)

theorem sanitizeModulus_ok (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w) (ptr : s.gpr .r0 = base)
    (bit : (s.mem.readW (off (State.addr base) 212) 32).toNat ≤ 1)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa sanitizeModulus s fun t =>
      Layout t.mem (State.addr base) len ∧ wOf t.mem (State.addr base) = w ∧
      numAt t.mem (State.addr base) w 0 =
        (if (s.mem.readW (off (State.addr base) 212) 32).toNat = 0 then 3
          else numAt s.mem (State.addr base) w 0) ∧
      Outs (State.addr base) [(arrAt w 7, 8 * w), (arrAt w 0, 8 * w)] s.mem t.mem ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧ t.gpr .r0 = base := by
  have fits : arrAt w 8 ≤ 8 * len := width ▸ layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  rw [sanitizeModulus, WP.seq_iff]
  refine WP.mono (smallConstLayout_ok s 3 ws layout width ptr (by decide : 7 < 8)
    (by decide) (by decide) stackRead stackSep saved) ?_
  rintro u ⟨layoutU, widthU, number, outsideU, frameU, restU, ptrU⟩
  have oldBit := outside_read32 outsideU (d := 212)
    (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) (by decide)
  have keeps := outside_array_keeps outsideU (len := len) (by have := ws.nowrap; omega)
  have oldM := keeps_array_num keeps fits
    (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide : 0 ≠ 7)
  rw [WP.seq_iff]
  refine WP.mono (sanitizeBit_ok u (ws.congr restU.wr) (by omega) ptrU) ?_
  rintro v ⟨loaded, memV, restV⟩
  rw [oldBit] at loaded
  have restUV : Rest roundClobbers s v := restU.trans (restV.mono (by decide))
  have savedV : v.mem.readW (State.addr v.sp) 32 = base := by
    rw [memV, restV.sp]
    exact saved_base_kept frameU stackSep saved restU.sp
  refine WP.mono (selectArray_ok (w := w) v (ws.congr restUV.wr) (by rw [memV]; exact layoutU)
    (by rw [memV]; exact widthU) ((restV.gpr .r0 (by decide)).trans ptrU)
    (by decide : 0 < 8) (by decide : 7 < 8) (by decide : 0 < 8) (by rw [loaded]; exact bit)
    (by rw [restUV.rd, restUV.wr, restUV.sp]; exact stackRead) (by rw [restUV.sp]; exact stackSep)
    savedV) ?_
  rintro t ⟨layoutT, widthT, value, outsideT, frameT, restT, ptrT⟩
  rw [loaded, memV, number, oldM] at value
  rw [memV] at outsideT frameT
  exact ⟨layoutT, widthT, value,
    (Outs.of_outside outsideU (by simp)).trans (Outs.of_outside outsideT (by simp)), frameU.trans frameT, restUV.trans restT, ptrT⟩

end VG.Proof.Bignum.Arm
