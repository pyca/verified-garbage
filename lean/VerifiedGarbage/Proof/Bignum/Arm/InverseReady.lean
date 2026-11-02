module

import VerifiedGarbage.Proof.Bignum.Arm.InitInverse
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Impl.Bignum.Arm.InitInverse
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Offset

/-! # Inverse initialization establishes the RSA arithmetic invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest)

theorem inverse_outside_layout {m m' : Mem} {base : Addr} {len : Nat}
    (outside : VG.Proof.Mont.Outside base 56 8 m m') (layout : Layout m base len) :
    wOf m' base = wOf m base ∧ Layout m' base len := by
  have width : wOf m' base = wOf m base :=
    congrArg BitVec.toNat (outside.word (d := 48) (by decide) (by decide))
  refine ⟨width, ?_⟩
  unfold Layout
  rw [width]
  refine ⟨layout.1, layout.2.1, layout.2.2.1, ?_⟩
  intro j hj
  change VG.Proof.Mont.word m' base (8 * (8 + j)) = _
  rw [outside.word (by omega) (by omega)]
  exact layout.2.2.2 j hj

theorem initInverse_ready_r2 (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 0)) (baseReg : s.gpr .r12 = base)
    (odd : (VG.Proof.Mont.word s.mem (State.addr base) (arrAt w 0)).toNat % 2 = 1)
    (large : 1 < numAt s.mem (State.addr base) w 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa initInverse s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t ∧
      numAt t.mem (State.addr base) w 4 = numAt s.mem (State.addr base) w 4 := by
  have hw : 2 ≤ w := width ▸ layout.1
  have fits : arrAt w 8 ≤ 8 * len := width ▸ layout.2.2.1
  have bound := Nat.le_trans (array_end_le (w := w) (j := 0) (k := 8) (by decide)) fits
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  refine WP.mono (initInverse_ok s ws (by omega) (by omega) ptr baseReg odd) ?_
  rintro t ⟨inv, inverse, mem, result, rest⟩
  have outside : VG.Proof.Mont.Outside (State.addr base) 56 8 s.mem t.mem := by
    rw [mem]
    exact VG.Proof.Mont.writeW_outside s.mem (State.addr base) inv (by decide)
  have number : numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
    rw [numAt_native, numAt_native]
    exact outside.val32 (by right; simp [arrAt, Proof.Rsa.Mont.hdrBytes]) (by have := ws.nowrap; omega)
  have kl := inverse_outside_layout outside layout
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by decide))
  refine ⟨⟨ws.congr rest.wr, kl.2, kl.1.trans width, result, ?_, ?_, ?_, ?_, ?_⟩,
    number, frame, rest.mono (by decide), ?_⟩
  · rw [outside.word (d := arrAt w 0) (by right; simp [arrAt, Proof.Rsa.Mont.hdrBytes]) (by have := ws.nowrap; omega)]
    change (_ * (t.mem.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [mem, Mem.readW_writeW_self64]
    exact inverse
  · rw [number]; exact large
  · rw [rest.rd, rest.wr, rest.sp]; exact stackRead
  · rw [rest.sp]; exact stackSep
  · exact saved_base_kept frame stackSep saved rest.sp

  · have bound4 := Nat.le_trans (array_end_le (w := w) (j := 4) (k := 8) (by decide)) fits
    rw [numAt_native, numAt_native]
    exact outside.val32 (by right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega)
      (by have := ws.nowrap; omega)


theorem initInverse_ready (s : State) {base : BitVec 32} {len w : Nat}
    (ws : Workspace s base (8 * len)) (layout : Layout s.mem (State.addr base) len)
    (width : wOf s.mem (State.addr base) = w)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 (arrAt w 0)) (baseReg : s.gpr .r12 = base)
    (odd : (VG.Proof.Mont.word s.mem (State.addr base) (arrAt w 0)).toNat % 2 = 1)
    (large : 1 < numAt s.mem (State.addr base) w 0)
    (stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, 8 * len⟩)
    (saved : s.mem.readW (State.addr s.sp) 32 = base) :
    WP isa initInverse s fun t => ArithmeticReady base len w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  exact WP.mono (initInverse_ready_r2 s ws layout width ptr baseReg odd large stackRead stackSep saved)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)

end VG.Proof.Bignum.Arm
