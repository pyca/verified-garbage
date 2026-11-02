module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.Offset

/-! # Updating an RSA control slot preserves all arithmetic arrays -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt wordAt wOf numAt Layout)
open VG.Proof.X25519.Arm (Rest)

theorem control_outside_layout {m m' : Mem} {base : Addr} {len d : Nat}
    (hd : 128 ≤ d) (outside : Outside base d 4 m m') (layout : Layout m base len) :
    wOf m' base = wOf m base ∧ Layout m' base len := by
  have width : wOf m' base = wOf m base :=
    congrArg BitVec.toNat (outside.word (d := 48) (by omega) (by decide))
  refine ⟨width, ?_⟩
  unfold Layout
  rw [width]
  refine ⟨layout.1, layout.2.1, layout.2.2.1, ?_⟩
  intro j hj
  change word m' base (8 * (8 + j)) = _
  rw [outside.word (by omega) (by omega)]
  exact layout.2.2.2 j hj

theorem ArithmeticReady.after_header {s t : State} {base : BitVec 32} {len w d : Nat} {value : BitVec 32}
    {rs : List Reg} (h : ArithmeticReady base len w s) (hd : 128 ≤ d) (hd' : d + 4 ≤ 256)
    (mem : t.mem = s.mem.writeW (off (State.addr base) d) value)
    (rest : Rest rs s t) (ptr : t.gpr .r0 = base) :
    ArithmeticReady base len w t ∧
      Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem ∧
      ∀ q < 8, numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q := by
  have nowrap := h.workspace.nowrap
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have outside := writeW32_outside s.mem (State.addr base) (d := d) value (by omega)
  rw [← mem] at outside
  have arrays (q : Nat) (hq : q < 8) :
      numAt t.mem (State.addr base) w q = numAt s.mem (State.addr base) w q := by
    have bound := Nat.le_trans (array_end_le hq) fits
    rw [numAt_native, numAt_native]
    apply outside.val32
    · right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega
    · omega
  have kl := control_outside_layout hd outside h.layout
  have frame : Frame [⟨State.addr base, 8 * len⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  refine ⟨⟨h.workspace.congr rest.wr, kl.2, kl.1.trans h.width, ptr, ?_, ?_, ?_, ?_, ?_⟩, frame, arrays⟩
  · have fit0 := Nat.le_trans (array_end_le (w := w) (j := 0) (k := 8) (by decide)) fits
    rw [outside.word (d := arrAt w 0) (by right; simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega) (by omega)]
    change (_ * (word t.mem (State.addr base) 56).toNat + 1) % 2 ^ 64 = 0
    rw [outside.word (d := 56) (by omega) (by decide)]
    exact h.inverse
  · rw [arrays 0 (by decide)]; exact h.modulus
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead
  · rw [rest.sp]; exact h.stackSep
  · exact saved_base_kept frame h.stackSep h.saved rest.sp

end VG.Proof.Bignum.Arm
