module

public import VerifiedGarbage.Proof.Rsa.Arm.DivShiftArray
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Shift the quotient's high bit into the extended remainder -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem shift_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa shift s fun t =>
      g.value t.mem 0 = 2 * g.value s.mem 0 % 2 ^ (32 * g.n) ∧
      (g.value s.mem 1 < 2 ^ (32 * g.n) →
        g.value t.mem 1 = 2 * g.value s.mem 1 + g.value s.mem 0 / 2 ^ (32 * g.n - 1)) ∧
      Context g t ∧ Outs (State.addr g.base) g.ranges s.mem t.mem ∧ Rest clobbers s t := by
  rw [shift, WP.seq_iff]
  refine WP.mono (quotientArgs_ok h) ?_
  rintro u ⟨p0, count, carry, memU, ctxU, restU⟩
  rw [WP.seq_iff]
  refine WP.mono (shiftArray_ok ctxU 0 (Or.inl rfl) p0 count (by rw [carry]; decide)) ?_
  rintro v ⟨qVal, qCarry, bit, ctxV, frameV, restV⟩
  simp only [Geometry.words, ↓reduceIte, carry, show (0 : BitVec 32).toNat = 0 from rfl,
    Nat.add_zero, memU] at qVal qCarry frameV
  have width : 1 ≤ 32 * g.n := by have := h.positive; omega
  have radix : 2 ^ (32 * g.n) = 2 * 2 ^ (32 * g.n - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have bitEq : (v.gpr .r11).toNat = g.value s.mem 0 / 2 ^ (32 * g.n - 1) := by
    rw [qCarry, radix, Nat.mul_div_mul_left _ _ (by decide)]
  have f0 : g.offsets 0 + 4 * g.n ≤ g.size := h.fits 0
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := h.fits 1
  have nowrap := h.workspace.nowrap
  have sep01 := h.separate 0 1 (by decide)
  change g.offsets 0 + 4 * g.n ≤ g.offsets 1 ∨
    g.offsets 1 + 4 * (g.n + 1) ≤ g.offsets 0 at sep01
  have rOld : g.value v.mem 1 = g.value s.mem 1 := by
    change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
    exact frameV.val32 (by omega) (by omega)
  rw [WP.seq_iff]
  refine WP.mono (remainderArgs_ok ctxV) ?_
  rintro z ⟨pz, cz, memZ, ctxZ, restZ⟩
  have bitZ : (z.gpr .r11).toNat ≤ 1 := by rw [restZ.gpr .r11 (by simp)]; exact bit
  refine WP.mono (shiftArray_ok ctxZ 1 (Or.inr rfl) pz cz bitZ) ?_
  rintro t ⟨rVal, _, _, ctxT, frameT, restT⟩
  change g.value t.mem 1 = (2 * g.value z.mem 1 + (z.gpr .r11).toNat) % 2 ^ (32 * (g.n + 1)) at rVal
  change Outside _ (g.offsets 1) (4 * (g.n + 1)) z.mem t.mem at frameT
  rw [memZ] at rVal frameT
  have qOld : g.value t.mem 0 = g.value v.mem 0 := by
    rw [← memZ]
    change val32 _ _ _ g.n = val32 _ _ _ g.n
    rw [memZ]
    exact frameT.val32 (by omega) (by omega)
  refine ⟨qOld.trans qVal, ?_, ctxT, ?_, ?_⟩
  · intro bound
    rw [rVal, restZ.gpr .r11 (by simp), bitEq, rOld]
    apply Nat.mod_eq_of_lt
    have topBound : g.value s.mem 0 / 2 ^ (32 * g.n - 1) ≤ 1 := by rw [← bitEq]; exact bit
    rw [show 32 * (g.n + 1) = 32 * g.n + 32 by omega, Nat.pow_add]
    omega
  · have fV : Outs (State.addr g.base) g.ranges s.mem v.mem :=
      Outs.of_outside frameV (by simp [Geometry.ranges])
    have fT : Outs (State.addr g.base) g.ranges v.mem t.mem :=
      Outs.of_outside frameT (by simp [Geometry.ranges])
    exact fV.trans fT
  · exact (restU.mono (by simp [clobbers])).trans
      ((restV.mono (by simp [clobbers])).trans
        ((restZ.mono (by simp [clobbers])).trans (restT.mono (by simp [clobbers]))))

end VG.Proof.Rsa.Arm.Div
