module

public import VerifiedGarbage.Proof.Rsa.Arm.DivReduce
public import VerifiedGarbage.Proof.Bignum.Arm.ShiftLeft
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Shifting either division register while preserving the public layout -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem shiftArray_ok {g : Geometry} {s : State} (h : Context g s) (i : Fin 4)
    (hi : i = 0 ∨ i = 1)
    (ptr : s.gpr .r0 = g.base + BitVec.ofNat 32 (g.offsets i))
    (count : s.gpr .lr = BitVec.ofNat 32 (g.words i))
    (carry : (s.gpr .r11).toNat ≤ 1) :
    WP isa shiftLeft s fun t =>
      g.value t.mem i = (2 * g.value s.mem i + (s.gpr .r11).toNat) % 2 ^ (32 * g.words i) ∧
      (t.gpr .r11).toNat = (2 * g.value s.mem i + (s.gpr .r11).toNat) / 2 ^ (32 * g.words i) ∧
      (t.gpr .r11).toNat ≤ 1 ∧ Context g t ∧
      Outside (State.addr g.base) (g.offsets i) (4 * g.words i) s.mem t.mem ∧
      Rest [.r0, .r3, .r4, .r11, .lr] s t := by
  have ctx : ShiftLeftCtx s g.base g.size (g.offsets i) (g.words i) :=
    ⟨h.workspace.nowrap, h.fits i, h.workspace.writable⟩
  have positive : 0 < g.words i := by
    have := h.positive; simp only [Geometry.words]; split <;> omega
  refine WP.mono (shiftLeft_ok s ctx positive ptr count carry) ?_
  intro t inv
  have frame : Outs (State.addr g.base) g.ranges s.mem t.mem :=
    Outs.of_outside inv.outside (by rcases hi with rfl | rfl <;> simp [Geometry.ranges, Geometry.words])
  exact ⟨inv.result.1, inv.result.2, inv.carry,
    h.after frame inv.rest.wr (inv.rest.gpr .r8 (by simp)), inv.outside, inv.rest⟩

end VG.Proof.Rsa.Arm.Div
