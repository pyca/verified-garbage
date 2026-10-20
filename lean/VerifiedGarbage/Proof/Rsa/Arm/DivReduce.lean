module
public import VerifiedGarbage.Impl.Rsa.Arm.Div
public import VerifiedGarbage.Proof.Rsa.Arm.DivContext

import VerifiedGarbage.Proof.Rsa.Arm.DivArgs
import VerifiedGarbage.Proof.Bignum.Arm.SubtractIfGe
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The division remainder's conditional subtraction -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Div
open VG VG.Arm VG.Impl.Rsa.Arm.Div VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

abbrev clobbers : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r7, .r9, .r10, .r11, .r12, .lr]

def Geometry.value (g : Geometry) (mem : Mem) (i : Fin 4) : Nat :=
  val32 mem (State.addr g.base) (g.offsets i) (g.words i)

theorem reduce_ok {g : Geometry} {s : State} (h : Context g s) :
    WP isa reduce s fun t =>
      g.value t.mem 1 = (if g.value s.mem 1 < g.value s.mem 2 then
        g.value s.mem 1 else g.value s.mem 1 - g.value s.mem 2) ∧
      (t.gpr .r11).toNat = (if g.value s.mem 1 < g.value s.mem 2 then 1 else 0) ∧
      Context g t ∧ Outs (State.addr g.base)
        [(g.offsets 3, 4 * (g.n + 1)), (g.offsets 1, 4 * (g.n + 1))] s.mem t.mem ∧
      Rest clobbers s t := by
  rw [reduce, WP.seq_iff]
  refine WP.mono (subtractArgs_ok h) ?_
  rintro u ⟨p0, p10, p12, p9, c7, count, carry, mem, ctx, rest⟩
  have f1 : g.offsets 1 + 4 * (g.n + 1) ≤ g.size := by simpa [Geometry.words] using h.fits 1
  have f2 : g.offsets 2 + 4 * (g.n + 1) ≤ g.size := by simpa [Geometry.words] using h.fits 2
  have f3 : g.offsets 3 + 4 * (g.n + 1) ≤ g.size := by simpa [Geometry.words] using h.fits 3
  have sep31 := h.separate 3 1 (by decide)
  have sep32 := h.separate 3 2 (by decide)
  have sep13 := h.separate 1 3 (by decide)
  simp only [Geometry.words, show (3 : Fin 4) ≠ 0 by decide,
    show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide, ite_false] at sep31 sep32 sep13
  have sub : SubCtx u g.base g.size (g.offsets 3) (g.offsets 1) (g.offsets 2) (g.n + 1) :=
    ⟨h.workspace.nowrap, f3, f1, f2, sep31, sep32, ctx.workspace.writable⟩
  have sel : SelectCtx u g.base g.size (g.offsets 1) (g.offsets 3) (g.offsets 1) (g.n + 1) :=
    ⟨h.workspace.nowrap, f1, f3, f1, by omega, Or.inr (Or.inr rfl), ctx.workspace.writable⟩
  refine WP.mono (subtractIfGe_ok u sub sel (by omega) p0 p10 p12 p9 count c7 carry) ?_
  rintro t ⟨value, bit, frame, keep⟩
  have finalFrame : Outs (State.addr g.base) g.ranges s.mem t.mem := by
    rw [← mem]
    exact frame.mono (by simp [Geometry.ranges])
  have finalRest : Rest clobbers s t :=
    (rest.mono (by simp [clobbers])).trans (keep.mono (by simp [subLoopClobbers, clobbers]))
  refine ⟨?_, ?_, h.after finalFrame finalRest.wr (finalRest.gpr .r8 (by simp [clobbers])),
    by rw [← mem]; exact frame, finalRest⟩
  · simpa only [Geometry.value, Geometry.words, mem, show (1 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 0 by decide, ite_false] using value
  · simpa only [Geometry.value, Geometry.words, mem, show (1 : Fin 4) ≠ 0 by decide,
      show (2 : Fin 4) ≠ 0 by decide, ite_false] using bit

theorem Context.divisor_frame {g : Geometry} {s t : State} (h : Context g s)
    (frame : Outs (State.addr g.base) g.ranges s.mem t.mem) : g.value t.mem 2 = g.value s.mem 2 := by
  have f2 : g.offsets 2 + 4 * (g.n + 1) ≤ g.size := h.fits 2
  have nowrap := h.workspace.nowrap
  change val32 _ _ _ (g.n + 1) = val32 _ _ _ (g.n + 1)
  refine frame.val32 ?_ (by omega)
  intro r hr
  simp only [Geometry.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.separate 2 0 (by decide)
  · exact h.separate 2 1 (by decide)
  · exact h.separate 2 3 (by decide)

end VG.Proof.Rsa.Arm.Div
