module

public import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.CrtCheckProductState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Factor multiplication preserves the inputs to product validation -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem CrtCheckProductInput.after_product {s t : State} {base : BitVec 32} {size len o a d w : Nat}
    (h : CrtCheckProductInput base size len o a d w s) (sep : 8 * len ≤ a)
    (outside : Outs (State.addr base) [(128, 20), (a, 4 * (4 * w + 2))] s.mem t.mem)
    (frame : Frame [⟨State.addr base, size⟩] s.mem t.mem) (ptr : t.gpr .r0 = base)
    (rest : Rest roundClobbers s t) :
    CrtCheckProductInput base size len o a d w t ∧
      numAt t.mem (State.addr base) w 0 = numAt s.mem (State.addr base) w 0 := by
  have small := h.padding.layout.size
  have nowrap := h.padding.workspace.nowrap
  have head := control_buffers_header outside (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega)
  have word (j : Nat) (hj : j = 48 ∨ j = 232 ∨ j = 236 ∨ j = 240) :
      t.mem.readW (off (State.addr base) j) 32 = s.mem.readW (off (State.addr base) j) 32 := by
    apply outs_readW outside
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    · omega
  have saved := saved_base_kept frame h.padding.stackSep h.padding.saved rest.sp
  have pad : CrtPadInput base size len w d t :=
    ⟨h.padding.workspace.congr rest.wr, h.padding.main.congr rest.wr, h.padding.layout.of_header_eq head,
      h.padding.separate, h.padding.fits, ptr, (word 240 (by simp)).trans h.padding.link,
      by rw [rest.rd, rest.wr, rest.sp]; exact h.padding.stackRead,
      by rw [rest.sp]; exact h.padding.stackSep, saved⟩
  have c := h.comparison
  have ctx : SubCtx t base size o a d (4 * w + 2) :=
    ⟨c.subtraction.nowrap, c.subtraction.outFits, c.subtraction.aFits, c.subtraction.bFits,
      c.subtraction.sepA, c.subtraction.sepB, by rw [rest.wr]; exact c.subtraction.writable⟩
  have compare : CrtCompareInput base size o a d w t :=
    ⟨c.workspace.congr rest.wr, c.fit, ctx, ptr, (word 48 (by simp)).trans c.count,
      (word 236 (by simp)).trans c.output, (word 232 (by simp)).trans c.first,
      (word 240 (by simp)).trans c.second,
      by rw [rest.rd, rest.wr, rest.sp]; exact c.stackRead,
      by rw [rest.sp]; exact c.stackSep,
      saved_base_kept frame c.stackSep c.saved rest.sp⟩
  refine ⟨⟨pad, compare, h.separate⟩, ?_⟩
  have fit : arrAt w 8 ≤ 8 * len := h.padding.layout.width ▸ h.padding.layout.layout.2.2.1
  have bound := Nat.le_trans (array_end_le (w := w) (j := 0) (by decide : 0 < 8)) fit
  rw [numAt_native, numAt_native]
  apply outside.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; simp only [arrAt, Spec.Rsa.Mont.hdrBytes]; omega
    · left; simp only; omega
  · have := h.padding.main.nowrap; omega

end VG.Proof.Bignum.Arm
