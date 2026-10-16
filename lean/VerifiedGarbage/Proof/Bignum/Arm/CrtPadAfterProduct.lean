module

public import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.CrtPadModulusState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Recombination multiplication preserves the source for padded residue export -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem CrtPadInput.after_product {s t : State} {base : BitVec 32} {size len w d product j : Nat}
    (h : CrtPadInput base size len w d s) (sep : 8 * len ≤ product) (hj : j < 8)
    (outside : Outs (State.addr base) [(128, 20), (product, 4 * (4 * w + 2))] s.mem t.mem)
    (frame : Frame [⟨State.addr base, size⟩] s.mem t.mem) (ptr : t.gpr .r0 = base)
    (rest : Rest roundClobbers s t) :
    CrtPadInput base size len w d t ∧ numAt t.mem (State.addr base) w j = numAt s.mem (State.addr base) w j := by
  have small := h.layout.size
  have nowrap := h.workspace.nowrap
  have head := control_buffers_header outside (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega)
  have link : t.mem.readW (off (State.addr base) 240) 32 = s.mem.readW (off (State.addr base) 240) 32 := by
    apply outs_readW outside
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    · omega
  refine ⟨⟨h.workspace.congr rest.wr, h.main.congr rest.wr, h.layout.of_header_eq head,
    h.separate, h.fits, ptr, link.trans h.link,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead,
    by rw [rest.sp]; exact h.stackSep, saved_base_kept frame h.stackSep h.saved rest.sp⟩, ?_⟩
  have fit : arrAt w 8 ≤ 8 * len := h.layout.width ▸ h.layout.layout.2.2.1
  have bound := Nat.le_trans (array_end_le hj) fit
  rw [numAt_native, numAt_native]
  apply outside.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right; simp only [arrAt, Spec.Rsa.Mont.hdrBytes]; omega
    · left; simp only; omega
  · have := h.main.nowrap; omega

end VG.Proof.Bignum.Arm
