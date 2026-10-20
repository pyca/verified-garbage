module

import VerifiedGarbage.Proof.Bignum.Arm.CrtFactorProduct
public import VerifiedGarbage.Proof.Bignum.Arm.CrtFinishRecombine
public import VerifiedGarbage.Proof.Bignum.Arm.CrtProductState
import VerifiedGarbage.Proof.Bignum.Arm.CrtPadAfterProduct
import VerifiedGarbage.Proof.Bignum.Arm.ControlBuffers

/-! # Multiplying h and q establishes the final CRT addition precondition -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

structure CrtRecombineInput (base : BitVec 32) (size len w o a b cp cq d : Nat) (s : State) : Prop where
  multiplication : CrtProductInput base size o a b cp cq w s true
  padding : CrtPadInput base size len w d s
  row : RowCtx s base size o d (4 * w)
  mainBeforeProduct : 8 * len ≤ o
  productBeforePad : o + 4 * (4 * w + 2) ≤ d
  sumFits : val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) +
    numAt s.mem (State.addr base) w 1 < 2 ^ (32 * (4 * w + 2))

theorem crt_recombineProduct_ready (s : State) {base : BitVec 32} {size len w o a b cp cq d : Nat}
    (h : CrtRecombineInput base size len w o a b cp cq d s) :
    WP isa (factorProduct true) s fun t => CrtFinishInput base size len w o d t ∧
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) ∧
      numAt t.mem (State.addr base) w 1 = numAt s.mem (State.addr base) w 1 ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (crt_factorProduct_ok s h.multiplication) ?_
  rintro t ⟨value, outside, ptr, frame, rest⟩
  rw [show 2 * w + 2 * w + 2 = 4 * w + 2 by omega] at value outside
  obtain ⟨pad, residue⟩ := h.padding.after_product h.mainBeforeProduct (by decide : 1 < 8) outside frame ptr rest
  have small := h.padding.layout.size
  have sep := h.mainBeforeProduct
  have output : t.mem.readW (off (State.addr base) 232) 32 = s.mem.readW (off (State.addr base) 232) 32 := by
    apply outs_readW outside
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only <;> omega
    · omega
  refine ⟨⟨pad, ⟨h.row.nowrap, h.row.outFits, h.row.inFits, h.row.separate,
    by rw [rest.wr]; exact h.row.writable⟩,
    by have := h.multiplication.outFits; omega, h.productBeforePad, output.trans h.multiplication.product, ?_⟩,
    value, residue, outside, frame, rest⟩
  rw [value, residue]
  exact h.sumFits

end VG.Proof.Bignum.Arm
