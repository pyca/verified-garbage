module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtRecombineProduct
public import VerifiedGarbage.Impl.Bignum.Arm.CrtRecombine
import VerifiedGarbage.Proof.Framework.Block

/-! # Exact wide CRT reconstruction, including all buffer initialization -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem crt_recombine_ok (s : State) {base : BitVec 32} {size len w o a b cp cq d : Nat}
    (h : CrtRecombineInput base size len w o a b cp cq d s) :
    WP isa recombine s fun t =>
      val32 t.mem (State.addr base) o (4 * w + 2) =
        val32 s.mem (State.addr base) a (2 * w) * val32 s.mem (State.addr base) b (2 * w) +
        numAt s.mem (State.addr base) w 1 ∧
      Outs (State.addr base) [(128, 20), (o, 4 * (4 * w + 2)), (d, 4 * (4 * w + 2))] s.mem t.mem ∧
      Frame [⟨State.addr base, size⟩] s.mem t.mem ∧ t.gpr .r0 = base ∧ Rest roundClobbers s t := by
  rw [recombine, WP.seq_iff]
  refine WP.mono (crt_recombineProduct_ready s h) ?_
  rintro u ⟨ready, product, residue, outside, frame, rest⟩
  refine WP.mono (crt_finishRecombine_ok u ready) ?_
  rintro t ⟨value, outsideT, frameT, ptrT, restT⟩
  rw [product, residue] at value
  refine ⟨value, (outside.mono ?_).trans (outsideT.mono ?_), frame.trans frameT, ptrT, rest.trans restT⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp

end VG.Proof.Bignum.Arm
