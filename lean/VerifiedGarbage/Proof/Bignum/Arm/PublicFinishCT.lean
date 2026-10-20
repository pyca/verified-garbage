module

import VerifiedGarbage.Proof.Bignum.Arm.PublicArgsCT
public import VerifiedGarbage.Proof.Bignum.Arm.ExportMaskedCT
public import VerifiedGarbage.Proof.Bignum.Arm.PublicResult
public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
import VerifiedGarbage.Proof.Bignum.Arm.PublicArgs
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! # The final RSA output and status are released without input-dependent leakage -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm

theorem publicOutputArgs_ready (s : State) {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb : List Byte}
    (h : PublicResult base dst np ep xp len k eLen nb eb xb s) :
    WP isa (.block PublicFn.outputArgs) s (ExportMaskedInput base dst len (Spec.Rsa.modulusWords k) 6 k) := by
  refine WP.mono (publicOutputArgs_ok s h.stack) ?_
  rintro t ⟨index, output, count, mem, rest⟩
  have ready := h.ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans h.ready.ptr)
  have dims := pc_dimensions h.buffers.minLength h.buffers.maxLength h.buffers.space
  refine ⟨⟨ready.workspace, ready.layout, ready.width, ready.ptr, index⟩,
    by have := h.buffers.minLength; omega, dims.2.2.2.1, h.buffers.outputFit, ?_, h.buffers.outputSeparate,
    output, count, ?_, ?_⟩
  · rw [rest.wr]; exact h.buffers.write
  · rw [rest.sp]; have := h.stack.nowrap; omega
  · rw [rest.rd, rest.wr, rest.sp]; exact h.stack.read (by decide) (by decide)

theorem publicFinish_ct {base dst np ep xp : BitVec 32} {len k eLen : Nat} {nb eb xb1 xb2 : List Byte} (hk : 0 < k) :
    RelCT isa (fun s t => PublicResult base dst np ep xp len k eLen nb eb xb1 s ∧
      PublicResult base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp)
      PublicFn.finish (fun _ _ => True) := by
  let P := fun (s t : State) => PublicResult base dst np ep xp len k eLen nb eb xb1 s ∧
    PublicResult base dst np ep xp len k eLen nb eb xb2 t ∧ s.sp = t.sp
  have args := (publicOutputArgs_ct.mono (P' := P) (fun _ _ h => h.2.2) (fun _ _ h => h)).wp
    (fun s t h => ⟨publicOutputArgs_ready s h.1, publicOutputArgs_ready t h.2.1⟩)
  exact args.seq ((exportMasked_ct (by decide : 6 < 8) hk).mono
    (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

end VG.Proof.Bignum.Arm
