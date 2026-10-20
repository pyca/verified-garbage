module
public import VerifiedGarbage.Proof.Rsa.X86.RvPair

import VerifiedGarbage.Proof.Rsa.X86.RvLoadTiming
import VerifiedGarbage.Proof.Rsa.X86.RvZero
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Clearing the recovery workspace and importing all three integers has a public trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.Recover VG.Impl.Rsa.X86.Keys

theorem zeros_relCT (g : CallGeometry) :
    RelCT isa (Pair g) (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (g.toGeo.w + 2))) (Pair g) := by
  have trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (g.toGeo.w + 2))) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (workspaceTaint false) (fun _ _ h => h)
      (hc := zerosHint false)
    rw [zeros_check]
    rfl
  intro s t tr ur sf tf h es et
  have eq := (trace _ _ _ _ _ _ h.workspace es et).1
  obtain ⟨hs, _, _, ks⟩ := wp_result (zeroArrays_ok h.left) es
  obtain ⟨ht, _, _, kt⟩ := wp_result (zeroArrays_ok h.right) et
  exact ⟨eq, h.after hs ht ks kt (by decide)⟩

theorem loads_relCT (g : CallGeometry) : RelCT isa (Pair g) (loads g.n) (Pair g) :=
  VG.RelCT.seq (zeros_relCT g) (VG.RelCT.seq (load_relCT g 0 aN (by decide))
    (VG.RelCT.seq (load_relCT g 1 (2 * wE) (by decide)) (load_relCT g 2 (2 * wD) (by decide))))

end VG.Proof.Rsa.X86.Recover
