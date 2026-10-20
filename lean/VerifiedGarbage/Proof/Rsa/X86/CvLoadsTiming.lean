module
public import VerifiedGarbage.Proof.Rsa.X86.CvPair

import VerifiedGarbage.Proof.Rsa.X86.CvLoadTiming
import VerifiedGarbage.Proof.Rsa.X86.CvZero
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Clearing the CRT workspace and importing all four integers has a public trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Rsa.X86.CrtValues VG.Impl.Rsa.X86.Keys

theorem zeros_relCT (g : CallGeometry) :
    RelCT isa (Pair g) (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (2 * g.n + 2))) (Pair g) := by
  have trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false))
      (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (2 * g.n + 2)))
      (VG.X86.Taint.Agree (workspaceTaint false)) := by
    apply erased_relCT (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (2 * g.n + 2))) (VG.Impl.Mont.X86.Dynamic.zerosW 0 1)
      (VG.Taint.hintOf taint (workspaceTaint false) (VG.Impl.Mont.X86.Dynamic.zerosW 0 1)) rfl rfl rfl
    rfl
  intro s t tr ur sf tf h es et
  have eq := (trace _ _ _ _ _ _ h.workspace es et).1
  obtain ⟨hs, _, _, ks⟩ := wp_result (zeroArrays_ok h.left) es
  obtain ⟨ht, _, _, kt⟩ := wp_result (zeroArrays_ok h.right) et
  exact ⟨eq, h.after hs ht ks kt (by decide)⟩

theorem loads_relCT (g : CallGeometry) : RelCT isa (Pair g) (loads g.n) (Pair g) :=
  VG.RelCT.seq (zeros_relCT g) (VG.RelCT.seq (load_relCT g 0 aDQ (by decide))
    (VG.RelCT.seq (load_relCT g 1 aP (by decide))
      (VG.RelCT.seq (load_relCT g 2 aQ (by decide)) (load_relCT g 3 aD (by decide)))))

end VG.Proof.Rsa.X86.CrtValues
