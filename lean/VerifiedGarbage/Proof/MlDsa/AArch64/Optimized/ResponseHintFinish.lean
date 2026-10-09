import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- Packed hint count and norm-success bit, exactly as returned to the signer. -/
def hintFinishValue (counts failures : BitVec 128) : BitVec 64 :=
  (vword counts 0+vword counts 1+vword counts 2+vword counts 3).setWidth 64 |||
    (finishValue failures <<< 32)

def hintFinish : List Instr :=
 [.umov .w .x1 .v31 0,.umov .w .x9 .v31 1,.logic .orr .w .x1 .x1 .x9,
  .umov .w .x9 .v31 2,.logic .orr .w .x1 .x1 .x9,
  .umov .w .x9 .v31 3,.logic .orr .w .x1 .x1 .x9,.addImm .w .x1 .x1 1,
  .umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.add .w .x0 .x0 .x9,
  .umov .w .x9 .v30 2,.add .w .x0 .x0 .x9,
  .umov .w .x9 .v30 3,.add .w .x0 .x0 .x9,
  .lsl .x .x1 .x1 32,.logic .orr .x .x0 .x0 .x1]

theorem hintFinish_ok (s : State) :
    WP isa (.block hintFinish) s fun t =>
      ((t.gpr .x0=hintFinishValue (s.v .v30) (s.v .v31) ∧ t.mem=s.mem) ∧
        Keep [.x0,.x1,.x9] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold hintFinish hintFinishValue finishValue
  arun [exec_umov_word (i := 0) (hi := by decide),exec_umov_word (i := 1) (hi := by decide),
    exec_umov_word (i := 2) (hi := by decide),exec_umov_word (i := 3) (hi := by decide)]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.Response
