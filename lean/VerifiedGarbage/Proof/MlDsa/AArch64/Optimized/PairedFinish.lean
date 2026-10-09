import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Paired
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseHintFinish

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.MlDsa.AArch64.Optimized.Paired
open VG.Proof.MlDsa.AArch64.Optimized.Response (finishValue hintFinishValue exec_umov_word)

def returnCode (kind : Kind) : List Instr :=
 [.umov .w .x0 .v30 0,.umov .w .x9 .v30 1,.logic .orr .w .x0 .x0 .x9,
 .umov .w .x9 .v30 2,.logic .orr .w .x0 .x0 .x9,.umov .w .x9 .v30 3,
 .logic .orr .w .x0 .x0 .x9,.addImm .w .x0 .x0 1] ++
 (if kind==.h then [.lsl .x .x0 .x0 32,
 .umov .w .x9 .v14 0,.umov .w .x10 .v14 1,.add .w .x9 .x9 .x10,
 .umov .w .x10 .v14 2,.add .w .x9 .x9 .x10,.umov .w .x10 .v14 3,
 .add .w .x9 .x9 .x10,.logic .orr .x .x0 .x0 .x9] else [])
def restoreCode : List Instr := saved.zipIdx.map (fun (r,i) => .ldrq r .x2 (1920+16*i))

theorem finish_split (kind : Kind) : finish kind=returnCode kind++restoreCode := by
  cases kind <;> rfl

def returnValue (kind : Kind) (s : State) : BitVec 64 :=
  if kind==.h then hintFinishValue (s.v .v14) (s.v .v30) else finishValue (s.v .v30)

/-- Both polynomial norm flags are accumulated before returning. The hint
kernel returns the combined count in low32 and success in bit32. -/
theorem return_ok (kind : Kind) (s : State) :
    WP isa (.block (returnCode kind)) s fun t =>
      ((t.gpr .x0=returnValue kind s ∧ t.mem=s.mem) ∧ Keep [.x0,.x9,.x10] s t) ∧ t.v=s.v := by
  cases kind <;>
    apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl) <;>
    refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl) <;>
    unfold returnCode returnValue hintFinishValue finishValue <;>
    arun [exec_umov_word (i := 0) (hi := by decide),exec_umov_word (i := 1) (hi := by decide),
      exec_umov_word (i := 2) (hi := by decide),exec_umov_word (i := 3) (hi := by decide)]
  · rfl
  · rfl
  · exact BitVec.or_comm _ _

end VG.Proof.MlDsa.AArch64.Optimized.Paired
