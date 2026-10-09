import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic

namespace VG.Proof.MlDsa.AArch64.Optimized.Response
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def finishValue (v : BitVec 128) : BitVec 64 :=
  ((vword v 0 ||| vword v 1 ||| vword v 2 ||| vword v 3)+1).setWidth 64

theorem exec_umov_word (s : State) (d : Reg) (n : VReg) {i : Nat} (hi : i<4) :
    exec (.umov .w d n i) s=some (s.write .w d (vword (s.v n) i)) := by
  simp only [exec,Size.bits,show i*32<128 by omega,ite_true,vword]

theorem finish_ok (s : State) :
    WP isa VG.Impl.MlDsa.AArch64.Optimized.Response.finish s fun t =>
      ((t.gpr .x0=finishValue (s.v .v31) ∧ t.mem=s.mem) ∧ Keep [.x0,.x9] s t) ∧ t.v=s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold finishValue
  arun [exec_umov_word (i := 0) (hi := by decide),exec_umov_word (i := 1) (hi := by decide),
    exec_umov_word (i := 2) (hi := by decide),exec_umov_word (i := 3) (hi := by decide)]
  rfl

def maskWord (b : Bool) : BitVec 32 := if b then -1 else 0

theorem finishValue_masks (a b c d : Bool) :
    finishValue (ofVWords (maskWord a) (maskWord b) (maskWord c) (maskWord d))=
      if a || b || c || d then 0 else 1 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Response
