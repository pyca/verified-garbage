module

public import VerifiedGarbage.Impl.Rsa.X86.GcdBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Ops
import VerifiedGarbage.Proof.Framework.Omega

/-! # What the batched GCD writes

For callers that state the GCD's frame without its proof (`BatchLaw`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.GcdBatchRt

open VG.Impl.Rsa.X86.InvBatchRt VG.Impl.Rsa.X86.GcdBatchRt VG.Proof.Rsa.X86.KeyRt VG.Proof.Rsa.X86.InvBatchRt

/-- What the GCD writes: the header from the window on, arrays 0 to 5, 11 and 12. -/
def gcdWrites (len : Nat) : List (Nat × Nat) :=
  [(win, 88), (rv (kw len) (a 0), 6 * (8 * nw len + 8)), (rv (kw len) (a 11), 2 * (8 * nw len + 8))]

/-- `res`, narrow array 1, just past wide array 0's `n + 1` words. -/
theorem rv_res (len : Nat) : rv (kw len) res = rv (kw len) (a 0) + 4 * nw len + 4 := by
  have := kw_eq len
  simp only [rv, res, a]; omega

end VG.Proof.Rsa.X86.GcdBatchRt
