module

public import VerifiedGarbage.TCB.Code

/-!
# Code with its calls of a parameter erased

Code built for a callee that is a parameter (e.g. the permutation of a Keccak
backend) differs between callees only in the calls of it, `.call name body`.
Built for a callee whose body is empty (`.block []`, a *hole*: the call with
its target erased), it is closed, and checks of it are decided once; the code
for any callee is that code with its holes filled (`Code.fillHoles name body`),
which the kernel checks by unfolding both with the callee a variable
(`kernel_rfl`). A property of code that does not look into the bodies of calls
(e.g. `Fusion.normalize`), or that is bounded by the callee's (the depth of its
frames), then holds of the code for every callee.

No function a caller calls has an empty body, so a hole is never a call of
another function; and `fillHoles` does not look into the bodies of calls.
-/

@[expose] public section

namespace VG

variable {M : ISA}

/-- `c` with each call whose body is empty (a hole) made a call of `n`, with
body `b`. Other calls, and their bodies, are kept. -/
def Code.fillHoles (n : String) (b : Prog M) : Prog M → Prog M
  | .block is => .block is
  | .seq x y => .seq (fillHoles n b x) (fillHoles n b y)
  | .ite cd t e => .ite cd (fillHoles n b t) (fillHoles n b e)
  | .loop x cd => .loop (fillHoles n b x) cd
  | .call m body => match body with
    | .block [] => .call n b
    | body => .call m body
  | .frame i x j => .frame i (fillHoles n b x) j
  | .icall i m x y => .icall i m x y

end VG
