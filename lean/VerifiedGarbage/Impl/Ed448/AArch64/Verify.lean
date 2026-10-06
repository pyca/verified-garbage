import VerifiedGarbage.Impl.Ed448.AArch64.Whole
import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow

/-!
# Ed448 verification on AArch64

`vg_ed448_verify(pk = x0, context = x1, ctxlen = x2, message = x3, len = x4,
signature = x5, scratch = x6) -> w0`: RFC 8032 §5.2.7, with the permutation `c`.

If `ctxlen ≥ 256` it returns 0 at once: such a context is not an Ed448
context. Otherwise, in the frame of the complete operations
(`Impl.Ed25519.AArch64.Whole.wrap`, which saves `x0`–`x5`), with `scratch`
kept in the locals at 248 and the first ten bytes of `dom4(0, context)` at 0:

* `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the locals at 16, with the sponge
  functions, each absorption starting at the position the previous one
  returned (in `x0`);
* `k`, the hash reduced modulo `L` (`vg_ed448_scalar_reduce`), at 136;
* the result of `vg_ed448_verify_equation(pk, signature, k, scratch)`, in `x0`.

Every address and branch depends only on the pointers and the lengths.
-/

namespace VG.Impl.Ed448.AArch64.Verify

open VG.AArch64
open VG.Impl.Ed25519.AArch64.Whole (Value wrap)
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS keep hdr zeroSt kabs kpad ksqz)

/-- Where the locals are: the header of `dom4`, the hash, `k` and `scratch`. -/
def fHdr : Nat := 0
def fH : Nat := 16
def fK : Nat := 136
def fScr : Nat := 248

/-- The saved arguments. -/
def aPk : Src := .val (.caller 0 0)
def aCtx : Src := .val (.caller 1 0)
def aCtxLen : Src := .val (.caller 2 0)
def aMsg : Src := .val (.caller 3 0)
def aLen : Src := .val (.caller 4 0)
def aSig : Src := .val (.caller 5 0)

/-- `scratch` kept, and the header of `dom4`. -/
def entry : List Instr := keep .x6 fScr ++ hdr fHdr (.caller 2 0)

/-- `H(dom4(0, context) ‖ R ‖ A ‖ M)` into the locals at `fH`. -/
def hash (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (zeroSt fScr) <|
  .seq (kabs c fScr (.val (.frame fHdr)) (.val (.const 10)) (.val (.const 0))) <|
  .seq (kabs c fScr aCtx aCtxLen .ret) <|
  .seq (kabs c fScr aSig (.val (.const 57)) .ret) <|
  .seq (kabs c fScr aPk (.val (.const 57)) .ret) <|
  .seq (kabs c fScr aMsg aLen .ret) <|
  .seq (kpad c fScr .ret) (ksqz c fScr (.val (.frame fH)))

def reduceArgs : List (Reg × Src) := [(.x0, .val (.frame fK)), (.x1, .val (.frame fH)), (.x2, .loc fScr 0)]
def equationArgs : List (Reg × Src) :=
  [(.x0, aPk), (.x1, aSig), (.x2, .val (.frame fK)), (.x3, .loc fScr 0)]

def body (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block entry) <| .seq (hash c) <|
    .seq (callS reduceArgs "vg_ed448_scalar_reduce" scalarReduce)
      (callS equationArgs "vg_ed448_verify_equation" verifyEquation)

/-- `vg_ed448_verify`, with the permutation `c`. -/
def verifyWith (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x2 8])
    (.ite (.zero .x .x9) (wrap (body c)) (.block [.movz .x .x0 0 0]))

end VG.Impl.Ed448.AArch64.Verify
