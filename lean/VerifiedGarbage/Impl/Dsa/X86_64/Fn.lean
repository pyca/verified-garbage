module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate

/-! # DSA on x86-64: the functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`): every
vector register at the level `v` and every caller-saved register but the `rb`
bits of the result cleared, and the `n` bytes of stack its frames use zeroed.
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.Dsa.parameterInitApi`'s function as emitted. -/
def parameterInit : Prog isa := scrubAll .sse 32 0 ParameterSearch.init

/-- `Spec.Dsa.randomSignPrevalidatedApi`'s function as emitted, over the
squaring `sq` and multiplication `mul`, calling its signer as `name`, its
cleanup at the level `v`. -/
def randomSignPrevalidated (v : VecLevel) (name : String) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) :
    Prog isa :=
  scrubAll v 32 264 (RandomSign.code name (PrevalidatedSign.sign sq mul))

/-- `Spec.Dsa.validatePrivateKeyApi`'s function as emitted. -/
def validatePrivateKey (v : VecLevel) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubAll v 32 8 (PrevalidatedSign.validate sq mul)

/-- `Spec.Dsa.validatePublicKeyApi`'s function as emitted. -/
def validatePublicKey (v : VecLevel) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubAll v 32 8 (Prevalidated.validate sq mul)

/-- `Spec.Dsa.verifyPrevalidatedApi`'s function as emitted. -/
def verifyPrevalidated (v : VecLevel) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubAll v 32 8 (Prevalidated.verify sq mul)

/-- `Spec.Dsa.generateKeyApi`'s function as emitted, calling its checks of
the parameters as `check` and its derivation as `derive`. -/
def generateKey (v : VecLevel) (check derive : String) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) :
    Prog isa :=
  scrubAll v 32 264 (GenerateKey.code check derive (Generate.checkParameters sq mul) (Generate.deriveChecked sq mul))

/-- `Spec.Dsa.deriveKeyApi`'s function as emitted. -/
def deriveKey (v : VecLevel) (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  scrubAll v 32 8 (Generate.deriveKey sq mul)

end VG.Impl.Dsa.X86_64.Fn
