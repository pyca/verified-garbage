module

import VerifiedGarbage.Spec.Dsa.DomainChecked

/-! Cached-domain contracts preserve the fully checked API's results and
allowed leakage on every ABI and stack bound. These checks also catch drift
if either contract changes independently in a later specification revision. -/

open VG VG.Spec.Dsa

example {M : ISA} (A : Abi M) (stack : Nat) :
    (signDomainCheckedContract A stack).post = (signContract A stack).post := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (signDomainCheckedContract A stack).pub = (signContract A stack).pub := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (verifyDomainCheckedContract A stack).post = (verifyContract A stack).post := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (verifyDomainCheckedContract A stack).pub = (verifyContract A stack).pub := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (randomSignDomainCheckedContract A stack).post = (randomSignContract A stack).post := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (randomSignDomainCheckedContract A stack).pub = (randomSignContract A stack).pub := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (generateKeyDomainCheckedContract A stack).post = (generateKeyContract A stack).post := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (generateKeyDomainCheckedContract A stack).pub = (generateKeyContract A stack).pub := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (deriveKeyDomainCheckedContract A stack).post = (deriveKeyContract A stack).post := rfl

example {M : ISA} (A : Abi M) (stack : Nat) :
    (deriveKeyDomainCheckedContract A stack).pub = (deriveKeyContract A stack).pub := rfl

