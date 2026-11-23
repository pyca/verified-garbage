module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Dsa.X86_64.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Impl.Dsa.X86_64.GenerateKey
public import VerifiedGarbage.Impl.Dsa.X86_64.Generate
public import VerifiedGarbage.Impl.ForwardCall.X86_64Slots
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFn

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

/-- `Spec.Dsa.parameterSearchApi`'s function as emitted, calling its search
for each width (`c₁₂₈`, `c₂₅₆`, `c₃₈₄`) by its name, with the addresses
`f₁₂₈`, `f₂₅₆` and `f₃₈₄` loads (`ParameterSearch.fnAddrs`). -/
def parameterSearch (v : VecLevel) (f₁₂₈ f₂₅₆ f₃₈₄ : List Instr) (n₁₂₈ n₂₅₆ n₃₈₄ : String)
    (c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa) : Prog isa :=
  scrubAll v 32 632 (ParameterSearch.widths f₁₂₈ f₂₅₆ f₃₈₄ n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄)

/-! ## One function for every implementation of the arithmetic

A function over the arithmetic is emitted once, as an internal function that
calls the multiplication and the squaring indirectly, through the words
above its `m` stack arguments (`mulS`, `sqS`). Each implementation's
function stores its callees' addresses there and calls it (`slotted`). -/

/-- `[o] = [a] [b] R⁻¹ mod m` by an indirect call, through `[rsp + disp]`, of
the function `name`, whose code is `body`. -/
def mulS (disp : Nat) (name : String) (body : Prog isa) (o a b : Nat) : Prog isa :=
  .seq (.block (Impl.Bignum.X86_64.MontFn.args o a b))
    (.icall (.callm { base := .rsp, disp := ((disp : Nat) : Int) }) name body (.block []))

/-- The squaring of `aY`, as `mulS`. -/
def sqS (disp : Nat) (name : String) (body : Prog isa) : Prog isa :=
  mulS disp name body Impl.Bignum.X86_64.Public.aY Impl.Bignum.X86_64.Public.aY Impl.Bignum.X86_64.Public.aY

/-- The function `entry` over the arithmetic, for `m` stack arguments, calling
the multiplication `nm` (code `bm`) and the squaring `ns` (code `bs`) through
the words above them. -/
def slotBody (m : Nat) (entry : Prog isa → (Nat → Nat → Nat → Prog isa) → Prog isa) (nm ns : String)
    (bm bs : Prog isa) : Prog isa :=
  entry (sqS (8 * (m + 2)) ns bs) (mulS (8 * (m + 1)) nm bm)

/-- The call of `slotBody`, as the internal function `name`, with the `m`
stack arguments and the addresses of `nm` and `ns` in a frame of `bytes`
bytes. -/
def slotted (bytes m : Nat) (name : String) (entry : Prog isa → (Nat → Nat → Nat → Prog isa) → Prog isa)
    (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  Impl.ForwardCall.X86_64.forwardS bytes m [nm, ns] name (slotBody m entry nm ns bm bs)

/-- `Spec.Dsa.validatePrivateKeyApi`'s function as emitted, calling the
multiplication `nm` and the squaring `ns`. -/
def validatePrivateKeyS (v : VecLevel) (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  scrubAll v 32 40 (slotted 24 0 "vg_dsa_validate_private_key_shared" PrevalidatedSign.validate nm ns bm bs)

/-- `Spec.Dsa.validatePublicKeyApi`'s function as emitted, as `validatePrivateKeyS`. -/
def validatePublicKeyS (v : VecLevel) (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  scrubAll v 32 40 (slotted 24 0 "vg_dsa_validate_public_key_shared" Prevalidated.validate nm ns bm bs)

/-- `Spec.Dsa.verifyPrevalidatedApi`'s function as emitted, as `validatePrivateKeyS`. -/
def verifyPrevalidatedS (v : VecLevel) (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  scrubAll v 32 72 (slotted 56 4 "vg_dsa_verify_prevalidated_shared" Prevalidated.verify nm ns bm bs)

/-- `Spec.Dsa.deriveKeyApi`'s function as emitted, as `validatePrivateKeyS`. -/
def deriveKeyS (v : VecLevel) (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  scrubAll v 32 56 (slotted 40 3 "vg_dsa_derive_key_shared" Generate.deriveKey nm ns bm bs)

/-- The signer for a validated private key over the multiplication `nm` and
the squaring `ns`, as an internal function that `randomSignPrevalidatedS` calls. -/
def signerS (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  slotted 56 5 "vg_dsa_sign_prevalidated_shared" PrevalidatedSign.sign nm ns bm bs

/-- The checks of the parameters, as `signerS`, called by `generateKeyS`. -/
def checkS (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  slotted 56 0 "vg_dsa_check_parameters_shared" Generate.checkParameters nm ns bm bs

/-- The derivation from checked parameters, as `signerS`, called by `generateKeyS`. -/
def deriveCheckedS (nm ns : String) (bm bs : Prog isa) : Prog isa :=
  slotted 56 3 "vg_dsa_derive_key_checked_shared" Generate.deriveChecked nm ns bm bs

/-- `Spec.Dsa.randomSignPrevalidatedApi`'s function as emitted, calling its
signer (`signerS`) as `name`, its cleanup at the level `v`. -/
def randomSignPrevalidatedS (v : VecLevel) (name nm ns : String) (bm bs : Prog isa) : Prog isa :=
  scrubAll v 32 328 (RandomSign.code name (signerS nm ns bm bs))

/-- `Spec.Dsa.generateKeyApi`'s function as emitted, calling its checks of
the parameters (`checkS`) as `check` and its derivation (`deriveCheckedS`) as
`derive`. -/
def generateKeyS (v : VecLevel) (check derive nm ns : String) (bm bs : Prog isa) : Prog isa :=
  scrubAll v 32 328 (GenerateKey.code check derive (checkS nm ns bm bs) (deriveCheckedS nm ns bm bs))

end VG.Impl.Dsa.X86_64.Fn
